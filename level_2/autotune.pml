int Tmin = 96;

// hardware parameters
#define DEVICES 2
#define UNITS_PER_DEVICE 2
#define PES_PER_UNIT 2
#define GLOBAL_MEMORY_ACCESS 4
#define LOCAL_MEMORY_SIZE 8

// input data
#define n 4
#define INPUT_DATA_SIZE 16 // 2^n

// arr -- within one device, isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId]
typedef twoDimArray { byte arr[INPUT_DATA_SIZE / PES_PER_UNIT * UNITS_PER_DEVICE] };       // nWarpsPerUnit ~ INPUT_DATA_SIZE / PES_PER_UNIT

twoDimArray barrierIn[DEVICES];

inline barrier() {
    barrierIn[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] = 1;
    atomic {
        t = 0;
        for (d : 0 .. nWorkingDevices - 1) {
            for (u : 0 .. nWorkingUnitsPerDevice - 1) {
                for (w : 0 .. nWarpsPerUnit - 1) {
                    sum(t, barrierIn[d].arr[u * nWarpsPerUnit + w]);
                }
            }
        }
    }
    if
    :: t == nWarps ->
        atomic {
            for (d : 0 .. nWorkingDevices - 1) {
                for (u : 0 .. nWorkingUnitsPerDevice - 1) {
                    for (w : 0 .. nWarpsPerUnit - 1) {
                        barrierIn[d].arr[u * nWarpsPerUnit + w] = 0;
                    }
                }
            }
        }
    fi;
}

inline work_step() {
    atomic {
        curTime = globalTime;
        nRunningPEs++;
        globalTime == curTime + 1;
    }
}

inline long_work(dt) {
    do
    :: globalTime >= startTime + dt -> break;
    :: else -> work_step();
    od;
}

inline even_sum(a, b) {
    atomic {
        if
        :: b % 2 == 0 -> a = a + b;
        :: else -> skip;
        fi
    }
}

inline sum(a, b) {
    atomic {
        a = a + b;
    }
}

// service variables
byte nWorkingDevices = 0;
byte nWorkingUnitsPerDevice = 0;
byte nWorkingPEsPerUnit = 0;
byte allWorkingPEs = 0;
byte nRunningPEs = 0;
byte nWarpsPerUnit = 0;
byte nWarps = 0;
byte nInstructions = 5;

int globalTime = 0;
byte unitsFinal = 0;
bool final;

mtype : action = { done, stop, stopwarps, go, gowg, gowarp, donewarp };

byte globalMemory[INPUT_DATA_SIZE];
byte aoutput = 0;

chan workgroups = [16] of {int, bool};      // wgId, readyToRun

twoDimArray isWarpReadyToRun[DEVICES];

// tuning parameters
int nWorkGroups = 0;
int workGroupSize = 0;
int tileSize = 0;

/*proctype clock() {
    do
    :: final -> break;
    :: nRunningPEs == allWorkingPEs - nWaitingPEs && allWorkingPEs != 0 && nWaitingPEs != allWorkingPEs ->
        atomic {
            nRunningPEs = 0;
            globalTime++;
        }
    od
}*/

proctype unit(byte deviceIdx; byte unitIdx; chan sch_u; chan u_sch) {
    byte pesIdx;
    byte wgId;
    byte warpId;
    byte instrId;
    byte i;
    byte t;
    byte d;
    byte u;
    byte w;
    byte tileIdx;

    byte localMemory[LOCAL_MEMORY_SIZE];

    // private memory (registers)
    byte localId[INPUT_DATA_SIZE];
    byte globalOffset[INPUT_DATA_SIZE];

    do
    :: sch_u ? 0, wgId, go ->

        for (i : 0 .. LOCAL_MEMORY_SIZE - 1) {
            localMemory[i] = 0;
        }

        do
        :: sch_u ? warpId, instrId, gowarp ->

            if
            :: instrId == 0 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        localId[pesIdx * nWarpsPerUnit + warpId] = (workGroupSize > nWorkingPEsPerUnit -> pesIdx + warpId * nWorkingPEsPerUnit : pesIdx);
                    }
                }
            :: instrId == 1 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        globalOffset[pesIdx * nWarpsPerUnit + warpId] = tileSize * (wgId * workGroupSize + localId[pesIdx * nWarpsPerUnit + warpId]);
                    }
                }
            :: instrId == 2 ->
                for (tileIdx : 0 .. tileSize - 1) {
                    atomic {
                        for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                            if
                            :: tileIdx + globalOffset[pesIdx * nWarpsPerUnit + warpId] >= INPUT_DATA_SIZE -> break;
                            :: else -> skip;
                            fi;
                            even_sum(localMemory[localId[pesIdx * nWarpsPerUnit + warpId]], globalMemory[tileIdx + globalOffset[pesIdx * nWarpsPerUnit + warpId]]);
                        }
                        globalTime = globalTime + GLOBAL_MEMORY_ACCESS;
                    }
                }
            :: instrId == 3 ->
                barrier();
            :: instrId == 4 ->
                if
                :: localId[0 * nWarpsPerUnit + warpId] == 0 ->
                    // заменить на nWarp * nWorkingPes ?
                    for (i : 0 .. LOCAL_MEMORY_SIZE - 1) {
                        atomic {
                            sum(aoutput, localMemory[i]);
                            globalTime++;
                        }
                    }
                :: else -> skip;
                fi;
            fi;

            u_sch ! instrId, donewarp;
        :: sch_u ? 0, 0, stopwarps ->
            break;
        od;
    :: sch_u ? 0, 0, stop ->
        unitsFinal++;
        break;
    od;
}

proctype warp_scheduler(byte deviceIdx; byte unitIdx; chan dev_sch; chan sch_dev) {
    byte wgId;
    byte warpId;

    byte instrId;

    chan sch_u = [0] of {byte, byte, mtype : action};       // warpId, instrId, gowarp
    chan u_sch = [0] of {byte, mtype : action};             // instrId, donewarp

    chan warps = [16] of {int, int};      // warpId, instrId

    run unit(deviceIdx, unitIdx, sch_u, u_sch);

    do
    :: dev_sch ? wgId, go ->

        sch_u ! 0, wgId, go;

        for (warpId : 0 .. nWarpsPerUnit - 1) {
            isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] = true;
            warps ! warpId, 0;
        }

        do
        :: nempty(warps) ->
            warps ? warpId, instrId;
            isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] = !barrierIn[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId];
            if
            :: isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] ->
                sch_u ! warpId, instrId, gowarp;
                u_sch ? instrId, donewarp;
                instrId++;
                if
                :: instrId < nInstructions ->
                    warps ! warpId, instrId;
                :: else ->
                    skip;
                fi;
            :: else ->
                warps ! warpId, instrId;
            fi;
        :: empty(warps) ->
            sch_u ! 0, 0, stopwarps;
            break;
        od;
        sch_dev ! done;
    :: dev_sch ? 0, stop ->
        sch_u ! 0, 0, stop;
        break;
    od;
}

proctype device(byte deviceIdx; chan d_hst; chan hst_d) {
    byte wgId;
    byte unitIdx;
    bool readyToRun;
    bool ready;

    chan dev_sch = [0] of {byte, mtype : action};
    chan sch_dev = [0] of {mtype : action};

    atomic {
        for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
            run warp_scheduler(deviceIdx, unitIdx, dev_sch, sch_dev);
        }
    }
    do
    :: hst_d ? go ->
        atomic {
            unitIdx = 0;
            do
            :: unitIdx < nWorkingUnitsPerDevice ->
                workgroups ? wgId, readyToRun;
                if
                :: readyToRun ->
                    dev_sch ! wgId, go;
                    unitIdx++;
                :: else ->
                    workgroups ! wgId, true;
                fi;
            :: else ->
                break;
            od;
        }
        if
        :: nWorkGroups <= nWorkingUnitsPerDevice ->
            atomic {
                for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
                    sch_dev ? done;
                    allWorkingPEs = allWorkingPEs - nWorkingPEsPerUnit;
                }
            }
        :: else ->
            unitIdx = 0;
            do
            :: unitIdx < nWorkGroups - nWorkingUnitsPerDevice ->
                atomic {
                    sch_dev ? done;
                    bool wgWaiting = true;
                    do
                    :: wgWaiting ->
                        workgroups ? wgId, readyToRun;
                        if
                        :: readyToRun ->
                            dev_sch ! wgId, go;
                            wgWaiting = false;
                            unitIdx++;
                        :: else ->
                            workgroups ! wgId, true;
                        fi;
                    :: else ->
                        break;
                    od;
                }
            :: else -> break;
            od;
            unitIdx = 0;
            do
            :: unitIdx < nWorkingUnitsPerDevice ->
                atomic {
                    sch_dev ? done;
                    allWorkingPEs = allWorkingPEs - nWorkingPEsPerUnit;
                    unitIdx++;
                }
            :: else -> break;
            od;
        fi;
        d_hst ! done;
    :: hst_d ? stop ->
        atomic {
            for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
                dev_sch ! 0, stop;
            }
        }
        break;
    od;
}

proctype host() {
    byte deviceIdx;

    chan hst_d = [0] of { mtype : action };
    chan d_hst = [0] of { mtype : action };

    final = false;

    byte wgId;
    for (wgId : 0 .. nWorkGroups - 1) {
        workgroups ! wgId, true;
    }

    atomic {
        for (deviceIdx : 0 .. nWorkingDevices - 1) {
            run device(deviceIdx, d_hst, hst_d);
        }
    }

    atomic {
        for (deviceIdx : 0 .. nWorkingDevices - 1) {
            hst_d ! go;
        }
    }
    atomic {
        for (deviceIdx : 0 .. nWorkingDevices - 1) {
            d_hst ? done;
            hst_d ! stop;
        }
    }

    unitsFinal == nWorkingUnitsPerDevice * nWorkingDevices;
    final = true;
}

active proctype main() {
    byte i;

    for (i : 0 .. INPUT_DATA_SIZE - 1) {
        globalMemory[i] = INPUT_DATA_SIZE - i;
    }

    select (i : 2 .. n - 1);
    workGroupSize = INPUT_DATA_SIZE >> (n - i);
    //workGroupSize = 2;  // 2 4

    select (i : 1 .. n - 1);
    tileSize = INPUT_DATA_SIZE >> (n - i);
    //tileSize = 2;   // 2 4 8
    tileSize = (workGroupSize * tileSize > INPUT_DATA_SIZE -> INPUT_DATA_SIZE / workGroupSize : tileSize);

    nWorkGroups = INPUT_DATA_SIZE / (workGroupSize * tileSize);
    nWorkingDevices = (nWorkGroups <= UNITS_PER_DEVICE * DEVICES -> nWorkGroups / UNITS_PER_DEVICE : DEVICES);
    nWorkingDevices = (nWorkGroups / UNITS_PER_DEVICE -> nWorkingDevices : 1);
    nWorkingUnitsPerDevice = (nWorkGroups <= UNITS_PER_DEVICE -> nWorkGroups : UNITS_PER_DEVICE);
    nWorkingPEsPerUnit = (workGroupSize <= PES_PER_UNIT -> workGroupSize : PES_PER_UNIT);
    allWorkingPEs = nWorkingDevices * nWorkingUnitsPerDevice * nWorkingPEsPerUnit;
    nWarpsPerUnit = workGroupSize / nWorkingPEsPerUnit;
    nWarps = nWarpsPerUnit * nWorkingUnitsPerDevice * nWorkingDevices;

    atomic {
        run host();
        //run clock();
    }
}

ltl NonTerm  { [] !final }
ltl Fin { <> final }
ltl OverTime { [] (final -> (globalTime > Tmin)) }
ltl Sum6 { [] (final -> ( aoutput == 6 )) }
ltl Sum20 { [] (final -> ( aoutput == 20 )) }
ltl Sum72 { [] (final -> ( aoutput == 72 )) }
