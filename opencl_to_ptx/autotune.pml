int Tmin = 27;

// hardware parameters
#define DEVICES 1
#define UNITS_PER_DEVICE 1
#define PES_PER_UNIT 4
#define GLOBAL_MEMORY_ACCESS 4
#define LOCAL_MEMORY_SIZE 8

// input data
#define n 2
#define INPUT_DATA_SIZE 4 // 2^n

// x - FAA register; r - returned value
inline FAA(x, r) {
    atomic {
        r = x;
        x = x + 1;
    }
}

// FAA registers
byte nWaitingPEs = 0;
byte nWaitingPEsOut = 0;

inline barrier(nWaitingPEs, nWaitingPEsOut, t) {
    FAA(nWaitingPEs, t);
    if
    :: t < (nWorkingPEsPerUnit - 1) -> nWaitingPEs == 0;
    :: else -> nWaitingPEs = 0;
    fi;
    FAA(nWaitingPEsOut, t);
    if
    :: t < (nWorkingPEsPerUnit - 1) -> nWaitingPEsOut == 0;
    :: else -> nWaitingPEsOut = 0;
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
byte nWarps = 0;
byte nInstructions = 5;

int globalTime = 0;
bool final = false;

mtype : action = { done, stop, stopwarps, go, gowg, gowarp, eoi, neoi };

byte localMemory[LOCAL_MEMORY_SIZE * UNITS_PER_DEVICE];
byte globalMemory[INPUT_DATA_SIZE];
byte aoutput = 0;

// tuning parameters
int nWorkGroups = 0;
int workGroupSize = 0;
int tileSize = 0;

proctype clock() {
    do
    :: final -> break;
    :: nRunningPEs == allWorkingPEs - nWaitingPEs && allWorkingPEs != 0 && nWaitingPEs != allWorkingPEs ->
        atomic {
            nRunningPEs = 0;
            globalTime++;
        }
    od
}

proctype unit(byte unitIdx; chan sch_u; chan u_sch) {
    byte pesIdx;
    byte wgId;
    byte warpId;
    byte instrId;
    byte i;
    byte tileIdx;

    // private memory (registers)
    byte localId[INPUT_DATA_SIZE];
    byte localMemIdx[INPUT_DATA_SIZE];
    byte globalOffset[INPUT_DATA_SIZE];

    do
    :: sch_u ? 0, wgId, go ->

        for (i : 0 .. LOCAL_MEMORY_SIZE * UNITS_PER_DEVICE - 1) {
            localMemory[i] = 0;
        }

        do
        :: sch_u ? warpId, instrId, gowarp ->
            if
            :: instrId == 0 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        localId[warpId * nWarps + pesIdx] = (workGroupSize > nWorkingPEsPerUnit -> pesIdx + warpId * nWorkingPEsPerUnit : pesIdx);
                    }
                }
            :: instrId == 1 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        localMemIdx[warpId * nWarps + pesIdx] = pesIdx + unitIdx * nWorkingPEsPerUnit;
                    }
                }
            :: instrId == 2 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        globalOffset[warpId * nWarps + pesIdx] = tileSize * (wgId * workGroupSize + localId[warpId * nWarps + pesIdx]);
                    }
                }
            :: instrId == 3 ->
                for (tileIdx : 0 .. tileSize - 1) {
                    atomic {
                        for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                            if
                            :: tileIdx + globalOffset[warpId * nWarps + pesIdx] >= INPUT_DATA_SIZE -> break;
                            :: else -> skip;
                            fi;
                            even_sum(localMemory[localMemIdx[pesIdx]], globalMemory[tileIdx + globalOffset[warpId * nWarps + pesIdx]]);
                            globalTime = globalTime + GLOBAL_MEMORY_ACCESS;
                        }
                    }
                }
            :: instrId == 4 ->
                if // get_local_id(0) == 0
                :: warpId + 1 == nWarps ->
                    for (tileIdx : 1 .. nWorkingPEsPerUnit - 1) {
                        atomic {
                            sum(localMemory[unitIdx * nWorkingPEsPerUnit], localMemory[tileIdx + unitIdx * nWorkingPEsPerUnit]);
                            globalTime++;
                        }
                    }

                    globalTime = globalTime + GLOBAL_MEMORY_ACCESS;
                    atomic {
                        sum(aoutput, localMemory[unitIdx * nWorkingPEsPerUnit]);
                    }
                    globalTime = globalTime + GLOBAL_MEMORY_ACCESS;
                :: else -> skip;
                fi;
            fi;

            u_sch ! done;
        :: sch_u ? 0, 0, stopwarps ->
            break;
        od;
    :: sch_u ? 0, 0, stop ->
        break;
    od;
}

proctype scheduler(byte unitIdx; chan dev_sch; chan sch_dev) {
    byte wgId;
    byte warpId;

    byte instrId;
    bool readyToRun;

    chan sch_u = [0] of {byte, byte, mtype : action};
    chan u_sch = [0] of {mtype : action};

    chan warps = [16] of {int, int, bool};      // warpId, instrId, readyToRun

    run unit(unitIdx, sch_u, u_sch);

    do
    :: dev_sch ? wgId, go ->

        sch_u ! 0, wgId, go;

        for (warpId : 0 .. nWarps - 1) {
            warps ! warpId, 0, true;
        }

        do
        :: nempty(warps) ->
            warps ? warpId, instrId, readyToRun;
            if
            :: readyToRun ->
                sch_u ! warpId, instrId, gowarp;
                u_sch ? done;
                instrId++;
                if
                :: instrId < nInstructions ->
                    warps ! warpId, instrId, readyToRun;
                :: else ->
                    skip;
                fi;
            :: else ->
                warps ! warpId, instrId, readyToRun;
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

proctype device(chan d_hst; chan hst_d) {
    byte wgId;
    byte unitIdx;

    chan dev_sch = [0] of {byte, mtype : action};
    chan sch_dev = [0] of {mtype : action};

    atomic {
        for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
            run scheduler(unitIdx, dev_sch, sch_dev);
        }
    }
    do
    :: hst_d ? go ->
        atomic {
            for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
                dev_sch ! unitIdx, go;
            }
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
            wgId = unitIdx;
            unitIdx = 0;
            do
            :: unitIdx < nWorkGroups - nWorkingUnitsPerDevice ->
                atomic {
                    sch_dev ? done;
                    dev_sch ! wgId, go;
                    wgId++;
                    unitIdx++;
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
    chan d_hst = [0] of { mtype : action };
    chan hst_d = [0] of { mtype : action };

    final = false;

    run device(d_hst, hst_d);
    hst_d ! go;
    atomic {
        d_hst ? done;
        hst_d ! stop;
    }

    final = true;
}

active proctype main() {
    byte i;

    for (i : 0 .. INPUT_DATA_SIZE - 1) {
        globalMemory[i] = INPUT_DATA_SIZE - i;
    }

    for (i : 0 .. LOCAL_MEMORY_SIZE * UNITS_PER_DEVICE - 1) {
        localMemory[i] = 0;
    }

    select (i : 2 .. n - 1);
    workGroupSize = INPUT_DATA_SIZE >> (n - i);
    //workGroupSize = 2;  // 2 4

    select (i : 1 .. n - 1);
    tileSize = INPUT_DATA_SIZE >> (n - i);
    //tileSize = 4;   // 2 4 8
    tileSize = (workGroupSize * tileSize > INPUT_DATA_SIZE -> INPUT_DATA_SIZE / workGroupSize : tileSize);

    nWorkGroups = INPUT_DATA_SIZE / (workGroupSize * tileSize);
    nWorkingDevices = (nWorkGroups <= UNITS_PER_DEVICE * DEVICES -> nWorkGroups / UNITS_PER_DEVICE : DEVICES);
    nWorkingDevices = (nWorkGroups / UNITS_PER_DEVICE -> nWorkingDevices : 1);
    nWorkingUnitsPerDevice = (nWorkGroups <= UNITS_PER_DEVICE -> nWorkGroups : UNITS_PER_DEVICE);
    nWorkingPEsPerUnit = (workGroupSize <= PES_PER_UNIT -> workGroupSize : PES_PER_UNIT);
    allWorkingPEs = nWorkingDevices * nWorkingUnitsPerDevice * nWorkingPEsPerUnit;
    nWarps = workGroupSize / nWorkingPEsPerUnit;

    atomic {
        run host();
        run clock();
    }
}

ltl NonTerm  { [] !final }
ltl Fin { <> final }
ltl OverTime { [] (final -> (globalTime > Tmin)) }
ltl Sum { [] (final -> ( aoutput == 20)) }
