// hardware parameters
#define DEVICES 1
#define UNITS_PER_DEVICE 1
#define PES_PER_UNIT 4
#define GLOBAL_MEMORY_ACCESS 4
#define LOCAL_MEMORY_SIZE 8

// input data
#define n 4
#define INPUT_DATA_SIZE 16  // 2^n

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
    :: t < (PES_PER_UNIT - 1) -> nWaitingPEs == 0;
    :: else -> nWaitingPEs = 0;
    fi;
    FAA(nWaitingPEsOut, t);
    if
    :: t < (PES_PER_UNIT - 1) -> nWaitingPEsOut == 0;
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

int globalTime = 0;
bool final = false;

mtype : action = { done, stop, go, gowg, eoi, neoi };

byte localMemory[LOCAL_MEMORY_SIZE * UNITS_PER_DEVICE];
byte globalMemory[INPUT_DATA_SIZE];

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

proctype pex(byte id; byte unitId; chan u_pex; chan pex_u) {
    printf("pex id %d unitid %d \n", id, unitId);
    int startTime = 0;
    int curTime = 0;

    byte globalOffset;
    byte tileIdx;        // iterator over tile elemetns within the wg
    byte wgIter;
    byte wgId;
    byte localId;        // within wg
    byte localMemIdx = id + unitId * PES_PER_UNIT;

    do
    :: u_pex ? wgId, gowg;
        do
        :: u_pex ? wgIter, go ->
            atomic {
                startTime = globalTime;
                curTime = globalTime;
            }
            localId = (workGroupSize > PES_PER_UNIT -> id + wgIter * PES_PER_UNIT : id);
            globalOffset = tileSize * (wgId * workGroupSize + localId);
            for (tileIdx : 0 .. tileSize - 1) {
                if
                :: tileIdx + globalOffset >= INPUT_DATA_SIZE -> break;
                :: else -> skip;
                fi;
                even_sum(localMemory[localMemIdx], globalMemory[tileIdx + globalOffset]);
                long_work(GLOBAL_MEMORY_ACCESS);
            }
            byte t = 0;
            barrier(nWaitingPEs, nWaitingPEsOut, t);
            if
            :: (wgIter + 1) >= workGroupSize / PES_PER_UNIT ->
                pex_u ! eoi;
                break;
            :: else ->
                pex_u ! neoi;
            fi;
        od;
    :: u_pex ? 0, stop ->
        if
        :: id == 0 ->
            for (tileIdx : 1 .. nWorkingPEsPerUnit - 1) {
                sum(localMemory[unitId * nWorkingPEsPerUnit], localMemory[tileIdx + unitId * nWorkingPEsPerUnit]);
                // не будет работать если кол-во юнитов более одного:
                globalTime++;
            }
            // аналогично:
            atomic {
                globalMemory[0] = 0;
                globalTime = globalTime + GLOBAL_MEMORY_ACCESS;
                sum(globalMemory[0], localMemory[unitId * nWorkingPEsPerUnit]);
                globalTime = globalTime + GLOBAL_MEMORY_ACCESS;
                // ?? не совсем корректно считается время
                // должно быть три обращения к глобальной памяти: чтениe и две записи
                // или один к глобальной -- все вычисления оставить в локальной, не зануляя [0] элемент
            }
            final = true;
        :: else -> skip;
        fi;
        break;
    od;
}

proctype unit(byte unitIdx; chan dev_u; chan u_dev) {
    byte pesIdx;
    byte wgIter;
    byte wgId;
    byte nProc;
    mtype : Action doneFlag;

    chan u_pex = [0] of {byte, mtype : action};
    chan pex_u = [0] of {mtype : action};

    atomic {
        for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
            run pex(pesIdx, unitIdx, u_pex, pex_u);
        }
    }
    do
    :: dev_u ? wgId, go ->
        wgIter = 0;
        atomic {
            for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                u_pex ! wgId, gowg;
                u_pex ! wgIter, go;
            }
        }
        if
        :: workGroupSize <= PES_PER_UNIT ->
            atomic {
                for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                    pex_u ? eoi;
                }
            }
        :: else ->
            wgIter = 1;
            nProc = 0;
            for (pesIdx : 0 .. workGroupSize - PES_PER_UNIT - 1) {
                atomic {
                    pex_u ? doneFlag;
                    if
                    :: doneFlag == neoi ->
                        u_pex ! wgIter, go;
                    :: else -> skip
                    fi;
                    nProc++;
                    if
                    :: nProc >= PES_PER_UNIT ->
                        wgIter++;
                        nProc = 0;
                    :: else -> skip;
                    fi;
                }
            }
            for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                pex_u ? eoi;
            }
        fi;
        u_dev ! done;
    :: dev_u ? 0, stop ->
        atomic {
            for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                u_pex ! 0, stop;
            }
        }
        break;
    od;
}

proctype device(chan d_hst; chan hst_d) {
    byte unitIdx;
    byte wgId;

    chan dev_u = [0] of {byte, mtype : action};     // wgId
    chan u_dev = [0] of {mtype : action};

    atomic {
        for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
            run unit(unitIdx, dev_u, u_dev);
        }
    }
    do
    :: hst_d ? go ->
        dev_u ! 0, go;
        if
        :: nWorkGroups <= UNITS_PER_DEVICE ->
            atomic {
                for (unitIdx : 0 .. nWorkingUnitsPerDevice - 1) {
                    u_dev ? done;
                    allWorkingPEs = allWorkingPEs - nWorkingPEsPerUnit;
                }
            }
        :: else ->
            unitIdx = 0;
            wgId = unitIdx + 1;
            do
            :: unitIdx < nWorkGroups - nWorkingUnitsPerDevice ->
                atomic {
                    u_dev ? done;
                    dev_u ! wgId, go;
                    wgId++;
                    unitIdx++;
                }
            :: else -> break;
            od;
            unitIdx = 0;
            do
            // ????????? не работает если оставшихся воркгрупп меньше чем юнитов (host аналогично)
            :: unitIdx < UNITS_PER_DEVICE ->
                atomic {
                    u_dev ? done;
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
                dev_u ! 0, stop;
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

    select (i : 1 .. n - 1);
    tileSize = INPUT_DATA_SIZE >> (n - i);
    tileSize = (workGroupSize * tileSize > INPUT_DATA_SIZE -> INPUT_DATA_SIZE / workGroupSize : tileSize);

    nWorkGroups = INPUT_DATA_SIZE / (workGroupSize * tileSize);  
    nWorkingDevices = (nWorkGroups <= UNITS_PER_DEVICE * DEVICES -> nWorkGroups / UNITS_PER_DEVICE : DEVICES);
    nWorkingDevices = (nWorkGroups / UNITS_PER_DEVICE -> nWorkingDevices : 1);
    nWorkingUnitsPerDevice = (nWorkGroups <= UNITS_PER_DEVICE -> nWorkGroups : UNITS_PER_DEVICE);
    nWorkingPEsPerUnit = (workGroupSize <= PES_PER_UNIT -> workGroupSize : PES_PER_UNIT);
    allWorkingPEs = nWorkingDevices * nWorkingUnitsPerDevice * nWorkingPEsPerUnit;

    atomic {
        run host();
        run clock();
    }
}
