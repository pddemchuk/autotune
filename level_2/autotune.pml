int Tmin = 101;

// hardware parameters
#define DEVICES 2
#define UNITS_PER_DEVICE 2
#define PES_PER_UNIT 2
#define LOCAL_MEMORY_ACCESS 1
#define GLOBAL_MEMORY_ACCESS 4
#define LOCAL_MEMORY_SIZE 32

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
                    nWaitingUnits = t;
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
                        nWaitingUnits = 0;
                    }
                }
            }
        }
    :: else -> skip;
    fi;
}

inline work_step() {
    atomic {
        curTime = globalTime;
        nRunningUnits++;
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
byte allWorkingUnits = 0;
byte nRunningUnits = 0;
byte nWaitingUnits = 0;
byte nWarpsPerUnit = 0;
byte nWarps = 0;
byte nInstructions = 7;

int globalTime = 0;
byte unitsFinal = 0;
bool final;

mtype : action = { done, stop, stopwarps, go, gowg, gowarp, donewarp };

byte globalMemory[INPUT_DATA_SIZE];
int aoutput = 0;

chan workgroups = [16] of {int, bool};      // wgId, readyToRun

twoDimArray isWarpReadyToRun[DEVICES];

// tuning parameters
int nWorkGroups = 0;
int workGroupSize = 0;
int tileSize = 0;

proctype clock() {
    do
    :: final -> break;
    :: nRunningUnits == allWorkingUnits - nWaitingUnits && allWorkingUnits != 0 && nWaitingUnits != allWorkingUnits ->
        atomic {
            nRunningUnits = 0;
            globalTime++;
        }
    od
}

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
    bool longWorkFlag;
    int startTime = 0;
    int curTime = 0;

    int localMemory[LOCAL_MEMORY_SIZE];

    // private memory (registers)
    byte localId[INPUT_DATA_SIZE];
    byte globalOffset[INPUT_DATA_SIZE];
    byte tileIdx[INPUT_DATA_SIZE];
    byte readyToEvenSum[INPUT_DATA_SIZE];

    // цикл по воркгруппам
    do
    :: sch_u ? 0, wgId, go ->

        for (i : 0 .. LOCAL_MEMORY_SIZE - 1) {
            localMemory[i] = 0;
        }

        for (i : 0 .. INPUT_DATA_SIZE - 1) {
            localId[i] = 0;
            globalOffset[i] = 0;
            tileIdx[i] = 0;
            readyToEvenSum[i] = 0;
        }

        // цикл по варпам
        do
        :: sch_u ? warpId, instrId, gowarp ->

            atomic {
                startTime = globalTime;
                curTime = globalTime;
            }

            if
            // индекс в локальной памяти
            :: instrId == 0 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        localId[pesIdx * nWarpsPerUnit + warpId] = (workGroupSize > nWorkingPEsPerUnit -> pesIdx + warpId * nWorkingPEsPerUnit : pesIdx);
                    }
                }
            // сдвиг в исходном массиве
            :: instrId == 1 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        globalOffset[pesIdx * nWarpsPerUnit + warpId] = tileSize * (wgId * workGroupSize + localId[pesIdx * nWarpsPerUnit + warpId]);
                    }
                }
            // проверка на выход за границы исходного массива, readyToEvenSum -- предикатный регистр
            :: instrId == 2 ->
                atomic {
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        if
                        :: tileIdx[warpId] + globalOffset[pesIdx * nWarpsPerUnit + warpId] < INPUT_DATA_SIZE ->
                            readyToEvenSum[pesIdx * nWarpsPerUnit + warpId] = 1;
                        :: else -> skip;
                        fi;
                    }
                }
            // суммируем, если предикатный регистр = 1
            :: instrId == 3 ->
                atomic {
                    longWorkFlag = false;
                    for (pesIdx : 0 .. nWorkingPEsPerUnit - 1) {
                        if
                        :: readyToEvenSum[pesIdx * nWarpsPerUnit + warpId] ->
                            even_sum(localMemory[localId[pesIdx * nWarpsPerUnit + warpId]], globalMemory[tileIdx[warpId] + globalOffset[pesIdx * nWarpsPerUnit + warpId]]);
                            longWorkFlag = true;
                            readyToEvenSum[pesIdx * nWarpsPerUnit + warpId] = 0;
                        :: else -> skip;
                        fi;
                    }
                if
                :: longWorkFlag ->
                    long_work(GLOBAL_MEMORY_ACCESS);
                    startTime = curTime;
                :: else -> skip;
                fi;
                }
            // цикл по tiles: если внутри цикла, возвращаемся на инструкцию 1
            :: instrId == 4 -> // for (tileIdx : 0 .. tileSize - 1)
                atomic {
                    tileIdx[warpId]++;
                    if
                    :: tileIdx[warpId] < tileSize - 1 ->
                        instrId = instrId - 3;
                    :: else -> skip;
                    fi;
                }
            :: instrId == 5 ->
                barrier();
            // пекс, у которого локальный индекс = 0, сумммирует все локальные результаты в глобальную переменную, хранящую результат
            :: instrId == 6 ->
                if
                :: localId[0 * nWarpsPerUnit + warpId] == 0 ->
                    for (i : 0 .. nWarpsPerUnit * nWorkingPEsPerUnit - 1) {
                        atomic {
                            sum(aoutput, localMemory[i]);
                            long_work(GLOBAL_MEMORY_ACCESS);
                            startTime = curTime;
                        }
                    }
                :: else -> skip;
                fi;
            fi;

            // инструкция с номером instrId выполнена
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

        // warps -- очередь варпов, isWarpReadyToRun -- массив битов готовности варпов
        for (warpId : 0 .. nWarpsPerUnit - 1) {
            isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] = true;
            warps ! warpId, 0;
        }

        do
        :: nempty(warps) ->
            warps ? warpId, instrId;
            // barrierIn -- массив, в котором элемент = 1, если варп ждет в барьере
            // соответсвенно бит готовности варпа = 1, если он не в барьере
            isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] = !barrierIn[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId];
            if
            :: isWarpReadyToRun[deviceIdx].arr[unitIdx * nWarpsPerUnit + warpId] ->
                // снимает с очереди варп и отправляет юниту
                sch_u ! warpId, instrId, gowarp;
                u_sch ? instrId, donewarp;
                instrId++;
                if
                :: instrId < nInstructions ->
                    // возрващает варп в конец очереди
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
        // снимает с очереди воркгруппы и отправляет варп_шедулерам
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
                    allWorkingUnits--;
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
                    allWorkingUnits--;
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

    // workgroups -- глобальная очередь воркгрупп (одна на все девайсы)
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

    // ждет пока все юниты закончат работу
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
    allWorkingUnits = nWorkingDevices * nWorkingUnitsPerDevice;
    nWarpsPerUnit = workGroupSize / nWorkingPEsPerUnit;
    nWarps = nWarpsPerUnit * nWorkingUnitsPerDevice * nWorkingDevices;

    atomic {
        run host();
        run clock();
    }
}

ltl NonTerm  { [] !final }
ltl Fin { <> final }
ltl OverTime { [] (final -> (globalTime > Tmin)) }
ltl Sum6 { [] (final -> ( aoutput == 6 )) }
ltl Sum20 { [] (final -> ( aoutput == 20 )) }
ltl Sum72 { [] (final -> ( aoutput == 72 )) }
