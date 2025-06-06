typedef twoDimArray { byte arr[INPUT_DATA_SIZE / PES_PER_UNIT * UNITS_PER_DEVICE] };
twoDimArray barrierIn[DEVICES];

inline barrier() {
    barrierIn[id] = 1;
    atomic {
        t = 0;
        for (byte i : 0 .. nWorkingElemets - 1) {
            sum(t, barrierIn[i]);
            nWaitingUnits = t;
        }
    }
    if
    :: t == nWarps ->
        atomic {
            for (byte i : 0 .. nWorkingDevices - 1) {
                barrierIn[i] = 0;
                nWaitingUnits = 0;
            }
        }
    :: else -> skip;
    fi;
}

if
:: instrId == 1 ->
	...
...
if
:: instrId == 6 ->
	atomic {
		tileIdx[warpId]++;
	    if
	    :: tileIdx[warpId] < tileSize ->
	    	instrId = instrId - 3;
	    :: else -> skip;
	    fi;
	}
...
fi


for (int i = 0; i < TS; i++) {
	..
}


if
:: instrId == 2 ->
	atomic {
		if
		:: tileIdx[pesIdx * nWarpsPerUnit + warpId] < INPUT_DATA_SIZE ->
			readyToEvenSum[pesIdx * nWarpsPerUnit + warpId] = 1;
		:: else -> skip;
		fi;
	}
:: instrId == 3 ->
	atomic {
		if
		:: readyToEvenSum[pesIdx * nWarpsPerUnit + warpId] ->
			min(..);
			readyToEvenSum[pesIdx * nWarpsPerUnit + warpId] = 0;
		:: else -> skip;
		fi;
	}
…
fi;
