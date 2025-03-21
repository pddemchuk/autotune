#!/bin/bash

usage() {
    echo "Usage: $0 seed"
    exit 1
}

seed=$1
[[ $seed ]] || usage

depth=1400

spin -p -s -r -X -v -n"$1" -l -g -u$depth autotune.pml > log
spin -s -r -X -v -n"$1" -l -g -u$depth autotune.pml > log_full
