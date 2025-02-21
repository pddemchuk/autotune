#!/bin/bash

usage() {
    echo "Usage: $0 seed"
    exit 1
}

seed=$1
[[ $seed ]] || usage

spin -p -s -r -X -v -n"$1" -l -g -u10000 autotune.pml > log
spin -s -r -X -v -n"$1" -l -g -u10000 autotune.pml > log_full
