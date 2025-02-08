#!/bin/bash

[[ $1 ]] || echo "need seed"

seed=$1

spin -p -s -r -X -v -n"$1" -l -g -u10000 autotune.pml > log
spin -s -r -X -v -n"$1" -l -g -u10000 autotune.pml > log_full
