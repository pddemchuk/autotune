#!/bin/bash

depth=1400

spin -p -s -r -X -v -n1 -l -g -k autotune.pml.trail -u$depth autotune.pml > log
spin -s -r -X -v -n1 -l -g -k autotune.pml.trail -u$depth autotune.pml > log_full
