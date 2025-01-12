#!/bin/bash

echo "input data size - 16"
echo ;

spin -k autotune.pml.trail autotune.pml | grep -E "trail ends after|workGroupSize|tileSize|globalTime =|nWorkGroups|nWorkingDevices|nWorkingUnitsPerDevice|nWorkingPEsPerUnit"
