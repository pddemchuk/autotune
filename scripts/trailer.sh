#!/bin/bash

spin -k autotune.pml.trail autotune.pml | grep -E "trail ends after|workGroupSize|tileSize|globalTime =|nWorkGroups|nWorkingDevices|nWorkingUnitsPerDevice|nWorkingPEsPerUnit"
