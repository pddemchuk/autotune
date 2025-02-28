#!/bin/bash

usage() {
    echo "Usage: $0 sum"
    exit 1
}

sum=$1
[[ $sum ]] || usage

for i in {1..1000}
do
	# echo $i
	if spin -p -s -r -X -v -n"$i" -l -g -u10000 autotune.pml | grep -q "aoutput = $sum"; then
		:
	else
		echo $i; break
	fi
done
