#!/bin/bash

for i in {1..1000}
do
	# echo $i
	if spin -p -s -r -X -v -n"$i" -l -g -u10000 autotune.pml | grep -q "aoutput = 6"; then 
		:
	else
		echo $i; break
	fi
done	
