#!/bin/bash

#Format: ./script spthyFile lemmaFiles

theoryFile=$1
theoryName=benchmark/$(sed 's#.*/\([^\.]*\).*#\1#' <<<$theoryFile).txt
lemmaFilename=$2

while read line; do
	if [ ${line:0:1} != '#' ] ; then
		echo $line >> $theoryName.txt
		{ time tamarin-prover --prove=$line $theoryFile > benchmark/$line.txt 2>&1 ; } 2>> $theoryName.txt
	fi
done < $lemmaFilename