#!/bin/bash

#Format: ./script spthyFile lemmaFiles oracleFile

theoryFile=$1
theoryName=benchmark/$(sed 's#.*/\([^\.]*\).*#\1#' <<<$theoryFile).txt
lemmaFilename=$2

while read line; do
	if [ $# -eq 3 ] ; then 
		if [ ${line:0:1} != '#' ] ; then
			echo $line >> $theoryName
			echo "oracle" >> $theoryName
			{ time tamarin-prover --prove=$line --heuristic=o --oraclename=$3 $theoryFile +RTS -N10 -RTS  > benchmark/$line.txt 2>&1 ; } 2>> $theoryName
		fi
	else
		if [ ${line:0:1} != '#' ] ; then
			echo $line >> $theoryName
			echo "tactic" >> $theoryName
			{ time tamarin-prover --prove=$line $theoryFile +RTS -N10 -RTS  > benchmark/$line.txt 2>&1 ; } 2>> $theoryName
		fi
	fi
done < $lemmaFilename