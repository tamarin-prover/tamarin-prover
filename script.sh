#!/bin/bash

#Format: ./script spthyFile lemmaFiles oracleFile

theoryFile=$1
theoryName=benchmark/$(sed 's#.*/\([^\.]*\).*#\1#' <<<$theoryFile).txt
lemmaFilename=$2

while read line; do
	if [ $# -eq 3 ] ; then 
		if [ ${line:0:1} != '#' ] ; then
			echo $line >> oracle_$theoryName.txt
			{ time tamarin-prover --prove=$line --heuristic=o --oraclename=$3 $theoryFile > benchmark/$line.txt 2>&1 ; } 2>> oracle_$theoryName.txt
		fi
	else
		if [ ${line:0:1} != '#' ] ; then
			echo $line >> tactic_$theoryName.txt
			{ time tamarin-prover --prove=$line $theoryFile > benchmark/$line.txt 2>&1 ; } 2>> tactic_$theoryName.txt
		fi
	fi
done < $lemmaFilename