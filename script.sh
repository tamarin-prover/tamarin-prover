#!/bin/bash

#Format: ./script spthyFile lemmaFiles oracleFile

theoryFile=$1
theoryName=benchmark/$(sed 's#.*/\([^\.]*\).*#\1#' <<<$theoryFile).txt
lemmaFilename=$2

while read line; do
	if [ $# -eq 3 ] ; then 
		if [ ${line:0:1} != '#' ] ; then
			echo $line >> $theoryName.txt
			echo "oracle" >> $theoryName.txt
			{ time tamarin-prover --prove=$line --heuristic=o --oraclename=$3 $theoryFile > benchmark/$line.txt 2>&1 ; } 2>> $theoryName.txt
		fi
	else
		if [ ${line:0:1} != '#' ] ; then
			echo $line >> $theoryName.txt
			echo "tactic" >> $theoryName.txt
			{ time tamarin-prover --prove=$line $theoryFile > benchmark/$line.txt 2>&1 ; } 2>> $theoryName.txt
		fi
	fi
done < $lemmaFilename