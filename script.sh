#!/bin/bash

#Format: ./script spthyFile lemmaFiles oracleFile

theoryFile=$1
theoryName=$(sed 's#.*/\([^\.]*\).*#\1#' <<<$theoryFile)
lemmaFilename=$2

cd benchmark

if [ ! -d $theoryName ]; then 
	mkdir $theoryName
fi
cd $theoryName

cpt=0
timeFile="time_"$cpt
while [ -f $timeFile ]; do
	cpt=$((cpt+1))
	timeFile="time_"$cpt
done

for i in {0..9}; do 
	echo "Iteration: "$i
	while read line; do
		if [ $# -eq 3 ] ; then 
			if [ ${line:0:1} != '#' ] ; then
				echo $line >> $timeFile
				echo "oracle" >> $timeFile
				{ time tamarin-prover --prove=$line --heuristic=o --oraclename=../../$3 ../../$theoryFile +RTS -N10 -RTS  > oracle_$cpt"_"$line 2>&1 ; } 2>> $timeFile
			fi
		else
			if [ ${line:0:1} != '#' ] ; then
				echo $line >> $timeFile
			echo "tactic" >> $timeFile
				{ time tamarin-prover --prove=$line ../../$theoryFile +RTS -N10 -RTS  > tactic_$cpt"_"$line 2>&1 ; } 2>> $timeFile
			fi
		fi
	done < ../../$lemmaFilename
done

cd ../..