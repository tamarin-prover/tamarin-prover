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
timeFile="time_"$cpt"_"*
while compgen -G "$timeFile" > /dev/null; do
	cpt=$((cpt+1))
	timeFile="time_"$cpt"_"*
done
timeFile="time_"$cpt

for i in {0..9}; do 
	echo "Iteration: "$i
	while read line; do
		if [ $# -eq 3 ] ; then 
			if [ ${line:0:1} != '#' ] ; then
				echo $line >> $timeFile"_"$i
				echo "oracle" >> $timeFile"_"$i
				{ time tamarin-prover --prove=$line --heuristic=o --oraclename=../../$3 ../../$theoryFile +RTS -N10 -RTS  > oracle_$cpt"_"$i"_"$line 2>&1 ; } 2>> $timeFile"_"$i
			fi
		else
			if [ ${line:0:1} != '#' ] ; then
				echo $line >> $timeFile"_"$i
				echo "tactic" >> $timeFile"_"$i
				{ time tamarin-prover --prove=$line ../../$theoryFile +RTS -N10 -RTS  > tactic_$cpt"_"$i"_"$line 2>&1 ; } 2>> $timeFile"_"$i
			fi
		fi
	done < ../../$lemmaFilename
done

cd ../..