#!/bin/bash

SAPIC_CASE_STUDIES_SLOW=*.spthy



runners=("tamarin-prover")

IFS='' # required to keep the tabs and spaces

TIMEOUT='100m'

exec_runner(){
    START=$(date +%s.%N)
    res=$(timeout $TIMEOUT $runner $filename -D=REACH --prove)
    END=$(date +%s.%N)
    DIFF=$(echo "$END - $START" | bc)
    echo -n $res | grep "verified\|falsified"  | tr '\n' ' '  >> "$outfilename"
    echo -n ",$DIFF," >> "$outfilename"
}


outfilename="res-tam.csv"
echo -n "filename"  >> "$outfilename"
for runner in "${runners[@]}"; do
    echo -n ", $runner result , $runner time"   >> "$outfilename"
done
echo ""  >> "$outfilename" # jump line
# for file in $files; do
find . -name "*.spthy"  | while read line; do
    filename="$line"
    echo 'Extracting examples from '"$filename"
    echo -n "$filename,"  >> "$outfilename"
    for runner in "${runners[@]}"; do
		exec_runner
    done
   echo ""  >> "$outfilename" # jump line
done
