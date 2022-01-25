#!/bin/bash

SAPIC_CASE_STUDIES_SLOW=*.spthy



runners=("progsverif-tamarin")

IFS='' # required to keep the tabs and spaces

TIMEOUT='30m'

exec_runner(){
    START=$(date +%s)
    res=$(timeout $TIMEOUT $runner $filename)
    END=$(date +%s)
    DIFF=$(echo "$END - $START" | bc)
    echo -n $res | grep "RESULT" | tr '\n' ' '  >> "$outfilename"
    echo -n ";$DIFF;" >> "$outfilename"
}


outfilename="res-pro.csv"
echo -n "filename"  >> "$outfilename"
for runner in "${runners[@]}"; do
    echo -n "; $runner result ; $runner time"   >> "$outfilename"
done
echo ""  >> "$outfilename" # jump line
# for file in $files; do
find . -name "*.spthy"  | while read line; do
    filename="$line"
    echo 'Extracting examples from '"$filename"
    echo -n "$filename;"  >> "$outfilename"
    for runner in "${runners[@]}"; do
		exec_runner
    done
   echo ""  >> "$outfilename" # jump line
done
