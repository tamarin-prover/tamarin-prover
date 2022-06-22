#!/bin/bash

filenames=(
# "SSH/ssh-with-forwarding-bounded.spthy"  # this one has too many partial deconstructions
"privacypass.spthy"
"ExistingSapicModels/OTP.spthy"
"ExistingSapicModels/nsl-no_as-untagged.spthy"
"ExistingSapicModels/AC_sid_with_attack.spthy"
"ExistingSapicModels/AKE.spthy"
"ExistingSapicModels/AC.spthy"
"ExistingSapicModels/AC_counter_with_attack.spthy"
"States/scytl-voting-system.spthy"
"States/secure-device.spthy"
# "States/canauth.spthy" # not working on tamarin
"LAKE/lake-edhoc.spthy"
"LAKE/lake-edhoc-DHmode-FS-KCI.spthy"
"KEMTLS/kemtls.spthy"
"KEMTLS/kemtls-noaead.spthy"
"KEMTLS/kemtls-clientauth.spthy"
"5G_AKA/5G_AKA.spthy"
"SSH/ssh-with-one-forwarding.spthy"
"SSH/ssh-without-forwarding.spthy"
)

runners=("tamarin-prover")

IFS='' # required to keep the tabs and spaces

TIMEOUT='100m'

exec_runner(){
    START=$(date +%s)
    res=$(timeout $TIMEOUT $runner $filename --prove)
    END=$(date +%s)
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
for file in "${filenames[@]}"; do
# find . -name "*.spthy"  | while read line; do
     #    filename="$line"
     filename="$file"
    echo 'Extracting examples from '"$filename"
    echo -n "$filename,"  >> "$outfilename"
    for runner in "${runners[@]}"; do
		exec_runner
    done
    echo ""  >> "$outfilename" # jump line
done
