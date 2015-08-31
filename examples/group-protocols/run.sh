#! /bin/bash
set -e

export TAMARIN=~/.local/bin/tamarin-prover

mkdir -p log/

function run {
  echo "Analyzing $2. Check './log/$2.log' for tamarin output."
  $TAMARIN +RTS -N -RTS --prove $1 -olog/$2.out >log/$2.log 2>/dev/null
  grep "verified\|falsified\|processing time" log/$2.log log/$2.out | sort -u
}

run  "-Dsecure               STR.spthy"        "STR1"
# run  "-Dsecure               STR_signed.spthy" "STR2"
run  "                       group_joux.spthy" "group_joux"
export TAMARIN_EXTENSIVE_SPLIT=1
run  "-Dsecure --heuristic=o GDH.spthy"        "GDH"
unset TAMARIN_EXTENSIVE_SPLIT
run "         Joux.spthy"          "Joux1"
run "         Joux_EphkRev.spthy"  "Joux2"
run "         TAK1.spthy"          "TAK1_1"
run "         TAK1_eCK_like.spthy" "TAK1_2"
run "-Dsecure RYY.spthy"           "RYY1"
run "-Dattack RYY.spthy"           "RYY2"
run "         Scott.spthy"         "Scott1"
run "         Scott_EphkRev.spthy" "Scott2"
run "-Dsecure Chen_Kudla.spthy"    "Chen_Kudla1"
run "-Dattack Chen_Kudla.spthy"    "Chen_Kudla2"
