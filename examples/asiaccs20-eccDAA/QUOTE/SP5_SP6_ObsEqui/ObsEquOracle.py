#!/usr/bin/env python3

import re
import os
import sys
debug = True

lines = sys.stdin.readlines()
lemma = sys.argv[1]

# INPUT:
# - lines contain a list of "%i:goal" where "%i" is the index of the goal
# - lemma contain the name of the lemma under scrutiny
# OUTPUT:
# - (on stdout) a list of ordered index separated by EOL


rank = []             # list of list of goals, main list is ordered by priority
maxPrio = 110
for i in range(0,maxPrio):
  rank.append([])

if lemma!="AnyLemma":
  print("applying lemma")
  for line in lines:
    num = line.split(':')[0]

    if re.match('.*!Pk\(.*', line): rank[109].append(num)
    elif re.match('.*!Ltk\(.*', line): rank[109].append(num)
    elif re.match('.*Correct*', line): rank[109].append(num)
    elif re.match('.*Shuffle*', line): rank[109].append(num)
    elif re.match('.*TPM_Public*', line): rank[109].append(num)
    elif re.match('.*TPM_EK_QPD*', line): rank[109].append(num)
    elif re.match('.*~~>.*', line): rank[108].append(num)

else:

  exit(0)

# Ordering all goals by ranking (higher first)
for listGoals in reversed(rank):
  for goal in listGoals:
    sys.stderr.write(goal)
    print(goal)
