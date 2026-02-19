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
  
if lemma[0:11]=="oracle_corr": #SP1
  print("applying oracle to "+lemma)
  for line in lines:
    num = line.split(':')[0]
    if re.match('.*Host_.*', line): rank[109].append(num)
    elif re.match('.*\!SignatureVerified.*', line): rank[109].append(num)
    elif re.match('.*Issuer_*', line): rank[108].append(num)
    elif re.match('.*\!TPM_.*', line): rank[107].append(num)
    elif re.match('.*TPM_tkt.*', line): rank[107].append(num)
    elif re.match('.*TPM_CV_E.*', line): rank[107].append(num)
    elif re.match('.*TPM_Commit_RCV1.*', line): rank[107].append(num)
    elif re.match('.*createPrimary.*', line): rank[90].append(num)
    elif re.match('.*returnEK\'>', line): rank[89].append(num)
    elif re.match('.*createDAAKey.*', line): rank[88].append(num)
    elif re.match('.*returnDAAKey\'>', line): rank[87].append(num)
    elif re.match('.*TPM2_ActivateCredentials\'>', line): rank[86].append(num)
    elif re.match('.*ret_TPM2_ActivateCredentials\'>', line): rank[85].append(num)
    elif re.match('.*TPM2_Commit\'>', line): rank[84].append(num)
    elif re.match('.*retTPM2_commit\'>', line): rank[83].append(num)
    elif re.match('.*TPM2_Hash\'>', line): rank[82].append(num)
    elif re.match('.*ret_TPM2_Hash\'>', line): rank[81].append(num)
    elif re.match('.*\'TPM2_Sign\'>', line): rank[80].append(num)
    elif re.match('.*ret_TPM2_Sign\'>', line): rank[79].append(num)
    elif re.match('.*\'TPM2_ActivateCredentials_2\'.*', line): rank[78].append(num)
    elif re.match('.*ret_TPM2_ActivateCredentials_2\'>', line): rank[77].append(num)
    elif re.match('.*TPM2_Commit_rand\'>', line): rank[76].append(num)
    elif re.match('.*ret_TPM2_Commit_rand\'>', line): rank[75].append(num)  
    elif re.match('.*TPM2_Hash_2\'>', line): rank[74].append(num)
    elif re.match('.*ret_TPM2_Hash_2\'>', line): rank[73].append(num) 
    elif re.match('.*\'TPM2_Sign_2\'>', line): rank[72].append(num)
    elif re.match('.*ret_TPM2_Sign_2\'>', line): rank[71].append(num)  
    elif re.match('.*\!KU\( pk\(KDF_EK\(~TPM_EK_Seed\).*', line): rank[70].append(num) 
    elif re.match('.*\!KU\( multp\(f.*, \'P1\'.*', line): rank[70].append(num) 
    elif re.match('.*\!KU\(.*<\'1\'.*', line): rank[60].append(num)
    elif re.match('.*\!KU\( KDF_EK\(~TPM_EK_Seed\).*', line): rank[50].append(num) 
    
elif lemma[0:15]=="oracle_SP3_Unfo":#SP3
  print("applying oracle to "+lemma)
  for line in lines:
    num = line.split(':')[0]
    if re.match('.*\!Pk\(.*', line): rank[109].append(num)
    elif re.match('.*\!TPM_.*', line): rank[109].append(num)
    elif re.match('.*\!KU\( ~y \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~x \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~r \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~f \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~l \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~m \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~r_cv.*', line): rank[100].append(num)
    elif re.match('.*\!KU\( plus\(r_cv.*', line): rank[99].append(num)
    elif re.match('.*\!KU\( plus\(~r_cv.*', line): rank[99].append(num)
    elif re.match('.*\!KU\( multp\(~l,.*', line): rank[97].append(num)
    elif re.match('.*\!KU\( H_n_2\(Nonce.*Message.*', line): rank[96].append(num)
    elif re.match('.*\!KU\( E_S.*',line): rank[95].append(num) 
    elif re.match('.*\!KU\( Message.*~m.*',line): rank[94].append(num) 
    elif re.match('.*createPrimary.*', line): rank[93].append(num)
    elif re.match('.*returnEK\'>', line): rank[92].append(num)
    elif re.match('.*createDAAKey.*', line): rank[91].append(num)
    elif re.match('.*returnDAAKey\'>', line): rank[90].append(num)
    elif re.match('.*\!KU\( multp\(H_n_2\(Nonce.*', line): rank[89].append(num)
    elif re.match('.*\!KU\( multp\(plus\(~r_cv.*', line): rank[89].append(num)
    elif re.match('.*\!KU\( H_k_.*Message.*~f.*', line): rank[88].append(num)
    elif re.match('.*\!KU\(.*<\'1\'.*', line): rank[88].append(num)
    elif re.match('.*In_S\( \$AS, .*', line): rank[87].append(num)
    elif re.match('.*In_S\( \$PS, .*', line): rank[87].append(num)
    elif re.match('.*TPM2_ActivateCredentials\'>', line): rank[86].append(num)
    elif re.match('.*ret_TPM2_ActivateCredentials\'>', line): rank[85].append(num)
    elif re.match('.*TPM2_Commit\'>', line): rank[84].append(num)
    elif re.match('.*retTPM2_commit\'>', line): rank[83].append(num)
    elif re.match('.*TPM2_Hash\'>', line): rank[82].append(num)
    elif re.match('.*ret_TPM2_Hash\'>', line): rank[81].append(num)
    elif re.match('.*\'TPM2_Sign\'>', line): rank[80].append(num)
    elif re.match('.*ret_TPM2_Sign\'>', line): rank[79].append(num)
    elif re.match('.*\'TPM2_ActivateCredentials_2\'.*', line): rank[78].append(num)
    elif re.match('.*ret_TPM2_ActivateCredentials_2\'>', line): rank[77].append(num)
    elif re.match('.*TPM2_Commit_rand\'>', line): rank[76].append(num)
    elif re.match('.*ret_TPM2_Commit_rand\'>', line): rank[75].append(num)  
    elif re.match('.*TPM2_Quote\'>', line): rank[74].append(num)
    elif re.match('.*ret_TPM2_Quote\'>', line): rank[73].append(num)  
    elif re.match('.*\!KU\( plus\(r_cv.*', line): rank[70].append(num)
    elif re.match('.*\!KU\(.*H_n_2\(Nonce\(rnd.*', line): rank[60].append(num)  
    elif re.match('.*\!KU\( multp\(~y.*', line): rank[60].append(num)
    elif re.match('.*\!KU\( multp\(multp\(~r.*', line): rank[40].append(num)
    elif re.match('.*\!KU\( KDF_EK\(~TPM_EK_Seed.*', line): rank[40].append(num)
    elif re.match('.*\!KU\( multp\(multp\(~r.*', line): rank[40].append(num)
    elif re.match('.*\!KU\( KDF_AES\(~TPM.*', line): rank[30].append(num)

elif lemma[0:17]=="oracle_auth_alive":
  print("applying oracle to "+lemma)
  for line in lines:
    num = line.split(':')[0]
    if re.match('.*In_S\(.*', line): rank[106].append(num)
    elif re.match('.*Host_.*', line): rank[109].append(num)
    elif re.match('.*Issuer_*', line): rank[108].append(num)


elif lemma[0:16]=="oracle_auth_weak" or lemma[0:15]=="oracle_auth_non" or lemma[0:21]=="oracle_auth_injective":
  print("applying oracle to "+lemma)
  for line in lines:
    num = line.split(':')[0]

    if re.match('.*In_S\( \$B,.*', line): rank[109].append(num)
    elif re.match('.*In_S\( \$A,.*', line): rank[109].append(num)
    elif re.match('.*In_S\( \$AS,.*', line): rank[109].append(num)
    elif re.match('.*In_S\( \$PS,.*', line): rank[109].append(num)
    elif re.match('.*_State_.*', line): rank[109].append(num)
    elif re.match('.*\!Pk\(.*', line): rank[109].append(num)
    elif re.match('.*createDAAKey\'>', line): rank[108].append(num)
    elif re.match('.*createPrimary\'\)', line): rank[108].append(num)
    elif re.match('.*returnEK\'>', line): rank[108].append(num)
    elif re.match('.*returnDAAKey\'>', line): rank[108].append(num)
    elif re.match('.*In_S\(.*', line): rank[107].append(num)
    elif re.match('.*\!KU\( KDF_EK\(~TPM.*', line): rank[108].append(num)
    elif re.match('.*\!KU\( KDF_AES\(~TPM.*', line): rank[108].append(num)
    elif re.match('.*\!KU\( curlyK\(~K_1\).*', line): rank[107].append(num)
    elif re.match('.*\!KU\( curlyK\(~K_1_1\).*', line): rank[107].append(num)
    elif re.match('.*\!KU\( multp\(~y,.*', line): rank[107].append(num)
    elif re.match('.*\!KU\( ~y \)', line): rank[107].append(num)
    elif re.match('.*\!KU\(.*curlyK\(~K_1_1\).*', line): rank[106].append(num)
    elif re.match('.*\!KU\( plus\(r_cv.*multp\(H_n_2.*~f\)', line): rank[106].append(num)
    elif re.match('.*\!KU\( plus\(r_cv.*multp\(H_n_2.*~f.1\)', line): rank[106].append(num)
    elif re.match('.*\!KU\( plus\(multp\(~x,.*', line): rank[106].append(num)
    elif re.match('.*\!KU\( multp\(~x,.*', line): rank[106].append(num)
    elif re.match('.*\!KU\( multp\(H_n_2.*~f\)', line): rank[106].append(num)
    elif re.match('.*\!KU\( multp\(H_n_2.*~f.1\)', line): rank[106].append(num)
    elif re.match('.*\!KU\( ~f \)', line): rank[106].append(num)
    elif re.match('.*\!KU\( ~f.1 \)', line): rank[106].append(num)
    elif re.match('.*\!KU\( ~x \)', line): rank[106].append(num)
    elif re.match('.*\!KU\(.*<\'1\'.*~.*~.*', line): rank[101].append(num)
    elif re.match('.*\!KU\( senc.*~.*~.*', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~TPM_EK.*', line): rank[100].append(num)
    elif (not(re.match('.*KU\( Nonce\(~n_J\).*', line)) and not(re.match('.*splitEqs\(0\).*', line))): rank[1].append(num)
    elif (re.match('.*KU\( Nonce\(~n_J\).*', line) or (re.match('.*splitEqs\(0\).*', line))): rank[0].append(num)


elif lemma[0:19]=="oracle_auth_secrecy":
  print("applying oracle to "+lemma)
  for line in lines:
    num = line.split(':')[0]
    if re.match('.*In_S\( \$B,.*', line): rank[109].append(num)
    elif re.match('.*In_S\( \$A,.*', line): rank[109].append(num)
    elif re.match('.*In_S\( \$AS,.*', line): rank[109].append(num)
    elif re.match('.*In_S\( \$PS,.*', line): rank[109].append(num)
    elif re.match('.*_State_.*', line): rank[109].append(num)
    elif re.match('.*\!Pk\(.*', line): rank[109].append(num)
    elif re.match('.*createDAAKey\'>', line): rank[108].append(num)
    elif re.match('.*createPrimary\'\)', line): rank[108].append(num)
    elif re.match('.*returnEK\'>', line): rank[108].append(num)
    elif re.match('.*returnDAAKey\'>', line): rank[108].append(num)
    elif re.match('.*In_S\(.*', line): rank[107].append(num)
    elif re.match('.*\!KU\( pk\( KDF_EK\(~TPM_EK.*', line): rank[100].append(num)
    elif re.match('.*\!KU\( KDF_EK\(~TPM_EK.*', line): rank[100].append(num)
    elif re.match('.*\!KU\( curlyK\(~K_2\) \)', line): rank[91].append(num)
    elif re.match('.*\!KU\( curlyK\(~K_1\) \)', line): rank[90].append(num)
    elif re.match('.*\!KU\( ~K_2 \)', line): rank[91].append(num)
    elif re.match('.*\!KU\( ~K_1 \)', line): rank[90].append(num)
    elif re.match('.*\!KU\( ~K \)', line): rank[90].append(num)
    elif re.match('.*\!KU\( plus\(r_cv.*multp\(H_n_2.*~f\)', line): rank[80].append(num)
    elif re.match('.*\!KU\( plus\(r_cv.*multp\(H_n_2.*~f.1\)', line): rank[80].append(num)
    elif re.match('.*\!KU\( plus\(multp\(~x,.*', line): rank[70].append(num)
    elif re.match('.*\!KU\( multp\(~x,.*', line): rank[85].append(num)
    elif re.match('.*\!KU\( multp\(~y,.*', line): rank[90].append(num)
    elif re.match('.*\!KU\( multp\(H_n_2.*~f\)', line): rank[70].append(num)
    elif re.match('.*\!KU\( multp\(H_n_2.*~f.1\)', line): rank[70].append(num)
    elif re.match('.*\!KU\( ~f \)', line): rank[105].append(num)
    elif re.match('.*\!KU\( ~f.1 \)', line): rank[105].append(num)
    elif re.match('.*\!KU\( ~x \)', line): rank[105].append(num)
    elif re.match('.*\!KU\( ~y \)', line): rank[105].append(num)
    elif re.match('.*\!KU\( ~s_2 \)', line): rank[105].append(num)
    elif re.match('.*\!KU\( ~s \)', line): rank[105].append(num)
    elif re.match('.*\!KU\( senc.*~.*~.*', line): rank[60].append(num)
    elif re.match('.*\!KU\( ~TPM_EK.*', line): rank[105].append(num)


elif lemma[0:14]=="oracle_SP4_Non":
  print("applying oracle to "+lemma)
  for line in lines:
    num = line.split(':')[0]
    if re.match('.*\!SignatureVerified.*', line): rank[108].append(num)
    elif re.match('.*Host_.*', line): rank[107].append(num)
    elif re.match('.*_State_.*', line): rank[106].append(num)
    elif re.match('.*\'ret_TPM2_Sign_2\'>', line): rank[105].append(num)
    elif re.match('.*\!KU\( ~y \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~r \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~f \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~l \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~m \)', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~r_cv.*', line): rank[100].append(num)
    elif re.match('.*\!KU\( ~TPM_EK_Seed.*', line): rank[100].append(num)
    elif re.match('.*\!KU\( multp\(plus\(~r_cv.*', line): rank[99].append(num)
    elif re.match('.*\!KU\( plus\(~r_cv.*', line): rank[99].append(num)
    elif re.match('.*\!KU\( H_n_2\(Nonce.*~.*~.*~.*~.*.~.*~.*.*', line): rank[98].append(num)
    elif re.match('.*\!KU\( multp\(H_n.*~.*~.*~.*~.*.~.*~.*.*', line): rank[98].append(num)
    elif re.match('.*\!KU\( Message\(~m\).*', line): rank[97].append(num)
    elif re.match('.*\!KU\( H_k_1\(H_k_9\(Message.*~f,.*', line): rank[97].append(num)
    elif re.match('.*\!KU\( H_k_9\(Message.*~f,.*', line): rank[97].append(num)
    elif re.match('.*\!KU\( H_k_1\(H_k_4.*~f,.*', line): rank[97].append(num)
    elif re.match('.*\!KU\( H_k_4\(.*~f,.*', line): rank[97].append(num)
    elif re.match('.*\!KU\( plus\(r_cv.*', line): rank[96].append(num)
    elif re.match('.*\!KU\( E_S.*',line): rank[95].append(num) 
    elif re.match('.*\!KU\( multp\(~l,.*multp\(~f.*', line): rank[95].append(num)
    elif re.match('.*\!KU\( multp\(~l,.*', line): rank[94].append(num)
    elif re.match('.*\!KU\( H_SHA256\(<\'DAA_public_data\'.*', line): rank[94].append(num)
    elif re.match('.*createPrimary.*', line): rank[93].append(num)
    elif re.match('.*returnEK\'>', line): rank[92].append(num)
    elif re.match('.*createDAAKey.*', line): rank[91].append(num)
    elif re.match('.*returnDAAKey\'>', line): rank[90].append(num)
    elif re.match('.*\!KU\( plus\(.*r_cv.*~f.*', line): rank[89].append(num)
    elif re.match('.*\!KU\( senc\(.*~r.*~.*~.*~.*~.*~.*~.*.~.*~.*', line): rank[89].append(num)
    elif re.match('.*\!KU\( H_n_2\(Nonce.*PkX.*~x.*PkY.*~y.*', line): rank[89].append(num)
    elif re.match('.*\!KU\(.*SHA256.*', line): rank[89].append(num)
    elif re.match('.*In_S\( \$AS, .*', line): rank[87].append(num)
    elif re.match('.*In_S\( \$PS, .*', line): rank[87].append(num)
    elif re.match('.*TPM2_ActivateCredentials\'>', line): rank[86].append(num)
    elif re.match('.*ret_TPM2_ActivateCredentials\'>', line): rank[85].append(num)
    elif re.match('.*TPM2_Commit\'>', line): rank[84].append(num)
    elif re.match('.*retTPM2_commit\'>', line): rank[83].append(num)
    elif re.match('.*TPM2_Hash\'>', line): rank[82].append(num)
    elif re.match('.*ret_TPM2_Hash\'>', line): rank[81].append(num)
    elif re.match('.*\'TPM2_Sign\'>', line): rank[80].append(num)
    elif re.match('.*ret_TPM2_Sign\'>', line): rank[79].append(num)
    elif re.match('.*\'TPM2_ActivateCredentials_2\'.*', line): rank[78].append(num)
    elif re.match('.*ret_TPM2_ActivateCredentials_2\'>', line): rank[77].append(num)
    elif re.match('.*TPM2_Commit_rand\'>', line): rank[76].append(num)
    elif re.match('.*ret_TPM2_Commit_rand\'>', line): rank[75].append(num)  
    elif re.match('.*TPM2_Hash_2\'>', line): rank[74].append(num)
    elif re.match('.*ret_TPM2_Hash_2\'>', line): rank[73].append(num) 
    elif re.match('.*\'TPM2_Sign_2\'>', line): rank[72].append(num)
    elif re.match('.*ret_TPM2_Sign_2\'>', line): rank[71].append(num)
    elif re.match('.*\!KU\( H_n_2\(Nonce\(rnd.*', line): rank[60].append(num)  
    elif re.match('.*\!KU\( multp\(~y.*', line): rank[60].append(num)
    elif re.match('.*\!KU\( multp\(multp\(~r.*', line): rank[40].append(num)
    elif re.match('.*\!KU\( KDF_EK\(~TPM_EK_Seed.*', line): rank[40].append(num)
    elif re.match('.*\!KU\( multp\(multp\(~r.*', line): rank[40].append(num)
    elif re.match('.*\!KU\( KDF_AES\(~TPM.*', line): rank[30].append(num)




else:
    print("not applying the rule")
    exit(0)

# Ordering all goals by ranking (higher first)
for listGoals in reversed(rank):
  for goal in listGoals:
    sys.stderr.write(goal)
    print(goal)
