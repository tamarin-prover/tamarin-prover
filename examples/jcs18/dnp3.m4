changequote(<!,!>)
changecom(<!@,@!>)
theory DNP3Asymm
begin
/*********************************************************
* ===============================
*  DNP3 Secure Authentication v5 
*   (With the Asymmetric Update Key Change Protocol included.)
* ===============================
* 
* Author: Martin Dehnel-Wild and Kevin Milner
* Date: Feb 2018
* Status: Final
*
* All results proven with tamarin-prover version 1.3.0
* (Branch: develop, commit 8e823691ad3325bce8921617b013735523d74557)
* https://github.com/tamarin-prover/tamarin-prover/tree/8e823691ad3325bce8921617b013735523d74557
* 
*********************************************************/

/********************************************************* 
*
* The major outline of the file is as follows:
* (We explain each section in a moment)
*
* - Adversary Rules
* - Auxiliary Rules
* - Initial Key Distribution
* - The 'Session Key Update Protocol'
* - The 'Critical ASDU Authentication Protocol'
*   - Including non-aggressive and aggressive modes
*   - And Control and Monitoring directions
* - The Update Key Change Protocol
*   - Including the Symmetric and Asymmetric protocols
*
*********************************************************

* For reference, the DNP3 standard can be found at:
    http://ieeexplore.ieee.org/document/6327578/
  Protocol definitions can be found in Chapter 7 of this document.
  All message formats are described in Appendix A.45.x where x is the
  object reference number. (e.g. g120v4 = Appendix A.45.4)


* Adversary Rules:
    These are key-reveal rules. These give the adversary the possibility
    of learning certain keys if they want, by transmitting 'Out' the key
    to the public (adversary controlled, Dolev-Yao) channel. The lemmas then
    restrict when these key reveal events are appropriate and acceptable,
    so this doesn't give the adversary un-restricted power to compromise
    keys as and when they want.
    It is worth noting that each of these adversary rules only ever compromise
    the specific key that they take as a premise; e.g. the Update_key_reveal
    rule does not compromise *all* Update Keys, but only the one it is
    considering at that specific point.

* Auxiliary Rules:
    The Authority_Symm_Key rule is used to act as a single point of
    Authority Key generation.
    The CountUp rule is used to increment any counters in the protocol.
    Instead of adding 1 to a number, we 'hash' the input value
    symbolically, (i.e. successor function) so 1 = val, 2 = h(val),
    3 = h(h(val)) etc.

* Keys and State / Initial_key_pre_distribution: 
    This rule effectively initiates the overall system, creating the user
    and outstation initial states, and distributing the initial symmetric
    update key to user and outstation, ready for them to run the Session
    Key (Initialisation and) Update Protocol. We also distribute user and
    outstation invariant terms from here too -- i.e. the long term
    Symmetric Authority Key, both the recipient's private key, and both
    parties' public keys. As these terms never change, we highlight them
    in a separate persistent fact which Tamarin can solve for easily.
    Each term or key is defined in line with the rule.

* Session Key Update Protocol
    This symmetric key transport protocol distributes session keys (CDSK
    and MDSK) from the user to the outstation. Its messages are described
    and detailed in line with the protocol.
    We give Appendix references for message formats inline with each rule;
    these are to be found in Appendix A.45.x (e.g. g120v4 = A.45.4).

* Critical ASDU Authentication Protocol
    This HMAC-based non-confidential protocol seeks to authenticate the
    validity of critical ASDU packets, which either request a change to
    operating parameters, or report on current status of a system.
    The protocol runs (at least once) as normal (non-aggressive) before
    the aggressive mode may be used. These models contain rules to send and
    receive each type of message while in the correct state.
    The protocol can also operate in two separate directions: control and
    monitoring. Rules are named with AX_Y_RuleDescription where X is the
    number of the rule, and Y is the direction of the protocol (C or M)
    We give Appendix references for message formats inline with each rule;
    these are to be found in Appendix A.45.x (e.g. g120v2 = A.45.2).

* Update Key Change Protocol
    This symmetric or asymmetric key-transport protocol is used to
    distribute new update keys to the user and outstation. While this is
    technically a 3-party protocol, we squash the rules U3, U4, and U5
    into a single Tamarin rule, as the User--Authority communication is
    out of scope for the DNP3: SAv5 specification. Collapsing these rules
    into one eases analysis, and models an authentic channel between these
    parties.
    We give Appendix references for message formats inline with each rule;
    these are to be found in Appendix A.45.x (e.g. g120v12 = A.45.12).

*********************************************************/

dnl // These m4 macros are used to prioritize (F_) or deprioritize (L_) facts in Tamarin's search heuristics.
define(AuthorityKey, F_AuthorityKey($*))
define(UpdateKey, F_UpdateKey($*))
define(OutstationInvariants, F_OutstationInvariants($*))
define(UserInvariants, F_UserInvariants($*))
define(UserMCSInvariant, F_UserMCSInvariant($*))
define(OutCCSInvariant, F_OutCCSInvariant($*))
define(OutSessKeys, F_OutSessKeys($*))
define(UserSessKeys, F_UserSessKeys($*))
define(OutstationState, L_OutstationState($*))
define(UserState, L_UserState($*))
define(OutSentKeyStatus, L_OutSentKeyStatus($*))
define(CounterValue, L_XCounterValue($*))
define(Counter, L_Counter($*))


builtins: hashing, symmetric-encryption, asymmetric-encryption, signing

// One-way HMAC function, which takes 2 terms as input.
functions: hmac/2

restriction Eq_testing: "All x y #i. Eq( x, y ) @ i ==> x = y"
restriction InEq_testing: "All x y #i. InEq( x, y ) @ i ==> not( x = y )"
restriction Unique_Pairings_id: "All x #i #j. Unique( x ) @ i & Unique( x ) @ j ==> #i = #j"
// This enforces that x and y are of distinct 'types': specifically in this case,
//  no outstation ID will end up being used as a user ID and vice versa
restriction USR_and_OutstationID_distinct: "All x y #i. Distinct( x, y ) @ i 
    ==> not( Ex #j z. Distinct( y, z ) @ j ) & not( Ex #j z. Distinct( z, x ) @ j )"

/*********************************************************
 * Adversary Rules
 *********************************************************/

// Reveal a specific Update Key.
rule Update_key_reveal:
    [ !UpdateKey( ~linkid, k ) ]
  --[ UpdateKeyReveal( k ) ]->
    [ Out( k ) ]

// Control Direction Session Key Reveal
// Takes in the fact of the CDSK from the S3_SKC_session_key_change rule
// Then outputs them again as a fact so that the Adversary can use it
rule cdsk_reveal:
    [ !CDSKToReveal( k1 ) ]
  --[ CDSKReveal( k1) ]->
    [ Out( k1 ) ]

// Monitoring Direction Session Key Reveal
// Takes in the fact of the MDSK from the S3_SKC_session_key_change rule
// Then outputs them again as a fact so that the Adversary can use it
rule mdsk_reveal:
    [ !MDSKToReveal( k1 ) ]
  --[ MDSKReveal( k1 ) ]->
    [ Out( k1 ) ]

// Symmetric Authority Key Reveal
rule authority_symm_key_reveal:
    [ !AuthorityKey( k1 ) ]
  --[ AuthorityKeyReveal( k1 ) ]->
    [ Out( k1 ) ]

// User's Asymmetric Private Key Reveal
rule user_asymm_priv_key_reveal:
    [ !UserPrivateKey( k1 ) ]
  --[ UserPrivateKeyReveal( k1 ) ]->
    [ Out( k1 ) ]

// Outstation's Asymmetric Private Key Reveal
rule outstation_asymm_priv_key_reveal:
    [ !OutstationPrivateKey( k1 ) ]
  --[ OutstationPrivateKeyReveal( k1 ) ]->
    [ Out( k1 ) ]


/*********************************************************
 * Auxiliary Rules
 *********************************************************/

// The Authority's single point of (symmetric) key generation.
rule Authority_Symm_Key:
    [ Fr( ~AK ) ]
  --[ AuthorityCertKey( ~AK ) ]->
    [ !AuthorityKey( ~AK ) ]

// Counter rule. We say that 1+1 = h(1) (e.g. successor function).
rule CountUp:
    [ Counter( ~id, val )
        ]
  --[ NewCounterValue( ~id, h( val ) ) ]->
    [ Counter( ~id, h( val ) )
    , CounterValue( ~id, h( val ) )
    , Out( h( val ) ) // So we can be sure counters are public
        ]

define(teleport, <!
/********************************************************************************************************************************************
 * Keys and State:
 * The Keys and State for each of the Outstation and User are passed between them by means of these Facts. 
 *  Names of the terms within rules may change, but the position of these terms within the facts will remain constant.
 * The UserState facts contain:
 *  UserState( ~UserIDInvariant, ~UserUpdateKeyInvariant, ~UserSessionKeyInvariant, ControlChallengeState, MonitorChallengeState,
 *                                                                                                      UserStateMachinePosition )
 * !UserInvariants( ~UserIDInvariant, ~AuthorityKey, $USR, $OutstationID, ~linkid )
 * !UserUpdateKey( ~UserIDInvariant, ~UserUpdateKeyInvariant, UpdateKey_i_USR_O, KeyChangeMethod, Auth/PubKeysUsedToChangeUpdateKey )
 *
 * The Outstation facts contain:
 * OutstationState( ~OutstationIDInvariant, KeySequenceNumberKSQ, ~OutstationUpdateKeyInvariant, ~OutstationSessionKeyInvariant,
 *                                                              ControlChallengeState, MonitoringChallengeState, OutstationStateMachinePosition )
 * !OutstationInvariants( ~OutstationIDInvariant, ~AuthorityKey, $USR, $OutstationID, ~linkid )
 * !OutSessKeys( ~OutstationIDInvariant, ~OutstationSessionKeyInvariant, 'OK', CDSK_i_USR_O, MDSK_i_USR_O )
 * , !OutUpdateKey( ~OutStationIDInvariant, ~OutStationUpdateKeyInvariant, ~UK_i_USR_O, KeyChangeMethod, Auth/PubKeysUsedToChangeUpdateKey )
 *
 * For 'StateMachinePosition', see Figures 10, 11, 12, and 13 of IEC/TS 62351-5 (pp 29-32). 
 *  This is just a string that says which state it's in, and therefore where it can move to.
 ********************************************************************************************************************************************/

// This is the initial Update Key distribution rule -- The Session Key Update Protocol then runs after this to Initialise the Session Keys.
rule Initial_key_pre_distribution:
    [ !AuthorityKey( ~AK ) // Receive Authority Key securely.
    , Fr( ~UK_i_USR_O )     // Generate first Update Key, between USR and Outstation (O)
    , Fr( ~uid ), Fr( ~oid ) // These two Fr() terms are Tamarin-specific, and used for injectivity.
    , Fr( ~uu), Fr( ~ou ), Fr( ~us ), Fr( ~os ) // These are for unifying the key source invariants
    , Fr( ~linkid )     // This is the unique shared 'link identifier' that the outstation and user should agree upon each session
    , Fr( ~user_priv_key )
    , Fr( ~outstation_priv_key )
        ]
  --[ // These Action Facts are the messages logged in the trace of a protocol, and the things over which we prove lemmas.
      Unique( < ~AK, $USR, $OUTSTATION > ) // The association of user number to outstation is unique *Per Authority Key*.
    , Unique( < ~AK, $OUTSTATION, $USR > )
    , Distinct( $USR, $OUTSTATION )

    , AuthorityCertKey( ~AK )
    , NewCounterValue( ~uid, '0' ), NewCounterValue( ~oid, '0' )
    , NewUpdateKey( ~linkid, ~UK_i_USR_O, 'Initial', 'usb_stick' )
    , InitialA3( ~uid )
    , InitialA3( ~oid )
    , Sourced_UpdateKey_for_skiup_lemma( ~linkid, ~UK_i_USR_O, 'Initial', 'usb_stick' )
    , Initial(~oid)
        ]->
    [ // We put cid and csq together in a single term so most rules can just pass it through
      UserState( ~uid, ~uu, ~us, < '0', 'none' >, < '0', 'none' >, 'Init' )
    , OutstationState( ~oid, '0', ~ou, ~os, < '0', 'none' >, < '0', 'none' >, 'SecurityIdle' )

    // These parts of state never change, so we mark them persistent
    , !UserInvariants( ~uid, ~AK, $USR, $OUTSTATION, ~linkid, ~user_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutstationInvariants( ~oid, ~AK, $USR, $OUTSTATION, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )

    // These hold the key state for each KSQ value
    , !UserUpdateKey( ~uid, ~uu, ~UK_i_USR_O, 'Initial', 'usb_stick' )
    , !OutUpdateKey( ~oid, ~ou, ~UK_i_USR_O, 'Initial', 'usb_stick' )
    , !UserSessKeys( ~uid, ~us, 'NOT_INIT', 'undefined', 'undefined', ~UK_i_USR_O, 'Initial', 'usb_stick' )
    , !OutSessKeys( ~oid, ~os, 'NOT_INIT', 'undefined', 'undefined', ~UK_i_USR_O, 'Initial', 'usb_stick' )

    // This is the last key status message, which the outstation is expected
    //  to accept key changes on, even if things have happened since it was sent
    , OutSentKeyStatus( ~oid, 'none' )

    // These are the counter facts, which will go into a special 'count up' rule
    //  so we can easily prove monotonicity (and therefore uniqueness) of counter values
    , Counter( ~uid, '0' ), Counter( ~oid, '0' )

    , !UpdateKey( ~linkid, ~UK_i_USR_O )   // These 4 are for e.g. adversary key-reveal events
    , !UserPrivateKey( ~user_priv_key )
    , !OutstationPrivateKey( ~outstation_priv_key )
        ]

/******************************************************************************************************************
 * Session Key Update Protocol
 ******************************************************************************************************************
 * Structure of the protocol is broadly: (after initial distribution for bootstrapping)
 *  S1: User sends a Session Key Status Request. This is unauthenticated and unencrypted.
        (Object g120v4, Appendix A.45.4)
 *  S2: Outstation sends the Session Key Status, and some challenge data (a fresh nonce, Fr( ~CD_j ) ) 
        (Object g120v5, Appendix A.45.5)
 *  S3: User sends a Session Key Change Request, which includes (notably) the new keys and the previous nonce,
 *      all encrypted with the agreed existing update key. (Object g120v6, Appendix A.45.6)
 *  S4: Outstation then sends another Session Key Status message, which increments the counter ( h(KSQ) )
 *      and sends new challenge data for use with further messages. (Also Object g120v5, Appendix A.45.5)
 *      We use the `GotSessKeysOutSt( CDSK_j_USR_O, MDSK_j_USR_O, $USR )` action to denote successful completion of
 *      this rule, and therefore the session key update protocol.
 *  S5: User receives the S4 message and check it all matches what they expect.
 ******************************************************************************************************************/

/*********************************************************
 * S1: Send `Session Key Status Request' (Object g120v4, Appendix A.45.4)
 * Sent by User
 *  - Contains: User Number
 *********************************************************/
rule S1_SKSR_session_key_status_request:
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, anystate )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
        ]
  --[ S1_trace( ~uid )   ]->
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SessionKeyChange' )
    
    , Out( $USR )
        ]

/*********************************************************
 * S2: Send `Session Key Status' Message (Object g120v5, Appendix A.45.5)
 * Sent by Outstation
 * Contains:
 * - Key Change Sequence Number
 * - User Number
 * - Key Status (e.g. 'OK', 'NOT_INIT')
 * - Challenge Data
 * - MAC Value (optional)
 *********************************************************/
rule S2_SKS_session_key_status:
    let SKSM_j = < h( KSQ ), $USR, keystatus, ~CD_j >
    in
    [ OutstationState( ~oid, KSQ,~ou,~os, < cCSQ, cChal >, < mCSQ, mChal >, 'SecurityIdle' )
    , OutSentKeyStatus( ~oid, lastkeystatus )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutSessKeys( ~oid, ~os, keystatus, CDSK, MDSK, UK_i_USR_O, update_key_method, auth_keys_used )
    , Fr( ~CD_j )
    , In( $USR )
        ]
  --[ S2_trace( ~oid )
        ]->
    [ OutstationState( ~oid, h( KSQ ), ~ou, ~os, < cCSQ, cChal >, < mCSQ, mChal >, 'SecurityIdle' )
    , OutSentKeyStatus( ~oid, SKSM_j )
    , Out( SKSM_j )
        ]
!>)

define(sesskeyteleport, <!
/*********************************************************
 * S3: Send `Session Key Change' Message (Object g120v6, Appendix A.45.6)
 * Sent by User
 * Contains:
 * - Key Change Sequence Number
 * - User Number
 * - Encrypted Key Wrap Data. This contains:
 *   - Control Direction Session Key
 *   - Monitoring Direction Session Key
 *   - Key Status Message: “All data in the session key status object most recently received from the outstation, KSQ first, not including any HMAC.”
 **********************************************************/

rule S3_SKC_session_key_change:
    let SKSM_j = < KSQ, $USR, keystatus, CD_j > // We'll let S3 change session keys regardless of keystatus
        SKCM_j = < KSQ, $USR,
             senc( < ~CDSK_j_USR_O, ~MDSK_j_USR_O, SKSM_j >, UK_i_USR_O ) > in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SessionKeyChange' )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !UserUpdateKey( ~uid, ~uu, UK_i_USR_O, update_key_method, auth_keys_used )
    , Fr( ~CDSK_j_USR_O ), Fr( ~MDSK_j_USR_O ) // The new session keys
    , Fr( ~newus )
    , In( SKSM_j )
        ]
  --[ SessKeys( ~CDSK_j_USR_O, ~MDSK_j_USR_O, $USR )
    , NewSKs( ~linkid, UK_i_USR_O, ~CDSK_j_USR_O, ~MDSK_j_USR_O, update_key_method, auth_keys_used )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O, update_key_method, auth_keys_used )
    , Sourced_UpdateKey_S3_for_new_lemma( ~linkid, UK_i_USR_O, update_key_method, auth_keys_used )
    , UpdateKeyUsedForSKs( ~linkid, UK_i_USR_O, ~CDSK_j_USR_O, ~MDSK_j_USR_O, update_key_method, auth_keys_used )
    , S3( ~uid, ~CDSK_j_USR_O, ~MDSK_j_USR_O )
    , S3_trace( ~uid )
        ]->
    [ // Update key state to a new one, although we are still in the waiting for confirmation state, with an oustanding challenge
      UserState( ~uid, ~uu, ~newus, cCS, mCS, < 'WaitForKeyChangeConfirmation', SKCM_j, ~CDSK_j_USR_O, ~MDSK_j_USR_O > )
    , !UserSessKeys( ~uid, ~newus, 'OK', ~CDSK_j_USR_O, ~MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , !CDSKToReveal( ~CDSK_j_USR_O )
    , !MDSKToReveal( ~MDSK_j_USR_O )
    , Out( SKCM_j )
        ]

/*********************************************************
 * S4: Send another `Session Key Status' Message' (Object g120v5, Appendix A.45.5)
 * Sent by Outstation
 * Contains: same as above, but with an HMAC of the previous message. HMAC keyed by the MDSK_j_USR_O
 *********************************************************/

rule S4_SKS_session_key_status:                                   // This message is the one that the outstation sends back
    let SKSM_j =  < KSQ, $USR, keystatus, CD_j >
        SKCM_j =  < KSQ, $USR, senc( < CDSK_j_USR_O, MDSK_j_USR_O, SKSM_j >, UK_i_USR_O ) >
        SKSM_j_plus_1 = < h( KSQ ), $USR, 'OK', ~CD_j_plus_1,     // SessionKeyStatus is now 'OK' as keys have been agreed
                          hmac( SKCM_j, MDSK_j_USR_O ) >          // HMAC of SKCM_j, keyed with MDSK_j_USR_O
    in
    [ OutstationState( ~oid, KSQ,~ou,~os, < cCSQ, cChal >, < mCSQ, mChal >, 'SecurityIdle' )
    , CounterValue( ~oid, h( cCSQ ) )
    , OutSentKeyStatus( ~oid, SKSM_j )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutUpdateKey( ~oid, ~ou, UK_i_USR_O, update_key_method, auth_keys_used )
    , Fr( ~CD_j_plus_1 )
    , Fr( ~newos )
    , In( SKCM_j )
        ]
  --[ GotSessKeysOutSt( ~linkid, CDSK_j_USR_O, MDSK_j_USR_O, $USR )
    , CSQ( ~oid, h( cCSQ ) )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O, update_key_method, auth_keys_used )
    , Sourced_SKs( ~linkid, UK_i_USR_O, CDSK_j_USR_O, MDSK_j_USR_O, update_key_method, auth_keys_used )
    , UpdateKeyUsedForSKs( ~linkid, UK_i_USR_O, CDSK_j_USR_O, MDSK_j_USR_O, update_key_method, auth_keys_used )
    , S4_trace( ~oid )
        ]->
    [ // Drop last challenge on key update
      OutstationState( ~oid, h( KSQ ), ~ou, ~newos, < h( cCSQ ), 'none' >, < h( mCSQ ), 'none' >, 'SecurityIdle' )
    , OutSentKeyStatus( ~oid, SKSM_j_plus_1 )
    , !OutSessKeys( ~oid, ~newos, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , Out( SKSM_j_plus_1 )
        ]
!>)

define(s5teleport, <!
/*********************************************************
 * S5: User receive SKS confirmation message from Outstation
 *********************************************************/

rule S5_receive_SKS_confirmation:
    let SKSM_j_plus_1 = < KSQ, $USR, 'OK', CD_j_plus_1,        // SessionKeyStatus is now 'OK' as keys have been agreed
                           hmac( SKCM_j, MDSK_j_USR_O ) >      // HMAC of SKCM_j, keyed with ~MDSK_j_USR_O_j_USR_O
    in
    [ UserState( ~uid, ~uu, ~us, < cCSQ, cChal >, < mCSQ, cChal >, < 'WaitForKeyChangeConfirmation', SKCM_j, CDSK_j_USR_O, MDSK_j_USR_O > )
    , CounterValue( ~uid, h( mCSQ ) )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~cid )
    , In( SKSM_j_plus_1 )
        ]
    --[ GotSessKeysUser( ~linkid, CDSK_j_USR_O, MDSK_j_USR_O, $USR )
    , CSQ( ~uid, h( mCSQ ) )
    , S5( ~uid, 'control', CDSK_j_USR_O, MDSK_j_USR_O )
    , S5_trace( ~uid )
        ]->
    [ // Last challenge is dropped on a key update
      UserState( ~uid, ~uu, ~us, < h( cCSQ ), 'none'>, < h( mCSQ ), 'none' >, 'SecurityIdle' )
        ]
!>)
/******************************************************************************************************************
 * Critical ASDU Authentication Protocol
 *
 * An ASDU is a request for a change, or a request for information
 * The protocol is not secret, but needs to be authenticated to
 *  ensure that an attacker can't inject false requests or changes.
 *
 * Broad overview of protocol:
 *  A1: User sends a critical ASDU. This says something like "increase voltage to over 9,000". Unauthenticated.
 *  A2: Outstation sends back an 'Authentication Challenge' message containing a counter, and a fresh nonce (CD).
 *      (Object g120v1, Appendix A.45.1)
 *  A3: User sends an 'Authentication Reply' to the challenge; this is a MAC of the previous message
 *      (including challenge data), the ASDU in question, and the symmetric update key.
 *      (Object g120v2, Appendix A.45.2)
 *  A4: Outstation receives the message from the User and either accepts or rejects it.
 ******************************************************************************************************************/

/********************************************************* 
 * A1 rule omitted, because it sends a public request 
 * and isn't involved in the challenge construction.
 *********************************************************/

/*********************************************************
 * A2: Authentication Challenge (Control Direction)
 * Outstation ('challenger') sends back an Authentication Challenge object upon receiving ASDU
 * (Object g120v1, Appendix A.45.1)
 **********************************************************/
rule A2_C_AC_Authentication_Challenge:
    let AC = < h( cCSQ ), $USR, ~CD > in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < cCSQ, cChal >, mCS, 'SecurityIdle')
    , CounterValue( ~oid, h( cCSQ ) )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~CD )
        ]
  --[ CSQ( ~oid, h( cCSQ ) )
    , A2_nonaggressive( ~oid, 'control', ~CD )
    , A2_trace( ~oid )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < cCSQ, cChal >, mCS, < 'WaitForReply', < h( cCSQ ), AC > > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, < cCSQ, cChal >, mCS, < h( cCSQ ), AC > )
    , !OutCCSInvariant( ~oid, ~os, AC )
    , Out( AC )
        ]

define(acteleport, <!
/*********************************************************
 * A3: Authentication Reply (Control Direction)
 * User replies with an Authentication Reply object upon receiving the AC
 * Now the real message where the ASDU is involved!
 * (Object g120v2, Appendix A.45.2)
 **********************************************************/
rule A3_C_AR_Authentication_Reply:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac( < CSQ, AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , Fr( ~cinvar )
    , In( AC )
        ]
  --[ SentASDU( ~linkid, AR, 'normal', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , A3_session_keys( ~linkid, CDSK_j_USR_O, MDSK_j_USR_O, update_key_method, auth_keys_used )
    , AuthReply( AC, $ASDU, CDSK_j_USR_O )
    , A3( ~uid, 'control', CDSK_j_USR_O, MDSK_j_USR_O )
    , A3_nonaggressive( ~uid, 'control', CDSK_j_USR_O, MDSK_j_USR_O, CD )
    , A3_trace( ~uid )
        ]->
    [ // Overwrite previous 'last C challenge data' with newly received value
      UserState( ~uid, ~uu, ~us, < CSQ, ~cinvar, AC >, mCS, 'SecurityIdle' )
    , !UserCCSInvariant( ~uid, ~us, ~cinvar, AC )
    , Out( AR )
        ]

/*********************************************************
 * A3: Authentication Aggressive Mode Request (Control Direction)
 * This is an Aggressive mode request sent by the User to the Outstation,
 * and can only be accepted after the non-aggressive mode of the protocol
 * has finished at least once.
 * (Object g120v3, Appendix A.45.3)
 **********************************************************/
rule A3_C_AR_Authentication_Aggressive:
    let cChal = < CSQ, $USR, CD >
        AR = < h( cCSQ ), $USR, hmac( < 'amode', h( cCSQ ), cChal, $ASDU >, CDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, < cCSQ, ~cinv, cChal >, mCS, 'SecurityIdle' )
    , !UserCCSInvariant( ~uid, ~us, ~cinv, cChal )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
        ]
  --[ SentASDU( ~linkid, AR, 'aggressive', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , AuthReply( cChal, $ASDU, CDSK_j_USR_O )
    , A3( ~uid, 'control', CDSK_j_USR_O, MDSK_j_USR_O )
    , A3_aggressive( ~uid, 'control', CDSK_j_USR_O, MDSK_j_USR_O, CD )
    , A3_Aggr_trace( ~uid )
        ]->
    [ UserState( ~uid, ~uu, ~us, < h( cCSQ ), ~cinv, cChal >, mCS, 'SecurityIdle' )
    , Out( AR )
        ]

/*********************************************************
 * A4: Receive Authentication Challenge (Control Direction)
 * The Outstation receives the Authentication Challenge (MAC'd value of the ASDU)
 *  in the non-aggressive mode from the user, and decides whether to accept it or not.
 **********************************************************/
rule A4_receive_C_AC_of_ASDU:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac( < CSQ, AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, < 'WaitForReply', < CSQ, AC > > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, cCS, mCS, < CSQ, AC > )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'normal', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , A4_C_FINISH()
    , A4_trace( ~oid )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, 'SecurityIdle' )
        ]

/*********************************************************
 * A4: Receive Aggressive Mode Request while in 'SecyurityIdle' State (Control Direction)
 * The Outstation receives an Aggressive mode request from the User and decides whether
 * to accept it or not.
 * The Outstation can receive it in either the 'WaitForReply' or 'SecurityIdle' states,
 *  where WaitForReply drops the previous message. In 'SecurityIdle', we need to get the
 *  next counter value to check the received CSQ
 **********************************************************/
rule A4_idle_receive_C_AC_aggressive:
    let AR = < h( CSQ ), $USR, hmac( < 'amode', h( CSQ ), AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, 'SecurityIdle' )
    , CounterValue( ~oid, h( CSQ ) )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , !OutstationInvariants( ~oid, AK , $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutCCSInvariant( ~oid, ~os, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , CSQ( ~oid, h( CSQ ) )
    , InEq( AC, 'none' )
    , A4_idle_aggr_receive( ~oid )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < h( CSQ ), AC >, mCS, 'SecurityIdle' ) 
        ]

// As above. In WaitForReply, we've already increased the CSQ when sending out the previous challenge
rule A4_waiting_receive_C_AC_aggressive:
    let AC = < h( CSQ ), $USR, CD >
        AR = < h( CSQ ), $USR, hmac( < 'amode', h( CSQ ), AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, < 'WaitForReply', newChal > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, newChal )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , !OutCCSInvariant( ~oid, ~os, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , InEq( AC, 'none' )
    , A4_waiting_aggr_receive( ~oid )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < h( CSQ ), AC >, mCS, 'SecurityIdle' )
        ]

// If the Outstation's timeout (arbitrary) for WaitForReply is exceeded, it returns to the 'SecurityIdle' state.
rule A_OutstationWaitForReply_TimeoutorError:
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, < 'WaitForReply', newChal > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, cCS, mCS, newChal ) ]
  -->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, newChal, mCS, 'SecurityIdle' )
        ]

!>)
/*************************************************
 * Critical ASDU Protocol, Monitoring direction
 *************************************************/

/*********************************************************
 * A1 rule omitted, because it sends a public request 
 * and isn't involved in the challenge construction.
 *********************************************************/

/*********************************************************
 * A2: Authentication Challenge (Monitoring Direction)
 * User ('challenger') sends back an authentication challenge object upon receiving ASDU
 * (Object g120v1, Appendix A.45.1)
 **********************************************************/

rule A2_M_AC_Authentication_Challenge:
    let AC = < h( mCSQ ), $USR, ~CD > in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, 'SecurityIdle' )
    , CounterValue( ~uid, h( mCSQ ) )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~CD )
        ]
  --[ CSQ( ~uid, h( mCSQ ) )
    , A2_nonaggressive( ~uid, 'monitor', ~CD )
    , A2_M_trace( ~uid )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < 'WaitForReply', < h( mCSQ ), AC > > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < h( mCSQ ), AC > )
    , !UserMCSInvariant( ~uid, ~us, AC )
    , Out( AC )
        ]


define(amteleport, <!
/*********************************************************
 * A3: Authentication Reply (Monitoring Direction)
 * Outstation replies with an Authentication Reply object upon receiving the AC
 * (Object g120v2, Appendix A.45.2)
 **********************************************************/
rule A3_M_AR_Authentication_Reply:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac(< CSQ, AC, $ASDU >, MDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, 'SecurityIdle')
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , Fr( ~cinv )
    , In( AC )
        ]
  --[ SentASDU( ~linkid, AR, 'normal', 'monitor')
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , AuthReply( AC, $ASDU, MDSK_j_USR_O )
    , A3( ~oid, 'monitor', CDSK_j_USR_O, MDSK_j_USR_O )
    , A3_nonaggressive( ~oid, 'monitor', CDSK_j_USR_O, MDSK_j_USR_O, CD )
    , A3_M_trace( ~oid )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, < CSQ, ~cinv, AC >, 'SecurityIdle' )
    , !OutMCSInvariant( ~oid, ~os, ~cinv, AC )
    , Out( AR )
        ]

/*********************************************************
 * A3: Authentication Aggressive Mode Request (Monitoring Direction)
 * This is an Aggressive mode request sent by the Outstation to the User,
 * and can only be accepted after the non-aggressive mode of the protocol
 * has finished at least once.
 * (Object g120v3, Appendix A.45.3)
 **********************************************************/
rule A3_M_AR_Authentication_Aggressive:
    let mChal = < CSQ, $USR, CD >
        AR = < h( mCSQ ), $USR, hmac( < 'amode', h( mCSQ ), mChal, $ASDU >, MDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, < mCSQ, ~cinv, mChal >, 'SecurityIdle' )
    , !OutMCSInvariant( ~oid, ~os, ~cinv, mChal )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
        ]
  --[ SentASDU( ~linkid, AR, 'aggressive', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , AuthReply( mChal, $ASDU, MDSK_j_USR_O )
    , A3( ~oid, 'monitor', CDSK_j_USR_O, MDSK_j_USR_O )
    , A3_aggressive( ~oid, 'monitor', CDSK_j_USR_O, MDSK_j_USR_O, CD )
    , A3_M_Aggr_trace( ~oid )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, < h( mCSQ ), ~cinv, mChal >, 'SecurityIdle' )
    , Out( AR )
        ]

/*********************************************************
 * A4: Receive Authentication Challenge (Monitoring Direction)
 * The User receives the Authentication Challenge (MAC'd value of the ASDU)
 *  in the non-aggressive mode from the Outstation, and decides whether to accept it or not.
 **********************************************************/
rule A4_receive_M_AC_of_ASDU:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac( < CSQ, AC, $ASDU >, MDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < 'WaitForReply', < CSQ, AC > > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < CSQ, AC > )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'normal', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , A4_M_FINISH()
    , A4_M_trace( ~uid )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < CSQ, AC >, 'SecurityIdle' )
        ]

/*********************************************************
 * A4: Receive Aggressive Mode Request while in 'SecyurityIdle' State (Monitoring Direction)
 * The User receives an Aggressive mode request from the Outstation and decides whether
 * to accept it or not.
 * The User can receive it in either the 'WaitForReply' or 'SecurityIdle' states,
 *  where WaitForReply drops the previous message. In 'SecurityIdle', we need to get the
 *  next counter value to check the received CSQ.
 **********************************************************/
rule A4_idle_receive_M_AC_aggressive:
    let AR = < h( mCSQ ), $USR, hmac( < 'amode', h( mCSQ ), mChal, $ASDU >, MDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, 'SecurityIdle' )
    , CounterValue( ~uid, h( mCSQ ) )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , !UserMCSInvariant( ~uid, ~us, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , CSQ( ~uid, h( mCSQ ) )
    , InEq( mChal, 'none' )
    , A4_M_idle_aggr_receive( ~uid )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < h( mCSQ ), mChal >, 'SecurityIdle' )
        ]

// As above. In WaitForReply, we've already increased the CSQ when sending out the previous challenge
// User does *not* leave 'WaitForReply' upon receiving an Aggressive Mode Request
rule A4_waiting_receive_M_AC_aggressive:
    let AR = < h( mCSQ ), $USR, hmac( < 'amode', h( mCSQ ), mChal, $ASDU >, MDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < 'WaitForReply', newChal > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, newChal )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , !UserMCSInvariant( ~uid, ~us, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O, UK_i_USR_O, update_key_method, auth_keys_used )
    , InEq( mChal, 'none' )
    , A4_M_waiting_aggr_receive( ~uid )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < h( mCSQ ), mChal >, 'SecurityIdle' )
        ]

// If the User's timeout (arbitrary) for WaitForReply is exceeded, it returns to the 'SecurityIdle' state.
rule A_UserWaitForReply_Timeout:
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForReply', newChal > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, mCS, newChal )
        ]
  -->
    [ UserState( ~uid, ~uu, ~us, cCS, newChal, 'SecurityIdle' )
        ]
!>)
sesskeyteleport()

/******************************************************************************************************************
 * Update Key Change protocol
 * This protocol updates the update keys, and has both Symmetric and Asymmetric variants.
 ******************************************************************************************************************/

/********************************************************* 
 * U1 rule omitted here, because the challenge is not used in
 *  the response message from U2, so we can delay its
 *  generation to U3/U4/U5, and isn't involved in the
 *  challenge construction. (Object g120v11, Appendix A.45.11)
 *********************************************************/

/********************************************************* 
 * U2: Update Key Change Reply
 * (Object g120v12, Appendix A.45.12)
 * Outstation sends $USR (ID) and Challenge Data (CD_b) to User.
 * While the KSQ (Key Change Sequence Number) is included in
 *  the formal spec of this message, as a modelling choice we
 *  ensure it is publicly transmitted 'Out' elsewhere; as a
 *  result, we can (correctly) guarantee that all counters
 *  are already public.
 *********************************************************/
rule U2_UKCRp_Key_Change_Reply:
    [ !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~CD_b ) 
        ]
  --[ OutUpdateKeyChallengeActionFact( ~oid, ~linkid, ~CD_b ) 
    , U2_trace( ~oid )
        ]->
    [ OutUpdateKeyChallenge( ~oid, ~CD_b )
    , Out( < $USR, ~CD_b > )
        ]

/********************************************************************
* This is the rules U3, U4, and U5 combined. (Symmetric variant)
* (U5: Object g120v13, Appendix A.45.13) Communication between the
* Authority and User is out of scope for the DNP3 spec.
* User sends UKC to Outstation.
* This rule is run by the User talking to the Authority. The Authority
*  is assumed to have an authentic way to communicate the UKC message to
*  the user, this is captured by just accessing the Adversary Key directly.
* The new Update Key is symmetrically encrypted (UKC) with the Authority Key,
*  and HMAC'd (UKCCu) with the new Update Key itself.
* Note: the adversary can construct all KSQ values so it never needs 
*  to be Out'd from U2.
*********************************************************************/
rule U3_U4_U5_new_update_key_symmetric_mode:
    let UKCRp = < KSQ, $USR, CD_b >
        UKC   = < KSQ, $USR, senc( < $USR, ~UK_i_USR_O, CD_b >, ~AK ) >
        UKCCu = hmac( < $OSID, ~CD_a, CD_b, KSQ >, ~UK_i_USR_O )
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserInvariants( ~uid, ~AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , !AuthorityKey( ~AK )
    , Fr( ~CD_a )
    , Fr( ~UK_i_USR_O )
    , In( UKCRp )
        ]
  --[ NewUpdateKey( ~linkid, ~UK_i_USR_O, 'Symmetric', ~AK )
    , U345_symm_trace( ~uid )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForKCC', UKCCu > )
    , F_WaitForKCC( ~uid, ~uu, ~us, cCS, mCS, UKCCu )
    , !UpdateKey( ~linkid, ~UK_i_USR_O )
    , Out( < ~CD_a, UKC, UKCCu > )
        ]

/********************************************************************
* Asymmetric version of U3, U4, and U5, as above.
* User sends UKC to Outstation.
* As the spec says the User/Authority communication is out of scope,
*  we model the message from Authority to the User as being over a
*  private channel.
* In contrast to the previous rule, the new Update Key is asymmetrically
*  encrypted (UKC) with the recipient's (Outstation's) Public Key, and
*  signed (UKCSu) with the User's Private Key.
*********************************************************************/
rule U3_U4_U5_new_update_key_asymmetric_mode:
    let UKCRp = < KSQ, $USR, CD_b >
        UKC   = < KSQ, $USR, aenc( < $USR, ~UK_i_USR_O, CD_b >, pk( ~outstation_priv_key ) ) >
        UKCSu = sign( < < $OSID, ~CD_a, CD_b, KSQ >, aenc( < $USR, ~UK_i_USR_O, CD_b >, pk( ~outstation_priv_key ) ) >, ~user_priv_key )
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserInvariants( ~uid, ~AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~CD_a )
    , Fr( ~UK_i_USR_O )
    , In( UKCRp )
        ]
  --[ NewUpdateKey( ~linkid, ~UK_i_USR_O, 'Asymmetric', < ~outstation_priv_key, ~user_priv_key > )
    , LinkAndOutstationPrivKey( ~linkid, ~outstation_priv_key )
    , U345_asymm_trace( ~uid )
    // We need to have the secrecy of whatever the user thinks the outstation's private key is, i.e. that the adversary hasn't 
    //  revealed the private half of the thing that the user is encrypting it under
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForKCC', UKCSu > )
    , F_WaitForKCC( ~uid, ~uu, ~us, cCS, mCS, UKCSu )
    , !UpdateKey( ~linkid, ~UK_i_USR_O )
    , Out( < ~CD_a, UKC, UKCSu > )
        ]

s5teleport()

teleport()

acteleport()

amteleport()

/********************************************************* 
 * U6: Update Key Change Confirmation
 * (Object g120v15, Appendix A.45.15)
 * Outstation sends UKCC to User.
 * This is the symmetric confirmation message back from the
 *  Outstation, confirming successful receipt of the new
 *  Update Key. UKCCo is HMAC'd with the new Update Key, and
 *  the challenge data (CD_a and CD_b) is reversed in order so
 *  that a UKCCu cannot be replayed into a recipient expecting
 *  a UKCCo message.
 * Since we delayed the Key Change Sequence Number (KSQ) update
 *  to U6, we should expect h(KSQ) as input.
 *********************************************************/
rule U6_UKCC_Update_Key_Change_Confirmation:
    let UKC = < h( KSQ ), $USR, senc( < $USR, UK_i_USR_O, CD_b >, AK ) >
        UKCCu = hmac( < $OSID, CD_a, CD_b, h( KSQ ) >, UK_i_USR_O )
        UKCCo = hmac( < $USR, CD_b, CD_a, h( KSQ ) >, UK_i_USR_O )
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, 'SecurityIdle' )
    , OutUpdateKeyChallenge( ~oid, CD_b )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~newou )
    , In( CD_a )
    , In( < UKC, UKCCu > )
        ]
  --[ OutstationUpdateKeySession( ~oid, UKCCu, UKCCo )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O, 'Symmetric', AK )
    , Sourced_UpdateKey_for_skiup_lemma_U6( ~linkid, UK_i_USR_O, 'Symmetric', AK )
    , U6_symm_trace( ~oid )
        ]->
    [ OutstationState( ~oid, h( KSQ ), ~newou, ~os, cCS, mCS, 'SecurityIdle' )
    , !OutUpdateKey( ~oid, ~newou, UK_i_USR_O, 'Symmetric', AK )
    , Out( UKCCo )
        ]

/********************************************************* 
 * U7: Receive Update Key Change Confirmation from Outstation
 * (Symmetric variant)
 *********************************************************/
rule U7_receive_UKCC_from_Outstation:
    let UKCCu = hmac( < $OSID, CD_a, CD_b, KSQ >, UK_i_USR_O )
        UKCCo = hmac( < $USR, CD_b, CD_a, KSQ >, UK_i_USR_O )
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForKCC', UKCCu > )
    , F_WaitForKCC( ~uid, ~uu, ~us, cCS, mCS, UKCCu )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~newuu )
    , In( UKCCo )
        ]
  --[ UserUpdateKeySession( ~uid, UKCCu, UKCCo )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O, 'Symmetric', AK )
    , Sourced_UpdateKey_for_skiup_lemma( ~linkid, UK_i_USR_O, 'Symmetric', AK )
    , U7_symm_trace( ~uid )
        ]->
    [ UserState( ~uid, ~newuu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserUpdateKey( ~uid, ~newuu, UK_i_USR_O, 'Symmetric', AK )
        ]

/********************************************************* 
 * U6: Update Key Change Signature (Asymmetric)
 * (Object g120v14, Appendix A.45.14)
 * Even though this is the asymmetric version, the Outstation
 *  does *not* send a digital signature; only the User sends
 *  a digital signature; the Outstation's reply is a g120v15
 *  UKCC object.
 *********************************************************/
rule U6_UKCS_Update_Key_Change_Signature:
    let UKC   = < h( KSQ ), $USR, aenc( < $USR, UK_i_USR_O, CD_b >, pk( ~outstation_priv_key ) ) >
        UKCSMessage = < < $OSID, CD_a, CD_b, KSQ >, aenc( < $USR, UK_i_USR_O, CD_b >, pk( ~outstation_priv_key ) ) >
        UKCCo = hmac( < $USR, CD_b, CD_a, h( KSQ ) >, UK_i_USR_O )
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, 'SecurityIdle' )
    , OutUpdateKeyChallenge( ~oid, CD_b )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid, ~outstation_priv_key, 
                             pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~newou )
    , In( CD_a )
    , In( < UKC, ukcsu1 > )
        ]
  --[ Eq( verify( ukcsu1, UKCSMessage, pk( ~user_priv_key ) ), true )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O, 'Asymmetric', < ~outstation_priv_key, ~user_priv_key > )
    , Sourced_UpdateKey_for_skiup_lemma_U6( ~linkid, UK_i_USR_O, 'Asymmetric', < ~outstation_priv_key, ~user_priv_key > )
    , OutstationUpdateKeySession( ~oid, ukcsu1, UKCCo )
    , AsymmU6Finish( ~oid, ukcsu1, UKCCo )
    , LinkAndUserPrivKey( ~linkid, ~user_priv_key )
    , LinkAndOutstationPrivKey( ~linkid, ~outstation_priv_key )
    , U6_asymm_trace( ~oid )
        ]->
    [ OutstationState( ~oid, h( KSQ ), ~newou, ~os, cCS, mCS, 'SecurityIdle' )
    , !OutUpdateKey( ~oid, ~newou, UK_i_USR_O, 'Asymmetric', ~outstation_priv_key )
    , Out( UKCCo )
        ]

/********************************************************* 
 * U7: Receive Update Key Change Confirmation from Outstation
 * (Asymmetric variant)
 * While this rule still receives a UKCC message (which is
 *  symmetric), it is in the asymmetric mode, and therefore
 *  the UKCSu term is what's in its state.
 * ~CD_a and ~UK_i_USR_O are both marked fresh as they are in
 *  UserState (in UKCSu). Apparently only the User sends a
 *  UKCS Signature object (Appendix item g120v14); the
 *  Outstation replies with a g120v15 Update Key Change
 *  Confirmation message regardless of mode.
 *********************************************************/
rule U7_receive_UKCC_from_Outstation_asymm:
    let UKCCu = hmac( < $OSID, ~CD_a, CD_b, KSQ >, ~UK_i_USR_O )
        UKCCo = hmac( < $USR, CD_b, ~CD_a, h( KSQ ) >, ~UK_i_USR_O )
        UKCSu = sign( < < $OSID, ~CD_a, CD_b, KSQ >, aenc( < $USR, ~UK_i_USR_O, CD_b >, pk( ~outstation_priv_key ) ) >, ~user_priv_key )
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForKCC', UKCSu > )
    , F_WaitForKCC( ~uid, ~uu, ~us, cCS, mCS, UKCSu )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid, ~user_priv_key, 
                       pk( ~outstation_priv_key ), pk( ~user_priv_key ) )
    , Fr( ~newuu )
    , In( UKCCo )
        ]
  --[ UserUpdateKeySession( ~uid, UKCSu, UKCCo )
    , Sourced_UpdateKey( ~linkid, ~UK_i_USR_O, 'Asymmetric', < ~outstation_priv_key, ~user_priv_key > )
    , Sourced_UpdateKey_for_skiup_lemma( ~linkid, ~UK_i_USR_O, 'Asymmetric', ~outstation_priv_key )
    , AsymmU7Finish( ~uid, ~linkid, UKCSu, UKCCo )
    , LinkAndUserPrivKey( ~linkid, ~user_priv_key )
    , LinkAndOutstationPrivKey( ~linkid, ~outstation_priv_key )
    , U7_asymm_trace( ~uid )
        ]->
    [ UserState( ~uid, ~newuu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserUpdateKey( ~uid, ~newuu, ~UK_i_USR_O, 'Asymmetric',  ~outstation_priv_key )
        ]


/********************************************************
* Lemmas from here on in. These are the things we prove. 
*********************************************************/

/********************************************************
* Every counter value is unique.
* Status: Autoproves (fast)
*********************************************************/
lemma countervalue_uniqueness[reuse, use_induction]:
    "All id x #i #j.
        NewCounterValue( id, x ) @ i & NewCounterValue( id, x ) @ j ==> #i = #j"

/********************************************************
* Every used CSQ value (rather than just counter) is unique.
* Takes a while to do automatically, but can be solved by
*  picking the goals with counter-related names
* We include the saved manual proof instead.
*********************************************************/
lemma CSQ_Uniqueness[reuse, use_induction]:
    "All id csq #i #j.
        CSQ( id, csq ) @ i & CSQ( id, csq ) @ j ==> #i = #j"
induction
  case empty_trace
  by contradiction
next
  case non_empty_trace
  simplify
  solve( CSQ( id, csq ) @ #i )
    case A2_C_AC_Authentication_Challenge
    solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~oid, h(cCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case A2_M_AC_Authentication_Challenge
    solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~uid, h(mCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case A4_idle_receive_C_AC_aggressive
    solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~oid, h(CSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_XCounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      qed
    qed
  next
    case A4_idle_receive_M_AC_aggressive
    solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~uid, h(mCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case S4_SKS_session_key_status
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case S4_SKS_session_key_status
    solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~oid, h(cCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction /* from formulas */
        qed
      next
        case S5_receive_SKS_confirmation
        by solve( L_XCounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case S5_receive_SKS_confirmation
    solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~uid, h(mCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        solve( L_XCounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction /* from formulas */
        qed
      qed
    qed
  qed
qed


/********************************************************
 * Exists-trace for Session Key Update Protocol, Critical ASDU Auth Protocol,
 *  and the Asymmetric Update Key Change Protocol.
 * Status: Doesn't really autoprove, but see trace-existence.spthy for manual trace,
 * and trace.png for the output.
 * If you really want to re-create it, un-comment the following lemma and work your
 * way through it!
 ********************************************************/

/********************************************************
lemma exists_trace: exists-trace
    "Ex x x1 #a #b #c #d #e #f #g #i #j #k #l #m.
          not(Ex ak #r. AuthorityKeyReveal( ak ) @ #r )
        & not(Ex oprk #r. OutstationPrivateKeyReveal( oprk ) @ #r )
        & not(Ex uprk #r. UserPrivateKeyReveal( uprk ) @ #r )
        & not(Ex uk #r. UpdateKeyReveal( uk ) @ #r )
        & not(Ex cdsk #r . CDSKReveal( cdsk ) @ #r )
        & not(Ex mdsk #r . MDSKReveal( mdsk ) @ #r )
        & S1_trace(x) @ #a
        & S2_trace(x1) @ #b
        & S3_trace(x) @ #c
        & S4_trace(x1) @ #d
        & S5_trace(x) @ #e
        & A2_trace(x1) @ #f
        & A3_trace(x) @ #g
        & A4_trace(x1) @ #i
        & U2_trace(x1) @ #j
        & U345_asymm_trace(x) @ #k
        & U6_asymm_trace(x1) @ #l
        & U7_asymm_trace(x) @ #m
        // Below are restrictions to speed finding a trace manually
        & (All id id1 #j #k . Initial(id)  @ #j &
                              Initial(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . S1_trace(id)  @ #j &
                              S1_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . S2_trace(id)  @ #j &
                              S2_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . S3_trace(id)  @ #j &
                              S3_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . S4_trace(id)  @ #j &
                              S4_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . S5_trace(id)  @ #j &
                              S5_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . A2_trace(id)  @ #j &
                              A2_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . A3_trace(id)  @ #j &
                              A3_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . A4_trace(id)  @ #j &
                              A4_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . U2_trace(id)  @ #j &
                              U2_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . U345_asymm_trace(id)  @ #j &
                              U345_asymm_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . U6_asymm_trace(id)  @ #j &
                              U6_asymm_trace(id1) @ #k ==> #j = #k)
        & (All id id1 #j #k . U7_asymm_trace(id)  @ #j &
                              U7_asymm_trace(id1) @ #k ==> #j = #k)
    "
********************************************************/

/********************************************************
 * Every instance of a successfully authenticated ASDU 
 * (with fresh challenge data) is unique.
 * Status: Autoproves (fast)
 ********************************************************/
lemma sessions_unique[reuse]:
    "( All id ar mode mode2 direction #i #j.
        AuthASDU( id, ar, mode, direction ) @ i
      & AuthASDU( id, ar, mode2, direction ) @ j ==> #i = #j )"

/********************************************************
 * With no disallowed key-reveal actions, there must exist
 * an honest creation point for all new update keys.
 * Status: Autoproves (fast)
 ********************************************************/
lemma update_key_sourced[reuse,use_induction]:
    // If an there was a 'Sourced_UpdateKey' event for an update key encrypted using symmetric crypto 
    // (under 'ak'), and neither the authority key ('ak') used to encrypt it, or the update key itself ('uk') is revealed directly, 
    // this implies there must have been a NewUpdateKey action fact with the same update key, mode of encryption, and authority key
    "(All id uk ak #i.
            // UK was encrypted with AK & No compromise of AK
              not(Ex #r. AuthorityKeyReveal( ak ) @ #r & #r < #i )
            & not(Ex #r. UpdateKeyReveal( uk ) @ #r & #r < #i )
            & Sourced_UpdateKey( id, uk, 'Symmetric', ak ) @ #i
            ==> (Ex #j. NewUpdateKey( id, uk, 'Symmetric', ak ) @ #j & #j < #i)
        )
    // If an there was a 'Sourced_UpdateKey' event for a new update key encrypted using asymmetric crypto, and the secret signing key 'uprk' 
    // isn't revealed directly, this implies there must have been a NewUpdateKey action fact with the same update key, mode of encryption, 
    // and private keys
    // N.B. This property does NOT require secrecy of the new Update Key, making it strictly stronger than the symmetric property above.
    & (All id uk oprk uprk #i.
             not(Ex #r. UserPrivateKeyReveal( uprk ) @ #r & #r < #i )
            & Sourced_UpdateKey( id, uk, 'Asymmetric', < oprk, uprk > ) @ #i
            ==> (Ex #j. NewUpdateKey( id, uk, 'Asymmetric', < oprk, uprk > ) @ #j & #j < #i )
            )
    "

/********************************************************
 * Same as above, but agreement on keys rather than source.
 * Status: Autoproves (<1min)
 ********************************************************/
lemma update_key_agreement[reuse,use_induction]:
    "(All id id2 uk ak ak2 update_key_method #i #j.
              not(Ex #r. AuthorityKeyReveal( ak ) @ #r & #r < #i )
            & not(Ex #r. UpdateKeyReveal( uk ) @ #r & #r < #i )
            & Sourced_UpdateKey( id, uk, 'Symmetric', ak ) @ #i
            & NewUpdateKey( id2, uk, update_key_method, ak2 ) @ #j & #j < #i
            ==> ( id = id2 ) & ( ak = ak2 ) & ( update_key_method = 'Symmetric' )
        )
    & (All id id2 uk oprk oprk2 uprk uprk2 update_key_method #i #j.
             not(Ex #r. UserPrivateKeyReveal( uprk ) @ #r & #r < #i )
            & Sourced_UpdateKey( id, uk, 'Asymmetric', < oprk, uprk > ) @ #i
            & NewUpdateKey( id2, uk, update_key_method, < oprk2, uprk2 > ) @ #j & #j < #i
            ==> ( id = id2 ) & ( oprk = oprk2 ) & ( uprk = uprk2 ) & ( update_key_method = 'Asymmetric' )
            )
    "

/********************************************************
 * Update Key Secrecy
 * Status: Autoproves (fast)
 ********************************************************/
lemma update_key_secrecy[use_induction]:
    // If the initial update key isn't explicitly revealed, this implies the adversary doesn't know it.
    "(All id uk #i.
        not(Ex #r. UpdateKeyReveal( uk ) @ r)
        & NewUpdateKey( id, uk, 'Initial', 'usb_stick' ) @ #i
        ==> not(Ex #j. K( uk ) @ #j)
        )
    // If an update key encrypted using symmetric crypto (under 'ak') isn't revealed directly, and
    // the authority key 'ak' used to encrypt it also wasn't revealed, this implies the adversary doesn't know it.
    & (All id uk ak #i.
        // No AKR & no UKR & NewUpdateKey(uk) 
        not(Ex #r. AuthorityKeyReveal( ak ) @ r ) 
                & not(Ex #r. UpdateKeyReveal( uk ) @ r )
        & NewUpdateKey( id, uk, 'Symmetric', ak ) @ #i
        ==> not(Ex #j. K( uk ) @ #j)
        )
    // If an update key transported using asymmetric crypto isn't revealed directly, and
    // the private key used (by the outstation) to decrypt it isn't revealed, this implies the adversary doesn't know it.
    & (All id uk oprk uprk #i.
        not(Ex #r. OutstationPrivateKeyReveal( oprk ) @ r)
        & not(Ex #r. UpdateKeyReveal( uk ) @ r)
        & NewUpdateKey( id, uk, 'Asymmetric', < oprk, uprk > ) @ #i
        ==> not(Ex #j. K( uk ) @ #j)
        )
    "

/********************************************************
 * Session Key Secrecy
 * Status: Autoproves (fairly slowly!)
 ********************************************************/
lemma session_key_secrecy[use_induction]:
    // For all traces such that there are no Update Key, CDSK, or MDSK reveals, 
    // and that there was a "Sourced_SKs" Action Fact from the Initial Update Key,
    // This implies there is not a #j such that the adversary knows either CDSK or MDSK
    "(All id uk cdsk mdsk #i.
          not( Ex #r . UpdateKeyReveal( uk ) @ #r )
        & not( Ex #r . CDSKReveal( cdsk ) @ #r )
        & not( Ex #r . MDSKReveal( mdsk ) @ #r )
        & Sourced_SKs( id, uk, cdsk, mdsk, 'Initial', 'usb_stick' ) @ #i
        ==> not(( Ex #j . K( cdsk ) @ #j ) | ( Ex #j . K( mdsk ) @ #j ))
        )
    // For all traces such that there are no Authority Key, Update Key, CDSK, or MDSK reveals, 
    // Where 'ak' was the key used to encrypt the new Update Key 'uk'
    // and that there was a "Sourced_SKs" Action Fact in the symmetric mode
    // This implies there is not a #j such that the adversary knows either CDSK or MDSK
    & (All id uk ak cdsk mdsk #i.
          not(Ex #r. AuthorityKeyReveal( ak ) @ r )
        & not( Ex #r . UpdateKeyReveal( uk ) @ #r )
        & not( Ex #r . CDSKReveal( cdsk ) @ #r )
        & not( Ex #r . MDSKReveal( mdsk ) @ #r )
        & Sourced_SKs( id, uk, cdsk, mdsk, 'Symmetric', ak ) @ #i
        ==> not(( Ex #j . K( cdsk ) @ #j ) | ( Ex #j . K( mdsk ) @ #j ))
        )
    // For all traces such that there are no OutStationPrivateKey, Update Key, CDSK, or MDSK reveals, 
    // Where 'oprk' was the private key half of the public key used to encrypt the new Update Key 'uk'
    // and that there was a "Sourced_SKs" Action Fact in the asymmetric mode with these keys
    // This implies there is not a #j such that the adversary knows either CDSK or MDSK
    & (All id uk cdsk mdsk oprk #i.
          not(Ex #r. OutstationPrivateKeyReveal( oprk ) @ r )
        & not( Ex #r . UpdateKeyReveal( uk ) @ #r )
        & not( Ex #r . CDSKReveal( cdsk ) @ #r )
        & not( Ex #r . MDSKReveal( mdsk ) @ #r )
        & Sourced_SKs( id, uk, cdsk, mdsk, 'Asymmetric', oprk ) @ #i
        ==> not(( Ex #j . K( cdsk ) @ #j ) | ( Ex #j . K( mdsk ) @ #j ))
        )
    "

/********************************************************
 * Session Key (honest) Source
 * Status: Autoproves (slowly)
 ********************************************************/
lemma sessionkeys_sourced[reuse,use_induction]:
    // For all traces such that there are no Update Key, CDSK, or MDSK reveals, 
    // and that there was a "Sourced_SKs" Action Fact from the Initial Update Key,
    // This implies there must have been a NewSKs Action Fact at the point of generation of the new session keys (CDSK, MDSK) 
    // before the Sourced_SKs action, and this NewSKs Action Fact must have used the same update key 'uk', 
    // which was the initial update key set at first run.
    "(All id uk cdsk mdsk #i.
          not( Ex #r . UpdateKeyReveal( uk ) @ #r & #r < #i )
        & Sourced_SKs( id, uk, cdsk, mdsk, 'Initial', 'usb_stick' ) @ #i
        ==>( Ex #j . NewSKs( id, uk, cdsk, mdsk, 'Initial', 'usb_stick' ) @ #j & #j < #i )
        )
    // For all traces such that there are no Authority Key, Update Key, CDSK, or MDSK reveals, 
    // and that there was a "Sourced_SKs" Action Fact from an Update Key (symmetrically) encrypted under the Authority Key 'ak' 
    // This implies there must have been a NewSKs Action Fact at the point of generation of the new session keys (CDSK, MDSK) 
    // before the Sourced_SKs action, and this NewSKs Action Fact must have used the same update key 'uk', 
    // which was encrypted symmetrically under 'ak'.
    & (All id uk ak cdsk mdsk #i.
          not(Ex #r. AuthorityKeyReveal( ak ) @ r & #r < #i )
        & not( Ex #r . UpdateKeyReveal( uk ) @ #r & #r < #i )
        & Sourced_SKs( id, uk, cdsk, mdsk, 'Symmetric', ak ) @ #i
        ==>( Ex #j . NewSKs( id, uk, cdsk, mdsk, 'Symmetric', ak ) @ #j & #j < #i )
        )
    // For all traces such that there are no OutstationPrivateKey (oprk), Update Key, CDSK, or MDSK reveals, 
    // and that there was a "Sourced_SKs" Action Fact from an Update Key (asymmetrically) encrypted under the outstation's public key
    // This implies there must have been a NewSKs Action Fact at the point of generation of the new session keys (CDSK, MDSK) 
    // before the Sourced_SKs action, and this NewSKs Action Fact must have used the same update key 'uk', 
    // which was encrypted asymmetrically under the outstation's public key.
    & (All id uk cdsk mdsk oprk #i.
          not(Ex #r. OutstationPrivateKeyReveal( oprk ) @ r & #r < #i )
        & not( Ex #r . UpdateKeyReveal( uk ) @ #r & #r < #i )
        & Sourced_SKs( id, uk, cdsk, mdsk, 'Asymmetric', oprk ) @ #i
        ==>( Ex #j . NewSKs( id, uk, cdsk, mdsk, 'Asymmetric', oprk ) @ #j & #j < #i )
        )
    "
/********************************************************
 * Session Key Agreement
 * Status: Autoproves (fairly slowly)
 ********************************************************/
lemma skiup_agreement[reuse,use_induction]:
    "(All id id2 uk uk2 cdsk mdsk type source type2 source2 #i #j.
          not( Ex #r . UpdateKeyReveal( uk ) @ #r & #r < #i)
        & ( not(type = 'Asymmetric') | not(Ex #r. OutstationPrivateKeyReveal(source) @ r))
        & ( not(type = 'Symmetric')  | not(Ex #r. AuthorityKeyReveal(source) @ r))
        & Sourced_SKs( id, uk, cdsk, mdsk, type, source ) @ #i
        & NewSKs( id2, uk2, cdsk, mdsk, type2, source2 ) @ #j & #j < #i
        ==> ( id = id2 ) & ( uk = uk2 ) & (type = type2) & (source = source2)
    )"

/********************************************************
 * ASDU Agreement implies mode agreement
 * Status: Autoproves (very slowly!)
 ********************************************************/
lemma asdu_agreement_implies_mode_agreement[hide_lemma=update_key_sourced,hide_lemma=sessionkeys_sourced]:
    "// Initial UK with no runs of UKCP 
     // No compromise of AK, or Outstation/User Private Keys
      not(Ex ak #r. AuthorityKeyReveal( ak ) @ r )
    & not(Ex oprk #r. OutstationPrivateKeyReveal( oprk ) @ r )
    & not(Ex uprk #r. UserPrivateKeyReveal( uprk ) @ r )
    ==>
    // Implies that when the method used was 'usb_stick' to deliver the UK, which itself cannot be compromised,
    // We get agreement between all A3 and A4 rules on linkid, AR message, mode, and direction.
    ( All linkid ar mode direction linkid2 mode2 direction2 #i #j.
            ( All cdsk mdsk uk type source. UsingSessKeys( cdsk, mdsk, uk, type, source ) @ i
            ==> // The update key that was used to send out the current session keys cannot be revealed
                not( Ex #kr. UpdateKeyReveal( uk ) @ kr & #kr < #i )
                // If the direction is control, then then no reveal of the current CDSK
                & ( direction = 'control' ==> not( Ex #skr. CDSKReveal( cdsk ) @ skr & #skr < #i ) )
                // And if the direction is monitor, then no reveal of the current MDSK
                & ( direction = 'monitor' ==> not( Ex #skr. MDSKReveal( mdsk ) @ skr & #skr < #i ) ) )
            & AuthASDU( linkid, ar, mode, direction ) @ i
            & SentASDU( linkid2, ar, mode2, direction2 ) @ j & #j < #i
            ==> ( mode = mode2 ) & ( direction = direction2 ) & ( linkid = linkid2 )
      )"

/********************************************************
 * ASDU Aliveness: If an ASDU is authenticated, there must
 * have been an honest origin for the ASDU transmission.
 * Status: Autoproves (very slowly)
 ********************************************************/
lemma asdu_aliveness[use_induction,hide_lemma=update_key_sourced,hide_lemma=sessionkeys_sourced]:
    "not( Ex ak #r. AuthorityKeyReveal( ak ) @ r )
    & not(Ex oprk #r. OutstationPrivateKeyReveal( oprk ) @ r )
    & not(Ex uprk #r. UserPrivateKeyReveal( uprk ) @ r )
    ==>
    ( All linkid ar mode direction #i.
        ( All cdsk mdsk uk type source. UsingSessKeys( cdsk, mdsk, uk, type, source ) @ i
        ==> // The update key that was used to send out the current session keys cannot be revealed
            ( All uk #k. UpdateKeyUsedForSKs( linkid, uk, cdsk, mdsk, type, source ) @ k 
                ==> not( Ex #kr. UpdateKeyReveal( uk ) @ kr & #kr < #i ) )
            // If the direction is control, then then no reveal of the current CDSK
            & ( direction = 'control' ==> not( Ex #skr. CDSKReveal( cdsk ) @ skr & #skr < #i ) )
            // And if the direction is monitor, then no reveal of the current MDSK
            & ( direction = 'monitor' ==> not( Ex #skr. MDSKReveal( mdsk ) @ skr & #skr < #i ) ) )
        & AuthASDU( linkid, ar, mode, direction ) @ i
            ==> Ex #j. SentASDU( linkid, ar, mode, direction ) @ j & j < i
    )"

/********************************************************
 * ASDU Injective Agreement
 * Status: Autoproves (instantly)
 ********************************************************/
lemma asdu_injective_agreement:
    "not( Ex ak #r. AuthorityKeyReveal(ak) @ r )
    & not(Ex oprk #r. OutstationPrivateKeyReveal( oprk ) @ r )
    & not(Ex uprk #r. UserPrivateKeyReveal( uprk ) @ r )
    ==>
    ( All linkid ar mode direction #i #j.
        ( All cdsk mdsk uk type source. UsingSessKeys( cdsk, mdsk, uk, type, source ) @ i
        ==> // The update key that was used to send out the current session keys cannot be revealed
            ( All uk #k. UpdateKeyUsedForSKs( linkid, uk, cdsk, mdsk, type, source ) @ k 
                ==> not( Ex #kr. UpdateKeyReveal( uk ) @ kr & #kr < #i ) )
            // If the direction is control, then then no reveal of the current CDSK
            & ( direction = 'control' ==> not( Ex #skr. CDSKReveal( cdsk ) @ skr & #skr < #i ) )
            // And if the direction is monitor, then no reveal of the current MDSK
            & ( direction = 'monitor' ==> not( Ex #skr. MDSKReveal( mdsk ) @ skr & #skr < #i ) ) )
        & AuthASDU( linkid, ar, mode, direction ) @ i
        & SentASDU( linkid, ar, mode, direction ) @ j & j < i
    ==> not( Ex #k. AuthASDU( linkid, ar, mode, direction ) @ k & not( #k = #i ) )
    )"

end
// vim: ft=spthy
