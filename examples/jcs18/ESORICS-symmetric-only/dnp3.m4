changequote(<!,!>)
changecom(<!@,@!>)
theory DNP3
begin
/*********************************************************
* ===============================
*  DNP3 Secure Authentication v5
* ===============================
* 
* Author: Martin Dehnel-Wild and Kevin Milner
* Date: Apr 2017
* Status: Complete
* 
*********************************************************/

builtins: hashing, symmetric-encryption

functions: hmac/2

restriction InEq_testing: "All x y #i. InEq( x, y ) @ i ==> not( x = y )"
restriction Unique_Pairings_id: "All x #i #j. Unique( x ) @ i & Unique( x ) @ j ==> #i = #j"
// This enforces that x and y are of distinct 'types': specifically in this case,
//  no outstation ID will end up being used as a user ID and vice versa
restriction USR_and_OutstationID_distinct: "All x y #i. Distinct( x, y ) @ i 
    ==> not( Ex #j z. Distinct( y, z ) @ j ) & not( Ex #j z. Distinct( z, x ) @ j )"


// These are used to prioritize (F_) or deprioritize (L_) in Tamarin's heuristics
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
define(CounterValue, L_CounterValue($*))
define(Counter, L_Counter($*))

/*********************************************************
 * Adversary Rules
 *********************************************************/

rule Update_key_reveal:
    [ !UpdateKey( ~linkid, k ) ]
  --[ UpdateKeyReveal( k ), AdversaryRule( 'Update_key_reveal' ) ]->
    [ Out( k ) ]

rule cdsk_reveal:          // Takes in the fact of the CDSK from the S3_SKC_session_key_change rule
    [ !CDSKToReveal( k1 ) ]
  --[ CDSKReveal( k1), AdversaryRule( 'Update_key_reveal' ) ]->
    [ Out( k1 ) ]               // Then outputs them again as a fact so that the Adversary can use it

rule mdsk_reveal:          // Takes in the fact of the MDSK from the S3_SKC_session_key_change rule
    [ !MDSKToReveal( k1 ) ]
  --[ MDSKReveal( k1 ), AdversaryRule( 'Update_key_reveal' ) ]->
    [ Out( k1 ) ]               // Then outputs them again as a fact so that the Adversary can use it

rule authority_key_reveal:
    [ !AuthorityKey( k1 ) ]
  --[ AuthorityKeyReveal( k1 ), AdversaryRule( 'Update_key_reveal' ) ]->
    [ Out( k1 ) ]

/*********************************************************
 * Auxiliary Rules
 *********************************************************/

// The Authority's single point of key generation.
rule Authority_Key:
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
    , Out( h( val ) ) // Just so we can be sure counters are public
        ]

define(teleport, <!
/********************************************************************************************************************************************
 * Keys and State:
 * The Keys and State for each of the Outstation and User are passed between them by means of these Facts. 
 *  Names of the terms within rules may change, but the position of these terms within the facts will remain constant.
 * The UserState facts contain:
 *  UserState( ~UserIDInvariant, ~UserUpdateKeyInvariant, ~UserSessionKeyInvariant, ControlChallengeState, MonitorChallengeState,
 *                                                                                                      UserStateMachinePosition )
 * !UserInvariants( ~UserIDInvariant, ~AdversaryKey, $USR, $OutstationID, ~linkid )
 * !UserUpdateKey( ~UserIDInvariant, ~UserUpdateKeyInvariant, UK_i_USR_O )
 *
 * The Outstation facts contain:
 * OutstationState( ~OutstationIDInvariant, KeySequenceNumberKSQ, ~OutstationUpdateKeyInvariant, ~OutstationSessionKeyInvariant,
 *                                                              ControlChallengeState, MonitoringChallengeState, OutstationStateMachinePosition )
 * !OutstationInvariants( ~OutstationIDInvariant, ~AdversaryKey, $USR, $OutstationID, ~linkid )
 * !OutSessKeys( ~OutstationIDInvariant, ~OutstationSessionKeyInvariant, 'OK', CDSK_i_USR_O, MDSK_i_USR_O )
 *
 * For 'StateMachinePosition', see Figures 10, 11, 12, and 13 of IEC/TS 62351-5 (pp 29-32). 
 *  This is just a string that says which state it's in, and therefore where it can move to.
 ********************************************************************************************************************************************/

// This is the initial Update Keys -- Session Key Update Protocol then runs after this to Initialise the Session Keys.
rule Initial_key_pre_distribution:
    [ !AuthorityKey( ~AK ) // Receive Authority Key securely.
    , Fr( ~UK_i_USR_O )     // Generate first Update Key, between USR and Outstation (O)
    , Fr( ~uid ), Fr( ~oid ) // These two Fr() terms are Tamarin-specific, and for injectivity.
    , Fr( ~uu), Fr( ~ou ), Fr( ~us ), Fr( ~os ) // These are for unifying the key source invariants
    , Fr( ~linkid )     // This is the unique shared 'link identifier' that the outstation and user should agree upon each session
        ]
  --[ // The association of user number to outstation is unique *per authority key*. 
      Unique( < ~AK, $USR, $OUTSTATION > )
    , Unique( < ~AK, $OUTSTATION, $USR > )
    , Distinct( $USR, $OUTSTATION )

    , AuthorityCertKey( ~AK )
    , NewCounterValue( ~uid, '0' ), NewCounterValue( ~oid, '0' )
    , NewUpdateKey( ~linkid, ~UK_i_USR_O )
        ]->
    [ // We put cid and csq together in a single term so most rules can just pass it through
      UserState( ~uid, ~uu, ~us, < '0', 'none' >, < '0', 'none' >, 'Init' )
    , OutstationState( ~oid, '0', ~ou, ~os, < '0', 'none' >, < '0', 'none' >, 'SecurityIdle' )

    // These parts of state never change, so we mark them persistent
    , !UserInvariants( ~uid, ~AK, $USR, $OUTSTATION, ~linkid )
    , !OutstationInvariants( ~oid, ~AK, $USR, $OUTSTATION, ~linkid )

    // These hold the key state for each KSQ value
    , !UserUpdateKey( ~uid, ~uu, ~UK_i_USR_O ), !OutUpdateKey( ~oid, ~ou, ~UK_i_USR_O )
    , !UserSessKeys( ~uid, ~us, 'NOT_INIT', 'undefined', 'undefined' )
    , !OutSessKeys( ~oid, ~os, 'NOT_INIT', 'undefined', 'undefined' )

    // This is the last key status message, which the outstation is expected
    //  to accept key changes on, even if things have happened since it was sent
    , OutSentKeyStatus( ~oid, 'none' )

    // These are the counter facts, which will go into a special 'count up' rule
    //  so we can easily prove monotonicity (and therefore uniqueness) of counter values
    , Counter( ~uid, '0' ), Counter( ~oid, '0' )

    , !UpdateKey( ~linkid, ~UK_i_USR_O )   // For e.g. adversary key-reveal events
        ]

/******************************************************************************************************************
 * Session Key Update Protocol
 ******************************************************************************************************************
 * Structure of the protocol is broadly: (after initial distribution for bootstrapping)
 *  S1: User sends a Session Key Status Request. This is unauthenticated and unencrypted.
 *  S2: Outstation sends the Session Key Status, and some challenge data (a fresh nonce, Fr( ~CD_j ) )
 *  S3: User sends a Session Key Change Request, which includes (notably) the new keys and the previous nonce,
 *      all encrypted with the agreed existing update key.
 *  S4: Outstation then sends another Session Key Status message, which increments the counter ( h(KSQ) )
 *      and sends new challenge data for use with further messages.
 *      We use the `GotSessKeysOutSt( CDSK_j_USR_O, MDSK_j_USR_O, $USR )` action to denote successful completion of
 *      this rule, and therefore the session key update protocol.
 *  S5: User receives the S4 message and check it all lines up with what they remember.
 ******************************************************************************************************************/

/*********************************************************
 * Send `Session Key Status Request' (g120v4)
 * Sent by User
 *  - Contains: User Number
 *********************************************************/

rule S1_SKSR_session_key_status_request:
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, anystate )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
        ]
  --[   ]->
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SessionKeyChange' )
    , Out( $USR )
        ]

/*********************************************************
 * Send `Session Key Status' Message (g120v5)
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
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , !OutSessKeys( ~oid, ~os, keystatus, CDSK, MDSK )
    , Fr( ~CD_j )
    , In( $USR )
        ]
  --[
        ]->
    [ OutstationState( ~oid, h( KSQ ), ~ou, ~os, < cCSQ, cChal >, < mCSQ, mChal >, 'SecurityIdle' )
    , OutSentKeyStatus( ~oid, SKSM_j )
    , Out( SKSM_j )
        ]
!>)

define(sesskeyteleport, <!
/*********************************************************
 * Send `Session Key Change' Message (g120v6)
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
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , !UserUpdateKey( ~uid, ~uu, UK_i_USR_O )
    , Fr( ~CDSK_j_USR_O ), Fr( ~MDSK_j_USR_O ) // The new session keys
    , Fr( ~newus )
    , In( SKSM_j )
        ]
  --[ SessKeys( ~CDSK_j_USR_O, ~MDSK_j_USR_O, $USR )
    , NewSKs( ~linkid, UK_i_USR_O, ~CDSK_j_USR_O, ~MDSK_j_USR_O )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O )
    , UpdateKeyUsedForSKs( ~linkid, UK_i_USR_O, ~CDSK_j_USR_O, ~MDSK_j_USR_O )
        ]->
    [ // Update key state to a new one, although we are still in the waiting for confirmation state, with an oustanding challenge
      UserState( ~uid, ~uu, ~newus, cCS, mCS, < 'WaitForKeyChangeConfirmation', SKCM_j, ~CDSK_j_USR_O, ~MDSK_j_USR_O > )
    , !UserSessKeys( ~uid, ~newus, 'OK', ~CDSK_j_USR_O, ~MDSK_j_USR_O )
    , !CDSKToReveal( ~CDSK_j_USR_O )
    , !MDSKToReveal( ~MDSK_j_USR_O )
    , Out( SKCM_j )
        ]

/*********************************************************
 * Send another `Session Key Status' Message' (g120v5)
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
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , !OutUpdateKey( ~oid, ~ou, UK_i_USR_O )
    , Fr( ~CD_j_plus_1 )
    , Fr( ~newos )
    , In( SKCM_j )
        ]
  --[ GotSessKeysOutSt( CDSK_j_USR_O, MDSK_j_USR_O, $USR )
    , CSQ( ~oid, h( cCSQ ) )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O )
    , Sourced_SKs( ~linkid, UK_i_USR_O, CDSK_j_USR_O, MDSK_j_USR_O )
    , UpdateKeyUsedForSKs( ~linkid, UK_i_USR_O, CDSK_j_USR_O, MDSK_j_USR_O )
        ]->
    [ // Drop last challenge on key update
      OutstationState( ~oid, h( KSQ ), ~ou, ~newos, < h( cCSQ ), 'none' >, < h( mCSQ ), 'none' >, 'SecurityIdle' )
    , OutSentKeyStatus( ~oid, SKSM_j_plus_1 )
    , !OutSessKeys( ~oid, ~newos, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , Out( SKSM_j_plus_1 )
        ]
!>)

define(s5teleport, <!
/*********************************************************
 * User receive SKS confirmation message from Outstation
 *********************************************************/

  rule S5_receive_SKS_confirmation:
    let SKSM_j_plus_1 = < KSQ, $USR, 'OK', CD_j_plus_1,        // SessionKeyStatus is now 'OK' as keys have been agreed
                           hmac( SKCM_j, MDSK_j_USR_O ) >      // HMAC of SKCM_j, keyed with ~MDSK_j_USR_O_j_USR_O
    in
    [ UserState( ~uid, ~uu, ~us, < cCSQ, cChal >, < mCSQ, cChal >, < 'WaitForKeyChangeConfirmation', SKCM_j, CDSK_j_USR_O, MDSK_j_USR_O > )
    , CounterValue( ~uid, h( mCSQ ) )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , Fr( ~cid )
    , In( SKSM_j_plus_1 )
        ]
  --[ GotSessKeysUser( CDSK_j_USR_O, MDSK_j_USR_O, $USR )
    , CSQ( ~uid, h( mCSQ ) )
        ]->
    [ // Last challenge is dropped on a key update
      UserState( ~uid, ~uu,~us, < h( cCSQ ), 'none'>, < h( mCSQ ), 'none' >, 'SecurityIdle' )
        ]
!>)
/******************************************************************************************************************
 * Critical ASDU functionality
 *
 * An ASDU is a request for a change, or a request for information
 * The protocol is not secret, but needs to be authenticated to
 *  ensure that an attacker can't inject false requests or changes.
 ******************************************************************************************************************/

/******************************************************************************************************************
 * Broad overview of protocol:
 *  A1: User sends a critical ASDU. This says something like "increase voltage to over 9,000". Unauthenticated.
 *  A2: Outstation sends back a counter, and a fresh nonce (CD)
 *  A3: User sends a response to the challenge; this is a MAC of the previous message (including challenge data),
 *      the ASDU in question, and the symmetric update key
 *  A4: Outstation receives the message from the User and either accepts or rejects it.
 ******************************************************************************************************************/

// A1 Omitted, because it sends some public request and isn't involved in the challenge construction
// Outstation ('challenger') sends back an authentication challenge object upon receiving ASDU
rule A2_C_AC_Authentication_Challenge: // g120v1
    let AC = < h( cCSQ ), $USR, ~CD > in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < cCSQ, cChal >, mCS, 'SecurityIdle')
    , CounterValue( ~oid, h( cCSQ ) )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , Fr( ~CD )
        ]
  --[ CSQ( ~oid, h( cCSQ ) )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < cCSQ, cChal >, mCS, < 'WaitForReply', < h( cCSQ ), AC > > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, < cCSQ, cChal >, mCS, < h( cCSQ ), AC > )
    , !OutCCSInvariant( ~oid, ~os, AC )
    , Out( AC )
        ]

define(acteleport, <!
// Now the real message where the ASDU is involved
rule A3_C_AR_Authentication_Reply: // g120v2 
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac( < CSQ, AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , Fr( ~cinvar )
    , In( AC )
        ]
  --[ SentASDU( ~linkid, AR, 'normal', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , AuthReply( AC, $ASDU, CDSK_j_USR_O )
        ]->
    [ // Overwrite previous 'last C challenge data' with newly received value
      UserState( ~uid, ~uu, ~us, < CSQ, ~cinvar, AC >, mCS, 'SecurityIdle' )
    , !UserCCSInvariant( ~uid, ~us, ~cinvar, AC )
    , Out( AR )
        ]

rule A3_C_AR_Authentication_Aggressive:
    let AR = < h( cCSQ ), $USR, hmac( < 'amode', h( cCSQ ), cChal, $ASDU >, CDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, < cCSQ, ~cinv, cChal >, mCS, 'SecurityIdle' )
    , !UserCCSInvariant( ~uid, ~us, ~cinv, cChal )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
        ]
  --[ SentASDU( ~linkid, AR, 'aggressive', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , AuthReply( cChal, $ASDU, CDSK_j_USR_O )
        ]->
    [ UserState( ~uid, ~uu, ~us, < h( cCSQ ), ~cinv, cChal >, mCS, 'SecurityIdle' )
    , Out( AR )
        ]


// Outstation receives MAC'd value of the ASDU (non-agressive mode)
rule A4_receive_C_AC_of_ASDU:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac( < CSQ, AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, < 'WaitForReply', < CSQ, AC > > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, cCS, mCS, < CSQ, AC > )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'normal', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, 'SecurityIdle' )
        ]

// Aggressive mode, can receive in either WaitForReply or SecurityIdle, where waitforreply drops previous message
// In security idle, we need to get the next counter value to check the received CSQ
rule A4_idle_receive_C_AC_aggressive:
    let AR = < h( CSQ ), $USR, hmac( < 'amode', h( CSQ ), AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, 'SecurityIdle' )
    , CounterValue( ~oid, h( CSQ ) )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , !OutstationInvariants( ~oid, AK , $USR, $OSID, ~linkid )
    , !OutCCSInvariant( ~oid, ~os, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , CSQ( ~oid, h( CSQ ) )
    , InEq( AC, 'none' )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < h( CSQ ), AC >, mCS, 'SecurityIdle' ) 
        ]

// In waitforreply, we've already increased the CSQ when sending out the previous challenge
rule A4_waiting_receive_C_AC_aggressive:
    let AC = < h( CSQ ), $USR, CD >
        AR = < h( CSQ ), $USR, hmac( < 'amode', h( CSQ ), AC, $ASDU >, CDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, < 'WaitForReply', newChal > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, < CSQ, AC >, mCS, newChal )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , !OutCCSInvariant( ~oid, ~os, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'control' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , InEq( AC, 'none' )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, < h( CSQ ), AC >, mCS, 'SecurityIdle' )
        ]

rule A_OutstationWaitForReply_TimeoutorError:
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, < 'WaitForReply', newChal > )
    , F_OutWaitForReply( ~oid, KSQ, ~ou, ~os, cCS, mCS, newChal ) ]
  --[  ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, newChal, mCS, 'SecurityIdle' )
        ]

!>)
/*************************************************
 * Critical ASDU Protocol, Monitoring direction
 *************************************************/


// A1 Omitted, because it sends some public request and isn't involved in the challenge construction

// User ('challenger') sends back an authentication challenge object upon receiving ASDU
rule A2_M_AC_Authentication_Challenge: // g120v1
    let AC = < h( mCSQ ), $USR, ~CD > in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, 'SecurityIdle' )
    , CounterValue( ~uid, h( mCSQ ) )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , Fr( ~CD )
        ]
  --[ CSQ( ~uid, h( mCSQ ) )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < 'WaitForReply', < h( mCSQ ), AC > > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < h( mCSQ ), AC > )
    , !UserMCSInvariant( ~uid, ~us, AC )
    , Out( AC )
        ]


define(amteleport, <!
// Now the real message where the ASDU is involved
rule A3_M_AR_Authentication_Reply:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac(< CSQ, AC, $ASDU >, MDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, 'SecurityIdle')
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , Fr( ~cinv )
    , In( AC )
        ]
  --[ SentASDU( ~linkid, AR, 'normal', 'monitor')
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , AuthReply( AC, $ASDU, MDSK_j_USR_O )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, < CSQ, ~cinv, AC >, 'SecurityIdle' )
    , !OutMCSInvariant( ~oid, ~os, ~cinv, AC )
    , Out( AR )
        ]

rule A3_M_AR_Authentication_Aggressive:
    let AR = < h( mCSQ ), $USR, hmac( < 'amode', h( mCSQ ), mChal, $ASDU >, MDSK_j_USR_O ) >
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, < mCSQ, ~cinv, mChal >, 'SecurityIdle' )
    , !OutMCSInvariant( ~oid, ~os, ~cinv, mChal )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , !OutSessKeys( ~oid, ~os, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
        ]
  --[ SentASDU( ~linkid, AR, 'aggressive', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , AuthReply( mChal, $ASDU, MDSK_j_USR_O )
        ]->
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, < h( mCSQ ), ~cinv, mChal >, 'SecurityIdle' )
    , Out( AR )
        ]


// User receives MAC'd value of the ASDU (non-agressive mode)
rule A4_receive_M_AC_of_ASDU:
    let AC = < CSQ, $USR, CD >
        AR = < CSQ, $USR, hmac( < CSQ, AC, $ASDU >, MDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < 'WaitForReply', < CSQ, AC > > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < CSQ, AC > )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'normal', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < CSQ, AC >, 'SecurityIdle' )
        ]

// Aggressive mode, can receive in either WaitForReply or SecurityIdle, where waitforreply drops previous message
// In security idle, we need to get the next counter value to check the received CSQ
rule A4_idle_receive_M_AC_aggressive:
    let AR = < h( mCSQ ), $USR, hmac( < 'amode', h( mCSQ ), mChal, $ASDU >, MDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, 'SecurityIdle' )
    , CounterValue( ~uid, h( mCSQ ) )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , !UserMCSInvariant( ~uid, ~us, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , CSQ( ~uid, h( mCSQ ) )
    , InEq( mChal, 'none' )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < h( mCSQ ), mChal >, 'SecurityIdle' )
        ]

// In waitforreply, we've already increased the CSQ when sending out the previous challenge
// User does *not* leave wait for reply upon receiving an aggressive mode request
rule A4_waiting_receive_M_AC_aggressive:
    let AR = < h( mCSQ ), $USR, hmac( < 'amode', h( mCSQ ), mChal, $ASDU >, MDSK_j_USR_O ) >
    in
    [ UserState( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, < 'WaitForReply', newChal > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, < mCSQ, mChal >, newChal )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , !UserSessKeys( ~uid, ~us, 'OK', CDSK_j_USR_O, MDSK_j_USR_O )
    , !UserMCSInvariant( ~uid, ~us, AC )
    , In( AR )
        ]
  --[ AuthASDU( ~linkid, AR, 'aggressive', 'monitor' )
    , UsingSessKeys( CDSK_j_USR_O, MDSK_j_USR_O )
    , InEq( mChal, 'none' )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, < h( mCSQ ), mChal >, 'SecurityIdle' )
        ]

rule A_UserWaitForReply_Timeout:
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForReply', newChal > )
    , F_UserWaitForReply( ~uid, ~uu, ~us, cCS, mCS, newChal )
        ]
  --[   ]->
    [ UserState( ~uid, ~uu, ~us, cCS, newChal, 'SecurityIdle' )
        ]
!>)
sesskeyteleport()

/******************************************************************************************************************
 * Update Key Change protocol
 *  This protocol updates the update keys
 ******************************************************************************************************************/

// We exclude U1 because the challenge is not used in the response message from U2,
//  so we can commute its generation to U3/U4/U5

// This includes rule U2 and U1, because they literally do nothing
rule U2_UKCRp_Key_Change_Reply:
    [ !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , Fr( ~CD_b ) 
        ]
  --[   ]->
    [ OutUpdateKeyChallenge( ~oid, ~CD_b )
    , Out( < $USR, ~CD_b > )
        ]

/********************************************************************
* This rule is run by the user talking to the authority.
* The authority is assumed
*  to have an authentic way to communicate UKC to the user, this
*  is captured by just accessing the ~AK directly.
* Note that the adversary can construct all KSQ values so it never
*  needs to be Out'd from U2 
*********************************************************************/
rule U3_U4_U5_new_update_key:
    let UKCRp = < KSQ, $USR, CD_b >
        UKC   = < KSQ, $USR, senc( < $USR, ~UK_i_USR_O, CD_b >, ~AK ) >
        UKCCu = hmac( < $OSID, ~CD_a, CD_b, KSQ >, ~UK_i_USR_O )
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserInvariants( ~uid, ~AK, $USR, $OSID, ~linkid )
    , !AuthorityKey( ~AK )
    , Fr( ~CD_a )
    , Fr( ~UK_i_USR_O )
    , In( UKCRp )
        ]
  --[ NewUpdateKey( ~linkid, ~UK_i_USR_O )
        ]->
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForKCC', UKCCu > )
    , F_WaitForKCC( ~uid, ~uu, ~us, cCS, mCS, UKCCu )
    , !UpdateKey( ~linkid, ~UK_i_USR_O )
    , Out( < ~CD_a, UKC, UKCCu > )
        ]


s5teleport()

teleport()

acteleport()

amteleport()


// Since we commuted the KSQ update to U6, we should expect h(KSQ) as input
rule U6_UKCC_Update_Key_Change_Confirmation:
    let UKC = < h( KSQ ), $USR, senc( < $USR, UK_i_USR_O, CD_b >, AK ) >
        UKCCu = hmac( < $OSID, CD_a, CD_b, h( KSQ ) >, UK_i_USR_O )
        UKCCo = hmac( < $USR, CD_b, CD_a, h( KSQ ) >, UK_i_USR_O )
    in
    [ OutstationState( ~oid, KSQ, ~ou, ~os, cCS, mCS, 'SecurityIdle' )
    , OutUpdateKeyChallenge( ~oid, CD_b )
    , !OutstationInvariants( ~oid, AK, $USR, $OSID, ~linkid )
    , Fr( ~newou )
    , In( CD_a )
    , In( < UKC, UKCCu > )
        ]
  --[ OutstationUpdateKeySession( ~oid, UKCCu, UKCCo )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O )
        ]->
    [ OutstationState( ~oid, h( KSQ ), ~newou, ~os, cCS, mCS, 'SecurityIdle' )
    , !OutUpdateKey( ~oid, ~newou, UK_i_USR_O )
    , Out( UKCCo )
        ]

rule U7_receive_UKCC_from_Outstation:
    let UKCCu = hmac( < $OSID, CD_a, CD_b, KSQ >, UK_i_USR_O )
        UKCCo = hmac( < $USR, CD_b, CD_a, KSQ >, UK_i_USR_O )
    in
    [ UserState( ~uid, ~uu, ~us, cCS, mCS, < 'WaitForKCC', UKCCu > )
    , F_WaitForKCC( ~uid, ~uu, ~us, cCS, mCS, UKCCu )
    , !UserInvariants( ~uid, AK, $USR, $OSID, ~linkid )
    , Fr( ~newuu )
    , In( UKCCo )
        ]
  --[ UserUpdateKeySession( ~uid, UKCCu, UKCCo )
    , Sourced_UpdateKey( ~linkid, UK_i_USR_O )
        ]->
    [ UserState( ~uid, ~newuu, ~us, cCS, mCS, 'SecurityIdle' )
    , !UserUpdateKey( ~uid, ~newuu, UK_i_USR_O )
        ]


/********************************************************
* Lemmas from here on in. These are the things we prove. 
*********************************************************/


lemma countervalue_uniqueness[reuse, use_induction]:
    "All id x #i #j.
        NewCounterValue( id, x ) @ i & NewCounterValue( id, x ) @ j ==> #i = #j"

// Takes a while to do automatically, but can be solved by picking the goals with counter-related names
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
    solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~oid, h(cCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case A2_M_AC_Authentication_Challenge
    solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~uid, h(mCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case A4_idle_receive_C_AC_aggressive
    solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~oid, h(CSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_CounterValue( ~oid, h(CSQ) ) ▶₁ #j )
      qed
    qed
  next
    case A4_idle_receive_M_AC_aggressive
    solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~uid, h(mCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction
        qed
      next
        case S4_SKS_session_key_status
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case S4_SKS_session_key_status
    solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~oid, h(cCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction /* from formulas */
        qed
      next
        case S5_receive_SKS_confirmation
        by solve( L_CounterValue( ~oid, h(cCSQ) ) ▶₁ #j )
      qed
    qed
  next
    case S5_receive_SKS_confirmation
    solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #i )
      case CountUp
      solve( CSQ( ~uid, h(mCSQ) ) @ #j )
        case A2_C_AC_Authentication_Challenge
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A2_M_AC_Authentication_Challenge
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_C_AC_aggressive
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case A4_idle_receive_M_AC_aggressive
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S4_SKS_session_key_status
        by solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
      next
        case S5_receive_SKS_confirmation
        solve( L_CounterValue( ~uid, h(mCSQ) ) ▶₁ #j )
          case CountUp
          by contradiction /* from formulas */
        qed
      qed
    qed
  qed
qed


// All of the following lemmas autoprove

lemma authed_sessions_unique[reuse]:
    "( All id ar mode mode2 direction #i #j.
        AuthASDU( id, ar, mode, direction ) @ i 
      & AuthASDU( id, ar, mode2, direction ) @ j ==> #i = #j )"


lemma update_key_sourced[reuse, use_induction]:
    "not( Ex ak #r. AuthorityKeyReveal( ak ) @ r)
    ==>
    ( All id uk #i. 
        not( Ex #r. UpdateKeyReveal( uk ) @ r & #r < #i )
        & Sourced_UpdateKey( id,uk ) @ i
        ==> Ex #j. #j < #i & NewUpdateKey( id, uk ) @ j
    )"

lemma update_key_secrecy:
    "not( Ex ak #r. AuthorityKeyReveal( ak ) @ r )
    ==>
    ( All id uk #i. 
        not( Ex #r. UpdateKeyReveal( uk ) @ r )
        & NewUpdateKey( id, uk ) @ #i
        ==> not( Ex #j. K( uk ) @ #j)
    )"

lemma sessionkey_secrecy_outst:
    "not(Ex ak #r. AuthorityKeyReveal( ak ) @ r)
    ==>
    ( All id uk CDSK MDSK #i.
        not( Ex #r. UpdateKeyReveal( uk ) @ r)
        & not( Ex #r . CDSKReveal( CDSK ) @ r )
        & not( Ex #r . MDSKReveal( MDSK ) @ r )
        & Sourced_SKs( id, uk, CDSK, MDSK ) @ i
         ==>  not( Ex #j . K( CDSK ) @ j ) & not( Ex #j. K( MDSK ) @ j )
    )"


lemma sessionkeys_sourced[reuse,use_induction]:
    "not( Ex ak #r. AuthorityKeyReveal( ak ) @ r )
    ==>
    ( All linkid uk CDSK MDSK #i.
        // If the Update key wasn't revealed, the session keys were set correctly
        not( Ex #kr. UpdateKeyReveal( uk ) @ kr & #kr < #i )
        & Sourced_SKs( linkid, uk, CDSK, MDSK ) @ i
        ==> Ex #j MDSK2. #j < #i & NewSKs( linkid, uk, CDSK, MDSK2 ) @ j
    )"

lemma asdu_agreement_implies_mode_agreement[reuse]:
    "not( Ex ak #r. AuthorityKeyReveal( ak ) @ r )
    ==>
    ( All linkid ar mode direction linkid2 mode2 direction2 #i #j.
        ( All cdsk mdsk. UsingSessKeys( cdsk, mdsk ) @ i
        ==> // The update key that was used to send out the current session keys cannot be revealed
            ( All uk #k. UpdateKeyUsedForSKs( linkid, uk, cdsk, mdsk ) @ k 
                ==> not( Ex #kr. UpdateKeyReveal( uk ) @ kr & #kr < #i ) )
            // If the direction is control, then then no reveal of the current CDSK
            & ( direction = 'control' ==> not( Ex #skr. CDSKReveal( cdsk ) @ skr & #skr < #i ) )
            // And if the direction is monitor, then no reveal of the current MDSK
            & ( direction = 'monitor' ==> not( Ex #skr. MDSKReveal( mdsk ) @ skr & #skr < #i ) ) )
        & AuthASDU( linkid, ar, mode, direction ) @ i
        & SentASDU( linkid2, ar, mode2, direction2 ) @ j & #j < #i
        ==> ( mode = mode2 ) & ( direction = direction2 ) & ( linkid = linkid2 )
    )"

lemma asdu_aliveness[use_induction,hide_lemma=update_key_sourced]:
    "not( Ex ak #r. AuthorityKeyReveal( ak ) @ r )
    ==>
    ( All linkid ar mode direction #i.
        ( All cdsk mdsk. UsingSessKeys( cdsk, mdsk ) @ i
        ==> // The update key that was used to send out the current session keys cannot be revealed
            ( All uk #k. UpdateKeyUsedForSKs( linkid, uk, cdsk, mdsk ) @ k 
                ==> not( Ex #kr. UpdateKeyReveal( uk ) @ kr & #kr < #i ) )
            // If the direction is control, then then no reveal of the current CDSK
            & ( direction = 'control' ==> not( Ex #skr. CDSKReveal( cdsk ) @ skr & #skr < #i ) )
            // And if the direction is monitor, then no reveal of the current MDSK
            & ( direction = 'monitor' ==> not( Ex #skr. MDSKReveal( mdsk ) @ skr & #skr < #i ) ) )
        & AuthASDU( linkid, ar, mode, direction ) @ i
            ==> Ex #j. SentASDU( linkid, ar, mode, direction ) @ j & j < i
    )"

lemma asdu_injective_agreement:
    "not( Ex ak #r. AuthorityKeyReveal(ak) @ r )
    ==>
    ( All linkid ar mode direction #i #j.
        ( All cdsk mdsk. UsingSessKeys( cdsk, mdsk ) @ i
        ==> // The update key that was used to send out the current session keys cannot be revealed
            ( All uk #k. UpdateKeyUsedForSKs( linkid, uk, cdsk, mdsk ) @ k 
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
