theory UM begin

section{* Finite Variants of the Intruder Rules *}

 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^x3, x4 ] --> [ x2^(x4*x3) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^x3, _x3 ] --> [ x2 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_x3, x3 ] --> [ x2 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_x3, _x4 ] --> [ x2^_((x4*x3)) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), x4 ] --> [ x2^x3 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x4*x3), _x3 ] --> [ x2^x4 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_((x4*x3)), x3 ] --> [ x2^_x4 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^x3, (x4*_x3) ] --> [ x2^x4 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^x3, _((x4*x3)) ] --> [ x2^_x4 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_x3, (x4*x3) ] --> [ x2^x4 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), _x5 ] --> [ x2^(x3*_((x5*x4))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_x3, (x4*_x5) ] --> [ x2^(x4*_((x5*x3))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), x4 ] --> [ x2^(x3*_x5) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), (x5*x4) ] --> [ x2^(x5*x3) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x4*x3), (x5*_x3) ] --> [ x2^(x5*x4) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x4*x3), _((x5*x3)) ] --> [ x2^(x4*_x5) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_((x4*x3)), (x5*x3) ] --> [ x2^(x5*_x4) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^x3, (x4*_((x5*x3))) ] --> [ x2^(x4*_x5) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), (x5*_x6) ] --> [ x2^((x5*x3)*_((x6*x4))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), (x4*_x3) ] --> [ x2 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), _((x5*x3)) ] --> [ x2^_((x5*x4)) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_((x4*x3)), (x3*_x5) ] --> [ x2^_((x5*x4)) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), (x6*x4) ] --> [ x2^((x6*x3)*_x5) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x4*x3), (x5*_((x6*x3))) ] --> [ x2^((x5*x4)*_x6) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_x5), (x5*_x3) ] --> [ x2^x4 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), (x4*_x3) ] --> [ x2^_x5 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), ((x5*x4)*_x3) ] --> [ x2^x5 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), (x4*_((x5*x3))) ] --> [ x2^_x5 ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_x5), _((x6*x3)) ] --> [ x2^(x4*_((x6*x5))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^_((x4*x3)), ((x5*x3)*_x6) ] --> [ x2^(x5*_((x6*x4))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), (x4*_x6) ] --> [ x2^(x3*_((x6*x5))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), (x5*_((x6*x3))) ] --> [ x2^(x5*_((x6*x4))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_x4), ((x5*x4)*_((x6*x3))) ] --> [ x2^(x5*_x6) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_((x6*x5))), (x5*_x3) ] --> [ x2^(x4*_x6) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), (x4*_((x6*x3))) ] --> [ x2^_((x6*x5)) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), ((x6*x4)*_x3) ] --> [ x2^(x6*_x5) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_x5), (x5*_((x6*x3))) ] --> [ x2^(x4*_x6) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_x5), ((x6*x5)*_x3) ] --> [ x2^(x6*x4) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_x5), (x6*_((x7*x3))) ] --> [ x2^((x6*x4)*_((x7*x5))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), ((x6*x4)*_x7) ] --> [ x2^((x6*x3)*_((x7*x5))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_x5), ((x6*x5)*_((x7*x3))) ] --> [ x2^((x6*x4)*_x7) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_((x6*x5))), ((x7*x5)*_x3) ] --> [ x2^((x7*x4)*_x6) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^(x3*_((x5*x4))), ((x6*x4)*_((x7*x3))) ] --> [ x2^(x6*_((x7*x5))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_((x6*x5))), (x5*_((x7*x3))) ] --> [ x2^(x4*_((x7*x6))) ]
 
 rule (modulo AC) Exp [Destr, y^y1]:
   [ x2^((x4*x3)*_((x6*x5))), ((x7*x5)*_((x8*x3))) ]
   -->
   [ x2^((x7*x4)*_((x8*x6))) ]
 
 rule (modulo AC) Inv [Destr, _y]:
   [ _x1 ] --> [ x1 ]
 
 rule (modulo AC) Inv [Destr, _y]:
   [ (x1*_x2) ] --> [ (x2*_x1) ]
 
 rule (modulo AC) snd [Destr, snd(y)]:
   [ <x1, x2> ] --> [ x2 ]
 
 rule (modulo AC) fst [Destr, fst(y)]:
   [ <x1, x2> ] --> [ x1 ]
 
 rule (modulo AC) decA [Destr, decA(y1, y)]:
   [ encA{x3}pk(x2), sk(x2) ] --> [ x3 ]
 
 rule (modulo AC) decS [Destr, decS(y1, y)]:
   [ encS{x3}x2, x2 ] --> [ x3 ]
 
 rule (modulo AC) verify [Destr, verify(y1, y)]:
   [ sign{x3}sk(x2), pk(x2) ] --> [ x3 ]
 
 rule (modulo AC) Exp [Constr, y^y1]:
   [ x, x1 ] --> [ x^x1 ]
 
 rule (modulo AC) Inv [Constr, _y]:
   [ x ] --> [ _x ]
 
 rule (modulo AC) Unit [Constr, 1]:
   [ ] --> [ 1 ]
 
 rule (modulo AC) h [Constr, h(y)]:
   [ x ] --> [ h(x) ]
 
 rule (modulo AC) sk [Constr, sk(y)]:
   [ x ] --> [ sk(x) ]
 
 rule (modulo AC) pk [Constr, pk(y)]:
   [ x ] --> [ pk(x) ]
 
 rule (modulo AC) snd [Constr, snd(y)]:
   [ x ] --> [ snd(x) ]
 
 rule (modulo AC) fst [Constr, fst(y)]:
   [ x ] --> [ fst(x) ]
 
 rule (modulo AC) encS [Constr, encS{y}y1]:
   [ x, x1 ] --> [ encS{x}x1 ]
 
 rule (modulo AC) encA [Constr, encA{y}y1]:
   [ x, x1 ] --> [ encA{x}x1 ]
 
 rule (modulo AC) decA [Constr, decA(y1, y)]:
   [ x, x1 ] --> [ decA(x1, x) ]
 
 rule (modulo AC) decS [Constr, decS(y1, y)]:
   [ x, x1 ] --> [ decS(x1, x) ]
 
 rule (modulo AC) sign [Constr, sign{y}y1]:
   [ x, x1 ] --> [ sign{x}x1 ]
 
 rule (modulo AC) verify [Constr, verify(y1, y)]:
   [ x, x1 ] --> [ verify(x1, x) ]



section{* Protocol Rules *}

 rule (modulo E) Reveal_pk:
   [ ] --> [ Out( pk(lts($m)) ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) Reveal_lts:
   [ In( m ) ] --> [ LTSR( m ), Out( lts(m) ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) Fr:
   [ ] --> [ Fr( ~x ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) Reveal_fresh:
   [ Fr( ~m ) ] --> [ Out( ~m ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) In:
   [ m ] --> [ In( m ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) Learn:
   [ Out( m ) ] --> [ m ]
   /* has exactly the trivial AC variant */

 rule (modulo E) reveal_pk:
   [ ] --> [ Out( 'g'^sk(lts($X)) ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) um_I_1:
   [ Fr( ~ni ) ] --> [ um_I_1( $I, $R, ~ni ), Out( <$I, 'g'^~ni> ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) um_I_2:
   [ um_I_1( $I, $R, ~ni ), In( <$R, Gr> ) ]
   -->
   [ um_I_2( $I, $R, ~ni, Gr ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) um_R_1:
   [ In( <I, Gi> ) ] --> [ um_R_1( I, $R, Gi ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) um_R_2:
   [ um_R_1( I, $R, Gi ), Fr( ~nr ) ]
   -->
   [ um_R_2( I, $R, Gi, ~nr ), Out( <$R, 'g'^~nr> ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) SeKeyI:
   [ um_I_2( $I, $R, ~ni, Gr ) ]
   -->
   [ SeKeyI( h(<Gr^~ni, 'g'^sk(lts($R))^sk(lts($I))>), <$I, $R, 'g'^~ni, Gr>
     ) ]
   /*
   rule (modulo AC) SeKeyI:
     [ um_I_2( $I3, $R4, ~ni2, Gr1 ) ]
     -->
     [ SeKeyI( h(<x, 'g'^(sk(lts($I3))*sk(lts($R4)))>),
               <$I3, $R4, 'g'^~ni2, Gr1>
       ) ]
   
     variants (modulo AC)
     1. x     = x175^~x176
        Gr1   = x175
        ~ni2  = ~x176
     
     2. x     = x176^(x177*~x178)
        Gr1   = x176^x177
        ~ni2  = ~x178
     
     3. x     = x175
        Gr1   = x175^_~x176
        ~ni2  = ~x176
     
     4. x     = x176^x177
        Gr1   = x176^(x177*_~x178)
        ~ni2  = ~x178
     
     5. x     = x176^_x177
        Gr1   = x176^_((x177*~x178))
        ~ni2  = ~x178
     
     6. x     = x177^(x178*_x179)
        Gr1   = x177^(x178*_((x179*~x180)))
        ~ni2  = ~x180
   */

 rule (modulo E) SeKeyR:
   [ um_R_2( I, $R, Gi, ~nr ) ]
   -->
   [ SeKeyR( h(<Gi^~nr, 'g'^sk(lts(I))^sk(lts($R))>), <I, $R, Gi, 'g'^~nr>
     ) ]
   /*
   rule (modulo AC) SeKeyR:
     [ um_R_2( I3, $R4, Gi1, ~nr2 ) ]
     -->
     [ SeKeyR( h(<x, 'g'^(sk(lts($R4))*sk(lts(I3)))>),
               <I3, $R4, Gi1, 'g'^~nr2>
       ) ]
   
     variants (modulo AC)
     1. x     = x175^~x176
        Gi1   = x175
        ~nr2  = ~x176
     
     2. x     = x176^(x177*~x178)
        Gi1   = x176^x177
        ~nr2  = ~x178
     
     3. x     = x175
        Gi1   = x175^_~x176
        ~nr2  = ~x176
     
     4. x     = x176^x177
        Gi1   = x176^(x177*_~x178)
        ~nr2  = ~x178
     
     5. x     = x176^_x177
        Gi1   = x176^_((x177*~x178))
        ~nr2  = ~x178
     
     6. x     = x177^(x178*_x179)
        Gi1   = x177^(x178*_((x179*~x180)))
        ~nr2  = ~x180
   */



section{* Typing Assertion Soundness Proofs *}



section{* Security Properties *}

lemma (modulo E) I_secrecy_ephkeys:
  "((#v :> um_I_2( $I, $R, ~ni, Gr )) & (#u :> In( ~ni ))) ==>
   (Ex #rN1 Agv2. (#rN1 :> LTSR( Agv2 )) & ((Agv2 = $I) | (Agv2 = $R)))"
/* proof based on the same lemma modulo AC */
solve( #u4 :> In( ~ni2 ) )
  case In
  solve( #v5 :> um_I_2( $I, $R1, ~ni2, Gr3 ) )
    case um_I_2
    solve( #v5 [0] <: um_I_1( $I, $R1, ~ni2 ) )
      case um_I_1
      by solve( #u4 [0] <: ~ni2 )
    qed
  qed
qed

lemma (modulo E) R_secrecy_ephkeys:
  "((#v :> um_R_2( I, $R, Gi, ~nr )) & (#u :> In( ~nr ))) ==>
   (Ex #rN1 Agv2. (#rN1 :> LTSR( Agv2 )) & ((Agv2 = $R) | (Agv2 = I)))"
/* proof based on the same lemma modulo AC */
solve( #u4 :> In( ~nr1 ) )
  case In
  solve( #v5 :> um_R_2( I3, $R, Gi2, ~nr1 ) )
    case um_R_2
    by solve( #u4 [0] <: ~nr1 )
  qed
qed

lemma (modulo E) I_secrecy_key:
  "((#vkey :> SeKeyI( k, <$I, $R, Gi, Gr> )) & (#vk :> In( k ))) ==>
   (Ex #rN1 Agv2. (#rN1 :> LTSR( Agv2 )) & ((Agv2 = $I) | (Agv2 = $R)))"
/* proof based on the same lemma modulo AC */
solve( #vk5 :> In( k4 ) )
  case In
  solve( #vkey6 :> SeKeyI( k4, <$I, $R1, Gi2, Gr3> ) )
    case SeKeyI
    solve( #vkey6 [0] <: um_I_2( $I, $R1, ~ni12, Gr3 ) )
      case um_I_2
      solve( #vk5 [0] <: h(<x10, 'g'^(sk(lts($I))*sk(lts($R1)))>) )
        case fake_h
        solve( #w40 [1] <: 'g'^(sk(lts($I))*sk(lts($R1))) )
          case fake_Exp
          solve( #w49 [0] <: sk(lts($I)) )
            case fake_sk
            solve( #w50 [0] <: sk(lts($R1)) )
              case fake_sk
              solve( #vr53 [0] <: lts($I) )
                case Reveal_lts
                by resolve "subformula_0"
              qed
            qed
          qed
        next
          case reveal_pk_case_0
          solve( #vd47 [1] <: sk(lts($I61)) )
            case fake_sk
            solve( #vr65 [0] <: lts($I61) )
              case Reveal_lts
              by resolve "subformula_0"
            qed
          qed
        next
          case reveal_pk_case_1
          solve( #vd47 [1] <: sk(lts($R62)) )
            case fake_sk
            solve( #vr65 [0] <: lts($R62) )
              case Reveal_lts
              by resolve "subformula_1"
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma (modulo E) R_secrecy_key:
  "((#vkey :> SeKeyR( k, <I, $R, Gi, Gr> )) & (#vk :> In( k ))) ==>
   (Ex #rN1 Agv2. (#rN1 :> LTSR( Agv2 )) & ((Agv2 = $R) | (Agv2 = I)))"
/* proof based on the same lemma modulo AC */
solve( #vk5 :> In( k4 ) )
  case In
  solve( #vkey6 :> SeKeyR( k4, <I3, $R, Gi1, Gr2> ) )
    case SeKeyR
    solve( #vkey6 [0] <: um_R_2( I3, $R, Gi1, ~nr12 ) )
      case um_R_2
      solve( #vk5 [0] <: h(<x10, 'g'^(sk(lts($R))*sk(lts(I3)))>) )
        case fake_h
        solve( #w39 [1] <: 'g'^(sk(lts($R))*sk(lts(I3))) )
          case fake_Exp
          solve( #w48 [0] <: sk(lts($R)) )
            case fake_sk
            solve( #w49 [0] <: sk(lts(I3)) )
              case fake_sk
              solve( #vr52 [0] <: lts($R) )
                case Reveal_lts
                by resolve "subformula_0"
              qed
            qed
          qed
        next
          case reveal_pk_case_0
          solve( #vd46 [1] <: sk(lts($R60)) )
            case fake_sk
            solve( #vr65 [0] <: lts($R60) )
              case Reveal_lts
              by resolve "subformula_0"
            qed
          qed
        next
          case reveal_pk_case_1
          solve( #vd46 [1] <: sk(lts(I61)) )
            case fake_sk
            solve( #vr64 [0] <: lts(I61) )
              case Reveal_lts
              by resolve "subformula_1"
            qed
          qed
        qed
      qed
    qed
  qed
qed

end