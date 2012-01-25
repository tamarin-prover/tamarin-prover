theory KEAPLUS begin

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

 rule (modulo E) keaplus_I_1:
   [ Fr( ~ni ) ]
   -->
   [ keaplus_I_1( $I, $R, ~ni ), Out( <$I, 'g'^~ni> ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) keaplus_I_2:
   [ keaplus_I_1( $I, $R, ~ni ), In( <$R, Gr> ) ]
   -->
   [ keaplus_I_2( $I, $R, ~ni, Gr ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) keaplus_R_1:
   [ In( <I, Gi> ) ] --> [ keaplus_R_1( I, $R, Gi ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) keaplus_R_2:
   [ keaplus_R_1( I, $R, Gi ), Fr( ~nr ) ]
   -->
   [ keaplus_R_2( I, $R, Gi, ~nr ), Out( <$R, 'g'^~nr> ) ]
   /* has exactly the trivial AC variant */

 rule (modulo E) SeKeyI:
   [ keaplus_I_2( $I, $R, ~ni, Gr ) ]
   -->
   [ SeKeyI( h(<Gr^sk(lts($I)), 'g'^sk(lts($R))^~ni, $I, $R>),
             <$I, $R, 'g'^~ni, Gr>
     ) ]
   /*
   rule (modulo AC) SeKeyI:
     [ keaplus_I_2( $I2, $R3, ~ni4, Gr1 ) ]
     -->
     [ SeKeyI( h(<x, 'g'^(~ni4*sk(lts($R3))), $I2, $R3>),
               <$I2, $R3, 'g'^~ni4, Gr1>
       ) ]
   
     variants (modulo AC)
     1. x     = x194^sk(lts($x195))
        Gr1   = x194
        $I2   = $x195
     
     2. x     = x195^(x196*sk(lts($x197)))
        Gr1   = x195^x196
        $I2   = $x197
     
     3. x     = x194
        Gr1   = x194^_(sk(lts($x195)))
        $I2   = $x195
     
     4. x     = x195^x196
        Gr1   = x195^(x196*_(sk(lts($x197))))
        $I2   = $x197
     
     5. x     = x195^_x196
        Gr1   = x195^_((x196*sk(lts($x197))))
        $I2   = $x197
     
     6. x     = x196^(x197*_x198)
        Gr1   = x196^(x197*_((x198*sk(lts($x199)))))
        $I2   = $x199
   */

 rule (modulo E) SeKeyR:
   [ keaplus_R_2( I, $R, Gi, ~nr ) ]
   -->
   [ SeKeyR( h(<'g'^sk(lts(I))^~nr, Gi^sk(lts($R)), I, $R>),
             <I, $R, Gi, 'g'^~nr>
     ) ]
   /*
   rule (modulo AC) SeKeyR:
     [ keaplus_R_2( I3, $R2, Gi1, ~nr4 ) ]
     -->
     [ SeKeyR( h(<'g'^(~nr4*sk(lts(I3))), x, I3, $R2>),
               <I3, $R2, Gi1, 'g'^~nr4>
       ) ]
   
     variants (modulo AC)
     1. x     = x205^sk(lts($x206))
        Gi1   = x205
        $R2   = $x206
     
     2. x     = x206^(x207*sk(lts($x208)))
        Gi1   = x206^x207
        $R2   = $x208
     
     3. x     = x205
        Gi1   = x205^_(sk(lts($x206)))
        $R2   = $x206
     
     4. x     = x206^x207
        Gi1   = x206^(x207*_(sk(lts($x208))))
        $R2   = $x208
     
     5. x     = x206^_x207
        Gi1   = x206^_((x207*sk(lts($x208))))
        $R2   = $x208
     
     6. x     = x207^(x208*_x209)
        Gi1   = x207^(x208*_((x209*sk(lts($x210)))))
        $R2   = $x210
   */



section{* Typing Assertion Soundness Proofs *}



section{* Security Properties *}

lemma (modulo E) I_secrecy_ephkeys:
  "((#v :> keaplus_I_2( $I, $R, ~ni, Gr )) & (#u :> In( ~ni ))) ==>
   (Ex #rN1 Agv2. (#rN1 :> LTSR( Agv2 )) & ((Agv2 = $I) | (Agv2 = $R)))"
/* proof based on the same lemma modulo AC */
solve( #u4 :> In( ~ni2 ) )
  case In
  solve( #v5 :> keaplus_I_2( $I, $R1, ~ni2, Gr3 ) )
    case keaplus_I_2
    solve( #v5 [0] <: keaplus_I_1( $I, $R1, ~ni2 ) )
      case keaplus_I_1
      by solve( #u4 [0] <: ~ni2 )
    qed
  qed
qed

lemma (modulo E) R_secrecy_ephkeys:
  "((#v :> keaplus_R_2( I, $R, Gi, ~nr )) & (#u :> In( ~nr ))) ==>
   (Ex #rN1 Agv2. (#rN1 :> LTSR( Agv2 )) & ((Agv2 = $R) | (Agv2 = I)))"
/* proof based on the same lemma modulo AC */
solve( #u4 :> In( ~nr1 ) )
  case In
  solve( #v5 :> keaplus_R_2( I3, $R, Gi2, ~nr1 ) )
    case keaplus_R_2
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
    solve( #vkey6 [0] <: keaplus_I_2( $I, $R1, ~ni14, Gr3 ) )
      case keaplus_I_2
      solve( #vk5 [0] <: h(<x10, 'g'^(~ni14*sk(lts($R1))), $I, $R1>) )
        case fake_h
        solve( #w41 [0] <: 'g'^(~ni14*sk(lts($R1))) )
          case fake_Exp
          by solve( #w53 [0] <: ~ni14 )
        next
          case keaplus_I_1
          solve( #vd55 [1] <: sk(lts($R51)) )
            case fake_sk
            solve( #vr66 [0] <: lts($R51) )
              case Reveal_lts
              by resolve "subformula_1"
            qed
          qed
        next
          case reveal_pk
          by solve( #vd51 [1] <: ~ni56 )
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
    solve( #vkey6 [0] <: keaplus_R_2( I3, $R, Gi1, ~nr14 ) )
      case keaplus_R_2
      solve( #vk5 [0] <: h(<'g'^(~nr14*sk(lts(I3))), x10, I3, $R>) )
        case fake_h
        solve( #w39 [0] <: 'g'^(~nr14*sk(lts(I3))) )
          case fake_Exp
          by solve( #w51 [0] <: ~nr14 )
        next
          case keaplus_R_2
          solve( #vd54 [1] <: sk(lts(I69)) )
            case fake_sk
            solve( #vr76 [0] <: lts(I69) )
              case Reveal_lts
              by resolve "subformula_1"
            qed
          qed
        next
          case reveal_pk
          by solve( #vd49 [1] <: ~nr54 )
        qed
      qed
    qed
  qed
qed

end