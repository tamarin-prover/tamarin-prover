/*
 * Generic macros for generating .spthy files.
 */

/* Long-term keys */
#define SK(X)		sk(lts(X))
#define PK(X)		'g'^SK(X)

/* Basic DH structure with just exchanged exponents */

/* Critical: the parameters eki and ekr must use ni and nr as the
 * underlying nonces, because these are freshly generated and stored in
 * the state.
 * The parameters eki and ekr may in fact be instantiated with ~ni and
 * ~nr. */

#define basicDH(name,eki,ekr)	\
rule reveal_pk:	\
   [ ] --> [ Send(PK($X)) ]	\
	\
rule name##_I_1:	\
   [ Fresh( ~ni ) ]	\
   -->	\
   [ name##_I_1( $I, $R, ~ni ), Send( <$I, 'g'^eki >) ]	\
	\
rule name##_I_2:	\
   [ name##_I_1( $I, $R, ~ni ), Knows( <$R, Gr> ) ]	\
   -->	\
   [ name##_I_2( $I, $R, ~ni, Gr ) ]	\
	\
rule name##_R_1:	\
   [ Knows( <I, Gi> ) ] --> [ name##_R_1( I, $R, Gi ) ]	\
	\
rule name##_R_2:	\
   [ name##_R_1( I, $R, Gi ), Fresh( ~nr ) ]	\
   -->	\
   [ name##_R_2( I, $R, Gi, ~nr ), Send( <$R, 'g'^ekr> ) ]


/* Generic construction for session keys */

#define sessionkeyI(name,K,eki,ekr)	\
rule SeKeyI:	\
  [ name##_I_2( $I, $R, ni, Gr ) ]	\
  -->	\
  [ SeKeyI(K, <$I,$R,'g'^eki,Gr> ) ]

#define sessionkeyR(name,K,eki,ekr)	\
rule SeKeyR:	\
  [ name##_R_2( I, $R, Gi, nr ) ]	\
  -->	\
  [ SeKeyR(K, <I,$R,Gi,'g'^ekr> ) ]


