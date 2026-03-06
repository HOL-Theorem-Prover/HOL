(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)
Theory word8
Ancestors
  pair


(*---------------------------------------------------------------------------*)
(* 8 bits per byte, represented as an 8-tuple of truth values.               *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("word8", Type`:bool#bool#bool#bool#bool#bool#bool#bool`);

Definition ZERO_def:       ZERO = (F,F,F,F,F,F,F,F)
End
Definition ONE_def:         ONE = (F,F,F,F,F,F,F,T)
End
Definition TWO_def:         TWO = (F,F,F,F,F,F,T,F)
End
Definition THREE_def:     THREE = (F,F,F,F,F,F,T,T)
End

(*---------------------------------------------------------------------------*)
(* There are two ways to do case-analysis on bytes: as an 8-tuple of         *)
(* variables, or as 256 tuples of bits. The former is useful for symbolic    *)
(* evaluation, while the other is good for brute-force.                      *)
(*---------------------------------------------------------------------------*)

Theorem FORALL_BYTE_VARS:
  (!x:word8. P x) = !b7 b6 b5 b4 b3 b2 b1 b0. P(b7,b6,b5,b4,b3,b2,b1,b0)
Proof
 SIMP_TAC std_ss [FORALL_PROD]
QED

Theorem FORALL_BYTE_BITS:
  (!x:word8. P x) =
  P (F,F,F,F,F,F,F,F) /\ P (F,F,F,F,F,F,F,T) /\ P (F,F,F,F,F,F,T,F) /\
  P (F,F,F,F,F,F,T,T) /\ P (F,F,F,F,F,T,F,F) /\ P (F,F,F,F,F,T,F,T) /\
  P (F,F,F,F,F,T,T,F) /\ P (F,F,F,F,F,T,T,T) /\ P (F,F,F,F,T,F,F,F) /\
  P (F,F,F,F,T,F,F,T) /\ P (F,F,F,F,T,F,T,F) /\ P (F,F,F,F,T,F,T,T) /\
  P (F,F,F,F,T,T,F,F) /\ P (F,F,F,F,T,T,F,T) /\ P (F,F,F,F,T,T,T,F) /\
  P (F,F,F,F,T,T,T,T) /\ P (F,F,F,T,F,F,F,F) /\ P (F,F,F,T,F,F,F,T) /\
  P (F,F,F,T,F,F,T,F) /\ P (F,F,F,T,F,F,T,T) /\ P (F,F,F,T,F,T,F,F) /\
  P (F,F,F,T,F,T,F,T) /\ P (F,F,F,T,F,T,T,F) /\ P (F,F,F,T,F,T,T,T) /\
  P (F,F,F,T,T,F,F,F) /\ P (F,F,F,T,T,F,F,T) /\ P (F,F,F,T,T,F,T,F) /\
  P (F,F,F,T,T,F,T,T) /\ P (F,F,F,T,T,T,F,F) /\ P (F,F,F,T,T,T,F,T) /\
  P (F,F,F,T,T,T,T,F) /\ P (F,F,F,T,T,T,T,T) /\ P (F,F,T,F,F,F,F,F) /\
  P (F,F,T,F,F,F,F,T) /\ P (F,F,T,F,F,F,T,F) /\ P (F,F,T,F,F,F,T,T) /\
  P (F,F,T,F,F,T,F,F) /\ P (F,F,T,F,F,T,F,T) /\ P (F,F,T,F,F,T,T,F) /\
  P (F,F,T,F,F,T,T,T) /\ P (F,F,T,F,T,F,F,F) /\ P (F,F,T,F,T,F,F,T) /\
  P (F,F,T,F,T,F,T,F) /\ P (F,F,T,F,T,F,T,T) /\ P (F,F,T,F,T,T,F,F) /\
  P (F,F,T,F,T,T,F,T) /\ P (F,F,T,F,T,T,T,F) /\ P (F,F,T,F,T,T,T,T) /\
  P (F,F,T,T,F,F,F,F) /\ P (F,F,T,T,F,F,F,T) /\ P (F,F,T,T,F,F,T,F) /\
  P (F,F,T,T,F,F,T,T) /\ P (F,F,T,T,F,T,F,F) /\ P (F,F,T,T,F,T,F,T) /\
  P (F,F,T,T,F,T,T,F) /\ P (F,F,T,T,F,T,T,T) /\ P (F,F,T,T,T,F,F,F) /\
  P (F,F,T,T,T,F,F,T) /\ P (F,F,T,T,T,F,T,F) /\ P (F,F,T,T,T,F,T,T) /\
  P (F,F,T,T,T,T,F,F) /\ P (F,F,T,T,T,T,F,T) /\ P (F,F,T,T,T,T,T,F) /\
  P (F,F,T,T,T,T,T,T) /\ P (F,T,F,F,F,F,F,F) /\ P (F,T,F,F,F,F,F,T) /\
  P (F,T,F,F,F,F,T,F) /\ P (F,T,F,F,F,F,T,T) /\ P (F,T,F,F,F,T,F,F) /\
  P (F,T,F,F,F,T,F,T) /\ P (F,T,F,F,F,T,T,F) /\ P (F,T,F,F,F,T,T,T) /\
  P (F,T,F,F,T,F,F,F) /\ P (F,T,F,F,T,F,F,T) /\ P (F,T,F,F,T,F,T,F) /\
  P (F,T,F,F,T,F,T,T) /\ P (F,T,F,F,T,T,F,F) /\ P (F,T,F,F,T,T,F,T) /\
  P (F,T,F,F,T,T,T,F) /\ P (F,T,F,F,T,T,T,T) /\ P (F,T,F,T,F,F,F,F) /\
  P (F,T,F,T,F,F,F,T) /\ P (F,T,F,T,F,F,T,F) /\ P (F,T,F,T,F,F,T,T) /\
  P (F,T,F,T,F,T,F,F) /\ P (F,T,F,T,F,T,F,T) /\ P (F,T,F,T,F,T,T,F) /\
  P (F,T,F,T,F,T,T,T) /\ P (F,T,F,T,T,F,F,F) /\ P (F,T,F,T,T,F,F,T) /\
  P (F,T,F,T,T,F,T,F) /\ P (F,T,F,T,T,F,T,T) /\ P (F,T,F,T,T,T,F,F) /\
  P (F,T,F,T,T,T,F,T) /\ P (F,T,F,T,T,T,T,F) /\ P (F,T,F,T,T,T,T,T) /\
  P (F,T,T,F,F,F,F,F) /\ P (F,T,T,F,F,F,F,T) /\ P (F,T,T,F,F,F,T,F) /\
  P (F,T,T,F,F,F,T,T) /\ P (F,T,T,F,F,T,F,F) /\ P (F,T,T,F,F,T,F,T) /\
  P (F,T,T,F,F,T,T,F) /\ P (F,T,T,F,F,T,T,T) /\ P (F,T,T,F,T,F,F,F) /\
  P (F,T,T,F,T,F,F,T) /\ P (F,T,T,F,T,F,T,F) /\ P (F,T,T,F,T,F,T,T) /\
  P (F,T,T,F,T,T,F,F) /\ P (F,T,T,F,T,T,F,T) /\ P (F,T,T,F,T,T,T,F) /\
  P (F,T,T,F,T,T,T,T) /\ P (F,T,T,T,F,F,F,F) /\ P (F,T,T,T,F,F,F,T) /\
  P (F,T,T,T,F,F,T,F) /\ P (F,T,T,T,F,F,T,T) /\ P (F,T,T,T,F,T,F,F) /\
  P (F,T,T,T,F,T,F,T) /\ P (F,T,T,T,F,T,T,F) /\ P (F,T,T,T,F,T,T,T) /\
  P (F,T,T,T,T,F,F,F) /\ P (F,T,T,T,T,F,F,T) /\ P (F,T,T,T,T,F,T,F) /\
  P (F,T,T,T,T,F,T,T) /\ P (F,T,T,T,T,T,F,F) /\ P (F,T,T,T,T,T,F,T) /\
  P (F,T,T,T,T,T,T,F) /\ P (F,T,T,T,T,T,T,T) /\ P (T,F,F,F,F,F,F,F) /\
  P (T,F,F,F,F,F,F,T) /\ P (T,F,F,F,F,F,T,F) /\ P (T,F,F,F,F,F,T,T) /\
  P (T,F,F,F,F,T,F,F) /\ P (T,F,F,F,F,T,F,T) /\ P (T,F,F,F,F,T,T,F) /\
  P (T,F,F,F,F,T,T,T) /\ P (T,F,F,F,T,F,F,F) /\ P (T,F,F,F,T,F,F,T) /\
  P (T,F,F,F,T,F,T,F) /\ P (T,F,F,F,T,F,T,T) /\ P (T,F,F,F,T,T,F,F) /\
  P (T,F,F,F,T,T,F,T) /\ P (T,F,F,F,T,T,T,F) /\ P (T,F,F,F,T,T,T,T) /\
  P (T,F,F,T,F,F,F,F) /\ P (T,F,F,T,F,F,F,T) /\ P (T,F,F,T,F,F,T,F) /\
  P (T,F,F,T,F,F,T,T) /\ P (T,F,F,T,F,T,F,F) /\ P (T,F,F,T,F,T,F,T) /\
  P (T,F,F,T,F,T,T,F) /\ P (T,F,F,T,F,T,T,T) /\ P (T,F,F,T,T,F,F,F) /\
  P (T,F,F,T,T,F,F,T) /\ P (T,F,F,T,T,F,T,F) /\ P (T,F,F,T,T,F,T,T) /\
  P (T,F,F,T,T,T,F,F) /\ P (T,F,F,T,T,T,F,T) /\ P (T,F,F,T,T,T,T,F) /\
  P (T,F,F,T,T,T,T,T) /\ P (T,F,T,F,F,F,F,F) /\ P (T,F,T,F,F,F,F,T) /\
  P (T,F,T,F,F,F,T,F) /\ P (T,F,T,F,F,F,T,T) /\ P (T,F,T,F,F,T,F,F) /\
  P (T,F,T,F,F,T,F,T) /\ P (T,F,T,F,F,T,T,F) /\ P (T,F,T,F,F,T,T,T) /\
  P (T,F,T,F,T,F,F,F) /\ P (T,F,T,F,T,F,F,T) /\ P (T,F,T,F,T,F,T,F) /\
  P (T,F,T,F,T,F,T,T) /\ P (T,F,T,F,T,T,F,F) /\ P (T,F,T,F,T,T,F,T) /\
  P (T,F,T,F,T,T,T,F) /\ P (T,F,T,F,T,T,T,T) /\ P (T,F,T,T,F,F,F,F) /\
  P (T,F,T,T,F,F,F,T) /\ P (T,F,T,T,F,F,T,F) /\ P (T,F,T,T,F,F,T,T) /\
  P (T,F,T,T,F,T,F,F) /\ P (T,F,T,T,F,T,F,T) /\ P (T,F,T,T,F,T,T,F) /\
  P (T,F,T,T,F,T,T,T) /\ P (T,F,T,T,T,F,F,F) /\ P (T,F,T,T,T,F,F,T) /\
  P (T,F,T,T,T,F,T,F) /\ P (T,F,T,T,T,F,T,T) /\ P (T,F,T,T,T,T,F,F) /\
  P (T,F,T,T,T,T,F,T) /\ P (T,F,T,T,T,T,T,F) /\ P (T,F,T,T,T,T,T,T) /\
  P (T,T,F,F,F,F,F,F) /\ P (T,T,F,F,F,F,F,T) /\ P (T,T,F,F,F,F,T,F) /\
  P (T,T,F,F,F,F,T,T) /\ P (T,T,F,F,F,T,F,F) /\ P (T,T,F,F,F,T,F,T) /\
  P (T,T,F,F,F,T,T,F) /\ P (T,T,F,F,F,T,T,T) /\ P (T,T,F,F,T,F,F,F) /\
  P (T,T,F,F,T,F,F,T) /\ P (T,T,F,F,T,F,T,F) /\ P (T,T,F,F,T,F,T,T) /\
  P (T,T,F,F,T,T,F,F) /\ P (T,T,F,F,T,T,F,T) /\ P (T,T,F,F,T,T,T,F) /\
  P (T,T,F,F,T,T,T,T) /\ P (T,T,F,T,F,F,F,F) /\ P (T,T,F,T,F,F,F,T) /\
  P (T,T,F,T,F,F,T,F) /\ P (T,T,F,T,F,F,T,T) /\ P (T,T,F,T,F,T,F,F) /\
  P (T,T,F,T,F,T,F,T) /\ P (T,T,F,T,F,T,T,F) /\ P (T,T,F,T,F,T,T,T) /\
  P (T,T,F,T,T,F,F,F) /\ P (T,T,F,T,T,F,F,T) /\ P (T,T,F,T,T,F,T,F) /\
  P (T,T,F,T,T,F,T,T) /\ P (T,T,F,T,T,T,F,F) /\ P (T,T,F,T,T,T,F,T) /\
  P (T,T,F,T,T,T,T,F) /\ P (T,T,F,T,T,T,T,T) /\ P (T,T,T,F,F,F,F,F) /\
  P (T,T,T,F,F,F,F,T) /\ P (T,T,T,F,F,F,T,F) /\ P (T,T,T,F,F,F,T,T) /\
  P (T,T,T,F,F,T,F,F) /\ P (T,T,T,F,F,T,F,T) /\ P (T,T,T,F,F,T,T,F) /\
  P (T,T,T,F,F,T,T,T) /\ P (T,T,T,F,T,F,F,F) /\ P (T,T,T,F,T,F,F,T) /\
  P (T,T,T,F,T,F,T,F) /\ P (T,T,T,F,T,F,T,T) /\ P (T,T,T,F,T,T,F,F) /\
  P (T,T,T,F,T,T,F,T) /\ P (T,T,T,F,T,T,T,F) /\ P (T,T,T,F,T,T,T,T) /\
  P (T,T,T,T,F,F,F,F) /\ P (T,T,T,T,F,F,F,T) /\ P (T,T,T,T,F,F,T,F) /\
  P (T,T,T,T,F,F,T,T) /\ P (T,T,T,T,F,T,F,F) /\ P (T,T,T,T,F,T,F,T) /\
  P (T,T,T,T,F,T,T,F) /\ P (T,T,T,T,F,T,T,T) /\ P (T,T,T,T,T,F,F,F) /\
  P (T,T,T,T,T,F,F,T) /\ P (T,T,T,T,T,F,T,F) /\ P (T,T,T,T,T,F,T,T) /\
  P (T,T,T,T,T,T,F,F) /\ P (T,T,T,T,T,T,F,T) /\ P (T,T,T,T,T,T,T,F) /\
  P (T,T,T,T,T,T,T,T)
Proof
 EQ_TAC THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC [],
   SIMP_TAC std_ss [FORALL_PROD, FORALL_BOOL]]
QED


(*---------------------------------------------------------------------------*)
(* Bytes and numbers.                                                        *)
(*---------------------------------------------------------------------------*)

Definition B2N:   (B2N T = 1) /\ (B2N F = 0)
End

Definition BYTE_TO_NUM:
    BYTE_TO_NUM (b7,b6,b5,b4,b3,b2,b1,b0) =
      128*B2N(b7) + 64*B2N(b6) + 32*B2N(b5) +
       16*B2N(b4) +  8*B2N(b3) +  4*B2N(b2) + 2*B2N(b1) + B2N(b0)
End

Definition NUM_TO_BYTE:
    NUM_TO_BYTE n7 =
      let n6 = n7 DIV 2 in
      let n5 = n6 DIV 2 in
      let n4 = n5 DIV 2 in
      let n3 = n4 DIV 2 in
      let n2 = n3 DIV 2 in
      let n1 = n2 DIV 2 in
      let n0 = n1 DIV 2
      in
        (ODD n0, ODD n1, ODD n2, ODD n3,
         ODD n4, ODD n5, ODD n6, ODD n7)
End


Theorem BYTE_TO_NUM_TO_BYTE:
  !b. NUM_TO_BYTE(BYTE_TO_NUM b) = b
Proof
 SIMP_TAC std_ss [FORALL_BYTE_BITS] THEN EVAL_TAC
QED

Theorem NUM_TO_BYTE_TO_NUM:
  !n. n < 256 ==> (BYTE_TO_NUM (NUM_TO_BYTE n) = n)
Proof
 CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL)) THEN PROVE_TAC []
QED


(*---------------------------------------------------------------------------
        Shift a byte left and right
 ---------------------------------------------------------------------------*)

Definition LeftShift:
    LeftShift (b7,b6,b5,b4,b3,b2,b1,b0):word8 = (b6,b5,b4,b3,b2,b1,b0,F)
End

Definition RightShift:
    RightShift (b7,b6,b5,b4,b3,b2,b1,b0):word8 = (F,b7,b6,b5,b4,b3,b2,b1)
End

(*---------------------------------------------------------------------------
       Compare bits and bytes as if they were numbers. Not currently used
 ---------------------------------------------------------------------------*)

(*

Datatype: order = LESS | EQUAL | GREATER
End

val BIT_COMPARE = Define
  `(BIT_COMPARE F T = LESS) /\
   (BIT_COMPARE T F = GREATER) /\
   (BIT_COMPARE x y = EQUAL)`;


val BYTE_COMPARE = Define
  `BYTE_COMPARE (a7,a6,a5,a4,a3,a2,a1,a0)
                (b7,b6,b5,b4,b3,b2,b1,b0) =
    case BIT_COMPARE a7 b7
     of EQUAL ->
        (case BIT_COMPARE a6 b6
          of EQUAL ->
             (case BIT_COMPARE a5 b5
               of EQUAL ->
                  (case BIT_COMPARE a4 b4
                    of EQUAL ->
                       (case BIT_COMPARE a3 b3
                         of EQUAL ->
                            (case BIT_COMPARE a2 b2
                              of EQUAL ->
                                 (case BIT_COMPARE a1 b1
                                   of EQUAL -> BIT_COMPARE a0 b0
                                   || other -> other)
                              || other -> other)
                         || other -> other)
                    || other -> other)
               || other -> other)
          || other -> other)
     || other -> other`;
*)

(*---------------------------------------------------------------------------*)
(* XOR and AND on bytes                                                      *)
(*---------------------------------------------------------------------------*)

val _ = (set_fixity "XOR"     (Infixr 350);
         set_fixity "XOR8x4"  (Infixr 350);
         set_fixity "XOR8"    (Infixr 350);
         set_fixity "AND8"    (Infixr 350));

Definition XOR_def:    (x:bool) XOR y = ~(x=y)
End

Definition XOR8_def:
  (a,b,c,d,e,f,g,h) XOR8 (a1,b1,c1,d1,e1,f1,g1,h1)
                     =
                 (a XOR a1,
                  b XOR b1,
                  c XOR c1,
                  d XOR d1,
                  e XOR e1,
                  f XOR f1,
                  g XOR g1,
                  h XOR h1)
End

val _ = overload_on ("#",Term`$XOR8`);
val _ = set_fixity "#" (Infixl 625);

Definition AND8_def:
  (a,b,c,d,e,f,g,h) AND8 (a1,b1,c1,d1,e1,f1,g1,h1)
                     =
                 (a /\ a1,
                  b /\ b1,
                  c /\ c1,
                  d /\ d1,
                  e /\ e1,
                  f /\ f1,
                  g /\ g1,
                  h /\ h1)
End

val _ = overload_on ("&",Term`$AND8`);
val _ = set_fixity "&" (Infixl 650);

(*---------------------------------------------------------------------------*)
(* Algebraic lemmas for XOR8                                                 *)
(*---------------------------------------------------------------------------*)

Theorem XOR8_ZERO:
  !x. x # ZERO = x
Proof
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR_def,XOR8_def,ZERO_def]
QED

Theorem XOR8_INV:
  !x. x # x = ZERO
Proof
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR_def,XOR8_def,ZERO_def]
QED

Theorem XOR8_AC:
  (!x y z:word8. (x # y) # z = x # (y # z)) /\
  (!x y:word8. (x # y) = (y # x))
Proof
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR_def,XOR8_def]
 THEN REPEAT STRIP_TAC
 THEN DECIDE_TAC
QED
