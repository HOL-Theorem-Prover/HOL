(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)
Theory word8
Ancestors
  pair


(*---------------------------------------------------------------------------*)
(* 8 bits per byte, represented as an 8-tuple of truth values.               *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `word8 = BYTE of bool => bool => bool => bool =>
                                      bool => bool => bool => bool`;

val word8_case_def = fetch "-" "word8_case_def";

val ZERO_def   = Define   `ZERO = BYTE F F F F F F F F`;
val ONE_def    = Define    `ONE = BYTE F F F F F F F T`;
val TWO_def    = Define    `TWO = BYTE F F F F F F T F`;
val THREE_def  = Define  `THREE = BYTE F F F F F F T T`;

(*---------------------------------------------------------------------------*)
(* There are two ways to do case-analysis on bytes: as an 8-tuple of         *)
(* variables, or as 256 tuples of bits. The former is useful for symbolic    *)
(* evaluation, while the other is good for brute-force.                      *)
(*---------------------------------------------------------------------------*)

val FORALL_BYTE_VARS = Q.store_thm
("FORALL_BYTE_VARS",
 `(!x:word8. P x) = !b7 b6 b5 b4 b3 b2 b1 b0. P(BYTE b7 b6 b5 b4 b3 b2 b1 b0)`,
 EQ_TAC THEN RW_TAC std_ss []
  THEN Cases_on `x` THEN PROVE_TAC[]);


val FORALL_BYTE_BITS = Q.store_thm
("FORALL_BYTE_BITS",
 `(!x:word8. P x) =
  P (BYTE F F F F F F F F) /\ P (BYTE F F F F F F F T) /\ P (BYTE F F F F F F T F) /\
  P (BYTE F F F F F F T T) /\ P (BYTE F F F F F T F F) /\ P (BYTE F F F F F T F T) /\
  P (BYTE F F F F F T T F) /\ P (BYTE F F F F F T T T) /\ P (BYTE F F F F T F F F) /\
  P (BYTE F F F F T F F T) /\ P (BYTE F F F F T F T F) /\ P (BYTE F F F F T F T T) /\
  P (BYTE F F F F T T F F) /\ P (BYTE F F F F T T F T) /\ P (BYTE F F F F T T T F) /\
  P (BYTE F F F F T T T T) /\ P (BYTE F F F T F F F F) /\ P (BYTE F F F T F F F T) /\
  P (BYTE F F F T F F T F) /\ P (BYTE F F F T F F T T) /\ P (BYTE F F F T F T F F) /\
  P (BYTE F F F T F T F T) /\ P (BYTE F F F T F T T F) /\ P (BYTE F F F T F T T T) /\
  P (BYTE F F F T T F F F) /\ P (BYTE F F F T T F F T) /\ P (BYTE F F F T T F T F) /\
  P (BYTE F F F T T F T T) /\ P (BYTE F F F T T T F F) /\ P (BYTE F F F T T T F T) /\
  P (BYTE F F F T T T T F) /\ P (BYTE F F F T T T T T) /\ P (BYTE F F T F F F F F) /\
  P (BYTE F F T F F F F T) /\ P (BYTE F F T F F F T F) /\ P (BYTE F F T F F F T T) /\
  P (BYTE F F T F F T F F) /\ P (BYTE F F T F F T F T) /\ P (BYTE F F T F F T T F) /\
  P (BYTE F F T F F T T T) /\ P (BYTE F F T F T F F F) /\ P (BYTE F F T F T F F T) /\
  P (BYTE F F T F T F T F) /\ P (BYTE F F T F T F T T) /\ P (BYTE F F T F T T F F) /\
  P (BYTE F F T F T T F T) /\ P (BYTE F F T F T T T F) /\ P (BYTE F F T F T T T T) /\
  P (BYTE F F T T F F F F) /\ P (BYTE F F T T F F F T) /\ P (BYTE F F T T F F T F) /\
  P (BYTE F F T T F F T T) /\ P (BYTE F F T T F T F F) /\ P (BYTE F F T T F T F T) /\
  P (BYTE F F T T F T T F) /\ P (BYTE F F T T F T T T) /\ P (BYTE F F T T T F F F) /\
  P (BYTE F F T T T F F T) /\ P (BYTE F F T T T F T F) /\ P (BYTE F F T T T F T T) /\
  P (BYTE F F T T T T F F) /\ P (BYTE F F T T T T F T) /\ P (BYTE F F T T T T T F) /\
  P (BYTE F F T T T T T T) /\ P (BYTE F T F F F F F F) /\ P (BYTE F T F F F F F T) /\
  P (BYTE F T F F F F T F) /\ P (BYTE F T F F F F T T) /\ P (BYTE F T F F F T F F) /\
  P (BYTE F T F F F T F T) /\ P (BYTE F T F F F T T F) /\ P (BYTE F T F F F T T T) /\
  P (BYTE F T F F T F F F) /\ P (BYTE F T F F T F F T) /\ P (BYTE F T F F T F T F) /\
  P (BYTE F T F F T F T T) /\ P (BYTE F T F F T T F F) /\ P (BYTE F T F F T T F T) /\
  P (BYTE F T F F T T T F) /\ P (BYTE F T F F T T T T) /\ P (BYTE F T F T F F F F) /\
  P (BYTE F T F T F F F T) /\ P (BYTE F T F T F F T F) /\ P (BYTE F T F T F F T T) /\
  P (BYTE F T F T F T F F) /\ P (BYTE F T F T F T F T) /\ P (BYTE F T F T F T T F) /\
  P (BYTE F T F T F T T T) /\ P (BYTE F T F T T F F F) /\ P (BYTE F T F T T F F T) /\
  P (BYTE F T F T T F T F) /\ P (BYTE F T F T T F T T) /\ P (BYTE F T F T T T F F) /\
  P (BYTE F T F T T T F T) /\ P (BYTE F T F T T T T F) /\ P (BYTE F T F T T T T T) /\
  P (BYTE F T T F F F F F) /\ P (BYTE F T T F F F F T) /\ P (BYTE F T T F F F T F) /\
  P (BYTE F T T F F F T T) /\ P (BYTE F T T F F T F F) /\ P (BYTE F T T F F T F T) /\
  P (BYTE F T T F F T T F) /\ P (BYTE F T T F F T T T) /\ P (BYTE F T T F T F F F) /\
  P (BYTE F T T F T F F T) /\ P (BYTE F T T F T F T F) /\ P (BYTE F T T F T F T T) /\
  P (BYTE F T T F T T F F) /\ P (BYTE F T T F T T F T) /\ P (BYTE F T T F T T T F) /\
  P (BYTE F T T F T T T T) /\ P (BYTE F T T T F F F F) /\ P (BYTE F T T T F F F T) /\
  P (BYTE F T T T F F T F) /\ P (BYTE F T T T F F T T) /\ P (BYTE F T T T F T F F) /\
  P (BYTE F T T T F T F T) /\ P (BYTE F T T T F T T F) /\ P (BYTE F T T T F T T T) /\
  P (BYTE F T T T T F F F) /\ P (BYTE F T T T T F F T) /\ P (BYTE F T T T T F T F) /\
  P (BYTE F T T T T F T T) /\ P (BYTE F T T T T T F F) /\ P (BYTE F T T T T T F T) /\
  P (BYTE F T T T T T T F) /\ P (BYTE F T T T T T T T) /\ P (BYTE T F F F F F F F) /\
  P (BYTE T F F F F F F T) /\ P (BYTE T F F F F F T F) /\ P (BYTE T F F F F F T T) /\
  P (BYTE T F F F F T F F) /\ P (BYTE T F F F F T F T) /\ P (BYTE T F F F F T T F) /\
  P (BYTE T F F F F T T T) /\ P (BYTE T F F F T F F F) /\ P (BYTE T F F F T F F T) /\
  P (BYTE T F F F T F T F) /\ P (BYTE T F F F T F T T) /\ P (BYTE T F F F T T F F) /\
  P (BYTE T F F F T T F T) /\ P (BYTE T F F F T T T F) /\ P (BYTE T F F F T T T T) /\
  P (BYTE T F F T F F F F) /\ P (BYTE T F F T F F F T) /\ P (BYTE T F F T F F T F) /\
  P (BYTE T F F T F F T T) /\ P (BYTE T F F T F T F F) /\ P (BYTE T F F T F T F T) /\
  P (BYTE T F F T F T T F) /\ P (BYTE T F F T F T T T) /\ P (BYTE T F F T T F F F) /\
  P (BYTE T F F T T F F T) /\ P (BYTE T F F T T F T F) /\ P (BYTE T F F T T F T T) /\
  P (BYTE T F F T T T F F) /\ P (BYTE T F F T T T F T) /\ P (BYTE T F F T T T T F) /\
  P (BYTE T F F T T T T T) /\ P (BYTE T F T F F F F F) /\ P (BYTE T F T F F F F T) /\
  P (BYTE T F T F F F T F) /\ P (BYTE T F T F F F T T) /\ P (BYTE T F T F F T F F) /\
  P (BYTE T F T F F T F T) /\ P (BYTE T F T F F T T F) /\ P (BYTE T F T F F T T T) /\
  P (BYTE T F T F T F F F) /\ P (BYTE T F T F T F F T) /\ P (BYTE T F T F T F T F) /\
  P (BYTE T F T F T F T T) /\ P (BYTE T F T F T T F F) /\ P (BYTE T F T F T T F T) /\
  P (BYTE T F T F T T T F) /\ P (BYTE T F T F T T T T) /\ P (BYTE T F T T F F F F) /\
  P (BYTE T F T T F F F T) /\ P (BYTE T F T T F F T F) /\ P (BYTE T F T T F F T T) /\
  P (BYTE T F T T F T F F) /\ P (BYTE T F T T F T F T) /\ P (BYTE T F T T F T T F) /\
  P (BYTE T F T T F T T T) /\ P (BYTE T F T T T F F F) /\ P (BYTE T F T T T F F T) /\
  P (BYTE T F T T T F T F) /\ P (BYTE T F T T T F T T) /\ P (BYTE T F T T T T F F) /\
  P (BYTE T F T T T T F T) /\ P (BYTE T F T T T T T F) /\ P (BYTE T F T T T T T T) /\
  P (BYTE T T F F F F F F) /\ P (BYTE T T F F F F F T) /\ P (BYTE T T F F F F T F) /\
  P (BYTE T T F F F F T T) /\ P (BYTE T T F F F T F F) /\ P (BYTE T T F F F T F T) /\
  P (BYTE T T F F F T T F) /\ P (BYTE T T F F F T T T) /\ P (BYTE T T F F T F F F) /\
  P (BYTE T T F F T F F T) /\ P (BYTE T T F F T F T F) /\ P (BYTE T T F F T F T T) /\
  P (BYTE T T F F T T F F) /\ P (BYTE T T F F T T F T) /\ P (BYTE T T F F T T T F) /\
  P (BYTE T T F F T T T T) /\ P (BYTE T T F T F F F F) /\ P (BYTE T T F T F F F T) /\
  P (BYTE T T F T F F T F) /\ P (BYTE T T F T F F T T) /\ P (BYTE T T F T F T F F) /\
  P (BYTE T T F T F T F T) /\ P (BYTE T T F T F T T F) /\ P (BYTE T T F T F T T T) /\
  P (BYTE T T F T T F F F) /\ P (BYTE T T F T T F F T) /\ P (BYTE T T F T T F T F) /\
  P (BYTE T T F T T F T T) /\ P (BYTE T T F T T T F F) /\ P (BYTE T T F T T T F T) /\
  P (BYTE T T F T T T T F) /\ P (BYTE T T F T T T T T) /\ P (BYTE T T T F F F F F) /\
  P (BYTE T T T F F F F T) /\ P (BYTE T T T F F F T F) /\ P (BYTE T T T F F F T T) /\
  P (BYTE T T T F F T F F) /\ P (BYTE T T T F F T F T) /\ P (BYTE T T T F F T T F) /\
  P (BYTE T T T F F T T T) /\ P (BYTE T T T F T F F F) /\ P (BYTE T T T F T F F T) /\
  P (BYTE T T T F T F T F) /\ P (BYTE T T T F T F T T) /\ P (BYTE T T T F T T F F) /\
  P (BYTE T T T F T T F T) /\ P (BYTE T T T F T T T F) /\ P (BYTE T T T F T T T T) /\
  P (BYTE T T T T F F F F) /\ P (BYTE T T T T F F F T) /\ P (BYTE T T T T F F T F) /\
  P (BYTE T T T T F F T T) /\ P (BYTE T T T T F T F F) /\ P (BYTE T T T T F T F T) /\
  P (BYTE T T T T F T T F) /\ P (BYTE T T T T F T T T) /\ P (BYTE T T T T T F F F) /\
  P (BYTE T T T T T F F T) /\ P (BYTE T T T T T F T F) /\ P (BYTE T T T T T F T T) /\
  P (BYTE T T T T T T F F) /\ P (BYTE T T T T T T F T) /\ P (BYTE T T T T T T T F) /\
  P (BYTE T T T T T T T T)`,
 EQ_TAC THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC [],
   STRIP_TAC THEN SIMP_TAC std_ss [FORALL_BYTE_VARS, FORALL_BOOL]
    THEN ASM_REWRITE_TAC[]]);


(*---------------------------------------------------------------------------*)
(* Bytes and numbers.                                                        *)
(*---------------------------------------------------------------------------*)

val B2N = Define `(B2N T = 1) /\ (B2N F = 0)`;

val BYTE_TO_NUM = Define
   `BYTE_TO_NUM (BYTE b7 b6 b5 b4 b3 b2 b1 b0) =
      128*B2N(b7) + 64*B2N(b6) + 32*B2N(b5) +
       16*B2N(b4) +  8*B2N(b3) +  4*B2N(b2) + 2*B2N(b1) + B2N(b0)`;

val NUM_TO_BYTE = Define
   `NUM_TO_BYTE n7 =
      let n6 = n7 DIV 2 in
      let n5 = n6 DIV 2 in
      let n4 = n5 DIV 2 in
      let n3 = n4 DIV 2 in
      let n2 = n3 DIV 2 in
      let n1 = n2 DIV 2 in
      let n0 = n1 DIV 2
      in
        BYTE (ODD n0) (ODD n1) (ODD n2) (ODD n3)
             (ODD n4) (ODD n5) (ODD n6) (ODD n7)`;


val BYTE_TO_NUM_TO_BYTE = Q.store_thm
("BYTE_TO_NUM_TO_BYTE",
 `!b. NUM_TO_BYTE(BYTE_TO_NUM b) = b`,
 SIMP_TAC std_ss [FORALL_BYTE_BITS] THEN EVAL_TAC);

val NUM_TO_BYTE_TO_NUM = Q.store_thm
("NUM_TO_BYTE_TO_NUM",
 `!n. n < 256 ==> (BYTE_TO_NUM (NUM_TO_BYTE n) = n)`,
 CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL)) THEN PROVE_TAC []);


(*---------------------------------------------------------------------------
        Shift a byte left and right
 ---------------------------------------------------------------------------*)

val LeftShift = Define
   `LeftShift (BYTE b7 b6 b5 b4 b3 b2 b1 b0) = BYTE b6 b5 b4 b3 b2 b1 b0 F`;

val RightShift = Define
   `RightShift (BYTE b7 b6 b5 b4 b3 b2 b1 b0) = BYTE F b7 b6 b5 b4 b3 b2 b1`;


val LeftShift_lem =
 Q.store_thm
 ("LeftShift_lem",
  `!b. LeftShift b =
         case b
          of (BYTE b7 b6 b5 b4 b3 b2 b1 b0) -> BYTE b6 b5 b4 b3 b2 b1 b0 F`,
  SIMP_TAC std_ss [FORALL_BYTE_VARS,LeftShift,word8_case_def]);

val RightShift_lem =
 Q.store_thm
 ("RightShift_lem",
  `!b. RightShift b =
         case b
          of (BYTE b7 b6 b5 b4 b3 b2 b1 b0) -> BYTE F b7 b6 b5 b4 b3 b2 b1`,
  SIMP_TAC std_ss [FORALL_BYTE_VARS,RightShift,word8_case_def]);


(*---------------------------------------------------------------------------
       Compare bits and bytes as if they were numbers. Not currently used
 ---------------------------------------------------------------------------*)

(*

val _ = Hol_datatype `order = LESS | EQUAL | GREATER`;

val BIT_COMPARE = Define
  `(BIT_COMPARE F T = LESS) /\
   (BIT_COMPARE T F = GREATER) /\
   (BIT_COMPARE x y = EQUAL)`;


val BYTE_COMPARE = Define
  `BYTE_COMPARE (BYTE a7 a6 a5 a4 a3 a2 a1 a0)
                (BYTE b7 b6 b5 b4 b3 b2 b1 b0) =
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

val XOR_def =  Define `(x:bool) XOR y = ~(x=y)`;

val XOR8_def = Define
 `(BYTE a b c d e f g h) XOR8 (BYTE a1 b1 c1 d1 e1 f1 g1 h1) =
   BYTE (a XOR a1) (b XOR b1) (c XOR c1) (d XOR d1)
        (e XOR e1) (f XOR f1) (g XOR g1) (h XOR h1)`;

val _ = overload_on ("#",Term`$XOR8`);
val _ = set_fixity "#" (Infixl 625);

val AND8_def =
 Define
 `(BYTE a b c d e f g h) AND8 (BYTE a1 b1 c1 d1 e1 f1 g1 h1) =
   BYTE (a /\ a1) (b /\ b1) (c /\ c1) (d /\ d1)
        (e /\ e1) (f /\ f1) (g /\ g1) (h /\ h1)`;

val _ = overload_on ("&",Term`$AND8`);
val _ = set_fixity "&" (Infixl 650);

(*---------------------------------------------------------------------------*)
(* Algebraic lemmas for XOR8                                                 *)
(*---------------------------------------------------------------------------*)

val XOR8_ZERO = Q.store_thm
("XOR8_ZERO",
 `!x. x # ZERO = x`,
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR_def,XOR8_def,ZERO_def]);

val XOR8_INV = Q.store_thm
("XOR8_INV",
 `!x. x # x = ZERO`,
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR_def,XOR8_def,ZERO_def]);

val XOR8_AC = Q.store_thm
("XOR8_AC",
 `(!x y z:word8. (x # y) # z = x # (y # z)) /\
  (!x y:word8. (x # y) = (y # x))`,
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR_def,XOR8_def]
  THEN RW_TAC std_ss [] THEN DECIDE_TAC);

