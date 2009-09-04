open HolKernel Parse boolLib;

val _ = new_theory "normalForms";

(* ------------------------------------------------------------------------- *)
(* EXT_POINT                                                                 *)
(* If two functions f and g agree on their extension point EXT_POINT f g,    *)
(* then they must agree everywhere (i.e., they are equal).                   *)
(* ------------------------------------------------------------------------- *)

val EXT_POINT_EXISTS =
  let
    val LAND_CONV = RATOR_CONV o RAND_CONV
    val f = Term `f : 'a -> 'b`
    val g = Term `g : 'a -> 'b`
    val A0 = SPECL [f, g] EQ_EXT
    val A1 = SPEC (Term `\x. ^f x = ^g x`) LEFT_EXISTS_IMP_THM
    val A2 = SPEC (Term `^f = ^g`) A1
    val A3 = CONV_RULE (LAND_CONV (QUANT_CONV (LAND_CONV BETA_CONV))) A2
    val A4 = CONV_RULE (RAND_CONV (LAND_CONV (QUANT_CONV BETA_CONV))) A3
    val A5 = EQ_MP (SYM A4) A0
    val A6 = GEN g A5
    val A7 = INST_TYPE [alpha |-> (alpha --> beta), beta |-> alpha] SKOLEM_THM
    val A8 = SPEC (Term `\g x. (^f x = g x) ==> (^f = g)`) A7
    val A9 =
      CONV_RULE (LAND_CONV (QUANT_CONV (QUANT_CONV (RATOR_CONV BETA_CONV)))) A8
    val A10 = CONV_RULE (LAND_CONV (QUANT_CONV (QUANT_CONV BETA_CONV))) A9
    val A11 = EQ_MP A10 A6
    val A12 = CONV_RULE (QUANT_CONV (QUANT_CONV (RATOR_CONV BETA_CONV))) A11
    val A13 = CONV_RULE (QUANT_CONV (QUANT_CONV BETA_CONV)) A12
    val A14 = GEN f A13
    val A15 =
      INST_TYPE
      [alpha |-> (alpha --> beta), beta |-> ((alpha --> beta) --> alpha)]
      SKOLEM_THM
    val A16 =
      SPEC (Term `\f x. !(g:'a->'b). (f (x g) = g (x g)) ==> (f = g)`) A15
    val A17 =
      CONV_RULE (LAND_CONV (QUANT_CONV (QUANT_CONV (RATOR_CONV BETA_CONV)))) A16
    val A18 = CONV_RULE (LAND_CONV (QUANT_CONV (QUANT_CONV BETA_CONV))) A17
    val A19 = EQ_MP A18 A14
    val A20 = CONV_RULE (QUANT_CONV (QUANT_CONV (RATOR_CONV BETA_CONV))) A19
    val A21 = CONV_RULE (QUANT_CONV (QUANT_CONV BETA_CONV)) A20
    val A22 =
      ALPHA (Term `?f. !(x:'a->'b) g. (x (f x g) = g (f x g)) ==> (x = g)`)
            (Term `?x. !(f:'a->'b) g. (f (x f g) = g (x f g)) ==> (f = g)`)
  in
    EQ_MP A22 A21
  end;

val EXT_POINT_DEF =
  Definition.new_specification
  ("EXT_POINT_DEF", ["EXT_POINT"], EXT_POINT_EXISTS);

val _ = add_const "EXT_POINT";

val EXT_POINT = store_thm
  ("EXT_POINT",
   ``!(f : 'a -> 'b) g. (f (EXT_POINT f g) = g (EXT_POINT f g)) = (f = g)``,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC EXT_POINT_DEF,
    DISCH_THEN (fn th => REWRITE_TAC [th])]);

(* ------------------------------------------------------------------------- *)
(* UNIV_POINT                                                                *)
(* If a predicate P is true on its UNIV_POINT, it is true everywhere.        *)
(* ------------------------------------------------------------------------- *)

val UNIV_POINT_EXISTS = prove
  (``?f. !p. p (f p) ==> !x : 'a. p x``,
   EXISTS_TAC ``\p. @x : 'a. ~p x`` THEN
   GEN_TAC THEN
   BETA_TAC THEN
   DISCH_TAC THEN
   ONCE_REWRITE_TAC [GSYM (CONJUNCT1 NOT_CLAUSES)] THEN
   CONV_TAC (RAND_CONV NOT_FORALL_CONV) THEN
   REWRITE_TAC [EXISTS_DEF] THEN
   BETA_TAC THEN
   ASM_REWRITE_TAC []);

val UNIV_POINT_DEF =
  Definition.new_specification
  ("UNIV_POINT_DEF", ["UNIV_POINT"], UNIV_POINT_EXISTS);

val _ = add_const "UNIV_POINT";

val UNIV_POINT = store_thm
  ("UNIV_POINT",
   ``!p. p (UNIV_POINT p) = !x : 'a. p x``,
   GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC UNIV_POINT_DEF,
    DISCH_THEN MATCH_ACCEPT_TAC]);

val _ = export_theory ();
