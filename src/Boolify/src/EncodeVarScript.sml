(* -*-sml-*-
app load
["bossLib", "CoderTheory"];
*)

open HolKernel boolLib Parse bossLib simpLib listTheory
     EncodeTheory DecodeTheory CoderTheory;

val _ = new_theory "EncodeVar";

infixr 0 ++ || <<;
infix 1 >>;

val op ++ = op THEN;
val op >> = op THEN1;
val op << = op THENL;
val op || = op ORELSE;

val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;

val REVERSE = Tactical.REVERSE;

(*---------------------------------------------------------------------------
     Fixed size encodings---necessary for encoding variables.
 ---------------------------------------------------------------------------*)

val fixed_width_def =
  Define `fixed_width n c = !x. domain c x ==> (LENGTH (encoder c x) = n)`;

local
  val th = prove
    (``?of_length. !(l : 'a list) n. l IN of_length n = (LENGTH l = n)``,
     EXISTS_TAC ``\n (l : 'a list). LENGTH l = n`` THEN
     SIMP_TAC bool_ss [IN_DEF]);
in
  val of_length_def = new_specification ("of_length_def", ["of_length"], th);
end;

val fixed_width_univ = store_thm
  ("fixed_width_univ",
   ``!(phi : 'a -> bool) c n.
       wf_coder c /\ fixed_width n c ==>
       ((!x. domain c x ==> phi x) =
        !w :: of_length n. phi (decoder c w))``,
   RW_TAC bool_ss [RES_FORALL_THM, fixed_width_def, of_length_def]
   ++ REPEAT (STRIP_TAC ORELSE EQ_TAC)
   ++ PROVE_TAC [wf_coder, wf_coder_closed]);

val of_length_univ_suc = store_thm
  ("of_length_univ_suc",
   ``!phi n.
       (!w :: of_length (SUC n). phi (w : 'a list)) =
       (!x. !w :: of_length n. phi (x :: w))``,
   SIMP_TAC bool_ss [RES_FORALL_THM, of_length_def] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [Q.PAT_ASSUM `!x. Q x` MATCH_MP_TAC THEN
    ASM_SIMP_TAC arith_ss [LENGTH],
    MP_TAC (ISPEC ``w : 'a list`` list_CASES) THEN
    STRIP_TAC THENL
    [FULL_SIMP_TAC arith_ss [LENGTH],
     FULL_SIMP_TAC arith_ss [LENGTH]]]);

val of_length_univ_zero = store_thm
  ("of_length_univ_zero",
   ``!phi. (!w :: of_length 0. phi w) = phi ([] : 'a list)``,
   SIMP_TAC bool_ss [RES_FORALL_THM, of_length_def, LENGTH_NIL]);

val fixed_width_exists = store_thm
  ("fixed_width_exists",
   ``!(phi : 'a -> bool) c n.
       wf_coder c /\ fixed_width n c ==>
       ((?x. domain c x /\ phi x) =
        ?w :: of_length n. phi (decoder c w))``,
   RW_TAC bool_ss [RES_EXISTS_THM, fixed_width_def, of_length_def]
   ++ REPEAT (STRIP_TAC ORELSE EQ_TAC)
   ++ PROVE_TAC [wf_coder, wf_coder_closed]);

val of_length_exists_suc = store_thm
  ("of_length_exists_suc",
   ``!phi n.
       (?w :: of_length (SUC n). phi (w : 'a list)) =
       (?x. ?w :: of_length n. phi (x :: w))``,
   SIMP_TAC bool_ss [RES_EXISTS_THM, of_length_def] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [MP_TAC (ISPEC ``w:'a list`` list_CASES) THEN
    (STRIP_TAC THEN1 FULL_SIMP_TAC arith_ss [LENGTH]) THEN
    FULL_SIMP_TAC arith_ss [LENGTH] THEN
    EXISTS_TAC ``h : 'a`` THEN
    EXISTS_TAC ``t : 'a list`` THEN
    ASM_SIMP_TAC bool_ss [],
    EXISTS_TAC ``(x : 'a) :: w`` THEN
    ASM_SIMP_TAC arith_ss [LENGTH]]);

val of_length_exists_zero = store_thm
  ("of_length_exists_zero",
   ``!phi. (?w :: of_length 0. phi w) = phi ([] : 'a list)``,
   SIMP_TAC bool_ss [RES_EXISTS_THM, of_length_def, LENGTH_NIL]);

(*---------------------------------------------------------------------------
     Units
 ---------------------------------------------------------------------------*)

val fixed_width_unit = store_thm
  ("fixed_width_unit",
   ``!p. fixed_width 0 (unit_coder p)``,
   SIMP_TAC arith_ss
   [unit_coder_def, fixed_width_def, domain_def, encoder_def,
    encode_unit_def, LENGTH]);

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val fixed_width_bool = store_thm
  ("fixed_width_bool",
   ``!p. fixed_width 1 (bool_coder p)``,
   SIMP_TAC arith_ss
   [bool_coder_def, fixed_width_def, domain_def, encoder_def,
    encode_bool_def, LENGTH]);

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val fixed_width_prod = store_thm
  ("fixed_width_prod",
   ``!c1 c2 n1 n2.
       fixed_width n1 c1 /\ fixed_width n2 c2 ==>
       fixed_width (n1 + n2) (prod_coder c1 c2)``,
   REPEAT GEN_TAC
   ++ Know `?p1 e1 d1. c1 = (p1, e1, d1)` >> PROVE_TAC [pairTheory.ABS_PAIR_THM]
   ++ Know `?p2 e2 d2. c2 = (p2, e2, d2)` >> PROVE_TAC [pairTheory.ABS_PAIR_THM]
   ++ RW_TAC std_ss []
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [fixed_width_def, prod_coder_def, domain_def, encoder_def]
   ++ Cases_on `x`
   ++ FULL_SIMP_TAC std_ss [lift_prod_def, encode_prod_def, LENGTH_APPEND]);

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val fixed_width_sum = store_thm
  ("fixed_width_sum",
   ``!c1 c2 n.
       fixed_width n c1 /\ fixed_width n c2 ==>
       fixed_width (SUC n) (sum_coder c1 c2)``,
   REPEAT GEN_TAC
   ++ Know `?p1 e1 d1. c1 = (p1, e1, d1)` >> PROVE_TAC [pairTheory.ABS_PAIR_THM]
   ++ Know `?p2 e2 d2. c2 = (p2, e2, d2)` >> PROVE_TAC [pairTheory.ABS_PAIR_THM]
   ++ RW_TAC std_ss []
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [fixed_width_def, sum_coder_def, domain_def, encoder_def]
   ++ Cases_on `x`
   ++ FULL_SIMP_TAC std_ss [lift_sum_def, encode_sum_def, LENGTH]);

(*---------------------------------------------------------------------------
        Bounded numbers
 ---------------------------------------------------------------------------*)

val fixed_width_bnum = store_thm
  ("fixed_width_bnum",
   ``!m p. fixed_width m (bnum_coder m p)``,
   RW_TAC std_ss
   [fixed_width_def, encode_bnum_length, bnum_coder_def, encoder_def]);

val _ = export_theory ();
