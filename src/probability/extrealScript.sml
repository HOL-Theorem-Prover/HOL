(* ------------------------------------------------------------------------- *)
(* Extended Real Numbers - Advanced Theory                                   *)
(*                                                                           *)
(* Original Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013, 2015)   *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Updated and further enriched by Chun Tian (2018 - 2025)                   *)
(* ------------------------------------------------------------------------- *)
Theory extreal
Ancestors
  combin pred_set pair prim_rec arithmetic topology real
  real_sigma iterate real_topology seq lim transc metric list
  rich_list cardinal nets extreal_base real_of_rat
Libs
  metisLib res_quanTools jrhUtils numLib tautLib pred_setLib
  hurdUtils realLib


fun METIS ths tm = prove(tm, METIS_TAC ths);
val set_ss = std_ss ++ PRED_SET_ss;
val T_TAC = rpt (Q.PAT_X_ASSUM ‘T’ K_TAC);
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* ------------------------------------------------------------------------- *)
(*   Transcendental Operations                                               *)
(* ------------------------------------------------------------------------- *)

Definition extreal_exp_def :
   (extreal_exp (Normal x) = Normal (exp x)) /\
   (extreal_exp PosInf = PosInf) /\
   (extreal_exp NegInf = Normal 0)
End

(* old definition: (`ln 0` is not defined)
val extreal_ln_def = Define
  `(extreal_ln (Normal x) = Normal (ln x)) /\
   (extreal_ln PosInf = PosInf)`;

   new definition: (ln 0 = NegInf)
 *)
local
  val thm = Q.prove (
     `?f. (!x. 0 < x ==> f (Normal x) = Normal (ln x)) /\
          (f (Normal 0) = NegInf) /\
          (f PosInf = PosInf)`,
      Q.EXISTS_TAC `\y. if (y = Normal 0) then NegInf
                        else if (y = PosInf) then PosInf
                        else if (?r. (y = Normal r) /\ r <> 0) then Normal (ln (real y))
                        else ARB` \\
      RW_TAC std_ss [extreal_not_infty, real_normal, REAL_LT_REFL]);
in
   (* |- (!x. 0 < x ==> extreal_ln (Normal x) = Normal (ln x)) /\
         extreal_ln (Normal 0) = NegInf /\
         extreal_ln PosInf = PosInf
    *)
   val extreal_ln_def = new_specification
     ("extreal_ln_def", ["extreal_ln"], thm);
end;

Definition extreal_powr_def :
    extreal_powr x a = extreal_exp (extreal_mul a (extreal_ln x))
End

(* removed `extreal_logr b NegInf = NegInf` *)
Definition extreal_logr_def :
   (extreal_logr b (Normal x) = Normal (logr b x)) /\
   (extreal_logr b PosInf = PosInf)
End

Definition extreal_lg_def :
    extreal_lg x = extreal_logr 2 x
End

Overload exp  = “extreal_exp”
Overload powr = “extreal_powr”
Overload logr = “extreal_logr”
Overload lg   = “extreal_lg”
Overload ln   = “extreal_ln”

(***************************)
(*      Log and Ln         *)
(***************************)

Theorem logr_not_infty:
    !x b. (x <> NegInf /\ x <> PosInf) ==> logr b x <> NegInf /\ logr b x <> PosInf
Proof
    Cases >> RW_TAC std_ss [extreal_logr_def, extreal_not_infty]
QED

Theorem ln_not_neginf :
    !x. 0 < x ==> ln x <> NegInf
Proof
    rpt STRIP_TAC
 >> ‘0 <= x’ by PROVE_TAC [lt_imp_le]
 >> ‘x <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> Cases_on ‘x’
 >> rfs [extreal_ln_def, extreal_of_num_def, extreal_lt_eq, extreal_le_eq]
QED

(* cf. transcTheory.LN_MUL
   NOTE: this lemma also holds if ‘x = 0 /\ y <> PosInf’, etc.
 *)
Theorem ln_mul :
    !x y. 0 < x /\ 0 < y ==> ln (x * y) = ln x + ln y
Proof
    rpt STRIP_TAC
 >> ‘0 <= x /\ 0 <= y’ by PROVE_TAC [lt_imp_le]
 >> ‘x <> NegInf /\ y <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> Cases_on ‘x’ >> fs []
 >- (rw [extreal_ln_def, mul_infty] \\
    ‘ln y <> NegInf’ by PROVE_TAC [ln_not_neginf] \\
     Q.ABBREV_TAC ‘x = ln y’ \\
     Cases_on ‘x’ >> fs [extreal_add_def])
 >> Cases_on ‘y’ >> fs []
 >- fs [extreal_ln_def, mul_infty, extreal_of_num_def, extreal_lt_eq, extreal_le_eq,
        le_infty, extreal_add_def]
 >> fs [extreal_of_num_def, extreal_lt_eq, extreal_le_eq, extreal_mul_def]
 >> ‘0 < r * r'’ by PROVE_TAC [REAL_LT_MUL]
 >> rw [extreal_ln_def, extreal_add_def]
 >> MATCH_MP_TAC LN_MUL >> art []
QED

(* cf. transcTheory.LN_1 *)
Theorem ln_1 :
    ln (1 :extreal) = 0
Proof
    rw [extreal_of_num_def, extreal_ln_def, LN_1]
QED

(* cf. transcTheory.LN_POS_LT *)
Theorem ln_pos_lt :
    !x. 1 < x ==> 0 < ln x
Proof
    rpt STRIP_TAC
 >> ‘0 < x’ by METIS_TAC [lt_trans, lt_01]
 >> ‘0 <= x’ by rw [lt_imp_le]
 >> ‘x <> NegInf’ by rw [pos_not_neginf]
 >> Cases_on ‘x’
 >> fs [extreal_of_num_def, extreal_le_eq, extreal_lt_eq, le_infty,
        extreal_ln_def, lt_infty, LN_POS_LT]
QED

(* cf. transcTheory.LN_POS *)
Theorem ln_pos :
    !x. 1 <= x ==> 0 <= ln x
Proof
    rpt STRIP_TAC
 >> ‘x = 1 \/ 1 < x’ by PROVE_TAC [le_lt] >- rw [ln_1]
 >> MATCH_MP_TAC lt_imp_le
 >> MATCH_MP_TAC ln_pos_lt >> art []
QED

(* cf. transcTheory.LN_NEG_LT, changed: ‘0 <= x’ *)
Theorem ln_neg_lt :
    !x. 0 <= x /\ x < 1 ==> ln x < 0
Proof
    rpt STRIP_TAC
 >> ‘x = 0 \/ 0 < x’ by PROVE_TAC [le_lt]
 >- rw [extreal_of_num_def, extreal_ln_def, lt_infty]
 >> ‘x <> NegInf’ by rw [pos_not_neginf]
 >> Cases_on ‘x’
 >> fs [extreal_of_num_def, extreal_le_eq, extreal_lt_eq, le_infty,
        extreal_ln_def, lt_infty, LN_NEG_LT]
QED

(* cf. transcTheory.LN_NEG, changed: ‘0 <= x’ *)
Theorem ln_neg :
    !x. 0 <= x /\ x <= 1 ==> ln x <= 0
Proof
    rpt STRIP_TAC
 >> ‘x = 1 \/ x < 1’ by PROVE_TAC [le_lt] >- rw [ln_1]
 >> MATCH_MP_TAC lt_imp_le
 >> MATCH_MP_TAC ln_neg_lt >> art []
QED

(* cf. transcTheory.LN_INV *)
Theorem ln_inv :
    !x. 0 < x ==> ln (inv x) = ~(ln x)
Proof
    rpt STRIP_TAC
 >> ‘0 <= x’ by rw [le_lt]
 >> ‘x <> NegInf’ by rw [pos_not_neginf]
 >> Cases_on ‘x’ >> fs [extreal_ln_def, extreal_inv_def, extreal_ainv_def]
 >> fs [extreal_of_num_def, extreal_lt_eq, extreal_le_eq]
 >> ‘r <> 0’ by rw [REAL_LT_IMP_NE]
 >> rw [extreal_inv_def, extreal_ln_def, extreal_ainv_def]
 >> MATCH_MP_TAC LN_INV >> art []
QED

(***************************)
(*      Exp and powr       *)
(***************************)

Theorem exp_pos :
    !x :extreal. 0 <= exp x
Proof
    Q.X_GEN_TAC ‘x’ >> Cases_on `x`
 >> RW_TAC real_ss [extreal_exp_def, le_infty, extreal_of_num_def,
                    extreal_le_eq, EXP_POS_LE]
QED

(* cf. transcTheory.EXP_POS_LT *)
Theorem exp_pos_lt :
    !x. x <> NegInf ==> 0 < exp x
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x’ >> rw [extreal_exp_def]
 >> rw [extreal_of_num_def, extreal_lt_eq, EXP_POS_LT]
QED

Theorem normal_exp :
    !r. exp (Normal r) = Normal (exp r)
Proof
    RW_TAC std_ss [extreal_exp_def]
QED

Theorem exp_0[simp] :
    exp 0 = (1 :extreal)
Proof
    rw [extreal_of_num_def, normal_exp, extreal_11, EXP_0]
QED

Theorem exp_add_lemma[local] :
    !x y. x <> NegInf /\ y <> NegInf ==> exp (x + y) = exp x * exp y
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x’ >> fs []
 >- (rw [extreal_exp_def] \\
    ‘0 < exp y’ by PROVE_TAC [exp_pos_lt] \\
     rw [mul_infty, add_infty, extreal_exp_def])
 >> Cases_on ‘y’ >> fs []
 >- (rw [add_infty, extreal_exp_def, mul_infty] \\
    ‘0 < exp r’ by PROVE_TAC [EXP_POS_LT] \\
     rw [extreal_mul_def] >> PROVE_TAC [REAL_LT_IMP_NE])
 >> rw [extreal_add_def, extreal_mul_def, extreal_exp_def, EXP_ADD]
QED

Theorem exp_add_lemma'[local] :
    !x y. x <> PosInf /\ y <> PosInf ==> exp (x + y) = exp x * exp y
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x’ >> fs []
 >- (rw [extreal_exp_def, GSYM extreal_of_num_def] \\
     rw [add_infty, extreal_exp_def])
 >> Cases_on ‘y’ >> fs []
 >- (rw [add_infty, extreal_exp_def, mul_infty, GSYM extreal_of_num_def])
 >> rw [extreal_add_def, extreal_mul_def, extreal_exp_def, EXP_ADD]
QED

Theorem exp_add :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          exp (x + y) = exp x * exp y
Proof
    METIS_TAC [exp_add_lemma, exp_add_lemma']
QED

(* cf. transcTheory.EXP_NEG, with ‘x <> NegInf’ added *)
Theorem exp_neg :
    !x. x <> NegInf ==> exp (~x) = inv (exp(x))
Proof
    Q.X_GEN_TAC ‘x’
 >> Cases_on ‘x’
 >> rw [extreal_exp_def, extreal_ainv_def, extreal_inv_def]
 >> ‘0 < exp r’ by rw [EXP_POS_LT]
 >> ‘exp r <> 0’ by rw [REAL_LT_IMP_NE]
 >> rw [extreal_inv_def, EXP_NEG]
QED

(* cf. transcTheory.EXP_LE_X_FULL *)
Theorem exp_le_x :
    !x :extreal. &1 + x <= exp x
Proof
    Q.X_GEN_TAC ‘x’
 >> Cases_on ‘x’
 >> rw [extreal_of_num_def, extreal_add_def, extreal_exp_def, le_infty,
        extreal_le_eq, EXP_LE_X_FULL]
QED

Theorem exp_le_x' :
    !x :extreal. &1 - x <= exp (-x)
Proof
    Q.X_GEN_TAC ‘x’
 >> MP_TAC (Q.SPEC ‘-x’ exp_le_x)
 >> Suff ‘1 - x = 1 + -x’ >- rw []
 >> MATCH_MP_TAC extreal_sub_add
 >> rw [extreal_of_num_def]
QED

(***************************)

Theorem powr_pos :
    !x a :extreal. 0 <= x powr a
Proof
    RW_TAC std_ss [extreal_powr_def, exp_pos]
QED

(* cf. transcTheory.RPOW_POS_LT *)
Theorem powr_pos_lt :
    !x a. 0 < x /\ 0 <= a /\ a <> PosInf ==> 0 < x powr a
Proof
    RW_TAC std_ss [extreal_powr_def]
 >> MATCH_MP_TAC exp_pos_lt
 >> ‘a <> NegInf’ by rw [pos_not_neginf]
 >> ‘?r. 0 <= r /\ a = Normal r’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq]
 >> POP_ORW
 >> ‘ln x <> NegInf’ by PROVE_TAC [ln_not_neginf]
 >> METIS_TAC [mul_not_infty]
QED

Theorem infty_powr :
    !a. 0 < a ==> PosInf powr a = PosInf
Proof
    rw [extreal_powr_def, extreal_ln_def, mul_infty, extreal_exp_def]
QED

(* NOTE: ‘0 rpow a’ is not defined (see transcTheory.rpow_def) *)
Theorem normal_powr :
    !r a. 0 < r /\ 0 < a ==> (Normal r) powr (Normal a) = Normal (r powr a)
Proof
    RW_TAC real_ss [extreal_exp_def, extreal_mul_def, extreal_powr_def,
                    extreal_ln_def, rpow_def]
QED

Theorem powr_0[simp] :
    !x. x powr 0 = (1 :extreal)
Proof
    rw [extreal_powr_def, exp_0]
QED

(* cf. transc.ONE_RPOW, changed ‘0 < a’ to ‘0 <= a’ *)
Theorem one_powr :
    !a. 0 <= a ==> 1 powr a = 1
Proof
    rpt STRIP_TAC
 >> Cases_on ‘a = 0’ >- rw []
 >> ‘0 < a’ by rw [lt_le]
 >> rw [extreal_powr_def, ln_1]
QED

(* only possible after the new definition of `ln` *)
Theorem zero_rpow :
    !x :extreal. 0 < x ==> 0 powr x = 0
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_powr_def, extreal_ln_def]
 >> Cases_on `x`
 >- METIS_TAC [lt_infty]
 >- RW_TAC std_ss [extreal_mul_def, extreal_exp_def]
 >> FULL_SIMP_TAC std_ss [extreal_mul_def, extreal_lt_eq]
 >> `r <> 0` by PROVE_TAC [REAL_LT_LE]
 >> ASM_SIMP_TAC std_ss [extreal_exp_def]
QED

Theorem powr_eq_0 :
    !x a. 0 <= x /\ 0 < a /\ a <> PosInf ==> (x powr a = 0 <=> x = 0)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- rw [zero_rpow]
 >> ‘0 <= a’ by rw [lt_imp_le]
 >> ‘a <> NegInf’ by rw [pos_not_neginf]
 >> DISCH_TAC
 >> CCONTR_TAC
 >> ‘0 < x’ by PROVE_TAC [le_lt]
 >> ‘0 < x powr a’ by PROVE_TAC [powr_pos_lt]
 >> METIS_TAC [lt_antisym]
QED

(* cf. transcTheory.RPOW_1, changed to ‘0 <= x’
   NOTE: another way is to use extreal_powr_def and "exp_ln" (not available yet)
 *)
Theorem powr_1 :
    !x. 0 <= x ==> x powr 1 = x
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x = PosInf’ >- rw [infty_powr]
 >> Cases_on ‘x = 0’ >- rw [zero_rpow]
 >> ‘0 < x’ by PROVE_TAC [le_lt]
 >> ‘x <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> ‘?r. 0 < r /\ x = Normal r’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> rw [extreal_of_num_def, normal_powr, RPOW_1]
QED

Theorem powr_infty :
    !x. (1 < x ==> x powr PosInf = PosInf) /\
        (x = 1 ==> x powr PosInf = 1) /\
        (0 <= x /\ x < 1 ==> x powr PosInf = 0)
Proof
    RW_TAC std_ss [] (* 3 goals *)
 >| [ (* goal 1 (of 3) *)
      rw [extreal_powr_def] \\
     ‘0 < ln x’ by PROVE_TAC [ln_pos_lt] \\
      rw [mul_infty, extreal_exp_def],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC one_powr \\
      rw [extreal_of_num_def, le_infty],
      (* goal 3 (of 3) *)
      rw [extreal_powr_def] \\
      Suff ‘ln x < 0’
      >- (DISCH_TAC \\
         ‘PosInf * ln x = NegInf’ by PROVE_TAC [mul_infty'] \\
          rw [extreal_exp_def]) \\
      MATCH_MP_TAC ln_neg_lt >> art [] ]
QED

(* cf. transcTheory.BASE_RPOW_LE *)
Theorem powr_mono_eq :
    !a b c. 0 <= a /\ 0 <= c /\ 0 < b /\ b <> PosInf ==> (a powr b <= c powr b <=> a <= c)
Proof
    rpt STRIP_TAC
 >> ‘0 <= b’ by rw [lt_imp_le]
 >> ‘a <> NegInf /\ b <> NegInf /\ c <> NegInf’ by rw [pos_not_neginf]
 >> Cases_on ‘a = 0’ >- rw [zero_rpow, powr_pos]
 >> Cases_on ‘c = 0’
 >- (rw [zero_rpow, powr_pos] \\
    ‘0 <= a powr b’ by rw [powr_pos] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘a powr b = 0’ by PROVE_TAC [le_antisym] \\
       rfs [powr_eq_0],
       (* goal 2 (of 2) *)
       PROVE_TAC [le_antisym] ])
 >> ‘0 < a /\ 0 < c’ by PROVE_TAC [le_lt]
 >> Cases_on ‘a = PosInf’ >> rw [infty_powr, le_infty]
 >- (EQ_TAC >> rw [infty_powr] \\
     CCONTR_TAC \\
    ‘?r. 0 < r /\ c = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
    ‘?p. 0 < p /\ b = Normal p’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     fs [normal_powr])
 >> Cases_on ‘c = PosInf’ >> rw [infty_powr, le_infty]
 >> ‘?A. 0 < A /\ a = Normal A’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘?B. 0 < B /\ b = Normal B’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘?C. 0 < C /\ c = Normal C’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> rw [BASE_RPOW_LE, normal_powr, extreal_le_eq]
QED

(* cf. transcTheory.RPOW_LE *)
Theorem powr_le_eq :
    !a b c. 1 < a /\ a <> PosInf /\ 0 <= b /\ 0 <= c ==>
           (a powr b <= a powr c <=> b <= c)
Proof
    rpt STRIP_TAC
 >> ‘0 < a’ by PROVE_TAC [lt_trans, lt_01]
 >> ‘0 <= a’ by PROVE_TAC [lt_imp_le]
 >> ‘a <> NegInf /\ b <> NegInf /\ c <> NegInf’ by rw [pos_not_neginf]
 >> Cases_on ‘b = 0’
 >- (rw [powr_0] \\
     Cases_on ‘c = 0’ >- rw [powr_0] \\
     Cases_on ‘c = PosInf’
     >- (rw [powr_infty, extreal_le_def, extreal_of_num_def]) \\
    ‘0 < c’ by rw [lt_le] \\
    ‘1 = 1 powr c’ by PROVE_TAC [one_powr] >> POP_ORW \\
     rw [powr_mono_eq, lt_imp_le])
 >> ‘0 < b’ by rw [lt_le]
 >> Cases_on ‘c = 0’
 >- (rw [powr_0] \\
     Cases_on ‘b = PosInf’
     >- (rw [powr_infty, extreal_le_def, extreal_of_num_def]) \\
    ‘1 = 1 powr b’ by PROVE_TAC [one_powr] >> POP_ORW \\
     rw [powr_mono_eq] \\
     METIS_TAC [extreal_lt_def])
 >> ‘0 < c’ by rw [lt_le]
 >> Cases_on ‘b = PosInf’
 >- (rw [powr_infty, extreal_le_def, extreal_of_num_def, le_infty] \\
     Cases_on ‘c = PosInf’ >- rw [powr_infty] \\
    ‘?A. 0 < A /\ a = Normal A’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
    ‘?C. 0 < C /\ c = Normal C’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     rw [normal_powr])
 >> Cases_on ‘c = PosInf’
 >- rw [powr_infty, extreal_le_def, extreal_of_num_def, le_infty]
 >> ‘?A. 0 < A /\ a = Normal A’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘?B. 0 < B /\ b = Normal B’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘?C. 0 < C /\ c = Normal C’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> gs [RPOW_LE, normal_powr, extreal_of_num_def, extreal_le_eq, extreal_lt_eq]
QED

Theorem powr_ge_1 :
    !a p. 1 <= a /\ 0 <= p ==> 1 <= a powr p
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p = 0’ >- rw [powr_0]
 >> Cases_on ‘a = 1’ >- rw [one_powr]
 >> ‘0 < p /\ 1 < a’ by rw [lt_le]
 >> Cases_on ‘a = PosInf’ >- rw [infty_powr]
 >> ‘1 = a powr 0’ by rw [] >> POP_ORW
 >> rw [powr_le_eq]
QED

(* cf. transcTheory.RPOW_RPOW
   changed: ‘0 <= a’, added: ‘b <> PosInf /\ c <> PosInf’ *)
Theorem powr_powr :
    !a b c. 0 <= a /\ 0 < b /\ 0 < c /\ b <> PosInf /\ c <> PosInf ==>
           (a powr b) powr c = a powr (b * c)
Proof
    rpt STRIP_TAC
 >> ‘a = 0 \/ 0 < a’ by PROVE_TAC [le_lt]
 >- rw [zero_rpow, lt_mul]
 >> ‘0 < b * c’ by rw [lt_mul]
 (* applying infty_powr *)
 >> Cases_on ‘a = PosInf’ >- rw [infty_powr]
 (* applying normal_powr *)
 >> ‘b <> 0 /\ c <> 0’ by rw [lt_imp_ne]
 >> ‘0 <= b /\ 0 <= c’ by rw [lt_imp_le]
 >> ‘a <> NegInf /\ b <> NegInf /\ c <> NegInf’ by rw [pos_not_neginf]
 >> ‘?A. 0 < A /\ a = Normal A’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq, extreal_le_eq]
 >> POP_ORW
 >> ‘?B. 0 < B /\ b = Normal B’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq, extreal_le_eq]
 >> POP_ORW
 >> ‘?C. 0 < C /\ c = Normal C’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq, extreal_le_eq]
 >> POP_ORW
 >> ‘0 < B * C’ by rw [REAL_LT_MUL]
 >> ‘0 < A powr B’ by rw [RPOW_POS_LT]
 >> rw [extreal_mul_def, normal_powr, RPOW_RPOW]
QED

(* cf. transcTheory.RPOW_MUL *)
Theorem mul_powr :
    !x y a. 0 <= x /\ 0 <= y /\ 0 < a /\ a <> PosInf ==>
           (x * y) powr a = x powr a * y powr a
Proof
    rpt STRIP_TAC
 >> ‘x = 0 \/ 0 < x’ by PROVE_TAC [le_lt] >- rw [zero_rpow]
 >> ‘y = 0 \/ 0 < y’ by PROVE_TAC [le_lt] >- rw [zero_rpow]
 >> rw [extreal_powr_def, ln_mul]
 >> ‘0 <= a’ by rw [le_lt]
 >> ‘a <> NegInf’ by rw [pos_not_neginf]
 >> ‘?r. 0 < r /\ a = Normal r’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 >> rw [ln_not_neginf, add_ldistrib_normal]
 >> MATCH_MP_TAC exp_add
 >> DISJ1_TAC
 >> METIS_TAC [mul_not_infty, ln_not_neginf, REAL_LT_IMP_LE]
QED

(* cf. transcTheory.RPOW_ADD *)
Theorem powr_add :
    !a b c. 0 <= a /\ 0 <= b /\ b <> PosInf /\ 0 <= c /\ c <> PosInf ==>
            a powr (b + c) = a powr b * a powr c
Proof
    rpt STRIP_TAC
 >> ‘a <> NegInf /\ b <> NegInf /\ c <> NegInf’ by rw [pos_not_neginf]
 >> Cases_on ‘b = 0’ >- rw []
 >> Cases_on ‘c = 0’ >- rw []
 >> ‘0 < b /\ 0 < c’ by rw [lt_le]
 >> ‘0 < b + c’ by rw [lt_add]
 >> Cases_on ‘a = 0’ >- rw [zero_rpow]
 >> ‘0 < a’ by rw [lt_le]
 >> Cases_on ‘a = PosInf’
 >- rw [infty_powr, extreal_mul_def]
 >> ‘?A. 0 < A /\ a = Normal A’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘?B. 0 < B /\ b = Normal B’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘?C. 0 < C /\ c = Normal C’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> ‘0 < B + C’ by rw [REAL_LT_ADD]
 >> rw [normal_powr, extreal_add_def, extreal_mul_def, RPOW_ADD]
QED

Theorem sqrt_powr :
    !x. 0 <= x ==> sqrt x = x powr (inv 2)
Proof
    rpt STRIP_TAC
 >> ‘x <> NegInf’ by rw [pos_not_neginf]
 >> ‘0 < inv 2’ by rw [inv_pos']
 >> ‘x = 0 \/ 0 < x’ by PROVE_TAC [le_lt]
 >- rw [sqrt_0, zero_rpow]
 >> Cases_on ‘x’ >> fs [extreal_sqrt_def]
 >- rw [infty_powr]
 >> fs [extreal_of_num_def, extreal_lt_eq, extreal_le_eq, extreal_inv_eq]
 >> ‘0 < inv (2 :real)’ by rw [REAL_INV_POS]
 >> rw [normal_powr]
 >> MATCH_MP_TAC SQRT_RPOW >> art []
QED

(* cf. transcTheory.RPOW_INV *)
Theorem inv_powr :
    !x p. 0 < x /\ 0 < p /\ p <> PosInf ==> (inv x) powr p = inv (x powr p)
Proof
    rw [extreal_powr_def, ln_inv]
 >> ‘ln x <> NegInf’ by rw [ln_not_neginf]
 >> ‘0 <= p’ by rw [le_lt]
 >> ‘p <> NegInf’ by rw [pos_not_neginf]
 >> Suff ‘inv (exp (p * ln x)) = exp (~(p * ln x))’ >- rw [mul_rneg]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC exp_neg
 >> ‘?r. 0 <= r /\ p = Normal r’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq]
 >> POP_ORW
 >> METIS_TAC [mul_not_infty]
QED

(* cf. transcTheory.GEN_RPOW. *)
Theorem gen_powr :
    !a n. 0 <= a ==> (a pow n = a powr (&n :extreal))
Proof
    rpt STRIP_TAC
 >> Cases_on `n = 0` >- rw []
 >> Cases_on `a`
 >- METIS_TAC [lt_imp_le, le_not_infty]
 >- (`(0 :real) < &n` by RW_TAC real_ss [] \\
     `(0 :extreal) < &n` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
     ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_powr_def, extreal_ln_def,
                          mul_infty, extreal_exp_def])
 >> `(0 :real) < &n` by RW_TAC real_ss []
 >> `(0 :extreal) < &n` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
 >> FULL_SIMP_TAC std_ss [le_lt]
 >- (`?b. &n = Normal (&n)`
       by METIS_TAC [num_not_infty, extreal_cases, extreal_of_num_def] \\
     POP_ORW \\
     FULL_SIMP_TAC std_ss [extreal_pow_def, normal_powr, extreal_lt_eq,
                           extreal_11, extreal_of_num_def] \\
     MATCH_MP_TAC GEN_RPOW >> art [])
 >> Q.PAT_X_ASSUM `0 = Normal r` (ONCE_REWRITE_TAC o wrap o SYM)
 >> ASM_SIMP_TAC std_ss [zero_rpow]
 >> MATCH_MP_TAC zero_pow
 >> RW_TAC arith_ss []
QED

(* cf. transcTheory.YOUNG_INEQUALITY, note that the extreal version supports
      ‘0 <= a /\ 0 <= b’ instead of ‘0 < a /\ 0 < b’ in the real case.

   NOTE: ‘p <> PosInf /\ q <> PosInf’ (thus also ‘0 < p /\ 0 < q’) cannot be
         removed in general, for there may be ‘PosInf / PosInf’ at RHS.
 *)
Theorem young_inequality :
    !a b p q. 0 <= a /\ 0 <= b /\ 0 < p /\ 0 < q /\ p <> PosInf /\ q <> PosInf /\
              inv(p) + inv(q) = 1
          ==> a * b <= a powr p / p + b powr q / q
Proof
    rpt STRIP_TAC
 >> ‘p <> 0 /\ q <> 0’ by PROVE_TAC [lt_imp_ne]
 >> ‘a = 0 \/ 0 < a’ by METIS_TAC [le_lt]
 >- (rw [zero_rpow, zero_div] \\
     Cases_on ‘q’ >> fs [lt_infty] \\
     MATCH_MP_TAC le_div \\
     reverse CONJ_TAC >- fs [extreal_of_num_def, extreal_lt_eq] \\
     REWRITE_TAC [powr_pos])
 >> ‘b = 0 \/ 0 < b’ by METIS_TAC [le_lt]
 >- (rw [zero_rpow, zero_div] \\
     Cases_on ‘p’ >> fs [lt_infty] \\
     MATCH_MP_TAC le_div \\
     reverse CONJ_TAC >- fs [extreal_of_num_def, extreal_lt_eq] \\
     REWRITE_TAC [powr_pos])
 >> Cases_on ‘a’ >- fs [lt_infty]
 >- (rw [mul_infty, infty_powr] \\
     Know ‘PosInf / p = PosInf’
     >- (Cases_on ‘p’ >> fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
         rw [infty_div]) >> Rewr' \\
     MATCH_MP_TAC le_addr_imp \\
     Cases_on ‘q’ >> fs [lt_infty] \\
     MATCH_MP_TAC le_div \\
     reverse CONJ_TAC >- fs [extreal_of_num_def, extreal_lt_eq] \\
     REWRITE_TAC [powr_pos])
 >> rename1 ‘0 < Normal A’
 >> Cases_on ‘b’ >- fs [lt_infty]
 >- (rw [mul_infty, infty_powr] \\
     Know ‘PosInf / q = PosInf’
     >- (Cases_on ‘q’ >> fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
         rw [infty_div]) >> Rewr' \\
     MATCH_MP_TAC le_addl_imp \\
     Cases_on ‘p’ >> fs [lt_infty] \\
     MATCH_MP_TAC le_div \\
     reverse CONJ_TAC >- fs [extreal_of_num_def, extreal_lt_eq] \\
     REWRITE_TAC [powr_pos])
 >> rename1 ‘0 < Normal B’
 >> ‘p <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> ‘q <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> ‘?P. p = Normal P’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> ‘?Q. q = Normal Q’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> fs [extreal_not_infty, extreal_of_num_def, extreal_lt_eq, extreal_le_eq,
        extreal_inv_eq, extreal_add_def]
 >> rw [extreal_mul_def, normal_powr, extreal_div_eq, extreal_add_def,
        extreal_le_eq]
 >> MATCH_MP_TAC YOUNG_INEQUALITY >> art []
QED

(* NOTE: improved ‘p = 1 ==> q = PosInf’ to ‘p = 1 <=> q = PosInf’, etc. *)
Theorem conjugate_properties :
    !p q. 0 < p /\ 0 < q /\ inv(p) + inv(q) = 1 ==>
          1 <= p /\ 1 <= q /\ (p = 1 <=> q = PosInf) /\ (q = 1 <=> p = PosInf)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘0 <= inv p /\ 0 <= inv q’ by PROVE_TAC [le_inv]
 >> rpt CONJ_TAC
 >| [ (* goal 1 (of 4) *)
      Know ‘1 <= p <=> inv p <= inv 1’
      >- (MATCH_MP_TAC (GSYM inv_le_antimono) >> art [lt_01]) >> Rewr' \\
      rw [inv_one] \\
      SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM extreal_lt_def])) \\
      Know ‘1 < inv p <=> 1 + inv q < inv p + inv q’
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          MATCH_MP_TAC lt_radd \\
         ‘q <> 0’ by PROVE_TAC [lt_imp_ne] \\
          METIS_TAC [inv_not_infty]) \\
      DISCH_THEN (rfs o wrap) \\
      Know ‘1 + inv q < 1 + 0 <=> inv q < 0’
      >- (MATCH_MP_TAC lt_ladd >> rw [extreal_of_num_def]) \\
      PURE_REWRITE_TAC [add_rzero] \\
      DISCH_THEN (fs o wrap) \\
      METIS_TAC [let_antisym],
      (* goal 2 (of 4) *)
      Know ‘1 <= q <=> inv q <= inv 1’
      >- (MATCH_MP_TAC (GSYM inv_le_antimono) >> art [lt_01]) >> Rewr' \\
      rw [inv_one] \\
      SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM extreal_lt_def])) \\
      Know ‘1 < inv q <=> inv p + 1 < inv p + inv q’
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          MATCH_MP_TAC lt_ladd \\
         ‘p <> 0’ by PROVE_TAC [lt_imp_ne] \\
          METIS_TAC [inv_not_infty]) \\
      DISCH_THEN (rfs o wrap) \\
      Know ‘inv p + 1 < 0 + 1 <=> inv p < 0’
      >- (MATCH_MP_TAC lt_radd >> rw [extreal_of_num_def]) \\
      PURE_REWRITE_TAC [add_lzero] \\
      DISCH_THEN (fs o wrap) \\
      METIS_TAC [let_antisym],
      (* goal 3 (of 4) *)
      reverse EQ_TAC >- (DISCH_THEN (fn th => fs [inv_infty, th]) \\
                         Suff ‘inv p = inv 1’ >- PROVE_TAC [inv_inj, lt_01] \\
                         rw [inv_one]) \\
      DISCH_THEN (fn th => fs [inv_one, th]) \\
     ‘q <> 0’ by PROVE_TAC [lt_imp_ne] \\
      Cases_on ‘q’ \\
      fs [lt_infty, extreal_of_num_def, extreal_lt_eq, extreal_le_eq, extreal_inv_def,
          extreal_add_def] \\
      METIS_TAC [REAL_ADD_RID_UNIQ, REAL_INV_POS, REAL_LT_IMP_NE],
      (* goal 4 (of 4) *)
      reverse EQ_TAC >- (DISCH_THEN (fn th => fs [inv_infty, th]) \\
                         Suff ‘inv q = inv 1’ >- PROVE_TAC [inv_inj, lt_01] \\
                         rw [inv_one]) \\
      DISCH_THEN (fn th => fs [inv_one, th]) \\
     ‘p <> 0’ by PROVE_TAC [lt_imp_ne] \\
      Cases_on ‘p’ \\
      fs [lt_infty, extreal_of_num_def, extreal_lt_eq, extreal_le_eq, extreal_inv_def,
          extreal_add_def] \\
      METIS_TAC [REAL_ADD_LID_UNIQ, REAL_INV_POS, REAL_LT_IMP_NE] ]
QED

Definition ext_mono_increasing_def :
    ext_mono_increasing f = (!m n:num. m <= n ==> f m <= f n)
End

Theorem ext_mono_increasing_suc:   !f. ext_mono_increasing f <=> !n. f n <= f (SUC n)
Proof
    RW_TAC std_ss [ext_mono_increasing_def]
 >> EQ_TAC >> RW_TAC real_ss []
 >> Know `?d. n = m + d` >- PROVE_TAC [LESS_EQ_EXISTS]
 >> RW_TAC std_ss []
 >> Induct_on `d` >- RW_TAC std_ss [add_rzero, le_refl]
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `m + d`)
 >> METIS_TAC [le_trans, ADD_CLAUSES, LESS_EQ_ADD]
QED

Definition ext_mono_decreasing_def :
    ext_mono_decreasing f = (!m n:num. m <= n ==> f n <= f m)
End

Theorem ext_mono_decreasing_suc:   !f. ext_mono_decreasing f <=> !n. f (SUC n) <= f n
Proof
    RW_TAC std_ss [ext_mono_decreasing_def]
 >> EQ_TAC >> RW_TAC real_ss []
 >> Know `?d. n = m + d` >- PROVE_TAC [LESS_EQ_EXISTS]
 >> RW_TAC std_ss []
 >> Induct_on `d` >- RW_TAC std_ss [add_rzero,le_refl]
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n. f (SUC n) <= f n` (MP_TAC o Q.SPEC `m + d`)
 >> METIS_TAC [le_trans, ADD_CLAUSES, LESS_EQ_ADD]
QED

Overload mono_increasing = “ext_mono_increasing”
Overload mono_decreasing = “ext_mono_decreasing”

Theorem mono_increasing_imp_ext :
    !f. mono_increasing f ==> mono_increasing (Normal o f)
Proof
    RW_TAC std_ss [extreal_le_eq, mono_increasing_def, ext_mono_increasing_def]
QED

Theorem mono_decreasing_imp_ext :
    !f. mono_decreasing f ==> mono_decreasing (Normal o f)
Proof
    RW_TAC std_ss [extreal_le_eq, mono_decreasing_def, ext_mono_decreasing_def]
QED

Theorem EXTREAL_ARCH_POW2 : (* was: EXTREAL_ARCH_POW *)
    !x. x <> PosInf ==> ?n. x < 2 pow n
Proof
    Cases
 >> RW_TAC std_ss [lt_infty, extreal_lt_eq, REAL_ARCH_POW2, extreal_pow_def,
                   extreal_of_num_def]
QED

Theorem EXTREAL_ARCH_POW2_INV : (* was: EXTREAL_ARCH_POW_INV *)
    !e. 0 < e ==> ?n. Normal ((1 / 2) pow n) < e
Proof
    Cases >- RW_TAC std_ss [lt_infty]
 >- METIS_TAC [lt_infty,extreal_not_infty]
 >> RW_TAC std_ss [extreal_of_num_def,extreal_lt_eq]
 >> MP_TAC (Q.SPEC `1 / 2` SEQ_POWER)
 >> RW_TAC std_ss [abs, REAL_HALF_BETWEEN, REAL_LT_IMP_LE, SEQ]
 >> POP_ASSUM (MP_TAC o Q.SPEC `r`)
 >> RW_TAC std_ss [REAL_SUB_RZERO, REAL_POW_LT,
                   REAL_HALF_BETWEEN,REAL_LT_IMP_LE,GREATER_EQ]
 >> PROVE_TAC [LESS_EQ_REFL]
QED

Theorem le_epsilon :
    !x y. (!e. 0 < e /\ e <> PosInf ==> x <= y + e) ==> x <= y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [le_infty]
 >| [ (* goal 1 *)
      Q.EXISTS_TAC `1` \\
      RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def],
      (* goal 2 *)
      Q.EXISTS_TAC `1` \\
      RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def],
      (* goal 3 *)
      Q.EXISTS_TAC `1` \\
      RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def,
                     extreal_le_def],
      (* goal 4 *)
     `!e. 0 < e ==> Normal r <= Normal r' + Normal e`
         by (RW_TAC std_ss [] \\
             Q.PAT_X_ASSUM `!e. P e` MATCH_MP_TAC \\
             METIS_TAC [extreal_not_infty, extreal_of_num_def, extreal_lt_eq]) \\
     `!e. 0 < e ==> Normal r <= Normal (r' + e)`
         by (RW_TAC real_ss [extreal_le_def, REAL_LT_IMP_LE, REAL_LE_ADD] \\
            `Normal r <= Normal r' + Normal e` by METIS_TAC [REAL_LT_IMP_LE] \\
            `Normal r' + Normal e = Normal (r' + e)`
                  by METIS_TAC [extreal_add_def, REAL_LT_IMP_LE] \\
             FULL_SIMP_TAC std_ss [] \\
             METIS_TAC [REAL_LE_ADD, extreal_le_def, REAL_LT_IMP_LE]) \\
     `!e. 0 < e ==> r <= r' + e`
       by METIS_TAC [extreal_le_def, REAL_LT_IMP_LE, REAL_LE_ADD, extreal_add_def,
                     REAL_LE_ADD] \\
     `!e. 0 < e ==>  r <= r' + e` by METIS_TAC [extreal_le_def] \\
      METIS_TAC [REAL_LE_EPSILON, extreal_le_def] ]
QED

Theorem le_mul_epsilon:
    !x y:extreal. (!z. 0 <= z /\ z < 1 ==> z * x <= y) ==> x <= y
Proof
    ASSUME_TAC half_between
 >> `1 / 2 <> 0` by METIS_TAC [lt_imp_ne]
 >> rpt Cases >> RW_TAC std_ss [le_infty]
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC `1 / 2` \\
      RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases],
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC `1 / 2` \\
      RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases,
                      le_infty, extreal_not_infty],
      (* goal 3 (of 4) *)
      Q.EXISTS_TAC `1 / 2` \\
      RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases,
                      le_infty, extreal_not_infty],
      (* goal 4 (of 4) *)
     `!z. 0 <= z /\ z < 1 <=> ?z1. 0 <= z1 /\ z1 < 1 /\ (z = Normal z1)`
         by (RW_TAC std_ss [] \\
             EQ_TAC
             >- (RW_TAC std_ss [] \\
                 Cases_on `z` >|
                 [ METIS_TAC [extreal_of_num_def, le_infty, extreal_not_infty],
                   METIS_TAC [extreal_of_num_def, lt_infty, extreal_not_infty],
                   METIS_TAC [extreal_le_def, extreal_lt_eq, extreal_of_num_def] ]) \\
             METIS_TAC [extreal_lt_eq, extreal_le_def, extreal_of_num_def]) \\
      RW_TAC std_ss [] \\
     `!z1. 0 <= z1 /\ z1 < 1 ==> Normal (z1) * Normal r <= Normal r'`
         by METIS_TAC [extreal_lt_eq, extreal_le_def, extreal_of_num_def] \\
     `!z1. 0 <= z1 /\ z1 < 1 ==> Normal (z1 * r) <= Normal r'`
         by METIS_TAC [extreal_mul_def] \\
      Suff `r <= r'` >- METIS_TAC [extreal_le_def] \\
      MATCH_MP_TAC REAL_LE_MUL_EPSILON \\
      METIS_TAC [extreal_le_def, REAL_LT_LE] ]
QED

(***************************************************)
(*   SUM over Finite Set (reworked by Chun Tian)   *)
(***************************************************)

(* Some lemmas about ITSET, (\e acc. f e + acc) and b:extreal *)

val absorption =         #1 (EQ_IMP_RULE (SPEC_ALL ABSORPTION));
val delete_non_element = #1 (EQ_IMP_RULE (SPEC_ALL DELETE_NON_ELEMENT));

local
val tactics =
   GEN_TAC >> DISCH_TAC >> rpt GEN_TAC >> DISCH_TAC
 >> completeInduct_on `CARD s`
 >> POP_ASSUM (ASSUME_TAC o (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]))
 >> GEN_TAC >> SIMP_TAC bool_ss [ITSET_INSERT]
 >> rpt STRIP_TAC
 >> Q.ABBREV_TAC `t = REST (x INSERT s)`
 >> Q.ABBREV_TAC `y = CHOICE (x INSERT s)`
 >> `~(y IN t)` by PROVE_TAC [CHOICE_NOT_IN_REST]
 >> Cases_on `x IN s` >| (* 2 sub-goals here *)
  [ (* goal 1 (of 2) *)
    FULL_SIMP_TAC bool_ss [absorption] \\
    Cases_on `x = y` >| (* 2 sub-goals here *)
    [ (* goal 1.1 (of 2), x = y, no extreal property used *)
      POP_ASSUM SUBST_ALL_TAC \\ (* all `x` disappeared *)
      Suff `t = s DELETE y` >- SRW_TAC [][] \\
     `s = y INSERT t` by PROVE_TAC [NOT_IN_EMPTY, CHOICE_INSERT_REST] \\
      SRW_TAC [][DELETE_INSERT, delete_non_element],
      (* goal 1.2 (of 2), x <> y *)
     `s = y INSERT t` by PROVE_TAC [NOT_IN_EMPTY, CHOICE_INSERT_REST] \\
     `x IN t` by PROVE_TAC [IN_INSERT] \\
      Q.ABBREV_TAC `u = t DELETE x` \\
     `t = x INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] \\
     `~(x IN u)` by PROVE_TAC [IN_DELETE] \\
     `s = x INSERT (y INSERT u)` by simp[INSERT_COMM] \\
      POP_ASSUM SUBST_ALL_TAC \\ (* all `s` disappeared *)
      FULL_SIMP_TAC bool_ss [FINITE_INSERT, CARD_INSERT, DELETE_INSERT,IN_INSERT] \\
      (* now we start using properties of extreal *)
     `f x + b <> li /\ f y + b <> li` by METIS_TAC [add_not_infty] \\
      Q.PAT_X_ASSUM `!s' x' b'. (CARD s' < SUC (SUC (CARD u)) /\ FINITE s') /\ X ==> Y`
        (ASSUME_TAC o (Q.SPEC `u`)) \\
      FULL_SIMP_TAC arith_ss [] \\
     `!z. (z = x) \/ z IN u ==> f z <> li` by METIS_TAC [] \\
     `!z. (z = y) \/ z IN u ==> f z <> li` by METIS_TAC [] \\
      rpt STRIP_TAC \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`x`, `f y + b`])) \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`y`, `f x + b`])) \\
      Q.PAT_X_ASSUM `!x' b'. FINITE u /\ X ==> Y` K_TAC \\
      rpt STRIP_TAC >> RES_TAC \\
      ASM_SIMP_TAC std_ss [delete_non_element] \\
      METIS_TAC [add_assoc, add_comm, add_not_infty] ],
    (* goal 2 (of 2), ~(x IN s) *)
    ASM_SIMP_TAC bool_ss [delete_non_element] \\
   `x INSERT s = y INSERT t` by PROVE_TAC [NOT_EMPTY_INSERT, CHOICE_INSERT_REST] \\
    Cases_on `x = y` >| (* 2 sub-goals here *)
    [ (* goal 2.1 (of 2), no extreal property used *)
      POP_ASSUM SUBST_ALL_TAC \\ (* all `x` disappeared *)
      Suff `t = s` THEN1 SRW_TAC [][] \\
      FULL_SIMP_TAC bool_ss [EXTENSION, IN_INSERT] >> PROVE_TAC [],
      (* goal 2.2 (of 2), ~(x = y) *)
     `x IN t /\ y IN s` by PROVE_TAC [IN_INSERT] \\
      Q.ABBREV_TAC `u = s DELETE y` \\
     `~(y IN u)` by PROVE_TAC [IN_DELETE] \\
     `s = y INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] \\
      POP_ASSUM SUBST_ALL_TAC \\ (* all `s` disappeared *)
      FULL_SIMP_TAC bool_ss [IN_INSERT, FINITE_INSERT, CARD_INSERT,
                             DELETE_INSERT, delete_non_element] \\
     `t = x INSERT u` by
          (FULL_SIMP_TAC bool_ss [EXTENSION, IN_INSERT] THEN PROVE_TAC []) \\
      ASM_REWRITE_TAC [] \\
      (* now we start using properties of extreal *)
     `f x + b <> li /\ f y + b <> li` by METIS_TAC [add_not_infty] \\
      Q.PAT_X_ASSUM `!s x' b'. (CARD s < SUC (CARD u) /\ FINITE s') /\ X ==> Y`
        (ASSUME_TAC o (Q.SPEC `u`)) \\
      FULL_SIMP_TAC arith_ss [] \\
     `!z. (z = x) \/ z IN u ==> f z <> li` by METIS_TAC [] \\
     `!z. (z = y) \/ z IN u ==> f z <> li` by METIS_TAC [] \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`x`, `f y + b`])) \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`y`, `f x + b`])) \\
      Q.PAT_X_ASSUM `!x' b'. FINITE u /\ X ==> Y` K_TAC \\
      rpt STRIP_TAC >> RES_TAC \\
      ASM_SIMP_TAC std_ss [delete_non_element] \\
      METIS_TAC [add_assoc, add_comm, add_not_infty] ] ];

Theorem lem[local]:
  !li.
     li = PosInf ==>
     !f s. FINITE s ==>
           !x b. (!z. z IN (x INSERT s) ==> f z <> li) /\ b <> li ==>
                 ITSET (\e acc. f e + acc) (x INSERT s) b =
                 ITSET (\e acc. f e + acc) (s DELETE x)
                       ((\e acc. f e + acc) x b)
Proof tactics
QED

val lem' = Q.prove (
   `!li. (li = NegInf) ==>
        !f s. FINITE s ==>
              !x b. (!z. z IN (x INSERT s) ==> f z <> li) /\ b <> li ==>
                    (ITSET (\e acc. f e + acc) (x INSERT s) b =
                     ITSET (\e acc. f e + acc) (s DELETE x) ((\e acc. f e + acc) x b))`,
    tactics);

in
  (* |- !f s.
         FINITE s ==>
         !x b.
             (!z. z IN x INSERT s ==> f z <> PosInf) /\ b <> PosInf ==>
             (ITSET (\e acc. f e + acc) (x INSERT s) b =
              ITSET (\e acc. f e + acc) (s DELETE x)
                ((\e acc. f e + acc) x b))
   *)
  val lemma1  = REWRITE_RULE [] (Q.SPEC `PosInf` lem);

  (* |- !f s.
         FINITE s ==>
         !x b.
             (!z. z IN x INSERT s ==> f z <> NegInf) /\ b <> NegInf ==>
             (ITSET (\e acc. f e + acc) (x INSERT s) b =
              ITSET (\e acc. f e + acc) (s DELETE x)
                ((\e acc. f e + acc) x b))
   *)
  val lemma1' = REWRITE_RULE [] (Q.SPEC `NegInf` lem');
end;

(* lemma2 is independent of lemma1 *)
local val tactics =
   (rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `CARD s`
 >- METIS_TAC [CARD_EQ_0, ITSET_EMPTY]
 >> POP_ASSUM (ASSUME_TAC o
               (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]))
 >> RW_TAC std_ss []
 >> `0 < CARD s` by METIS_TAC [prim_recTheory.LESS_0]
 >> `CARD s <> 0` by RW_TAC real_ss [REAL_LT_NZ]
 >> `s <> {}` by METIS_TAC [CARD_EQ_0]
 >> `?x t. (s = x INSERT t) /\ x NOTIN t` by METIS_TAC [SET_CASES]
 >> FULL_SIMP_TAC std_ss [ITSET_INSERT, FINITE_INSERT]
 >> RW_TAC std_ss [REST_DEF]
 >> Q.ABBREV_TAC `y = CHOICE (x INSERT t)`
 >> Q.ABBREV_TAC `u = x INSERT t`
 >> `y IN u` by PROVE_TAC [CHOICE_DEF]
 >> `CARD (u DELETE y) = v` by METIS_TAC [CARD_DELETE, FINITE_INSERT, SUC_SUB1]
 >> METIS_TAC [add_not_infty, FINITE_INSERT, FINITE_DELETE, IN_DELETE])
in
  val lemma2  = Q.prove (
     `!f s. (!x. x IN s ==> f x <> PosInf) /\ FINITE s ==>
            !b. b <> PosInf ==> ITSET (\e acc. f e + acc) s b <> PosInf`, tactics);

  val lemma2' = Q.prove (
     `!f s. (!x. x IN s ==> f x <> NegInf) /\ FINITE s ==>
            !b. b <> NegInf ==> ITSET (\e acc. f e + acc) s b <> NegInf`, tactics);
end;

(** lemma3 depends on both lemma1 and lemma2 *)
Theorem lemma3[local]:
    !b f x s. (!y. y IN (x INSERT s) ==> f y <> PosInf) /\ b <> PosInf /\ FINITE s ==>
              (ITSET (\e acc. f e + acc) (x INSERT s) b =
               (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))
Proof
  (* proof *)
    Suff `!f s. FINITE s ==>
                !x b. (!y. y IN (x INSERT s) ==> f y <> PosInf) /\ b <> PosInf ==>
                      (ITSET (\e acc. f e + acc) (x INSERT s) b =
                       (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> IMP_RES_TAC lemma1 >> ASM_REWRITE_TAC []
 >> Suff `!s. FINITE s ==>
              !x b. (!y. y IN (x INSERT s) ==> f y <> PosInf) /\ b <> PosInf ==>
                   (ITSET (\e acc. f e + acc) s (f x + b) =
                    f x + (ITSET (\e acc. f e + acc) s b))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `t = s DELETE x` \\
     `FINITE t` by METIS_TAC [FINITE_DELETE] \\
     BETA_TAC \\
     Q.PAT_X_ASSUM `!s. FINITE s ==> X` (MP_TAC o Q.SPEC `t`) >> RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o SPEC_ALL) >> RW_TAC std_ss [] \\
     Suff `!y. y IN (x INSERT t) ==> f y <> PosInf` >- PROVE_TAC [] \\
     GEN_TAC >> STRIP_TAC \\
     Q.UNABBREV_TAC `t` \\
     Cases_on `y = x` >- (POP_ASSUM SUBST_ALL_TAC >> PROVE_TAC [IN_INSERT]) \\
     FULL_SIMP_TAC std_ss [IN_INSERT] \\
     PROVE_TAC [DELETE_SUBSET, SUBSET_DEF])
 >> KILL_TAC (* remove all assumptions *)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- SIMP_TAC bool_ss [ITSET_THM, FINITE_EMPTY]
 >> rpt STRIP_TAC
 >> `f x + b <> PosInf` by PROVE_TAC [IN_INSERT, add_not_infty]
 >> `!z. z IN (e INSERT s) ==> f z <> PosInf` by PROVE_TAC [IN_INSERT]
 >> `!x. x IN s ==> f x <> PosInf` by PROVE_TAC [IN_INSERT]
 >> `!y. y IN (x INSERT s) ==> f y <> PosInf` by PROVE_TAC [IN_INSERT, INSERT_COMM]
 >> ASM_SIMP_TAC bool_ss [lemma1, delete_non_element]
 >> `ITSET (\e acc. f e + acc) s b <> PosInf` by METIS_TAC [lemma2]
 >> Q.ABBREV_TAC `t = ITSET (\e acc. f e + acc) s b`
 >> Q.PAT_X_ASSUM `!x b. b <> PosInf => X` K_TAC
 >> METIS_TAC [add_assoc, add_comm, IN_INSERT]
QED

(** lemma3' depends on lemma1' and lemma2' (proof is the same as lemma3) *)
Theorem lemma3'[local]:
    !b f x s. (!y. y IN (x INSERT s) ==> f y <> NegInf) /\ b <> NegInf /\ FINITE s ==>
              (ITSET (\e acc. f e + acc) (x INSERT s) b =
               (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))
Proof
 (* proof *)
    Suff `!f s. FINITE s ==>
                !x b. (!y. y IN (x INSERT s) ==> f y <> NegInf) /\ b <> NegInf ==>
                      (ITSET (\e acc. f e + acc) (x INSERT s) b =
                       (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> IMP_RES_TAC lemma1' >> ASM_REWRITE_TAC []
 >> Suff `!s. FINITE s ==>
              !x b. (!y. y IN (x INSERT s) ==> f y <> NegInf) /\ b <> NegInf ==>
                   (ITSET (\e acc. f e + acc) s (f x + b) =
                    f x + (ITSET (\e acc. f e + acc) s b))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `t = s DELETE x` \\
     `FINITE t` by METIS_TAC [FINITE_DELETE] \\
     BETA_TAC \\
     Q.PAT_X_ASSUM `!s. FINITE s ==> X` (MP_TAC o Q.SPEC `t`) >> RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o SPEC_ALL) >> RW_TAC std_ss [] \\
     Suff `!y. y IN (x INSERT t) ==> f y <> NegInf` >- PROVE_TAC [] \\
     GEN_TAC >> STRIP_TAC \\
     Q.UNABBREV_TAC `t` \\
     Cases_on `y = x` >- (POP_ASSUM SUBST_ALL_TAC >> PROVE_TAC [IN_INSERT]) \\
     FULL_SIMP_TAC std_ss [IN_INSERT] \\
     PROVE_TAC [DELETE_SUBSET, SUBSET_DEF])
 >> KILL_TAC (* remove all assumptions *)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- SIMP_TAC bool_ss [ITSET_THM, FINITE_EMPTY]
 >> rpt STRIP_TAC
 >> `f x + b <> NegInf` by PROVE_TAC [IN_INSERT, add_not_infty]
 >> `!z. z IN (e INSERT s) ==> f z <> NegInf` by PROVE_TAC [IN_INSERT]
 >> `!x. x IN s ==> f x <> NegInf` by PROVE_TAC [IN_INSERT]
 >> `!y. y IN (x INSERT s) ==> f y <> NegInf` by PROVE_TAC [IN_INSERT, INSERT_COMM]
 >> ASM_SIMP_TAC bool_ss [lemma1', delete_non_element]
 >> `ITSET (\e acc. f e + acc) s b <> NegInf` by METIS_TAC [lemma2']
 >> Q.ABBREV_TAC `t = ITSET (\e acc. f e + acc) s b`
 >> Q.PAT_X_ASSUM `!x b. b <> NegInf => X` K_TAC
 >> METIS_TAC [add_assoc, add_comm, IN_INSERT]
QED

(* NOTE: EXTREAL_SUM_IMAGE is not defined if there're mixing of PosInfs and NegInfs
   in the summation, since ``PosInf + NegInf`` is not defined. *)

Definition EXTREAL_SUM_IMAGE_DEF[nocompute]:
  EXTREAL_SUM_IMAGE f s = ITSET (\e acc. f e + acc) s (0 :extreal)
End

(* Now theorems about EXTREAL_SUM_IMAGE itself *)
Theorem EXTREAL_SUM_IMAGE_EMPTY[simp] :
    !f. EXTREAL_SUM_IMAGE f {} = 0
Proof
    SRW_TAC [][ITSET_THM, EXTREAL_SUM_IMAGE_DEF]
QED

(* This is provable by (old) EXTREAL_SUM_IMAGE_THM but using original definition is much
   easier, because CHOICE and REST from singleton can be easily eliminated.
 *)
Theorem EXTREAL_SUM_IMAGE_SING[simp] :
    !f e. EXTREAL_SUM_IMAGE f {e} = f e
Proof
    SRW_TAC [][EXTREAL_SUM_IMAGE_DEF, ITSET_THM, add_rzero]
QED

(* This new theorem provides a "complete" picture for EXTREAL_SUM_IMAGE. *)
Theorem EXTREAL_SUM_IMAGE_THM:
    !f. (EXTREAL_SUM_IMAGE f {} = 0) /\
        (!e. EXTREAL_SUM_IMAGE f {e} = f e) /\
        (!e s. FINITE s /\ ((!x. x IN (e INSERT s) ==> f x <> PosInf) \/
                            (!x. x IN (e INSERT s) ==> f x <> NegInf)) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) =
               f e + EXTREAL_SUM_IMAGE f (s DELETE e)))
Proof
  let val thm  = SIMP_RULE std_ss [num_not_infty] (Q.SPEC `0` lemma3);
      val thm' = SIMP_RULE std_ss [num_not_infty] (Q.SPEC `0` lemma3');
  in
    rpt STRIP_TAC >- REWRITE_TAC [EXTREAL_SUM_IMAGE_EMPTY]
                  >- REWRITE_TAC [EXTREAL_SUM_IMAGE_SING]
    >> SIMP_TAC (srw_ss()) [EXTREAL_SUM_IMAGE_DEF]
    >| [ METIS_TAC [thm], METIS_TAC [thm'] ]
  end
QED

(* A weaker but practical version in which all values from function f is restricted *)
Theorem EXTREAL_SUM_IMAGE_INSERT:
    !f. (!x. f x <> PosInf) \/ (!x. f x <> NegInf) ==>
        !e s. FINITE s ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) =
               f e + EXTREAL_SUM_IMAGE f (s DELETE e))
Proof
    PROVE_TAC [EXTREAL_SUM_IMAGE_THM]
QED

Theorem EXTREAL_SUM_IMAGE_NOT_NEGINF:
    !f s. FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==> EXTREAL_SUM_IMAGE f s <> NegInf
Proof
  let val thm = ((SIMP_RULE std_ss [num_not_infty])
                 o (Q.SPECL [`f`, `s`, `0`])
                 o (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO])) lemma2';
  in
    rpt GEN_TAC >> STRIP_TAC \\
    REWRITE_TAC [EXTREAL_SUM_IMAGE_DEF] \\
    MATCH_MP_TAC thm >> ASM_REWRITE_TAC []
  end
QED

Theorem EXTREAL_SUM_IMAGE_NOT_POSINF:
    !f s. FINITE s /\ (!x. x IN s ==> f x <> PosInf) ==> EXTREAL_SUM_IMAGE f s <> PosInf
Proof
  let val thm = ((SIMP_RULE std_ss [num_not_infty])
                 o (Q.SPECL [`f`, `s`, `0`])
                 o (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO])) lemma2;
  in
    rpt GEN_TAC >> STRIP_TAC \\
    REWRITE_TAC [EXTREAL_SUM_IMAGE_DEF] \\
    MATCH_MP_TAC thm >> ASM_REWRITE_TAC []
  end
QED

Theorem EXTREAL_SUM_IMAGE_NOT_INFTY:
    !f s. (FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==> EXTREAL_SUM_IMAGE f s <> NegInf) /\
          (FINITE s /\ (!x. x IN s ==> f x <> PosInf) ==> EXTREAL_SUM_IMAGE f s <> PosInf)
Proof
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_NEGINF,
                 EXTREAL_SUM_IMAGE_NOT_POSINF]
QED

Theorem EXTREAL_SUM_IMAGE_PROPERTY_NEG:
    !f s. FINITE s ==>
          !e. (!x. x IN e INSERT s ==> f x <> NegInf) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) = f e + EXTREAL_SUM_IMAGE f (s DELETE e))
Proof
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM]
QED

Theorem EXTREAL_SUM_IMAGE_PROPERTY_POS:
    !f s. FINITE s ==>
          !e. (!x. x IN e INSERT s ==> f x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) = f e + EXTREAL_SUM_IMAGE f (s DELETE e))
Proof
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM]
QED

Theorem EXTREAL_SUM_IMAGE_PROPERTY:
    !f s. FINITE s  ==>
          !e. (!x. x IN e INSERT s ==> f x <> NegInf) \/
              (!x. x IN e INSERT s ==> f x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) = f e + EXTREAL_SUM_IMAGE f (s DELETE e))
Proof
  PROVE_TAC [EXTREAL_SUM_IMAGE_PROPERTY_NEG,
             EXTREAL_SUM_IMAGE_PROPERTY_POS]
QED

Theorem EXTREAL_SUM_IMAGE_POS:
     !f s. FINITE s /\ (!x. x IN s ==> 0 <= f x) ==>
           0 <= EXTREAL_SUM_IMAGE f s
Proof
  Suff `!s. FINITE s ==> (\s. !f. (!x. x IN s ==> 0 <= f x) ==>
            0 <= EXTREAL_SUM_IMAGE f s) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,le_refl]
  >> `!x. x IN e INSERT s ==> f x <> NegInf`
        by METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans]
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,delete_non_element]
  >> METIS_TAC [le_add,IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_NEG:
    !f s. FINITE s /\ (!x. x IN s ==> f x <= 0) ==> EXTREAL_SUM_IMAGE f s <= 0
Proof
    Suff `!s. FINITE s ==>
              (\s. !f. (!x. x IN s ==> f x <= 0) ==>
                   EXTREAL_SUM_IMAGE f s <= 0) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, le_refl]
 >> `!x. x IN e INSERT s ==> f x <> PosInf`
        by METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, let_trans]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, delete_non_element]
 >> METIS_TAC [le_add_neg, IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_SPOS:
    !f s. FINITE s /\ (~(s = {})) /\ (!x. x IN s ==> 0 < f x) ==>
          0 < EXTREAL_SUM_IMAGE f s
Proof
    Suff `!s. FINITE s ==> (\s. !f. s <> {} /\ (!x. x IN s ==> 0 < f x) ==>
                                    0 < EXTREAL_SUM_IMAGE f s) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> `!x. x IN e INSERT s ==> f x <> NegInf`
        by METIS_TAC [IN_INSERT, lt_infty, lt_trans, lt_imp_le, extreal_of_num_def]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, delete_non_element]
 >> Cases_on `s = {}`
 >- METIS_TAC [EXTREAL_SUM_IMAGE_EMPTY, add_rzero, IN_INSERT]
 >> METIS_TAC [lt_add, IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_SNEG:
    !f s. FINITE s /\ (~(s = {})) /\ (!x. x IN s ==> f x < 0) ==>
          EXTREAL_SUM_IMAGE f s < 0
Proof
    Suff `!s. FINITE s ==> (\s. !f. s <> {} /\ (!x. x IN s ==> f x < 0) ==>
                                    EXTREAL_SUM_IMAGE f s < 0) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> `!x. x IN e INSERT s ==> f x <> PosInf`
        by METIS_TAC [IN_INSERT, lt_infty, lt_trans, lt_imp_le, extreal_of_num_def]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, delete_non_element]
 >> Cases_on `s = {}`
 >- METIS_TAC [EXTREAL_SUM_IMAGE_EMPTY, add_rzero, IN_INSERT]
 >> METIS_TAC [lt_add_neg, IN_INSERT]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_IF_ELIM:
    !s P f. FINITE s /\ (!x. x IN s ==> P x) /\
            ((!x. x IN s ==> f x <> NegInf) \/ !x. x IN s ==> f x <> PosInf)
        ==> (EXTREAL_SUM_IMAGE (\x. if P x then f x else 0) s = EXTREAL_SUM_IMAGE f s)
Proof
    Suff `!s. FINITE s ==>
             (\s. !P f. (!x. x IN s ==> P x) /\
                        ((!x. x IN s ==> f x <> NegInf) \/ !x. x IN s ==> f x <> PosInf) ==>
                        (EXTREAL_SUM_IMAGE (\x. if P x then f x else 0) s =
                         EXTREAL_SUM_IMAGE f s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY]
 >- (`!x. x IN e INSERT s ==> (\x. if P x then f x else 0) x <> NegInf`
        by METIS_TAC [extreal_of_num_def, lt_infty, lt_imp_ne] \\
     RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY] \\
     METIS_TAC [IN_INSERT, DELETE_NON_ELEMENT, lt_infty] )
 >> `!x. x IN (e INSERT s) ==> ((\x. if P x then f x else 0) x <> PosInf)`
        by METIS_TAC[extreal_of_num_def,lt_infty,lt_imp_ne]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >- METIS_TAC [IN_INSERT, DELETE_NON_ELEMENT]
 >> METIS_TAC [IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_FINITE_SAME :
    !s. FINITE s ==> !f p. p IN s /\ (!q. q IN s ==> (f p = f q)) ==>
                          (EXTREAL_SUM_IMAGE f s = (&(CARD s)) * f p)
Proof
    Suff `!s. FINITE s ==>
             (\s. !f p. p IN s /\ (!q. q IN s ==> (f p = f q))
              ==> (EXTREAL_SUM_IMAGE f s = (&(CARD s)) * f p)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, CARD_EMPTY, mul_lzero, DELETE_NON_ELEMENT]
 >> Know ‘(!x. x IN e INSERT s ==> f x <> NegInf) \/ (!x. x IN e INSERT s ==> f x <> PosInf)’
 >- (Cases_on ‘f p = NegInf’
     >- (DISJ2_TAC >> GEN_TAC >> STRIP_TAC \\
        ‘f x = NegInf’ by METIS_TAC [IN_INSERT] >> POP_ORW \\
         rw []) \\
     DISJ1_TAC >> GEN_TAC >> STRIP_TAC \\
     METIS_TAC [IN_INSERT])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o
      (MATCH_MP (MATCH_MP EXTREAL_SUM_IMAGE_PROPERTY (ASSUME “FINITE s”))))
 >> RW_TAC real_ss [DELETE_NON_ELEMENT]
 >> `f p = f e` by FULL_SIMP_TAC std_ss [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
 >> RW_TAC std_ss [CARD_INSERT, ADD1, extreal_of_num_def, GSYM REAL_ADD, GSYM extreal_add_def]
 >> RW_TAC std_ss [Once add_comm_normal, GSYM extreal_of_num_def]
 >> `(&CARD s) <> NegInf /\ 1 <> NegInf /\ (&CARD s) <> PosInf /\ 1 <> PosInf /\ 0 <= (&CARD s) /\ 0 <= 1`
       by METIS_TAC [extreal_not_infty, extreal_of_num_def, le_num, le_01]
 >> RW_TAC std_ss [add_rdistrib, mul_lone]
 >> Suff `EXTREAL_SUM_IMAGE f s = &(CARD s) * f e` >- Rewr
 >> (MP_TAC o Q.SPECL [`s`]) SET_CASES >> RW_TAC std_ss []
 >- RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, CARD_EMPTY, mul_lzero]
 >> `f e = f x` by FULL_SIMP_TAC std_ss [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
 >> Q.PAT_X_ASSUM `!f p. b` MATCH_MP_TAC >> METIS_TAC [IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_FINITE_CONST : (* was: extreal_sum_image_finite_corr *)
    !P. FINITE P ==>
        !f x. (!y. y IN P ==> (f y = x)) ==> (EXTREAL_SUM_IMAGE f P = (&(CARD P)) * x)
Proof
    rw []
 >> Cases_on ‘P = {}’ >> simp []
 >> ‘?m. m IN P’ by metis_tac [MEMBER_NOT_EMPTY]
 >> ‘x = f m’ by fs [] >> rw []
 >> irule EXTREAL_SUM_IMAGE_FINITE_SAME >> rw []
QED

Theorem EXTREAL_SUM_IMAGE_ZERO:   !s. FINITE s ==> (EXTREAL_SUM_IMAGE (\x. 0) s = 0)
Proof
    RW_TAC std_ss []
 >> Suff `EXTREAL_SUM_IMAGE (\x. 0) s = &CARD s * 0`
 >- METIS_TAC [mul_rzero]
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_FINITE_CONST
 >> RW_TAC std_ss [num_not_infty]
QED

Theorem EXTREAL_SUM_IMAGE_0:
    !f s. FINITE s /\ (!x. x IN s ==> (f x = 0)) ==> (EXTREAL_SUM_IMAGE f s = 0)
Proof
    Suff `!s. FINITE s ==>
             (\s. !f. (!x. x IN s ==> (f x = 0)) ==> (EXTREAL_SUM_IMAGE f s = 0)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, DELETE_NON_ELEMENT]
 >> `!x. x IN (e INSERT s) ==> f x <> PosInf` by PROVE_TAC [num_not_infty]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> METIS_TAC [IN_INSERT, add_lzero]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_IN_IF:
    !s. FINITE s ==>
        !f. ((!x. x IN s ==> f x <> NegInf) \/
             (!x. x IN s ==> f x <> PosInf)) ==>
            (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s)
Proof
    Suff `!s. FINITE s ==>
              (\s. !f. ((!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf)) ==>
                       (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s)) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY]
 >- (`!x. (\x. if x IN e INSERT s then f x else 0) x <> NegInf`
         by RW_TAC std_ss [extreal_not_infty, extreal_of_num_def]
     >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY]
     >> `s DELETE e = s` by rw[GSYM DELETE_NON_ELEMENT]
     >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s`
         by METIS_TAC [IN_INSERT]
     >> Q.PAT_X_ASSUM `!x:'a. x IN e INSERT s ==> f x <> NegInf` K_TAC
     >> FULL_SIMP_TAC real_ss [IN_INSERT])
 >> `!x. (\x. if x IN e INSERT s then f x else 0) x <> PosInf`
         by RW_TAC std_ss [extreal_not_infty, extreal_of_num_def]
 >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> `s DELETE e = s` by rw [GSYM DELETE_NON_ELEMENT]
 >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s`
         by METIS_TAC [IN_INSERT]
 >> Q.PAT_X_ASSUM `!x:'a. x IN e INSERT s ==> f x <> PosInf` K_TAC
 >> FULL_SIMP_TAC std_ss [IN_INSERT]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_CMUL :
    !s. FINITE s ==>
        !f c. (!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE (\x. Normal c * f x) s = Normal c * (EXTREAL_SUM_IMAGE f s))
Proof
    Suff `!f c s.
             FINITE s ==>
             (\s. (!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf) ==>
                  (EXTREAL_SUM_IMAGE (\x. Normal c * f x) s = Normal c * (EXTREAL_SUM_IMAGE f s))) s`
 >- METIS_TAC []
 >> STRIP_TAC >> STRIP_TAC >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,mul_rzero]
 >- ( Cases_on `0 <= c`
      >- (`!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> NegInf` by METIS_TAC [mul_not_infty,IN_INSERT]
          >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
          >> METIS_TAC [add_ldistrib_normal,EXTREAL_SUM_IMAGE_NOT_INFTY,IN_INSERT])
      >> `!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> PosInf`
                by METIS_TAC [mul_not_infty,real_lt,REAL_LT_IMP_LE]
      >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
      >> METIS_TAC [add_ldistrib_normal,EXTREAL_SUM_IMAGE_NOT_INFTY,IN_INSERT] )
 >> Cases_on `0 <= c`
 >- (`!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> PosInf` by METIS_TAC [mul_not_infty] \\
     FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT] \\
     METIS_TAC [add_ldistrib_normal, EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT])
 >> `!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> NegInf`
                by METIS_TAC [mul_not_infty, real_lt, REAL_LT_IMP_LE]
 >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> METIS_TAC [add_ldistrib_normal, EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_MINUS :
    !f s. FINITE s /\
         ((!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf)) ==>
          EXTREAL_SUM_IMAGE (\x. -f x) s = -EXTREAL_SUM_IMAGE f s
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> simp [neg_minus1']
 >> irule EXTREAL_SUM_IMAGE_CMUL >> simp []
QED

(* more antecedents added, cf. SUM_IMAGE_INJ_o *)
Theorem EXTREAL_SUM_IMAGE_IMAGE :
    !s. FINITE s ==>
        !f'. INJ f' s (IMAGE f' s) ==>
             !f. (!x. x IN (IMAGE f' s) ==> f x <> NegInf) \/
                 (!x. x IN (IMAGE f' s) ==> f x <> PosInf)
             ==> (EXTREAL_SUM_IMAGE f (IMAGE f' s) = EXTREAL_SUM_IMAGE (f o f') s)
Proof
     Suff `!s. FINITE s ==>
               (\s. !f'. INJ f' s (IMAGE f' s) ==>
                         !f. (!x. x IN (IMAGE f' s) ==> f x <> NegInf) \/
                             (!x. x IN (IMAGE f' s) ==> f x <> PosInf) ==>
                             (EXTREAL_SUM_IMAGE f (IMAGE f' s) =
                              EXTREAL_SUM_IMAGE (f o f') s)) s`
  >- METIS_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,IMAGE_EMPTY,IMAGE_INSERT,INJ_DEF]
  >- (`FINITE (IMAGE f' s)` by METIS_TAC [IMAGE_FINITE]
      >> `!x. x IN e INSERT s ==> (f o f') x <> NegInf` by METIS_TAC [o_DEF]
      >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
      >> `~ (f' e IN IMAGE f' s)`
        by (RW_TAC std_ss [IN_IMAGE] >> reverse (Cases_on `x IN s`)
            >- ASM_REWRITE_TAC [] >> METIS_TAC [IN_INSERT])
      >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
      >> `(IMAGE f' s) DELETE f' e = IMAGE f' s` by METIS_TAC [DELETE_NON_ELEMENT]
      >> ASM_REWRITE_TAC []
      >> `(!x. x IN s ==> f' x IN IMAGE f' s)` by METIS_TAC [IN_IMAGE]
      >> `(!x y. x IN s /\ y IN s ==> (f' x = f' y) ==> (x = y))` by METIS_TAC [IN_INSERT]
      >> `(!x. x IN IMAGE f' s ==> f x <> NegInf)` by METIS_TAC [IN_INSERT]
      >> FULL_SIMP_TAC std_ss [])
  >> `FINITE (IMAGE f' s)` by METIS_TAC [IMAGE_FINITE]
  >> `!x. x IN e INSERT s ==> (f o f') x <> PosInf` by METIS_TAC [o_DEF]
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
  >> `f' e NOTIN IMAGE f' s`
        by (RW_TAC std_ss [IN_IMAGE] >> reverse (Cases_on `x IN s`)
            >- ASM_REWRITE_TAC [] >> METIS_TAC [IN_INSERT])
  >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  >> `(IMAGE f' s) DELETE f' e = IMAGE f' s` by METIS_TAC [DELETE_NON_ELEMENT]
  >> ASM_REWRITE_TAC []
  >> `(!x. x IN s ==> f' x IN IMAGE f' s)` by METIS_TAC [IN_IMAGE]
  >> `(!x y. x IN s /\ y IN s ==> (f' x = f' y) ==> (x = y))` by METIS_TAC [IN_INSERT]
  >> `(!x. x IN IMAGE f' s ==> f x <> PosInf)` by METIS_TAC [IN_INSERT]
  >> FULL_SIMP_TAC std_ss []
QED

Theorem EXTREAL_SUM_IMAGE_PERMUTES :
    !s. FINITE s ==> !g. g PERMUTES s ==>
        !f. (!x. x IN (IMAGE g s) ==> f x <> NegInf) \/
            (!x. x IN (IMAGE g s) ==> f x <> PosInf) ==>
            (EXTREAL_SUM_IMAGE (f o g) s = EXTREAL_SUM_IMAGE f s)
Proof
    NTAC 5 STRIP_TAC >> DISCH_TAC
 >> `INJ g s s /\ SURJ g s s` by METIS_TAC [BIJ_DEF]
 >> `IMAGE g s = s` by SRW_TAC[][GSYM IMAGE_SURJ]
 >> `s SUBSET univ(:'a)` by SRW_TAC[][SUBSET_UNIV]
 >> `INJ g s univ(:'a)` by METIS_TAC[INJ_SUBSET, SUBSET_REFL]
 >> Know `EXTREAL_SUM_IMAGE (f o g) s = EXTREAL_SUM_IMAGE f (IMAGE g s)`
 >- (MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_IMAGE >> rw [])
 >> SRW_TAC[][]
QED

Theorem EXTREAL_SUM_IMAGE_DISJOINT_UNION : (* more antecedents added *)
    !s s'. FINITE s /\ FINITE s' /\ DISJOINT s s' ==>
           !f. (!x. x IN s UNION s' ==> f x <> NegInf) \/
               (!x. x IN s UNION s' ==> f x <> PosInf) ==>
               (EXTREAL_SUM_IMAGE f (s UNION s') =
                EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')
Proof
  Suff `!s. FINITE s ==> (\s. !s'. FINITE s' ==>
            (\s'. DISJOINT s s' ==>
                  (!f. (!x. x IN s UNION s' ==> f x <> NegInf) \/
                       (!x. x IN s UNION s' ==> f x <> PosInf) ==>
                       (EXTREAL_SUM_IMAGE f (s UNION s') =
                        EXTREAL_SUM_IMAGE f s +
                        EXTREAL_SUM_IMAGE f s'))) s') s`
  >- METIS_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> CONJ_TAC
  >- RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY,add_lzero]
  >> rpt STRIP_TAC
  >> CONV_TAC (BETA_CONV) >> MATCH_MP_TAC FINITE_INDUCT
  >> CONJ_TAC
  >- RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY,add_rzero]
  >> FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
  >> ONCE_REWRITE_TAC [DISJOINT_SYM]
  >> RW_TAC std_ss [INSERT_UNION, DISJOINT_INSERT, IN_INSERT]
  >- ( FULL_SIMP_TAC std_ss [DISJOINT_SYM]
       >> ONCE_REWRITE_TAC [UNION_COMM] >> RW_TAC std_ss [INSERT_UNION]
       >> ONCE_REWRITE_TAC [UNION_COMM] >> ONCE_REWRITE_TAC [INSERT_COMM]
       >> `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
       >> Q.ABBREV_TAC `Q = e INSERT s UNION s'`
       >> `!x. x IN e INSERT s ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> `!x. x IN e' INSERT s' ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> `!x. x IN e' INSERT Q ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
       >> Q.UNABBREV_TAC `Q`
       >> `~ (e' IN (e INSERT s UNION s'))`
              by (RW_TAC std_ss[IN_INSERT, IN_UNION] \\
                FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT])
       >> `!x. x IN e INSERT (s UNION s') ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> `~(e IN (s UNION s'))` by METIS_TAC [IN_UNION,DELETE_NON_ELEMENT]
       >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT,EXTREAL_SUM_IMAGE_PROPERTY,FINITE_UNION]
       >> `EXTREAL_SUM_IMAGE f s <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION]
       >> `EXTREAL_SUM_IMAGE f s' <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION,IN_INSERT]
       >> FULL_SIMP_TAC std_ss [IN_INSERT]
       >> RW_TAC std_ss [add_assoc]
       >> `f e' + (f e + EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s') =
          (f e + (EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')) + f e'`
              by METIS_TAC [add_comm,add_not_infty,add_assoc,IN_INSERT]
       >> POP_ORW
       >> RW_TAC std_ss [add_assoc]
       >> METIS_TAC [add_not_infty,add_comm,add_assoc] )
  >> FULL_SIMP_TAC std_ss [DISJOINT_SYM]
  >> ONCE_REWRITE_TAC [UNION_COMM] >> RW_TAC std_ss [INSERT_UNION]
  >> ONCE_REWRITE_TAC [UNION_COMM] >> ONCE_REWRITE_TAC [INSERT_COMM]
  >> `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
  >> Q.ABBREV_TAC `Q = e INSERT s UNION s'`
  >> `!x. x IN e INSERT s ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> `!x. x IN e' INSERT s' ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> `!x. x IN e' INSERT Q ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> Q.UNABBREV_TAC `Q`
  >> `~ (e' IN (e INSERT s UNION s'))`
      by (RW_TAC std_ss [IN_INSERT, IN_UNION] \\
          FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT])
  >> `!x. x IN e INSERT (s UNION s') ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> `~(e IN (s UNION s'))` by METIS_TAC [IN_UNION,DELETE_NON_ELEMENT]
  >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT,EXTREAL_SUM_IMAGE_PROPERTY,FINITE_UNION]
  >> `EXTREAL_SUM_IMAGE f s <> PosInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION]
  >> `EXTREAL_SUM_IMAGE f s' <> PosInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION,IN_INSERT]
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >> RW_TAC std_ss [add_assoc]
  >> `f e' + (f e + EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s') =
       (f e + (EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')) + f e'`
              by METIS_TAC [add_comm,add_not_infty,add_assoc,IN_INSERT]
  >> POP_ORW
  >> RW_TAC std_ss [add_assoc]
  >> METIS_TAC [add_not_infty, add_comm, add_assoc]
QED

Theorem EXTREAL_SUM_IMAGE_EQ_CARD :
    !s. FINITE s ==>
       (EXTREAL_SUM_IMAGE (\x. if x IN s then 1 else 0) s = &(CARD s))
Proof
    Suff `!s. FINITE s ==>
             (\s. EXTREAL_SUM_IMAGE (\x. if x IN s then 1 else 0) s = (&(CARD s))) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, CARD_EMPTY, IN_INSERT]
 >> `!x. (\x. if (x = e) \/ x IN s then 1 else 0) x <> NegInf`
      by RW_TAC real_ss [extreal_of_num_def,extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> (MP_TAC o Q.SPECL [`s`]) CARD_INSERT
 >> `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
 >> RW_TAC std_ss [ADD1,extreal_of_num_def, GSYM REAL_ADD, GSYM extreal_add_eq]
 >> RW_TAC std_ss [GSYM extreal_of_num_def]
 >> Suff `EXTREAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) s =
          EXTREAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s`
 >- METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, add_comm, extreal_not_infty,
               extreal_of_num_def]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_IN_IF]
QED

Theorem EXTREAL_SUM_IMAGE_INV_CARD_EQ_1:
    !s. s <> {} /\ FINITE s ==>
        (EXTREAL_SUM_IMAGE (\x. if x IN s then inv (&(CARD s)) else 0) s = 1)
Proof
    rpt STRIP_TAC
 >> `(\x. if x IN s then inv (& (CARD s)) else 0) =
     (\x. inv (& (CARD s)) * (\x. if x IN s then 1 else 0) x)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [mul_rzero, mul_rone])
 >> POP_ORW
 >> `CARD s <> 0` by METIS_TAC [CARD_EQ_0]
 >> `inv (&CARD s) = Normal (inv (&CARD s))`
    by FULL_SIMP_TAC real_ss [extreal_inv_def, extreal_of_num_def]
 >> POP_ORW
 >> `!x. (\x. if x IN s then 1 else 0) x <> NegInf`
    by METIS_TAC [extreal_not_infty, extreal_of_num_def]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL, EXTREAL_SUM_IMAGE_EQ_CARD]
 >> RW_TAC std_ss [extreal_of_num_def,extreal_mul_def]
 >> `&CARD s <> 0r` by FULL_SIMP_TAC real_ss [extreal_inv_def, extreal_of_num_def]
 >> METIS_TAC [REAL_MUL_LINV]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_INTER_NONZERO:
    !s. FINITE s ==>
        !f. (!x. x IN s ==> f x <> NegInf) \/
            (!x. x IN s ==> f x <> PosInf) ==>
           (EXTREAL_SUM_IMAGE f (s INTER (\p. ~(f p = 0))) =
            EXTREAL_SUM_IMAGE f s)
Proof
 (* proof *)
    Suff `!s. FINITE s ==>
             (\s. !f. (!x. x IN s ==> f x <> NegInf) \/
                      (!x. x IN s ==> f x <> PosInf) ==>
                      (EXTREAL_SUM_IMAGE f (s INTER (\p. ~(f p = 0))) =
                       EXTREAL_SUM_IMAGE f s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, INTER_EMPTY, INSERT_INTER]
 >- ( Cases_on `e IN (\p. f p <> 0)`
      >- (RW_TAC std_ss []
          >> `~(e IN (s INTER (\p. ~(f p = 0))))` by RW_TAC std_ss [IN_INTER]
          >> `!x. x IN (e INSERT s INTER (\p. f p <> 0)) ==> f x <> NegInf`
                by METIS_TAC [IN_INTER,IN_INSERT]
          >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT,INTER_FINITE]
          >> FULL_SIMP_TAC std_ss [IN_INSERT])
      >> RW_TAC std_ss []
      >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT,add_lzero,IN_ABS] )
 >> Cases_on `e IN (\p. f p <> 0)`
 >- ( RW_TAC std_ss []
      >> `~(e IN (s INTER (\p. ~(f p = 0))))` by RW_TAC std_ss [IN_INTER]
      >> `!x. x IN (e INSERT s INTER (\p. f p <> 0)) ==> f x <> PosInf`
            by METIS_TAC [IN_INTER,IN_INSERT]
      >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT,INTER_FINITE]
      >> FULL_SIMP_TAC std_ss [IN_INSERT] )
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> FULL_SIMP_TAC std_ss [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, add_lzero, IN_ABS]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_INTER_ELIM:
     !s. FINITE s ==>
         !f s'. ((!x. x IN s ==> f x <> NegInf) \/
                 (!x. x IN s ==> f x <> PosInf)) /\
                (!x. (~(x IN s')) ==> (f x = 0)) ==>
                (EXTREAL_SUM_IMAGE f (s INTER s') =
                 EXTREAL_SUM_IMAGE f s)
Proof
  Suff `!s. FINITE s ==>
        (\s. !f s'. ((!x. x IN s ==> f x <> NegInf) \/
                     (!x. x IN s ==> f x <> PosInf)) /\
                    (!x. (~(x IN s')) ==> (f x = 0)) ==>
                    (EXTREAL_SUM_IMAGE f (s INTER s') =
                     EXTREAL_SUM_IMAGE f s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [INTER_EMPTY,INSERT_INTER]
  >- (FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
      >> Cases_on `e IN s'`
      >- (`~ (e IN (s INTER s'))` by (rw[IN_INTER] >> fs[DELETE_NON_ELEMENT])
          >> `!x. x IN e INSERT (s INTER s') ==> f x <> NegInf` by METIS_TAC [IN_INTER,IN_INSERT]
          >> FULL_SIMP_TAC std_ss [INTER_FINITE, EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
          >> FULL_SIMP_TAC std_ss [IN_INSERT]
          >> METIS_TAC [IN_INTER,DELETE_NON_ELEMENT])
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> METIS_TAC [DELETE_NON_ELEMENT,add_lzero])
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> Cases_on `e IN s'`
  >- (`~ (e IN (s INTER s'))` by (rw[IN_INTER] >> fs[DELETE_NON_ELEMENT])
      >> `!x. x IN e INSERT (s INTER s') ==> f x <> PosInf` by METIS_TAC [IN_INTER,IN_INSERT]
      >> FULL_SIMP_TAC std_ss [INTER_FINITE, EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> METIS_TAC [IN_INTER,DELETE_NON_ELEMENT])
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >> METIS_TAC [DELETE_NON_ELEMENT,add_lzero]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_ZERO_DIFF:
    !s. FINITE s ==> !f t. ((!x. x IN s ==> f x <> NegInf) \/
                             (!x. x IN s ==> f x <> PosInf)) /\
                           (!x. x IN t ==> (f x = 0)) ==>
                           (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f (s DIFF t))
Proof
  RW_TAC std_ss []
  >> `s = (s DIFF t) UNION (s INTER t)` by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
                                            >> METIS_TAC [])
  >> `FINITE (s DIFF t) /\ FINITE (s INTER t)` by METIS_TAC [INTER_FINITE, FINITE_DIFF]
  >> `DISJOINT (s DIFF t) (s INTER t)` by (RW_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY,
                                           EXTENSION, IN_DIFF] >> METIS_TAC [])
  >> `EXTREAL_SUM_IMAGE f (s INTER t) = 0` by METIS_TAC [EXTREAL_SUM_IMAGE_0, IN_INTER]
  >> METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION, add_rzero]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_MONO:
     !s. FINITE s ==>
           !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\
                  (!x. x IN s ==> f x <= f' x) ==>
                  EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f' s
Proof
   Suff `!s. FINITE s ==>
             (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                          (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\
                         (!x. x IN s ==> f x <= f' x) ==>
                         EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f' s) s`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,le_refl]
   >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT, IN_INSERT,
                      DISJ_IMP_THM, FORALL_AND_THM]
   >> METIS_TAC [le_add2,EXTREAL_SUM_IMAGE_NOT_INFTY]
QED

(* NOTE: There's no way to have better (and weaker) antecedents such as
  “(!x. x IN s ==> f x <= g x) /\ (?x. x IN s /\ f x < g x)” as in
   REAL_SUM_IMAGE_MONO_LT, because, if there exists x such that f x = g x = PosInf,
   then both sums become PosInf, making the conclusion impossible.
 *)
Theorem EXTREAL_SUM_IMAGE_MONO_LT :
    !f g s. FINITE s /\ s <> {} /\
            ((!x. x IN s ==> f x <> NegInf /\ g x <> NegInf) \/
             (!x. x IN s ==> f x <> PosInf /\ g x <> PosInf)) /\
            (!x. x IN s ==> f x < g x) ==>
            EXTREAL_SUM_IMAGE f s < EXTREAL_SUM_IMAGE g s
Proof
    Suff ‘!s. FINITE s ==>
              (\s. s <> {} ==>
                  !f g. ((!x. x IN s ==> f x <> NegInf /\ g x <> NegInf) \/
                          (!x. x IN s ==> f x <> PosInf /\ g x <> PosInf)) /\
                         (!x. x IN s ==> f x < g x) ==>
                          EXTREAL_SUM_IMAGE f s < EXTREAL_SUM_IMAGE g s) s’
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, le_refl, NOT_IN_EMPTY]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT, IN_INSERT,
                          DISJ_IMP_THM, FORALL_AND_THM]
 >| [ (* goal 1 (of 2) *)
      Cases_on ‘s = {}’ >> simp [EXTREAL_SUM_IMAGE_EMPTY] \\
      MATCH_MP_TAC lt_add2 >> art [] \\
      FIRST_X_ASSUM irule >> rw [],
      (* goal 2 (of 2) *)
      Cases_on ‘s = {}’ >> simp [EXTREAL_SUM_IMAGE_EMPTY] \\
      MATCH_MP_TAC lt_add2 >> art [] \\
      FIRST_X_ASSUM irule >> rw [] ]
QED

Theorem EXTREAL_SUM_IMAGE_MONO_SET:
     !f s t. (FINITE s /\ FINITE t /\ s SUBSET t /\ (!x. x IN t ==> 0 <= f x)) ==>
             EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f t
Proof
  RW_TAC std_ss []
  >> `t = s UNION (t DIFF s)` by RW_TAC std_ss [UNION_DIFF]
  >> `FINITE (t DIFF s)` by RW_TAC std_ss [FINITE_DIFF]
  >> `DISJOINT s (t DIFF s)`
        by (`DISJOINT s (t DIFF s)`
                by (rw [DISJOINT_DEF,IN_DIFF,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER] \\
                    metis_tac[]) \\
            metis_tac[])
  >> `!x. x IN (s UNION (t DIFF s)) ==> f x <> NegInf`
        by METIS_TAC [extreal_of_num_def,extreal_not_infty,lt_infty,lte_trans]
  >> `EXTREAL_SUM_IMAGE f t = EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f (t DIFF s)`
        by METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
  >> POP_ORW
  >> METIS_TAC [le_add2,le_refl,add_rzero,EXTREAL_SUM_IMAGE_POS,IN_DIFF]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_EQ:
     !s. FINITE s ==>
           !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\
                   (!x. x IN s ==> (f x = f' x)) ==>
                (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)
Proof
  Suff `!s. FINITE s ==>
                (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\ (!x. x IN s ==> (f x = f' x)) ==>
                (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)) s`
  >- PROVE_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT, IN_INSERT,
                           DISJ_IMP_THM, FORALL_AND_THM]
  >> METIS_TAC []
QED

(* ‘!n. 0 <= f n’ can be weakened but enough for now *)
Theorem EXTREAL_SUM_IMAGE_OFFSET :
    !f m n. m <= n /\ (!n. 0 <= f n) ==>
            EXTREAL_SUM_IMAGE f (count n) =
            EXTREAL_SUM_IMAGE f (count m) +
            EXTREAL_SUM_IMAGE (\i. f (i + m)) (count (n - m))
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘h = \(i :num). i + m’
 >> ‘(\i. f (i + m)) = f o h’ by METIS_TAC [o_DEF] >> POP_ORW
 (* applying EXTREAL_SUM_IMAGE_IMAGE *)
 >> Know ‘EXTREAL_SUM_IMAGE (f o h) (count (n - m)) =
          EXTREAL_SUM_IMAGE f (IMAGE h (count (n - m)))’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     irule EXTREAL_SUM_IMAGE_IMAGE >> rw []
     >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> rw [] \\
         METIS_TAC [pos_not_neginf]) \\
     rw [INJ_DEF, Abbr ‘h’]) >> Rewr'
 (* preparing for EXTREAL_SUM_IMAGE_DISJOINT_UNION *)
 >> Know ‘count n = count m UNION (IMAGE h (count (n - m)))’
 >- (rw [Once EXTENSION] >> EQ_TAC >> rw [Abbr ‘h’] \\
    ‘x < m \/ m <= x’ by rw [] >- art [] \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘x - m’ >> rw [])
 >> Rewr'
 (* applying EXTREAL_SUM_IMAGE_DISJOINT_UNION *)
 >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp []
 >> reverse CONJ_TAC
 >- (DISJ1_TAC >> rw [] >> METIS_TAC [pos_not_neginf])
 >> rw [DISJOINT_ALT, Abbr ‘h’]
QED

(* if the first N items of (g n) are all zero, we can ignore them in SIGMA *)
Theorem EXTREAL_SUM_IMAGE_EQ_SHIFT :
    !f g N. (!n. n < N ==> g n = 0) /\ (!n. 0 <= f n /\ f n = g (n + N)) ==>
            !n. EXTREAL_SUM_IMAGE f (count n) = EXTREAL_SUM_IMAGE g (count (n + N))
Proof
    rpt STRIP_TAC
 >> Know ‘EXTREAL_SUM_IMAGE g (count (n + N)) =
          EXTREAL_SUM_IMAGE g (count N) +
          EXTREAL_SUM_IMAGE (\i. g (i + N)) (count (n + N - N))’
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_OFFSET >> rw [] \\
    ‘n < N \/ N <= n’ by rw [] >- rw [] \\
    ‘n = n - N + N’ by rw [] >> POP_ORW >> METIS_TAC [])
 >> Rewr'
 >> Know ‘EXTREAL_SUM_IMAGE g (count N) = 0’
 >- (irule EXTREAL_SUM_IMAGE_0 >> rw [])
 >> Rewr'
 >> rw []
 >> irule EXTREAL_SUM_IMAGE_EQ >> rw []
 >> DISJ1_TAC >> rw []
 >> MATCH_MP_TAC pos_not_neginf
 >> Suff ‘g (N + x) = f x’ >- (Rewr' >> rw [])
 >> METIS_TAC [ADD_SYM]
QED

Theorem EXTREAL_SUM_IMAGE_POS_MEM_LE:
     !f s. FINITE s  /\ (!x. x IN s ==> 0 <= f x) ==>
            (!x. x IN s ==> f x <= EXTREAL_SUM_IMAGE f s)
Proof
  Suff `!s. FINITE s ==>
        (\s. !f. (!x. x IN s ==> 0 <= f x) ==>
            (!x. x IN s ==> f x <= EXTREAL_SUM_IMAGE f s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [NOT_IN_EMPTY]
  >> `!x. x IN e INSERT s ==> f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >- METIS_TAC [EXTREAL_SUM_IMAGE_POS,le_add2,add_rzero,extreal_of_num_def,extreal_not_infty,le_refl]
  >> `f x <= EXTREAL_SUM_IMAGE f s` by FULL_SIMP_TAC std_ss [IN_INSERT]
  >> METIS_TAC [le_add2,add_lzero,extreal_of_num_def,extreal_not_infty]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_ADD:
    !s. FINITE s ==>
        !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) ==>
               (EXTREAL_SUM_IMAGE (\x. f x + f' x) s =
                EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f' s)
Proof
  Suff `!s. FINITE s ==>
        (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) ==>
                (EXTREAL_SUM_IMAGE (\x. f x + f' x) s =
                 EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f' s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,add_lzero]
  >- (`!x. x IN e INSERT s ==> (\x. f x + f' x) x <> NegInf` by METIS_TAC [add_not_infty]
      >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
      >> `EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
          f' e + (EXTREAL_SUM_IMAGE f' s + EXTREAL_SUM_IMAGE f s)`
           by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
      >> `f e + EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
          f e + (EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s))`
           by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
      >> POP_ORW >> POP_ORW
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty,IN_INSERT])
  >> `!x. x IN e INSERT s ==> (\x. f x + f' x) x <> PosInf` by METIS_TAC [add_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> `EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
      f' e + (EXTREAL_SUM_IMAGE f' s + EXTREAL_SUM_IMAGE f s)`
         by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
  >> `f e + EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
      f e + (EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s))`
         by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
  >> POP_ORW >> POP_ORW
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >> METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty,IN_INSERT]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_SUB:
    !s. FINITE s ==>
        !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> PosInf) \/
                (!x. x IN s ==> f x <> PosInf /\ f' x <> NegInf)) ==>
               (EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
                EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s)
Proof
  Suff `!s. FINITE s ==>
        (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> PosInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> NegInf)) ==>
                (EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
                 EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,sub_rzero]
  >- (`FINITE (e INSERT s)` by FULL_SIMP_TAC std_ss [FINITE_INSERT]
      >> (MP_TAC o Q.SPEC `(\x. f x - f' x)` o UNDISCH o Q.SPEC `e INSERT  s`) EXTREAL_SUM_IMAGE_IN_IF
      >> `!x. x IN e INSERT s ==> (\x. f x - f' x) x <> NegInf`
          by RW_TAC std_ss [sub_not_infty]
      >> `EXTREAL_SUM_IMAGE f (e INSERT s) <> NegInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
      >> `EXTREAL_SUM_IMAGE f' (e INSERT s) <> PosInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
      >> RW_TAC std_ss [extreal_sub_add]
      >> `-EXTREAL_SUM_IMAGE f' (e INSERT s) = Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s)`
            by METIS_TAC [neg_minus1,extreal_of_num_def,extreal_ainv_def]
      >> POP_ORW
      >> `Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s) =
          EXTREAL_SUM_IMAGE (\x. Normal (-1) * f' x) (e INSERT s)` by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL]
      >> RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def,GSYM neg_minus1]
      >> `(\x. if x IN e INSERT s then f x + -f' x else 0) =
          (\x. if x IN e INSERT s then (\x. f x + -f' x) x else 0)` by METIS_TAC []
      >> POP_ORW
      >> (MP_TAC o Q.SPEC `(\x. f x + -f' x)` o UNDISCH o Q.SPEC `e INSERT s ` o GSYM)
           EXTREAL_SUM_IMAGE_IN_IF
      >> RW_TAC std_ss []
      >> `!x. x IN e INSERT s ==> NegInf <> f x + -f' x` by METIS_TAC [extreal_sub_add]
      >> FULL_SIMP_TAC std_ss []
      >> `(\x. f x + -f' x) = (\x. f x + (\x. -f' x) x)` by METIS_TAC []
      >> POP_ORW
      >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `e INSERT s`) EXTREAL_SUM_IMAGE_ADD
      >> DISJ1_TAC
      >> RW_TAC std_ss []
      >> Cases_on `f' x`
      >> METIS_TAC [extreal_ainv_def,extreal_not_infty])
  >> `FINITE (e INSERT s)` by FULL_SIMP_TAC std_ss [FINITE_INSERT]
  >> (MP_TAC o Q.SPEC `(\x. f x - f' x)` o UNDISCH o Q.SPEC `e INSERT  s`) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x. x IN e INSERT s ==> (\x. f x - f' x) x <> PosInf`
        by RW_TAC std_ss [sub_not_infty]
  >> `EXTREAL_SUM_IMAGE f (e INSERT s) <> PosInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
  >> `EXTREAL_SUM_IMAGE f' (e INSERT s) <> NegInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
  >> RW_TAC std_ss [extreal_sub_add]
  >> `-EXTREAL_SUM_IMAGE f' (e INSERT s) = Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s)`
        by METIS_TAC [neg_minus1,extreal_of_num_def,extreal_ainv_def]
  >> POP_ORW
  >> `Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s) =
      EXTREAL_SUM_IMAGE (\x. Normal (-1) * f' x) (e INSERT s)` by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL]
  >> RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def,GSYM neg_minus1]
  >> `(\x. if x IN e INSERT s then f x + -f' x else 0) =
      (\x. if x IN e INSERT s then (\x. f x + -f' x) x else 0)` by METIS_TAC []
  >> POP_ORW
  >> (MP_TAC o Q.SPEC `(\x. f x + -f' x)` o UNDISCH o Q.SPEC `e INSERT s ` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
  >> RW_TAC std_ss []
  >> `!x. x IN e INSERT s ==> PosInf <> f x + -f' x` by METIS_TAC [extreal_sub_add]
  >> FULL_SIMP_TAC std_ss []
  >> `(\x. f x + -f' x) = (\x. f x + (\x. -f' x) x)` by METIS_TAC []
  >> POP_ORW
  >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `e INSERT s`) EXTREAL_SUM_IMAGE_ADD
  >> DISJ2_TAC
  >> RW_TAC std_ss []
  >> Cases_on `f' x`
  >> METIS_TAC [extreal_ainv_def,extreal_not_infty]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_SUM_IMAGE:
    !s s' f. FINITE s /\ FINITE s' /\
             ((!x. x IN s CROSS s' ==> f (FST x) (SND x) <> NegInf) \/
              (!x. x IN s CROSS s' ==> f (FST x) (SND x) <> PosInf)) ==>
             (EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
              EXTREAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))
Proof
    Suff `!s. FINITE s ==>
             (\s. !s' f. FINITE s' /\
                       ((!x. x IN s CROSS s' ==> f (FST x) (SND x) <> NegInf) \/
                        (!x. x IN s CROSS s' ==> f (FST x) (SND x) <> PosInf)) ==>
                 (EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
                  EXTREAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [CROSS_EMPTY, EXTREAL_SUM_IMAGE_EMPTY, DELETE_NON_ELEMENT] (* 2 subgoals *)
 >> `((e INSERT s) CROSS s') = (IMAGE (\x. (e,x)) s') UNION (s CROSS s')`
        by (RW_TAC std_ss [Once EXTENSION, IN_INSERT, IN_SING, IN_CROSS, IN_UNION, IN_IMAGE]
            >> Cases_on `x`
            >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [FST,SND, GSYM DELETE_NON_ELEMENT]
            >> METIS_TAC []) >> POP_ORW
 >> `DISJOINT (IMAGE (\x. (e,x)) s') (s CROSS s')`
        by (FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, Once EXTENSION,
                                  NOT_IN_EMPTY, IN_INTER, IN_CROSS, IN_SING, IN_IMAGE]
            >> STRIP_TAC >> Cases_on `x`
            >> RW_TAC std_ss [FST, SND]
            >> METIS_TAC [])
 >> `FINITE (IMAGE (\x. (e,x)) s')` by RW_TAC std_ss [IMAGE_FINITE]
 >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
 >> (MP_TAC o Q.SPEC `(\x. f (FST x) (SND x))` o UNDISCH o UNDISCH o UNDISCH o
       REWRITE_RULE [GSYM AND_IMP_INTRO] o
       Q.ISPECL [`IMAGE (\x. (e:'a,x)) (s':'b->bool)`,
                 `(s:'a->bool) CROSS (s':'b->bool)`]) EXTREAL_SUM_IMAGE_DISJOINT_UNION
 >| [ `(!x. x IN IMAGE (\x. (e,x)) s' UNION s CROSS s' ==> f (FST x) (SND x) <> NegInf)`
          by (FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNION, IN_INSERT, IN_CROSS]
              >> METIS_TAC [FST, SND]),
      `(!x. x IN IMAGE (\x. (e,x)) s' UNION s CROSS s' ==> f (FST x) (SND x) <> PosInf)`
          by (FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_INSERT, IN_CROSS]
              >> METIS_TAC [FST, SND]) ]
 >> RW_TAC std_ss []
 >> `INJ (\x. (e,x)) s' (IMAGE (\x. (e,x)) s')` by RW_TAC std_ss [INJ_DEF, IN_IMAGE]
 >> (MP_TAC o Q.SPEC `(\x. f (FST x) (SND x))` o UNDISCH o Q.SPEC `(\x. (e,x))` o
       UNDISCH o Q.SPEC `s'` o
       INST_TYPE [``:'c``|->``:'a # 'b``] o INST_TYPE [``:'a``|->``:'b``] o
       INST_TYPE [``:'b``|->``:'c``]) EXTREAL_SUM_IMAGE_IMAGE
 >| [ `!x. x IN IMAGE (\x. (e,x)) s' ==> (\x. f (FST x) (SND x)) x <> NegInf`
          by FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_INSERT, IN_CROSS],
      `!x. x IN IMAGE (\x. (e,x)) s' ==> (\x. f (FST x) (SND x)) x <> PosInf`
          by FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_INSERT, IN_CROSS] ]
 >> RW_TAC std_ss [o_DEF]
 >| [ `!x. x IN e INSERT s ==> (\x. EXTREAL_SUM_IMAGE (f x) s') x <> NegInf`
        by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT, IN_CROSS, FST, SND],
      `!x. x IN e INSERT s ==> (\x. EXTREAL_SUM_IMAGE (f x) s') x <> PosInf`
        by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT, IN_CROSS, FST, SND] ]
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o
       Q.SPECL [`(\x. EXTREAL_SUM_IMAGE (f x) s')`,`s`]) EXTREAL_SUM_IMAGE_PROPERTY
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [IN_INSERT, IN_IMAGE, IN_UNION]
 >> METIS_TAC [FUN_EQ_THM]
QED

Theorem EXTREAL_SUM_IMAGE_NORMAL:
    !f s. FINITE s ==> (EXTREAL_SUM_IMAGE (\x. Normal (f x)) s = Normal (SIGMA f s))
Proof
    Suff `!s. FINITE s ==>
             (\s. !f. EXTREAL_SUM_IMAGE (\x. Normal (f x)) s = Normal (SIGMA f s) ) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, REAL_SUM_IMAGE_THM, extreal_of_num_def,
                   REAL_SUM_IMAGE_THM, GSYM extreal_add_def]
 >> (MP_TAC o UNDISCH o Q.SPECL [`(\x. Normal (f x))`,`s`]) EXTREAL_SUM_IMAGE_PROPERTY
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT, extreal_not_infty]
QED

(* more antecedents added *)
Theorem EXTREAL_SUM_IMAGE_IN_IF_ALT:
    !s f z. FINITE s /\ ((!x. x IN s ==> f x <> NegInf) \/
                         (!x. x IN s ==> f x <> PosInf)) ==>
           (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s)
Proof
    Suff `!s. FINITE s ==>
             (\s. !f z. ((!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf)) ==>
                        (EXTREAL_SUM_IMAGE f s =
                         EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY]
 >- (`!i. i IN e INSERT s ==> (\x. if x IN e INSERT s then f x else z) i <> NegInf`
       by RW_TAC std_ss []
     >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]) (* 2 sub-goals here *)
     >> FULL_SIMP_TAC std_ss [IN_INSERT]                     (* 1 remains *)
     >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
     >> Suff `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN e INSERT s then f x else z) s`
     >- RW_TAC std_ss [IN_INSERT]
     >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s`
          by METIS_TAC [IN_INSERT]
     >> POP_ORW
     >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_EQ
     >> RW_TAC std_ss [IN_INSERT])
 >> `!i. i IN e INSERT s ==> (\x. if x IN e INSERT s then f x else z) i <> PosInf` by RW_TAC std_ss []
 >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY])
 >- FULL_SIMP_TAC std_ss [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 >> Suff `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN e INSERT s then f x else z) s`
 >- RW_TAC std_ss []
 >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s`
       by METIS_TAC [IN_INSERT]
 >> POP_ORW
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_EQ
 >> RW_TAC std_ss [IN_INSERT]
QED

Theorem EXTREAL_SUM_IMAGE_CROSS_SYM :
    !f s1 s2. FINITE s1 /\ FINITE s2 /\
             ((!s. s IN (s1 CROSS s2) ==> f s <> NegInf) \/
              (!s. s IN (s1 CROSS s2) ==> f s <> PosInf)) ==>
             (EXTREAL_SUM_IMAGE (\(x,y). f (x,y)) (s1 CROSS s2) =
              EXTREAL_SUM_IMAGE (\(y,x). f (x,y)) (s2 CROSS s1))
Proof
    rpt GEN_TAC
 >> DISCH_TAC
 >> `s2 CROSS s1 = IMAGE (\a. (SND a, FST a)) (s1 CROSS s2)`
       by (RW_TAC std_ss [IN_IMAGE, IN_CROSS, EXTENSION] \\
           METIS_TAC [FST,SND,PAIR])
 >> POP_ORW
 >> `INJ (\a. (SND a, FST a)) (s1 CROSS s2) (IMAGE (\a. (SND a, FST a)) (s1 CROSS s2))`
       by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_CROSS] \\
           METIS_TAC [FST,SND,PAIR])
 >> Q.ABBREV_TAC ‘f' = \a. (SND a, FST a)’
 >> Q.ABBREV_TAC ‘g = \(y,x). f (x,y)’
 >> Know ‘(\(x,y). f (x,y)) = g o f'’
 >- (rw [Abbr ‘g’, Abbr ‘f'’, o_DEF, FUN_EQ_THM] \\
     Cases_on ‘x’ >> rw [])
 >> Rewr'
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> irule EXTREAL_SUM_IMAGE_IMAGE
 >> CONJ_TAC >- (MATCH_MP_TAC FINITE_CROSS >> rw [])
 >> rw [Abbr ‘g’]
 >| [ DISJ1_TAC, DISJ2_TAC ]
 >> Q.X_GEN_TAC ‘x’ >> Cases_on ‘x’ >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rename1 ‘(q,r) = f' y’ >> Cases_on ‘y’
 >> fs [Abbr ‘f'’]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT :
    !f. (!x. f x <> PosInf) \/ (!x. f x <> NegInf) ==>
        (EXTREAL_SUM_IMAGE f (count 2) = f 0 + f 1) /\
        (EXTREAL_SUM_IMAGE f (count 3) = f 0 + f 1 + f 2) /\
        (EXTREAL_SUM_IMAGE f (count 4) = f 0 + f 1 + f 2 + f 3) /\
        (EXTREAL_SUM_IMAGE f (count 5) = f 0 + f 1 + f 2 + f 3 + f 4)
Proof
    Q.X_GEN_TAC ‘f’
 >> DISCH_TAC
 >> `count 2 = {0;1} /\
     count 3 = {0;1;2} /\
     count 4 = {0;1;2;3} /\
     count 5 = {0;1;2;3;4}`
       by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
 >> `{1:num} DELETE 0 = {1}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{2:num} DELETE 1 = {2}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{3:num} DELETE 2 = {3}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{4:num} DELETE 3 = {4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{2:num; 3} DELETE 1 = {2;3}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{3:num; 4} DELETE 2 = {3;4}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{2:num; 3; 4} DELETE 1 = {2;3;4}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2} DELETE 0 = {1;2}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2; 3} DELETE 0 = {1;2;3}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2; 3; 4} DELETE 0 = {1;2;3;4}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> FULL_SIMP_TAC real_ss [FINITE_SING, FINITE_INSERT, EXTREAL_SUM_IMAGE_INSERT,
                           EXTREAL_SUM_IMAGE_SING, IN_INSERT, NOT_IN_EMPTY,
                           add_assoc, add_not_infty]
QED

Overload SIGMA = ``EXTREAL_SUM_IMAGE``

(* N-ARY SUMMATION *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x2211, tmnm = "SIGMA"};

Theorem NESTED_EXTREAL_SUM_IMAGE_REVERSE:
    !f s s'. FINITE s /\ FINITE s' /\
            (!x y. x IN s /\ y IN s' ==> f x y <> NegInf) ==>
            (EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
             EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (\y. f y x) s) s')
Proof
    rpt STRIP_TAC
 >> Know `SIGMA (\x. SIGMA (f x) s') s =
          SIGMA (\x. f (FST x) (SND x)) (s CROSS s')`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     ASM_REWRITE_TAC [IN_CROSS]) >> Rewr'
 >> Know `SIGMA (\x. SIGMA ((\x y. f y x) x) s) s' =
          SIGMA (\x. (\x y. f y x) (FST x) (SND x)) (s' CROSS s)`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     BETA_TAC >> ASM_REWRITE_TAC [IN_CROSS] >> PROVE_TAC [])
 >> BETA_TAC >> Rewr'
 >> Know `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
 >- (RW_TAC std_ss [EXTENSION, IN_CROSS, IN_IMAGE] \\
     EQ_TAC >- (STRIP_TAC >> Q.EXISTS_TAC `(SND x, FST x)` >> RW_TAC std_ss [PAIR]) \\
     RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND]) >> Rewr'
 >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
 >> `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
       by (RW_TAC std_ss [INJ_DEF, IN_IMAGE] >- METIS_TAC [] \\
           METIS_TAC [PAIR, PAIR_EQ])
 >> Know `SIGMA (\x. f (SND x) (FST x)) (IMAGE (\x. (SND x,FST x)) (s CROSS s')) =
          SIGMA ((\x. f (SND x) (FST x)) o (\x. (SND x,FST x))) (s CROSS s')`
 >- (irule EXTREAL_SUM_IMAGE_IMAGE >> art [] \\
     DISJ1_TAC >> RW_TAC std_ss [IN_IMAGE, IN_CROSS] \\
     RW_TAC std_ss [FST, SND])
 >> Rewr' >> RW_TAC std_ss [o_DEF]
QED

Theorem EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO:
   !(f :num -> num -> extreal) a b c d.
        (!m n. 0 <= f m n) /\ a <= c /\ b <= d ==>
        SIGMA (\i. SIGMA (f i) (count a)) (count b) <=
        SIGMA (\i. SIGMA (f i) (count c)) (count d)
Proof
    rpt STRIP_TAC >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA (\i. SIGMA (f i) (count a)) (count d)`
 >> CONJ_TAC
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     SIMP_TAC arith_ss [FINITE_COUNT] \\
     CONJ_TAC >- (MATCH_MP_TAC COUNT_MONO >> RW_TAC arith_ss []) \\
     GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> PROVE_TAC [FINITE_COUNT])
 >> irule EXTREAL_SUM_IMAGE_MONO
 >> SIMP_TAC arith_ss [FINITE_COUNT]
 >> CONJ_TAC
 >- (GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     SIMP_TAC arith_ss [FINITE_COUNT] \\
     CONJ_TAC >- (MATCH_MP_TAC COUNT_MONO >> RW_TAC arith_ss []) \\
     PROVE_TAC [])
 >> DISJ1_TAC >> GEN_TAC >> DISCH_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [FINITE_COUNT])
 >> MATCH_MP_TAC pos_not_neginf
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> RW_TAC std_ss [FINITE_COUNT]
QED

Theorem EXTREAL_SUM_IMAGE_POW:
    !f s. FINITE s ==>
        ((!x. x IN s ==> f x <> NegInf) /\ (!x. x IN s ==> f x <> PosInf)) ==>
        ((EXTREAL_SUM_IMAGE f s) pow 2 =
          EXTREAL_SUM_IMAGE (\(i,j). f i * f j) (s CROSS s))
Proof
    rpt STRIP_TAC
 >> `(\(i,j). f i * f j) = (\x. (\i j. f i * f j) (FST x) (SND x))`
       by (RW_TAC std_ss [FUN_EQ_THM] \\
           Cases_on `x` >> RW_TAC std_ss []) >> POP_ORW
 >> (MP_TAC o Q.SPECL [`s`,`s`,`(\i j. f i * f j)`] o INST_TYPE [``:'b`` |-> ``:'a``])
       EXTREAL_SUM_IMAGE_SUM_IMAGE >> art []
 >> Know `((!x. x IN s CROSS s ==> (\i j. f i * f j) (FST x) (SND x) <> NegInf) \/
           (!x. x IN s CROSS s ==> (\i j. f i * f j) (FST x) (SND x) <> PosInf))`
 >- (RW_TAC std_ss [IN_CROSS] \\
     DISJ1_TAC >> RW_TAC std_ss [] \\
    `f (FST x) <> NegInf /\ f (SND x) <> NegInf` by PROVE_TAC [] \\
     METIS_TAC [mul_not_infty2])
 >> SIMP_TAC std_ss [] >> DISCH_TAC
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
 >> Know `!x. x IN s ==> SIGMA (\j. f x * f j) s = f x * SIGMA f s`
 >- (rpt STRIP_TAC >> `?c. f x = Normal c` by PROVE_TAC [extreal_cases] >> art [] \\
     ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL]) >> DISCH_TAC
 >> Know `SIGMA (\x. SIGMA (\j. f x * f j) s) s = SIGMA (\x. f x * (SIGMA f s)) s`
 >- (irule EXTREAL_SUM_IMAGE_EQ >> ASM_SIMP_TAC std_ss [] \\
     DISJ2_TAC >> GEN_TAC >> DISCH_TAC \\
    `f x <> PosInf /\ f x <> NegInf` by PROVE_TAC [] \\
     Suff `SIGMA f s <> PosInf /\ SIGMA f s <> NegInf` >- METIS_TAC [mul_not_infty2] \\
     ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]) >> Rewr'
 >> `SIGMA f s <> PosInf /\ SIGMA f s <> NegInf`
      by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY]
 >> `?c. SIGMA f s = Normal c` by PROVE_TAC [extreal_cases] >> art []
 >> ONCE_REWRITE_TAC [mul_comm]
 >> Know `SIGMA (\x. Normal c * f x) s = Normal c * SIGMA f s`
 >- ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL]
 >> Rewr' >> art [pow_2]
QED

(* ------------------------------------------------------------------------- *)
(* Supremums and infimums (these are always defined on extended reals)       *)
(* ------------------------------------------------------------------------- *)

Definition extreal_sup_def:
    extreal_sup p =
       if !x. (!y. p y ==> y <= x) ==> (x = PosInf) then PosInf
       else (if !x. p x ==> (x = NegInf) then NegInf
             else Normal (sup (\r. p (Normal r))))
End

Definition extreal_inf_def:
    extreal_inf p = -extreal_sup (IMAGE numeric_negate p)
End

Overload sup = Term `extreal_sup`
Overload inf = Term `extreal_inf`

Theorem le_sup_imp :
    !p x. p x ==> x <= sup p
Proof
    RW_TAC std_ss [extreal_sup_def, le_infty, le_refl]
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `x` (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      RW_TAC std_ss [le_infty],
      (* goal 2 (of 3) *)
      rename1 ‘y <> PosInf’ \\
     `y < PosInf` by (Cases_on `y` >> RW_TAC std_ss [lt_infty]) \\
      METIS_TAC [let_trans, lt_refl],
      (* goal 3 (of 3) *)
      RW_TAC std_ss [extreal_le_def] \\
      MATCH_MP_TAC REAL_IMP_LE_SUP \\
      reverse CONJ_TAC >- (Q.EXISTS_TAC `r` >> RW_TAC real_ss []) \\
      rename1 ‘y <> PosInf’ \\
      Cases_on `y` >| (* 3 subgoals *)
      [ METIS_TAC [le_infty],
        RW_TAC std_ss [],
        rename1 ‘Normal z <> PosInf’ \\
        Q.EXISTS_TAC `z` \\
        RW_TAC std_ss [] \\
        METIS_TAC [extreal_le_def] ] ]
QED

Theorem le_sup_imp':   !p x. x IN p ==> x <= sup p
Proof
    REWRITE_TAC [IN_APP]
 >> PROVE_TAC [le_sup_imp]
QED

Theorem sup_le :
    !p x. sup p <= x <=> (!y. p y ==> y <= x)
Proof
    RW_TAC std_ss [extreal_sup_def, le_infty]
 >- (EQ_TAC >- RW_TAC std_ss [le_infty] >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `x`
 >- METIS_TAC [le_infty, extreal_not_infty]
 >- METIS_TAC [le_infty]
 >> rename1 ‘y <> PosInf’
 >> Cases_on `y`
 >- METIS_TAC [le_infty]
 >- RW_TAC std_ss []
 >> RW_TAC std_ss [extreal_le_def]
 >> EQ_TAC
 >- (RW_TAC std_ss [] \\
     Cases_on `y` >| (* 3 subgoals *)
     [ (* goal 1 (of 2) *)
       METIS_TAC [le_infty],
       (* goal 2 (of 3) *)
       METIS_TAC [le_infty, extreal_not_infty],
       (* goal 3 (of 3) *)
       RW_TAC std_ss [extreal_le_def] \\
       MATCH_MP_TAC REAL_LE_TRANS \\
       Q.EXISTS_TAC `sup (\r. p (Normal r))` \\
       RW_TAC std_ss [] \\
       MATCH_MP_TAC REAL_IMP_LE_SUP \\
       rename1 ‘p (Normal z)’ \\
       reverse CONJ_TAC >- (Q.EXISTS_TAC `z` >> RW_TAC real_ss []) \\
       rename1 ‘!y. p y ==> y <= Normal u’ \\
       Q.EXISTS_TAC `u` \\
       RW_TAC std_ss [] \\
       METIS_TAC [extreal_le_def] ])
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_IMP_SUP_LE
 >> reverse (RW_TAC std_ss [])
 >- METIS_TAC [extreal_le_def]
 >> rename1 ‘z <> NegInf’
 >> Cases_on `z`
 >- RW_TAC std_ss []
 >- METIS_TAC [le_infty, extreal_not_infty]
 >> METIS_TAC []
QED

Theorem sup_le' : (* was: Sup_le_iff *)
    !p x. sup p <= x <=> (!y. y IN p ==> y <= x)
Proof
    METIS_TAC [sup_le, SPECIFICATION]
QED

Theorem le_sup:   !p x. x <= sup p <=> (!y. (!z. p z ==> z <= y) ==> x <= y)
Proof
    RW_TAC std_ss [extreal_sup_def,le_infty]
 >- (EQ_TAC >- RW_TAC std_ss [le_infty] >> METIS_TAC [le_infty, le_refl])
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `x'` (* 3 subgoals *)
 >| [ METIS_TAC [le_infty],
      METIS_TAC [le_infty],
      Cases_on `x` >| (* 3 subgoals *)
      [ METIS_TAC [le_infty],
        METIS_TAC [le_infty, extreal_not_infty],
        RW_TAC std_ss [extreal_le_def] \\
        EQ_TAC
        >- (RW_TAC std_ss [] \\
            Cases_on `y` >|
            [ METIS_TAC [le_infty],
              METIS_TAC [le_infty],
              RW_TAC std_ss [extreal_le_def] \\
              MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC `sup (\r. p (Normal r))` \\
              RW_TAC std_ss [] \\
              MATCH_MP_TAC REAL_IMP_SUP_LE \\
              RW_TAC std_ss []
              >- (Cases_on `x''` >| (* 3 gubgoals *)
                  [ RW_TAC std_ss [],
                    METIS_TAC [le_infty, extreal_not_infty],
                    METIS_TAC [] ]) \\
              METIS_TAC [extreal_le_def] ]) \\
        RW_TAC std_ss [extreal_le_def] \\
       (MP_TAC o Q.SPECL [`(\r. p (Normal r))`,`r'`]) REAL_LE_SUP \\
        MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) \\
        CONJ_TAC
        >- (RW_TAC std_ss []
            >- METIS_TAC [extreal_cases, le_infty, extreal_not_infty] \\
            METIS_TAC [extreal_le_def]) \\
            RW_TAC std_ss [] \\
            Q.PAT_X_ASSUM `!y. (!z. p z ==> z <= y) ==> Normal r' <= y`
                (MATCH_MP_TAC o REWRITE_RULE [extreal_le_def] o Q.SPEC `Normal y`) \\
            Cases >| (* 3 subgoals *)
            [ METIS_TAC [le_infty],
              METIS_TAC [le_infty, extreal_not_infty],
              METIS_TAC [extreal_le_def] ] ] ]
QED

Theorem le_sup':   !p x. x <= sup p <=> !y. (!z. z IN p ==> z <= y) ==> x <= y
Proof
    REWRITE_TAC [IN_APP]
 >> REWRITE_TAC [le_sup]
QED

Theorem le_sup_imp2:   !p z. (?x. x IN p) /\ (!x. x IN p ==> z <= x) ==> z <= sup p
Proof
    RW_TAC std_ss [le_sup']
 >> MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `x`
 >> CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem sup_eq:   !p x. (sup p = x) <=>
                     (!y. p y ==> y <= x) /\ !y. (!z. p z ==> z <= y) ==> x <= y
Proof
    METIS_TAC [le_antisym, le_sup, sup_le]
QED

Theorem sup_eq':
    !p x. (sup p = x) <=>
          (!y. y IN p ==> y <= x) /\ !y. (!z. z IN p ==> z <= y) ==> x <= y
Proof
    REWRITE_TAC [IN_APP]
 >> METIS_TAC [le_antisym, le_sup, sup_le]
QED

Theorem sup_const:   !x. sup (\y. y = x) = x
Proof
    RW_TAC real_ss [sup_eq, le_refl]
QED

Theorem sup_sing :
    !a:extreal. sup {a} = a
Proof
    REWRITE_TAC [METIS [EXTENSION, IN_SING, IN_DEF] ``{a} = (\x. x = a)``]
 >> SIMP_TAC std_ss [sup_const]
QED

Theorem sup_const_alt:   !p z. (?x. p x) /\ (!x. p x ==> (x = z)) ==> (sup p = z)
Proof
    RW_TAC std_ss [sup_eq,le_refl]
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss []
QED

Theorem sup_const_alt' :
    !p z. (?x. x IN p) /\ (!x. x IN p ==> (x = z)) ==> (sup p = z)
Proof
    rw [IN_APP, sup_const_alt]
QED

Theorem sup_const_over_set:   !s k. s <> {} ==> (sup (IMAGE (\x. k) s) = k)
Proof
    RW_TAC std_ss [sup_eq]
 >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [IN_IMAGE] >> RW_TAC std_ss [le_refl])
 >> POP_ASSUM MATCH_MP_TAC
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> RW_TAC std_ss [IN_IMAGE]
 >> METIS_TAC [CHOICE_DEF]
QED

Theorem sup_const_over_univ:   !k. sup (IMAGE (\x. k) UNIV) = k
Proof
    GEN_TAC >> MATCH_MP_TAC sup_const_over_set
 >> SET_TAC []
QED

Theorem sup_num:   sup (\x. ?n :num. x = &n) = PosInf
Proof
    RW_TAC std_ss [GSYM le_infty,le_sup]
 >> Cases_on `y`
 >| [ POP_ASSUM (MP_TAC o Q.SPEC `0`) \\
      RW_TAC real_ss [le_infty, extreal_of_num_def, extreal_not_infty],
      RW_TAC std_ss [le_refl],
      RW_TAC std_ss [le_infty, extreal_not_infty] \\
      MP_TAC (Q.SPEC `r` REAL_BIGNUM) \\
      PURE_REWRITE_TAC [real_lt] \\
      STRIP_TAC \\
      Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `&n`) \\
      RW_TAC std_ss [extreal_of_num_def] >- METIS_TAC [] \\
      METIS_TAC [extreal_le_def] ]
QED

Theorem sup_le_sup_imp:
    !p q. (!x. p x ==> ?y. q y /\ x <= y) ==> sup p <= sup q
Proof
    RW_TAC std_ss [sup_le]
 >> METIS_TAC [le_trans, le_sup_imp]
QED

Theorem sup_le_sup_imp':
    !p q. (!x. x IN p ==> ?y. y IN q /\ x <= y) ==> sup p <= sup q
Proof
    REWRITE_TAC [IN_APP]
 >> PROVE_TAC [sup_le_sup_imp]
QED

(* NOTE: The type variable :num has been generalized to alpha *)
Theorem sup_mono :
    !p q. (!n. p n <= q n) ==> sup (IMAGE p UNIV) <= sup (IMAGE q UNIV)
Proof
    rw [sup_le', le_sup']
 >> rename1 ‘p n <= z’
 >> Q_TAC (TRANS_TAC le_trans) ‘q n’ >> art []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘n’ >> rw []
QED

(* This is more general than "sup_mono", as f <= g in arbitrary order *)
Theorem sup_mono_ext : (* was: SUP_mono *)
    !f g A B. (!n. n IN A ==> ?m. m IN B /\ f n <= g m) ==>
              sup {f n | n IN A} <= sup {g n | n IN B}
Proof
  RW_TAC std_ss [] THEN MATCH_MP_TAC sup_le_sup_imp THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `g m` THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN ASM_SET_TAC []
QED

Theorem sup_mono_subset:   !p q. p SUBSET q ==> extreal_sup p <= extreal_sup q
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC sup_le_sup_imp
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `x`
 >> REWRITE_TAC [le_refl]
 >> PROVE_TAC [SUBSET_DEF, IN_APP]
QED

Theorem inf_mono_subset:   !p q. p SUBSET q ==> extreal_inf q <= extreal_inf p
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [extreal_inf_def, le_neg]
 >> MATCH_MP_TAC sup_mono_subset
 >> PROVE_TAC [IMAGE_SUBSET]
QED

Theorem sup_suc:   !f. (!m n. m <= n ==> f m <= f n) ==>
                    (sup (IMAGE (\n. f (SUC n)) UNIV) = sup (IMAGE f UNIV))
Proof
    RW_TAC std_ss [sup_eq, sup_le, le_sup]
 >- (POP_ASSUM MATCH_MP_TAC \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     METIS_TAC [])
 >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
 >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
 >> Cases_on `x`
 >- (MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `f 1` \\
     RW_TAC std_ss [] \\
     POP_ASSUM MATCH_MP_TAC \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
    `SUC 0 = 1` by RW_TAC real_ss [] \\
     METIS_TAC [])
 >> POP_ASSUM MATCH_MP_TAC
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> METIS_TAC []
QED

Theorem sup_shift:
    !f :num -> extreal.
      (!m n. m <= n ==> f m <= f n) ==>
       !N. (sup (IMAGE (\n. f (n + N)) UNIV) = sup (IMAGE f UNIV))
Proof
    GEN_TAC >> DISCH_TAC
 >> Induct_on `N` >- RW_TAC arith_ss [ETA_THM]
 >> Know `(\n. f (n + SUC N)) = (\n. (\n. f (n + N)) (SUC n))`
 >- (FUN_EQ_TAC >> RW_TAC arith_ss [ADD_CLAUSES]) >> Rewr'
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC sup_suc
 >> RW_TAC std_ss []
QED

Theorem sup_seq :
    !f l. mono_increasing f ==>
         ((f --> l) <=> (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))
Proof
     RW_TAC std_ss []
  >> EQ_TAC
  >- (RW_TAC std_ss [sup_eq]
      >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> RW_TAC std_ss [extreal_le_def]
          >> METIS_TAC [mono_increasing_suc, SEQ_MONO_LE, ADD1])
      >> `!n. Normal (f n) <= y`
            by (RW_TAC std_ss []
                >> POP_ASSUM MATCH_MP_TAC
                >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
                >> METIS_TAC [])
      >> Cases_on `y`
      >| [METIS_TAC [le_infty, extreal_not_infty],
          METIS_TAC [le_infty],
          METIS_TAC [SEQ_LE_IMP_LIM_LE,extreal_le_def]])
  >> RW_TAC std_ss [extreal_sup_def]
  >> `(\r. IMAGE (\n. Normal (f n)) UNIV (Normal r)) = IMAGE f UNIV`
       by (RW_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_UNIV]
           >> EQ_TAC
           >> (RW_TAC std_ss []
               >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
               >> RW_TAC std_ss [IN_IMAGE, IN_UNIV])
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV, IN_IMAGE]
           >> METIS_TAC [])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss []
  >> `!n. Normal (f n) <= x`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!y. P` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
           >> METIS_TAC [])
  >> `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans]
  >> `?z. x = Normal z` by METIS_TAC [extreal_cases]
  >> `!n. f n <= z` by FULL_SIMP_TAC std_ss [extreal_le_def]
  >> RW_TAC std_ss [SEQ]
  >> (MP_TAC o Q.ISPECL [`IMAGE (f:num->real) UNIV`,`e:real/2`]) SUP_EPSILON
  >> SIMP_TAC std_ss [REAL_LT_HALF1]
  >> `!y x z. IMAGE f UNIV x <=> x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
  >> POP_ORW
  >> Know `(?z. !x. x IN IMAGE f UNIV ==> x <= z)`
  >- (Q.EXISTS_TAC `z`
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [])
  >> `?x. x IN IMAGE f UNIV` by RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> RW_TAC std_ss []
  >> `?x. x IN IMAGE f univ(:num) /\
          sup (IMAGE f univ(:num)) <= x + e / 2` by METIS_TAC []
  >> RW_TAC std_ss [GSYM ABS_BETWEEN, GREATER_EQ]
  >> FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> rename1 ‘x2 = f x6’
  >> Q.EXISTS_TAC ‘x6’
  >> RW_TAC std_ss [REAL_LT_SUB_RADD]
  >- (MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC ‘f x6 + e / 2’
      >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LET_TRANS
      >> Q.EXISTS_TAC `f n + e / 2`
      >> reverse CONJ_TAC >- METIS_TAC [REAL_LET_ADD2,REAL_LT_HALF2,REAL_LE_REFL]
      >> RW_TAC std_ss [REAL_LE_RADD]
      >> METIS_TAC [mono_increasing_def])
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `sup (IMAGE f UNIV)`
   >> RW_TAC std_ss [REAL_LT_ADDR]
   >> Suff `!y. (\y. y IN IMAGE f UNIV) y ==> y <= sup (IMAGE f UNIV)`
   >- METIS_TAC [IN_IMAGE, IN_UNIV]
   >> SIMP_TAC std_ss [IN_DEF]
   >> MATCH_MP_TAC REAL_SUP_UBOUND_LE
   >> `!y x z. IMAGE f UNIV x <=> x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
   >> POP_ORW
   >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   >> Q.EXISTS_TAC `z'`
   >> RW_TAC std_ss []
QED

Theorem sup_lt_infty:   !p. (sup p < PosInf) ==> (!x. p x ==> x < PosInf)
Proof
    METIS_TAC [le_sup_imp,let_trans]
QED

Theorem sup_max:   !p z. p z /\ (!x. p x ==> x <= z) ==> (sup p = z)
Proof
    RW_TAC std_ss [sup_eq]
QED

Theorem sup_add_mono :
    !f g. (!n. 0 <= f n) /\ (!n. f n <= f (SUC n)) /\
          (!n. 0 <= g n) /\ (!n. g n <= g (SUC n)) ==>
          sup (IMAGE (\n. f n + g n) UNIV) =
          sup (IMAGE f UNIV) + sup (IMAGE g UNIV)
Proof
    rw [sup_eq']
 >- (MATCH_MP_TAC le_add2 >> rw [le_sup'] \\
     POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘n’ >> rw [])
 >> Cases_on ‘y = PosInf’ >- rw [le_infty]
 >> Cases_on ‘sup (IMAGE f UNIV) = 0’
 >- (rw [sup_le'] >> fs [sup_eq'] \\
    ‘!n. f n = 0’
       by METIS_TAC [EXTENSION, IN_IMAGE, IN_UNIV, SPECIFICATION, le_antisym] \\
     Q.PAT_X_ASSUM ‘!z. Q z ==> z <= y’ MATCH_MP_TAC \\
     RW_TAC std_ss [add_lzero] \\
     METIS_TAC [])
 >> Cases_on ‘sup (IMAGE g UNIV) = 0’
 >- (rw [sup_le'] >> fs [sup_eq'] \\
    ‘!n. g n = 0’
       by METIS_TAC [EXTENSION, IN_IMAGE, IN_UNIV, SPECIFICATION, le_antisym] \\
     Q.PAT_X_ASSUM ‘!z. Q z ==> z <= y’ MATCH_MP_TAC \\
     RW_TAC std_ss [add_rzero] \\
     METIS_TAC [])
 >> Know ‘!n. f n + g n <= y’
 >- (Q.X_GEN_TAC ‘n’ \\
     Q.PAT_X_ASSUM ‘!z. Q z ==> z <= y’ MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISCH_TAC
 >> ‘!n. f n <= f n + g n’ by METIS_TAC [add_rzero, le_add2, le_refl]
 >> ‘!n. g n <= f n + g n’ by METIS_TAC [add_lzero, le_add2, le_refl]
 >> ‘!n. f n <> PosInf’ by METIS_TAC [le_trans, lt_infty, let_trans]
 >> ‘!n. g n <> PosInf’ by METIS_TAC [le_trans, lt_infty, let_trans]
 >> ‘!n. f n <> NegInf’ by rw [pos_not_neginf]
 >> ‘!n. g n <> NegInf’ by rw [pos_not_neginf]
 >> MATCH_MP_TAC le_trans
 (* stage work *)
 >> Q.EXISTS_TAC ‘sup (IMAGE (\n. (sup (IMAGE f UNIV)) + g n) UNIV)’
 >> reverse (rw [sup_le'])
 >- (Suff ‘sup (IMAGE f UNIV) <= y - g n’ >- RW_TAC std_ss [le_sub_eq] \\
     rw [sup_le'] \\
     MATCH_MP_TAC le_sub_imp >> rw [] \\
     Cases_on ‘x <= n’
     >- (MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘f n + g n’ \\
         CONJ_TAC
         >- METIS_TAC [le_radd, ext_mono_increasing_def, ext_mono_increasing_suc] \\
         Q.PAT_X_ASSUM ‘!z. Q z ==> z <= y’ MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘f x + g x’ \\
     CONJ_TAC
     >- METIS_TAC [le_ladd, ext_mono_increasing_def, ext_mono_increasing_suc,
                   le_refl, NOT_LEQ, le_trans] \\
     Q.PAT_X_ASSUM ‘!z. Q z ==> z <= y’ MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> rw [])
 >> Know ‘sup (IMAGE f UNIV) <> NegInf’
 >- (rw [sup_eq', le_infty] \\
     Q.EXISTS_TAC ‘f 0’ >> rw [] \\
     Q.EXISTS_TAC ‘0’ >> rw [])
 >> DISCH_TAC
 >> Know ‘sup (IMAGE g UNIV) <> NegInf’
 >- (rw [sup_eq', le_infty] \\
     Q.EXISTS_TAC ‘g 0’ >> rw [] \\
     Q.EXISTS_TAC ‘0’ >> rw [])
 >> DISCH_TAC
 >> Cases_on ‘sup (IMAGE f UNIV) = PosInf’
 >- (Know ‘sup (IMAGE (\n. sup (IMAGE f UNIV) + g n) UNIV) = PosInf’
     >- (POP_ORW \\
         qmatch_abbrev_tac ‘sup s = PosInf’ \\
         Suff ‘s = \y. y = PosInf’ >- rw [sup_const] \\
         rw [Abbr ‘s’, Once EXTENSION] \\
         EQ_TAC >> rw []
         >- (‘?r. g n = Normal r’ by METIS_TAC [extreal_cases] \\
             rw [extreal_add_def]) \\
         Q.EXISTS_TAC ‘0’ \\
        ‘?r. g 0 = Normal r’ by METIS_TAC [extreal_cases] \\
         rw [extreal_add_def]) >> Rewr' \\
     METIS_TAC [le_infty])
 >> RW_TAC std_ss [add_comm]
 >> Suff ‘sup (IMAGE g UNIV) <=
          sup (IMAGE (\n. g n + sup (IMAGE f UNIV)) UNIV) - sup (IMAGE f UNIV)’
 >- METIS_TAC [le_sub_eq, add_comm]
 >> rw [sup_le']
 >> MATCH_MP_TAC le_sub_imp
 >> rw [le_sup']
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘x’ >> rw []
QED

Theorem sup_sum_mono:
    !f s. FINITE s /\ (!i:num. i IN s ==> (!n. 0 <= f i n)) /\
          (!i:num. i IN s ==> (!n. f i n <= f i (SUC n))) ==>
          (sup (IMAGE (\n. SIGMA (\i:num. f i n) s) UNIV) =
           SIGMA (\i:num. sup (IMAGE (f i) UNIV)) s)
Proof
  Suff `!s. FINITE s ==> (\s. !f. (!i:num. i IN s ==> (!n. 0 <= f i n)) /\
                         (!i:num. i IN s ==> (!n. f i n <= f i (SUC n))) ==>
                      (sup (IMAGE (\n. SIGMA (\i:num. f i n) s) UNIV) =
                       SIGMA (\i:num. sup (IMAGE (f i) UNIV)) s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,UNIV_NOT_EMPTY,sup_const_over_set]
  >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  >> `!n. SIGMA (\i. f i n) (e INSERT s) =
          (\i. f i n) e + SIGMA (\i. f i n) (s DELETE e)`
        by (STRIP_TAC
            >> (MATCH_MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i n)`,`s`] o
                INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
            >> METIS_TAC [IN_INSERT, le_infty, lt_infty, extreal_of_num_def,
                          extreal_not_infty])
  >> RW_TAC std_ss []
  >> `!n. !x. x IN e INSERT s ==> f x n <> NegInf`
        by METIS_TAC [IN_INSERT, le_infty, lt_infty, extreal_of_num_def,
                      extreal_not_infty]
  >> `sup (IMAGE (\n. f e n + (\n. SIGMA (\i. f i n) s) n) UNIV) =
      sup (IMAGE (f e) UNIV) + sup (IMAGE (\n. SIGMA (\i. f i n) s) UNIV)`
        by ((MATCH_MP_TAC o Q.SPECL [`f e`, `(\n. SIGMA (\i. f i n) s)`] o
             INST_TYPE [alpha |-> ``:num``]) sup_add_mono
            >> FULL_SIMP_TAC std_ss [IN_INSERT,EXTREAL_SUM_IMAGE_POS]
            >> RW_TAC std_ss []
            >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``])
                  EXTREAL_SUM_IMAGE_MONO
            >> FULL_SIMP_TAC std_ss [IN_INSERT])
  >> FULL_SIMP_TAC std_ss []
  >> `!i. i IN e INSERT s ==> 0 <= (\i. sup (IMAGE (f i) univ(:num))) i`
      by (RW_TAC std_ss [le_sup]
          >> MATCH_MP_TAC le_trans
          >> Q.EXISTS_TAC `f i 0`
          >> FULL_SIMP_TAC std_ss []
          >> POP_ASSUM MATCH_MP_TAC
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `!i. i IN e INSERT s ==> (\i. sup (IMAGE (f i) univ(:num))) i <> NegInf`
      by METIS_TAC [IN_INSERT,le_infty,lt_infty,extreal_of_num_def,extreal_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
QED

Theorem sup_le_mono:
    !f z. (!n. f n <= f (SUC n)) /\ z < sup (IMAGE f UNIV) ==> ?n. z <= f n
Proof
  RW_TAC std_ss []
  >> SPOSE_NOT_THEN ASSUME_TAC
  >> FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
  >> `!x. x IN (IMAGE f UNIV) ==> x <= z`
       by METIS_TAC [IN_IMAGE,IN_UNIV,lt_imp_le]
  >> METIS_TAC [sup_le,SPECIFICATION,extreal_lt_def]
QED

Theorem sup_cmul_general :
    !f c J. 0 <= c /\ (J :'index set) <> {} ==>
            sup (IMAGE (\n. Normal c * f n) J) = Normal c * sup (IMAGE f J)
Proof
    RW_TAC std_ss []
 >> Cases_on ‘c = 0’ >- simp [sup_const_over_set, normal_0]
 >> ‘0 < c’ by PROVE_TAC [REAL_LT_LE]
 >> rw [sup_eq']
 >- (Cases_on ‘sup (IMAGE f J) = PosInf’
     >- simp [extreal_mul_def, le_infty] \\
     Cases_on ‘f n = NegInf’
     >- simp [extreal_mul_def, le_infty] \\
     MATCH_MP_TAC le_lmul_imp >> simp [extreal_of_num_def, extreal_le_eq] \\
     MATCH_MP_TAC le_sup_imp' >> simp [])
 >> Know ‘!n. n IN J ==> Normal c * f n <= y’
 >- (rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> simp [])
 >> DISCH_TAC
 >> Know ‘!n. n IN J ==> f n <= y / Normal c’
 >- (rpt STRIP_TAC \\
     Know ‘f n <= y / Normal c <=> f n * Normal c <= y’
     >- (SYM_TAC \\
         MATCH_MP_TAC le_rdiv >> art []) >> Rewr' \\
     ONCE_REWRITE_TAC [mul_comm] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> ONCE_REWRITE_TAC [mul_comm]
 >> Know ‘sup (IMAGE f J) * Normal c <= y <=>
          sup (IMAGE f J) <= y / Normal c’
 >- (MATCH_MP_TAC le_rdiv >> art [])
 >> Rewr'
 >> rw [sup_le']
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* |- !f c.
        0 <= c ==>
        sup (IMAGE (\n. Normal c * f n) univ(:'a)) =
        Normal c * sup (IMAGE f univ(:'a))
 *)
Theorem sup_cmul =
        sup_cmul_general |> INST_TYPE [“:'index” |-> alpha]
                         |> Q.SPECL [‘f’, ‘c’, ‘UNIV’] |> SRULE [] |> GEN_ALL

(* Another version of `sup_cmul`: f is positive, c can be PosInf *)
Theorem sup_cmult :
    !f c. 0 <= c /\ (!n. 0 <= f n) ==>
         (sup (IMAGE (\n. c * f n) UNIV) = c * sup (IMAGE f UNIV))
Proof
    rpt STRIP_TAC
 >> Cases_on `c <> PosInf`
 >- (IMP_RES_TAC pos_not_neginf \\
    `?r. c = Normal r` by PROVE_TAC [extreal_cases] >> art [] \\
     MATCH_MP_TAC sup_cmul \\
     REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
     PROVE_TAC [])
 >> fs []
 >> Know `0 <= sup (IMAGE f univ(:'a))`
 >- (RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `f ARB` >> RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [le_lt, Once DISJ_SYM]))
 >- (FIRST_ASSUM (REWRITE_TAC o wrap o SYM) >> REWRITE_TAC [mul_rzero] \\
     Know `!n. f n = 0`
     >- (POP_ASSUM (MP_TAC o SYM) \\
         RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV] \\
         RW_TAC std_ss [GSYM le_antisym] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> Rewr' \\
     REWRITE_TAC [mul_rzero] \\
     MATCH_MP_TAC sup_const_over_set >> SET_TAC [])
 >> RW_TAC std_ss [mul_lposinf]
 >> Know `?n. 0 < f n`
 >- (CCONTR_TAC >> fs [] \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [extreal_lt_def])) \\
    `!n. f n = 0` by PROVE_TAC [le_antisym] \\
    `f = \n. 0` by PROVE_TAC [] \\
     ASSUME_TAC (Q.SPEC `0` sup_const_over_univ) \\
    `(\x. 0) = f` by METIS_TAC [] >> fs [lt_refl]) >> STRIP_TAC
 >> RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV, le_infty]
 >> RW_TAC std_ss [GSYM le_antisym, Once le_infty]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n`
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC mul_lposinf >> art []
QED

Theorem sup_lt:   !P y. (?x. P x /\ y < x) <=> y < sup P
Proof
  RW_TAC std_ss []
  >> EQ_TAC >- METIS_TAC [le_sup_imp,lte_trans]
  >> RW_TAC std_ss []
  >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
  >> METIS_TAC [sup_le,extreal_lt_def]
QED

Theorem lt_sup : (* was: less_Sup_iff *)
    !a s. a < sup s <=> ?x. x IN s /\ a < x
Proof
    METIS_TAC [sup_lt, SPECIFICATION]
QED

Theorem sup_lt':   !P y. (?x. x IN P /\ y < x) <=> y < sup P
Proof
    RW_TAC std_ss [IN_APP]
 >> REWRITE_TAC [sup_lt]
QED

(* cf. realTheory.SUP_LT_EPSILON *)
Theorem sup_lt_epsilon :
    !P e. 0 < e /\ (?x. P x /\ x <> NegInf) /\ sup P <> PosInf ==>
          ?x. P x /\ sup P < x + e
Proof
    RW_TAC std_ss []
 >> Cases_on ‘e = PosInf’
 >- (Q.EXISTS_TAC ‘x’ >> RW_TAC std_ss [] \\
     METIS_TAC [extreal_add_def, lt_infty, extreal_cases])
 >> ‘e <> NegInf’ by METIS_TAC [le_sup_imp, lt_infty, lte_trans,
                                extreal_of_num_def, extreal_not_infty]
 >> ‘sup P <> NegInf’ by METIS_TAC [le_sup_imp, lt_infty, lte_trans]
 >> ‘sup P < sup P + e’
      by (Cases_on ‘sup P’ >> Cases_on ‘e’ \\
          RW_TAC std_ss [extreal_cases, extreal_add_def, extreal_lt_def,
                         extreal_le_def, GSYM real_lt] \\
          METIS_TAC [REAL_LT_ADDR, extreal_lt_def, extreal_le_def,
                     extreal_of_num_def, real_lt])
 >> ‘sup P - e < sup P’ by METIS_TAC [sub_lt_imp]
 >> ‘?x. P x /\ sup P - e < x’ by METIS_TAC [sup_lt]
 >> rename1 ‘P y’
 >> Q.EXISTS_TAC ‘y’
 >> RW_TAC std_ss []
 >> ‘y <> PosInf’ by METIS_TAC [le_sup_imp, let_trans, lt_infty]
 >> ‘?r. sup P = Normal r’ by METIS_TAC [extreal_cases]
 >> ‘?E. e = Normal E’ by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_sub_def]
 >> ‘y <> NegInf’ by METIS_TAC [lt_infty, extreal_not_infty, lt_trans]
 >> ‘?z. y = Normal z’ by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                          GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sup_lt_epsilon' :
    !P e. 0 < e /\ (?x. x IN P /\ x <> NegInf) /\ (sup P <> PosInf) ==>
          ?x. x IN P /\ sup P < x + e
Proof
    REWRITE_TAC [IN_APP, sup_lt_epsilon]
QED

Theorem inf_le_imp:   !p x. p x ==> inf p <= x
Proof
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,le_sup]
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE]
  >> METIS_TAC [SPECIFICATION]
QED

Theorem inf_le_imp':   !p x. x IN p ==> inf p <= x
Proof
    REWRITE_TAC [IN_APP]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC inf_le_imp >> art []
QED

Theorem le_inf:
     !p x. x <= inf p <=> (!y. p y ==> x <= y)
Proof
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,sup_le]
  >> EQ_TAC
  >- (RW_TAC std_ss []
      >> `-y IN (IMAGE numeric_negate p)`
           by (RW_TAC std_ss [IN_IMAGE]
               >> METIS_TAC [SPECIFICATION])
      >> METIS_TAC [le_neg,SPECIFICATION])
  >> RW_TAC std_ss []
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE]
  >> METIS_TAC [le_neg,SPECIFICATION]
QED

Theorem le_inf' :
    !p x. x <= inf p <=> (!y. y IN p ==> x <= y)
Proof
    REWRITE_TAC [IN_APP, le_inf]
QED

Theorem inf_le:
     !p x. (inf p <= x) <=> (!y. (!z. p z ==> y <= z) ==> y <= x)
Proof
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,le_sup]
  >> EQ_TAC
  >- (RW_TAC std_ss []
      >> `!z. IMAGE numeric_negate p z ==> y <= -z`
            by (RW_TAC std_ss []
                >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
                >> RW_TAC std_ss [IN_IMAGE]
                >> METIS_TAC [neg_neg,SPECIFICATION])
      >> `!z. IMAGE numeric_negate p z ==> z <= -y`
           by METIS_TAC [le_neg,neg_neg]
      >> `(!z. IMAGE numeric_negate p z ==> z <= -y) ==> -x <= -y`
           by METIS_TAC []
      >> METIS_TAC [le_neg])
  >> RW_TAC std_ss []
  >> `!z. p z ==> -z <= y`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!z. IMAGE numeric_negate p z ==> z <= y` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE]
           >> METIS_TAC [SPECIFICATION])
  >> `!z. p z ==> -y <= z` by METIS_TAC [le_neg,neg_neg]
  >> METIS_TAC [le_neg,neg_neg]
QED

Theorem inf_le' :
    !p x. (extreal_inf p <= x) <=>
          (!y. (!z. z IN p ==> y <= z) ==> y <= x)
Proof
    REWRITE_TAC [IN_APP, inf_le]
QED

Theorem inf_mono :
    !p q. (!n:num. p n <= q n) ==> inf (IMAGE p UNIV) <= inf (IMAGE q UNIV)
Proof
    rw [inf_le', le_inf']
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `p x` >> art []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘x’ >> rw []
QED

Theorem inf_eq:   !p x. (extreal_inf p = x) <=>
                       (!y. p y ==> x <= y) /\
                       (!y. (!z. p z ==> y <= z) ==> y <= x)
Proof
  METIS_TAC [le_antisym,inf_le,le_inf]
QED

Theorem inf_eq' :
    !p x. (extreal_inf p = x) <=>
          (!y. y IN p ==> x <= y) /\
          (!y. (!z. z IN p ==> y <= z) ==> y <= x)
Proof
    REWRITE_TAC [IN_APP, inf_eq]
QED

Theorem inf_const:   !x. extreal_inf (\y. y = x) = x
Proof
    RW_TAC real_ss [inf_eq, le_refl]
QED

Theorem inf_sing :
    !a:extreal. inf {a} = a
Proof
    REWRITE_TAC [METIS [EXTENSION, IN_SING, IN_DEF] ``{a} = (\x. x = a)``]
 >> SIMP_TAC std_ss [inf_const]
QED

Theorem inf_const_alt:   !p z. (?x. p x) /\ (!x. p x ==> (x = z)) ==> (inf p = z)
Proof
  RW_TAC std_ss [inf_eq,le_refl]
  >> POP_ASSUM MATCH_MP_TAC
  >> RW_TAC std_ss []
QED

Theorem inf_const_alt' :
    !p z. (?x. x IN p) /\ (!x. x IN p ==> (x = z)) ==> (inf p = z)
Proof
    rw [IN_APP, inf_const_alt]
QED

Theorem inf_const_over_set:   !s k. s <> {} ==> (inf (IMAGE (\x. k) s) = k)
Proof
  RW_TAC std_ss [inf_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE] >> RW_TAC std_ss [le_refl])
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE]
  >> METIS_TAC [CHOICE_DEF]
QED

Theorem inf_suc:
     !f. (!m n. m <= n ==> f n <= f m) ==>
     (inf (IMAGE (\n. f (SUC n)) UNIV) = inf (IMAGE f UNIV))
Proof
  RW_TAC std_ss [inf_eq,inf_le,le_inf]
  >- (POP_ASSUM MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [])
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `f (SUC x)`
  >> RW_TAC real_ss []
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> METIS_TAC []
QED

Theorem inf_seq :
    !f l. mono_decreasing f ==>
         ((f --> l) <=> (inf (IMAGE (\n. Normal (f n)) UNIV) = Normal l))
Proof
     RW_TAC std_ss []
  >> EQ_TAC
  >- (RW_TAC std_ss [inf_eq]
      >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> RW_TAC std_ss [extreal_le_def]
          >> METIS_TAC [mono_decreasing_suc,SEQ_LE_MONO,ADD1])
      >> `!n. y <= Normal (f n)`
            by (RW_TAC std_ss []
                >> POP_ASSUM MATCH_MP_TAC
                >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
                >> METIS_TAC [])
      >> Cases_on `y`
      >| [METIS_TAC [le_infty],
          METIS_TAC [le_infty,extreal_not_infty],
          METIS_TAC [LE_SEQ_IMP_LE_LIM,extreal_le_def]])
  >> RW_TAC std_ss [extreal_inf_def,extreal_sup_def,extreal_ainv_def,extreal_not_infty]
  >> `(\r. IMAGE numeric_negate (IMAGE (\n. Normal (f n)) univ(:num)) (Normal r)) =
       IMAGE (\n. - f n) UNIV`
       by (RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV]
           >> EQ_TAC
           >- (RW_TAC std_ss []
               >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
               >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
               >> METIS_TAC [extreal_ainv_def,extreal_11])
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
           >> METIS_TAC [extreal_ainv_def,extreal_11])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss []
  >> `!n. -Normal (f n) <= x`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!y. P` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
           >> METIS_TAC [])
  >> `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans]
  >> `?z. x = Normal z` by METIS_TAC [extreal_cases]
  >> `!n. -(f n) <= z` by METIS_TAC [extreal_le_def,extreal_ainv_def]
  >> Suff `(\n. -f n) --> sup (IMAGE (\n. -f n) univ(:num))`
  >- METIS_TAC [SEQ_NEG,REAL_NEG_NEG]
  >> `mono_increasing (\n. -f n)`
        by FULL_SIMP_TAC std_ss [mono_increasing_def,mono_decreasing_def,REAL_LE_NEG]
  >> Suff `?r. (\n. -f n) --> r`
  >- METIS_TAC [mono_increasing_converges_to_sup]
  >> RW_TAC std_ss [GSYM convergent]
  >> MATCH_MP_TAC SEQ_ICONV
  >> FULL_SIMP_TAC std_ss [GREATER_EQ,real_ge,mono_increasing_def]
  >> MATCH_MP_TAC SEQ_BOUNDED_2
  >> Q.EXISTS_TAC `-f 0`
  >> Q.EXISTS_TAC `z`
  >> RW_TAC std_ss []
QED

Theorem inf_lt_infty:   !p. (NegInf < inf p) ==> (!x. p x ==> NegInf < x)
Proof
  METIS_TAC [inf_le_imp,lte_trans]
QED

Theorem inf_min:   !p z. p z /\ (!x. p x ==> z <= x) ==> (inf p = z)
Proof
  RW_TAC std_ss [inf_eq]
QED

Theorem inf_cminus:   !f c. Normal c - inf (IMAGE f UNIV) =
                         sup (IMAGE (\n. Normal c - f n) UNIV)
Proof
 (* new proof *)
  RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> `inf (IMAGE f UNIV) <= f n`
           by (MATCH_MP_TAC inf_le_imp
               >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
               >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
               >> METIS_TAC [])
      >> METIS_TAC [le_lsub_imp])
  >> `!n. Normal c - f n <= y`
        by (RW_TAC std_ss []
            >> Q.PAT_ASSUM `!z. P` MATCH_MP_TAC
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
            >> METIS_TAC [])
  >> RW_TAC std_ss [extreal_inf_def,sub_rneg]
  >> Suff `sup (IMAGE numeric_negate (IMAGE f UNIV)) <= y - Normal c`
  >- METIS_TAC [le_sub_eq,extreal_not_infty,add_comm_normal]
  >> RW_TAC std_ss [sup_le]
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> RW_TAC std_ss [le_sub_eq,extreal_not_infty,GSYM add_comm_normal]
  >> Cases_on `y = PosInf` >- RW_TAC std_ss [le_infty]
  >> `f x' <> NegInf` by METIS_TAC [extreal_sub_def,lt_infty,extreal_lt_def]
  >> METIS_TAC [extreal_not_infty,extreal_sub_add]
QED

(* The "inf" of an empty set is PosInf, reasonable but quite unexpected *)
Theorem inf_empty:   inf EMPTY = PosInf
Proof
    RW_TAC std_ss [extreal_inf_def, extreal_sup_def, IMAGE_EMPTY,
                   REWRITE_RULE [IN_APP] NOT_IN_EMPTY, extreal_ainv_def]
QED

(* The "sup" of an empty set is NegInf, reasonable but quite unexpected *)
Theorem sup_empty:   sup EMPTY = NegInf
Proof
    RW_TAC std_ss [extreal_sup_def, IMAGE_EMPTY,
                   REWRITE_RULE [IN_APP] NOT_IN_EMPTY, extreal_ainv_def]
 >> METIS_TAC [num_not_infty]
QED

Theorem sup_univ:   sup univ(:extreal) = PosInf
Proof
    RW_TAC std_ss [sup_eq', IN_UNIV, GSYM le_infty]
QED

Theorem inf_univ:   inf univ(:extreal) = NegInf
Proof
    RW_TAC std_ss [inf_eq', IN_UNIV, GSYM le_infty]
QED

Theorem inf_lt:   !P y. (?x. P x /\ x < y) <=> extreal_inf P < y
Proof
    RW_TAC std_ss []
 >> EQ_TAC >- METIS_TAC [inf_le_imp, let_trans]
 >> RW_TAC std_ss []
 >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
 >> METIS_TAC [le_inf,extreal_lt_def]
QED

Theorem inf_lt' :
    !P y. (?x. x IN P /\ x < y) <=> extreal_inf P < y
Proof
    REWRITE_TAC [IN_APP, inf_lt]
QED

(* dual version of sup_lt_epsilon *)
Theorem lt_inf_epsilon :
    !P e. 0 < e /\ (?x. P x /\ x <> PosInf) /\ inf P <> NegInf ==>
          ?x. P x /\ x < inf P + e
Proof
    RW_TAC std_ss []
 >> Cases_on `e = PosInf` (* ``inf P <> NegInf`` is necessary here *)
 >- (Q.EXISTS_TAC `x`
     >> RW_TAC std_ss []
     >> METIS_TAC [extreal_add_def,lt_infty,extreal_cases])
 >> `e <> NegInf` by METIS_TAC [le_sup_imp,lt_infty,lte_trans,
                                extreal_of_num_def,extreal_not_infty]
 >> `inf P <> PosInf` by METIS_TAC [inf_le_imp,lt_infty,let_trans]
 >> `inf P < inf P + e`
     by (Cases_on `inf P` \\
         Cases_on `e` \\
         RW_TAC std_ss [extreal_cases, extreal_add_def, extreal_lt_def,
                        extreal_le_def, GSYM real_lt] \\
         METIS_TAC [REAL_LT_ADDR, extreal_lt_def, extreal_le_def,
                    extreal_of_num_def, real_lt])
 >> `?x. P x /\ x < inf P + e` by METIS_TAC [inf_lt]
 >> Q.EXISTS_TAC `x'`
 >> RW_TAC std_ss []
QED

Theorem lt_inf_epsilon' :
    !P e. 0 < e /\ (?x. x IN P /\ x <> PosInf) /\ inf P <> NegInf ==>
          ?x. x IN P /\ x < inf P + e
Proof
    REWRITE_TAC [IN_APP, lt_inf_epsilon]
QED

Theorem inf_num :
    inf (\x. ?n :num. x = -&n) = NegInf
Proof
    rw [GSYM le_infty, inf_le]
 >> CCONTR_TAC
 >> fs [GSYM extreal_lt_def, GSYM lt_infty]
 >> STRIP_ASSUME_TAC (MATCH_MP (Q.SPEC ‘y’ SIMP_EXTREAL_ARCH_NEG)
                               (ASSUME “y <> NegInf”))
 >> Know ‘-&SUC n < y’
 >- (MATCH_MP_TAC lte_trans \\
     Q.EXISTS_TAC ‘-&n’ >> rw [extreal_of_num_def, extreal_ainv_def, extreal_lt_eq])
 >> DISCH_TAC
 >> Suff ‘y <= -&SUC n’ >- METIS_TAC [let_antisym]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘SUC n’ >> rw []
QED

(* NOTE: This theorem doesn't hold in general, when ‘r = 0’ or ‘Normal r = PosInf’ *)
Theorem inf_cmul :
    !P r. 0 < r ==>
          inf {x * Normal r | 0 < x /\ P x} = Normal r * inf {x | 0 < x /\ P x}
Proof
    rw [inf_eq']
 >| [ (* goal 1 (of 2) *)
     ‘x * Normal r = Normal r * x’ by rw [mul_comm] >> POP_ORW \\
      MATCH_MP_TAC le_lmul_imp \\
      CONJ_TAC >- rw [REAL_LT_IMP_LE, extreal_of_num_def, extreal_le_eq] \\
      Cases_on ‘x = PosInf’ >- rw [le_infty] \\
      MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC \\
      MATCH_MP_TAC lt_imp_le >> rw [GSYM inf_lt] \\
      Q.EXISTS_TAC ‘x’ >> art [] \\
      MATCH_MP_TAC lt_addr_imp >> art [] \\
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC lt_imp_le >> art [],
      (* goal 2 (of 2) *)
      ONCE_REWRITE_TAC [mul_comm] \\
      Know ‘y <= inf {x | 0 < x /\ P x} * Normal r <=>
            y / Normal r <= inf {x | 0 < x /\ P x}’
      >- (MATCH_MP_TAC le_ldiv >> art []) >> Rewr' \\
      rw [le_inf] >> rename1 ‘P z’ \\
      Know ‘y / Normal r <= z <=> y <= z * Normal r’
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          MATCH_MP_TAC le_ldiv >> art []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘z’ >> art [] ]
QED

(* NOTE: This theorem is based on sup_cmul_general and extreal_inf_def *)
Theorem inf_cmul_general :
    !f c J.
        0 <= c /\ J <> {} ==>
        inf (IMAGE (\n. Normal c * f n) J) = Normal c * inf (IMAGE f J)
Proof
    rw [extreal_inf_def, IMAGE_IMAGE, o_DEF]
 >> Know ‘!n. -(Normal c * f n) = Normal c * -f n’
 >- (rw [neg_minus1', mul_assoc] \\
     AP_THM_TAC >> AP_TERM_TAC \\
     simp [Once mul_comm])
 >> Rewr'
 >> qabbrev_tac ‘g = \n. -f n’
 >> ‘!n. -f n = g n’ by rw [Abbr ‘g’] >> POP_ORW
 >> simp [sup_cmul_general]
 >> simp [neg_minus1', mul_assoc]
 >> AP_THM_TAC >> AP_TERM_TAC
 >> simp [Once mul_comm]
QED

(* |- !f c.
        0 <= c ==>
        inf (IMAGE (\n. Normal c * f n) univ(:'a)) =
        Normal c * inf (IMAGE f univ(:'a))
 *)
Theorem inf_cmul' =
        inf_cmul_general |> INST_TYPE [“:'index” |-> alpha]
                         |> Q.SPECL [‘f’, ‘c’, ‘UNIV’] |> SRULE [] |> GEN_ALL

Theorem sup_comm_ext :
    !(f :'a -> 'a -> extreal) A B.
        sup {sup {f i j | j IN A} | i IN B} =
        sup {sup {f i j | i IN B} | j IN A}
Proof
  RW_TAC std_ss [sup_eq] THENL
  [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [sup_le] THEN
   GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [le_sup] THEN
   GEN_TAC THEN
   DISCH_THEN (MP_TAC o Q.SPEC `sup {f (i:'a) (j:'a) | i IN B}`) THEN
   impl_tac >- (rw [] >> Q.EXISTS_TAC ‘j’ >> art []) \\
   RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
   Q.EXISTS_TAC `sup {f i j | i IN B}` THEN ASM_REWRITE_TAC [le_sup] THEN
   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
   rw [] >> Q.EXISTS_TAC ‘i’ >> art [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [sup_le] THEN GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [sup_le] THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `sup {f (i:'a) (j:'a) | j IN A}`) THEN
  impl_tac >- (rw [] >> Q.EXISTS_TAC ‘i’ >> art []) \\
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
  Q.EXISTS_TAC `sup {f i j | j IN A}` THEN ASM_SIMP_TAC std_ss [le_sup] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  rw [] >> Q.EXISTS_TAC ‘j’ >> art []
QED

Theorem sup_comm : (* was: SUP_commute *)
    !f. sup {sup {f i j | j IN univ(:num)} | i IN univ(:num)} =
        sup {sup {f i j | i IN univ(:num)} | j IN univ(:num)}
Proof
    rw [sup_comm_ext]
QED

Theorem sup_close : (* was: Sup_ereal_close *)
    !e s. 0 < e /\ abs (sup s) <> PosInf /\ s <> {} ==>
          ?x. x IN s /\ sup s - e < x
Proof
  RW_TAC std_ss [] THEN
  `?r. sup s = Normal r` by METIS_TAC [extreal_cases, extreal_abs_def] THEN
  `e <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lt_trans] THEN
  Q_TAC SUFF_TAC `Normal r - e < sup s` THENL
  [SIMP_TAC std_ss [lt_sup] THEN RW_TAC std_ss [],
   ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``e = PosInf`` THENL
   [ASM_REWRITE_TAC [extreal_sub_def, lt_infty], ALL_TAC] THEN
   `?k. e = Normal k` by METIS_TAC [extreal_cases] THEN
   ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_lt_eq] THEN
   MATCH_MP_TAC (REAL_ARITH ``0 < k ==> a - k < a:real``) THEN
   ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN
   METIS_TAC [extreal_of_num_def]]
QED

(* This lemma find a countable monotonic sequence of element in any non-empty
   extreal sets, with the same limit point.
 *)
Theorem sup_countable_seq : (* was: Sup_countable_SUPR *)
    !A. A <> {} ==> ?f:num->extreal. IMAGE f UNIV SUBSET A /\
                      (sup A = sup {f n | n IN UNIV})
Proof
    RW_TAC std_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `sup A` extreal_cases) (* 3 subgoals *)
 >| [ (* goal 1 (of 3): NegInf *)
      POP_ASSUM (MP_TAC o REWRITE_RULE [sup_eq]) THEN RW_TAC std_ss [le_infty] THEN
     `A = {NegInf}` by ASM_SET_TAC [] THEN
      ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `(\n. NegInf)` THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [] THEN
      AP_TERM_TAC THEN SET_TAC [],
      (* goal 2 (of 3): PosInf *)
   FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
   ASM_CASES_TAC ``PosInf IN A`` THENL
   [Q.EXISTS_TAC `(\x. PosInf)` THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN
    REWRITE_TAC [SET_RULE ``{PosInf | n IN univ(:num)} = {PosInf}``] THEN
    SIMP_TAC std_ss [sup_sing], ALL_TAC] THEN
   Q_TAC SUFF_TAC `?x. x IN A /\ 0 <= x` THENL
   [STRIP_TAC,
    UNDISCH_TAC ``sup A = PosInf`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    SIMP_TAC std_ss [sup_eq] THEN RW_TAC std_ss [lt_infty, GSYM extreal_lt_def] THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `z`) THEN ASM_SIMP_TAC std_ss [le_lt]] THEN
   Q_TAC SUFF_TAC `!n. ?f. f IN A /\ x' + Normal (&n) <= f` THENL
   [DISCH_TAC,
    CCONTR_TAC THEN Q_TAC SUFF_TAC `?n. sup A <= x' + Normal (&n)` THENL
    [RW_TAC std_ss [GSYM extreal_lt_def] THEN
     `x' <> PosInf` by METIS_TAC [] THEN
     ASM_CASES_TAC ``x' = NegInf`` THENL
     [FULL_SIMP_TAC std_ss [extreal_add_def, lt_infty], ALL_TAC] THEN
     `?r. x' = Normal r` by METIS_TAC [extreal_cases] THEN
     ASM_SIMP_TAC std_ss [extreal_add_def, lt_infty],
     ALL_TAC] THEN
    SIMP_TAC std_ss [sup_le] THEN FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
    Q.EXISTS_TAC `n` THEN
    GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `y`) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [le_lt]] THEN
   Q_TAC SUFF_TAC `?f. !z. f z IN A /\ x' + Normal (&z) <= f z` THENL
   [STRIP_TAC, METIS_TAC []] THEN
   Q_TAC SUFF_TAC `sup {f n | n IN UNIV} = PosInf` THENL
   [DISCH_TAC THEN Q.EXISTS_TAC `f` THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ASM_REWRITE_TAC [] THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `!n. ?i. Normal (&n) <= f i` THENL
   [DISCH_TAC,
    GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN STRIP_TAC THEN
    Q.EXISTS_TAC `n` THEN MATCH_MP_TAC le_trans THEN
    Q.EXISTS_TAC `x' + Normal (&n)` THEN ASM_REWRITE_TAC [] THEN
    `x' <> PosInf` by METIS_TAC [] THEN
    `x' <> NegInf` by (METIS_TAC [lt_infty, lte_trans, num_not_infty]) THEN
    `?r. x' = Normal r` by (METIS_TAC [extreal_cases]) THEN
    ASM_SIMP_TAC std_ss [extreal_add_def, extreal_le_def] THEN
    MATCH_MP_TAC (REAL_ARITH ``0 <= b ==> a <= b + a:real``) THEN
    METIS_TAC [extreal_le_def, extreal_of_num_def]] THEN
   SIMP_TAC std_ss [sup_eq] THEN
   CONJ_TAC THENL [SIMP_TAC std_ss [le_infty], ALL_TAC] THEN
   RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [GSYM extreal_lt_def, GSYM lt_infty] THEN
   POP_ASSUM (MP_TAC o MATCH_MP SIMP_EXTREAL_ARCH) THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n`) THEN STRIP_TAC THEN
   Q.EXISTS_TAC `f i` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [IN_UNIV], ALL_TAC] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `Normal (&SUC n)` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `&n` THEN
   ASM_REWRITE_TAC [] THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq],
      (* goal 3 (of 3): Normal r *)
      Know `!n:num. ?x. x IN A /\ sup A < x + 1 / &(SUC n)`
      >- (GEN_TAC \\
          Know `?x. x IN A /\ sup A - 1 / &(SUC n) < x`
          >- (MATCH_MP_TAC sup_close \\
              ASM_SIMP_TAC std_ss [extreal_abs_def, lt_infty] \\
             `&(SUC n) = Normal &(SUC n)` by METIS_TAC [extreal_of_num_def] \\
             `SUC n <> 0` by RW_TAC arith_ss [] \\
             `(0 :real) < &(SUC n)` by METIS_TAC [REAL_NZ_IMP_LT] \\
              METIS_TAC [lt_div, lt_01]) >> RW_TAC std_ss [] \\
          Q.EXISTS_TAC `x` >> art [] \\
         `&(SUC n) = Normal &(SUC n)` by METIS_TAC [extreal_of_num_def] \\
         `&(SUC n) <> (0 :real)` by RW_TAC real_ss [] \\
         `(1 :extreal) / &SUC n = Normal (1 / &SUC n)`
            by METIS_TAC [extreal_of_num_def, extreal_div_eq] >> fs [] \\
         `Normal (1 / &SUC n) <> PosInf /\ Normal (1 / &SUC n) <> NegInf`
            by PROVE_TAC [extreal_not_infty] \\
          METIS_TAC [sub_lt_eq]) >> DISCH_TAC \\
      FULL_SIMP_TAC std_ss [SKOLEM_THM] \\
      Know `sup {f n | n IN univ(:num)} = sup A`
      >- (RW_TAC std_ss [sup_eq', GSPECIFICATION, IN_UNIV]
          >- (Q.PAT_X_ASSUM `sup A = _` (ONCE_REWRITE_TAC o wrap o SYM) \\
              MATCH_MP_TAC le_sup_imp >> METIS_TAC [IN_APP]) \\
          Q.PAT_X_ASSUM `sup A = _` (ONCE_REWRITE_TAC o wrap o SYM) \\
          MATCH_MP_TAC le_epsilon >> RW_TAC std_ss [] \\
         `e <> NegInf` by METIS_TAC [lt_trans, lt_infty] \\
         `?r. e = Normal r` by METIS_TAC [extreal_cases] \\
          ONCE_ASM_REWRITE_TAC [] \\
         `0 < r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
         `?n. inv (&SUC n) < r` by METIS_TAC [REAL_ARCH_INV_SUC] \\
          MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `f n + 1 / &SUC n` \\
          CONJ_TAC >- METIS_TAC [le_lt] \\
          MATCH_MP_TAC le_add2 \\
          CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                       Q.EXISTS_TAC `n` >> REWRITE_TAC []) \\
         `&SUC n <> (0 :real)` by RW_TAC real_ss [] \\
          ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq,
                               extreal_le_eq, GSYM REAL_INV_1OVER] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
      Q.EXISTS_TAC `f` >> ASM_SET_TAC [] ]
QED

Theorem sup_seq_countable_seq : (* was: SUPR_countable_SUPR *)
    !A g. A <> {} ==>
          ?f:num->extreal. IMAGE f UNIV SUBSET IMAGE g A /\
                    (sup {g n | n IN A} = sup {f n | n IN UNIV})
Proof
  RW_TAC std_ss [] THEN ASSUME_TAC sup_countable_seq THEN
  POP_ASSUM (MP_TAC o Q.SPEC `IMAGE g A`) THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN DISCH_THEN (MATCH_MP_TAC) THEN
  ASM_SET_TAC []
QED

Theorem inf_countable_seq :
    !A. A <> {} ==> ?f. IMAGE f univ(:num) SUBSET A /\
                        inf A = inf {f n | n IN univ(:num)}
Proof
    rw [extreal_inf_def]
 >> qabbrev_tac ‘A' = IMAGE numeric_negate A’
 >> MP_TAC (Q.SPEC ‘A'’ sup_countable_seq)
 >> impl_tac >- rw [Once EXTENSION, Abbr ‘A'’]
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘\n. -f n’
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘_ SUBSET A'’ MP_TAC \\
     rw [SUBSET_DEF] \\
     Know ‘f n IN A'’ >- (POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘n’ >> rw []) \\
     rw [Abbr ‘A'’] >> fs [])
 >> POP_ORW
 >> AP_TERM_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘-f n’ >> simp [] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> Q.EXISTS_TAC ‘n’ >> simp []
QED

Theorem inf_seq_countable_inf :
    !A g. A <> {} ==>
          ?f:num->extreal. IMAGE f UNIV SUBSET IMAGE g A /\
                    (inf {g n | n IN A} = inf {f n | n IN UNIV})
Proof
  RW_TAC std_ss [] THEN ASSUME_TAC inf_countable_seq THEN
  POP_ASSUM (MP_TAC o Q.SPEC `IMAGE g A`) THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN DISCH_THEN (MATCH_MP_TAC) THEN
  ASM_SET_TAC []
QED

(* ------------------------------------------------------------------------- *)
(*  Limit superior and limit inferior (limsup and liminf) [1, p.313] [4]     *)
(* ------------------------------------------------------------------------- *)

(* for a sequence of function (u :num -> 'a -> extreal),
   use `ext_limsup (\n. u n x)` as "limsup u x" [1, p.63], etc.

   cf. set_limsup_def and set_liminf_def (borelTheory)
 *)
Definition ext_limsup_def:
    ext_limsup (a :num -> extreal) = inf (IMAGE (\m. sup {a n | m <= n}) UNIV)
End

Definition ext_liminf_def:
    ext_liminf (a :num -> extreal) = sup (IMAGE (\m. inf {a n | m <= n}) UNIV)
End

Overload limsup = ``ext_limsup``
Overload liminf = ``ext_liminf``

Theorem ext_liminf_le_limsup :
    !a. liminf a <= limsup a
Proof
    rw [ext_limsup_def, le_inf']
 >> rw [le_sup']
 >> rw [ext_liminf_def, sup_le']
 >> rw [inf_le']
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘a (MAX m m')’
 >> reverse CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘MAX m m'’ >> rw [MAX_LE])
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘MAX m m'’
 >> rw [MAX_LE]
QED

(* Properties A.1 (ii) [1, p.409] *)
Theorem ext_liminf_alt_limsup :
    !a. liminf a = -limsup (numeric_negate o a)
Proof
    rw [ext_liminf_def, ext_limsup_def, extreal_inf_def]
 >> Know ‘!m. IMAGE numeric_negate {a n | m <= n} = {-a n | m <= n}’
 >- (rw [Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rw [] >- (Q.EXISTS_TAC ‘n’ >> rw []) \\
     Q.EXISTS_TAC ‘a n’ >> rw [] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> Rewr'
 >> Q.ABBREV_TAC ‘f = \m. sup {(-a n) | m <= n}’ >> simp []
 >> rw [IMAGE_IMAGE, o_DEF]
QED

Theorem ext_limsup_alt_liminf :
    !a. limsup a = -liminf (numeric_negate o a)
Proof
    rw [ext_liminf_alt_limsup, o_DEF]
 >> METIS_TAC []
QED

Theorem ext_limsup_upperbound :
    !a c. (!n. a n <= c) ==> limsup a <= c
Proof
    rw [ext_limsup_def, inf_le']
 >> Know ‘!m. y <= sup {a n | m <= n}’
 >- (Q.X_GEN_TAC ‘m’ \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘m’ >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!z. _ ==> y <= z’ K_TAC
 >> Q_TAC (TRANS_TAC le_trans) ‘sup {a n | 0 <= n}’
 >> rw [sup_le'] >> art []
QED

Theorem ext_limsup_lowerbound :
    !a c. (!n. c <= a n) ==> c <= limsup a
Proof
    rw [ext_limsup_def, le_inf']
 >> rw [le_sup']
 >> Know ‘!n. m <= n ==> a n <= y’
 >- (rpt STRIP_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!z. _ ==> z <= y’ K_TAC
 >> Q_TAC (TRANS_TAC le_trans) ‘a m’ >> rw []
QED

Theorem ext_liminf_upperbound :
    !a c. (!n. a n <= c) ==> liminf a <= c
Proof
    rw [ext_liminf_def, sup_le']
 >> rw [inf_le']
 >> Know ‘!n. m <= n ==> y <= a n’
 >- (rpt STRIP_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!z. _ ==> y <= z’ K_TAC
 >> Q_TAC (TRANS_TAC le_trans) ‘a m’ >> rw []
QED

Theorem ext_liminf_lowerbound :
    !a c. (!n. c <= a n) ==> c <= liminf a
Proof
    rw [ext_liminf_def, le_sup']
 >> Know ‘!m. inf {a n | m <= n} <= y’
 >- (Q.X_GEN_TAC ‘m’ \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘m’ >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!z. _ ==> z <= y’ K_TAC
 >> Q_TAC (TRANS_TAC le_trans) ‘inf {a n | 0 <= n}’
 >> rw [le_inf'] >> art []
QED

Theorem ext_limsup_pos :
    !a. (!n. 0 <= a n) ==> 0 <= limsup a
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ext_limsup_lowerbound >> art []
QED

Theorem ext_liminf_pos :
    !a. (!n. 0 <= a n) ==> 0 <= liminf a
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ext_liminf_lowerbound >> art []
QED

Theorem ext_limsup_bounded :
    !a k. (!n. abs (a n) <= k) ==> abs (limsup a) <= k
Proof
    rw [abs_bounds]
 >| [ MATCH_MP_TAC ext_limsup_lowerbound >> rw [],
      MATCH_MP_TAC ext_limsup_upperbound >> rw [] ]
QED

Theorem ext_liminf_bounded :
    !a k. (!n. abs (a n) <= k) ==> abs (liminf a) <= k
Proof
    rw [abs_bounds]
 >| [ MATCH_MP_TAC ext_liminf_lowerbound >> rw [],
      MATCH_MP_TAC ext_liminf_upperbound >> rw [] ]
QED

Theorem sup_pos :
    !a m. (!n. 0 <= a n) ==> 0 <= sup {a n | m <= (n :num)}
Proof
    rw [le_sup']
 >> Q_TAC (TRANS_TAC le_trans) ‘a m’ >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem sup_pos' :
    !a. (!n. 0 <= a n) ==> 0 <= sup (IMAGE a UNIV)
Proof
    rw [le_sup']
 >> Q_TAC (TRANS_TAC le_trans) ‘a ARB’ >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘ARB’ >> rw []
QED

Theorem inf_pos :
    !a m. (!n. 0 <= a n) ==> 0 <= inf {a n | m <= (n :num)}
Proof
    rw [le_inf'] >> rw []
QED

Theorem inf_pos' :
    !a. (!n. 0 <= a n) ==> 0 <= inf (IMAGE a UNIV)
Proof
    rw [le_inf'] >> rw []
QED

Theorem sup_bounded :
    !a k. (!n. abs (a n) <= k) ==> !m. abs (sup {a n | m <= (n :num)}) <= k
Proof
    reverse (rw [abs_bounds])
 >- (rw [sup_le'] >> art [])
 >> rw [le_sup']
 >> Q_TAC (TRANS_TAC le_trans) ‘a m’ >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem sup_bounded' :
    !a k. (!n. abs (a n) <= k) ==> abs (sup (IMAGE a UNIV)) <= k
Proof
    reverse (rw [abs_bounds])
 >- (rw [sup_le'] >> art [])
 >> rw [le_sup']
 >> Q_TAC (TRANS_TAC le_trans) ‘a ARB’ >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘ARB’ >> rw []
QED

Theorem sup_bounded_alt :
    !s. s <> {} /\ (!x. x IN s ==> abs x <= Normal k) ==>
        abs (sup s) <= Normal k
Proof
    reverse (rw [abs_bounds]) >- rw [sup_le']
 >> rw [le_sup']
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> Q_TAC (TRANS_TAC le_trans) ‘x’ >> rw []
QED

Theorem inf_bounded :
    !a k. (!n. abs (a n) <= k) ==> !m. abs (inf {a n | m <= (n :num)}) <= k
Proof
    rw [abs_bounds]
 >- (rw [le_inf'] >> art [])
 >> rw [inf_le']
 >> Q_TAC (TRANS_TAC le_trans) ‘a m’ >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem inf_bounded' :
    !a k. (!n. abs (a n) <= k) ==> !m. abs (inf (IMAGE a UNIV)) <= k
Proof
    rw [abs_bounds]
 >- (rw [le_inf'] >> art [])
 >> rw [inf_le']
 >> Q_TAC (TRANS_TAC le_trans) ‘a ARB’ >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘ARB’ >> rw []
QED

Theorem inf_bounded_alt :
    !s. s <> {} /\ (!x. x IN s ==> abs x <= Normal k) ==>
        abs (inf s) <= Normal k
Proof
    rw [abs_bounds] >- rw [le_inf']
 >> rw [inf_le']
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> Q_TAC (TRANS_TAC le_trans) ‘x’ >> rw []
QED

Theorem sup_normal :
    !s k. abs (sup s) <= Normal k ==> Normal (sup (s o Normal)) = sup s
Proof
    rw [extreal_sup_def, extreal_abs_def, abs_bounds, le_infty, extreal_ainv_def,
        extreal_le_eq, o_DEF]
QED

Theorem inf_normal :
    !s k. abs (inf s) <= Normal k ==> Normal (inf (s o Normal)) = inf s
Proof
    rw [extreal_inf_def, inf_def, GSYM extreal_ainv_def, abs_bounds, le_neg]
 >> Know ‘(\r. s (-Normal r)) = s o numeric_negate o Normal’
 >- rw [o_DEF, FUN_EQ_THM]
 >> Rewr'
 >> REWRITE_TAC [o_ASSOC]
 >> Know ‘IMAGE numeric_negate s = s o numeric_negate’
 >- (rw [Once EXTENSION, o_DEF, IN_APP] \\
     METIS_TAC [neg_neg])
 >> DISCH_THEN (FULL_SIMP_TAC bool_ss o wrap)
 >> qabbrev_tac ‘P = s o numeric_negate’
 >> MATCH_MP_TAC sup_normal
 >> Q.EXISTS_TAC ‘k’
 >> rw [abs_bounds]
 >> METIS_TAC [neg_neg, le_neg]
QED

(* ------------------------------------------------------------------------- *)
(* Suminf over extended reals. Definition and properties                     *)
(* ------------------------------------------------------------------------- *)

(* old definition, which (wrongly) allows `!f. 0 <= ext_suminf f`:
val ext_suminf_def = Define
   `ext_suminf f = sup (IMAGE (\n. SIGMA f (count n)) UNIV)`;

   new definition, which is only specified on positive functions: *)
local
  val thm = Q.prove (
     `?sum. !f. (!n. 0 <= f n) ==>
                (sum f = sup (IMAGE (\n. SIGMA f (count n)) UNIV))`,
      Q.EXISTS_TAC `\f. sup (IMAGE (\n. SIGMA f (count n)) UNIV)` \\
      RW_TAC std_ss []);
in
  val ext_suminf_def = new_specification
    ("ext_suminf_def", ["ext_suminf"], thm);
end;

Theorem ext_suminf_alt : (* without IMAGE *)
    !f. (!n. 0 <= f n) ==>
        (ext_suminf (\x. f x) = sup {SIGMA (\i. f i) (count n) | n IN UNIV})
Proof
    RW_TAC std_ss [ext_suminf_def, IMAGE_DEF]
QED

Theorem ext_suminf_alt' : (* without IMAGE, further simplified *)
    !f. (!n. 0 <= f n) ==>
        (ext_suminf (\x. f x) = sup {SIGMA f (count n) | n | T})
Proof
    RW_TAC bool_ss [ext_suminf_alt, ETA_AX, IN_UNIV]
QED

Theorem ext_suminf_add :
    !f g. (!n. 0 <= f n /\ 0 <= g n) ==>
          (ext_suminf (\n. f n + g n) = ext_suminf f + ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\n. f n + g n) n`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC le_add >> art []) >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))
 >> RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV]
 >- (`!n. f n <> NegInf /\ g n <> NegInf`
       by METIS_TAC [lt_infty, lte_trans, num_not_infty] \\
     RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_ADD] \\
     MATCH_MP_TAC le_add2 \\
     RW_TAC std_ss [le_sup'] \\
     POP_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC [])
 >> Know `!n. SIGMA (\n. f n + g n) (count n) <= y`
 >- (RW_TAC std_ss [] >> POP_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> `!n. f n <> NegInf /\ g n <> NegInf`
       by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> `!n. SIGMA (\n. f n + g n) (count n) =
         SIGMA f (count n) + SIGMA g (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_ADD, FINITE_COUNT]
 >> `!n. SIGMA f (count n) + SIGMA g (count n) <= y`
       by FULL_SIMP_TAC std_ss []
 >> Know `!n m. SIGMA f (count n) + SIGMA g (count m) <= y`
 >- (RW_TAC std_ss [] \\
     Cases_on `n <= m`
     >- (MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC `SIGMA f (count m) + SIGMA g (count m)` \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_radd_imp \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
         RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT] \\
         DECIDE_TAC) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `SIGMA f (count n) + SIGMA g (count n)` \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_ladd_imp \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT] \\
     DECIDE_TAC) >> DISCH_TAC
 >> Cases_on `y = PosInf` >- RW_TAC std_ss [le_infty]
 >> `!n. SIGMA f (count n) <> NegInf`
       by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT]
 >> `!n. SIGMA g (count n) <> NegInf`
       by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT]
 >> `y <> NegInf` by METIS_TAC [lt_infty, add_not_infty, lte_trans]
 >> FULL_SIMP_TAC std_ss [GSYM le_sub_eq2]
 >> Know `!m. sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <= y - SIGMA g (count m)`
 >- (RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
     FULL_SIMP_TAC std_ss []) >> DISCH_TAC
 >> Know `sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <> NegInf`
 >- (RW_TAC std_ss [lt_infty, GSYM sup_lt', IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `SIGMA f (count 0)` \\
     reverse (RW_TAC bool_ss []) >- FULL_SIMP_TAC std_ss [lt_infty] \\
     Q.EXISTS_TAC `0` >> REWRITE_TAC []) >> DISCH_TAC
 >> `!m. SIGMA g (count m) + sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <= y`
       by METIS_TAC [le_sub_eq2, add_comm]
 >> `!m. SIGMA g (count m) <= y - sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
       by METIS_TAC [le_sub_eq2]
 >> `!m. sup (IMAGE (\n. SIGMA g (count n)) univ(:num)) <=
         y - sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
       by (RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
           FULL_SIMP_TAC std_ss [])
 >> Know `sup (IMAGE (\n. SIGMA g (count n)) univ(:num)) <> NegInf`
 >- (RW_TAC std_ss [lt_infty, GSYM sup_lt', IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `SIGMA g (count 0)` \\
     reverse (RW_TAC bool_ss []) >- FULL_SIMP_TAC std_ss [lt_infty] \\
     Q.EXISTS_TAC `0` >> REWRITE_TAC []) >> DISCH_TAC
 >> METIS_TAC [le_sub_eq2, add_comm]
QED

Theorem ext_suminf_add' :
    !f g h. (!n. 0 <= f n) /\ (!n. 0 <= g n) /\ (!n. h n = f n + g n) ==>
            (ext_suminf h = ext_suminf f + ext_suminf g)
Proof
    rpt STRIP_TAC
 >> ‘h = \n. f n + g n’ by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC ext_suminf_add >> rw []
QED

Theorem ext_suminf_cmul :
    !f c. 0 <= c /\ (!n. 0 <= f n) ==>
          (ext_suminf (\n. c * f n) = c * ext_suminf f)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\n. c * f n) n`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC le_mul >> art [])
 >> RW_TAC std_ss [ext_suminf_def]
 >> `c <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans]
 >> `!n. f n <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans]
 >> reverse (Cases_on `c` >> (RW_TAC std_ss []))
 >- (`!n. SIGMA (\n. Normal r * f n) (count n) =
          Normal r * SIGMA f (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL, FINITE_COUNT] >> POP_ORW \\
     METIS_TAC [sup_cmul, extreal_le_def, extreal_of_num_def])
 >> Cases_on `!n. f n = 0`
 >- (RW_TAC std_ss [extreal_mul_def, extreal_of_num_def, EXTREAL_SUM_IMAGE_0,
                    FINITE_COUNT] \\
     Know `sup (IMAGE (\n. Normal 0) univ(:num)) = 0`
     >- (MATCH_MP_TAC sup_const_alt' \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         REWRITE_TAC [extreal_of_num_def]) >> DISCH_TAC \\
     RW_TAC std_ss [extreal_of_num_def, extreal_mul_def])
 >> FULL_SIMP_TAC std_ss []
 >> `0 < f n` by METIS_TAC [lt_le]
 >> Know `0 < sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
 >- (RW_TAC std_ss [GSYM sup_lt'] \\
     Q.EXISTS_TAC `SIGMA f (count (SUC n))` \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV]
     >- (Q.EXISTS_TAC `SUC n` >> REWRITE_TAC []) \\
    `f n <= SIGMA f (count (SUC n))`
       by METIS_TAC [COUNT_SUC, IN_INSERT, FINITE_COUNT,
                     EXTREAL_SUM_IMAGE_POS_MEM_LE] \\
     METIS_TAC [lte_trans]) >> DISCH_TAC
 >> `PosInf * f n <= SIGMA (\n. PosInf * f n) (count (SUC n))`
       by (`!n. 0 <= PosInf * f n` by METIS_TAC [le_infty, le_mul] \\
           `n IN count (SUC n)` by METIS_TAC [COUNT_SUC, IN_INSERT] \\
           (MP_TAC o REWRITE_RULE [FINITE_COUNT] o
            Q.ISPECL [`(\n:num. PosInf * f n)`, `count (SUC n)`])
              EXTREAL_SUM_IMAGE_POS_MEM_LE \\
           RW_TAC std_ss [])
 >> `!x. 0 < x ==> (PosInf * x = PosInf)`
       by (Cases_on `x`
           >| [ METIS_TAC [lt_infty],
                RW_TAC std_ss [extreal_mul_def],
                RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def,
                                extreal_mul_def] ])
 >> `PosInf * f n = PosInf`
       by ((Cases_on `f n` >> FULL_SIMP_TAC std_ss [extreal_mul_def])
           >- METIS_TAC []
           >> METIS_TAC [extreal_lt_eq, extreal_of_num_def])
 >> `SIGMA (\n. PosInf * f n) (count (SUC n)) = PosInf` by METIS_TAC [le_infty]
 >> `SIGMA (\n. PosInf * f n) (count (SUC n)) <=
     sup (IMAGE (\n. SIGMA (\n. PosInf * f n) (count n)) univ(:num))`
       by (MATCH_MP_TAC le_sup_imp' \\
           RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
           METIS_TAC [])
 >> `sup (IMAGE (\n. SIGMA (\n. PosInf * f n) (count n)) univ(:num)) = PosInf`
       by METIS_TAC [le_infty]
 >> METIS_TAC []
QED

Theorem ext_suminf_cmul_alt :
    !f c. 0 <= c /\ (!n. 0 <= f n) /\ (!n. f n < PosInf) ==>
         (ext_suminf (\n. (Normal c) * f n) = (Normal c) * ext_suminf f)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\n. Normal c * f n) n`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC le_mul >> art [] \\
     ASM_REWRITE_TAC [extreal_of_num_def, extreal_le_eq]) >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))
 >> Know `!n. SIGMA (\n. Normal c * f n) (count n) =
              (Normal c) * SIGMA f (count n)`
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_CMUL \\
     RW_TAC std_ss [FINITE_COUNT, lt_infty]) >> Rewr'
 >> RW_TAC std_ss [sup_cmul]
QED

(* Note: changed `ext_suminf f <> PosInf` to `ext_suminf f < PosInf` for
   easier applications. To get the original version, use "lt_infty". *)
Theorem ext_suminf_lt_infty :
    !f. (!n. 0 <= f n) /\ ext_suminf f < PosInf ==> !n. f n < PosInf
Proof
    rpt STRIP_TAC
 >> Q.PAT_ASSUM `!n. 0 <= f n`
       ((FULL_SIMP_TAC std_ss) o wrap o (MATCH_MP ext_suminf_def))
 >> Know `!n. SIGMA f (count n) < PosInf`
 >- (GEN_TAC \\
    `!n. SIGMA f (count n) IN IMAGE (\n. SIGMA f (count n)) UNIV`
       by (RW_TAC std_ss [IN_IMAGE, IN_UNIV] >> METIS_TAC []) \\
     METIS_TAC [sup_lt_infty, SPECIFICATION])
 >> DISCH_TAC
 >> Suff `f n <= SIGMA f (count (SUC n))` >- METIS_TAC [let_trans]
 >> `FINITE (count (SUC n))` by RW_TAC std_ss [FINITE_COUNT]
 >> `n IN (count (SUC n))` by RW_TAC real_ss [IN_COUNT]
 >> METIS_TAC [EXTREAL_SUM_IMAGE_POS_MEM_LE]
QED

local val th =
      SIMP_RULE std_ss [GSYM lt_infty]
                       (ONCE_REWRITE_RULE [MONO_NOT_EQ] (Q.SPEC `f` ext_suminf_lt_infty))
in
Theorem ext_suminf_posinf:
    !f. (!n. 0 <= f n) /\ (?n. f n = PosInf) ==> (ext_suminf f = PosInf)
Proof
    METIS_TAC [th]
QED
end;

Theorem ext_suminf_suminf :
    !r. (!n. 0 <= r n) /\ ext_suminf (\n. Normal (r n)) <> PosInf ==>
        (ext_suminf (\n. Normal (r n)) = Normal (suminf r))
Proof
     GEN_TAC
  >> Suff `(!n. 0 <= r n) ==> ext_suminf (\n. Normal (r n)) <> PosInf ==>
           (ext_suminf (\n. Normal (r n)) = Normal (suminf r))` >- rw []
  >> DISCH_TAC
  >> Know `!n. 0 <= (\n. Normal (r n)) n`
  >- (RW_TAC std_ss [extreal_of_num_def, extreal_le_eq])
  >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def)) >> Rewr'
  >> RW_TAC std_ss []
  >> `!n. FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL]
  >> `(\n. Normal (SIGMA r (count n))) = (\n. Normal ((\n. SIGMA r (count n)) n))` by METIS_TAC []
  >> POP_ORW
  >> `mono_increasing (\n. SIGMA r (count n))`
      by (RW_TAC std_ss [mono_increasing_def,GSYM extreal_le_def]
          >> FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL]
          >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
          >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,SUBSET_DEF,IN_COUNT]
          >> DECIDE_TAC)
  >> RW_TAC std_ss [GSYM sup_seq]
  >> FULL_SIMP_TAC std_ss [suminf,sums,REAL_SUM_IMAGE_EQ_sum]
  >> RW_TAC std_ss []
  >> SELECT_ELIM_TAC
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [sup_eq,le_infty]
  >> `!n. SIGMA (\n. Normal (r n)) (count n) <= y`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!z. P ==> Q` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
  >> `!n. 0 <= SIGMA (\n. Normal (r n)) (count n)`
       by (RW_TAC std_ss []
           >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
           >> METIS_TAC [extreal_le_def,extreal_of_num_def])
  >> `y <> NegInf` by METIS_TAC [lt_infty,num_not_infty,lte_trans]
  >> `?z. y = Normal z` by METIS_TAC [extreal_cases]
  >> `!n. SIGMA r (count n) <= z` by METIS_TAC [extreal_le_def,EXTREAL_SUM_IMAGE_NORMAL]
  >> RW_TAC std_ss [GSYM convergent]
  >> MATCH_MP_TAC SEQ_ICONV
  >> FULL_SIMP_TAC std_ss [GREATER_EQ,real_ge,mono_increasing_def]
  >> MATCH_MP_TAC SEQ_BOUNDED_2
  >> METIS_TAC [REAL_SUM_IMAGE_POS]
QED

(* another version with functional composition *)
Theorem ext_suminf_suminf':
    !r. (!n. 0 <= r n) /\ (ext_suminf (Normal o r) < PosInf) ==>
        (ext_suminf (Normal o r) = Normal (suminf r))
Proof
    METIS_TAC [o_DEF, ext_suminf_suminf, lt_infty]
QED

Theorem ext_suminf_mono :
    !f g. (!n. 0 <= g n) /\ (!n. g n <= f n) ==> (ext_suminf g <= ext_suminf f)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= f n`
 >- (GEN_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `g n` >> art []) >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def, sup_le', le_sup', IN_IMAGE, IN_UNIV]
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA f (count n)`
 >> RW_TAC std_ss []
 >- (MATCH_MP_TAC ((REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`)
                       EXTREAL_SUM_IMAGE_MONO) \\
     RW_TAC std_ss [COUNT_SUC, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC pos_not_neginf >> art [])
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC []
QED

(* removed ‘!n. 0 <= f n’ from antecedents *)
Theorem ext_suminf_eq :
    !f g. (!n. f n = g n) ==> (ext_suminf f = ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Suff ‘f = g’ >- rw []
 >> rw [FUN_EQ_THM]
QED

(* if the first N items of (g n) are all zero, we can shift them in suminf *)
Theorem ext_suminf_eq_shift :
    !f g N. (!n. n < N ==> g n = 0) /\ (!n. 0 <= f n /\ f n = g (n + N)) ==>
            (ext_suminf f = ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Know ‘!n. 0 <= g n’
 >- (Q.X_GEN_TAC ‘n’ \\
     Cases_on ‘n < N’ >- rw [] \\
    ‘n = n - N + N’ by rw [] >> POP_ORW \\
    ‘g (n - N + N) = f (n - N)’ by rw [] >> POP_ORW >> rw [])
 >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def, GSYM le_antisym]
 >| [ (* goal 1 (of 2): easy *)
      rw [sup_le', le_sup'] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘n + N’ \\
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ_SHIFT >> rw [],
      (* goal 1 (of 2): hard *)
      rw [sup_le', le_sup'] \\
      Cases_on ‘n < N’
      >- (Know ‘SIGMA g (count n) = 0’
          >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 >> rw []) >> Rewr' \\
          FIRST_X_ASSUM MATCH_MP_TAC \\
          Q.EXISTS_TAC ‘0’ >> rw [EXTREAL_SUM_IMAGE_EMPTY]) \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
     ‘n = n - N + N’ by rw [] >> POP_ORW \\
      Q.EXISTS_TAC ‘n - N’ \\
      ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ_SHIFT >> rw [] ]
QED

Theorem ext_suminf_sub :
    !f g. (!n. 0 <= g n /\ g n <= f n) /\ ext_suminf f <> PosInf ==>
          (ext_suminf (\i. f i - g i) = ext_suminf f - ext_suminf g)
Proof
    RW_TAC std_ss []
 >> `!n. 0 <= g n` by PROVE_TAC []
 >> `!n. 0 <= f n` by PROVE_TAC [le_trans]
 >> Know `ext_suminf g <= ext_suminf f`
 >- (RW_TAC std_ss [ext_suminf_def, sup_le', le_sup', IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `SIGMA f (count n)` \\
     RW_TAC std_ss []
     >- (MATCH_MP_TAC ((REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`)
                         EXTREAL_SUM_IMAGE_MONO) \\
         RW_TAC std_ss [IN_COUNT] \\
         DISJ1_TAC \\
         METIS_TAC [lt_infty, lte_trans, num_not_infty, le_trans]) \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> `ext_suminf g <> PosInf` by METIS_TAC [lt_infty,let_trans]
 >> `!n. f n <> PosInf` by METIS_TAC [ext_suminf_lt_infty,le_trans,lt_infty]
 >> `!n. g n <> PosInf` by METIS_TAC [ext_suminf_lt_infty,lt_infty]
 >> `!n. f n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty,le_trans]
 >> `!n. g n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
 >> `?p. !n. f n = Normal (p n)`
       by (Q.EXISTS_TAC `(\n. @r. f n = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `?q. !n. g n = Normal (q n)`
       by (Q.EXISTS_TAC `(\n. @r. g n = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `f = (\n. Normal (p n))` by METIS_TAC []
 >> `g = (\n. Normal (q n))` by METIS_TAC []
 >> FULL_SIMP_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_le_def,
                          extreal_not_infty, extreal_of_num_def]
 >> `!n. p n - q n <= p n`
       by METIS_TAC [REAL_LE_SUB_RADD, REAL_ADD_COMM, REAL_LE_ADDR]
 >> Know `ext_suminf (\i. Normal (p i - q i)) <> PosInf`
 >- (`!n. Normal (p n - q n) <= Normal (p n)` by METIS_TAC [extreal_le_def] \\
     Know `ext_suminf (\i. Normal (p i - q i)) <= ext_suminf (\n. Normal (p n))`
     >- (MATCH_MP_TAC ext_suminf_mono \\
         RW_TAC std_ss [extreal_le_eq, extreal_of_num_def] \\
         METIS_TAC [REAL_SUB_LE]) >> DISCH_TAC \\
     METIS_TAC [lt_infty, let_trans])
 >> `!n. 0 <= p n` by METIS_TAC [REAL_LE_TRANS]
 >> `!n. 0 <= p n - q n` by METIS_TAC [REAL_SUB_LE]
 >> RW_TAC std_ss [ext_suminf_suminf, extreal_sub_def]
 (* stage work *)
 >> Know `!n. 0 <= (\n. Normal (p n)) n`
 >- RW_TAC std_ss [extreal_of_num_def, extreal_le_eq]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def))
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `!n. 0 <= (\n. Normal (q n)) n`
 >- RW_TAC std_ss [extreal_of_num_def, extreal_le_eq]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def))
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `!n. 0 <= (\i. Normal (p i - q i)) n`
 >- RW_TAC std_ss [extreal_of_num_def, extreal_sub_def, extreal_le_eq]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def))
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> FULL_SIMP_TAC std_ss [sup_eq', le_infty, IN_IMAGE, IN_UNIV]
 >> Know `!n. SIGMA (\n. Normal (p n)) (count n) <= y`
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Know `!n. SIGMA (\n. Normal (q n)) (count n) <= y'`
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Know `!n. SIGMA (\n. Normal (p n - q n)) (count n) <= y''`
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!z. Q ==> (z <= y)`   K_TAC
 >> Q.PAT_X_ASSUM `!z. Q ==> (z <= y')`  K_TAC
 >> Q.PAT_X_ASSUM `!z. Q ==> (z <= y'')` K_TAC
 >> Q.PAT_X_ASSUM `sup a <= sup b`       K_TAC
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT]
 >> `0 <= y` by METIS_TAC [REAL_SUM_IMAGE_POS,FINITE_COUNT,extreal_le_def,
                            extreal_of_num_def,le_trans]
 >> `0 <= y'` by METIS_TAC [REAL_SUM_IMAGE_POS,FINITE_COUNT,extreal_le_def,
                             extreal_of_num_def,le_trans]
 >> `0 <= SIGMA (\n. p n - q n) (count n)`
       by (MATCH_MP_TAC REAL_SUM_IMAGE_POS
           >> RW_TAC std_ss [FINITE_COUNT])
 >> `0 <= y''` by METIS_TAC [extreal_le_def,extreal_of_num_def,le_trans]
 >> `y <> NegInf /\ y' <> NegInf /\ y'' <> NegInf`
       by METIS_TAC [lt_infty,num_not_infty,lte_trans]
 >> `?z. y = Normal z` by METIS_TAC [extreal_cases]
 >> `?z'. y' = Normal z'` by METIS_TAC [extreal_cases]
 >> `?z''. y'' = Normal z''` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_le_def, extreal_not_infty]
 >> RW_TAC std_ss [suminf, sums]
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >- (RW_TAC std_ss [GSYM convergent]
      >> MATCH_MP_TAC SEQ_ICONV
      >> RW_TAC std_ss [GREATER_EQ,real_ge]
      >- (MATCH_MP_TAC SEQ_BOUNDED_2
          >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
          >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `z''`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
          >> RW_TAC std_ss [FINITE_COUNT])
      >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      >> DECIDE_TAC)
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >- (RW_TAC std_ss [GSYM convergent]
      >> MATCH_MP_TAC SEQ_ICONV
      >> RW_TAC std_ss [GREATER_EQ,real_ge]
      >- (MATCH_MP_TAC SEQ_BOUNDED_2
          >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
          >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `z`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
          >> RW_TAC std_ss [FINITE_COUNT])
      >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      >> DECIDE_TAC)
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >- (RW_TAC std_ss [GSYM convergent]
      >> MATCH_MP_TAC SEQ_ICONV
      >> RW_TAC std_ss [GREATER_EQ,real_ge]
      >- (MATCH_MP_TAC SEQ_BOUNDED_2
          >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
          >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `z'`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
          >> RW_TAC std_ss [FINITE_COUNT])
      >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      >> DECIDE_TAC)
 >> Suff `(\n. sum (0,n) (\i. p i - q i)) --> (x' - x'')` >- METIS_TAC [SEQ_UNIQ]
 >> FULL_SIMP_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
 >> `(\n. SIGMA (\i. p i - q i) (count n)) =
     (\n. (\n. SIGMA p (count n)) n - (\n.  SIGMA q (count n)) n)`
        by (RW_TAC std_ss [FUN_EQ_THM,real_sub]
            >> `-SIGMA q (count n') = SIGMA (\x. - q x) (count n')`
                by METIS_TAC [REAL_NEG_MINUS1,REAL_SUM_IMAGE_CMUL,FINITE_COUNT]
            >> RW_TAC std_ss [REAL_SUM_IMAGE_ADD,FINITE_COUNT])
 >> POP_ORW
 >> MATCH_MP_TAC SEQ_SUB
 >> RW_TAC std_ss []
QED

Theorem ext_suminf_sum :
    !f n. (!n. 0 <= f n) /\ (!m. n <= m ==> (f m = 0)) ==>
          (ext_suminf f = SIGMA f (count n))
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [ext_suminf_def, sup_eq', IN_IMAGE, IN_UNIV]
 >- (Cases_on `n' <= n`
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
         RW_TAC real_ss [SUBSET_DEF, IN_COUNT, FINITE_COUNT])
     >> `count n SUBSET (count n')` by METIS_TAC [IN_COUNT,NOT_LESS_EQUAL,SUBSET_DEF,LESS_TRANS]
     >> `count n' = (count n) UNION (count n' DIFF (count n))` by METIS_TAC [UNION_DIFF]
     >> POP_ORW
     >> `DISJOINT (count n) (count n' DIFF count n)` by METIS_TAC [DISJOINT_DIFF]
     >> `!n. f n <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lte_trans]
     >> RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_DISJOINT_UNION]
     >> `FINITE (count n' DIFF count n)` by METIS_TAC [FINITE_COUNT,FINITE_DIFF]
     >> (MP_TAC o (REWRITE_RULE [FINITE_COUNT]) o
         (Q.ISPECL [`count n`, `count n' DIFF count n`])) EXTREAL_SUM_IMAGE_DISJOINT_UNION
     >> RW_TAC std_ss []
     >> POP_ASSUM (MP_TAC o Q.SPEC `f`)
     >> RW_TAC std_ss []
     >> Suff `SIGMA f (count n' DIFF count n) = 0`
     >- RW_TAC std_ss [add_rzero,le_refl]
     >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
     >> RW_TAC std_ss [IN_COUNT,IN_DIFF]
     >> METIS_TAC [NOT_LESS])
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC []
QED

Overload suminf = ``ext_suminf``

Theorem ext_suminf_zero:   !f. (!n. f n = 0) ==> (ext_suminf f = 0)
Proof
    rpt STRIP_TAC
 >> ASSUME_TAC (Q.SPECL [`f`, `0`] ext_suminf_sum)
 >> `0 = SIGMA f (count 0)` by PROVE_TAC [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap)
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [le_refl]
QED

(* |- suminf (\n. 0) = 0 *)
Theorem ext_suminf_0 = SIMP_RULE std_ss [] (Q.SPEC `\n. 0` ext_suminf_zero);

Theorem ext_suminf_pos :
    !f. (!n. 0 <= f n) ==> (0 <= ext_suminf f)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE [ext_suminf_0]
                               (Q.SPECL [`f`, `\n. 0`] ext_suminf_mono))
 >> rw [le_refl]
QED

Theorem ext_suminf_sing:
    !r. 0 <= r ==> (ext_suminf (\n. if n = 0 then r else 0) = r)
Proof
    GEN_TAC >> STRIP_TAC
 >> Q.ABBREV_TAC `f = (\n :num. if n = 0 then r else 0)`
 >> Suff `ext_suminf f = SIGMA f (count 1)`
 >- (Rewr >> REWRITE_TAC [ONE, COUNT_SUC, COUNT_ZERO] \\
     REWRITE_TAC [EXTREAL_SUM_IMAGE_SING] \\
     Q.UNABBREV_TAC `f` >> SIMP_TAC std_ss [])
 >> MATCH_MP_TAC ext_suminf_sum
 >> Q.UNABBREV_TAC `f`
 >> SIMP_TAC arith_ss []
 >> METIS_TAC [le_refl]
QED

(* finite version of ext_suminf_add *)
Theorem ext_suminf_sigma :
    !f n. (!i x. i < n ==> 0 <= f i x) ==>
          (SIGMA (ext_suminf o f) (count n) = ext_suminf (\x. SIGMA (\i. f i x) (count n)))
Proof
    REWRITE_TAC [o_DEF]
 >> GEN_TAC >> Induct_on `n`
 >- (DISCH_TAC >> REWRITE_TAC [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY] \\
     MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_zero \\
     BETA_TAC >> REWRITE_TAC [])
 >> RW_TAC std_ss [COUNT_SUC]
 >> Know `SIGMA (\i. suminf (f i)) (n INSERT count n) =
          (\i. suminf (f i)) n + SIGMA (\i. suminf (f i)) (count n DELETE n)`
 >- (irule EXTREAL_SUM_IMAGE_PROPERTY \\
     REWRITE_TAC [FINITE_COUNT, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> BETA_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC ext_suminf_pos \\
     GEN_TAC >> POP_ASSUM STRIP_ASSUME_TAC \\ (* 2 subgoals, same tactics *)
    `x < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> Rewr' >> BETA_TAC >> REWRITE_TAC [COUNT_DELETE]
 >> Know `!i x. i < n ==> 0 <= f i x`
 >- (rpt STRIP_TAC >> `i < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> DISCH_TAC >> RES_TAC >> POP_ORW
 >> Q.PAT_X_ASSUM `X ==> Y` K_TAC
 >> Know `!x. SIGMA (\i. f i x) (n INSERT count n) =
              (\i. f i x) n + SIGMA (\i. f i x) (count n DELETE n)`
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_PROPERTY \\
     REWRITE_TAC [FINITE_COUNT, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> BETA_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     POP_ASSUM STRIP_ASSUME_TAC \\ (* 2 subgoals, same tactics *)
    `x' < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> Rewr' >> BETA_TAC >> REWRITE_TAC [COUNT_DELETE]
 >> `suminf (\x. f n x + SIGMA (\i. f i x) (count n)) =
     suminf (\x. (f n) x + (\y. SIGMA (\i. f i y) (count n)) x)` by PROVE_TAC []
 >> POP_ORW
 >> Suff `suminf (\x. f n x + (\y. SIGMA (\i. f i y) (count n)) x) =
          suminf (f n) + suminf (\x. SIGMA (\i. f i x) (count n))` >- Rewr
 >> MATCH_MP_TAC ext_suminf_add >> GEN_TAC >> BETA_TAC
 >> CONJ_TAC >- (`n < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT]
QED

(* |- !f n.
         (!i x. i < n ==> 0 <= f i x) ==>
         (SIGMA (\x. suminf (f x)) (count n) =
          suminf (\x. SIGMA (\i. f i x) (count n))) *)
Theorem ext_suminf_sigma' = REWRITE_RULE [o_DEF] ext_suminf_sigma;

Theorem lemma[local]:
    !f n'. (!i. (!m n. m <= n ==> (\x. f x i) m <= (\x. f x i) n)) /\
        (!n i. 0 <= f n i) ==>
        (SIGMA (\i. sup {f k i | k IN univ(:num)}) (count n') =
         sup {SIGMA (\i. f k i) (count n') | k IN UNIV})
Proof
  RW_TAC std_ss [] THEN Q.ABBREV_TAC `s = count n'` THEN
  `FINITE s` by METIS_TAC [FINITE_COUNT] THEN POP_ASSUM MP_TAC THEN
  Q.SPEC_TAC (`s`,`s`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IN_UNIV] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{0 | k | T} = {0}``] THEN
   SIMP_TAC std_ss [sup_sing],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `sup {SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e} | k IN univ(:num)} =
   sup {SIGMA (\i. f k i) s' | k IN univ(:num)} +
   sup {SIGMA (\i. f k i) {e} | k IN univ(:num)}` THENL
  [ALL_TAC,
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   ONCE_REWRITE_TAC [METIS [] ``SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e} =
     (\k. SIGMA (\i. f k i) s') k + (\k. SIGMA (\i. f k i) {e}) k``] THEN
   MATCH_MP_TAC sup_add_mono THEN RW_TAC std_ss [] THENL
   [MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN ASM_SIMP_TAC std_ss [],
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_MONO) THEN
    RW_TAC std_ss [] THEN DISJ1_TAC THEN GEN_TAC THEN
    SIMP_TAC std_ss [lt_infty] THEN DISCH_TAC THEN
    METIS_TAC [lte_trans, num_not_infty, lt_infty],
    ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING],
    ALL_TAC] THEN
   RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]] THEN
  DISCH_TAC THEN `FINITE {e}` by SIMP_TAC std_ss [FINITE_SING] THEN
  `DISJOINT s' {e}` by ASM_SET_TAC [] THEN
  `!k.
   (!x. x IN (s' UNION {e}) ==> (\i. f k i) x <> NegInf) \/
   (!x. x IN (s' UNION {e}) ==> (\i. f k i) x <> PosInf) ==>
   (SIGMA (\i. f k i) (s' UNION {e}) = SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e})` by
   METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION] THEN
  Q_TAC SUFF_TAC `!k. (SIGMA (\i. f k i) (s' UNION {e}) =
       SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e})` THENL
  [ALL_TAC,
   GEN_TAC THEN POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
   RW_TAC std_ss [lt_infty] THEN METIS_TAC [lte_trans, num_not_infty, lt_infty]] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC [SET_RULE ``e INSERT s' = s' UNION {e}``] THEN
  ASM_REWRITE_TAC [] THEN
  `(!x. x IN s' UNION {e} ==> (\i. sup {f k i | k IN univ(:num)}) x <> NegInf) \/
   (!x. x IN s' UNION {e} ==> (\i. sup {f k i | k IN univ(:num)}) x <> PosInf) ==>
   (SIGMA (\i. sup {f k i | k IN univ(:num)}) (s' UNION {e}) =
    SIGMA (\i. sup {f k i | k IN univ(:num)}) s' + SIGMA (\i. sup {f k i | k IN univ(:num)}) {e})`
   by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN ASM_SIMP_TAC std_ss []) THEN
  Q_TAC SUFF_TAC `(SIGMA (\i. sup {f k i | k IN univ(:num)}) (s' UNION {e}) =
        SIGMA (\i. sup {f k i | k IN univ(:num)}) s' +
        SIGMA (\i. sup {f k i | k IN univ(:num)}) {e})` THENL
  [ALL_TAC,
   POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN RW_TAC std_ss [sup_eq] THEN
   DISJ1_TAC THEN Q.EXISTS_TAC `f k x` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
   METIS_TAC [lte_trans, num_not_infty, lt_infty]]
 >> Rewr'
 >> ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING]
QED

Theorem ext_suminf_sup_eq : (* was: suminf_SUP_eq *)
   !(f:num->num->extreal).
     (!i m n. m <= n ==> f m i <= f n i) /\
     (!n i. 0 <= f n i) ==>
     (suminf (\i. sup {f n i | n IN UNIV}) = sup {suminf (\i. f n i) | n IN UNIV})
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\i. sup {f n i | n IN UNIV}) n`
 >- (RW_TAC set_ss [IN_UNIV, le_sup'] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `f 0 n` >> rw [] \\
     POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `0` >> rw [])
 >> RW_TAC std_ss [ext_suminf_def, IMAGE_DEF]
 >> Suff `!n. SIGMA (\i. sup {f k i | k IN UNIV}) (count n) =
              sup {SIGMA (\i. f k i) (count n) | k IN UNIV}`
 >- (DISCH_TAC \\
     Know `sup {SIGMA (\i. sup {f n i | n IN UNIV}) (count n) | n IN UNIV} =
           sup {sup {SIGMA (\i. f k i) (count n) | k IN UNIV} | n IN UNIV}`
     >- (AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN METIS_TAC []) >> Rewr' \\
     Know
    `sup {sup {(\k n. SIGMA (\i. f k i) (count n)) k n | k IN UNIV} | n IN UNIV} =
     sup {sup {(\k n. SIGMA (\i. f k i) (count n)) k n | n IN UNIV} | k IN UNIV}`
     >- (Q.ABBREV_TAC `g = (\k n. SIGMA (\i. f k i) (count n))` \\
         SIMP_TAC std_ss [sup_comm]) \\
     METIS_TAC [])
 >> ASM_SIMP_TAC std_ss [lemma]
QED

(* ------------------------------------------------------------------------- *)
(*  Further theorems concerning the relationship of suminf and SIGMA         *)
(*  Used by the new measureTheory. (Chun Tian)                               *)
(* ------------------------------------------------------------------------- *)

(* The extreal version of POS_SUMMABLE (util_probTheory) *)
Theorem pos_summable :
    !f. (!n. 0 <= f n) /\ (?r. !n. SIGMA f (count n) <= Normal r) ==>
        suminf f < PosInf
Proof
    GEN_TAC >> STRIP_TAC
 (* 1. f is a normal extreal function *)
 >> Know `!n. f n <> PosInf`
 >- (CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `!n. SIGMA f (count n) <= Normal r`
       (MP_TAC o (REWRITE_RULE [COUNT_SUC]) o (Q.SPEC `SUC n`)) \\
    `FINITE (count n)` by PROVE_TAC [FINITE_COUNT] \\
    `!x. x IN (n INSERT (count n)) ==> f x <> NegInf` by PROVE_TAC [le_not_infty] \\
     ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, GSYM extreal_lt_def] \\
     Suff `SIGMA f (count n DELETE n) <> NegInf`
     >- RW_TAC std_ss [add_infty, lt_infty] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     CONJ_TAC >- PROVE_TAC [FINITE_DELETE] \\
     rpt STRIP_TAC >> PROVE_TAC [le_not_infty])
 >> DISCH_TAC
 (* 2. g is the real version of f, and `!n. 0 <= g n` *)
 >> Q.ABBREV_TAC `g = real o f`
 >> Know `f = \x. Normal (g x)`
 >- (Q.UNABBREV_TAC `g` >> REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
     REWRITE_TAC [o_DEF] >> BETA_TAC \\
    `!n. f n <> NegInf` by PROVE_TAC [pos_not_neginf] \\
     METIS_TAC [normal_real]) >> DISCH_TAC
 >> Know `!n. 0 <= g n`
 >- (Q.UNABBREV_TAC `g` >> REWRITE_TAC [o_DEF] >> BETA_TAC \\
     POP_ASSUM K_TAC \\ (* useless *)
     GEN_TAC >> `0 <= f n /\ f n <> PosInf` by PROVE_TAC [] \\
     Q.ABBREV_TAC `h = f n` \\
     Cases_on `h` >|
     [ REWRITE_TAC [REAL_LE_REFL, extreal_not_infty, real_def],
       REWRITE_TAC [REAL_LE_REFL, extreal_not_infty, real_def],
       REWRITE_TAC [real_normal] \\
       METIS_TAC [extreal_of_num_def, extreal_le_def] ]) >> DISCH_TAC
 (* 3. g is summable, using POS_SUMMABLE *)
 >> Know `summable g`
 >- (MATCH_MP_TAC POS_SUMMABLE >> art [] \\
     Q.PAT_X_ASSUM `f = \x. Normal (g x)` SUBST_ALL_TAC \\
     REWRITE_TAC [REAL_SUM_IMAGE_EQ_sum] \\
     Q.EXISTS_TAC `r` >> GEN_TAC \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     METIS_TAC [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT])
 (* stage work *)
 >> RW_TAC std_ss [summable, sums, REAL_SUM_IMAGE_EQ_sum]
 >> Q.PAT_X_ASSUM `!n. 0 <= (\x. Normal (g x)) n`
      (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))
 (* 4. `\n. SIGMA g (count n)` is mono_increasing (for sup_seq) *)
 >> Know `mono_increasing (\n. SIGMA g (count n))`
 >- (REWRITE_TAC [mono_increasing_suc] >> BETA_TAC >> GEN_TAC \\
     MATCH_MP_TAC REAL_SUM_IMAGE_MONO_SET \\
     CONJ_TAC >- PROVE_TAC [FINITE_COUNT] \\
     CONJ_TAC >- PROVE_TAC [FINITE_COUNT] \\
     CONJ_TAC >- ( REWRITE_TAC [SUBSET_DEF, IN_COUNT] >> RW_TAC arith_ss [] ) \\
     rpt STRIP_TAC >> ASM_REWRITE_TAC [])
 >> DISCH_THEN (MP_TAC o (Q.SPEC `s`) o (MATCH_MP sup_seq))
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 (* 5. now swap Normal and SIGMA *)
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT, lt_infty]
QED

(* the lemma is non-trivial because it depends on "pos_summable" *)
Theorem summable_ext_suminf:
    !f. (!n. 0 <= f n) /\ summable f ==> suminf (Normal o f) < PosInf
Proof
    REWRITE_TAC [o_DEF]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC pos_summable
 >> BETA_TAC
 >> CONJ_TAC >- ASM_REWRITE_TAC [extreal_le_eq, extreal_of_num_def]
 >> Q.EXISTS_TAC `suminf f`
 (* !n. SIGMA (\n. Normal (f n)) (count n) <= Normal (suminf f) *)
 >> GEN_TAC
 >> Know `SIGMA (\n. Normal (f n)) (count n) = Normal (SIGMA f (count n))`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> METIS_TAC [FINITE_COUNT])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> REWRITE_TAC [extreal_le_eq]
 (* SIGMA f (count n) <= suminf f *)
 >> REWRITE_TAC [REAL_SUM_IMAGE_COUNT]
 >> MATCH_MP_TAC SER_POS_LE
 >> METIS_TAC []
QED

Theorem summable_ext_suminf_suminf:
    !f. (!n. 0 <= f n) /\ summable f ==> (suminf (Normal o f) = Normal (suminf f))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ext_suminf_suminf'
 >> ASM_REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC summable_ext_suminf
 >> ASM_REWRITE_TAC []
QED

(* added `(!n. 0 <= f n)`, otherwise not true *)
Theorem EXTREAL_SUM_IMAGE_le_suminf :
    !f n. (!n. 0 <= f n) ==> SIGMA f (count n) <= ext_suminf f
Proof
    rpt STRIP_TAC
 >> ASM_SIMP_TAC std_ss [ext_suminf_def]
 >> MATCH_MP_TAC le_sup_imp'
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC []
QED

Theorem ext_suminf_summable :
    !g. (!n. 0 <= g n) /\ suminf g < PosInf ==> summable (real o g)
Proof
    rpt STRIP_TAC
 >> Know `!n. g n < PosInf`
 >- (MATCH_MP_TAC ext_suminf_lt_infty \\
     METIS_TAC [lt_infty]) >> DISCH_TAC
 >> Q.ABBREV_TAC `f = real o g`
 >> Know `g = \n. Normal (f n)`
 >- (RW_TAC std_ss [FUN_EQ_THM] \\
     Q.UNABBREV_TAC `f` >> RW_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC normal_real \\
     METIS_TAC [lt_infty, pos_not_neginf]) >> DISCH_TAC
 >> MATCH_MP_TAC POS_SUMMABLE
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC `f` >> GEN_TAC >> RW_TAC std_ss [o_DEF] \\
     REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
     Know `Normal (real (g n)) = g n`
     >- (MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf]) \\
     DISCH_THEN (REWRITE_TAC o wrap) >> ASM_REWRITE_TAC [])
 >> Q.EXISTS_TAC `real (suminf g)`
 >> GEN_TAC >> REWRITE_TAC [GSYM REAL_SUM_IMAGE_COUNT]
 >> REWRITE_TAC [GSYM extreal_le_eq]
 >> `0 <= suminf g` by PROVE_TAC [ext_suminf_pos]
 >> Know `Normal (real (suminf g)) = suminf g`
 >- (MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 (* Normal (SIGMA f (count n)) <= suminf g *)
 >> Know `Normal (SIGMA f (count n)) = SIGMA (\n. Normal (f n)) (count n)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> PROVE_TAC [FINITE_COUNT])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> Q.PAT_X_ASSUM `g = (\n. Normal (f n))` (REWRITE_TAC o wrap o SYM)
 (* SIGMA g (count n) <= suminf g *)
 >> ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_le_suminf]
QED

Theorem ext_suminf_real_suminf:
    !g. (!n. 0 <= g n) /\ suminf g < PosInf ==> (suminf (real o g) = real (suminf g))
Proof
    rpt STRIP_TAC
 >> Know `!n. g n < PosInf`
 >- (MATCH_MP_TAC ext_suminf_lt_infty \\
     METIS_TAC [lt_infty])
 >> DISCH_TAC
 >> Know `!n. Normal (real (g n)) = g n`
 >- (GEN_TAC >> MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf])
 >> DISCH_TAC
 >> `summable (real o g)` by PROVE_TAC [ext_suminf_summable]
 >> REWRITE_TAC [GSYM extreal_11]
 >> `0 <= suminf g` by PROVE_TAC [ext_suminf_pos]
 >> Know `Normal (real (suminf g)) = suminf g`
 >- (MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> Know `Normal (suminf (real o g)) = suminf (\n. Normal ((real o g) n))`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_suminf \\
     RW_TAC std_ss [o_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
       ASM_REWRITE_TAC [],
       (* goal 2 (of 2) *)
       METIS_TAC [lt_infty] ])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> ASM_SIMP_TAC std_ss [o_DEF]
 >> REWRITE_TAC [ETA_AX]
QED

Theorem SUMINF_2D_suminf[local]:
    !(f :num -> num -> real) (g :num -> real) (h :num -> num # num).
       (!m n. 0 <= f m n) /\ (!n. summable (f n) /\ (suminf (f n) = g n)) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       (suminf (UNCURRY f o h) = suminf g)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC SUM_UNIQ
 >> MATCH_MP_TAC SUMINF_2D
 >> ASM_REWRITE_TAC []
 >> GEN_TAC
 >> `summable (f n)` by METIS_TAC []
 >> METIS_TAC [SUMMABLE_SUM]
QED

Theorem SUMINF_2D_summable[local]:
    !(f :num -> num -> real) (g :num -> real) (h :num -> num # num).
       (!m n. 0 <= f m n) /\ (!n. summable (f n) /\ (suminf (f n) = g n)) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       summable (UNCURRY f o h)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [summable]
 >> Q.EXISTS_TAC `suminf g`
 >> MATCH_MP_TAC SUMINF_2D
 >> ASM_REWRITE_TAC []
 >> GEN_TAC
 >> Suff `f n sums suminf (f n)` >- METIS_TAC []
 >> MATCH_MP_TAC SUMMABLE_SUM
 >> ASM_REWRITE_TAC []
QED

(* extreal version of SUMINF_2D, based on SUMINF_2D_suminf and SUMINF_2D_summable,
   c.f. ext_suminf_2d_infinite (more general, proved from scratch)
 *)
Theorem ext_suminf_2d :
    !(f :num -> num -> extreal) (g :num -> extreal) (h :num -> num # num).
      (!m n. 0 <= f m n) /\
      (!n. ext_suminf (f n) = g n) /\  (* f n sums g n *)
      (ext_suminf g < PosInf) /\       (* summable g *)
      BIJ h UNIV (UNIV CROSS UNIV)
     ==>
      (ext_suminf (UNCURRY f o h) = ext_suminf g)
Proof
 (* general properties of g and f *)
    rpt STRIP_TAC
 >> `!n. 0 <= g n` by PROVE_TAC [ext_suminf_pos]
 >> `!n. g n < PosInf` by PROVE_TAC [ext_suminf_lt_infty]
 >> `!n. g n <> PosInf /\ g n <> NegInf` by PROVE_TAC [GSYM lt_infty, pos_not_neginf]
 >> `!x. 0 <= UNCURRY f x` by METIS_TAC [UNCURRY]
 >> Know `!m n. f m n < PosInf`
 >- (GEN_TAC >> MATCH_MP_TAC ext_suminf_lt_infty \\
     CONJ_TAC >- ASM_REWRITE_TAC [] \\
     METIS_TAC [lt_infty]) >> DISCH_TAC
 >> `!m n. f m n <> PosInf /\ f m n <> NegInf`
        by PROVE_TAC [GSYM lt_infty, pos_not_neginf]
 (* properties of `UNCURRY f` *)
 >> `!x. UNCURRY f x < PosInf` by METIS_TAC [UNCURRY]
 >> `!x. UNCURRY f x <> PosInf /\ UNCURRY f x <> NegInf`
        by PROVE_TAC [GSYM lt_infty, pos_not_neginf]
 (* convert g into real function g' *)
 >> Q.ABBREV_TAC `g' = real o g`
 >> Know `g = \x. Normal (g' x)`
 >- (Q.UNABBREV_TAC `g'` >> REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
     REWRITE_TAC [o_DEF] >> BETA_TAC \\
     METIS_TAC [normal_real])
 >> DISCH_TAC
 >> ASM_REWRITE_TAC []
 (* properties of g' *)
 >> Know `summable g'`
 >- (Q.UNABBREV_TAC `g'` \\
     MATCH_MP_TAC ext_suminf_summable >> ASM_REWRITE_TAC [])
 >> DISCH_TAC
 (* RHS reduce of the goal *)
 >> Know `suminf (\x. Normal (g' x)) = Normal (suminf g')`
 >- (MATCH_MP_TAC ext_suminf_suminf \\
     reverse CONJ_TAC >- fs [GSYM lt_infty] \\
     Q.UNABBREV_TAC `g'` >> REWRITE_TAC [o_DEF] >> BETA_TAC \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     GEN_TAC >> REWRITE_TAC [GSYM extreal_of_num_def] \\
     METIS_TAC [normal_real])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 (* convert f into real function f' *)
 >> Q.ABBREV_TAC `(f' :num -> num -> real) = (\n. real o f n)`
 >> Know `f = (\n. Normal o f' n)`
 >- (Q.UNABBREV_TAC `f'` >> REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
     REWRITE_TAC [o_DEF] >> BETA_TAC \\
     METIS_TAC [normal_real]) >> DISCH_TAC
 >> `!m n. Normal (f' m n) = f m n` by METIS_TAC [o_DEF]
 (* properties of f' *)
 >> Know `!m n. 0 <= f' m n`
 >- (NTAC 2 GEN_TAC \\
     REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
     METIS_TAC []) >> DISCH_TAC
 >> Know `!n. summable (f' n)`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f'` >> BETA_TAC \\
     MATCH_MP_TAC ext_suminf_summable >> METIS_TAC []) >> DISCH_TAC
 >> Know `!n. suminf (f' n) = g' n`
 >- (GEN_TAC >> REWRITE_TAC [GSYM extreal_11] \\
     Q.PAT_X_ASSUM `g = X`
        (REWRITE_TAC o wrap o (SIMP_RULE std_ss [FUN_EQ_THM]) o (MATCH_MP EQ_SYM)) \\
     Know `Normal (suminf (f' n)) = suminf (\m. Normal ((f' n) m))`
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_suminf \\
         ASM_REWRITE_TAC [] >> BETA_TAC >> METIS_TAC [o_DEF]) >> Rewr \\
     Q.PAT_X_ASSUM `!m n. Normal (f' m n) = f m n` (REWRITE_TAC o wrap) \\
     METIS_TAC []) >> DISCH_TAC
 (* applying SUMINF_2D_summable *)
 >> Know `summable (UNCURRY f' o h)`
 >- (MATCH_MP_TAC SUMINF_2D_summable \\
     Q.EXISTS_TAC `g'` >> ASM_REWRITE_TAC []) >> DISCH_TAC
 >> `!n. 0 <= (UNCURRY f' o h) n` by RW_TAC std_ss [o_DEF, UNCURRY]
 >> Know `UNCURRY f o h = Normal o (UNCURRY f' o h)`
 >- (ASM_REWRITE_TAC [] \\
     PURE_ONCE_REWRITE_TAC [o_DEF] \\
     PURE_ONCE_REWRITE_TAC [UNCURRY] \\
     REWRITE_TAC [o_DEF, UNCURRY] \\
     METIS_TAC []) >> DISCH_TAC
 (* using summable_ext_suminf, indirectly uses "pos_summable"! *)
 >> Know `suminf (UNCURRY f o h) < PosInf`
 >- (ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC summable_ext_suminf >> ASM_REWRITE_TAC []) >> DISCH_TAC
 >> ASM_REWRITE_TAC []
 (* LHS reduce of the goal *)
 >> Know `suminf (Normal o UNCURRY f' o h) = Normal (suminf (UNCURRY f' o h))`
 >- (MATCH_MP_TAC ext_suminf_suminf' \\
     ASM_REWRITE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM `UNCURRY f o h = Normal o UNCURRY f' o h`
        (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     ASM_REWRITE_TAC []) >> Rewr
 (* remove outer `Normal`s from LHS and RHS *)
 >> REWRITE_TAC [extreal_11]
 (* finally, apply SUMINF_2D_suminf, with all assumptions already proved. *)
 >> MATCH_MP_TAC SUMINF_2D_suminf >> art []
QED

(* some local facts of extreals needed by CARATHEODORY_SEMIRING *)
Theorem lt_inf_epsilon_set:
    !P e. 0 < e /\ (?x. x IN P /\ x <> PosInf) /\ inf P <> NegInf ==>
          ?x. x IN P /\ x < inf P + e
Proof
    METIS_TAC [IN_APP, lt_inf_epsilon]
QED

Theorem le_inf_epsilon_set:
    !P e. 0 < e /\ (?x. x IN P /\ x <> PosInf) /\ inf P <> NegInf ==>
          ?x. x IN P /\ x <= inf P + e
Proof
    rpt STRIP_TAC
 >> `?x. x IN P /\ x < inf P + e` by PROVE_TAC [lt_inf_epsilon_set]
 >> Q.EXISTS_TAC `x'` >> ASM_REWRITE_TAC []
 >> PROVE_TAC [lt_le]
QED

Theorem pow_half_pos_lt:   !n. 0  < (1 / 2) pow (n + 1)
Proof
    MATCH_MP_TAC pow_pos_lt >> PROVE_TAC [half_between]
QED

Theorem pow_half_pos_le :
    !n. 0 <= (1 / 2) pow n
Proof
    Cases_on ‘n’ >- REWRITE_TAC [pow_0, le_01]
 >> REWRITE_TAC [ADD1]
 >> MATCH_MP_TAC pow_pos_le
 >> REWRITE_TAC [half_between]
QED

Theorem ext_suminf_eq_infty_imp :
    !f. (!n. 0 <= f n) /\ (ext_suminf f = PosInf) ==>
        !e. e < PosInf ==> ?n. e <= SIGMA f (count n)
Proof
    rpt STRIP_TAC
 >> `!n. SIGMA f (count n) = (\n. SIGMA f (count n)) n` by PROVE_TAC []
 >> POP_ORW >> MATCH_MP_TAC sup_le_mono
 >> BETA_TAC >> reverse CONJ_TAC
 >- ASM_SIMP_TAC std_ss [GSYM ext_suminf_def]
 >> GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
 >> fs [FINITE_COUNT, COUNT_SUC]
QED

(* the other direction *)
Theorem ext_suminf_eq_infty :
    !f. (!n. 0 <= f n) /\ (!e. e < PosInf ==> ?n. e <= SIGMA f (count n)) ==>
        (ext_suminf f = PosInf)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [GSYM le_infty]
 >> Suff `sup (\x. ?n : num. x = & n) <= suminf f` >- PROVE_TAC [sup_num]
 >> ASM_SIMP_TAC std_ss [ext_suminf_def]
 >> MATCH_MP_TAC sup_le_sup_imp'
 >> SIMP_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> RW_TAC std_ss [IN_APP]
 >> `&n < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def]
 >> RES_TAC
 >> Q.EXISTS_TAC `SIGMA f (count n')` >> art []
 >> Q.EXISTS_TAC `n'` >> REWRITE_TAC []
QED

(* general version of `ext_suminf_2d` without ``ext_suminf g < PosInf`` *)
Theorem ext_suminf_2d_full :
    !(f :num -> num -> extreal) (g :num -> extreal) (h :num -> num # num).
       (!m n. 0 <= f m n) /\ (!n. ext_suminf (f n) = g n) /\
        BIJ h UNIV (UNIV CROSS UNIV) ==>
       (ext_suminf (UNCURRY f o h) = ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Cases_on `suminf g < PosInf`
 >- (MATCH_MP_TAC ext_suminf_2d >> art [])
 >> fs [GSYM lt_infty]
 >> Know `!n. 0 <= g n`
 >- (GEN_TAC \\
     Q.PAT_X_ASSUM `!n. X = g n` (REWRITE_TAC o wrap o GSYM) \\
     MATCH_MP_TAC ext_suminf_pos >> art []) >> DISCH_TAC
(* suminf (UNCURRY f o h) = PosInf *)
 >> Know `suminf g = sup (IMAGE
                           (\n. SIGMA (\i. SIGMA (f i) (count n)) (count n))
                           univ(:num))`
 >- (REWRITE_TAC [GSYM le_antisym] \\
     reverse CONJ_TAC >| (* easy goal first *)
     [ (* goal 1 (of 2) *)
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       Q.PAT_X_ASSUM `suminf g = PosInf` (ONCE_REWRITE_TAC o wrap o SYM) \\
       POP_ASSUM (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def)) \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `SIGMA g (count n)` \\
       reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                            Q.EXISTS_TAC `n` >> REWRITE_TAC []) \\
       irule EXTREAL_SUM_IMAGE_MONO \\
       SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
       CONJ_TAC >- (rpt STRIP_TAC \\
                    Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM) \\
                    ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_le_suminf]) \\
       DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> STRIP_TAC >|
       [ (* goal 1.1 (of 2) *)
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT],
         (* goal 1.2 (of 2) *)
         MATCH_MP_TAC pos_not_neginf \\
         Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM) \\
         MATCH_MP_TAC ext_suminf_pos >> art [] ],
       (* goal 2 (of 2) *)
       POP_ASSUM (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def)) \\
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
      `g = (\n. g n)` by METIS_TAC [] >> POP_ORW \\
       Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM) \\
       Know `SIGMA (\n. suminf (f n)) (count n) = suminf (\x. SIGMA (\i. f i x) (count n))`
       >- (MATCH_MP_TAC ext_suminf_sigma' >> PROVE_TAC []) >> Rewr' \\
       (* stage work *)
       Know `!j. 0 <= (\x. SIGMA (\i. f i x) (count n)) j`
       >- (RW_TAC std_ss [] \\
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
           RW_TAC std_ss [FINITE_COUNT]) \\
       DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))  \\
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       Know `SIGMA (\x. SIGMA (\i. f i x) (count n)) (count n') =
             SIGMA (\x. SIGMA (f x) (count n')) (count n)`
       >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC NESTED_EXTREAL_SUM_IMAGE_REVERSE \\
           REWRITE_TAC [FINITE_COUNT, IN_COUNT] \\
           rpt GEN_TAC >> STRIP_TAC >> MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr' \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC `SIGMA (\i. SIGMA (f i) (count (MAX n n'))) (count (MAX n n'))` \\
       reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                            Q.EXISTS_TAC `MAX n n'` >> REWRITE_TAC []) \\
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO \\
       RW_TAC arith_ss [] ])
 >> DISCH_TAC
 >> Know `!r. r < PosInf ==> ?n. r <= SIGMA (\i. SIGMA (f i) (count n)) (count n)`
 >- (rpt STRIP_TAC \\
    `!n. SIGMA (\i. SIGMA (f i) (count n)) (count n) =
         (\n. SIGMA (\i. SIGMA (f i) (count n)) (count n)) n` by PROVE_TAC [] >> POP_ORW \\
     MATCH_MP_TAC sup_le_mono >> BETA_TAC \\
     reverse CONJ_TAC >- PROVE_TAC [] \\
     GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO \\
     RW_TAC arith_ss [])
 >> DISCH_TAC
 >> MATCH_MP_TAC ext_suminf_eq_infty
 >> CONJ_TAC >- RW_TAC std_ss [o_DEF, UNCURRY]
 >> rpt STRIP_TAC
 >> RES_TAC
 >> STRIP_ASSUME_TAC (((Q.SPEC `n`) o (MATCH_MP NUM_2D_BIJ_SMALL_SQUARE))
                          (ASSUME ``BIJ h univ(:num) (univ(:num) CROSS univ(:num))``))
 >> Q.EXISTS_TAC `N`
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA (\i. SIGMA (f i) (count n)) (count n)` >> art []
 >> Know `SIGMA (\i. SIGMA (f i) (count n)) (count n) =
          SIGMA (\x. f (FST x) (SND x)) ((count n CROSS count n))`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     REWRITE_TAC [FINITE_COUNT] >> DISJ1_TAC \\
     GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr'
 >> Know `SIGMA (UNCURRY f o h) (count N) = SIGMA (UNCURRY f) (IMAGE h (count N))`
 >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_IMAGE \\
     SIMP_TAC std_ss [FINITE_COUNT, UNCURRY] \\
     CONJ_TAC >- (DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
                  MATCH_MP_TAC pos_not_neginf >> art []) \\
     MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `UNIV` \\
     RW_TAC std_ss [INJ_DEF, IN_COUNT, IN_UNIV] \\
     PROVE_TAC [BIJ_DEF, INJ_DEF, IN_UNIV]) >> Rewr'
 >> Know `UNCURRY f = (\x. f (FST x) (SND x))`
 >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC >> REWRITE_TAC [UNCURRY]) >> Rewr'
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> art []
 >> CONJ_TAC >- (MATCH_MP_TAC FINITE_CROSS >> REWRITE_TAC [FINITE_COUNT])
 >> CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT])
 >> GEN_TAC >> BETA_TAC >> DISCH_TAC >> art []
QED

Theorem harmonic_series_pow_2 :
    ext_suminf (\n. inv (&(SUC n) pow 2)) < PosInf
Proof
    Q.ABBREV_TAC `f :num -> real = \n. inv (&(SUC n) pow 2)`
 >> Suff `(\n. inv (&(SUC n) pow 2)) = Normal o f`
 >- (Rewr' >> MATCH_MP_TAC summable_ext_suminf \\
     rw [HARMONIC_SERIES_POW_2, Abbr `f`])
 >> RW_TAC real_ss [Abbr `f`, o_DEF, FUN_EQ_THM]
 >> Know `(0 :real) < &(SUC n) pow 2`
 >- (MATCH_MP_TAC REAL_POW_LT >> RW_TAC real_ss []) >> DISCH_TAC
 >> `&(SUC n) pow 2 <> (0 :real)` by PROVE_TAC [REAL_LT_IMP_NE]
 >> ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_inv_eq, extreal_pow_def]
QED

Theorem geometric_series_pow : (* cf. seqTheory.GP, seqTheory.GP_FINITE *)
    !x. 0 < x /\ x < 1 ==> ext_suminf (\n. x pow n) = inv (1 - x)
Proof
    rpt STRIP_TAC
 >> Know ‘?r. x = Normal r’
 >- (Suff ‘x <> PosInf /\ x <> NegInf’ >- METIS_TAC [extreal_cases] \\
     CONJ_TAC >> REWRITE_TAC [lt_infty] >> MATCH_MP_TAC lt_trans >| (* 2 subgoals *)
     [ Q.EXISTS_TAC ‘1’  >> rw [extreal_of_num_def],
       Q.EXISTS_TAC ‘0’ >> rw [extreal_of_num_def, lt_infty] ])
 >> STRIP_TAC
 >> POP_ASSUM
      (fn th => FULL_SIMP_TAC std_ss [th, extreal_of_num_def, extreal_lt_eq, extreal_sub_def,
                                      extreal_pow_def, extreal_11])
 >> Know ‘r <> 1’ >- (CCONTR_TAC >> fs [])
 >> DISCH_TAC
 >> ‘1 - r <> 0’ by rw []
 >> rw [extreal_inv_eq]
 >> Know ‘inv (1 - r) = suminf (\n. r pow n)’
 >- (MATCH_MP_TAC SUM_UNIQ \\
     MATCH_MP_TAC GP >> rw [ABS_BOUNDS_LT] \\
     MATCH_MP_TAC REAL_LT_TRANS \\
     Q.EXISTS_TAC ‘0’ >> rw [])
 >> Rewr'
 >> HO_MATCH_MP_TAC ext_suminf_suminf
 >> STRONG_CONJ_TAC
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC POW_POS \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘f = \n. Normal (r pow n)’
 >> Know ‘!n. 0 <= f n’
 >- (rw [Abbr ‘f’, extreal_of_num_def, extreal_le_eq])
 >> rw [lt_infty, ext_suminf_def, Abbr ‘f’]
 >> Know ‘!n. SIGMA (\n. Normal ((\n. r pow n) n)) (count n) =
              Normal (SIGMA (\n. r pow n) (count n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL \\
     REWRITE_TAC [FINITE_COUNT])
 >> BETA_TAC >> Rewr'
 >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_COUNT, GP_FINITE]
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘Normal ((0 - 1) / (r - 1))’
 >> rw [sup_le', lt_infty]
 (* stage work *)
 >> RW_TAC std_ss [extreal_le_eq, real_div]
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> Know ‘inv (r - 1) * (r pow n - 1) <= inv (r - 1) * -1 <=>
          -1 <= r pow n - 1 ’
 >- (MATCH_MP_TAC REAL_LE_LMUL_NEG \\
     rw [REAL_INV_LT0] \\
     Q.PAT_X_ASSUM ‘r < 1’ MP_TAC >> REAL_ARITH_TAC)
 >> Rewr'
 >> Suff ‘0 <= r pow n’ >- REAL_ARITH_TAC
 >> MATCH_MP_TAC POW_POS
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

Theorem pow_half_ser' : (* was: suminf_half_series_ereal *)
    ext_suminf (\n. (1 / 2) pow (SUC n)) = 1
Proof
    rw [extreal_pow]
 >> Know ‘suminf (\n. 1 / 2 * (1 / 2) pow n) =
          (1 / 2) * suminf (\n. (1 / 2) pow n)’
 >- (HO_MATCH_MP_TAC ext_suminf_cmul >> rw [half_between] \\
     MATCH_MP_TAC pow_pos_le >> rw [half_between])
 >> Rewr'
 >> Know ‘suminf (\n. (1 / 2) pow n) = inv (1 - 1 / 2)’
 >- (MATCH_MP_TAC geometric_series_pow \\
     rw [half_between])
 >> Rewr'
 >> RW_TAC real_ss [extreal_of_num_def, extreal_inv_eq, ne_02, extreal_mul_def,
                    extreal_div_eq, extreal_sub_def, REAL_MUL_RINV]
QED

Theorem pow_half_ser = REWRITE_RULE [ADD1] pow_half_ser'

Theorem pow_half_ser_by_e :
    !e. 0 < e /\ e <> PosInf ==> (e = ext_suminf (\n. e * ((1 / 2) pow (n + 1))))
Proof
    rpt STRIP_TAC
 >> Cases_on `e` >> fs [lt_infty]
 >> `(\n. Normal r * (1 / 2) pow (n + 1)) = (\n. Normal r * (\n. (1 / 2) pow (n + 1)) n)`
        by METIS_TAC []
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> Suff `suminf (\n. Normal r * (\n. (1 / 2) pow (n + 1)) n) =
                      Normal r * suminf (\n. (1 / 2) pow (n + 1))`
 >- (DISCH_THEN (REWRITE_TAC o wrap) \\
     REWRITE_TAC [pow_half_ser, mul_rone])
 >> MATCH_MP_TAC ext_suminf_cmul_alt
 >> CONJ_TAC
 >- (MATCH_MP_TAC REAL_LT_IMP_LE \\
     PROVE_TAC [extreal_lt_eq, extreal_of_num_def])
 >> BETA_TAC
 >> CONJ_TAC >- (MATCH_MP_TAC pow_pos_le \\
                 PROVE_TAC [half_between])
 >> GEN_TAC
 >> METIS_TAC [half_not_infty, pow_not_infty, lt_infty]
QED

Theorem ext_suminf_offset :
    !f m. (!n. 0 <= f n) ==>
           suminf f = SIGMA f (count m) + suminf (\i. f (i + m))
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘f1 = \n. if n < m then f n else 0’
 >> Q.ABBREV_TAC ‘f2 = \n. if m <= n then f n else 0’
 >> Know ‘SIGMA f (count m) = SIGMA f1 (count m)’
 >- (irule EXTREAL_SUM_IMAGE_EQ >> rw [Abbr ‘f1’] \\
     DISJ1_TAC >> rw [pos_not_neginf])
 >> Rewr'
 (* applying ext_suminf_sum *)
 >> Know ‘SIGMA f1 (count m) = suminf f1’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC ext_suminf_sum >> rw [Abbr ‘f1’])
 >> Rewr'
 (* applying ext_suminf_eq_shift *)
 >> Know ‘suminf (\i. f (i + m)) = suminf f2’
 >- (MATCH_MP_TAC ext_suminf_eq_shift \\
     Q.EXISTS_TAC ‘m’ >> rw [Abbr ‘f2’])
 >> Rewr'
 >> MATCH_MP_TAC ext_suminf_add'
 >> rw [Abbr ‘f1’, Abbr ‘f2’]
 >> fs []
QED

(* `sup` is the maximal element of any finite non-empty extreal set,
    see also le_sup_imp'.
 *)
Theorem sup_maximal :
    !p. FINITE p /\ p <> {} ==> extreal_sup p IN p
Proof
    Suff `!p. FINITE p ==> p <> {} ==> extreal_sup p IN p` >- rw []
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> Cases_on `p = EMPTY` >- fs [sup_sing]
 >> Suff `sup (e INSERT p) = max e (sup p)`
 >- (Rewr' >> rw [extreal_max_def])
 >> RW_TAC std_ss [sup_eq']
 >| [ (* goal 1 (of 2) *)
      fs [IN_INSERT, le_max] \\
      DISJ2_TAC \\
      MATCH_MP_TAC le_sup_imp' >> art [],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC \\
      fs [IN_INSERT, extreal_max_def] \\
      Cases_on `e <= sup p` >> fs [] ]
QED

(* `inf` is the minimal element of any finite non-empty extreal set.
    see also inf_le_imp'.
 *)
Theorem inf_minimal :
    !p. FINITE p /\ p <> {} ==> extreal_inf p IN p
Proof
    Suff `!p. FINITE p ==> p <> {} ==> extreal_inf p IN p` >- rw []
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> Cases_on `p = EMPTY` >- fs [inf_sing]
 >> Suff `inf (e INSERT p) = min e (inf p)`
 >- (Rewr' >> rw [extreal_min_def])
 >> RW_TAC std_ss [inf_eq']
 >| [ (* goal 1 (of 2) *)
      fs [IN_INSERT, min_le] \\
      DISJ2_TAC \\
      MATCH_MP_TAC inf_le_imp' >> art [],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC \\
      fs [IN_INSERT, extreal_min_def] \\
      Cases_on `e <= inf p` >> fs [] ]
QED

(* `open interval` of extreal sets. c.f. `OPEN_interval` / `CLOSED_interval`
   in real_toplogyTheory, `right_open_interval` in real_borelTheory.
 *)
Definition open_interval_def :
    open_interval (a :extreal) b = {x | a < x /\ x < b}
End

Theorem IN_open_interval :
    !a b x. x IN open_interval a b <=> a < x /\ x < b
Proof
    rw [open_interval_def]
QED

(* renamed from `open_intervals_set`, needed in borelTheory (lambda0_premeasure) *)
Definition open_intervals_def :
    open_intervals = {open_interval a b | T}
End

Definition rational_intervals_def :
    rational_intervals = {open_interval a b | a IN Q_set /\ b IN Q_set}
End

Theorem COUNTABLE_RATIONAL_INTERVALS :
    countable rational_intervals
Proof
    Suff `rational_intervals = IMAGE (\(a,b). open_interval a b) (Q_set CROSS Q_set)`
 >- METIS_TAC [cross_countable, Q_COUNTABLE, image_countable]
 >> RW_TAC std_ss [rational_intervals_def, IMAGE_DEF, EXTENSION, GSPECIFICATION,
                   IN_CROSS]
 >> EQ_TAC (* 2 subgoals, same tactics *)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ MP_TAC)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘y’
 >> Cases_on ‘y’ >> FULL_SIMP_TAC std_ss [PAIR_EQ, EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(*  Finite Product Images (PI) of extreals                                   *)
(* ------------------------------------------------------------------------- *)

(* old definition:

val EXTREAL_PROD_IMAGE_DEF = new_definition
  ("EXTREAL_PROD_IMAGE_DEF",
  ``EXTREAL_PROD_IMAGE f s = ITSET (\e acc. f e * acc) s (1 :extreal)``);

   new definition (based on iterateTheory):
 *)
Definition ext_product_def :
    ext_product = iterate (( * ):extreal->extreal->extreal)
End

Overload EXTREAL_PROD_IMAGE = “\f s. ext_product s f”
Overload PI = “EXTREAL_PROD_IMAGE”

val _ = Unicode.unicode_version {u = UTF8.chr 0x220F, tmnm = "PI"};
val _ = TeX_notation {hol = UTF8.chr 0x220F, TeX = ("\\HOLTokenPI{}", 1)};
val _ = TeX_notation {hol = "PI"           , TeX = ("\\HOLTokenPI{}", 1)};

Theorem neutral_mul :
    neutral(( * ):extreal->extreal->extreal) = &1
Proof
    REWRITE_TAC [neutral]
 >> MATCH_MP_TAC SELECT_UNIQUE
 >> METIS_TAC [mul_lone, mul_rone]
QED

Theorem monoidal_mul :
    monoidal(( * ):extreal->extreal->extreal)
Proof
    rw [monoidal, neutral_mul, mul_assoc]
 >> REWRITE_TAC [Once mul_comm]
QED

Theorem EXTREAL_PROD_IMAGE_THM :
    !f. (EXTREAL_PROD_IMAGE f {} = 1) /\
        !e s. FINITE s ==> (EXTREAL_PROD_IMAGE f (e INSERT s) =
                            f e * EXTREAL_PROD_IMAGE f (s DELETE e))
Proof
    Q.X_GEN_TAC ‘f’
 >> ASSUME_TAC monoidal_mul
 >> rw [ext_product_def, GSYM neutral_mul]
 >- rw [ITERATE_CLAUSES]
 >> reverse (Cases_on ‘e IN s’)
 >- (‘s DELETE e = s’ by METIS_TAC [DELETE_NON_ELEMENT] >> POP_ORW \\
     rw [ITERATE_CLAUSES])
 >> ‘e INSERT s = e INSERT (s DELETE e)’ by SET_TAC [] >> POP_ORW
 >> rw [ITERATE_CLAUSES]
QED

Theorem EXTREAL_PROD_IMAGE_EMPTY[simp]:   !f. EXTREAL_PROD_IMAGE f {} = 1
Proof
    SRW_TAC [] [EXTREAL_PROD_IMAGE_THM]
QED

Theorem EXTREAL_PROD_IMAGE_SING[simp]:   !f e. EXTREAL_PROD_IMAGE f {e} = f e
Proof
    SRW_TAC [] [EXTREAL_PROD_IMAGE_THM, mul_rone]
QED

Theorem EXTREAL_PROD_IMAGE_PROPERTY:
    !f e s. FINITE s ==> (EXTREAL_PROD_IMAGE f (e INSERT s) =
                          f e * EXTREAL_PROD_IMAGE f (s DELETE e))
Proof
    PROVE_TAC [EXTREAL_PROD_IMAGE_THM]
QED

Theorem EXTREAL_PROD_IMAGE_PAIR:
    !f a b. a <> b ==> (EXTREAL_PROD_IMAGE f {a; b} = f a * f b)
Proof
    RW_TAC std_ss []
 >> `FINITE {b}` by PROVE_TAC [FINITE_SING]
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`, `a`]) o (MATCH_MP EXTREAL_PROD_IMAGE_PROPERTY))
 >> RW_TAC std_ss []
 >> Know `{b} DELETE a = {b}`
 >- (RW_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DELETE, IN_SING] \\
     EQ_TAC >> rpt STRIP_TAC >> fs []) >> Rewr'
 >> REWRITE_TAC [EXTREAL_PROD_IMAGE_SING]
QED

(* NOTE: removed ‘FINITE s’ due to iterateTheory *)
Theorem EXTREAL_PROD_IMAGE_EQ :
    !s f f'. (!x. x IN s ==> (f x = f' x)) ==>
             (EXTREAL_PROD_IMAGE f s = EXTREAL_PROD_IMAGE f' s)
Proof
    rw [ext_product_def]
 >> irule ITERATE_EQ
 >> rw [monoidal_mul]
QED

Theorem EXTREAL_PROD_IMAGE_DISJOINT_UNION :
    !s s'. FINITE s /\ FINITE s' /\ DISJOINT s s' ==>
           !f. (EXTREAL_PROD_IMAGE f (s UNION s') =
                EXTREAL_PROD_IMAGE f s * EXTREAL_PROD_IMAGE f s')
Proof
    rw [ext_product_def]
 >> irule ITERATE_UNION
 >> rw [monoidal_mul]
QED

(* NOTE: removed ‘FINITE s’ due to iterateTheory *)
Theorem EXTREAL_PROD_IMAGE_IMAGE :
    !s f'. INJ f' s (IMAGE f' s) ==>
           !f. EXTREAL_PROD_IMAGE f (IMAGE f' s) = EXTREAL_PROD_IMAGE (f o f') s
Proof
    rw [ext_product_def, INJ_DEF]
 >> irule ITERATE_IMAGE
 >> rw [monoidal_mul]
QED

Theorem EXTREAL_PROD_IMAGE_COUNT :
    !f. (EXTREAL_PROD_IMAGE f (count 2) = f 0 * f 1) /\
        (EXTREAL_PROD_IMAGE f (count 3) = f 0 * f 1 * f 2) /\
        (EXTREAL_PROD_IMAGE f (count 4) = f 0 * f 1 * f 2 * f 3) /\
        (EXTREAL_PROD_IMAGE f (count 5) = f 0 * f 1 * f 2 * f 3 * f 4)
Proof
    Q.X_GEN_TAC ‘f’
 >> `count 2 = {0;1} /\
     count 3 = {0;1;2} /\
     count 4 = {0;1;2;3} /\
     count 5 = {0;1;2;3;4}`
       by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
 >> `{1:num} DELETE 0 = {1}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{2:num} DELETE 1 = {2}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{3:num} DELETE 2 = {3}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{4:num} DELETE 3 = {4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{2:num; 3} DELETE 1 = {2;3}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{3:num; 4} DELETE 2 = {3;4}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{2:num; 3; 4} DELETE 1 = {2;3;4}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2} DELETE 0 = {1;2}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2; 3} DELETE 0 = {1;2;3}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE,IN_SING,IN_INSERT]
 >> `{1:num; 2; 3; 4} DELETE 0 = {1;2;3;4}`
        by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> ASM_SIMP_TAC real_ss [FINITE_SING, FINITE_INSERT, EXTREAL_PROD_IMAGE_PROPERTY,
                          EXTREAL_PROD_IMAGE_SING, IN_INSERT, NOT_IN_EMPTY,
                          mul_assoc]
QED

(* ------------------------------------------------------------------------- *)
(*  Maximal values of a sequence of functions at the same point              *)
(* ------------------------------------------------------------------------- *)

Definition max_fn_seq_def :
   (max_fn_seq g 0       x = g 0 x) /\
   (max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x))
End

Theorem max_fn_seq_0[simp] :
    !g. max_fn_seq g 0 = g 0
Proof
    rw [FUN_EQ_THM, max_fn_seq_def]
QED

Theorem max_fn_seq_cong :
    !f g x. (!n. f n x = g n x) ==> !n. max_fn_seq f n x = max_fn_seq g n x
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on ‘n’
 >> rw [max_fn_seq_def]
QED

(* cf. real_topologyTheory.SUP_INSERT. For extreal, ‘bounded‘ is not needed. *)
Theorem sup_insert :
    !x s. sup (x INSERT s) = if s = {} then x else max x (sup s)
Proof
    rpt STRIP_TAC
 >> Cases_on ‘s = {}’ >- rw [sup_sing]
 >> rw [sup_eq', le_max, max_le]
 >| [ rw [le_refl] (* goal 1 (of 3) *),
      rw [le_sup'] (* goal 2 (of 3) *),
      rw [sup_le'] (* goal 3 (of 3) *) ]
QED

Theorem max_fn_seq_alt_sup :
    !f x n. max_fn_seq f n x = sup (IMAGE (\i. f i x) (count (SUC n)))
Proof
    NTAC 2 GEN_TAC
 >> Induct_on ‘n’ >- rw [max_fn_seq_def, sup_sing, COUNT_ONE]
 >> RW_TAC std_ss [max_fn_seq_def]
 >> KILL_TAC
 >> Q.ABBREV_TAC ‘A = IMAGE (\i. f i x) (count (SUC n))’
 >> ONCE_REWRITE_TAC [COUNT_SUC]
 >> rw [IMAGE_INSERT]
 >> ‘A <> {}’ by (rw [Abbr ‘A’, Once EXTENSION])
 >> rw [sup_insert, Once max_comm]
QED

(* An analog of ‘max_le’ *)
Theorem max_fn_seq_le :
    !f x y n. max_fn_seq f n x <= y <=> !i. i <= n ==> f i x <= y
Proof
    NTAC 3 GEN_TAC
 >> Induct_on ‘n’ >> rw [max_fn_seq_def]
 >> rw [max_le]
 >> KILL_TAC
 >> EQ_TAC >> rw []
 >> ‘i = SUC n \/ i <= n’ by rw [] >- rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem lt_max_fn_seq :
    !f x y n. x < max_fn_seq f n y <=> ?i. i <= n /\ x < f i y
Proof
    NTAC 3 GEN_TAC
 >> Induct_on ‘n’ >> rw [max_fn_seq_def, lt_max]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 3) *)
      Q.EXISTS_TAC ‘i’ >> rw [],
      (* goal 2 (of 3) *)
      Q.EXISTS_TAC ‘SUC n’ >> rw [],
      (* goal 3 (of 3) *)
     ‘i = SUC n \/ i <= n’ by rw [] >- rw [] \\
      DISJ1_TAC >> Q.EXISTS_TAC ‘i’ >> rw [] ]
QED

Theorem max_fn_seq_mono :
    !g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x
Proof
    RW_TAC std_ss [max_fn_seq_def, extreal_max_def, le_refl]
QED

(* ------------------------------------------------------------------------- *)
(*  Positive and negative parts of functions (moved from borelTheory)        *)
(* ------------------------------------------------------------------------- *)

Definition fn_plus_def:   (* f^+ *)
    fn_plus (f :'a -> extreal) = (\x. if 0 < f x then f x else 0)
End

Overload TC = ``fn_plus``(* relationTheory *)

Definition fn_minus_def:   (* f^- *)
    fn_minus (f :'a -> extreal) = (\x. if f x < 0 then ~(f x) else 0)
End

val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^-"],
                   term_name = "fn_minus"};

val _ = Unicode.unicode_version {u = Unicode.UChar.sup_minus, tmnm = "fn_minus"};
val _ = TeX_notation {hol = Unicode.UChar.sup_minus,
                      TeX = ("\\HOLTokenSupMinus{}", 1)};
val _ = TeX_notation {hol = "^-", TeX = ("\\HOLTokenSupMinus{}", 1)};

(* alternative definitions of fn_plus and fn_minus using max/min *)
Theorem FN_PLUS_ALT :
    !f. fn_plus f = (\x. max (f x) 0)
Proof
    RW_TAC std_ss [fn_plus_def, extreal_max_def]
 >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC
 >> Cases_on `0 < f x`
 >- (`~(f x <= 0)` by PROVE_TAC [let_antisym] >> fs [])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> fs []
QED

(* !f. fn_plus f = (\x. max 0 (f x)) *)
Theorem FN_PLUS_ALT' = ONCE_REWRITE_RULE [max_comm] FN_PLUS_ALT

Theorem fn_plus : (* original definition *)
    !f x. fn_plus f x = max 0 (f x)
Proof
    RW_TAC std_ss [FN_PLUS_ALT']
QED

Theorem FN_MINUS_ALT :
    !f. fn_minus f = (\x. -min (f x) 0)
Proof
    RW_TAC std_ss [fn_minus_def, extreal_min_def]
 >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC
 >> Cases_on `f x < 0`
 >- (`f x <= 0` by PROVE_TAC [lt_imp_le] >> fs [])
 >> fs []
 >> `0 <= f x` by PROVE_TAC [extreal_lt_def]
 >> Cases_on `f x <= 0`
 >- (`f x = 0` by PROVE_TAC [le_antisym] >> fs [neg_0])
 >> fs [neg_0]
QED

(* |- !f. fn_minus f = (\x. -min 0 (f x)) *)
Theorem FN_MINUS_ALT' = ONCE_REWRITE_RULE [min_comm] FN_MINUS_ALT;

Theorem fn_minus : (* original definition *)
    !f x. fn_minus f x = -min 0 (f x)
Proof
    RW_TAC std_ss [FN_MINUS_ALT']
QED

Theorem FN_DECOMP:   !f x. f x = fn_plus f x - fn_minus f x
Proof
    RW_TAC std_ss [fn_plus_def, fn_minus_def]
 >- METIS_TAC [lt_antisym]
 >- REWRITE_TAC [sub_rzero]
 >- (`0 - -f x = 0 + f x` by METIS_TAC [sub_rneg, extreal_of_num_def] \\
     POP_ORW >> REWRITE_TAC [add_lzero])
 >> REWRITE_TAC [sub_rzero]
 >> METIS_TAC [extreal_lt_def, le_antisym]
QED

Theorem FN_DECOMP':   !f. f = (\x. fn_plus f x - fn_minus f x)
Proof
    METIS_TAC [FN_DECOMP]
QED

(* `fn_plus f x + fn_minus f x` is always defined (same reason as above) *)
Theorem FN_ABS :
    !f x. (abs o f) x = fn_plus f x + fn_minus f x
Proof
    RW_TAC std_ss [o_DEF, fn_plus_def, fn_minus_def, add_rzero, add_lzero]
 >> Q.ABBREV_TAC `e = f x` (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      METIS_TAC [lt_antisym],
      (* goal 2 (of 4) *)
      Cases_on `e` >- METIS_TAC [extreal_of_num_def, lt_infty]
      >- REWRITE_TAC [extreal_abs_def] \\
      REWRITE_TAC [extreal_abs_def, extreal_11] \\
     `0 <= r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq, REAL_LT_IMP_LE] \\
      METIS_TAC [abs],
      (* goal 3 (of 4) *)
      Cases_on `e` >- REWRITE_TAC [extreal_abs_def, extreal_ainv_def]
      >- METIS_TAC [extreal_of_num_def, lt_infty] \\
      REWRITE_TAC [extreal_abs_def, extreal_ainv_def, extreal_11] \\
     `r < 0` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
      METIS_TAC [real_lte, abs],
      (* goal 4 (of 4) *)
     `e = 0` by METIS_TAC [extreal_lt_def, le_antisym] \\
      PROVE_TAC [abs_0] ]
QED

Theorem FN_ABS' :
    !f. (abs o f) = (\x. fn_plus f x + fn_minus f x)
Proof
    METIS_TAC [FN_ABS]
QED

Theorem FN_PLUS_POS :
    !g x. 0 <= (fn_plus g) x
Proof
    RW_TAC real_ss [fn_plus_def, FUN_EQ_THM, lt_imp_le, le_refl]
QED

Theorem FN_MINUS_POS :
    !g x. 0 <= (fn_minus g) x
Proof
    RW_TAC real_ss [fn_minus_def, FUN_EQ_THM, le_refl]
 >> METIS_TAC [le_neg, lt_imp_le, neg_0]
QED

Theorem FN_PLUS_POS_ID :
    !g. (!x. 0 <= g x) ==> ((fn_plus g) = g)
Proof
    RW_TAC real_ss [fn_plus_def,FUN_EQ_THM]
 >> Cases_on `g x = 0` >- METIS_TAC []
 >> METIS_TAC [le_lt]
QED

Theorem FN_PLUS_REDUCE[simp] :
    !f x. 0 <= f x ==> (fn_plus f x = f x)
Proof
    RW_TAC std_ss [fn_plus_def]
 >> METIS_TAC [le_lt]
QED

Theorem FN_PLUS_REDUCE' :
    !f x. f x <= 0 ==> (fn_plus f x = 0)
Proof
    RW_TAC std_ss [fn_plus_def]
 >> METIS_TAC [let_antisym]
QED

Theorem FN_MINUS_REDUCE[simp] :
    !f x. 0 <= f x ==> (fn_minus f x = 0)
Proof
    RW_TAC std_ss [fn_minus_def]
 >> PROVE_TAC [let_antisym]
QED

(* don't put it into simp sets, ‘o’ may be eliminated *)
Theorem FN_PLUS_ABS_SELF :
    !f. fn_plus (abs o f) = abs o f
Proof
    RW_TAC bool_ss [FUN_EQ_THM]
 >> MATCH_MP_TAC FN_PLUS_REDUCE
 >> RW_TAC std_ss [o_DEF, abs_pos]
QED
Theorem fn_plus_abs = FN_PLUS_ABS_SELF

(* don't put it into simp sets, ‘o’ may be eliminated *)
Theorem FN_MINUS_ABS_ZERO :
    !f. fn_minus (abs o f) = \x. 0
Proof
    RW_TAC bool_ss [FUN_EQ_THM]
 >> MATCH_MP_TAC FN_MINUS_REDUCE
 >> RW_TAC std_ss [o_DEF, abs_pos]
QED
Theorem fn_minus_abs = FN_MINUS_ABS_ZERO

Theorem FN_PLUS_NEG_ZERO :
    !g. (!x. g x <= 0) ==> (fn_plus g = (\x. 0))
Proof
    RW_TAC real_ss [fn_plus_def, FUN_EQ_THM]
 >> `~(0 < g x)` by PROVE_TAC [extreal_lt_def]
 >> fs []
QED

Theorem FN_MINUS_POS_ZERO :
    !g. (!x. 0 <= g x) ==> (fn_minus g = (\x. 0))
Proof
    RW_TAC real_ss [fn_minus_def, FUN_EQ_THM]
 >> Cases_on `g x = 0` >- METIS_TAC [neg_0]
 >> `0 < g x` by METIS_TAC [lt_le]
 >> METIS_TAC [extreal_lt_def]
QED

Theorem FN_PLUS_ZERO[simp] :
    fn_plus (\x. 0) = (\x. 0)
Proof
    MATCH_MP_TAC FN_PLUS_NEG_ZERO
 >> RW_TAC std_ss [le_refl]
QED

Theorem FN_MINUS_ZERO[simp] :
    fn_minus (\x. 0) = (\x. 0)
Proof
    MATCH_MP_TAC FN_MINUS_POS_ZERO
 >> RW_TAC std_ss [le_refl]
QED

Theorem FN_MINUS_TO_PLUS :
    !f. fn_minus (\x. -(f x)) = fn_plus f
Proof
    RW_TAC std_ss [fn_plus_def, fn_minus_def, neg_neg]
 >> `!x. -f x < 0 <=> 0 < f x` by PROVE_TAC [neg_0, lt_neg]
 >> POP_ORW >> REWRITE_TAC []
QED

Theorem FN_PLUS_TO_MINUS :
    !f. fn_plus (\x. -(f x)) = fn_minus f
Proof
    RW_TAC std_ss [fn_plus_def, fn_minus_def, neg_neg]
 >> `!x. 0 < -f x <=> f x < 0` by PROVE_TAC [neg_0, lt_neg]
 >> POP_ORW >> REWRITE_TAC []
QED

Theorem FN_PLUS_NOT_INFTY :
    !f x. f x <> PosInf ==> fn_plus f x <> PosInf
Proof
    RW_TAC std_ss [fn_plus_def]
 >> Cases_on `0 < f x` >- PROVE_TAC []
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]
QED

Theorem FN_MINUS_NOT_INFTY :
    !f x. f x <> NegInf ==> fn_minus f x <> PosInf
Proof
    RW_TAC std_ss [fn_minus_def]
 >> Cases_on `f x < 0`
 >- PROVE_TAC [extreal_ainv_def, neg_neg]
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]
QED

Theorem FN_PLUS_CMUL:
    !f c. (0 <= c ==> (fn_plus (\x. Normal c * f x) = (\x. Normal c * fn_plus f x))) /\
          (c <= 0 ==> (fn_plus (\x. Normal c * f x) = (\x. -Normal c * fn_minus f x)))
Proof
    RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
 >- (Cases_on `0 < f x`
     >- METIS_TAC [let_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, le_antisym]
     >> RW_TAC std_ss [mul_rzero]
     >> METIS_TAC [mul_le, extreal_lt_def, extreal_le_def, extreal_of_num_def, lt_imp_le,
                   le_antisym])
 >> RW_TAC std_ss [mul_rzero, neg_mul2]
 >- METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
               le_antisym, mul_comm]
 >> METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
               le_antisym]
QED

(* NOTE: This (new) lemma is more general than FN_PLUS_CMUL_full because sometimes ‘c’
   depends on ‘x’. But the proof is the same.
 *)
Theorem fn_plus_cmul :
    !f c x. (0 <= c ==> fn_plus (\x. c * f x) x = c * fn_plus f x) /\
            (c <= 0 ==> fn_plus (\x. c * f x) x = -c * fn_minus f x)
Proof
    rpt GEN_TAC
 >> Cases_on `c`
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     RW_TAC std_ss [fn_plus_def, fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [neg_mul2],
       (* goal 2 (of 4) *)
      `0 <= f x` by PROVE_TAC [extreal_lt_def] \\
      `NegInf <= 0` by PROVE_TAC [le_infty] \\
      `NegInf * f x <= 0` by PROVE_TAC [mul_le2] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `NegInf < 0` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `0 < NegInf * f x` by PROVE_TAC [lt_mul_neg],
       (* goal 4 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     RW_TAC std_ss [fn_plus_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
      `f x <= 0` by PROVE_TAC [extreal_lt_def] \\
       fs [le_lt] \\
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `PosInf * f x < 0` by PROVE_TAC [mul_lt] \\
       PROVE_TAC [lt_antisym],
       (* goal 2 (of 3) *)
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `0 < PosInf * f x` by PROVE_TAC [lt_mul],
       (* goal 3 (of 3) *)
       REWRITE_TAC [mul_rzero] ])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `0 <= r` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_PLUS_CMUL],
      (* goal 2 (of 2) *)
     `r <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_PLUS_CMUL] ]
QED

Theorem FN_PLUS_CMUL_full :
    !f c. (0 <= c ==> (fn_plus (\x. c * f x) = (\x. c * fn_plus f x))) /\
          (c <= 0 ==> (fn_plus (\x. c * f x) = (\x. -c * fn_minus f x)))
Proof
    RW_TAC std_ss [FUN_EQ_THM, fn_plus_cmul]
QED

Theorem FN_MINUS_CMUL:
    !f c. (0 <= c ==> (fn_minus (\x. Normal c * f x) = (\x. Normal c * fn_minus f x))) /\
          (c <= 0 ==> (fn_minus (\x. Normal c * f x) = (\x. -Normal c * fn_plus f x)))
Proof
    RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
 >- (RW_TAC std_ss [mul_rzero, mul_rneg, neg_eq0]
     >- METIS_TAC [le_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
                   le_antisym]
     >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
                   le_antisym, neg_eq0])
 >> RW_TAC std_ss [mul_rzero, neg_eq0, mul_lneg, neg_0]
 >- METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
               le_antisym]
 >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
               le_antisym, neg_eq0, mul_comm]
QED

Theorem fn_minus_cmul :
    !f c x. (0 <= c ==> fn_minus (\x. c * f x) x = c * fn_minus f x) /\
            (c <= 0 ==> fn_minus (\x. c * f x) x = -c * fn_plus f x)
Proof
    rpt GEN_TAC
 >> Cases_on `c`
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     RW_TAC std_ss [fn_plus_def, fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [GSYM mul_lneg],
       (* goal 2 (of 4) *)
      `f x <= 0` by PROVE_TAC [extreal_lt_def] \\
      `NegInf <= 0` by PROVE_TAC [le_infty] \\
      `0 <= NegInf * f x` by PROVE_TAC [le_mul_neg] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `NegInf < 0` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `NegInf * f x < 0` by PROVE_TAC [mul_lt2],
       (* goal 4 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     RW_TAC std_ss [fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [GSYM mul_rneg],
       (* goal 2 (of 4) *)
      `0 <= f x` by PROVE_TAC [extreal_lt_def] \\
      `0 <= PosInf` by PROVE_TAC [le_infty] \\
      `0 <= PosInf * f x` by PROVE_TAC [le_mul] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `PosInf * f x < 0` by PROVE_TAC [mul_lt],
       (* goal 3 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `0 <= r` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_MINUS_CMUL],
      (* goal 2 (of 2) *)
     `r <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_MINUS_CMUL] ]
QED

Theorem FN_MINUS_CMUL_full :
    !f c. (0 <= c ==> (fn_minus (\x. c * f x) = (\x. c * fn_minus f x))) /\
          (c <= 0 ==> (fn_minus (\x. c * f x) = (\x. -c * fn_plus f x)))
Proof
    RW_TAC std_ss [FUN_EQ_THM, fn_minus_cmul]
QED

Theorem fn_plus_fmul :
    !f c x. (!x. 0 <= c x) ==> fn_plus (\x. c x * f x) x = c x * fn_plus f x
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> simp [fn_plus_def]
 >> Cases_on `0 < f x`
 >- (`0 <= c x * f x` by PROVE_TAC [let_mul] \\
     fs [le_lt])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> `c x * f x <= 0` by PROVE_TAC [mul_le]
 >> `~(0 < c x * f x)` by PROVE_TAC [extreal_lt_def]
 >> fs [mul_rzero]
QED

Theorem FN_PLUS_FMUL :
    !f c. (!x. 0 <= c x) ==> fn_plus (\x. c x * f x) = (\x. c x * fn_plus f x)
Proof
    RW_TAC std_ss [FUN_EQ_THM, fn_plus_fmul]
QED

Theorem fn_minus_fmul :
    !f c x. (!x. 0 <= c x) ==> fn_minus (\x. c x * f x) x = c x * fn_minus f x
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> simp [fn_minus_def]
 >> Cases_on `0 < f x`
 >- (`0 <= c x * f x` by PROVE_TAC [let_mul] \\
     `~(c x * f x < 0)` by PROVE_TAC [extreal_lt_def] \\
     `~(f x < 0)` by PROVE_TAC [lt_antisym] \\
     fs [mul_rzero])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> `c x * f x <= 0` by PROVE_TAC [mul_le]
 >> `~(0 < c x * f x)` by PROVE_TAC [extreal_lt_def]
 >> fs [le_lt, lt_refl, mul_rzero, neg_0]
 >- REWRITE_TAC [GSYM mul_rneg]
 >> fs [entire, neg_0]
QED

Theorem FN_MINUS_FMUL :
    !f c. (!x. 0 <= c x) ==> fn_minus (\x. c x * f x) = (\x. c x * fn_minus f x)
Proof
    RW_TAC std_ss [FUN_EQ_THM, fn_minus_fmul]
QED

Theorem FN_PLUS_ADD_LE:
    !f g x. fn_plus (\x. f x + g x) x <= (fn_plus f x) + (fn_plus g x)
Proof
    RW_TAC real_ss [fn_plus_def, add_rzero, add_lzero, le_refl, le_add2]
 >> METIS_TAC [le_refl, extreal_lt_def, le_add2, add_lzero, add_rzero, lt_imp_le]
QED

(* more antecedents added: no mixing of PosInf and NegInf *)
Theorem FN_MINUS_ADD_LE:
    !f g x. (f x <> NegInf) /\ (g x <> NegInf) \/
            (f x <> PosInf) /\ (g x <> PosInf) ==>
            fn_minus (\x. f x + g x) x <= (fn_minus f x) + (fn_minus g x)
Proof
    rpt GEN_TAC
 >> DISCH_TAC
 >> MP_TAC (BETA_RULE (Q.SPECL [`\x. -f x`, `\x. -g x`, `x`] FN_PLUS_ADD_LE))
 >> Suff `fn_plus (\x. -f x + -g x) x = fn_minus (\x. f x + g x) x`
 >- (Rewr' >> REWRITE_TAC [FN_PLUS_TO_MINUS])
 >> SIMP_TAC std_ss [fn_plus_def, fn_minus_def]
 >> Know `-f x + -g x = -(f x + g x)`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC neg_add >> art []) >> Rewr
 >> `0 < -(f x + g x) <=> f x + g x < 0` by PROVE_TAC [neg_0, lt_neg] >> POP_ORW
 >> REWRITE_TAC []
QED

Theorem FN_PLUS_LE_ABS :
    !f x. fn_plus f x <= abs (f x)
Proof
    rpt GEN_TAC >> REWRITE_TAC [SIMP_RULE std_ss [o_DEF] FN_ABS]
 >> ACCEPT_TAC
      (((REWRITE_RULE [le_refl, add_rzero, FN_MINUS_POS]) o
        (Q.SPECL [`fn_plus f x`, `fn_plus f x`, `0`, `fn_minus f x`])) le_add2)
QED

Theorem FN_MINUS_LE_ABS :
    !f x. fn_minus f x <= abs (f x)
Proof
    rpt GEN_TAC >> REWRITE_TAC [SIMP_RULE std_ss [o_DEF] FN_ABS]
 >> ACCEPT_TAC
      (((REWRITE_RULE [le_refl, add_lzero, FN_PLUS_POS]) o
        (Q.SPECL [`0`, `fn_plus f x`, `fn_minus f x`, `fn_minus f x`])) le_add2)
QED

(* A balance between fn_plus and fn_minus *)
Theorem FN_PLUS_INFTY_IMP :
    !f x. (fn_plus f x = PosInf) ==> (fn_minus f x = 0)
Proof
    rpt STRIP_TAC
 >> Suff ‘f x = PosInf’
 >- (DISCH_TAC >> MATCH_MP_TAC FN_MINUS_REDUCE \\
     POP_ORW >> REWRITE_TAC [extreal_of_num_def, extreal_le_def])
 >> CCONTR_TAC
 >> Suff ‘fn_plus f x <> PosInf’ >- PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘fn_plus f x = PosInf’ K_TAC
 >> RW_TAC std_ss [fn_plus_def]
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]
QED

Theorem FN_MINUS_INFTY_IMP :
    !f x. (fn_minus f x = PosInf) ==> (fn_plus f x = 0)
Proof
    rpt STRIP_TAC
 >> Suff ‘f x = NegInf’
 >- (DISCH_TAC \\
     RW_TAC std_ss [fn_plus_def, FUN_EQ_THM] \\
     fs [lt_infty, extreal_of_num_def])
 >> CCONTR_TAC
 >> Suff ‘fn_minus f x <> PosInf’ >- PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘fn_minus f x = PosInf’ K_TAC
 >> reverse (RW_TAC std_ss [fn_minus_def])
 >- PROVE_TAC [extreal_not_infty, extreal_of_num_def]
 >> CCONTR_TAC >> fs []
 >> METIS_TAC [neg_neg, extreal_ainv_def]
QED

(* ******************************************* *)
(*   Non-negative functions (not very useful)  *)
(* ******************************************* *)

Definition nonneg_def:
    nonneg (f :'a -> extreal) = !x. 0 <= f x
End

Theorem nonneg_abs:   !f. nonneg (abs o f)
Proof
    RW_TAC std_ss [o_DEF, nonneg_def, abs_pos]
QED

Theorem nonneg_fn_abs:   !f. nonneg f ==> (abs o f = f)
Proof
    RW_TAC std_ss [nonneg_def, o_DEF, FUN_EQ_THM, abs_refl]
QED

Theorem nonneg_fn_plus:   !f. nonneg f ==> (fn_plus f = f)
Proof
    RW_TAC std_ss [nonneg_def, fn_plus_def]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss []
 >> PROVE_TAC [le_lt]
QED

Theorem nonneg_fn_minus:   !f. nonneg f ==> (fn_minus f = (\x. 0))
Proof
    RW_TAC std_ss [nonneg_def, fn_minus_def]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss [extreal_lt_def]
QED

(* ------------------------------------------------------------------------- *)
(*  Indicator functions                                                      *)
(* ------------------------------------------------------------------------- *)

(* `indicator_fn s` maps x to 0 or 1 when x IN or NOTIN s,

   The new definition is based on the real-valued iterateTheory.indicator:
 *)
Definition indicator_fn :
    indicator_fn s = Normal o indicator s
End

(* The old definition now becomes an equivalent theorem *)
Theorem indicator_fn_def :
    !s. indicator_fn s = \x. if x IN s then (1 :extreal) else (0 :extreal)
Proof
    rw [indicator, indicator_fn, extreal_of_num_def, o_DEF, FUN_EQ_THM]
 >> Cases_on ‘x IN s’ >> rw []
QED

(* MATHEMATICAL DOUBLE-STRUCK DIGIT ONE *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x1D7D9, tmnm = "indicator_fn"};
val _ = TeX_notation {hol = UTF8.chr 0x1D7D9, TeX = ("\\HOLTokenOne{}", 1)};
val _ = TeX_notation {hol = "indicator_fn",   TeX = ("\\HOLTokenOne{}", 1)};

Theorem DROP_INDICATOR_FN :
    !s x. indicator_fn s x = if x IN s then 1 else 0
Proof
    rw [indicator_fn, extreal_of_num_def, DROP_INDICATOR]
QED

Theorem INDICATOR_FN_POS :
    !s x. 0 <= indicator_fn s x
Proof
    rw [indicator_fn, extreal_of_num_def, extreal_le_eq, DROP_INDICATOR_POS_LE]
QED

Theorem INDICATOR_FN_LE_1 :
    !s x. indicator_fn s x <= 1
Proof
    rw [indicator_fn, extreal_of_num_def, extreal_le_eq, DROP_INDICATOR_LE_1]
QED

Theorem INDICATOR_FN_NOT_INFTY:
    !s x. indicator_fn s x <> NegInf /\ indicator_fn s x <> PosInf
Proof
    RW_TAC std_ss []
 >- (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [INDICATOR_FN_POS])
 >> Cases_on `x IN s`
 >> ASM_SIMP_TAC std_ss [indicator_fn_def, extreal_of_num_def, extreal_not_infty]
QED

(* "advanced" lemmas/theorems should have lower-case names *)
Theorem indicator_fn_normal :
    !s x. ?r. (indicator_fn s x = Normal r) /\ 0 <= r /\ r <= 1
Proof
    rpt STRIP_TAC
 >> `?r. indicator_fn s x = Normal r`
       by METIS_TAC [extreal_cases, INDICATOR_FN_NOT_INFTY]
 >> Q.EXISTS_TAC `r` >> art []
 >> METIS_TAC [INDICATOR_FN_POS, INDICATOR_FN_LE_1, extreal_le_eq,
               extreal_of_num_def]
QED

Theorem INDICATOR_FN_SING_1:   !x y. (x = y) ==> (indicator_fn {x} y = 1)
Proof
    RW_TAC std_ss [indicator_fn_def, IN_SING]
QED

Theorem INDICATOR_FN_SING_0:   !x y. x <> y ==> (indicator_fn {x} y = 0)
Proof
    RW_TAC std_ss [indicator_fn_def, IN_SING]
QED

Theorem INDICATOR_FN_EMPTY[simp] :
    !x. indicator_fn {} x = 0
Proof
    RW_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY]
QED

Theorem INDICATOR_FN_UNIV :
    !x. indicator_fn UNIV (x :'a) = 1
Proof
    rw [indicator_fn_def]
QED

(* Properties of the indicator function [1, p.14] *)
Theorem INDICATOR_FN_INTER:
    !A B. indicator_fn (A INTER B) = (\t. (indicator_fn A t) * (indicator_fn B t))
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> RW_TAC std_ss [indicator_fn_def, mul_lone, IN_INTER, mul_lzero]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem INDICATOR_FN_MUL_INTER:
    !A B. (\t. (indicator_fn A t) * (indicator_fn B t)) = (\t. indicator_fn (A INTER B) t)
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
       by METIS_TAC [indicator_fn_def]
 >> RW_TAC std_ss [indicator_fn_def, mul_lone, IN_INTER, mul_lzero]
 >> FULL_SIMP_TAC real_ss []
QED

Theorem INDICATOR_FN_INTER_MIN:
    !A B. indicator_fn (A INTER B) = (\t. min (indicator_fn A t) (indicator_fn B t))
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_of_num_def, extreal_min_def, extreal_le_eq]
QED

Theorem INDICATOR_FN_DIFF:
    !A B. indicator_fn (A DIFF B) = (\t. indicator_fn A t - indicator_fn (A INTER B) t)
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A DIFF B) t = if t IN (A DIFF B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_DIFF, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [sub_rzero]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC sub_refl
 >> PROVE_TAC [extreal_of_num_def, extreal_not_infty]
QED

Theorem INDICATOR_FN_DIFF_SPACE:
    !A B sp. A SUBSET sp /\ B SUBSET sp ==>
            (indicator_fn (A INTER (sp DIFF B)) =
             (\t. indicator_fn A t - indicator_fn (A INTER B) t))
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A DIFF B) t = if t IN (A DIFF B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_DIFF, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [SUBSET_DEF, sub_rzero]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC sub_refl
 >> PROVE_TAC [extreal_of_num_def, extreal_not_infty]
QED

Theorem INDICATOR_FN_UNION_MAX:
    !A B. indicator_fn (A UNION B) = (\t. max (indicator_fn A t) (indicator_fn B t))
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_max_def, extreal_le_eq, extreal_of_num_def]
QED

Theorem INDICATOR_FN_UNION_MIN:
    !A B. indicator_fn (A UNION B) = (\t. min (indicator_fn A t + indicator_fn B t) 1)
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_max_def, extreal_add_def, extreal_of_num_def, extreal_min_def, extreal_le_eq]
QED

Theorem INDICATOR_FN_UNION:
    !A B. indicator_fn (A UNION B) =
          (\t. indicator_fn A t + indicator_fn B t - indicator_fn (A INTER B) t)
Proof
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [add_lzero, add_rzero, mul_rzero, sub_rzero]
 >> fs [extreal_add_def, extreal_sub_def, extreal_of_num_def]
QED

Theorem INDICATOR_FN_MONO :
    !s t x. s SUBSET t ==> indicator_fn s x <= indicator_fn t x
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x IN s’
 >- (‘x IN t’ by PROVE_TAC [SUBSET_DEF] \\
     rw [indicator_fn_def, le_refl])
 >> ‘indicator_fn s x = 0’ by METIS_TAC [indicator_fn_def] >> POP_ORW
 >> REWRITE_TAC [INDICATOR_FN_POS]
QED

Theorem INDICATOR_FN_CROSS :
    !s t x y. indicator_fn (s CROSS t) (x,y) = indicator_fn s x *
                                               indicator_fn t y
Proof
    rw [indicator_fn_def]
 >> PROVE_TAC []
QED

Theorem indicator_fn_split :
    !(r:num->bool) s (b:num->('a->bool)).
       FINITE r /\ (BIGUNION (IMAGE b r) = s) /\
       (!i j. i IN r /\ j IN r /\ i <> j ==> DISJOINT (b i) (b j)) ==>
       !a. a SUBSET s ==>
          (indicator_fn a = (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))
Proof
    Suff `!r. FINITE r ==>
            (\r. !s (b:num->('a->bool)).
             FINITE r /\
             (BIGUNION (IMAGE b r) = s) /\
             (!i j. i IN r /\ j IN r /\ i <> j ==> DISJOINT (b i) (b j)) ==>
             !a. a SUBSET s ==>
                 ((indicator_fn a) =
                  (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))) r`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY,
                   SUBSET_EMPTY, indicator_fn_def, NOT_IN_EMPTY,
                   FINITE_INSERT, IMAGE_INSERT, DELETE_NON_ELEMENT,
                   IN_INSERT, BIGUNION_INSERT]
 >> Q.PAT_X_ASSUM `!b. P ==> !a. Q ==> (x = y)`
      (MP_TAC o Q.ISPEC `(b :num -> 'a -> bool)`)
 >> RW_TAC std_ss [SUBSET_DEF]
 >> POP_ASSUM (MP_TAC o Q.ISPEC `a DIFF ((b :num -> 'a -> bool) e)`)
 >> Know `(!x. x IN a DIFF b e ==> x IN BIGUNION (IMAGE b s))`
 >- METIS_TAC [SUBSET_DEF, IN_UNION, IN_DIFF]
 >> RW_TAC std_ss [FUN_EQ_THM]
 >> `!i. i IN e INSERT s ==> (\i. if x IN a INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def, extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> Know `SIGMA (\i. (if x IN a INTER b i then 1 else 0)) s =
          SIGMA (\i. (if x IN (a DIFF b e) INTER b i then 1 else 0)) s`
 >- (`!i. i IN s ==> (\i. if x IN a INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def,extreal_not_infty] \\
     `!i. i IN s ==> (\i. if x IN (a DIFF b e) INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def,extreal_not_infty] \\
     FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
     FULL_SIMP_TAC std_ss [(Q.SPEC `(\i. if x IN (a DIFF b e) INTER b i then 1 else 0)`
                            o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
     MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) \\
     RW_TAC std_ss [FUN_EQ_THM, IN_INTER, IN_DIFF] \\
     FULL_SIMP_TAC real_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, IN_INTER,
                            NOT_IN_EMPTY, EXTENSION, GSPECIFICATION] \\
     RW_TAC real_ss [extreal_of_num_def] >> METIS_TAC []) >> STRIP_TAC
 >> `SIGMA (\i. if x IN a INTER b i then 1 else 0) s = (if x IN a DIFF b e then 1 else 0)`
      by METIS_TAC []
 >> POP_ORW
 >> RW_TAC real_ss [IN_INTER, IN_DIFF, EXTREAL_SUM_IMAGE_ZERO, add_rzero, add_lzero]
 >> FULL_SIMP_TAC std_ss []
 >> `x IN BIGUNION (IMAGE b s)` by METIS_TAC [SUBSET_DEF,IN_UNION]
 >> FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE]
 >> `s = {x'} UNION (s DIFF {x'})` by METIS_TAC [UNION_DIFF, SUBSET_DEF, IN_SING]
 >> POP_ORW
 >> `FINITE {x'} /\ FINITE (s DIFF {x'})` by METIS_TAC [FINITE_SING, FINITE_DIFF]
 >> `DISJOINT {x'} (s DIFF {x'})` by METIS_TAC [EXTENSION, IN_DISJOINT, IN_DIFF, IN_SING]
 >> `!i. (\i. if x IN b i then 1 else 0) i <> NegInf`
       by METIS_TAC [extreal_of_num_def,extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]
 >> Suff `SIGMA (\i. if x IN b i then 1 else 0) (s DIFF {x'}) = 0`
 >- METIS_TAC [add_rzero]
 >> FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool) DIFF {x'}`)
                              EXTREAL_SUM_IMAGE_IN_IF]
 >> Suff `(\i. if i IN s DIFF {x'} then if x IN b i then 1 else 0 else 0) = (\x. 0)`
 >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
 >> RW_TAC std_ss [FUN_EQ_THM, IN_DIFF, IN_SING]
 >> METIS_TAC [IN_SING, IN_DIFF, IN_DISJOINT]
QED

Theorem indicator_fn_suminf :
    !a x. (!m n. m <> n ==> DISJOINT (a m) (a n)) ==>
          suminf (\i. indicator_fn (a i) x) =
          indicator_fn (BIGUNION (IMAGE a univ(:num))) x
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\i. indicator_fn (a i) x) n`
 >- RW_TAC std_ss [INDICATOR_FN_POS]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def)) >> Rewr'
 >> RW_TAC std_ss [sup_eq', IN_UNIV, IN_IMAGE]
 >- (Cases_on `~(x IN BIGUNION (IMAGE a univ(:num)))`
     >- (FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV] \\
         RW_TAC std_ss [indicator_fn_def, EXTREAL_SUM_IMAGE_ZERO, FINITE_COUNT, le_refl, le_01]) \\
     FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, indicator_fn_def] \\
     reverse (RW_TAC std_ss []) >- METIS_TAC [] \\
    `!n. n <> x' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] \\
     Cases_on `~(x' IN count n)`
     >- (`SIGMA (\i. if x IN a i then 1 else 0) (count n) = 0`
            by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 \\
                RW_TAC real_ss [FINITE_COUNT] >> METIS_TAC []) \\
         RW_TAC std_ss [le_01]) \\
    `count n = ((count n) DELETE x') UNION {x'}`
        by (RW_TAC std_ss [EXTENSION, IN_DELETE, IN_UNION, IN_SING, IN_COUNT] \\
            METIS_TAC []) >> POP_ORW \\
    `DISJOINT ((count n) DELETE x') ({x'})`
        by RW_TAC std_ss [DISJOINT_DEF, EXTENSION,IN_INTER, NOT_IN_EMPTY, IN_SING, IN_DELETE] \\
    `!n. (\i. if x IN a i then 1 else 0) n <> NegInf` by RW_TAC std_ss [num_not_infty] \\
     FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, FINITE_SING,
                           EXTREAL_SUM_IMAGE_DISJOINT_UNION, EXTREAL_SUM_IMAGE_SING] \\
     Suff `SIGMA (\i. if x IN a i then 1 else 0) (count n DELETE x') = 0`
     >- RW_TAC std_ss [add_lzero, le_refl] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 \\
     RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE] \\
     METIS_TAC [IN_DELETE])
 >> Know `!n. SIGMA (\i. indicator_fn (a i) x) (count n) <= y`
 >- (RW_TAC std_ss [] >> POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> reverse (RW_TAC std_ss [indicator_fn_def, IN_BIGUNION_IMAGE, IN_UNIV])
 >- (`0 <= SIGMA (\i. indicator_fn (a i) x) (count 0)`
        by RW_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY, le_refl] \\
     METIS_TAC [le_trans])
 >> rename1 `x IN a x''`
 >> Suff `SIGMA (\i. indicator_fn (a i) x) (count (SUC x'')) = 1`
 >- METIS_TAC []
 >> `!i. (\i. indicator_fn (a i) x) i <> NegInf`
        by RW_TAC std_ss [indicator_fn_def, num_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, FINITE_COUNT, COUNT_SUC]
 >> Suff `SIGMA (\i. indicator_fn (a i) x) (count x'' DELETE x'') = 0`
 >- RW_TAC std_ss [indicator_fn_def, add_rzero]
 >> `!n. n <> x'' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
 >> FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, IN_COUNT, IN_DELETE, indicator_fn_def]
QED

Theorem INDICATOR_FN_ABS[simp] :
    !s. abs o (indicator_fn s) = indicator_fn s
Proof
    GEN_TAC >> FUN_EQ_TAC
 >> RW_TAC std_ss [o_DEF]
 >> REWRITE_TAC [abs_refl, INDICATOR_FN_POS]
QED

Theorem INDICATOR_FN_ABS_MUL :
    !f s. abs o (\x. f x * indicator_fn s x) = (\x. (abs o f) x * indicator_fn s x)
Proof
    RW_TAC std_ss [o_DEF, abs_mul]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss []
 >> Suff `abs (indicator_fn s x) = indicator_fn s x` >- rw []
 >> rw [abs_refl, INDICATOR_FN_POS]
QED

Theorem fn_plus_mul_indicator :
    !f s. fn_plus (\x. f x * indicator_fn s x) =
          (\x. fn_plus f x * indicator_fn s x)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC (Q.SPECL [‘f’, ‘indicator_fn s’] FN_PLUS_FMUL)
 >> GEN_TAC
 >> REWRITE_TAC [INDICATOR_FN_POS]
QED

Theorem fn_minus_mul_indicator :
    !f s. fn_minus (\x. f x * indicator_fn s x) =
          (\x. fn_minus f x * indicator_fn s x)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC (Q.SPECL [‘f’, ‘indicator_fn s’] FN_MINUS_FMUL)
 >> GEN_TAC
 >> REWRITE_TAC [INDICATOR_FN_POS]
QED

(* ------------------------------------------------------------------------- *)
(* univ(:extreal) is metrizable                                              *)
(* ------------------------------------------------------------------------- *)

Definition extreal_dist_def :
    extreal_dist (Normal x) (Normal y) = dist (bounded_metric mr1) (x,y) /\
    extreal_dist  PosInf     PosInf    = 0 /\
    extreal_dist  NegInf     NegInf    = 0 /\
    extreal_dist  _          _         = 1
End

(* ‘extreal_dist’ is a valid metric *)
Theorem extreal_dist_ismet :
    ismet (UNCURRY extreal_dist)
Proof
    RW_TAC std_ss [ismet]
 >- (Cases_on ‘x’ >> Cases_on ‘y’ \\
     rw [extreal_dist_def, bounded_metric_thm, MR1_DEF] \\
     EQ_TAC >> rw [] \\
     fs [REAL_DIV_ZERO] \\
     rename1 ‘1 + abs (a - b)’ \\
     Suff ‘0 < 1 + abs (a - b)’ >- METIS_TAC [REAL_LT_IMP_NE] \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [])
 >> Know ‘!a (b :real). dist (bounded_metric mr1) (a,b) <= 2’
 >- (rpt GEN_TAC \\
     MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC ‘1’ >> rw [] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> rw [bounded_metric_lt_1])
 >> DISCH_TAC
 >> Cases_on ‘x’ >> Cases_on ‘y’ >> Cases_on ‘z’
 >> rw [extreal_dist_def, METRIC_POS]
 >> rename1 ‘dist (bounded_metric mr1) (x,z) <=
             dist (bounded_metric mr1) (y,x) + dist (bounded_metric mr1) (y,z)’
 >> ‘dist (bounded_metric mr1) (y,x) = dist (bounded_metric mr1) (x,y)’
      by PROVE_TAC [METRIC_SYM]
 >> rw [METRIC_TRIANGLE]
QED

(* Thus ‘mtop extreal_mr1’ will be a possible topology of all extreals, and
  ‘open_in (mtop extreal_mr1)’ is the set of all extreal-valued "open" sets
  (w.r.t. ‘extreal_mr1’).
 *)
Definition extreal_mr1_def :
    extreal_mr1 = metric (UNCURRY extreal_dist)
End

(* Use this theorem to actually calculate the "distance" between two extreals *)
Theorem extreal_mr1_thm :
    dist extreal_mr1 = UNCURRY extreal_dist
Proof
    METIS_TAC [extreal_mr1_def, extreal_dist_ismet, metric_tybij]
QED

(* |- !x y. dist mr1 (x,y) = abs (x - y) *)
Theorem mr1_def[local] = ONCE_REWRITE_RULE [ABS_SUB] MR1_DEF

Theorem extreal_dist_normal :
    !x y. extreal_dist (Normal x) (Normal y) = abs (x - y) / (1 + abs (x - y))
Proof
    rw [extreal_dist_def, bounded_metric_thm, mr1_def]
QED

Theorem extreal_dist_normal' :
    !x y. extreal_dist (Normal x) (Normal y) = 1 - inv (1 + abs (x - y))
Proof
    rw [extreal_dist_def, bounded_metric_thm, bounded_metric_alt, mr1_def]
QED

(* Use this theorem to calculate the "distance" between two normal extreals *)
Theorem extreal_mr1_normal :
    !x y. dist extreal_mr1 (Normal x,Normal y) = abs (x - y) / (1 + abs (x - y))
Proof
    rw [extreal_mr1_thm, extreal_dist_normal]
QED

Theorem extreal_mr1_normal' :
    !x y. dist extreal_mr1 (Normal x,Normal y) = 1 - inv (1 + abs (x - y))
Proof
    rw [extreal_mr1_thm, extreal_dist_normal']
QED

Theorem extreal_mr1_lt_1 :
    !x y. dist extreal_mr1 (Normal x,Normal y) < 1
Proof
    rw [extreal_mr1_thm, extreal_dist_normal']
 >> Suff ‘0 < inv (1 + abs (x - y))’ >- REAL_ARITH_TAC
 >> MATCH_MP_TAC REAL_INV_POS
 >> Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘1’ >> simp []
QED

Theorem extreal_mr1_le_1 :
    !x y. dist extreal_mr1 (x,y) <= 1
Proof
    rpt GEN_TAC
 >> Cases_on ‘x’ >> Cases_on ‘y’
 >> rw [extreal_mr1_thm, extreal_dist_def]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> rw [bounded_metric_lt_1]
QED

Theorem extreal_mr1_eq_1[simp] :
    dist extreal_mr1 (Normal r,PosInf) = 1 /\
    dist extreal_mr1 (Normal r,NegInf) = 1 /\
    dist extreal_mr1 (PosInf,Normal r) = 1 /\
    dist extreal_mr1 (NegInf,Normal r) = 1 /\
    dist extreal_mr1 (PosInf,NegInf) = 1 /\
    dist extreal_mr1 (NegInf,PosInf) = 1
Proof
    simp [extreal_mr1_thm, extreal_dist_def]
QED

Theorem dist_triangle_add :
    !x1 y1 x2 y2. dist extreal_mr1 (x1 + y1,x2 + y2) <=
                  dist extreal_mr1 (x1,x2) + dist extreal_mr1 (y1,y2)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x1 = PosInf’
 >- (Cases_on ‘y1 = PosInf’
     >- (simp [extreal_add_def] \\
         Cases_on ‘x2 = PosInf’
         >- (simp [MDIST_REFL] \\
             Cases_on ‘y2 = PosInf’ >- simp [MDIST_REFL, extreal_add_def] \\
             Cases_on ‘y2 = NegInf’ >- simp [extreal_mr1_le_1] \\
            ‘?r. y2 = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_add_def, MDIST_REFL, MDIST_POS_LE]) \\
         Cases_on ‘x2 = NegInf’
         >- (simp [] \\
             Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
             simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1]) \\
        ‘?r. x2 = Normal r’ by METIS_TAC [extreal_cases] \\
         simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1]) \\
     Cases_on ‘y1 = NegInf’
     >- (simp [] \\
         Cases_on ‘x2 = PosInf’
         >- (simp [MDIST_REFL] \\
             Cases_on ‘y2 = PosInf’ >- simp [extreal_mr1_le_1] \\
             Cases_on ‘y2 = NegInf’ >- simp [MDIST_REFL, extreal_add_def] \\
            ‘?r. y2 = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_add_def, extreal_mr1_le_1]) \\
         Cases_on ‘x2 = NegInf’
         >- (simp [] \\
             Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
             simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1]) \\
        ‘?r. x2 = Normal r’ by METIS_TAC [extreal_cases] \\
         simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1]) \\
    ‘?r. y1 = Normal r’ by METIS_TAC [extreal_cases] \\
     simp [extreal_add_def] \\
     Cases_on ‘y2 = PosInf’
     >- (simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDL, MDIST_POS_LE, extreal_mr1_le_1]) \\
     Cases_on ‘y2 = NegInf’
     >- (simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDL, MDIST_POS_LE, extreal_mr1_le_1]) \\
    ‘?z. y2 = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     Cases_on ‘x2 = NegInf’
     >- (simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1]) \\
     Cases_on ‘x2 = PosInf’ >- simp [extreal_add_def, MDIST_POS_LE] \\
    ‘?a. x2 = Normal a’ by METIS_TAC [extreal_cases] \\
     simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
     simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1])
 >> Cases_on ‘x1 = NegInf’
 >- (POP_ORW \\
     Cases_on ‘x2 = PosInf’
     >- (simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1]) \\
     Cases_on ‘x2 = NegInf’
     >- (simp [MDIST_REFL] \\
         Cases_on ‘y1 = PosInf’
         >- (POP_ORW \\
             Cases_on ‘y2 = PosInf’ >- simp [MDIST_REFL] \\
             Cases_on ‘y2 = NegInf’ >- simp [extreal_mr1_le_1] \\
            ‘?r. y2 = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_mr1_le_1]) \\
         Cases_on ‘y1 = NegInf’
         >- (simp [extreal_add_def] \\
             Cases_on ‘y2 = PosInf’ >- simp [extreal_mr1_le_1] \\
             Cases_on ‘y2 = NegInf’ >- simp [extreal_add_def] \\
            ‘?r. y2 = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_add_def, extreal_mr1_le_1]) \\
        ‘?r. y1 = Normal r’ by METIS_TAC [extreal_cases] \\
         simp [extreal_add_def] \\
         Cases_on ‘y2 = PosInf’ >- simp [extreal_mr1_le_1] \\
         Cases_on ‘y2 = NegInf’ >- simp [extreal_mr1_le_1] \\
        ‘?z. y2 = Normal z’ by METIS_TAC [extreal_cases] \\
         simp [extreal_add_def, MDIST_REFL, MDIST_POS_LE]) \\
    ‘?r. x2 = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
     simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1])
 >> ‘?a. x1 = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> Cases_on ‘x2 = PosInf’
 >- (simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
     simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1])
 >> Cases_on ‘x2 = NegInf’
 >- (simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
     simp [REAL_LE_ADDR, MDIST_POS_LE, extreal_mr1_le_1])
 >> ‘?c. x2 = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> Cases_on ‘y1 = PosInf’
 >- (simp [extreal_add_def] \\
     Cases_on ‘y2 = PosInf’ >- simp [extreal_add_def, MDIST_POS_LE] \\
     Cases_on ‘y2 = NegInf’
     >- (simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDL, MDIST_POS_LE, extreal_mr1_le_1]) \\
    ‘?r. y2 = Normal r’ by METIS_TAC [extreal_cases] \\
     simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
     simp [REAL_LE_ADDL, MDIST_POS_LE, extreal_mr1_le_1])
 >> Cases_on ‘y1 = NegInf’
 >- (simp [extreal_add_def] \\
     Cases_on ‘y2 = PosInf’
     >- (simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
         simp [REAL_LE_ADDL, MDIST_POS_LE, extreal_mr1_le_1]) \\
     Cases_on ‘y2 = NegInf’ >- simp [extreal_add_def, MDIST_REFL, MDIST_POS_LE] \\
    ‘?z. y2 = Normal z’ by METIS_TAC [extreal_cases] \\
     simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1’ \\
     simp [REAL_LE_ADDL, MDIST_POS_LE, extreal_mr1_le_1])
 >> ‘?b. y1 = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> Cases_on ‘y2 = PosInf’ >- simp [extreal_add_def, MDIST_POS_LE]
 >> Cases_on ‘y2 = NegInf’ >- simp [extreal_add_def, MDIST_POS_LE]
 >> ‘?d. y2 = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> KILL_TAC
 >> simp [extreal_add_def, extreal_mr1_thm, extreal_dist_normal']
 >> qmatch_abbrev_tac ‘_ <= _ - x + (_ - y :real)’
 >> simp [REAL_ARITH “1 - x + (1 - y) = 1 - (x + y - (1 :real))”]
 >> REWRITE_TAC [REAL_LE_SUB_CANCEL1]
 >> REWRITE_TAC [REAL_ADD2_SUB2]
 >> qunabbrevl_tac [‘x’, ‘y’]
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘inv (1 + abs (a - c) + abs (b - d))’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_INV_LE_ANTIMONO_IMPR \\
     CONJ_TAC
     >- (REWRITE_TAC [GSYM REAL_ADD_ASSOC] \\
         MATCH_MP_TAC REAL_LTE_ADD >> simp [REAL_LE_ADD, ABS_POS]) \\
     CONJ_TAC
     >- (MATCH_MP_TAC REAL_LTE_ADD >> simp [ABS_POS]) \\
     REWRITE_TAC [GSYM REAL_ADD_ASSOC, REAL_LE_LADD] \\
     REWRITE_TAC [ABS_TRIANGLE])
 >> qmatch_abbrev_tac ‘_ <= inv (1 + x + (y :real))’
 >> REWRITE_TAC [REAL_LE_SUB_RADD]
 >> REWRITE_TAC [REAL_INV_1OVER]
 >> Know ‘0 < 1 + x /\ 0 < 1 + y’
 >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC REAL_LTE_ADD >> simp [Abbr ‘x’, Abbr ‘y’, ABS_POS])
 >> STRIP_TAC
 >> ‘1 + x <> 0 /\ 1 + y <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ASM_SIMP_TAC real_ss [RAT_LEMMA2]
 >> ASM_SIMP_TAC real_ss [GSYM REAL_MUL_ASSOC, GSYM REAL_INV_MUL]
 >> ‘1 / (1 + x + y) + 1 = 1 / (1 + x + y) + 1 / 1’ by simp [] >> POP_ORW
 >> Know ‘0 < 1 + x + y’
 >- (REWRITE_TAC [GSYM REAL_ADD_ASSOC] \\
     MATCH_MP_TAC REAL_LTE_ADD \\
     simp [Abbr ‘x’, Abbr ‘y’, REAL_LE_ADD, ABS_POS])
 >> DISCH_TAC
 >> ‘0 < (1 :real)’ by simp []
 >> ASM_SIMP_TAC std_ss [RAT_LEMMA2]
 >> ‘1 + x + y <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> simp [REAL_ADD_ASSOC]
 >> ‘1 + y + 1 + x = 2 + x + (y :real)’ by REAL_ARITH_TAC >> POP_ORW
 >> qabbrev_tac ‘z = 2 + x + y’
 >> MATCH_MP_TAC REAL_LE_RMUL_IMP
 >> ‘0 <= x /\ 0 <= y’ by simp [Abbr ‘x’, Abbr ‘y’, ABS_POS]
 >> CONJ_TAC
 >- (simp [Abbr ‘z’, GSYM REAL_ADD_ASSOC] \\
     MATCH_MP_TAC REAL_LE_ADD >> simp [] \\
     MATCH_MP_TAC REAL_LE_ADD >> simp [])
 >> simp [REAL_LDISTRIB, REAL_RDISTRIB, GSYM REAL_ADD_ASSOC]
 >> REWRITE_TAC [Once REAL_ADD_COMM]
 >> simp []
 >> MATCH_MP_TAC REAL_LE_MUL >> art []
QED

(* cf. real_topologyTheory.euclidean_def *)
Definition ext_euclidean_def :
    ext_euclidean = mtop extreal_mr1
End

Theorem topspace_ext_euclidean :
    topspace ext_euclidean = UNIV
Proof
    rw [TOPSPACE_MTOP, ext_euclidean_def]
QED

Theorem mspace_extreal_mr1 :
    mspace extreal_mr1 = UNIV
Proof
    rw [mspace, GSYM ext_euclidean_def, topspace_ext_euclidean]
QED

(* ------------------------------------------------------------------------- *)
(* Limits of extreal functions ('a -> extreal) and continuous functions      *)
(* ------------------------------------------------------------------------- *)

Definition ext_tendsto :
    ext_tendsto = limit ext_euclidean
End
Overload "-->" = “ext_tendsto”

Theorem ext_tendsto_def :
    !f l net. ext_tendsto f l net <=>
             !e. &0 < e ==> eventually (\x. dist extreal_mr1 (f(x),l) < e) net
Proof
    rw [ext_tendsto, ext_euclidean_def, limit, TOPSPACE_MTOP]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.PAT_X_ASSUM ‘!u. open_in (mtop extreal_mr1) u /\ l IN u ==> P’
       (MP_TAC o Q.SPEC ‘mball extreal_mr1 (l,e)’) \\
     simp [OPEN_IN_MBALL, IN_MBALL, mspace_extreal_mr1] \\
     rw [MDIST_REFL, Once METRIC_SYM])
 >> fs [OPEN_IN_MTOPOLOGY, mspace_extreal_mr1]
 >> Q.PAT_X_ASSUM ‘!x. x IN u ==> P’ (MP_TAC o Q.SPEC ‘l’) >> rw []
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’  (MP_TAC o Q.SPEC ‘r’) >> rw []
 >> MATCH_MP_TAC EVENTUALLY_MONO
 >> Q.EXISTS_TAC ‘\x. dist extreal_mr1 (f x,l) < r’ >> rw []
 >> fs [SUBSET_DEF, IN_MBALL, mspace_extreal_mr1]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [Once METRIC_SYM]
QED

(* see EXTREAL_LIM which corresponds real_topologyTheory.LIM_DEF *)
Definition extreal_lim_def :
    extreal_lim net f = @l. ext_tendsto f l net
End
Overload lim = “extreal_lim”

Theorem EXTREAL_LIM :
    !(f :'a -> extreal) l net.
       (f --> l) net <=>
        trivial_limit net \/
        !e. &0 < e ==> ?y. (?x. netord(net) x y) /\
                           !x. netord(net) x y ==> dist extreal_mr1(f(x),l) < e
Proof
    rw [ext_tendsto_def, eventually] >> PROVE_TAC []
QED

Theorem EXTREAL_LIM_CONST :
    !net (a :extreal). ((\x. a) --> a) net
Proof
    rw [EXTREAL_LIM, trivial_limit, MDIST_REFL]
 >> METIS_TAC []
QED

(* NOTE: This proof is derived from real_topologyTheory.LIM_ADD *)
Theorem EXTREAL_LIM_ADD :
    !net:('a)net f g l (m :extreal).
       (f --> l) net /\ (g --> m) net ==> ((\x. f(x) + g(x)) --> (l + m)) net
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTREAL_LIM] THEN
  ASM_CASES_TAC ``trivial_limit (net:('a)net)`` THEN
  ASM_SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
  DISCH_TAC THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2:real``) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  qabbrev_tac ‘dist' = dist extreal_mr1’ \\
  Know `!x y. (dist'(f x, l) < e / 2:real) =
              (\x. (dist'(f x, l) < e / 2:real)) x` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  Know `!x y. (dist'(g x, m) < e / 2:real) =
              (\x. (dist'(g x, m) < e / 2:real)) x` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA) THEN BETA_TAC THEN
  STRIP_TAC THEN EXISTS_TAC ``c:'a`` THEN CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `x'`) THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  Q.EXISTS_TAC `dist' (f x', l) + dist' (g x', m)` THEN
  reverse CONJ_TAC
  >- METIS_TAC[REAL_LT_HALF1, REAL_LT_ADD2, GSYM REAL_HALF_DOUBLE] \\
  simp [Abbr ‘dist'’, dist_triangle_add]
QED

(* Name convention: "EXTREAL_" + (theorem name as in real_topologyTheory)

   e.g. cf. LIM_SEQUENTIALLY for EXTREAL_LIM_SEQUENTIALLY below:
 *)
Theorem EXTREAL_LIM_SEQUENTIALLY :
    !(f :num -> extreal) l. (f --> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> dist extreal_mr1 (f n,l) < e
Proof
    rw [ext_tendsto_def, EVENTUALLY_SEQUENTIALLY] >> PROVE_TAC []
QED

Theorem EXTREAL_LIM_EVENTUALLY :
    !net (f :'a -> extreal) l. eventually (\x. f x = l) net ==> (f --> l) net
Proof
    rw [eventually, EXTREAL_LIM] >> PROVE_TAC [METRIC_SAME]
QED

Theorem lim_sequentially_imp_extreal_lim :
    !f l. (f --> l) sequentially ==> (Normal o f --> Normal l) sequentially
Proof
    RW_TAC std_ss [LIM_SEQUENTIALLY, EXTREAL_LIM_SEQUENTIALLY,
                   extreal_mr1_normal, dist]
 >> ‘1 <= e \/ e < 1’ by PROVE_TAC [REAL_LET_TOTAL]
 >- (Q.EXISTS_TAC ‘0’ >> rw [] \\
     MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC ‘1’ >> art [] \\
     MATCH_MP_TAC REAL_LT_1 >> rw [])
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o Q.SPEC ‘e / (1 - e)’)
 >> Know ‘0 < e / (1 - e)’
 >- (MATCH_MP_TAC REAL_LT_DIV >> rw [REAL_SUB_LT])
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘N’ >> rw []
 >> Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o Q.SPEC ‘n’)
 >> RW_TAC std_ss []
 >> Q.ABBREV_TAC ‘x = abs (f n - l)’
 >> ‘0 <= x’ by METIS_TAC [ABS_POS]
 >> Know ‘x / (1 + x) < e <=> x < e * (1 + x)’
 >- (MATCH_MP_TAC REAL_LT_LDIV_EQ \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [REAL_LE_ADDR])
 >> Rewr'
 >> rw [REAL_ADD_LDISTRIB, GSYM REAL_LT_SUB_RADD]
 >> ‘x - e * x = 1 * x - e * x’ by rw [] >> POP_ORW
 >> REWRITE_TAC [GSYM REAL_SUB_RDISTRIB]
 >> Suff ‘x < e / (1 - e) <=> x * (1 - e) < e’ >- PROVE_TAC [REAL_MUL_COMM]
 >> MATCH_MP_TAC REAL_LT_RDIV_EQ
 >> rw [REAL_SUB_LT]
QED

Theorem extreal_lim_sequentially_imp_real_lim[local] :
    !f l. (?N. !n. N <= n ==> f n <> PosInf /\ f n <> NegInf) /\
          l <> PosInf /\ l <> NegInf /\ (f --> l) sequentially ==>
          (real o f --> real l) sequentially
Proof
    RW_TAC std_ss [LIM_SEQUENTIALLY, EXTREAL_LIM_SEQUENTIALLY, dist]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o Q.SPEC ‘e / (1 + e)’)
 >> ‘e <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> Know ‘0 < 1 + e’
 >- (MATCH_MP_TAC REAL_LT_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [])
 >> DISCH_TAC
 >> ‘1 + e <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ‘0 < e / (1 + e)’ by PROVE_TAC [REAL_LT_DIV]
 >> RW_TAC std_ss []
 >> Q.ABBREV_TAC ‘M = MAX N N'’
 >> Q.EXISTS_TAC ‘M’
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!n. N' <= n ==> P’ (MP_TAC o Q.SPEC ‘n’)
 >> Know ‘N' <= n’
 >- (MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘M’ >> rw [Abbr ‘M’])
 >> ‘?r. l = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o Q.SPEC ‘n’)
 >> Know ‘N <= n’
 >- (MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘M’ >> rw [Abbr ‘M’])
 >> RW_TAC std_ss []
 >> ‘?z. f n = Normal z’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fn th => fs [th, extreal_mr1_normal])
 >> Q.ABBREV_TAC ‘y = e / (1 + e)’
 >> Know ‘e = y / (1 - y)’
 >- (rw [Abbr ‘y’] \\
     Know ‘1 - e / (1 + e) = (1 + e) / (1 + e) - e / (1 + e)’
     >- (Suff ‘(1 + e) / (1 + e) = 1’ >- rw [] \\
         MATCH_MP_TAC REAL_DIV_REFL >> art []) >> Rewr' \\
     rw [REAL_DIV_SUB, REAL_ADD_SUB_ALT, GSYM REAL_INV_1OVER, REAL_INV_INV])
 >> Rewr'
 >> Q.ABBREV_TAC ‘a = abs (z - r)’
 >> Know ‘a < y / (1 - y) <=> a * (1 - y) < y’
 >- (MATCH_MP_TAC REAL_LT_RDIV_EQ \\
     rw [REAL_SUB_LT, Abbr ‘y’])
 >> Rewr'
 >> rw [REAL_SUB_LDISTRIB, REAL_LT_SUB_RADD]
 >> ‘y + a * y = (1 + a) * y’ by REAL_ARITH_TAC >> POP_ORW
 >> Suff ‘a / (1 + a) < y <=> a < y * (1 + a)’ >- PROVE_TAC [REAL_MUL_COMM]
 >> MATCH_MP_TAC REAL_LT_LDIV_EQ
 >> MATCH_MP_TAC REAL_LTE_TRANS
 >> Q.EXISTS_TAC ‘1’ >> rw [Abbr ‘a’]
QED

Theorem extreal_lim_sequentially_eq :
    !f l. (?N. !n. N <= n ==> f n <> PosInf /\ f n <> NegInf) /\
          l <> PosInf /\ l <> NegInf ==>
         ((f --> l) sequentially <=> (real o f --> real l) sequentially)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (MATCH_MP_TAC extreal_lim_sequentially_imp_real_lim >> rw [] \\
     Q.EXISTS_TAC ‘N’ >> rw [])
 (* applying lim_sequentially_imp_extreal_lim *)
 >> ‘?r. l = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fn th => fs [th, real_normal])
 >> Q.ABBREV_TAC ‘g = Normal o real o f’
 >> Know ‘(g --> Normal r) sequentially’
 >- (Q.UNABBREV_TAC ‘g’ \\
     MATCH_MP_TAC lim_sequentially_imp_extreal_lim >> art [])
 >> rw [EXTREAL_LIM_SEQUENTIALLY]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o Q.SPEC ‘e’)
 >> RW_TAC std_ss []
 >> Q.ABBREV_TAC ‘M = MAX N N'’
 >> Q.EXISTS_TAC ‘M’ >> rw []
 >> Suff ‘f n = g n’
 >- (Rewr' >> FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC LESS_EQ_TRANS >> Q.EXISTS_TAC ‘M’ >> rw [Abbr ‘M’])
 >> rw [Abbr ‘g’, Once EQ_SYM_EQ]
 >> MATCH_MP_TAC normal_real
 >> Suff ‘N <= n’ >- rw []
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC ‘M’ >> rw [Abbr ‘M’]
QED

Theorem extreal_lim_sequentially_eq' :
    !f r. (?N. !n. N <= n ==> f n <> PosInf /\ f n <> NegInf) ==>
         ((f --> Normal r) sequentially <=> (real o f --> r) sequentially)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘Normal r’] extreal_lim_sequentially_eq)
 >> rw [real_normal]
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘N’ >> rw []
QED

(* ------------------------------------------------------------------------- *)
(*  Various definitions of bounded and continuous functions                  *)
(* ------------------------------------------------------------------------- *)

Definition ext_continuous_def :
    ext_continuous (f :'a -> extreal) net <=> ext_tendsto f (f (netlimit net)) net
End

Definition ext_continuous_on_def :
    ext_continuous_on f s <=> !x. x IN s ==> ext_continuous f (at x within s)
End

(* Use ‘ext_bounded (IMAGE f UNIV)’ to say a function f is bounded (on UNIV) *)
Definition ext_bounded_def :
    ext_bounded s <=> ?a. a <> PosInf /\ !x. x IN s ==> abs x <= a
End

Theorem ext_bounded_alt :
    !s. ext_bounded s <=> ?k. 0 <= k /\ !x. x IN s ==> abs x <= Normal k
Proof
    rw [ext_bounded_def]
 >> reverse EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘Normal k’ >> rw [])
 >> Cases_on ‘s = {}’
 >- (rw [] >> Q.EXISTS_TAC ‘0’ >> rw [])
 >> Know ‘0 <= a’
 >- (fs [GSYM MEMBER_NOT_EMPTY] \\
     Q_TAC (TRANS_TAC le_trans) ‘abs x’ >> rw [abs_pos])
 >> DISCH_TAC
 >> ‘a <> NegInf’ by rw [pos_not_neginf]
 >> ‘?k. a = Normal k /\ 0 <= k’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq]
 >> Q.EXISTS_TAC ‘k’ >> rw []
QED

Theorem sup_normal' :
    !s. ext_bounded s /\ s <> {} ==> Normal (sup (s o Normal)) = sup s
Proof
    rw [ext_bounded_alt]
 >> MATCH_MP_TAC sup_normal
 >> Q.EXISTS_TAC ‘k’
 >> MATCH_MP_TAC sup_bounded_alt >> art []
QED

(* NOTE: “sup (s :real set)” doesn't exist (i.e. unspecified) when “s = {}” *)
Theorem sup_image_normal :
    !s. s <> {} /\ bounded s ==> sup (IMAGE Normal s) = Normal (sup s)
Proof
    Q.X_GEN_TAC ‘t’ >> rw [bounded_alt]
 >> qabbrev_tac ‘s = IMAGE Normal t’
 >> MP_TAC (Q.SPEC ‘s’ sup_normal')
 >> impl_tac
 >- (reverse CONJ_TAC >- rw [Once EXTENSION, NOT_IN_EMPTY, Abbr ‘s’] \\
     rw [ext_bounded_def, Abbr ‘s’] \\
     Q.EXISTS_TAC ‘Normal a’ >> rw [] \\
     simp [extreal_abs_def, extreal_le_eq])
 >> DISCH_THEN (REWRITE_TAC o wrap o SYM)
 >> AP_TERM_TAC
 >> simp [Abbr ‘s’, o_DEF, IN_APP, ETA_AX]
QED

(* NOTE: This is the general definition actually used in converge_in_dist_def *)
Definition bounded_continuous_def :
    bounded_continuous top (f :'a -> real) <=>
    continuous_map (top,euclidean) f /\ bounded (IMAGE f UNIV)
End
Overload C_b = “bounded_continuous”

Theorem IN_bounded_continuous :
    !top f. f IN C_b top <=>
            continuous_map (top,euclidean) f /\ bounded (IMAGE f UNIV)
Proof
    REWRITE_TAC [IN_APP, bounded_continuous_def]
QED

Theorem continuous_map_normal :
    continuous_map (euclidean,ext_euclidean) Normal
Proof
    rw [euclidean_def, ext_euclidean_def, METRIC_CONTINUOUS_MAP, MSPACE]
 >> Cases_on ‘1 <= e’
 >- (Q.EXISTS_TAC ‘1’ >> rw [] \\
     Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘1’ >> art [] \\
     simp [extreal_mr1_lt_1])
 >> fs [REAL_NOT_LE]
 >> simp [extreal_mr1_normal', GSYM dist_def, dist]
 >> ‘!x. 1 - inv (1 + abs (a - x)) < e <=> 1 - e < inv (1 + abs (a - x))’
      by REAL_ARITH_TAC >> POP_ORW
 >> ‘1 - e <> 0’ by REAL_ASM_ARITH_TAC
 >> ‘1 - e = inv (inv (1 - e))’ by simp [REAL_INVINV]
 >> POP_ORW
 >> Know ‘!x. inv (inv (1 - e)) < inv (1 + abs (a - x)) <=>
              1 + abs (a - x) < inv (1 - e)’
 >- (Q.X_GEN_TAC ‘x’ \\
     MATCH_MP_TAC REAL_INV_LT_ANTIMONO \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_INV_POS >> simp [REAL_SUB_LT]) \\
     Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘1’ >> simp [])
 >> Rewr'
 >> ‘!x. 1 + abs (a - x) < inv (1 - e) <=> abs (a - x) < inv (1 - e) - 1’
      by REAL_ARITH_TAC >> POP_ORW
 >> Q.EXISTS_TAC ‘inv (1 - e) - 1’ >> simp [REAL_SUB_LT]
 >> REAL_ASM_ARITH_TAC
QED

Theorem continuous_map_real :
    continuous_map (ext_euclidean,euclidean) real
Proof
    rw [euclidean_def, ext_euclidean_def, METRIC_CONTINUOUS_MAP, MSPACE,
        GSYM dist_def, dist]
 >> Cases_on ‘a = PosInf’
 >- (POP_ASSUM (simp o wrap) \\
     Q.EXISTS_TAC ‘1’ >> rw [] \\
     Cases_on ‘x = PosInf’ >- simp [] \\
     Cases_on ‘x = NegInf’ >- simp [] \\
    ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> fs [])
 >> Cases_on ‘a = NegInf’
 >- (POP_ASSUM (simp o wrap) \\
     Q.EXISTS_TAC ‘1’ >> rw [] \\
     Cases_on ‘x = PosInf’ >- simp [] \\
     Cases_on ‘x = NegInf’ >- simp [] \\
    ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> fs [])
 (* stage work *)
 >> ‘?r. a = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (simp o wrap)
 >> Suff ‘?d. 0 < d /\ d < 1 /\
              !y. dist extreal_mr1 (Normal r,Normal y) < d ==> abs (r - y) < e’
 >- (STRIP_TAC \\
     Q.EXISTS_TAC ‘d’ >> rw [] \\
    ‘dist extreal_mr1 (Normal r,x) < 1’ by PROVE_TAC [REAL_LT_TRANS] \\
    ‘dist extreal_mr1 (Normal r,x) <> 1’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     Cases_on ‘x = PosInf’ >- fs [] \\
     Cases_on ‘x = NegInf’ >- fs [] \\
    ‘?z. x = Normal z’ by METIS_TAC [extreal_cases] \\
     POP_ASSUM (fs o wrap))
 >> simp [extreal_mr1_normal']
 (* NOTE: Below we try to prove a serious of inequations to obtain the
    expression of “d” by the existing value “e”.
  *)
 >> ‘!d y. 1 - inv (1 + abs (r - y)) < d <=> 1 - d < inv (1 + abs (r - y))’
      by REAL_ARITH_TAC >> POP_ORW
 >> Know ‘!(d :real). d < 1 ==> 1 - d = inv (inv (1 - d))’
 >- (rpt STRIP_TAC \\
     SYM_TAC >> MATCH_MP_TAC REAL_INVINV \\
     REAL_ASM_ARITH_TAC)
 >> DISCH_TAC
 >> Know ‘!d y. d < 1 ==>
               (inv (inv (1 - d)) < inv (1 + abs (r - y)) <=>
                1 + abs (r - y) < inv (1 - d))’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC REAL_INV_LT_ANTIMONO \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_INV_POS >> simp [REAL_SUB_LT]) \\
     Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘1’ >> simp [])
 >> DISCH_TAC
 >> ‘!d y. 1 + abs (r - y) < inv (1 - d) <=> abs (r - y) < inv (1 - d) - 1’
      by REAL_ARITH_TAC
 >> Know ‘!d. inv (1 - d) - 1 = e <=> inv (1 - d) = e + 1’
 >- REAL_ARITH_TAC
 >> Know ‘e + 1 = inv (inv (e + 1))’
 >- (SYM_TAC >> MATCH_MP_TAC REAL_INVINV \\
     Q.PAT_X_ASSUM ‘0 < e’ MP_TAC >> REAL_ARITH_TAC)
 >> Rewr'
 >> simp [REAL_INV_INJ]
 >> ‘!d. 1 - d = inv (e + 1) <=> d = 1 - inv (e + 1)’ by REAL_ARITH_TAC
 >> POP_ORW
 >> DISCH_TAC
 (* stage work *)
 >> qabbrev_tac ‘d = 1 - inv (e + 1)’
 >> Q.EXISTS_TAC ‘d’
 >> CONJ_TAC
 >- (simp [Abbr ‘d’, REAL_SUB_LT] \\
     MATCH_MP_TAC REAL_INV_GT1 >> simp [])
 >> CONJ_ASM1_TAC
 >- (qunabbrev_tac ‘d’ \\
     Suff ‘0 < inv (e + 1)’ >- REAL_ARITH_TAC \\
     MATCH_MP_TAC REAL_INV_POS \\
     Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘1’ >> simp [])
 >> Q.X_GEN_TAC ‘y’
 >> Q.PAT_X_ASSUM ‘!d. d < 1 ==> 1 - d = inv (inv (1 - d))’
      (MP_TAC o Q.SPEC ‘d’)
 >> impl_tac >- art []
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘!d y. d < 1 ==> (inv (inv (1 - d)) < inv (1 + abs (r - y)) <=> _)’
      (MP_TAC o Q.SPECL [‘d’, ‘y’])
 >> impl_tac >- art []
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘!d y. 1 + abs (r - y) < inv (1 - d) <=> _’
      (MP_TAC o Q.SPECL [‘d’, ‘y’])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘!d. inv (1 - d) - 1 = e <=> _’ (MP_TAC o Q.SPEC ‘d’)
 >> simp []
QED

(* NOTE: “|- Lipschitz_continuous_map (extreal_mr1,mr1) real” doesn't hold *)
Theorem Lipschitz_continuous_map_normal :
     Lipschitz_continuous_map (mr1,extreal_mr1) Normal
Proof
    rw [Lipschitz_continuous_map_def, GSYM dist_def, dist]
 >> Q.EXISTS_TAC ‘1’ >> rw []
 >> rw [extreal_mr1_normal]
 >> MATCH_MP_TAC REAL_LE_LDIV
 >> qabbrev_tac ‘z = abs (x - y)’
 >> simp [REAL_LDISTRIB]
 >> Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘1’ >> rw [Abbr ‘z’]
QED

(* ------------------------------------------------------------------------- *)
(*  Preliminary for Radon-Nikodym Theorem                                    *)
(* ------------------------------------------------------------------------- *)

Definition seq_sup_def :
   (seq_sup P 0       = @r. r IN P /\ sup P < r + 1) /\
   (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + Normal ((1 / 2) pow (SUC n)) /\
                           (seq_sup P n) < r /\ r < sup P)
End

Theorem EXTREAL_SUP_SEQ :
   !P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
        ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)
Proof
  RW_TAC std_ss []
  >> Cases_on `?z. P z /\ (z = sup P)`
  >- (Q.EXISTS_TAC `(\i. sup P)`
      >> RW_TAC std_ss [le_refl,SPECIFICATION]
      >> `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)`
           by RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS]
      >> RW_TAC std_ss [sup_const])
  >> Cases_on `!x. P x ==> (x = NegInf)`
  >- (`sup P = NegInf` by METIS_TAC [sup_const_alt]
      >> Q.EXISTS_TAC `(\n. NegInf)`
      >> FULL_SIMP_TAC std_ss [le_refl]
      >> RW_TAC std_ss []
      >- METIS_TAC []
      >> METIS_TAC [UNIV_NOT_EMPTY,sup_const_over_set])
  >> FULL_SIMP_TAC std_ss []
  >> Q.EXISTS_TAC `seq_sup P`
  >> FULL_SIMP_TAC std_ss []
  >> `sup P <> PosInf` by METIS_TAC [sup_le,lt_infty,let_trans]
  >> `!x. P x ==> x < sup P` by METIS_TAC [lt_le,le_sup_imp]
  >> `!e. 0 < e ==> ?x. P x /\ sup P < x + e`
       by (RW_TAC std_ss [] >> MATCH_MP_TAC sup_lt_epsilon >> METIS_TAC [])
  >> `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS,REAL_POW_LT]
  >> `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
  >> `!n. seq_sup P n IN P`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >> METIS_TAC [lt_01,SPECIFICATION])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >> `?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
          >> rename1 `seq_sup P n < x2`
          >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          >> rename1 `sup P < x3 + _`
          >> Q.EXISTS_TAC `max x2 x3`
          >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              >> `x3 +  Normal ((1 / 2) pow (SUC n)) <= x2 +  Normal ((1 / 2) pow (SUC n))`
                  by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lte_trans])
  >> `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> rename1 `sup_sup P n < x2`
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> rename1 `sup P < x3 + _`
              >> Q.EXISTS_TAC `max x2 x3`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x3 + Normal ((1 / 2) pow (SUC n)) <= x2 + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss []
  >> `!n. sup P <= seq_sup P n + Normal ((1 / 2) pow n)`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def,pow,GSYM extreal_of_num_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >- METIS_TAC [lt_01,SPECIFICATION]
              >> METIS_TAC [lt_le])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> rename1 `sup_sup P n < x2`
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> rename1 `sup P < x3 + _`
              >> Q.EXISTS_TAC `max x2 x3`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x3 + Normal ((1 / 2) pow (SUC n)) <= x2 + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [SPECIFICATION,lt_le])
  >> MATCH_MP_TAC le_epsilon
  >> RW_TAC std_ss []
  >> `e <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lt_trans]
  >> `?r. e = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss []
  >> `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW2_INV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC le_add2
  >> FULL_SIMP_TAC std_ss [lt_le]
  >> Q.PAT_X_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> METIS_TAC []
QED

Theorem EXTREAL_SUP_FUN_SEQ_IMAGE :
    !(P:extreal->bool) (P':('a->extreal)->bool) f.
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')
           ==> ?g. (!n:num. g n IN P') /\
                   (sup (IMAGE (\n. f (g n)) UNIV) = sup P)
Proof
  rpt STRIP_TAC
  >> `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)`
     by METIS_TAC [EXTREAL_SUP_SEQ]
  >> Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
  >> `(\n. f (@(r :'a -> extreal). r IN (P' :('a -> extreal) -> bool) /\
                                  ((f :('a -> extreal) -> extreal) r = (y :num -> extreal) n))) = y`
  by (rw [FUN_EQ_THM] >> SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE])
  >> ASM_SIMP_TAC std_ss []
  >> RW_TAC std_ss []
  >> SELECT_ELIM_TAC
  >> RW_TAC std_ss []
  >> METIS_TAC [IN_IMAGE]
QED

Theorem EXTREAL_SUP_FUN_SEQ_MONO_IMAGE :
    !f (P :extreal->bool) (P' :('a->extreal)->bool).
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
       (!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
       (!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
      ==>
       ?g. (!n. g n IN P') /\ (!x n. g n x <= g (SUC n) x) /\
           (sup (IMAGE (\n. f (g n)) UNIV) = sup P)
Proof
    rpt STRIP_TAC
  >> `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)`
      by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  >> Q.EXISTS_TAC `max_fn_seq g`
  >> `!n. max_fn_seq g n IN P'`
      by (Induct
          >- (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> METIS_TAC [])
              >> `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))`
                  by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> RW_TAC std_ss []
              >> METIS_TAC [])
  >> `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x`
      by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC >- RW_TAC std_ss []
  >> `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >- RW_TAC std_ss [max_fn_seq_def,le_refl]
          >> METIS_TAC [le_max2,max_fn_seq_def])
  >> `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  >> `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC sup_le_sup_imp
          >> RW_TAC std_ss []
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> Q.EXISTS_TAC `f (max_fn_seq g n)`
          >> RW_TAC std_ss []
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (RW_TAC std_ss [sup_le]
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> MATCH_MP_TAC le_sup_imp
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE]
          >> METIS_TAC [])
  >> METIS_TAC [le_antisym]
QED

(************************************************************************)
(*   Miscellaneous Results (generally for use in descendent theories)   *)
(************************************************************************)

(*  I add these results at the end
      in order to manipulate the simplifier without breaking anything
      - Jared Yeager                                                    *)

Theorem normal_minus1:
    Normal (-1) = -1
Proof
    rw [extreal_of_num_def, extreal_ainv_def]
QED

Theorem extreal_le_simps[simp]:
    (!x y. Normal x <= Normal y <=> x <= y) /\
    (!x. NegInf <= x <=> T) /\ (!x. x <= PosInf <=> T) /\
    (!x. Normal x <= NegInf <=> F) /\
    (!x. PosInf <= Normal x <=> F) /\
    (PosInf <= NegInf <=> F)
Proof
    rw[extreal_le_def] >> Cases_on ‘x’ >> simp[extreal_le_def]
QED

Theorem extreal_lt_simps[simp]:
    (!x y. Normal x < Normal y <=> x < y) /\
    (!x. x < NegInf <=> F) /\ (!x. PosInf < x <=> F) /\
    (!x. Normal x < PosInf <=> T) /\
    (!x. NegInf < Normal x <=> T) /\
    (NegInf < PosInf <=> T)
Proof
    simp[extreal_lt_eq] >> rw[extreal_lt_def]
QED

Theorem extreal_0_simps[simp]:
    (0 <= PosInf <=> T) /\ (0 < PosInf <=> T) /\
    (PosInf <= 0 <=> F) /\ (PosInf < 0 <=> F) /\
    (0 = PosInf <=> F) /\ (PosInf = 0 <=> F) /\
    (0 <= NegInf <=> F) /\ (0 < NegInf <=> F) /\
    (NegInf <= 0 <=> T) /\ (NegInf < 0 <=> T) /\
    (0 = NegInf <=> F) /\ (NegInf = 0 <=> F) /\
    (!r. 0 <= Normal r <=> 0 <= r) /\
    (!r. 0 < Normal r <=> 0 < r) /\ (!r. 0 = Normal r <=> r = 0) /\
    (!r. Normal r <= 0 <=> r <= 0) /\
    (!r. Normal r < 0 <=> r < 0) /\ (!r. Normal r = 0 <=> r = 0)
Proof
    simp[GSYM normal_0]
QED

Theorem extreal_1_simps[simp]:
    (1 <= PosInf <=> T) /\ (1 < PosInf <=> T) /\ (PosInf <= 1 <=> F) /\
    (PosInf < 1 <=> F) /\ (1 = PosInf <=> F) /\ (PosInf = 1 <=> F) /\
    (1 <= NegInf <=> F) /\ (1 < NegInf <=> F) /\ (NegInf <= 1 <=> T) /\
    (NegInf < 1 <=> T) /\ (1 = NegInf <=> F) /\ (NegInf = 1 <=> F) /\
    (!r. 1 <= Normal r <=> 1 <= r) /\
    (!r. 1 < Normal r <=> 1 < r) /\ (!r. 1 = Normal r <=> r = 1) /\
    (!r. Normal r <= 1 <=> r <= 1) /\
    (!r. Normal r < 1 <=> r < 1) /\ (!r. Normal r = 1 <=> r = 1)
Proof
    simp[GSYM normal_1]
QED

(* do NOT add to a simpset, way too much overhead *)
Theorem ineq_imp:
    (!x:extreal y. x < y ==> ~(y < x)) /\ (!x:extreal y. x < y ==> x <> y) /\
    (!x:extreal y. x < y ==> ~(y <= x)) /\ (!x:extreal y. x < y ==> x <= y) /\
    (!x:extreal y. x <= y ==> ~(y < x))
Proof
    rw[] >> Cases_on ‘x’ >> Cases_on ‘y’ >> fs[SF realSimps.REAL_ARITH_ss]
QED

Theorem fn_plus_alt:
    !f. fn_plus f = (λx. if 0 <= f x then f x else (0: extreal))
Proof
    rw[fn_plus_def,FUN_EQ_THM] >> qspecl_then [‘f x’,‘0’] assume_tac lt_total >>
    FULL_SIMP_TAC bool_ss [] >> simp[ineq_imp]
QED

Theorem extreal_pow_alt:
    (!x:extreal. x pow 0 = 1) /\
    (!n x:extreal. x pow (SUC n) = x pow n * x)
Proof
    simp[pow_0,ADD1,pow_add,pow_1]
QED

Theorem sqrt_real :
  !x. 0 <= x ==> real (sqrt x) = sqrt (real x)
Proof
  rpt STRIP_TAC
  >> ‘x <> NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
  >> Cases_on ‘x = PosInf’
  >- (gs [extreal_sqrt_def, real_def, GSYM SQRT_0])
  >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases]
  >> gs [real_normal, extreal_sqrt_def, normal_real]
  >> METIS_TAC [extreal_cases, real_normal]
QED

(*** EXTREAL_SUM_IMAGE Theorems ***)

Theorem EXTREAL_SUM_IMAGE_ALT_FOLDR:
    !f s. FINITE s ==>
          EXTREAL_SUM_IMAGE f s =
          FOLDR (λe acc. f e + acc) 0x (REVERSE (SET_TO_LIST s))
Proof
    simp[EXTREAL_SUM_IMAGE_DEF,ITSET_TO_FOLDR]
QED

Theorem EXTREAL_SUM_IMAGE_EQ':
    !f g s. FINITE s /\ (!x. x IN s ==> f x = g x) ==>
            EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE g s: extreal
Proof
    rw[] >> simp[EXTREAL_SUM_IMAGE_ALT_FOLDR] >> irule FOLDR_CONG >> rw[]
QED

Theorem EXTREAL_SUM_IMAGE_MONO':
    !f g s. FINITE s /\ (!x. x IN s ==> f x <= g x) ==>
            EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE g s: extreal
Proof
    ‘!f g l. (!e. MEM e l ==> f e <= g e) ==>
      (FOLDR (λe acc. f e + acc) 0x l <= FOLDR (λe acc. g e + acc) 0x l)’
        suffices_by rw[EXTREAL_SUM_IMAGE_ALT_FOLDR] >>
    Induct_on ‘l’ >> rw[FOLDR] >> irule le_add2 >> simp[]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT_ZERO[simp]:
    !f. EXTREAL_SUM_IMAGE f (count 0) = 0:extreal
Proof
    simp[COUNT_ZERO]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT_ONE[simp]:
    !f. EXTREAL_SUM_IMAGE f (count 1) = f 0:extreal
Proof
    simp[COUNT_ONE]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT_SUC:
    !f n. (!m. m <= n ==> f m <> NegInf) \/ (!m. m <= n ==> f m <> PosInf) ==>
          EXTREAL_SUM_IMAGE f (count (SUC n)) =
         (EXTREAL_SUM_IMAGE f (count n)) + f n:extreal
Proof
    rw[] >> ‘count (SUC n) = (count n) UNION {n}’ by fs[count_def,EXTENSION]
 >> rw[] >> pop_assum kall_tac
 >> ‘EXTREAL_SUM_IMAGE f (count n UNION {n}) =
     EXTREAL_SUM_IMAGE f (count n) + EXTREAL_SUM_IMAGE f {n}’
       suffices_by fs[EXTREAL_SUM_IMAGE_SING]
 >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp[]
QED

Theorem EXTREAL_SUM_IMAGE_CDIV :
  !s. FINITE s ==>
      !f c. ((!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf)) /\
            c <> 0 ==> SIGMA (λx. f x / Normal c) s = SIGMA f s / Normal c
Proof
   rw [extreal_div_def, extreal_inv_def, Once mul_comm]
 >> ‘SIGMA f s * Normal (inv c) = Normal (inv c) *  ∑ f s’ by rw [mul_comm]
 >> POP_ORW
 >> irule EXTREAL_SUM_IMAGE_CMUL
 >> art []
QED

Theorem EXTREAL_SUM_IMAGE_ABS_TRIANGLE :
    !f s. FINITE s ==> abs (SIGMA f s) <= SIGMA (λx. abs (f x)) s
Proof
    ‘!f l. (!x. MEM x l ==> T) ==>
           abs (FOLDR (λe acc. f e + acc) 0x l) <=
           FOLDR (λe acc. abs (f e) + acc) 0x l’
      suffices_by rw [EXTREAL_SUM_IMAGE_ALT_FOLDR]
 >> Induct_on ‘l’ >> rw[listTheory.FOLDR]
 >> ‘abs (f h + FOLDR (λe acc. f e + acc) 0x l)
     <= abs (f h) + abs (FOLDR (λe acc. f e + acc) 0x l)’
      by (irule abs_triangle_full >> simp[])
 >> ‘abs (FOLDR (λe acc. f e + acc) 0x l)
     <= FOLDR (λe acc. abs (f e) + acc) 0x l’ by simp[]
 >> ‘abs (f h) + abs (FOLDR (λe acc. f e + acc) 0x l)
     <= abs (f h) + FOLDR (λe acc. abs (f e) + acc) 0x l’ by (irule le_add2 >> simp[])
 >> METIS_TAC [le_trans]
QED

Theorem EXTREAL_SUM_IMAGE_ABS_LE :
    !f g s. FINITE s /\ (!x. x IN s ==> abs (f x) <= g x) ==>
            abs (SIGMA f s) <= SIGMA g s
Proof
    rpt STRIP_TAC
 >> ‘abs (SIGMA f s) <= SIGMA (λx. abs (f x)) s’
      by (irule EXTREAL_SUM_IMAGE_ABS_TRIANGLE >> rw[])
 >> ‘(!x. x IN s ==> (λx. abs (f x)) x <= g x)’ by simp[]
 >> ‘SIGMA (λx. abs (f x)) s <= SIGMA g s’ by (irule EXTREAL_SUM_IMAGE_MONO' >> rw[])
 >> METIS_TAC [le_trans]
QED

Theorem EXTREAL_SUM_IMAGE_REAL :
    !s f. FINITE s ==>
          (!x. x IN s ==> f x <> NegInf) /\ (!x. x IN s ==> f x <> PosInf) ==>
          SIGMA (λx. real (f x)) s = real (SIGMA f s)
Proof
    Induct_on ‘CARD s’ >> rw [o_DEF]
 >- (‘s = {}’ by METIS_TAC [CARD_EQ_0] \\
     gs [EXTREAL_SUM_IMAGE_EMPTY, real_0])
 >> MP_TAC (Q.SPEC ‘f’ EXTREAL_SUM_IMAGE_THM)
 >> Cases_on ‘s = {}’ >> rw [EXTREAL_SUM_IMAGE_EMPTY, real_0]
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> Q.ABBREV_TAC ‘t = s DELETE x’
 >> Q.PAT_X_ASSUM ‘!e s'. _’ (STRIP_ASSUME_TAC o Q.SPECL [‘x’, ‘t’])
 >> gs [FINITE_DELETE, Abbr ‘t’]
 >> ‘SIGMA f s = f x + SIGMA f (s DELETE x)’
       by (POP_ASSUM MATCH_MP_TAC >> METIS_TAC [])
 >> gs []
 >> Q.ABBREV_TAC ‘t = s DELETE x’
 >> Q.PAT_X_ASSUM ‘!s. v = CARD s ==> _’ (STRIP_ASSUME_TAC o Q.SPEC ‘t’)
 >> ‘v = CARD t’ by rw [Abbr ‘t’, CARD_DELETE] >> gs []
 >> Q.PAT_X_ASSUM ‘!f. FINITE t ==> _’ (STRIP_ASSUME_TAC o Q.SPEC ‘f’)
 >> ‘FINITE t’ by rw [Abbr ‘t’, FINITE_DELETE] >> gs []
 >> ‘s = x INSERT t’ by rw [Abbr ‘t’, INSERT_DELETE]
 >> POP_ORW
 >> MP_TAC (Q.SPECL [‘f x’, ‘SIGMA f t’] add_real)
 >> impl_tac
 >- (‘f x <> PosInf /\ f x <> NegInf’ by METIS_TAC [] >> simp [] \\
     ‘SIGMA f t = SIGMA f s - f x’ by (fs [] >> METIS_TAC [GSYM add_sub2]) \\
     POP_ORW \\
     ‘SIGMA f s <> PosInf /\ SIGMA f s <> NegInf’
        by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY] \\
     rw [sub_not_infty])
 >> Rewr
 >> MP_TAC (Q.SPEC ‘λx. real (f x)’ REAL_SUM_IMAGE_THM)
 >> rw [Abbr ‘t’, REAL_SUM_IMAGE_EMPTY]
 >> POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [‘x’, ‘s’])
 >> gs [o_DEF, ABSORPTION]
QED

(*** EXTREAL_PROD_IMAGE Theorems ***)

Theorem EXTREAL_PROD_IMAGE_NOT_INFTY:
    !f s. FINITE s /\ (!x. x IN s ==> f x <> NegInf /\ f x <> PosInf) ==>
        EXTREAL_PROD_IMAGE f s <> NegInf /\ EXTREAL_PROD_IMAGE f s <> PosInf
Proof
    strip_tac >> simp[Once $ GSYM AND_IMP_INTRO] >> Induct_on ‘s’ >> CONJ_TAC
    >- simp[EXTREAL_PROD_IMAGE_EMPTY,SYM normal_1] >>
    NTAC 5 strip_tac >> fs[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT] >>
    Cases_on ‘f e’ >> Cases_on ‘EXTREAL_PROD_IMAGE f s’ >> rfs[extreal_mul_def]
QED

Theorem EXTREAL_PROD_IMAGE_NORMAL:
    !f s. FINITE s ==>
          EXTREAL_PROD_IMAGE (λx. Normal (f x)) s = Normal (REAL_PROD_IMAGE f s)
Proof
    strip_tac >> Induct_on ‘s’ >>
    rw [EXTREAL_PROD_IMAGE_THM,REAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT,
        extreal_mul_def,normal_1]
QED

Theorem EXTREAL_PROD_IMAGE_0:
    !f s. FINITE s /\ (?x. x IN s /\ f x = 0) ==> EXTREAL_PROD_IMAGE f s = 0
Proof
    NTAC 2 strip_tac >> simp[GSYM AND_IMP_INTRO] >> Induct_on ‘s’ >>
    rw[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >- fs[] >>
    DISJ2_TAC >> first_x_assum irule >> qexists_tac ‘x’ >> simp[]
QED

Theorem EXTREAL_PROD_IMAGE_1:
    !f s. FINITE s /\ (!x. x IN s ==> f x = 1) ==> EXTREAL_PROD_IMAGE f s = 1
Proof
    NTAC 2 strip_tac >> simp[GSYM AND_IMP_INTRO] >> Induct_on ‘s’ >>
    rw[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT]
QED

Theorem EXTREAL_PROD_IMAGE_ONE:
    !s. FINITE s ==> EXTREAL_PROD_IMAGE (λx. 1) s = 1x
Proof
    Induct_on ‘s’
 >> simp[EXTREAL_PROD_IMAGE_EMPTY,EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT]
QED

Theorem EXTREAL_PROD_IMAGE_POS:
    !f s. FINITE s /\ (!x. x IN s ==> 0 <= f x) ==> 0 <= EXTREAL_PROD_IMAGE f s
Proof
    strip_tac >> simp[GSYM AND_IMP_INTRO] >> Induct_on ‘s’ >>
    rw[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >> irule le_mul >> simp[]
QED

Theorem EXTREAL_PROD_IMAGE_MONO:
    !f g s. FINITE s /\ (!x. x IN s ==> 0 <= f x /\ f x <= g x) ==>
        EXTREAL_PROD_IMAGE f s <= EXTREAL_PROD_IMAGE g s
Proof
    NTAC 2 strip_tac >> simp[GSYM AND_IMP_INTRO] >> Induct_on ‘s’ >>
    rw[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >> irule le_mul2 >>
    simp[EXTREAL_PROD_IMAGE_POS]
QED

Theorem EXTREAL_PROD_IMAGE_COUNT_ZERO[simp]:
    !f. EXTREAL_PROD_IMAGE f (count 0) = 1x
Proof
    simp[COUNT_ZERO]
QED

Theorem EXTREAL_PROD_IMAGE_COUNT_ONE[simp]:
    !f. EXTREAL_PROD_IMAGE f (count 1) = f 0: extreal
Proof
    simp[COUNT_ONE]
QED

Theorem EXTREAL_PROD_IMAGE_COUNT_SUC:
    !f n. EXTREAL_PROD_IMAGE f (count (SUC n)) =
          EXTREAL_PROD_IMAGE f (count n) * f n: extreal
Proof
    rw[] >> qspecl_then [‘f’,‘n’,‘count n’] assume_tac EXTREAL_PROD_IMAGE_PROPERTY >>
    rfs[] >> simp[mul_comm] >> pop_assum $ SUBST1_TAC o SYM >>
    ‘count (SUC n) = n INSERT count n’ suffices_by simp[] >> simp[EXTENSION]
QED

Theorem EXTREAL_PROD_IMAGE_SUPPORT :
  !s t f. FINITE s /\ FINITE t /\
          s SUBSET t /\ (!x. x IN t DIFF s ==> f x = 1) ==> PI f t = PI f s
Proof
  rpt STRIP_TAC
  >> ‘t = s UNION (t DIFF s)’ by rw [UNION_DIFF] >> POP_ORW
  >> Know ‘PI f (s UNION (t DIFF s)) = PI f s * PI f (t DIFF s)’
  >- (irule EXTREAL_PROD_IMAGE_DISJOINT_UNION >> simp [DISJOINT_DIFF]) >> Rewr
  >> Know ‘PI f (t DIFF s) = 1’
  >- (Know ‘PI f (t DIFF s) = PI (λi. 1) (t DIFF s)’
      >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ >> fs []) >> Rewr \\
      irule EXTREAL_PROD_IMAGE_1 >> fs []) >> Rewr >> rw [mul_rone]
QED

Theorem EXTREAL_PROD_IMAGE_SUPPORT' :
  !s t f. FINITE t /\ FINITE s /\ s SUBSET t ==>
          PI (λx. if x IN s then f x else (1 :extreal)) t = PI f s
Proof
  rpt STRIP_TAC
  >> MP_TAC (Q.SPECL [‘s’, ‘t’, ‘λx. if x IN s then f x else 1’]
                     EXTREAL_PROD_IMAGE_SUPPORT)
  >> simp [] >> Rewr
  >> MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ >> METIS_TAC []
QED

(*** Miscellany Within Miscellany ***)

Theorem ext_suminf_sing_general:
    !m r. 0 <= r ==> suminf (λn. if n = m then r else 0) = r
Proof
    rw[] >> ‘!n. 0 <= (λn. if n = m then r else 0) n’ by rw[] >> fs[ext_suminf_def] >>
    ‘(λn. EXTREAL_SUM_IMAGE (λn. if n = m then r else 0) (count n)) =
      (λn. if n < SUC m then 0 else r)’ by (
        rw[FUN_EQ_THM] >> Induct_on ‘n’ >> simp[] >>
        (qspecl_then [‘(λn. if n = m then r else 0)’,‘n’] assume_tac) EXTREAL_SUM_IMAGE_COUNT_SUC >>
        rfs[pos_not_neginf] >> pop_assum kall_tac >>
        map_every (fn tm => Cases_on tm >> simp[]) [‘n < m’,‘n = m’]) >>
    simp[] >> pop_assum kall_tac >> rw[IMAGE_DEF,sup_eq] >- rw[] >>
    pop_assum irule >> qexists_tac ‘SUC m’ >> simp[]
QED

Theorem ext_suminf_nested:
    !f. (!m n. 0 <= f m n) ==>
        suminf (λn. suminf (λm. f m n)) = suminf (λm. suminf (λn. f m n))
Proof
    rw[] >>
    map_every (fn tms => qspecl_then tms assume_tac ext_suminf_2d_full)
        [[‘λm n. f m n’,‘(λm. suminf (λn. f m n))’,‘num_to_pair’],
        [‘λn m. f m n’,‘(λn. suminf (λm. f m n))’,‘SWAP o num_to_pair’]] >>
    rfs[BIJ_NUM_TO_PAIR,INST_TYPE [alpha |-> “:num”,beta |-> “:num”] BIJ_SWAP,BIJ_COMPOSE,SF SFY_ss] >>
    NTAC 2 $ pop_assum $ SUBST1_TAC o SYM >> irule ext_suminf_eq >>
    rw[o_DEF] >> Cases_on `num_to_pair n` >> simp[SWAP_def]
QED

Theorem exp_mono_le[simp]:
    !x:extreal y. exp x <= exp y <=> x <= y
Proof
    rw[] >> Cases_on ‘x’ >> Cases_on ‘y’ >> simp[extreal_exp_def,EXP_MONO_LE]
    >- (simp[EXP_POS_LE])
    >- (simp[GSYM real_lt,EXP_POS_LT])
QED

Theorem pow_even_le:
    !n. EVEN n ==> !x. 0 <= x pow n
Proof
    rw[] >> Cases_on ‘0 <= x’ >- simp[pow_pos_le]
 >> fs[GSYM extreal_lt_def] >> simp[le_lt,pow_pos_even]
QED

Theorem pow_ainv_odd:
    !n. ODD n ==> !x. -x pow n = -(x pow n)
Proof
    rw[] >> qspecl_then [‘n’,‘-1’,‘x’] mp_tac pow_mul >> simp[GSYM neg_minus1] >>
    ‘-1 pow n = -1’ suffices_by simp[GSYM neg_minus1] >> completeInduct_on ‘n’ >>
    NTAC 2 (Cases_on ‘n’ >> fs[extreal_pow_alt,ODD] >> rename [‘ODD n’])
 >> simp[GSYM neg_minus1]
QED

Theorem pow_ainv_even:
    !n. EVEN n ==> !x. -x pow n = x pow n
Proof
    rw[] >> qspecl_then [‘n’,‘-1’,‘x’] mp_tac pow_mul >> simp[GSYM neg_minus1] >>
    ‘-1 pow n = 1’ suffices_by simp[] >> completeInduct_on ‘n’ >>
    NTAC 2 (Cases_on ‘n’ >> fs[extreal_pow_alt,EVEN] >> rename [‘EVEN n’])
 >> simp[GSYM neg_minus1]
QED

Theorem pow_abs :
  !c n. abs (c pow n) = (abs c) pow n
Proof
  rpt STRIP_TAC
  >> Cases_on ‘c = PosInf’ >- (gs [] \\
                               Cases_on ‘n = 0’  >- (gs [abs_refl, extreal_1_simps]) \\
                               gs [extreal_pow_def, extreal_abs_def])
  >> Cases_on ‘c = NegInf’ >- (gs [] \\
                               Cases_on ‘n = 0’ >- (gs [abs_refl, extreal_1_simps]) \\
                               Cases_on ‘EVEN n’ >- (gs [extreal_pow_def, extreal_abs_def]) \\
                               gs [extreal_pow_def, extreal_abs_def])
  >> ‘?r. c = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW
  >> ‘Normal r pow n = Normal (r pow n)’ by rw [extreal_pow_def] >> POP_ORW
  >> ‘abs (Normal (r pow n)) = Normal (abs (r pow n))’ by rw [extreal_abs_def] >> POP_ORW
  >> ‘abs (Normal r) = Normal (abs r)’ by rw [extreal_abs_def] >> POP_ORW
  >> ‘Normal (abs r) pow n = Normal ((abs r) pow n)’ by rw [extreal_pow_def]
  >> METIS_TAC [extreal_11, POW_ABS]
QED

Theorem sub_le_sub_imp:
    !w x y z. w <= x /\ z <= y ==> w - y <= x - z
Proof
    rw[] >> irule le_trans >> qexists_tac ‘x - y’ >> simp[le_lsub_imp,le_rsub_imp]
QED

Theorem le_negl:
    !x y. -x <= y <=> -y <= x
Proof
    rw[] >> ‘-x <= - -y <=> -y <= x’ suffices_by simp[] >> simp[le_neg,Excl "neg_neg"]
QED

Theorem le_negr:
    !x y. x <= -y <=> y <= -x
Proof
    rw[] >> ‘- -x <= -y <=> y <= -x’ suffices_by simp[] >> simp[le_neg,Excl "neg_neg"]
QED

Theorem leeq_trans:
    !x:extreal y z. x <= y /\ y = z ==> x <= z
Proof
    simp[]
QED

Theorem eqle_trans:
    !x:extreal y z. x = y /\ y <= z ==> x <= z
Proof
    simp[]
QED

Theorem seq_le_imp_lim_le :
    !x y (f :num->real). (!n. f n <= x) /\ (f --> y) sequentially ==> y <= x
Proof
    RW_TAC bool_ss [LIM_SEQUENTIALLY]
 >> MATCH_MP_TAC REAL_LE_EPSILON
 >> RW_TAC bool_ss []
 >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o Q.SPEC `N`)
 >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
 >> REWRITE_TAC [dist]
 >> (RW_TAC bool_ss [GREATER_EQ, LESS_EQ_REFL, abs, REAL_LE_SUB_LADD, REAL_ADD_LID] \\
     FULL_SIMP_TAC bool_ss [REAL_NOT_LE, REAL_NEG_SUB, REAL_LT_SUB_RADD])
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC `x` \\
      CONJ_TAC >- PROVE_TAC [REAL_LE_TRANS] \\
      PROVE_TAC [REAL_LE_ADDR, REAL_LT_LE],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC `f N + e` \\
      CONJ_TAC >- PROVE_TAC [REAL_LT_LE, REAL_ADD_SYM] \\
      PROVE_TAC [REAL_LE_ADD2, REAL_LE_REFL] ]
QED

(* cf. seqTheory.SEQ_MONO_LE *)
Theorem seq_mono_le :
    !(f :num->real) x n. (!n. f n <= f (n + 1)) /\ (f --> x) sequentially ==> f n <= x
Proof
   RW_TAC bool_ss [LIM_SEQUENTIALLY] THEN MATCH_MP_TAC REAL_LE_EPSILON THEN
   RW_TAC bool_ss [] THEN Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`) THEN
   RW_TAC bool_ss [GREATER_EQ] THEN MP_TAC (Q.SPECL [`N`, `n`] LESS_EQ_CASES) THEN
   STRIP_TAC THENL
   [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`) THEN ASM_REWRITE_TAC [dist] THEN
    REAL_ARITH_TAC, ALL_TAC] THEN FULL_SIMP_TAC std_ss [dist] THEN
   (SUFF_TAC ``!i : num. f (N - i) <= x + (e : real)`` THEN1
    PROVE_TAC [LESS_EQUAL_DIFF]) THEN
   INDUCT_TAC
   THENL [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
          THEN RW_TAC bool_ss [abs, LESS_EQ_REFL, SUB_0]
          THEN simpLib.FULL_SIMP_TAC bool_ss
               [REAL_LT_SUB_RADD, REAL_NEG_SUB, REAL_NOT_LE, REAL_ADD_LID,
                REAL_LE_SUB_LADD]
          THEN PROVE_TAC
               [REAL_LT_LE, REAL_ADD_SYM, REAL_LE_TRANS, REAL_LE_ADDR],
          MP_TAC (ARITH_PROVE
                  ``(N - i = N - SUC i) \/ (N - i = (N - SUC i) + 1)``)
          THEN PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]
QED

Theorem sup_seq' : (* was: sup_sequence *)
    !f l. mono_increasing f ==>
         ((f --> l) sequentially <=>
          (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))
Proof
    rpt STRIP_TAC
 >> Suff ‘(f --> l) sequentially <=> (f --> l)’
 >- (Rewr' \\
     MATCH_MP_TAC sup_seq >> art [])
 >> REWRITE_TAC [LIM_SEQUENTIALLY_SEQ]
QED

Theorem inf_seq' :
    !f l. mono_decreasing f ==>
         ((f --> l) sequentially <=>
          (inf (IMAGE (\n. Normal (f n)) UNIV) = Normal l))
Proof
    rpt STRIP_TAC
 >> Suff ‘(f --> l) sequentially <=> (f --> l)’
 >- (Rewr' \\
     MATCH_MP_TAC inf_seq >> art [])
 >> REWRITE_TAC [LIM_SEQUENTIALLY_SEQ]
QED

Theorem bounded_imp_not_infty :
    !x k. abs x <= Normal k ==> x <> NegInf /\ x <> PosInf
Proof
    rw [abs_bounds, lt_infty] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q_TAC (TRANS_TAC lte_trans) ‘-Normal k’ >> art [] \\
      rw [extreal_ainv_def, lt_infty],
      (* goal 2 (of 2) *)
      Q_TAC (TRANS_TAC let_trans) ‘Normal k’ >> art [] \\
      rw [lt_infty] ]
QED

Theorem mono_increasing_ext :
    !f f'. ext_mono_increasing f /\ (!n. f n = Normal (f' n)) ==>
           mono_increasing f'
Proof
    rpt STRIP_TAC
 >> rw [mono_increasing_def]
 >> REWRITE_TAC [GSYM extreal_le_eq]
 >> Q.PAT_X_ASSUM ‘!n. f n = Normal (f' n)’ (REWRITE_TAC o wrap o GSYM)
 >> fs [ext_mono_increasing_def]
QED

Theorem mono_decreasing_ext :
    !f f'. ext_mono_decreasing f /\ (!n. f n = Normal (f' n)) ==>
           mono_decreasing f'
Proof
    rpt STRIP_TAC
 >> rw [mono_decreasing_def]
 >> REWRITE_TAC [GSYM extreal_le_eq]
 >> Q.PAT_X_ASSUM ‘!n. f n = Normal (f' n)’ (REWRITE_TAC o wrap o GSYM)
 >> fs [ext_mono_decreasing_def]
QED

Theorem sup_add_mono_bounded :
    !f g. ext_bounded (IMAGE f UNIV) /\ ext_mono_increasing f /\
          ext_bounded (IMAGE g UNIV) /\ ext_mono_increasing g ==>
          sup (IMAGE (\n. f n + g n) UNIV) =
          sup (IMAGE f UNIV) + sup (IMAGE g UNIV)
Proof
    rw [ext_bounded_alt]
 >> ‘!n. abs (f n) <= Normal k /\ abs (g n) <= Normal k'’ by METIS_TAC []
 >> Q.PAT_X_ASSUM ‘!x. _ ==> abs x <= Normal k’  K_TAC
 >> Q.PAT_X_ASSUM ‘!x. _ ==> abs x <= Normal k'’ K_TAC
 >> ‘!n. f n <> NegInf /\ f n <> PosInf /\ g n <> NegInf /\ g n <> PosInf’
       by METIS_TAC [bounded_imp_not_infty]
 >> qabbrev_tac ‘h = \n. f n + g n’
 >> Know ‘!n. abs (h n) <= Normal (k + k')’
 >- (rw [Abbr ‘h’] \\
     Q_TAC (TRANS_TAC le_trans) ‘abs (f n) + abs (g n)’ \\
     simp [abs_triangle, GSYM extreal_add_eq] \\
     MATCH_MP_TAC le_add2 >> rw [])
 >> DISCH_TAC
 >> ‘!n. h n <> NegInf /\ h n <> PosInf’ by METIS_TAC [bounded_imp_not_infty]
 >> Know ‘mono_increasing h’
 >- (rw [ext_mono_increasing_def, Abbr ‘h’] \\
     MATCH_MP_TAC le_add2 >> fs [ext_mono_increasing_def])
 >> DISCH_TAC
 >> qmatch_abbrev_tac ‘l3 = l1 + l2’
 >> ‘abs l1 <= Normal k /\
     abs l2 <= Normal k' /\
     abs l3 <= Normal (k + k')’ by METIS_TAC [sup_bounded']
 >> ‘l1 <> NegInf /\ l1 <> PosInf /\
     l2 <> NegInf /\ l2 <> PosInf /\
     l3 <> NegInf /\ l3 <> PosInf’ by PROVE_TAC [bounded_imp_not_infty]
 >> ‘?r1. l1 = Normal r1’ by METIS_TAC [extreal_cases]
 >> ‘?r2. l2 = Normal r2’ by METIS_TAC [extreal_cases]
 >> ‘?r3. l3 = Normal r3’ by METIS_TAC [extreal_cases]
 >> NTAC 3 (POP_ASSUM MP_TAC)
 >> Know ‘!n. ?r. f n = Normal r’
 >- (Q.X_GEN_TAC ‘n’ \\
     METIS_TAC [extreal_cases])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘f'’ STRIP_ASSUME_TAC)
 >> Know ‘!n. ?r. g n = Normal r’
 >- (Q.X_GEN_TAC ‘n’ \\
     METIS_TAC [extreal_cases])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘g'’ STRIP_ASSUME_TAC)
 >> Know ‘!n. ?r. h n = Normal r’
 >- (Q.X_GEN_TAC ‘n’ \\
     METIS_TAC [extreal_cases])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘h'’ STRIP_ASSUME_TAC)
 >> ‘mono_increasing f' /\
     mono_increasing g' /\
     mono_increasing h'’ by PROVE_TAC [mono_increasing_ext]
 >> simp [Abbr ‘l1’, Abbr ‘l2’, Abbr ‘l3’]
 >> ‘f = \n. Normal (f' n)’ by rw [FUN_EQ_THM] >> POP_ORW
 >> ‘g = \n. Normal (g' n)’ by rw [FUN_EQ_THM] >> POP_ORW
 >> ‘h = \n. Normal (h' n)’ by rw [FUN_EQ_THM] >> POP_ORW
 >> simp [GSYM sup_seq']
 >> Know ‘h' = \n. f' n + g' n’
 >- (rw [FUN_EQ_THM] \\
     REWRITE_TAC [GSYM extreal_11, GSYM extreal_add_eq] \\
     Q.PAT_X_ASSUM ‘!n. f n = Normal (f' n)’ (REWRITE_TAC o wrap o GSYM) \\
     Q.PAT_X_ASSUM ‘!n. g n = Normal (g' n)’ (REWRITE_TAC o wrap o GSYM) \\
     Q.PAT_X_ASSUM ‘!n. h n = Normal (h' n)’ (REWRITE_TAC o wrap o GSYM) \\
     simp [Abbr ‘h’])
 >> Rewr'
 >> rw [extreal_add_eq, extreal_11]
 >> ‘((\n. f' n + g' n) --> (r1 + r2)) sequentially’
      by METIS_TAC [real_topologyTheory.LIM_ADD]
 >> METIS_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, LIM_UNIQUE]
QED

Theorem inf_add_mono_bounded :
    !f g. ext_bounded (IMAGE f UNIV) /\ ext_mono_decreasing f /\
          ext_bounded (IMAGE g UNIV) /\ ext_mono_decreasing g ==>
          inf (IMAGE (\n. f n + g n) UNIV) =
          inf (IMAGE f UNIV) + inf (IMAGE g UNIV)
Proof
    rw [ext_bounded_alt]
 >> ‘!n. abs (f n) <= Normal k /\ abs (g n) <= Normal k'’ by METIS_TAC []
 >> Q.PAT_X_ASSUM ‘!x. _ ==> abs x <= Normal k’  K_TAC
 >> Q.PAT_X_ASSUM ‘!x. _ ==> abs x <= Normal k'’ K_TAC
 >> ‘!n. f n <> NegInf /\ f n <> PosInf /\ g n <> NegInf /\ g n <> PosInf’
       by METIS_TAC [bounded_imp_not_infty]
 >> qabbrev_tac ‘h = \n. f n + g n’
 >> Know ‘!n. abs (h n) <= Normal (k + k')’
 >- (rw [Abbr ‘h’] \\
     Q_TAC (TRANS_TAC le_trans) ‘abs (f n) + abs (g n)’ \\
     simp [abs_triangle, GSYM extreal_add_eq] \\
     MATCH_MP_TAC le_add2 >> rw [])
 >> DISCH_TAC
 >> ‘!n. h n <> NegInf /\ h n <> PosInf’ by METIS_TAC [bounded_imp_not_infty]
 >> Know ‘mono_decreasing h’
 >- (rw [ext_mono_decreasing_def, Abbr ‘h’] \\
     MATCH_MP_TAC le_add2 >> fs [ext_mono_decreasing_def])
 >> DISCH_TAC
 >> qmatch_abbrev_tac ‘l3 = l1 + l2’
 >> ‘abs l1 <= Normal k /\
     abs l2 <= Normal k' /\
     abs l3 <= Normal (k + k')’ by METIS_TAC [inf_bounded']
 >> ‘l1 <> NegInf /\ l1 <> PosInf /\
     l2 <> NegInf /\ l2 <> PosInf /\
     l3 <> NegInf /\ l3 <> PosInf’ by PROVE_TAC [bounded_imp_not_infty]
 >> ‘?r1. l1 = Normal r1’ by METIS_TAC [extreal_cases]
 >> ‘?r2. l2 = Normal r2’ by METIS_TAC [extreal_cases]
 >> ‘?r3. l3 = Normal r3’ by METIS_TAC [extreal_cases]
 >> NTAC 3 (POP_ASSUM MP_TAC)
 >> Know ‘!n. ?r. f n = Normal r’
 >- (Q.X_GEN_TAC ‘n’ \\
     METIS_TAC [extreal_cases])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘f'’ STRIP_ASSUME_TAC)
 >> Know ‘!n. ?r. g n = Normal r’
 >- (Q.X_GEN_TAC ‘n’ \\
     METIS_TAC [extreal_cases])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘g'’ STRIP_ASSUME_TAC)
 >> Know ‘!n. ?r. h n = Normal r’
 >- (Q.X_GEN_TAC ‘n’ \\
     METIS_TAC [extreal_cases])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘h'’ STRIP_ASSUME_TAC)
 >> ‘mono_decreasing f' /\
     mono_decreasing g' /\
     mono_decreasing h'’ by PROVE_TAC [mono_decreasing_ext]
 >> simp [Abbr ‘l1’, Abbr ‘l2’, Abbr ‘l3’]
 >> ‘f = \n. Normal (f' n)’ by rw [FUN_EQ_THM] >> POP_ORW
 >> ‘g = \n. Normal (g' n)’ by rw [FUN_EQ_THM] >> POP_ORW
 >> ‘h = \n. Normal (h' n)’ by rw [FUN_EQ_THM] >> POP_ORW
 >> simp [GSYM inf_seq']
 >> Know ‘h' = \n. f' n + g' n’
 >- (rw [FUN_EQ_THM] \\
     REWRITE_TAC [GSYM extreal_11, GSYM extreal_add_eq] \\
     Q.PAT_X_ASSUM ‘!n. f n = Normal (f' n)’ (REWRITE_TAC o wrap o GSYM) \\
     Q.PAT_X_ASSUM ‘!n. g n = Normal (g' n)’ (REWRITE_TAC o wrap o GSYM) \\
     Q.PAT_X_ASSUM ‘!n. h n = Normal (h' n)’ (REWRITE_TAC o wrap o GSYM) \\
     simp [Abbr ‘h’])
 >> Rewr'
 >> rw [extreal_add_eq, extreal_11]
 >> ‘((\n. f' n + g' n) --> (r1 + r2)) sequentially’
      by METIS_TAC [real_topologyTheory.LIM_ADD]
 >> METIS_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, LIM_UNIQUE]
QED

Theorem ext_liminf_add :
    !a b. ext_bounded (IMAGE a UNIV) /\
          ext_bounded (IMAGE b UNIV) ==>
          liminf a + liminf b <= liminf (\n. a n + b n)
Proof
    rw [ext_liminf_def]
 >> qmatch_abbrev_tac ‘sup (IMAGE f UNIV) + sup (IMAGE g UNIV) <= _’
 >> Know ‘sup (IMAGE f UNIV) + sup (IMAGE g UNIV) = sup (IMAGE (\n. f n + g n) UNIV)’
 >- (SYM_TAC >> MATCH_MP_TAC sup_add_mono_bounded \\
     rpt STRIP_TAC >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       NTAC 2 (Q.PAT_X_ASSUM ‘ext_bounded _’ MP_TAC) \\
       rw [ext_bounded_alt] \\
       Q.EXISTS_TAC ‘k + k'’ >> rw [REAL_LE_ADD] \\
       rename1 ‘abs (f n) <= Normal (k + k')’ \\
       Q_TAC (TRANS_TAC le_trans) ‘Normal k’ \\
       reverse CONJ_TAC >- rw [extreal_le_eq] \\
       METIS_TAC [inf_bounded],
       (* goal 2 (of 4) *)
       rw [ext_mono_increasing_def, Abbr ‘f’] \\
       MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
       Q.EXISTS_TAC ‘n’ >> rw [],
       (* goal 3 (of 4) *)
       NTAC 2 (Q.PAT_X_ASSUM ‘ext_bounded _’ MP_TAC) \\
       rw [ext_bounded_alt] \\
       Q.EXISTS_TAC ‘k + k'’ >> rw [REAL_LE_ADD] \\
       rename1 ‘abs (g n) <= Normal (k + k')’ \\
       Q_TAC (TRANS_TAC le_trans) ‘Normal k'’ \\
       reverse CONJ_TAC >- rw [extreal_le_eq] \\
       METIS_TAC [inf_bounded],
       (* goal 4 (of 4) *)
       rw [ext_mono_increasing_def, Abbr ‘g’] \\
       MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
       Q.EXISTS_TAC ‘n’ >> rw [] ])
 >> Rewr'
 >> MATCH_MP_TAC sup_mono
 >> rw [le_inf']
 >> rename1 ‘n <= m’
 >> MATCH_MP_TAC le_add2
 >> rw [Abbr ‘f’, Abbr ‘g’, inf_le'] (* 2 subgoals, same tactics *)
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> art []
QED

Theorem ext_limsup_add :
    !a b. ext_bounded (IMAGE a UNIV) /\
          ext_bounded (IMAGE b UNIV) ==>
          limsup (\n. a n + b n) <= limsup a + limsup b
Proof
    rw [ext_limsup_def]
 >> qmatch_abbrev_tac ‘_ <= inf (IMAGE f UNIV) + inf (IMAGE g UNIV)’
 >> Know ‘inf (IMAGE f UNIV) + inf (IMAGE g UNIV) = inf (IMAGE (\n. f n + g n) UNIV)’
 >- (SYM_TAC >> MATCH_MP_TAC inf_add_mono_bounded \\
     rpt STRIP_TAC >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       NTAC 2 (Q.PAT_X_ASSUM ‘ext_bounded _’ MP_TAC) \\
       rw [ext_bounded_alt] \\
       Q.EXISTS_TAC ‘k + k'’ >> rw [REAL_LE_ADD] \\
       rename1 ‘abs (f n) <= Normal (k + k')’ \\
       Q_TAC (TRANS_TAC le_trans) ‘Normal k’ \\
       reverse CONJ_TAC >- rw [extreal_le_eq] \\
       METIS_TAC [sup_bounded],
       (* goal 2 (of 4) *)
       rw [ext_mono_decreasing_def, Abbr ‘f’] \\
       MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
       Q.EXISTS_TAC ‘n’ >> rw [],
       (* goal 3 (of 4) *)
       NTAC 2 (Q.PAT_X_ASSUM ‘ext_bounded _’ MP_TAC) \\
       rw [ext_bounded_alt] \\
       Q.EXISTS_TAC ‘k + k'’ >> rw [REAL_LE_ADD] \\
       rename1 ‘abs (g n) <= Normal (k + k')’ \\
       Q_TAC (TRANS_TAC le_trans) ‘Normal k'’ \\
       reverse CONJ_TAC >- rw [extreal_le_eq] \\
       METIS_TAC [sup_bounded],
       (* goal 4 (of 4) *)
       rw [ext_mono_decreasing_def, Abbr ‘g’] \\
       MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
       Q.EXISTS_TAC ‘n’ >> rw [] ])
 >> Rewr'
 >> MATCH_MP_TAC inf_mono
 >> rw [sup_le'] >> rename1 ‘n <= m’
 >> MATCH_MP_TAC le_add2
 >> rw [Abbr ‘f’, Abbr ‘g’, le_sup'] (* 2 subgoals, same tactics *)
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> art []
QED

Theorem ext_limsup_mono :
    !p q. (!n. p n <= q n) ==> limsup p <= limsup q
Proof
    rw [ext_limsup_def]
 >> MATCH_MP_TAC inf_mono >> rw []
 >> qabbrev_tac ‘A = {i | n <= i}’
 >> ‘{p i | n <= i} = {p i | i IN A}’ by rw [Once EXTENSION, Abbr ‘A’] >> POP_ORW
 >> ‘{q i | n <= i} = {q i | i IN A}’ by rw [Once EXTENSION, Abbr ‘A’] >> POP_ORW
 >> MATCH_MP_TAC sup_mono_ext
 >> rw [Abbr ‘A’]
 >> rename1 ‘n <= k’
 >> Q.EXISTS_TAC ‘k’ >> rw []
QED

Theorem ext_liminf_mono :
    !p q. (!n. p n <= q n) ==> liminf p <= liminf q
Proof
    rw [ext_liminf_def]
 >> MATCH_MP_TAC sup_mono >> rw []
 >> rw [le_inf']
 >> rename1 ‘n <= m’
 >> Q_TAC (TRANS_TAC le_trans) ‘p m’ >> rw []
 >> rw [inf_le']
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

(* NOTE: The equation doesn't hold (even “!n. mono_increasing (f n)” is assumed) *)
Theorem ext_limsup_sup_lemma :
    !f. sup (IMAGE (\m. limsup (\n. f n m)) univ(:num)) <=
        limsup (\n. sup (IMAGE (f n) univ(:num)))
Proof
    rw [sup_le']
 >> MATCH_MP_TAC ext_limsup_mono
 >> rw [le_sup']
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem ext_limsup_const :
    !(c :extreal). limsup (\n. c) = c
Proof
    rw [ext_limsup_def]
 >> Know ‘!(m :num). sup {c | n | m <= n} = c’
 >- (Q.X_GEN_TAC ‘m’ \\
     MATCH_MP_TAC sup_const_alt' >> simp [GSPECIFICATION] \\
     rw [] >> Q.EXISTS_TAC ‘m’ >> simp [])
 >> rw []
 >> MATCH_MP_TAC inf_const_alt' >> simp []
QED

Theorem ext_liminf_const :
    !(c :extreal). liminf (\n. c) = c
Proof
    rw [ext_liminf_alt_limsup, o_DEF, ext_limsup_const]
QED

Theorem ext_limsup_triangle :
    !f (J :'index set).
       FINITE J /\ (!i. ext_bounded (IMAGE (\n. f n i) UNIV)) ==>
       limsup (\n. SIGMA (f n) J) <= SIGMA (\i. limsup (\n. f n i)) J
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘FINITE J’ MP_TAC
 >> Induct_on ‘J’ >> rw [ext_limsup_const]
 >> Know ‘!n. SIGMA (f n) (e INSERT J) = f n e + SIGMA (f n) (J DELETE e)’
 >- (Q.X_GEN_TAC ‘n’ \\
     irule EXTREAL_SUM_IMAGE_PROPERTY >> art [] \\
     DISJ2_TAC (* or DISJ1_TAC *) \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. ext_bounded _’ (MP_TAC o Q.SPEC ‘i’) \\
     rw [lt_infty, ext_bounded_def, abs_bounds] \\
     Q_TAC (TRANS_TAC let_trans) ‘a’ >> art [] \\
     POP_ASSUM (MATCH_MP_TAC o cj 2) \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> Rewr'
 >> qmatch_abbrev_tac ‘_ <= SIGMA g _’
 >> Know ‘SIGMA g (e INSERT J) = g e + SIGMA g (J DELETE e)’
 >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> art [] \\
     DISJ2_TAC \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. ext_bounded _’ (MP_TAC o Q.SPEC ‘i’) \\
     rw [lt_infty, ext_bounded_def, Abbr ‘g’] \\
     Q_TAC (TRANS_TAC let_trans) ‘a’ >> art [] \\
     Suff ‘abs (limsup (\n. f n i)) <= a’ >- simp [abs_bounds] \\
     MATCH_MP_TAC ext_limsup_bounded >> rw [] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> Rewr'
 >> ‘J DELETE e = J’ by PROVE_TAC [DELETE_NON_ELEMENT] >> POP_ORW
 >> Cases_on ‘J = {}’ >- simp []
 (* applying ext_limsup_add *)
 >> Q_TAC (TRANS_TAC le_trans) ‘limsup (\n. f n e) + limsup (\n. SIGMA (f n) J)’
 >> CONJ_TAC
 >- (HO_MATCH_MP_TAC ext_limsup_add >> art [] \\
     fs [ext_bounded_def, SKOLEM_THM] \\
     Q.EXISTS_TAC ‘SIGMA f' J’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> simp []) \\
     reverse (rw [abs_bounds])
     >- (irule EXTREAL_SUM_IMAGE_MONO >> fs [abs_bounds] \\
         CONJ_ASM1_TAC >- METIS_TAC [] \\
         DISJ2_TAC >> rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!x. x IN J ==> f n x <= f' x’ (MP_TAC o Q.SPEC ‘x’) \\
         simp [GSYM extreal_lt_def, GSYM lt_infty]) \\
     Know ‘-SIGMA f' J =  SIGMA (\x. -f' x) J’
     >- (SYM_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MINUS >> art []) >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO >> fs [abs_bounds] \\
     CONJ_TAC >- METIS_TAC [] \\
     DISJ1_TAC >> RW_TAC std_ss []
     >- (‘NegInf = -PosInf’ by rw [extreal_ainv_def] >> POP_ORW \\
         simp [eq_neg]) \\
     CCONTR_TAC >> fs [] \\
     Q.PAT_X_ASSUM ‘!i. _’ (MP_TAC o Q.SPEC ‘x’) >> STRIP_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘(f :num -> 'index -> extreal) n x’) \\
     impl_tac >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
     simp [le_infty] \\
    ‘NegInf = -PosInf’ by rw [extreal_ainv_def] >> POP_ORW \\
     simp [eq_neg])
 (* stage work *)
 >> simp []
 >> MATCH_MP_TAC le_ladd_imp >> art []
QED

Theorem ext_limsup_cmul :
    !f c. 0 <= c ==> limsup (\n. Normal c * f n) = Normal c * limsup f
Proof
    rw [ext_limsup_def]
 >> Know ‘!m. {Normal c * f n | m <= n} = IMAGE (\n. Normal c * f n) {i | m <= i}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> Know ‘!m. {f n | m <= n} = IMAGE f {i | m <= i}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> Know ‘!m. sup (IMAGE (\n. Normal c * f n) {i | m <= i}) =
              Normal c * sup (IMAGE f {i | m <= i})’
 >- (Q.X_GEN_TAC ‘m’ \\
     MATCH_MP_TAC sup_cmul_general >> rw [Once EXTENSION] \\
     Q.EXISTS_TAC ‘m’ >> simp [])
 >> Rewr'
 >> qabbrev_tac ‘g = \m. sup (IMAGE f {i | m <= i})’
 >> simp []
 >> MATCH_MP_TAC inf_cmul' >> art []
QED

Theorem ext_liminf_cmul :
    !f c. 0 <= c ==> liminf (\n. Normal c * f n) = Normal c * liminf f
Proof
    rw [ext_liminf_def]
 >> Know ‘!m. {Normal c * f n | m <= n} = IMAGE (\n. Normal c * f n) {i | m <= i}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> Know ‘!m. {f n | m <= n} = IMAGE f {i | m <= i}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> Know ‘!m. inf (IMAGE (\n. Normal c * f n) {i | m <= i}) =
              Normal c * inf (IMAGE f {i | m <= i})’
 >- (Q.X_GEN_TAC ‘m’ \\
     MATCH_MP_TAC inf_cmul_general >> rw [Once EXTENSION] \\
     Q.EXISTS_TAC ‘m’ >> simp [])
 >> Rewr'
 >> qabbrev_tac ‘g = \m. inf (IMAGE f {i | m <= i})’
 >> simp []
 >> MATCH_MP_TAC sup_cmul >> art []
QED

(* ------------------------------------------------------------------------- *)
(*   Advanced results of ext_limsup/liminf (moved from martingaleTheory)     *)
(* ------------------------------------------------------------------------- *)

Theorem LIM_SEQUENTIALLY_real_normal :
    !a l. (!n. a n <> PosInf /\ a n <> NegInf) ==>
          ((real o a --> l) sequentially <=>
           !e. 0 < e ==> ?N. !n. N <= n ==> abs (a n - Normal l) < Normal e)
Proof
    rw [LIM_SEQUENTIALLY, dist, o_DEF]
 >> EQ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] \\
     Know ‘!n. real (a n) - l = real (a n - Normal l)’
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [real_normal, extreal_sub_eq]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘!n. abs (real (a n - Normal l)) = real (abs (a n - Normal l))’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC abs_real \\
        ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     POP_ASSUM MP_TAC \\
     ONCE_REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘!n. Normal (real (abs (a n - Normal l))) = abs (a n - Normal l)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC normal_real \\
        ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_abs_def]) >> Rewr' \\
     DISCH_TAC \\
     Q.EXISTS_TAC ‘N’ >> rw [])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e’))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘N’
 >> rpt STRIP_TAC
 >> Know ‘real (a n) - l = real (a n - Normal l)’
 >- (‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [real_normal, extreal_sub_eq]) >> Rewr'
 >> Know ‘abs (real (a n - Normal l)) = real (abs (a n - Normal l))’
 >- (MATCH_MP_TAC abs_real \\
    ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def]) >> Rewr'
 >> ONCE_REWRITE_TAC [GSYM extreal_lt_eq]
 >> Know ‘Normal (real (abs (a n - Normal l))) = abs (a n - Normal l)’
 >- (MATCH_MP_TAC normal_real \\
    ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_abs_def]) >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* The limit of the arithmetic means of the first n partial sums is called
  "Cesaro summation". cf. https://en.wikipedia.org/wiki/Cesaro_summation

   This proof uses iterateTheory (numseg), added for WLLN_IID and SLLN_IID.
 *)
Theorem LIM_SEQUENTIALLY_CESARO :
    !(f :num->real) l. ((\n. f n) --> l) sequentially ==>
          ((\n. SIGMA f (count (SUC n)) / &SUC n) --> l) sequentially
Proof
    RW_TAC std_ss [LIM_SEQUENTIALLY, dist]
 >> Q.ABBREV_TAC ‘g = \n. f n - l’
 >> Know ‘!n. SIGMA f (count (SUC n)) / &SUC n - l =
              SIGMA g (count (SUC n)) / &SUC n’
 >- (rw [Abbr ‘g’] \\
     Know ‘SIGMA (\n. f n - l) (count (SUC n)) =
           SIGMA f (count (SUC n)) - SIGMA (\x. l) (count (SUC n))’
     >- (HO_MATCH_MP_TAC REAL_SUM_IMAGE_SUB >> rw []) >> Rewr' \\
    ‘FINITE (count (SUC n))’ by rw [] \\
     rw [REAL_SUM_IMAGE_FINITE_CONST3, CARD_COUNT, real_div, REAL_SUB_LDISTRIB])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> _’ MP_TAC
 >> ‘!n. f n - l = g n’ by METIS_TAC [] >> POP_ORW
 >> DISCH_THEN (MP_TAC o (Q.SPEC ‘(1 / 2) * e’))
 >> ‘0 < 1 / 2 * e’ by rw []
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘Abbrev (g = (\n. f n - l))’ K_TAC
 (* special case: N = 0 *)
 >> Cases_on ‘N = 0’
 >- (fs [] >> Q.EXISTS_TAC ‘0’ >> rw [real_div] \\
    ‘abs (inv (&SUC n) * SIGMA g (count (SUC n))) =
     abs (inv (&SUC n)) * abs (SIGMA g (count (SUC n)))’
       by rw [REAL_ABS_MUL] >> POP_ORW \\
    ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘inv (&SUC n) * SIGMA (abs o g) (count (SUC n))’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [] \\
                  MATCH_MP_TAC REAL_SUM_IMAGE_ABS_TRIANGLE >> rw []) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘inv (&SUC n) * SIGMA (\i. 1 / 2 * e) (count (SUC n))’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [] \\
                  irule REAL_SUM_IMAGE_MONO >> rw [o_DEF] \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> rw []) \\
     rw [REAL_SUM_IMAGE_FINITE_CONST3])
 (* stage work, now ‘0 < N’ *)
 >> ‘0 < N’ by RW_TAC arith_ss []
 >> Q.ABBREV_TAC ‘M = abs (SIGMA g (count N))’
 >> Q.EXISTS_TAC ‘MAX N (2 * clg (M * inv e))’
 >> RW_TAC std_ss [MAX_LE]
 (* applying LE_NUM_CEILING *)
 >> ‘M * realinv e <= &clg (M * realinv e)’ by PROVE_TAC [LE_NUM_CEILING]
 >> Know ‘2 * &clg (M * realinv e) <= (&n :real)’
 >- (REWRITE_TAC [GSYM REAL_DOUBLE] \\
    ‘!n. &n + (&n :real) = &(n + n)’ by rw [] >> POP_ORW \\
     REWRITE_TAC [GSYM TIMES2] >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘2 * clg (M * realinv e) <= n’ K_TAC
 >> Know ‘2 * (M * realinv e) <= &n’
 >- (MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘2 * &clg (M * realinv e)’ >> art [] \\
     MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [])
 >> NTAC 2 (POP_ASSUM K_TAC) (* clg is gone *)
 >> DISCH_TAC
 >> ‘count (SUC n) = (count N) UNION {N .. n}’
      by (rw [Once EXTENSION, numseg, IN_COUNT]) >> POP_ORW
 >> ‘DISJOINT (count N) {N .. n}’
      by (rw [DISJOINT_ALT, IN_COUNT, IN_NUMSEG])
 >> Know ‘SIGMA g ((count N) UNION {N .. n}) = SIGMA g (count N) + SIGMA g {N .. n}’
 >- (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION \\
     rw [FINITE_COUNT, FINITE_NUMSEG]) >> Rewr'
 >> REWRITE_TAC [real_div, REAL_ADD_RDISTRIB]
 (* applying ABS_TRIANGLE *)
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘abs (SIGMA g (count N) * inv (&SUC n)) +
                  abs (SIGMA g {N .. n}  * inv (&SUC n))’
 >> REWRITE_TAC [ABS_TRIANGLE]
 >> Suff ‘abs (SIGMA g (count N) * inv (&SUC n)) < 1 / 2 * e /\
          abs (SIGMA g {N .. n} * inv (&SUC n)) < 1 / 2 * e’
 >- (DISCH_TAC \\
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
                     [GSYM X_HALF_HALF] \\
     MATCH_MP_TAC REAL_LT_ADD2 >> art [])
 (* applying REAL_SUM_IMAGE_ABS_TRIANGLE *)
 >> reverse CONJ_TAC
 >- (Know ‘abs (SIGMA g {N .. n} * inv (&SUC n)) =
           abs (SIGMA g {N .. n}) * abs (inv (&SUC n))’
     >- (rw [REAL_ABS_MUL]) >> Rewr' \\
    ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘SIGMA (abs o g) {N .. n} * inv (&SUC n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [] \\
                  MATCH_MP_TAC REAL_SUM_IMAGE_ABS_TRIANGLE \\
                  REWRITE_TAC [FINITE_NUMSEG]) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘SIGMA (\i. 1 / 2 * e) {N .. n} * inv (&SUC n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [] \\
                  irule REAL_SUM_IMAGE_MONO >> rw [FINITE_NUMSEG, IN_NUMSEG, o_DEF] \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> fs []) \\
    ‘FINITE {N .. n}’ by PROVE_TAC [FINITE_NUMSEG] \\
     rw [REAL_SUM_IMAGE_FINITE_CONST3, CARD_NUMSEG, GSYM ADD1])
 (* final part *)
 >> Know ‘abs (SIGMA g (count N) * inv (&SUC n)) = M * abs (inv (&SUC n))’
 >- (rw [Abbr ‘M’, REAL_ABS_MUL]) >> Rewr'
 >> ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW
 >> Q.PAT_X_ASSUM ‘2 * (M * realinv e) <= &n’
      (MP_TAC o (ONCE_REWRITE_RULE [REAL_MUL_ASSOC]))
 >> ‘e <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] >> rw []
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘e * &n’ >> rw []
QED

(* Properties A.1 (iv) [1, p.409] *)
Theorem ext_liminf_le_subseq :
    !a f l. (!n. a n <> PosInf /\ a n <> NegInf) /\
            (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> l) sequentially ==> liminf a <= Normal l
Proof
    rpt STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> Know ‘((real o a o f) --> l) sequentially <=>
          !e. 0 < e ==> ?N. !n. N <= n ==> abs ((a o f) n - Normal l) < Normal e’
 >- (HO_MATCH_MP_TAC LIM_SEQUENTIALLY_real_normal >> rw [])
 >> Rewr'
 >> rw [o_DEF, abs_bounds_lt, ext_liminf_def, sup_le']
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘inf {a (f n) | m <= n}’
 >> CONJ_TAC
 >- (MATCH_MP_TAC inf_mono_subset \\
     rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘f n’ >> rw [] \\
     MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
     MATCH_MP_TAC MONOTONE_BIGGER >> rw [])
 >> rw [inf_le']
 >> MATCH_MP_TAC le_epsilon
 >> rpt STRIP_TAC
 >> ‘e <> NegInf’ by METIS_TAC [lt_imp_le, pos_not_neginf]
 >> ‘?E. 0 < E /\ e = Normal E’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘e <> PosInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘e <> NegInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘0 < e’       K_TAC
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘E’))
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘N + m’))
 >> RW_TAC arith_ss []
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘a (f (N + m))’
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘N + m’ >> rw [])
 >> MATCH_MP_TAC lt_imp_le
 >> ONCE_REWRITE_TAC [add_comm_normal]
 >> Suff ‘a (f (N + m)) < Normal E + Normal l <=>
          a (f (N + m)) - Normal l < Normal E’ >- rw []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC sub_lt_eq >> rw []
QED

(* Properties A.1 (iv) [1, p.409] (dual of previous lemma) *)
Theorem ext_limsup_le_subseq :
    !a f l. (!n. a n <> PosInf /\ a n <> NegInf) /\
            (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> l) sequentially ==> Normal l <= limsup a
Proof
    rw [ext_limsup_alt_liminf]
 >> ‘Normal l = -Normal (-l)’ by rw [extreal_ainv_def] >> POP_ORW
 >> rw [le_neg]
 >> MATCH_MP_TAC ext_liminf_le_subseq
 >> Q.EXISTS_TAC ‘f’ >> rw []
 >| [ (* goal 1 (of 3) *)
     ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> rw [extreal_ainv_def],
      (* goal 2 (of 3) *)
     ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> rw [extreal_ainv_def],
      (* goal 3 (of 3) *)
      Suff ‘real o numeric_negate o a o f = (\n. -(real o a o f) n)’
      >- (Rewr' >> MATCH_MP_TAC real_topologyTheory.LIM_NEG >> art []) \\
      rw [o_DEF, FUN_EQ_THM] \\
      ‘?r. a (f n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ASM_SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_ainv_def] \\
      Know ‘Normal (real (-Normal r)) = -Normal r’
      >- (MATCH_MP_TAC normal_real \\
          SIMP_TAC std_ss [extreal_ainv_def, extreal_not_infty]) >> Rewr' \\
      Know ‘Normal (real (Normal r)) = Normal r’
      >- (MATCH_MP_TAC normal_real >> rw []) >> Rewr' \\
      rw [extreal_ainv_def] ]
QED

(* Properties A.1 (iv) [1, p.409] (construction of subsequence with liminf as
   the limit)
 *)
Theorem ext_liminf_imp_subseq :
    !a. (!n. a n <> PosInf /\ a n <> NegInf) /\
        liminf a <> PosInf /\ liminf a <> NegInf ==>
        ?f. (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> real (liminf a)) sequentially
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘L = liminf a’
 >> Know ‘!k. inf {a n | k <= n} <= L’
 >- (rw [Abbr ‘L’, ext_liminf_def] \\
     MATCH_MP_TAC le_sup_imp' >> rw [] \\
     Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. inf {a n | k <= n} <> PosInf’
 >- (rw [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘L’ >> art [] \\
    ‘?r. L = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [lt_infty])
 >> DISCH_TAC
 (* it's impossible that ‘inf {a n | k <= n}’ (increasing) is always NegInf *)
 >> Cases_on ‘!Z. inf {a n | Z <= n} = NegInf’
 >- (Suff ‘L = NegInf’ >- PROVE_TAC [] \\
     SIMP_TAC std_ss [Abbr ‘L’, ext_liminf_def] >> POP_ORW \\
     Know ‘IMAGE (\m. NegInf) univ(:num) = (\y. y = NegInf)’
     >- (rw [Once EXTENSION]) >> Rewr' \\
     rw [sup_const])
 >> FULL_SIMP_TAC bool_ss [] (* this asserts ‘Z’ *)
 >> Know ‘!k. Z <= k ==> inf {a n | k <= n} <> NegInf’
 >- (rw [lt_infty] \\
     MATCH_MP_TAC lte_trans \\
     Q.EXISTS_TAC ‘inf {a n | Z <= n}’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
                          Q.EXISTS_TAC ‘n’ >> rw []) \\
     rw [GSYM lt_infty])
 >> DISCH_TAC
 (* applying sup_lt_epsilon' *)
 >> Know ‘!e. 0 < e ==>
              ?N. Z <= N /\ !k. N <= k ==> abs (L - inf {a n | k <= n}) < Normal e’
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC ‘P = IMAGE (\m. inf {a n | m <= n}) UNIV’ \\
     Know ‘?x. x IN P /\ sup P < x + Normal e’
     >- (MATCH_MP_TAC sup_lt_epsilon' \\
        ‘sup P = L’ by METIS_TAC [ext_liminf_def] >> POP_ORW \\
         rw [extreal_of_num_def, extreal_lt_eq, Abbr ‘P’] \\
         Q.EXISTS_TAC ‘inf {a n | Z <= n}’ >> rw [] \\
         Q.EXISTS_TAC ‘Z’ >> rw []) \\
     rw [Abbr ‘P’, GSYM ext_liminf_def] (* this asserts ‘m’ *) \\
     Q.EXISTS_TAC ‘MAX m Z’ >> rw [] \\
     Know ‘abs (L - inf {a n | k <= n}) = L - inf {a n | k <= n}’
     >- (rw [abs_refl] \\
         Suff ‘0 <= L - inf {a n | k <= n} <=> inf {a n | k <= n} <= L’ >- rw [] \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC sub_zero_le >> rw []) >> Rewr' \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘L - inf {a n | m <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_lsub_imp \\
                  MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
                  Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC sub_lt_imp2 >> rw [add_comm_normal])
 >> DISCH_TAC
 (* applying lt_inf_epsilon' *)
 >> Know ‘!e. 0 < e ==>
              !k. Z <= k ==> ?l. k <= l /\ abs (a l - inf {a n | k <= n}) < Normal e’
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC ‘P = {a n | k <= n}’ \\
     Know ‘?x. x IN P /\ x < inf P + Normal e’
     >- (MATCH_MP_TAC lt_inf_epsilon' \\
         rw [Abbr ‘P’, extreal_of_num_def, extreal_lt_eq] \\
         Q.EXISTS_TAC ‘a k’ >> rw [] \\
         Q.EXISTS_TAC ‘k’ >> rw []) >> rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
     Know ‘abs (a n - inf {a n | k <= n}) = a n - inf {a n | k <= n}’
     >- (rw [abs_refl] \\
         Know ‘0 <= a n - inf {a n | k <= n} <=> inf {a n | k <= n} <= a n’
         >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             MATCH_MP_TAC sub_zero_le >> rw []) >> Rewr' \\
         rw [inf_le'] >> FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘n’ >> rw []) >> Rewr' \\
     MATCH_MP_TAC sub_lt_imp2 >> rw [add_comm_normal])
 >> DISCH_TAC
 (* combine the previous two results, applying abs_triangle_neg

    NOTE: now we go beyond the textbook proofs, to assert a "successor" function f
    which turns a previous (a l) (l starts from 0) to the next (a l'), such that
   ‘abs (a l' - L) < Normal (inv &SUC l)’.

    The resulting subsequence is ‘g = \n. FUNPOW f n 0’.
 *)
 >> Know ‘!l. ?l'. l < l' /\ abs (a l' - L) < Normal (inv (&SUC l))’
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC ‘(e :real) = inv (&SUC l)’ \\
     Know ‘0 < e’
     >- (Q.UNABBREV_TAC ‘e’ \\
         MATCH_MP_TAC REAL_INV_POS >> rw []) >> DISCH_TAC \\
    ‘0 < e / 2’ by rw [REAL_LT_DIV] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e / 2’)) \\
     RW_TAC std_ss [] (* this asserts ‘N’ *) \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> !k. P’ (MP_TAC o (Q.SPEC ‘e / 2’)) \\
     RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘!k. Z <= k ==> ?l. P’ (MP_TAC o (Q.SPEC ‘MAX N (SUC l)’)) \\
     RW_TAC std_ss [MAX_LE] (* this asserts ‘l'’ *) \\
     Q.EXISTS_TAC ‘l'’ >> rw [] (* l < l' *) \\

     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘abs (a l' - inf {a n | MAX N (SUC l) <= n}) +
                   abs (L    - inf {a n | MAX N (SUC l) <= n})’ \\
     reverse CONJ_TAC
     >- (‘e = e / 2 + e / 2’ by PROVE_TAC [REAL_HALF_DOUBLE] >> POP_ORW \\
         REWRITE_TAC [GSYM extreal_add_def] \\
         MATCH_MP_TAC lt_add2 >> rw []) \\
    ‘?r1. a l' = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r2. L = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     Know ‘inf {a n | MAX N (SUC l) <= n} <> NegInf’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) >> DISCH_TAC \\
    ‘?r3. inf {a n | MAX N (SUC l) <= n} = Normal r3’
       by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_abs_def, extreal_add_def, extreal_le_eq] \\
     Suff ‘r1 - r2 = (r1 - r3) - (r2 - r3)’ >- rw [ABS_TRIANGLE_NEG] \\
     REAL_ARITH_TAC)
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                (SIMP_RULE std_ss [SKOLEM_THM])) (* this asserts ‘f’ *)
 >> Q.ABBREV_TAC ‘g = \n. FUNPOW f n 0’
 >> Q.EXISTS_TAC ‘g’
 (* applying STRICTLY_INCREASING_TC (arithmeticTheory) *)
 >> STRONG_CONJ_TAC (* !m n. m < n ==> g m < g n *)
 >- (MATCH_MP_TAC STRICTLY_INCREASING_TC \\
     rw [Abbr ‘g’, FUNPOW_SUC])
 >> DISCH_TAC
 (* applying MONOTONE_BIGGER (real_topologyTheory) *)
 >> Know ‘!n. n <= g n’
 >- (MATCH_MP_TAC MONOTONE_BIGGER >> art [])
 >> DISCH_TAC
 (* stage work, now touching the goal *)
 >> Know ‘(real o a o g --> real L) sequentially <=>
          !e. 0 < e ==>
              ?N. !n. N <= n ==> abs ((a o g) n - Normal (real L)) < Normal e’
 >- (MATCH_MP_TAC LIM_SEQUENTIALLY_real_normal >> rw []) >> Rewr'
 >> rw [normal_real, o_DEF] (* this asserts ‘e’ *)
 (* find ‘N’ such that ‘&SUC N < 1 / e’ *)
 >> ‘?n. n <> 0 /\ (0 :real) < inv (&n) /\ inv (&n) < (e :real)’
       by METIS_TAC [REAL_ARCH_INV]
 (* stage work, the purpose of ‘N’ is to eliminate ‘Normal e’ *)
 >> Q.EXISTS_TAC ‘n’
 >> Q.X_GEN_TAC ‘m’ >> DISCH_TAC (* this asserts ‘m’ (‘n <= m’) *)
 >> ‘m <> 0’ by rw [] >> Cases_on ‘m’ >- fs []
 >> rename1 ‘SUC N <> 0’
 >> FULL_SIMP_TAC std_ss [Abbr ‘g’, FUNPOW_SUC]
 >> MATCH_MP_TAC lt_trans
 >> Q.ABBREV_TAC ‘l = FUNPOW f N 0’
 >> Q.EXISTS_TAC ‘Normal (inv (&SUC l))’
 >> Q.PAT_X_ASSUM ‘!l. l < f l /\ P’ (MP_TAC o (Q.SPEC ‘l’))
 >> RW_TAC std_ss [Abbr ‘l’, extreal_lt_eq]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘inv (&SUC N)’
 >> CONJ_TAC
 >- (Know ‘inv (&SUC (FUNPOW f N 0)) <= (inv (&SUC N) :real) <=>
           &SUC N <= (&SUC (FUNPOW f N 0)) :real’
     >- (MATCH_MP_TAC REAL_INV_LE_ANTIMONO >> rw []) >> Rewr' \\
     rw [])
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘inv (&n)’ >> art []
 >> Know ‘inv (&SUC N) <= (inv (&n) :real) <=> &n <= (&SUC N :real)’
 >- (MATCH_MP_TAC REAL_INV_LE_ANTIMONO >> rw [])
 >> Rewr'
 >> RW_TAC real_ss []
QED

(* Properties A.1 (iv) [1, p.409] *)
Theorem ext_limsup_imp_subseq :
    !a. (!n. a n <> PosInf /\ a n <> NegInf) /\
        limsup a <> PosInf /\ limsup a <> NegInf ==>
        ?f. (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> real (limsup a)) sequentially
Proof
    rw [ext_limsup_alt_liminf]
 >> Know ‘liminf (numeric_negate o a) <> PosInf’
 >- (CCONTR_TAC >> fs [extreal_ainv_def])
 >> DISCH_TAC
 >> Know ‘liminf (numeric_negate o a) <> NegInf’
 >- (CCONTR_TAC >> fs [extreal_ainv_def])
 >> DISCH_TAC
 >> Know ‘real (-liminf (numeric_negate o a)) = -real (liminf (numeric_negate o a))’
 >- (REWRITE_TAC [GSYM extreal_11, GSYM extreal_ainv_def] \\
     rw [normal_real])
 >> Rewr'
 >> Know ‘?f. (!m n. m < n ==> f m < f n) /\
              (real o (numeric_negate o a) o f -->
               real (liminf (numeric_negate o a))) sequentially’
 >- (MATCH_MP_TAC ext_liminf_imp_subseq >> rw [o_DEF] \\
    ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> rw [extreal_ainv_def])
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘f’ >> art []
 >> Q.ABBREV_TAC ‘l = real (liminf (numeric_negate o a))’
 >> Q.ABBREV_TAC ‘g = real o (numeric_negate o a) o f’
 >> Suff ‘real o a o f = \n. -g n’
 >- (Rewr' >> MATCH_MP_TAC real_topologyTheory.LIM_NEG >> art [])
 >> rw [o_DEF, Abbr ‘g’, FUN_EQ_THM]
 >> REWRITE_TAC [GSYM extreal_11, GSYM extreal_ainv_def]
 >> Know ‘-a (f n) <> PosInf /\ -a (f n) <> NegInf’
 >- (‘?r. a (f n) = Normal r’ by METIS_TAC [extreal_cases] \\
     rw [extreal_ainv_def])
 >> STRIP_TAC
 >> rw [normal_real]
QED

(* Properties A.1 (v) [1, p.409] (full version) *)
Theorem ext_limsup_thm :
    !a l. (!n. a n <> PosInf /\ a n <> NegInf) ==>
          ((real o a --> l) sequentially <=>
           limsup a = Normal l /\ liminf a = Normal l)
Proof
    rpt STRIP_TAC
 >> EQ_TAC (* easy part first *)
 >- (DISCH_TAC \\
     MP_TAC (Q.SPECL [‘a’, ‘I’, ‘l’] ext_limsup_le_subseq) \\
     MP_TAC (Q.SPECL [‘a’, ‘I’, ‘l’] ext_liminf_le_subseq) \\
     RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘limsup a <> NegInf’
       >- (fs [lt_infty] >> MATCH_MP_TAC lte_trans \\
           Q.EXISTS_TAC ‘Normal l’ >> rw [lt_infty]) >> DISCH_TAC \\
       (* ‘(real o a --> l) sequentially’ cannot hold if limsup a = PosInf *)
       Know ‘limsup a <> PosInf’
       >- (rw [ext_limsup_def] \\
           CCONTR_TAC >> fs [] \\
          ‘!e. 0 < e ==> ?N. !n. N <= n ==> abs (a n - Normal l) < Normal e’
             by METIS_TAC [LIM_SEQUENTIALLY_real_normal] \\
           Q.ABBREV_TAC ‘P = IMAGE (\m. sup {a n | m <= n}) UNIV’ \\
           Suff ‘?x. x IN P /\ x < PosInf’
           >- (DISCH_TAC >> fs [Abbr ‘P’] \\
               Know ‘inf (IMAGE (\m. sup {a n | m <= n}) UNIV) < PosInf’
               >- (rw [GSYM inf_lt'] \\
                   Q.EXISTS_TAC ‘sup {a n | m <= n}’ >> rw [] \\
                   Q.EXISTS_TAC ‘m’ >> rw []) \\
               rw [lt_infty]) \\
           rw [Abbr ‘P’] \\
           POP_ASSUM (MP_TAC o (Q.SPEC ‘1’)) >> rw [abs_bounds_lt] \\
           Q.EXISTS_TAC ‘sup {a n | N <= n}’ \\
           CONJ_TAC >- (Q.EXISTS_TAC ‘N’ >> rw []) \\
           MATCH_MP_TAC let_trans \\
           Q.EXISTS_TAC ‘Normal (1 + l)’ >> rw [lt_infty, sup_le'] \\
           rw [GSYM extreal_add_def] \\
           MATCH_MP_TAC lt_imp_le \\
           Know ‘a n < Normal 1 + Normal l <=> a n - Normal l < Normal 1’
           >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
               MATCH_MP_TAC sub_lt_eq >> rw []) >> Rewr' \\
           METIS_TAC []) >> DISCH_TAC \\
       Know ‘?f. (!m n. m < n ==> f m < f n) /\
                 (real o a o f --> real (limsup a)) sequentially’
       >- (MATCH_MP_TAC ext_limsup_imp_subseq >> art []) >> STRIP_TAC \\
       Know ‘(real o a o f --> l) sequentially’
       >- (REWRITE_TAC [o_ASSOC] \\
           MATCH_MP_TAC LIM_SUBSEQUENCE >> art []) >> DISCH_TAC \\
       Know ‘real (limsup a) = l’
       >- (METIS_TAC [LIM_UNIQUE, TRIVIAL_LIMIT_SEQUENTIALLY]) \\
       REWRITE_TAC [GSYM extreal_11] \\
       ASM_SIMP_TAC std_ss [normal_real],
       (* goal 2 (of 2) *)
       Know ‘liminf a <> PosInf’
       >- (fs [lt_infty] >> MATCH_MP_TAC let_trans \\
           Q.EXISTS_TAC ‘Normal l’ >> rw [lt_infty]) >> DISCH_TAC \\
       (* if liminf a = NegInf, ‘(real o a --> l) sequentially’ cannot hold *)
       Know ‘liminf a <> NegInf’
       >- (rw [ext_liminf_def] \\
           CCONTR_TAC >> fs [] \\
          ‘!e. 0 < e ==> ?N. !n. N <= n ==> abs (a n - Normal l) < Normal e’
             by METIS_TAC [LIM_SEQUENTIALLY_real_normal] \\
           Q.ABBREV_TAC ‘P = IMAGE (\m. inf {a n | m <= n}) UNIV’ \\
           Suff ‘?x. x IN P /\ NegInf < x’
           >- (DISCH_TAC >> fs [Abbr ‘P’] \\
               Know ‘NegInf < sup (IMAGE (\m. inf {a n | m <= n}) UNIV)’
               >- (rw [lt_sup] \\
                   Q.EXISTS_TAC ‘inf {a n | m <= n}’ >> rw [] \\
                   Q.EXISTS_TAC ‘m’ >> rw []) \\
               rw [lt_infty]) \\
           rw [Abbr ‘P’] \\
           POP_ASSUM (MP_TAC o (Q.SPEC ‘1’)) >> rw [abs_bounds_lt] \\
           Q.EXISTS_TAC ‘inf {a n | N <= n}’ \\
           CONJ_TAC >- (Q.EXISTS_TAC ‘N’ >> rw []) \\
           MATCH_MP_TAC lte_trans \\
           Q.EXISTS_TAC ‘Normal (-1 + l)’ >> rw [lt_infty, le_inf'] \\
           rw [GSYM extreal_add_def, GSYM extreal_ainv_def] \\
           MATCH_MP_TAC lt_imp_le \\
           Know ‘-Normal 1 + Normal l < a n <=> -Normal 1 < a n - Normal l’
           >- (MATCH_MP_TAC lt_sub >> rw [extreal_ainv_def]) >> Rewr' \\
           METIS_TAC []) >> DISCH_TAC \\
       Know ‘?f. (!m n. m < n ==> f m < f n) /\
                 (real o a o f --> real (liminf a)) sequentially’
       >- (MATCH_MP_TAC ext_liminf_imp_subseq >> art []) >> STRIP_TAC \\
       Know ‘(real o a o f --> l) sequentially’
       >- (REWRITE_TAC [o_ASSOC] \\
           MATCH_MP_TAC LIM_SUBSEQUENCE >> art []) >> DISCH_TAC \\
    (* applying LIM_UNIQUE *)
       Know ‘real (liminf a) = l’
       >- (METIS_TAC [LIM_UNIQUE, TRIVIAL_LIMIT_SEQUENTIALLY]) \\
       REWRITE_TAC [GSYM extreal_11] \\
       ASM_SIMP_TAC std_ss [normal_real] ])
 (* stage work, now the hard part *)
 >> STRIP_TAC
 (* eventually ‘inf {a n | k <= n}’ (increasing) is normal *)
 >> Cases_on ‘!N1. inf {a n | N1 <= n} = NegInf’
 >- (Suff ‘liminf a = NegInf’ >- fs [] \\
     SIMP_TAC std_ss [ext_liminf_def] >> POP_ORW \\
     Know ‘IMAGE (\m. NegInf) univ(:num) = (\y. y = NegInf)’
     >- (rw [Once EXTENSION]) >> Rewr' \\
     rw [sup_const])
 (* eventually ‘sup {a n | k <= n}’ (decreasing) is normal *)
 >> Cases_on ‘!N2. sup {a n | N2 <= n} = PosInf’
 >- (Suff ‘limsup a = PosInf’ >- fs [] \\
     SIMP_TAC std_ss [ext_limsup_def] >> POP_ORW \\
     Know ‘IMAGE (\m. PosInf) univ(:num) = (\y. y = PosInf)’
     >- (rw [Once EXTENSION]) >> Rewr' \\
     rw [inf_const])
 >> FULL_SIMP_TAC bool_ss [] (* this asserts N1 and N2 *)
 >> Know ‘!k. N1 <= k ==> inf {a n | k <= n} <> NegInf’
 >- (rw [lt_infty] >> MATCH_MP_TAC lte_trans \\
     Q.EXISTS_TAC ‘inf {a n | N1 <= n}’ \\
     CONJ_TAC >- rw [GSYM lt_infty] \\
     MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. N2 <= k ==> sup {a n | k <= n} <> PosInf’
 >- (rw [lt_infty] >> MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘sup {a n | N2 <= n}’ \\
     reverse CONJ_TAC >- rw [GSYM lt_infty] \\
     MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘inf {a n | N1 <= n} <> NegInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘sup {a n | N2 <= n} <> PosInf’ K_TAC
 (* stage work *)
 >> Know ‘!k. 0 <= a k - inf {a n | k <= n}’
 >- (Q.X_GEN_TAC ‘k’ \\
     MATCH_MP_TAC le_sub_imp2 >> rw [inf_le'] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. inf {a n | k <= n} <> PosInf’
 >- (Q.X_GEN_TAC ‘k’ \\
     SPOSE_NOT_THEN (ASSUME_TAC o (SIMP_RULE std_ss [])) \\
     Q.PAT_X_ASSUM ‘!k. 0 <= a k - inf {a n | k <= n}’ (MP_TAC o (Q.SPEC ‘k’)) \\
    ‘?r. a k = Normal r’ by METIS_TAC [extreal_cases] >> art [] \\
     simp [extreal_sub_def, GSYM extreal_lt_def, lt_infty, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘!k. sup {a n | k <= n} <> NegInf’
 >- (rw [lt_infty] \\
     MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘a k’ \\
     CONJ_TAC >- (‘?r. a k = Normal r’ by METIS_TAC [extreal_cases] \\
                  rw [GSYM lt_infty]) \\
     rw [le_sup'] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. a k - inf {a n | k <= n} <= sup {a n | k <= n} - inf {a n | k <= n}’
 >- (Q.X_GEN_TAC ‘k’ \\
     MATCH_MP_TAC le_rsub_imp >> rw [le_sup'] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘P = \(k :num). sup {a n | k <= n} - inf {a n | k <= n}’
 >> Know ‘!k. 0 <= P k’
 >- (rw [Abbr ‘P’] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘a k - inf {a n | k <= n}’ >> rw [])
 >> DISCH_TAC
 (* applying lt_inf_epsilon' on liminf a *)
 >> Q.ABBREV_TAC ‘Q = IMAGE (\m. inf {a n | m <= n}) UNIV’
 >> ‘sup Q = liminf a’ by METIS_TAC [ext_liminf_def]
 >> Know ‘!z. 0 < z ==> ?x. x IN Q /\ sup Q < x + z’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC sup_lt_epsilon' >> rw [Abbr ‘Q’] \\
     Q.EXISTS_TAC ‘inf {a n | N1 <= n}’ >> rw [] \\
     Q.EXISTS_TAC ‘N1’ >> rw [])
 >> POP_ORW >> rw [Abbr ‘Q’]
 (* applying sup_lt_epsilon' on limsup a *)
 >> Q.ABBREV_TAC ‘Q = IMAGE (\m. sup {a n | m <= n}) UNIV’
 >> ‘inf Q = limsup a’ by METIS_TAC [ext_limsup_def]
 >> Know ‘!z. 0 < z ==> ?x. x IN Q /\ x < inf Q + z’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC lt_inf_epsilon' >> rw [Abbr ‘Q’] \\
     Q.EXISTS_TAC ‘sup {a n | N2 <= n}’ >> rw [] \\
     Q.EXISTS_TAC ‘N2’ >> rw [])
 >> POP_ORW >> rw [Abbr ‘Q’]
 (* This is stronger than ‘inf (IMAGE P UNIV) = 0’ *)
 >> Know ‘(real o P --> 0) sequentially’
 >- (rw [LIM_SEQUENTIALLY, o_DEF, dist] \\
    ‘0 < e / 2’ by rw [] \\
     NTAC 2 (Q.PAT_X_ASSUM ‘!z. 0 < z ==> ?x. R’
               (MP_TAC o (Q.SPEC ‘Normal (e / 2)’))) \\
     rw [extreal_of_num_def, extreal_lt_eq] (* this asserts ‘m’ and ‘m'’ *) \\
     fs [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘MAX m m'’ \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     Know ‘inf {a n | m <= n} <> NegInf’
     >- (SPOSE_NOT_THEN (ASSUME_TAC o (SIMP_RULE std_ss [])) \\
         Q.PAT_X_ASSUM ‘Normal l < inf {a n | m <= n} + Normal (e / 2)’ MP_TAC \\
         ASM_REWRITE_TAC [extreal_add_def, lt_infty]) >> DISCH_TAC \\
     Know ‘inf {a n | i <= n} <> NegInf’
     >- (REWRITE_TAC [lt_infty] >> MATCH_MP_TAC lte_trans \\
         Q.EXISTS_TAC ‘inf {a n | m <= n}’ >> rw [GSYM lt_infty] \\
         MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
         Q.EXISTS_TAC ‘n’ >> rw []) >> DISCH_TAC \\
     Know ‘sup {a n | m' <= n} <> PosInf’
     >- (SPOSE_NOT_THEN (ASSUME_TAC o (SIMP_RULE std_ss [])) \\
         Q.PAT_X_ASSUM ‘sup {a n | m' <= n} < Normal l + Normal (e / 2)’ MP_TAC \\
         ASM_REWRITE_TAC [extreal_add_def, lt_infty]) >> DISCH_TAC \\
     Know ‘sup {a n | i <= n} <> PosInf’
     >- (REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC ‘sup {a n | m' <= n}’ >> rw [GSYM lt_infty] \\
         MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
         Q.EXISTS_TAC ‘n’ >> rw []) >> DISCH_TAC \\
     Know ‘abs (real (sup {a n | i <= n} - inf {a n | i <= n})) =
                real (sup {a n | i <= n} - inf {a n | i <= n})’
     >- (rw [abs_refl] \\
         RW_TAC std_ss [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         Suff ‘Normal (real (sup {a n | i <= n} - inf {a n | i <= n})) =
                             sup {a n | i <= n} - inf {a n | i <= n}’
         >- RW_TAC std_ss [] \\
         MATCH_MP_TAC normal_real \\
        ‘?r. sup {a n | i <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> Rewr' \\
     REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘Normal (real (sup {a n | i <= n} - inf {a n | i <= n})) =
                         sup {a n | i <= n} - inf {a n | i <= n}’
     >- (MATCH_MP_TAC normal_real \\
        ‘?r. sup {a n | i <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> Rewr' \\
    ‘Normal e = Normal (e / 2) + Normal (e / 2)’
       by METIS_TAC [REAL_HALF_DOUBLE, extreal_add_def, extreal_11] >> POP_ORW \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘sup {a n | m' <= n} - inf {a n | i <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_rsub_imp \\
                  MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
                  Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘sup {a n | m' <= n} - inf {a n | m <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_lsub_imp \\
                  MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
                  Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC lt_trans \\
     Q.EXISTS_TAC ‘Normal l + Normal (e / 2) - inf {a n | m <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC lt_rsub_imp >> rw []) \\
     MATCH_MP_TAC sub_lt_imp2 \\
     NTAC 2 (CONJ_TAC >- rw [extreal_add_def]) \\
     Q.ABBREV_TAC ‘E = e / 2’ \\
     Q.PAT_X_ASSUM ‘Normal l < inf {a n | m <= n} + Normal E’ MP_TAC \\
    ‘?r. inf {a n | m <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     simp [extreal_add_def, extreal_lt_eq] \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘Q = \(k :num). a k - inf {a n | k <= n}’
 >> ‘!k. 0 <= Q k /\ Q k <= P k’ by METIS_TAC []
 >> Know ‘(real o Q --> 0) sequentially’
 >- (Q.PAT_X_ASSUM ‘(real o P --> 0) sequentially’ MP_TAC \\
     rw [LIM_SEQUENTIALLY, o_DEF, dist] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. !n. N <= n ==> abs (real (P n)) < e’
       (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] (* this asserts ‘N’ *) \\
     Q.EXISTS_TAC ‘MAX N (MAX N1 N2)’ \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     Know ‘P i <> PosInf /\ P i <> NegInf’
     >- (simp [Abbr ‘P’] \\
        ‘?r. sup {a n | i <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> STRIP_TAC \\
     Know ‘Q i <> PosInf /\ Q i <> NegInf’
     >- (simp [Abbr ‘Q’] \\
        ‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> STRIP_TAC \\
     Know ‘abs (real (Q i)) = real (Q i)’
     >- (rw [abs_refl] \\
         RW_TAC std_ss [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         Suff ‘Normal (real (Q i)) = Q i’ >- RW_TAC std_ss [] \\
         MATCH_MP_TAC normal_real >> rw []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!n. N <= n ==> abs (real (P n)) < e’
       (fn th => ASSUME_TAC (MATCH_MP th (ASSUME “N <= (i :num)”))) \\
     Know ‘abs (real (P i)) = real (P i)’
     >- (rw [abs_refl] \\
         RW_TAC std_ss [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         Suff ‘Normal (real (P i)) = P i’ >- RW_TAC std_ss [] \\
         MATCH_MP_TAC normal_real >> rw []) >> DISCH_THEN (fs o wrap) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘real (P i)’ >> art [] \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     RW_TAC std_ss [normal_real])
 >> DISCH_TAC
 (* final stage *)
 >> rw [LIM_SEQUENTIALLY_real_normal]
 >> ‘0 < e / 2’ by rw []
 >> Q.PAT_X_ASSUM ‘(real o Q --> 0) sequentially’ MP_TAC
 >> rw [LIM_SEQUENTIALLY, dist]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e / 2’))
 >> RW_TAC std_ss [] (* this asserts ‘N’ *)
 >> FULL_SIMP_TAC std_ss [Abbr ‘Q’]
 >> Q.PAT_X_ASSUM ‘!z. 0 < z ==> ?x. _ /\ Normal l < x + z’
      (MP_TAC o (Q.SPEC ‘Normal (e / 2)’))
 >> rw [extreal_of_num_def, extreal_lt_eq] (* this asserts ‘m’ *)
 >> Q.EXISTS_TAC ‘MAX (MAX N1 N) m’
 >> Q.X_GEN_TAC ‘i’ >> rw []
 >> Know ‘a i - Normal l =
         (a i - inf {a n | i <= n}) + (inf {a n | i <= n} - Normal l)’
 >- (‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] >> POP_ORW \\
     ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_add_def, extreal_sub_def] >> REAL_ARITH_TAC)
 >> Rewr'
 (* applying abs_triangle *)
 >> Q_TAC (TRANS_TAC let_trans) ‘abs (a i - inf {a n | i <= n}) +
                                 abs (inf {a n | i <= n} - Normal l)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC abs_triangle \\
    ‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> ‘Normal e = Normal (e / 2) + Normal (e / 2)’
       by METIS_TAC [REAL_HALF_DOUBLE, extreal_add_def, extreal_11] >> POP_ORW
 >> MATCH_MP_TAC lt_add2
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
     ‘abs (a i - inf {a n | i <= n}) = a i - inf {a n | i <= n}’
        by (rw [abs_refl]) >> POP_ORW \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> _ < e / 2’ (MP_TAC o (Q.SPEC ‘i’)) \\
      RW_TAC std_ss [] \\
     ‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] \\
      POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
     ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] \\
      POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
      FULL_SIMP_TAC std_ss [extreal_sub_def, real_normal, extreal_lt_eq] \\
      FULL_SIMP_TAC std_ss [ABS_BOUNDS_LT],
      (* goal 2 (of 2) *)
      Know ‘abs (inf {a n | i <= n} - Normal l) = -(inf {a n | i <= n} - Normal l)’
      >- (MATCH_MP_TAC abs_neg' \\
          Know ‘inf {a n | i <= n} - Normal l <= 0 <=> inf {a n | i <= n} <= Normal l’
          >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
              MATCH_MP_TAC sub_le_zero >> rw []) >> Rewr' \\
          Q.PAT_X_ASSUM ‘liminf a = Normal l’ (ONCE_REWRITE_TAC o wrap o SYM) \\
          rw [ext_liminf_def, le_sup'] \\
          POP_ASSUM MATCH_MP_TAC \\
          Q.EXISTS_TAC ‘i’ >> rw []) >> Rewr' \\
      Know ‘-(inf {a n | i <= n} - Normal l) = Normal l - inf {a n | i <= n}’
      >- (MATCH_MP_TAC neg_sub \\
          DISJ2_TAC >> rw []) >> Rewr' \\
      MATCH_MP_TAC sub_lt_imp2 >> rw [] \\
      MATCH_MP_TAC lte_trans \\
      Q.EXISTS_TAC ‘inf {a n | m <= n} + Normal (e / 2)’ >> rw [add_comm_normal] \\
      MATCH_MP_TAC le_radd_imp \\
      MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
      Q.EXISTS_TAC ‘n’ >> rw [] ]
QED

(* NOTE: This is a combination of ext_limsup_thm and extreal_lim_sequentially_eq *)
Theorem ext_limsup_thm' :
    !f l. (!n. f n <> PosInf /\ f n <> NegInf) /\ l <> PosInf /\ l <> NegInf ==>
          ((f --> l) sequentially <=> limsup f = l /\ liminf f = l)
Proof
    rpt STRIP_TAC
 >> Know ‘(f --> l) sequentially <=> (real o f --> real l) sequentially’
 >- (MATCH_MP_TAC extreal_lim_sequentially_eq >> art [])
 >> Rewr'
 >> ‘?r. l = Normal r’ by METIS_TAC [extreal_cases]
 >> simp [real_normal]
 >> MATCH_MP_TAC ext_limsup_thm >> art []
QED

(* |- !f g l m.
        (f --> l) sequentially /\ (g --> m) sequentially ==>
        ((\x. f x + g x) --> (l + m)) sequentially
 *)
Theorem lim_sequentially_add = Q.ISPEC ‘sequentially’ EXTREAL_LIM_ADD

Theorem lim_sequentially_sum :
    !f l s. FINITE s /\ (!i. i IN s ==> (f i --> l i) sequentially) /\
           (!i n. i IN s ==> f i n <> PosInf /\ f i n <> NegInf) /\
           (!i. l i <> PosInf /\ l i <> NegInf) ==>
           ((\n. SIGMA (\i. f i n) s) --> SIGMA l s) sequentially
Proof
    qx_genl_tac [‘f’, ‘l’]
 >> Suff ‘!s. FINITE s ==>
             (!i. i IN s ==> (f i --> l i) sequentially) /\
             (!i n. i IN s ==> f i n <> PosInf /\ f i n <> NegInf) /\
             (!i. l i <> PosInf /\ l i <> NegInf) ==>
             ((\n. SIGMA (\i. f i n) s) --> SIGMA l s) sequentially’
 >- METIS_TAC []
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> simp [EXTREAL_LIM_CONST]
 >> rpt STRIP_TAC
 (* applying EXTREAL_SUM_IMAGE_PROPERTY *)
 >> Know ‘!n. SIGMA (\i. f i n) (e INSERT s) =
              (\i. f i n) e + SIGMA (\i. f i n) (s DELETE e)’
 >- (Q.X_GEN_TAC ‘n’ \\
     irule EXTREAL_SUM_IMAGE_PROPERTY >> simp [] \\
     METIS_TAC [])
 >> Rewr'
 >> Know ‘SIGMA l (e INSERT s) = l e + SIGMA l (s DELETE e)’
 >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> simp [])
 >> Rewr'
 >> ‘s DELETE e = s’ by rw [GSYM DELETE_NON_ELEMENT]
 >> simp []
 >> HO_MATCH_MP_TAC lim_sequentially_add >> simp []
 >> ‘(\n. f e n) = f e’ by rw [FUN_EQ_THM] >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC >> simp []
QED

Theorem lim_sequentially_cmul :
    !f l c. (!n. f n <> PosInf /\ f n <> NegInf) /\ l <> PosInf /\ l <> NegInf /\
            c <> PosInf /\ c <> NegInf /\
            (f --> l) sequentially ==> ((\n. c * f n) --> (c * l)) sequentially
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘(g --> m) sequentially’
 >> Know ‘(g --> m) sequentially <=> (real o g --> real m) sequentially’
 >- (MATCH_MP_TAC extreal_lim_sequentially_eq \\
     simp [Abbr ‘g’, Abbr ‘m’] \\
    ‘?l'. l = Normal l'’ by METIS_TAC [extreal_cases] \\
    ‘?c'. c = Normal c'’ by METIS_TAC [extreal_cases] \\
     simp [extreal_mul_def] \\
     Q.EXISTS_TAC ‘0’ >> simp [] \\
     Q.X_GEN_TAC ‘n’ \\
    ‘?r. f n = Normal r’ by METIS_TAC [extreal_cases] \\
     simp [extreal_mul_def])
 >> Rewr'
 >> simp [Abbr ‘g’, Abbr ‘m’, mul_real, o_DEF]
 >> HO_MATCH_MP_TAC LIM_CMUL
 >> ‘(\n. real (f n)) = real o f’ by rw [FUN_EQ_THM, o_DEF] >> POP_ORW
 >> Suff ‘(real o f --> real l) sequentially <=> (f --> l) sequentially’
 >- rw []
 >> SYM_TAC
 >> MATCH_MP_TAC extreal_lim_sequentially_eq >> simp []
QED

(* ------------------------------------------------------------------------- *)
(*   Analytic properties of mono-increasing functions (:extreal -> extreal)  *)
(* ------------------------------------------------------------------------- *)

(* NOTE: “f right_continuous_at x0” (continuous from right) only holds for
   certain mono-increasing functions such as distribution functions.

   It seems meaningless to talk about continuous at infinities, thus the type
   of x0 is :real instead of :extreal.
 *)
val _ = set_fixity "right_continuous_at" (Infix(NONASSOC, 450));

Definition right_continuous_at :
    (f :extreal -> extreal) right_continuous_at x0 <=> inf {f x | x0 < x} = f x0
End

(* cf. continuous_at for the rationale of the conclusion part. The present proof
   is based on inf_seq', which connects the sequential limit to inf IMAGE.
 *)
Theorem right_continuous_at_thm :
    !f x0. (!x y. x <= y ==> f x <= f y) /\ f right_continuous_at (Normal x0) /\
           (!x. f x <> PosInf /\ f x <> NegInf) ==>
            !e. 0 < e /\ e <> PosInf ==>
                ?d. 0 < d /\ !x. x - x0 < d ==> f (Normal x) - f (Normal x0) <= e
Proof
    rw [right_continuous_at]
 >> qabbrev_tac ‘y = f (Normal x0)’
 >> Q.PAT_X_ASSUM ‘inf _ = y’ MP_TAC
 (* preparing for inf_seq' *)
 >> qabbrev_tac ‘g = \n. real (f (Normal (x0 + inv &SUC n)))’
 >> Know ‘mono_decreasing g’
 >- (rw [mono_decreasing_def, Abbr ‘g’] \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     ASM_SIMP_TAC std_ss [normal_real] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 >> DISCH_TAC
 >> Know ‘inf {f x | Normal x0 < x} = inf (IMAGE (\n. Normal (g n)) UNIV)’
 >- (reverse (rw [inf_eq'])
     >- (rw [le_inf', Abbr ‘g’, normal_real] \\
         POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘Normal (x0 + inv (&SUC n))’ >> rw []) \\
     rw [inf_le', Abbr ‘g’, normal_real] \\
     Cases_on ‘x = PosInf’
     >- (Q_TAC (TRANS_TAC le_trans) ‘f (Normal (x0 + inv (&SUC 0)))’ \\
         CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                      Q.EXISTS_TAC ‘0’ >> rw []) \\
         FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
     Cases_on ‘x = NegInf’ >> fs [] \\
    ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] \\
     POP_ASSUM (fs o wrap) >> T_TAC \\
    ‘0 < r - x0’ by rw [REAL_SUB_LT] \\
     drule REAL_ARCH_INV_SUC >> STRIP_TAC \\
     POP_ASSUM (ASSUME_TAC o
                REWRITE_RULE [REAL_LT_SUB_LADD, Once REAL_ADD_COMM]) \\
     Q_TAC (TRANS_TAC le_trans) ‘f (Normal (x0 + inv (&SUC n)))’ \\
     reverse CONJ_TAC
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> simp [] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> Rewr'
 >> ‘?l. y = Normal l’ by METIS_TAC [extreal_cases]
 >> fs [Abbr ‘y’]
 (* applying inf_seq' *)
 >> Know ‘inf (IMAGE (\n. Normal (g n)) univ(:num)) = Normal l <=>
          (g --> l) sequentially’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC inf_seq' >> art [])
 >> Rewr'
 >> rw [LIM_SEQUENTIALLY, metricTheory.dist, Abbr ‘g’]
 >> ‘e <> NegInf’ by rw [pos_not_neginf, lt_imp_le]
 >> ‘?r. 0 < r /\ e = Normal r’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> _’ (MP_TAC o Q.SPEC ‘r’) >> rw []
 >> Q.EXISTS_TAC ‘inv &SUC N’
 >> CONJ_TAC >- (MATCH_MP_TAC REAL_INV_POS >> rw [])
 >> rpt STRIP_TAC
 (* redefine g as the real version of f *)
 >> qabbrev_tac ‘g = real o f’
 >> Know ‘!x. f x = Normal (g x)’
 >- (rw [Abbr ‘g’] \\
     rw [normal_real])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> FULL_SIMP_TAC std_ss [real_normal, extreal_le_eq, extreal_sub_def, extreal_11]
 >> Q.PAT_X_ASSUM ‘!n. N <= n ==> _’ (MP_TAC o Q.SPEC ‘N’)
 >> simp []
 >> Know ‘abs (g (Normal (x0 + inv (&SUC N))) - l) =
               g (Normal (x0 + inv (&SUC N))) - l’
 >- (simp [ABS_REFL, REAL_SUB_LE] \\
     Q.PAT_X_ASSUM ‘_ = l’ (REWRITE_TAC o wrap o SYM) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> simp [])
 >> Rewr'
 >> DISCH_TAC
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘g (Normal (x0 + inv (&SUC N))) - l’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> REWRITE_TAC [REAL_LE_SUB_CANCEL2]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp []
 >> REWRITE_TAC [Once REAL_ADD_COMM]
 >> REWRITE_TAC [GSYM REAL_LE_SUB_RADD]
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

(* A function is "right-continuous" if it's right-continuous at every point.

   NOTE: the requirement of mono-increasing is included since this version of
  "right-continuous" definition only works on mono-increasing functions.

   NOTE: The concept of "right-continuous" at points PosInf/NegInf is tricky,
   and (may) not be true for all distribution functions, thus is excluded.
 *)
Definition right_continuous :
    right_continuous (f :extreal -> extreal) <=>
      (!x y. x <= y ==> f x <= f y) /\ !x. f right_continuous_at (Normal x)
End

(* |- !f. right_continuous f <=>
         (!x y. x <= y ==> f x <= f y) /\ !x. inf {f x' | x < x'} = f (Normal x)
 *)
Theorem right_continuous_def =
        right_continuous |> REWRITE_RULE [right_continuous_at]

(* NOTE: This core lemma holds also for other shapes of intervals (not used) *)
Theorem countable_disjoint_interval_lemma :
    !s. s = {interval (c,d) | c < d} /\ disjoint s ==> countable s
Proof
    simp [disjoint_def, IN_INTERVAL] >> DISCH_TAC
 >> qmatch_abbrev_tac ‘countable s’
 >> MP_TAC Q_DENSE_IN_REAL
 >> simp [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
 >> STRIP_TAC
 (* t is the set of rationals one-one mapping to each open intervals *)
 >> qabbrev_tac ‘g = \e. f (interval_lowerbound e) (interval_upperbound e)’
 >> qabbrev_tac ‘t = IMAGE g s’
 >> Suff ‘cardeq s t’
 >- (DISCH_TAC \\
     Know ‘countable s <=> countable t’
     >- (MATCH_MP_TAC CARD_COUNTABLE_CONG >> art []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘cardeq s t’ K_TAC \\
     MATCH_MP_TAC COUNTABLE_SUBSET \\
     Q.EXISTS_TAC ‘q_set’ \\
     rw [QSET_COUNTABLE, SUBSET_DEF, Abbr ‘t’, Abbr ‘g’, Abbr ‘s’] \\
     simp [OPEN_INTERVAL_LOWERBOUND, OPEN_INTERVAL_UPPERBOUND])
 (* stage work *)
 >> simp [GSYM CARD_LE_ANTISYM]
 >> reverse CONJ_TAC >- rw [IMAGE_cardleq, Abbr ‘t’]
 >> rw [cardleq_def, INJ_DEF]
 >> Q.EXISTS_TAC ‘g’
 >> CONJ_TAC
 >- (rw [Abbr ‘g’, Abbr ‘t’] \\
     Q.EXISTS_TAC ‘x’ >> art [])
 (* NOTE: from now on the set ‘t’ is no more used *)
 >> rw [Abbr ‘s’, Abbr ‘g’, Abbr ‘t’]
 >> gs [OPEN_INTERVAL_LOWERBOUND, OPEN_INTERVAL_UPPERBOUND]
 >> rename1 ‘f c d = f a b’
 >> CCONTR_TAC
 >> qabbrev_tac ‘y = f a b’
 >> ‘c < y /\ y < d /\ a < y /\ y < b’ by METIS_TAC []
 >> Know ‘DISJOINT (interval (c,d)) (interval (a,b))’ >- METIS_TAC []
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!a b. _’ K_TAC)
 >> simp [DISJOINT_ALT, OPEN_interval]
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

(* NOTE: It's surprising hard to prove such a simple and obvious statement *)
Theorem sup_open_interval :
    !a b. a < b ==> sup (open_interval a b) = b
Proof
    rw [open_interval_def]
 >> simp [GSYM le_antisym]
 >> CONJ_TAC
 >- (rw [sup_le'] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> MATCH_MP_TAC le_epsilon
 >> rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘b <= c + e’
 >> Know ‘e <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> DISCH_TAC
 >> Know ‘b <= c + e <=> b - e <= c’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC sub_le_eq >> art [])
 >> Rewr'
 >> rw [Abbr ‘c’, le_sup']
 >> Cases_on ‘b = PosInf’
 >- (‘?r. 0 < r /\ e = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     POP_ORW \\
     rw [extreal_sub_def] \\
     CCONTR_TAC >> fs [GSYM extreal_lt_def] \\
     MP_TAC (Q.SPECL [‘max a y’, ‘PosInf’] extreal_mean) \\
     ASM_REWRITE_TAC [max_lt] \\
     CCONTR_TAC >> fs [] \\
     METIS_TAC [let_antisym])
 (* b cannot be NegInf because a < b *)
 >> Cases_on ‘b = NegInf’ >- fs [lt_infty]
 >> MP_TAC (Q.SPECL [‘max a (b - e)’, ‘b’] extreal_mean) >> simp [max_lt]
 >> impl_tac >- rw [sub_lt_eq, lt_addr]
 >> STRIP_TAC
 >> ‘z <= y’ by rw []
 >> Q_TAC (TRANS_TAC le_trans) ‘z’ >> art []
 >> MATCH_MP_TAC lt_imp_le >> art []
QED

Theorem inf_open_interval :
    !a b. a < b ==> inf (open_interval a b) = a
Proof
    rw [open_interval_def]
 >> simp [GSYM le_antisym]
 >> reverse CONJ_TAC
 >- (rw [le_inf'] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> MATCH_MP_TAC le_epsilon
 >> rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘c <= a + e’
 >> Know ‘e <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> DISCH_TAC
 >> rw [Abbr ‘c’, inf_le']
 >> Cases_on ‘a = NegInf’
 >- (‘?r. 0 < r /\ e = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     POP_ORW \\
     rw [extreal_add_def] \\
     CCONTR_TAC >> fs [GSYM extreal_lt_def] \\
     MP_TAC (Q.SPECL [‘NegInf’, ‘min b y’] extreal_mean) \\
     ASM_REWRITE_TAC [lt_min] \\
     CCONTR_TAC >> fs [] \\
     METIS_TAC [let_antisym])
 >> Cases_on ‘a = PosInf’ >- fs [lt_infty]
 >> MP_TAC (Q.SPECL [‘a’, ‘min (a + e) b’] extreal_mean) >> simp [lt_min]
 >> impl_tac >- rw [sub_lt_eq, lt_addr]
 >> STRIP_TAC
 >> ‘y <= z’ by rw []
 >> Q_TAC (TRANS_TAC le_trans) ‘z’ >> art []
 >> MATCH_MP_TAC lt_imp_le >> art []
QED

(* NOTE: This is the extreal version of the core lemma we actually used. *)
Theorem countable_disjoint_open_interval_lemma :
    !s. s SUBSET {open_interval c d | c < d} /\ disjoint s ==> countable s
Proof
    rw [SUBSET_DEF, disjoint_def, IN_open_interval]
 >> MP_TAC Q_DENSE_IN_R' (* instead of Q_DENSE_IN_REAL *)
 >> simp [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
 >> STRIP_TAC
 (* t is the set of rationals one-one mapping to each open intervals *)
 >> qabbrev_tac ‘g = \e. f (inf e) (sup e)’
 >> qabbrev_tac ‘t = IMAGE g s’
 >> Suff ‘cardeq s t’
 >- (DISCH_TAC \\
     Know ‘countable s <=> countable t’
     >- (MATCH_MP_TAC CARD_COUNTABLE_CONG >> art []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘cardeq s t’ K_TAC \\
     MATCH_MP_TAC COUNTABLE_SUBSET \\
     Q.EXISTS_TAC ‘q_set’ \\
     rw [QSET_COUNTABLE, SUBSET_DEF, Abbr ‘t’, Abbr ‘g’] \\
     Q.PAT_X_ASSUM ‘!x. x IN s ==> ?c d. _’ drule >> rw [] \\
     simp [inf_open_interval, sup_open_interval])
 (* stage work *)
 >> simp [GSYM CARD_LE_ANTISYM]
 >> reverse CONJ_TAC >- rw [IMAGE_cardleq, Abbr ‘t’]
 >> rw [cardleq_def, INJ_DEF]
 >> Q.EXISTS_TAC ‘g’
 >> CONJ_TAC
 >- (rw [Abbr ‘g’, Abbr ‘t’] \\
     Q.EXISTS_TAC ‘x’ >> art [])
 (* NOTE: from now on the set ‘t’ is no more used *)
 >> rw [Abbr ‘g’, Abbr ‘t’]
 >> ‘?a b. x = open_interval a b /\ a < b’ by METIS_TAC []
 >> ‘?c d. y = open_interval c d /\ c < d’ by METIS_TAC []
 >> gs [inf_open_interval, sup_open_interval]
 >> CCONTR_TAC
 >> qabbrev_tac ‘z = f c d’
 >> ‘a < Normal z /\ Normal z < b /\ c < Normal z /\ Normal z < d’ by METIS_TAC []
 >> Know ‘DISJOINT (open_interval a b) (open_interval c d)’ >- METIS_TAC []
 >> Q.PAT_X_ASSUM ‘!a b. _ ==> DISJOINT a b’ K_TAC
 >> simp [DISJOINT_ALT, IN_open_interval]
 >> Q.EXISTS_TAC ‘Normal z’ >> art []
QED

(* NOTE: This definition does not assume f is left or right-continuous. *)
val _ = set_fixity "jumping_point_of" (Infix(NONASSOC, 450));

Definition jumping_point_of :
    x0 jumping_point_of (f :extreal -> extreal) <=>
    sup {f x | x < Normal x0} <> inf {f x | Normal x0 < x}
End

(* A jumping point is indeed "jumping".

   NOTE: Although the jumping point is :real (i.e. meaningless at PosInf/NegInf),
   the function values, however, may jump from NegInf to PosInf (of course, such
   a big jumping can only happen once if exists.) For distribution functions
   ranged from 0 to 1 this is impossible, but the present definition is general.
 *)
Theorem jumping_point_of_jumping :
    !f x0. (!x y. x <= y ==> f x <= f y) /\ x0 jumping_point_of f ==>
           sup {f x | x < Normal x0} < inf {f x | Normal x0 < x}
Proof
    rw [jumping_point_of, lt_le]
 >> rw [sup_le']
 >> rw [le_inf']
 >> Q_TAC (TRANS_TAC le_trans) ‘f (Normal x0)’ >> rw []
QED

(* NOTE: The set of "jumping points" is simply {x | x jumping_point_of f}.
   The next “jumping_area” is a set of all ranges of f where f is jumping, and
   therefore “BIGUNION (jumping_area f)” is the actual range (as set of reals)
   where f is jumping. f is continuous outside of this range.
 *)
val _ = set_fixity "flat_area_of" (Infix(NONASSOC, 450));

Definition jumping_area_def :
    jumping_area f = {open_interval a b | ?x0. x0 jumping_point_of f /\
                                               a = sup {f x | x < Normal x0} /\
                                               b = inf {f x | Normal x0 < x}}
End

(* NOTE: There may be jumping points between x0 and y0, but at this moment we
   don't know if these jumping points are countable or not.
 *)
Theorem mono_increasing_lemma :
    !f x0 y0. (!x y. x <= y ==> f x <= f y) /\ x0 < y0 ==>
              inf {f x | Normal x0 < x} <= sup {f x | x < Normal y0}
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘x0’, ‘y0’] REAL_MEAN) >> rw []
 >> Q_TAC (TRANS_TAC le_trans) ‘f (Normal z)’
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC inf_le_imp' >> rw [] \\
      Q.EXISTS_TAC ‘Normal z’ >> rw [extreal_lt_eq],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC le_sup_imp' >> rw [] \\
      Q.EXISTS_TAC ‘Normal z’ >> rw [extreal_lt_eq] ]
QED

(* NOTE: This is saying the number of (disjoint) jumping areas is countable.
   The entire big union of all jumping areas is still uncountable (if exists).
 *)
Theorem jumping_area_countable :
    !f. (!x y. x <= y ==> f x <= f y) ==> countable (jumping_area f)
Proof
    rw [jumping_area_def]
 >> MATCH_MP_TAC countable_disjoint_open_interval_lemma
 >> CONJ_TAC
 >- (rw [SUBSET_DEF] \\
     qexistsl_tac [‘sup {f x | x < Normal x0}’,
                   ‘inf {f x | Normal x0 < x}’] >> art [] \\
     MATCH_MP_TAC jumping_point_of_jumping >> art [])
 >> rw [disjoint_def]
 >> rename1 ‘y0 jumping_point_of f’
 >> rw [DISJOINT_ALT, IN_open_interval]
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘open_interval _ _ <> open_interval _ _’ MP_TAC >> fs []
 >> qmatch_abbrev_tac ‘open_interval a b = open_interval c d’
 >> fs [jumping_point_of]
 >> ‘a < b /\ c < d’ by METIS_TAC [lt_trans]
 >> Cases_on ‘x0 = y0’ >> fs []
 >> ‘x0 < y0 \/ y0 < x0’ by METIS_TAC [REAL_LT_TOTAL]
 >| [ (* goal 1 (of 2) *)
     ‘b <= c’ by METIS_TAC [mono_increasing_lemma] \\
     ‘x < c’ by METIS_TAC [lte_trans] \\
      METIS_TAC [lt_antisym],
      (* goal 2 (of 2) *)
     ‘d <= a’ by METIS_TAC [mono_increasing_lemma] \\
     ‘x < a’ by METIS_TAC [lte_trans] \\
      METIS_TAC [lt_antisym] ]
QED

Theorem open_interval_11 :
    !a b c d. a < b /\ c < d ==>
             (open_interval a b = open_interval c d <=> a = c /\ b = d)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- rw []
 >> rw [Once EXTENSION, IN_open_interval]
 >| [ (* goal 1 (of 2) *)
      CCONTR_TAC \\
     ‘a < c \/ c < a’ by METIS_TAC [lt_total] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2): c--------d
                        a-z------b *)
        MP_TAC (Q.SPECL [‘a’, ‘min b c’] extreal_mean) >> rw [lt_min] \\
        CCONTR_TAC >> fs [] \\
        METIS_TAC [lt_antisym],
        (* goal 1.2 (of 2): a--------b
                        c-z------d *)
        MP_TAC (Q.SPECL [‘c’, ‘min a d’] extreal_mean) >> rw [lt_min] \\
        CCONTR_TAC >> fs [] \\
        METIS_TAC [lt_antisym] ],
      (* goal 2 (of 2) *)
      CCONTR_TAC \\
     ‘b < d \/ d < b’ by METIS_TAC [lt_total] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2): c------z-d
                        a--------b *)
        MP_TAC (Q.SPECL [‘max b c’, ‘d’] extreal_mean) >> rw [max_lt] \\
        CCONTR_TAC >> fs [] \\
        METIS_TAC [lt_antisym],
        (* goal 1.2 (of 2): a------z-b
                        c--------d *)
        MP_TAC (Q.SPECL [‘max a d’, ‘b’] extreal_mean) >> rw [max_lt] \\
        CCONTR_TAC >> fs [] \\
        METIS_TAC [lt_antisym] ] ]
QED

(* NOTE: This is also Lemma 14.14 of [1. p.147] *)
Theorem countable_jumping_point_of :
    !f. (!x y. x <= y ==> f x <= f y) ==> countable {x | x jumping_point_of f}
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘countable s’
 >> Suff ‘countable s <=> countable (jumping_area f)’
 >- (Rewr' \\
     MATCH_MP_TAC jumping_area_countable >> art [])
 >> MATCH_MP_TAC CARD_COUNTABLE_CONG
 >> rw [cardeq_def, Abbr ‘s’]
 >> qabbrev_tac ‘g = \x0. let a = sup {f x | x < Normal x0};
                              b = inf {f x | Normal x0 < x} in
                            open_interval a b’
 >> Q.EXISTS_TAC ‘g’
 >> rw [BIJ_THM, Abbr ‘g’, jumping_area_def]
 >- (qexistsl_tac [‘sup {f x | x < Normal x0}’,
                   ‘inf {f x | Normal x0 < x}’] >> art [] \\
     Q.EXISTS_TAC ‘x0’ >> art [])
 >> rw [EXISTS_UNIQUE_ALT]
 >> Q.EXISTS_TAC ‘x0’
 >> Q.X_GEN_TAC ‘y0’
 >> reverse EQ_TAC >- (rw [] >> rw [])
 >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> qmatch_abbrev_tac ‘open_interval c d = open_interval a b ==> _’
 >> ‘a < b /\ c < d’ by METIS_TAC [jumping_point_of_jumping]
 >> simp [open_interval_11]
 >> STRIP_TAC
 >> CCONTR_TAC
 >> ‘x0 < y0 \/ y0 < x0’ by METIS_TAC [REAL_LT_TOTAL]
 >| [ (* goal 1 (of 2) *)
     ‘b <= c’ by METIS_TAC [mono_increasing_lemma] \\
     ‘a < c’ by METIS_TAC [lte_trans] \\
      METIS_TAC [lt_le],
      (* goal 2 (of 2) *)
     ‘d <= a’ by METIS_TAC [mono_increasing_lemma] \\
     ‘d < b’ by METIS_TAC [let_trans] \\
      METIS_TAC [lt_le] ]
QED

(* NOTE: This definition does not assume f is left or right-continuous.
   For constant function (\x. c), “(NegInf,PosInf) flat_area_of f” should hold.
 *)
Definition flat_area_of :
   (a,b) flat_area_of (f :extreal -> extreal) <=> a < b /\
        ?c. (!x. a < x /\ x < b ==> f x = c) /\
            (!x. x < a ==> f x < c) /\ (!x. b < x ==> c < f x)
End

Definition flat_areas_def :
    flat_areas f = {open_interval a b | (a,b) flat_area_of f}
End

Theorem flat_areas_countable :
    !f. (!x y. x <= y ==> f x <= f y) ==> countable (flat_areas f)
Proof
    rw [flat_areas_def]
 >> MATCH_MP_TAC countable_disjoint_open_interval_lemma
 >> CONJ_TAC
 >- (rw [SUBSET_DEF, flat_area_of] \\
     qexistsl_tac [‘a’, ‘b’] >> art [])
 >> rw [disjoint_def]
 >> rw [DISJOINT_ALT, IN_open_interval]
 >> CCONTR_TAC >> fs []
 >> Q.PAT_X_ASSUM ‘open_interval _ _ <> open_interval _ _’ MP_TAC >> fs []
 >> qmatch_abbrev_tac ‘open_interval a b = open_interval c d’
 >> fs [flat_area_of]
 >> NTAC 4 (POP_ASSUM K_TAC)
 >> simp [open_interval_11]
 >> ‘c' = c''’ by METIS_TAC []
 >> POP_ASSUM (fs o wrap o SYM)
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      CCONTR_TAC \\
     ‘a < c \/ c < a’ by METIS_TAC [lt_total] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2): a_z_c___________/__/
                           /   /           b  d *)
        MP_TAC (Q.SPECL [‘a’, ‘min b c’] extreal_mean) >> rw [lt_min] \\
        CCONTR_TAC >> fs [] \\
       ‘f z = c' /\ f z < c'’ by METIS_TAC [] \\
        METIS_TAC [lt_le],
        (* goal 1.2 (of 2): c_z_a___________/__/
                           /   /           d  b *)
        MP_TAC (Q.SPECL [‘c’, ‘min a d’] extreal_mean) >> rw [lt_min] \\
        CCONTR_TAC >> fs [] \\
       ‘f z = c' /\ f z < c'’ by METIS_TAC [] \\
        METIS_TAC [lt_le] ],
      (* goal 2 (of 2) *)
      CCONTR_TAC \\
     ‘b < d \/ d < b’ by METIS_TAC [lt_total] >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2): a__c___________/___/
                           /  /           b z d *)
        MP_TAC (Q.SPECL [‘max b c’, ‘d’] extreal_mean) >> rw [max_lt] \\
        CCONTR_TAC >> fs [] \\
       ‘f z = c' /\ c' < f z’ by METIS_TAC [] \\
        METIS_TAC [lt_le],
        (* goal 2.2 (of 2): c__a___________/___/
                           /  /           d z b *)
        MP_TAC (Q.SPECL [‘max a d’, ‘b’] extreal_mean) >> rw [max_lt] \\
        CCONTR_TAC >> fs [] \\
       ‘f z = c' /\ c' < f z’ by METIS_TAC [] \\
        METIS_TAC [lt_le] ] ]
QED

Theorem countable_flat_area_of :
    !f. (!x y. x <= y ==> f x <= f y) ==> countable {(a,b) | (a,b) flat_area_of f}
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘countable s’
 >> Suff ‘countable s <=> countable (flat_areas f)’
 >- (Rewr' \\
     MATCH_MP_TAC flat_areas_countable >> art [])
 >> MATCH_MP_TAC CARD_COUNTABLE_CONG
 >> rw [cardeq_def, Abbr ‘s’]
 >> qabbrev_tac ‘g = \e. open_interval (FST e) (SND e)’
 >> Q.EXISTS_TAC ‘g’
 >> rw [BIJ_THM, Abbr ‘g’, flat_areas_def]
 >- (qexistsl_tac [‘a’, ‘b’] >> simp [])
 >> rw [EXISTS_UNIQUE_ALT]
 >> Q.EXISTS_TAC ‘(a,b)’
 >> simp [FORALL_PROD]
 >> qx_genl_tac [‘c’, ‘d’]
 >> reverse EQ_TAC >- NTAC 2 (rw [])
 >> STRIP_TAC
 >> fs [flat_area_of]
 >> gs [open_interval_11]
QED

(* NOTE: Both ‘sup o IMAGE f’ and ‘inf o IMAGE f’ are equivalent here. See
  [flat_values_alt] below. The present definition is easier for proving its
   countable.
 *)
Definition flat_values_def :
    flat_values f = IMAGE (sup o IMAGE f) (flat_areas f)
End

Theorem IN_flat_values_lemma[local] :
    !a b. a < b /\ (!x. a < x /\ x < b ==> f x = c) ==>
          IMAGE f (open_interval a b) = (\y. y = c)
Proof
    rpt STRIP_TAC
 >> rw [Once EXTENSION, IN_open_interval]
 >> EQ_TAC >> rw []
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> MP_TAC (Q.SPECL [‘a’, ‘b’] extreal_mean) >> rw []
 >> Q.EXISTS_TAC ‘z’ >> art []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem IN_flat_values :
    !f z. z IN flat_values f <=>
          ?a b. a < b /\ (!x. a < x /\ x < b ==> f x = z) /\
               (!x. x < a ==> f x < z) /\ (!x. b < x ==> z < f x)
Proof
    rw [flat_values_def, flat_areas_def, flat_area_of]
 >> EQ_TAC >> rw []
 >- (qexistsl_tac [‘a’, ‘b’] \\
     Suff ‘IMAGE f (open_interval a b) = (\y. y = c)’
     >- (Rewr' >> simp [sup_const]) \\
     MATCH_MP_TAC IN_flat_values_lemma >> art [])
 >> Q.EXISTS_TAC ‘open_interval a b’
 >> Suff ‘IMAGE f (open_interval a b) = (\y. y = z)’
 >- (Rewr' >> simp [sup_const] \\
     qexistsl_tac [‘a’, ‘b’] >> art [] \\
     Q.EXISTS_TAC ‘z’ >> art [])
 >> MATCH_MP_TAC IN_flat_values_lemma >> art []
QED

Theorem flat_values_alt :
    !f. flat_values f = IMAGE (inf o IMAGE f) (flat_areas f)
Proof
    rw [Once EXTENSION, IN_flat_values]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘open_interval a b’ \\
     Know ‘IMAGE f (open_interval a b) = (\y. y = x)’
     >- (MATCH_MP_TAC IN_flat_values_lemma >> art []) >> Rewr' \\
     simp [inf_const] \\
     rw [flat_areas_def, flat_area_of] \\
     qexistsl_tac [‘a’, ‘b’] >> art [] \\
     Q.EXISTS_TAC ‘x’ >> art [])
 >> fs [flat_areas_def, flat_area_of]
 >> qexistsl_tac [‘a’, ‘b’] >> art []
 >> Know ‘IMAGE f (open_interval a b) = (\y. y = c)’
 >- (MATCH_MP_TAC IN_flat_values_lemma >> art [])
 >> Rewr'
 >> simp [inf_const]
QED

Theorem flat_values_countable :
    !f. (!x y. x <= y ==> f x <= f y) ==> countable (flat_values f)
Proof
    rw [flat_values_def]
 >> MATCH_MP_TAC COUNTABLE_IMAGE
 >> MATCH_MP_TAC flat_areas_countable >> art []
QED

(* ------------------------------------------------------------------------- *)
(* Backwards compatibility: export all theorems moved to extreal_baseTheory  *)
(* ------------------------------------------------------------------------- *)

val _ = map (fn name => save_thm (name, DB.fetch "extreal_base" name))
      ["EXTREAL_ARCH",
       "EXTREAL_EQ_LADD",
       "EXTREAL_EQ_RADD",
       "SIMP_EXTREAL_ARCH", "SIMP_EXTREAL_ARCH_NEG",
       "EXTREAL_ARCH_INV", "EXTREAL_ARCH_INV'",
       "Q_COUNTABLE", "Q_DENSE_IN_R", "Q_not_infty",
       "abs_0",
       "abs_abs",
       "abs_bounds", "abs_bounds_lt",
       "abs_div", "abs_div_normal",
       "abs_eq_0",
       "abs_gt_0",
       "abs_le_0",
       "abs_le_half_pow2",
       "abs_le_square_plus1",
       "abs_max",
       "abs_mul",
       "abs_neg", "abs_neg'", "abs_neg_eq",
       "abs_not_infty",
       "abs_not_zero",
       "abs_pos",
       "abs_pow2",
       "abs_pow_le_mono",
       "abs_real",
       "abs_refl",
       "abs_sub", "abs_sub'",
       "abs_triangle", "abs_triangle_full",
       "abs_triangle_neg", "abs_triangle_neg_full",
       "abs_triangle_sub", "abs_triangle_sub_full",
       "abs_triangle_sub'", "abs_triangle_sub_full'",
       "abs_unbounds",
       "add_assoc",
       "add_comm", "add_comm_normal",
       "add_infty",
       "add_ldistrib",
       "add_ldistrib_pos", "add_ldistrib_neg",
       "add_ldistrib_normal", "add_ldistrib_normal2",
       "add_lzero",
       "add_not_infty",
       "add_pow2", "add_pow2_pos",
       "add_rdistrib",
       "add_rdistrib_normal", "add_rdistrib_normal2",
       "add_rzero",
       "add_sub", "add_sub_normal", "add_sub2",
       "add2_sub2",
       "div_add", "div_add2",
       "div_eq_mul_linv",
       "div_eq_mul_rinv",
       "div_infty",
       "div_mul_refl",
       "div_not_infty",
       "div_one",
       "div_refl", "div_refl_pos",
       "div_sub",
       "entire",
       "eq_add_sub_switch",
       "eq_neg",
       "eq_sub_ladd", "eq_sub_ladd_normal",
       "eq_sub_radd",
       "eq_sub_switch",
       "extreal_11",
       "extreal_abs_def",
       "extreal_add_def", "extreal_add_eq",
       "extreal_ainv_def",
       "extreal_cases",
       "extreal_double",
       "extreal_distinct",
       "extreal_div_def", "extreal_div_eq",
       "extreal_eq_zero",
       "extreal_inv_def", "extreal_inv_eq",
       "extreal_le_def", "extreal_le_eq",
       "extreal_lt_def", "extreal_lt_eq",
       "extreal_mean",
       "extreal_max_def",
       "extreal_min_def",
       "extreal_mul_def",
       "extreal_mul_eq",
       "extreal_of_num_def",
       "extreal_pow_def", "extreal_pow",
       "extreal_sqrt_def",
       "extreal_sub",
       "extreal_sub_add",
       "extreal_sub_def", "extreal_sub_eq",
       "extreal_not_infty",
       "extreal_not_lt",
       "fourths_between",
       "fourth_cancel",
       "half_between",
       "half_cancel",
       "half_double",
       "half_not_infty",
       "infty_div",
       "infty_pow2",
       "inv_1over",
       "inv_infty",
       "inv_inj",
       "inv_inv",
       "inv_le_antimono", "inv_le_antimono_imp",
       "inv_lt_antimono",
       "inv_mul",
       "inv_not_infty",
       "inv_one",
       "inv_pos", "inv_pos'", "inv_pos_eq",
       "ldiv_eq",
       "ldiv_le_imp",
       "le_01", "le_02",
       "le_abs",
       "le_abs_bounds",
       "le_add", "le_add2",
       "le_add_neg",
       "le_addl", "le_addl_imp",
       "le_addr", "le_addr_imp",
       "le_antisym",
       "le_div",
       "le_infty",
       "le_inv",
       "le_ladd", "le_ladd_imp",
       "le_lsub_imp",
       "le_lt",
       "le_ldiv",
       "le_lmul", "le_lmul_imp",
       "le_lneg",
       "le_max", "le_max1", "le_max2",
       "le_min",
       "le_mul", "le_mul_neg",
       "le_mul2",
       "le_neg",
       "le_not_infty",
       "le_num",
       "le_pow2",
       "le_radd", "le_radd_imp",
       "le_refl",
       "le_rmul", "le_rmul_imp",
       "le_rdiv",
       "le_rsub_imp",
       "le_sub_eq", "le_sub_eq2",
       "le_sub_imp", "le_sub_imp2",
       "le_total",
       "le_trans",
       "let_add", "let_add2", "let_add2_alt",
       "let_antisym",
       "let_mul",
       "let_total",
       "let_trans",
       "linv_uniq",
       "lt_01", "lt_02", "lt_10",
       "lt_add", "lt_add2",
       "lt_add_neg",
       "lt_abs_bounds",
       "lt_addl",
       "lt_addr", "lt_addr_imp",
       "lt_antisym",
       "lt_div",
       "lt_imp_le",
       "lt_imp_ne",
       "lt_infty",
       "lt_ladd",
       "lt_ldiv",
       "lt_le",
       "lt_lmul", "lt_lmul_imp",
       "lt_lsub_imp",
       "lt_max",
       "lt_max_between",
       "lt_mul", "lt_mul_neg",
       "lt_mul2",
       "lt_neg",
       "lt_radd",
       "lt_rdiv", "lt_rdiv_neg",
       "lt_refl",
       "lt_rmul", "lt_rmul_imp",
       "lt_rsub_imp",
       "lt_sub", "lt_sub'",
       "lt_sub_imp", "lt_sub_imp'", "lt_sub_imp2",
       "lt_total",
       "lt_trans",
       "lte_add",
       "lte_mul",
       "lte_total",
       "lte_trans",
       "max_comm",
       "max_infty",
       "max_le", "max_le2_imp",
       "max_reduce",
       "max_refl",
       "min_comm",
       "min_infty",
       "min_le", "min_le1", "min_le2", "min_le2_imp",
       "min_le_between",
       "min_reduce",
       "min_refl",
       "mul_assoc",
       "mul_comm",
       "mul_div_refl",
       "mul_infty", "mul_infty'",
       "mul_lcancel",
       "mul_le", "mul_le2",
       "mul_let",
       "mul_linv", "mul_linv_pos",
       "mul_lneg",
       "mul_lt", "mul_lt2",
       "mul_lte",
       "mul_lone",
       "mul_lposinf",
       "mul_lzero",
       "mul_not_infty", "mul_not_infty2",
       "mul_rcancel",
       "mul_rneg",
       "mul_rone",
       "mul_rposinf",
       "mul_rzero",
       "ne_01", "ne_02",
       "neg_0",
       "neg_add",
       "neg_eq0",
       "neg_minus1",
       "neg_mul2",
       "neg_sub",
       "neg_neg",
       "neg_not_posinf",
       "normal_0", "normal_1",
       "normal_inv_eq",
       "normal_real_set",
       "num_lt_infty",
       "num_not_infty",
       "one_pow",
       "pos_not_neginf",
       "pow_0", "pow_1", "pow_2",
       "pow_2_abs",
       "pow_add",
       "pow_div",
       "pow_eq",
       "pow_inv",
       "pow_le", "pow_le_full",
       "pow_le_mono",
       "pow_lt", "pow_lt2",
       "pow_minus1",
       "pow_mul",
       "pow_neg_odd",
       "pow_not_infty",
       "pow_pos_even",
       "pow_pos_le",
       "pow_pos_lt",
       "pow_pow",
       "pow_zero", "pow_zero_imp",
       "pow2_le_eq",
       "pow2_sqrt",
       "quotient_normal",
       "real_0",
       "real_def",
       "real_normal",
       "rdiv_eq",
       "real_set_def", "real_set_empty",
       "rinv_uniq",
       "sqrt_0", "sqrt_1",
       "sqrt_le_n",
       "sqrt_le_x",
       "sqrt_mono_le",
       "sqrt_mul",
       "sqrt_pos_le",
       "sqrt_pos_lt",
       "sqrt_pos_ne",
       "sqrt_pow2",
       "sub_0",
       "sub_add", "sub_add_normal", "sub_add2",
       "sub_eq_0",
       "sub_infty",
       "sub_ldistrib",
       "sub_lzero",
       "sub_le_eq", "sub_le_eq2",
       "sub_le_imp", "sub_le_imp2",
       "sub_le_switch", "sub_le_switch2",
       "sub_le_zero",
       "sub_lneg",
       "sub_lt_eq",
       "sub_lt_imp", "sub_lt_imp2",
       "sub_lt_zero", "sub_lt_zero2",
       "sub_not_infty",
       "sub_pow2",
       "sub_rdistrib",
       "sub_refl",
       "sub_rneg",
       "sub_rzero",
       "sub_zero_le",
       "sub_zero_lt", "sub_zero_lt2",
       "thirds_between",
       "third_cancel",
       "normal_real",
       "x_half_half",
       "zero_div",
       "zero_pow"];

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (2nd Edition).
      Cambridge University Press (2017).
  [2] Fichtenholz, G.M.: Differential- und Integralrechnung (Differential and
      Integral Calculus), Vol.2. (1967).
  [3] Harrison, J.: Constructing the real numbers in HOL. TPHOLs. (1992).
  [4] Wikipedia: https://en.wikipedia.org/wiki/Limit_superior_and_limit_inferior
 *)
