open HolKernel Parse boolLib IndDefLib DefnBase

open arithmeticTheory BasicProvers simpLib

fun simp ths = ASM_SIMP_TAC (srw_ss()) ths
fun SRULE ths = SIMP_RULE (srw_ss()) ths

val _ = new_theory "cv";

val N0_def = new_definition("N0_def",
  “N0 (m:num) n = if n = 0 then m+1 else 0”);

val P0_def = new_definition("P0_def",
  “P0 (c:num -> num) d n =
   if n = 0 then 0
   else if ODD n then c (n DIV 2)
   else d ((n-2) DIV 2)”);

Theorem N0_11[local,simp]:
  N0 m = N0 n <=> m = n
Proof
  simp[FUN_EQ_THM, N0_def, EQ_IMP_THM] >>
  disch_then $ Q.SPEC_THEN ‘0’ mp_tac >> simp[EQ_MONO_ADD_EQ]
QED

Theorem simple_inequalities[local,simp]:
  1 <> 0 /\ 2 <> 0
Proof
  simp[ONE, TWO]
QED

Theorem ODD12[local,simp]:
  ODD 1 /\ ~ODD 2
Proof
  simp[ONE, TWO, ODD]
QED

Theorem ONE_DIV2[local,simp]:
  1 DIV 2 = 0
Proof
  simp[ONE, TWO, prim_recTheory.LESS_MONO_EQ, prim_recTheory.LESS_0,
       LESS_DIV_EQ_ZERO]
QED

Theorem P0_11[local,simp]:
  P0 c d = P0 e f <=> c = e /\ d = f
Proof
  simp[FUN_EQ_THM, P0_def, EQ_IMP_THM] >> rpt strip_tac
  >- (Q.RENAME_TAC [‘c x = e x’] >>
      pop_assum $ Q.SPEC_THEN ‘2 * x + 1’ mp_tac >>
      simp[ADD_EQ_0, ADD_CLAUSES, ODD_ADD, ODD_MULT]) >>
  Q.RENAME_TAC [‘d x = f x’] >>
  pop_assum $ Q.SPEC_THEN ‘2 * x + 2’ mp_tac >>
  simp[ADD_EQ_0, ADD_CLAUSES, ODD_ADD, ODD_MULT, MULT_EQ_0, ADD_SUB]
QED

Inductive iscv:
[~num:] (!m. iscv (N0 m)) /\
[~pair:] (!c d. iscv c /\ iscv d ==> iscv (P0 c d))
End

val cv_tydefrec = newtypeTools.rich_new_type("cv",
  prove(“?cv. iscv cv”,
        Q.EXISTS_TAC ‘N0 0’ >> REWRITE_TAC[iscv_num]))

val Pair_def = new_definition("Pair_def",
  “Pair c d = cv_ABS (P0 (cv_REP c) (cv_REP d))”);

Theorem Pair_11:
  Pair c d = Pair e f <=> c = e /\ d = f
Proof
  simp[Pair_def, EQ_IMP_THM] >> strip_tac >>
  drule_at (Pat ‘cv_ABS _ = cv_ABS _’)
           (iffLR $ #term_ABS_pseudo11 cv_tydefrec) >>
  simp[#termP_term_REP cv_tydefrec, iscv_pair, #term_REP_11 cv_tydefrec]
QED

val Num_def = new_definition("Num_def", “Num n = cv_ABS (N0 n)”);

Theorem Num_11:
  Num m = Num n <=> m = n
Proof
  simp[Num_def, EQ_IMP_THM] >> strip_tac >>
  drule_at (Pat ‘cv_ABS _ = cv_ABS _’)
           (iffLR $ #term_ABS_pseudo11 cv_tydefrec) >>
  simp[iscv_num]
QED

Theorem cv_distinct:
  Num n <> Pair c d
Proof
  simp[Num_def, Pair_def] >> strip_tac >>
  drule_at (Pat ‘cv_ABS _ = cv_ABS _’)
           (iffLR $ #term_ABS_pseudo11 cv_tydefrec) >>
  simp[iscv_num, iscv_pair, #termP_term_REP cv_tydefrec] >>
  simp[N0_def, P0_def, FUN_EQ_THM] >> Q.EXISTS_TAC ‘0’ >>
  simp[ADD_EQ_0]
QED

Theorem cv_induction =
        iscv_strongind |> Q.SPEC ‘λc0. P (cv_ABS c0)’
                       |> BETA_RULE
                       |> SRULE [GSYM Num_def]
                       |> SRULE [#termP_exists cv_tydefrec, PULL_EXISTS,
                                 GSYM Pair_def, #absrep_id cv_tydefrec]
                       |> Q.GEN ‘P’

Inductive cvrel:
[~num:]
  (!n. cvrel f g (Num n) (f n)) /\
[~pair:]
  (!c d rc rd. cvrel f g c rc /\ cvrel f g d rd ==>
               cvrel f g (Pair c d) (g c d rc rd))
End

Theorem cvrel_exists:
  !f g c. ?r. cvrel f g c r
Proof
  ntac 2 gen_tac >> ho_match_mp_tac cv_induction >> rpt strip_tac
  >- irule_at Any cvrel_num >>
  irule_at Any cvrel_pair >> rpt (first_assum $ irule_at Any)
QED

Theorem cvrel_unique:
  !c r1. cvrel f g c r1 ==>
         !r2. cvrel f g c r2 ==> r1 = r2
Proof
  ho_match_mp_tac cvrel_strongind >> rpt strip_tac
  >- (pop_assum mp_tac >> simp[Once cvrel_cases] >>
      simp[Num_11,cv_distinct]) >>
  Q.PAT_X_ASSUM ‘cvrel _ _ (Pair _ _) _’ mp_tac>>
  simp[Once cvrel_cases] >> simp[cv_distinct, Pair_11]>>
  metisLib.METIS_TAC[]
QED

val cvrelf_def = new_definition("cvrelf_def",
                                “cvrelf f g c = @r. cvrel f g c r”);

Theorem cvrelf_Pair:
  cvrelf f g (Pair c d) = g c d (cvrelf f g c) (cvrelf f g d)
Proof
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [cvrelf_def])) >>
  SELECT_ELIM_TAC>> conj_tac
  >- (irule_at Any cvrel_exists) >>
  simp[Once cvrel_cases, cv_distinct, Pair_11, PULL_EXISTS] >>
  rpt strip_tac >>
  Q.SUBGOAL_THEN ‘cvrelf f g c = rc /\ cvrelf f g d = rd’ strip_assume_tac
  >- (simp[cvrelf_def] >> conj_tac >> SELECT_ELIM_TAC >>
      metisLib.METIS_TAC[cvrel_unique]) >>
  simp[]
QED

Theorem cv_Axiom:
  !f g. ?h. (!n. h (Num n) = f n) /\
            (!c d. h (Pair c d) = g c d (h c) (h d))
Proof
  rpt gen_tac >> Q.EXISTS_TAC ‘cvrelf f g’ >> simp[cvrelf_Pair] >>
  simp[cvrelf_def, Once cvrel_cases, Num_11, cv_distinct]
QED

(* helpers/auxiliaries *)
val c2b_def = new_definition ("c2b_def", “c2b x = ?k. x = Num (SUC k)”);
val cv_if_def0 = new_definition(
  "cv_if_def0",
  “cv_if p (q:cv) (r:cv) = if c2b p then q else r”);
Theorem cv_if_def:
  cv_if (Num (SUC m)) (p:cv) (q:cv) = p /\
  cv_if (Num 0) p q = q /\
  cv_if (Pair r s) p q = q
Proof
  simp[c2b_def, cv_if_def0, Num_11, cv_distinct]
QED

Theorem c2b_thm[simp]:
  (c2b (Num (SUC n)) = T) /\
  (c2b (Num 1) = T) /\
  (c2b (Num 0) = F) /\
  (c2b (Num (NUMERAL ZERO)) = F) /\
  (c2b (Pair x y) = F)
Proof
  rewrite_tac [c2b_def,Num_11,prim_recTheory.INV_SUC_EQ]
  \\ rewrite_tac [GSYM boolTheory.EXISTS_REFL,NORM_0]
  \\ rewrite_tac [SUC_NOT]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [cv_distinct]
  \\ EXISTS_TAC “0:num”
  \\ rewrite_tac [ADD1,ADD_CLAUSES]
QED

val cv_case_def = Prim_rec.new_recursive_definition {
  name = "cv_case_def",
  rec_axiom = cv_Axiom,
  def = “cv_CASE (Num n) nmf prf = nmf n /\
         cv_CASE (Pair c d) nmf prf = prf c d”};

Overload case = “cv_CASE”

val cv_size_def = Prim_rec.new_recursive_definition {
  name = "cv_size_def",
  rec_axiom = cv_Axiom,
  def = “cv_size (Num n) = 1 + n /\
         cv_size (Pair c d) = 1 + (cv_size c + cv_size d)”};

val _ = TypeBase.export (
    TypeBasePure.gen_datatype_info{
      ax = cv_Axiom, ind = cv_induction, case_defs = [cv_case_def]
    } |> map (TypeBasePure.put_size (“cv_size”, TypeBasePure.ORIG cv_size_def))
)

fun recdef (n,t) =
  Prim_rec.new_recursive_definition{name = n, def = t, rec_axiom = cv_Axiom}

val cv_fst_def = recdef("cv_fst_def",
                       “cv_fst (Pair p q) = p /\ cv_fst (Num m) = Num 0”);
val cv_snd_def = recdef("cv_snd_def",
                       “cv_snd (Pair p q) = q /\ cv_snd (Num m) = Num 0”);
val cv_ispair_def = recdef("cv_ispair_def",
                           “cv_ispair (Pair p q) = Num (SUC 0) /\
                            cv_ispair (Num m) = Num 0”);
val _ = export_rewrites ["cv_fst_def", "cv_snd_def", "cv_ispair_def"];

val b2c_def = Prim_rec.new_recursive_definition{
  def = “b2c T = Num (SUC 0) /\ b2c F = Num 0”,
  rec_axiom = TypeBase.axiom_of “:bool”,
  name = "b2c_def"};
val _ = BasicProvers.export_rewrites ["b2c_def"]

Theorem b2c[simp]:
  ((b2c x = Num 1) = x) /\
  (b2c x = Num (SUC 0)) = x
Proof
  ASM_CASES_TAC “x:bool” \\ simp[ONE]
QED


Theorem b2c_if:
  b2c g = if g then Num (SUC 0) else Num 0
Proof
  Cases_on ‘g’ >> simp[b2c_def]
QED

val cv_lt_def0 = recdef(
  "cv_lt_def0",
  “cv_lt (Num m) c = (case c of | Num n => b2c (m < n) | _ => Num 0) /\
   cv_lt (Pair c d) e = Num 0”);

Theorem cv_lt_def[simp]:
  cv_lt (Num m) (Num n) = Num (if m < n then SUC 0 else 0) /\
  cv_lt (Num m) (Pair p q) = Num 0 /\
  cv_lt (Pair p q) (Num n) = Num 0 /\
  cv_lt (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_lt_def0, b2c_if, SF boolSimps.COND_elim_ss]
QED

Inductive isnseq:
[~nil:] isnseq (Num 0) /\
[~cons:] (!n c. isnseq c ==> isnseq (Pair n c))
End

val cvnumval_def = recdef(
  "cvnumval_def",
  “cvnumval (Num n) = n /\ cvnumval (Pair c d) = 0”
);

val cvnum_map2_def = new_definition(
  "cvnum_map2_def",
  “cvnum_map2 f c d = Num (f (cvnumval c) (cvnumval d))”);

val cv_add_def0 = new_definition ("cv_add_def0", “cv_add = cvnum_map2 $+”);
Theorem cv_add_def[simp]:
  cv_add (Num m) (Num n) = Num (m + n) /\
  cv_add (Num m) (Pair p q) = Num m /\
  cv_add (Pair p q) (Num n) = Num n /\
  cv_add (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_add_def0, FUN_EQ_THM,cvnumval_def, cvnum_map2_def, ADD_CLAUSES]
QED

val cv_sub_def0 = new_definition("cv_sub_def0", “cv_sub = cvnum_map2 $-”);
Theorem cv_sub_def[simp]:
  cv_sub (Num m) (Num n) = Num (m - n) /\
  cv_sub (Num m) (Pair p q) = Num m /\
  cv_sub (Pair p q) (Num n) = Num 0 /\
  cv_sub (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_sub_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def, SUB_0]
QED

val cv_mul_def0 = new_definition("cv_mul_def0", “cv_mul = cvnum_map2 $*”);
Theorem cv_mul_def[simp]:
  cv_mul (Num m) (Num n) = Num (m * n) /\
  cv_mul (Num m) (Pair p q) = Num 0 /\
  cv_mul (Pair p q) (Num n) = Num 0 /\
  cv_mul (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_mul_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def]
QED

val cv_div_def0 = new_definition("cv_div_def0", “cv_div = cvnum_map2 $DIV”);
Theorem cv_div_def[simp]:
  cv_div (Num m) (Num n) = Num (m DIV n) /\
  cv_div (Num m) (Pair p q) = Num 0 /\
  cv_div (Pair p q) (Num n) = Num 0 /\
  cv_div (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_div_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def]
QED

val cv_mod_def0 = new_definition("cv_mod_def0", “cv_mod = cvnum_map2 $MOD”);
Theorem cv_mod_def[simp]:
  cv_mod (Num m) (Num n) = Num (m MOD n) /\
  cv_mod (Num m) (Pair p q) = Num m /\
  cv_mod (Pair p q) (Num n) = Num 0 /\
  cv_mod (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_mod_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def]
QED

val cv_eq_def0 = new_definition("cv_eq_def0", “cv_eq (c:cv) d = b2c (c = d)”);
Theorem cv_eq_def:
  cv_eq p q = Num (if p = q then SUC 0 else 0)
Proof
  simp[cv_eq_def0, b2c_if, SF boolSimps.COND_elim_ss]
QED
Theorem cv_eq[simp]:
  (cv_eq (Pair x y) (Pair x' y') = b2c (x = x' /\ y = y')) /\
  (cv_eq (Num m) (Num n) = b2c (m = n)) /\
  (cv_eq (Pair x y) (Num n) = b2c F) /\
  (cv_eq (Num n) (Pair x y) = b2c F)
Proof
  simp [cv_eq_def0]
QED


val cv_size_alt_def = recdef("cv_size_alt_def",
  “(cv_size_alt (Num n) = n) /\
   (cv_size_alt (Pair p q) = 1 + cv_size_alt p + cv_size_alt q)”);

(* -------------------------------------------------------------------------
 * Extra characteristic theorems
 * ------------------------------------------------------------------------- *)

Theorem lemma[local]:
  n:num <= m ==> (m - n = k <=> m = n + k)
Proof
  simp[SUB_RIGHT_EQ, LESS_EQ_0, EQ_IMP_THM, DISJ_IMP_THM, ADD_CLAUSES] >>
  metisLib.METIS_TAC[LESS_EQUAL_ANTISYM]
QED

Theorem DIV_RECURSIVE:
  m DIV n =
    if n = 0 then 0 else
    if m < n then 0 else
      SUC ((m - n) DIV n)
Proof
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[LESS_DIV_EQ_ZERO] >>
  irule DIV_UNIQUE >>
  Q.SUBGOAL_THEN ‘0 < n’ ASSUME_TAC >- ASM_REWRITE_TAC[GSYM NOT_ZERO_LT_ZERO] >>
  drule_then (Q.SPEC_THEN ‘m - n’ strip_assume_tac) DIVISION >>
  simp [ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_LEFT_1] >>
  Q.EXISTS_TAC ‘(m - n) MOD n’ >> simp[] >>
  RULE_ASSUM_TAC (SRULE [NOT_LESS]) >> Q.PAT_X_ASSUM ‘m - n = _’ mp_tac >>
  simp[lemma] >> disch_then (CONV_TAC o LAND_CONV o K) >>
  simp[AC ADD_COMM ADD_ASSOC]
QED

Theorem MOD_RECURSIVE:
  m MOD n = if n = 0 then m else if m < n then m else (m - n) MOD n
Proof
  IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[LESS_MOD] >>
  RULE_ASSUM_TAC (SRULE[NOT_LESS, NOT_ZERO_LT_ZERO]) >>
  simp[SUB_MOD]
QED

Theorem CV_EQ:
  ((Pair p q = Pair r s) = (if p = r then q = s else F)) /\
  ((Pair p q = Num n) = F) /\
  ((Num m = Num n) = (m = n))
Proof
  simp []
QED

Theorem LT_RECURSIVE:
  ((m < 0) = F) /\
  ((m < SUC n) = (if m = n then T else m < n))
Proof
  simp[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0]
QED

Theorem SUC_EQ:
  ((SUC m = 0) = F) /\
  ((SUC m = SUC n) = (m = n))
Proof
  simp[]
QED

Theorem cv_if_cong[defncong]:
  (c2b P = c2b Q) /\
  (c2b Q ==> x = x') /\
  (~c2b Q ==> y = y') ==>
    cv_if P x y = cv_if Q x' y'
Proof
  Cases_on ‘P’ >> Cases_on ‘Q’ >> simp[c2b_def, cv_if_def] >>
  rpt (Q.RENAME_TAC [‘cv_if (Num m) _ _’] >> Cases_on ‘m’ >>
       simp[c2b_def, cv_if_def])
QED

Theorem cv_if[simp]:
  cv_if x y z = if c2b x then y else z
Proof
  simp[cv_if_def0]
QED

Theorem cv_extras[simp]:
  (cv_lt v (Pair x y) = Num 0) /\
  (cv_lt (Pair x y) v = Num 0) /\
  (cv_add (Pair x y) v = case v of Pair a b => Num 0 | _ => v) /\
  (cv_add v (Pair x y) = case v of Pair a b => Num 0 | _ => v) /\
  (cv_sub (Pair x y) v = Num 0) /\
  (cv_sub v (Pair x y) = case v of Pair a b => Num 0 | _ => v) /\
  (cv_mul (Pair x y) v = Num 0) /\
  (cv_mul v (Pair x y) = Num 0) /\
  (cv_div (Pair x y) v = Num 0) /\
  (cv_div v (Pair x y) = case v of Pair a b => Num 0 | _ => Num 0) /\
  (cv_mod (Pair x y) v = Num 0) /\
  (cv_mod v (Pair x y) = case v of Pair a b => Num 0 | _ => v)
Proof
  Cases_on `v` \\ simp [cv_lt_def, cv_add_def, cv_sub_def, cv_mul_def,
                        cv_div_def, cv_mod_def]
QED

(* -------------------------------------------------------------------------
 * Theorems used in automation
 * ------------------------------------------------------------------------- *)

Triviality c2b_if:
  c2b (Num (if b then SUC 0 else 0)) = b
Proof
  Cases_on ‘b’
  \\ rewrite_tac [c2b_def,Num_11,SUC_EQ]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [SUC_EQ,EXISTS_REFL]
QED

Theorem neq_to_cv:
  !m n. m = n <=> c2b (cv_eq (Num m) (Num n))
Proof
  rewrite_tac [cv_eq_def,c2b_if,Num_11]
QED

Theorem lt_to_cv:
  m < n <=> c2b (cv_lt (Num m) (Num n))
Proof
  rewrite_tac [cv_lt_def,c2b_if,Num_11]
QED

Theorem gt_to_cv:
  m > n <=> c2b (cv_lt (Num n) (Num m))
Proof
  rewrite_tac [cv_lt_def,c2b_if,Num_11,GREATER_DEF]
QED

Theorem le_to_cv:
  m <= n <=> ~c2b (cv_lt (Num n) (Num m))
Proof
  rewrite_tac [GSYM NOT_LESS,lt_to_cv]
QED

Theorem ge_to_cv:
  n >= m <=> ~c2b (cv_lt (Num n) (Num m))
Proof
  rewrite_tac [le_to_cv,GREATER_EQ]
QED

Theorem ODD_to_cv:
  ODD n <=> c2b (cv_mod (Num n) (Num 2))
Proof
  rewrite_tac [ODD_EVEN,cv_mod_def]
  \\ rewrite_tac [c2b_def,Num_11,EVEN_MOD2]
  \\ Cases_on ‘n MOD 2’
  \\ rewrite_tac [numTheory.NOT_SUC]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [numTheory.NOT_SUC,SUC_EQ,EXISTS_REFL]
QED

Theorem EVEN_to_cv:
  EVEN n <=> ~c2b (cv_mod (Num n) (Num 2))
Proof
  rewrite_tac [EVEN_ODD,ODD_to_cv]
QED

Theorem c2n_def[simp,allow_rebind] = Prim_rec.new_recursive_definition {
  name = "c2n_def",
  rec_axiom = cv_Axiom,
  def = “c2n (Num n) = n /\
         c2n (Pair c d) = 0”
};

Theorem add_to_cv:
  m + n = c2n (cv_add (Num m) (Num n))
Proof
  rewrite_tac [c2n_def,cv_add_def]
QED

Theorem suc_to_cv:
  SUC m = c2n (cv_add (Num m) (Num 1))
Proof
  rewrite_tac [c2n_def,cv_add_def,ADD1]
QED

Theorem sub_to_cv:
  m - n = c2n (cv_sub (Num m) (Num n))
Proof
  rewrite_tac [c2n_def,cv_sub_def]
QED

Theorem pre_to_cv:
  PRE m = c2n (cv_sub (Num m) (Num 1))
Proof
  rewrite_tac [c2n_def,cv_sub_def,PRE_SUB1]
QED

Theorem mul_to_cv:
  m * n = c2n (cv_mul (Num m) (Num n))
Proof
  rewrite_tac [c2n_def,cv_mul_def]
QED

Theorem div_to_cv:
  m DIV n = c2n (cv_div (Num m) (Num n))
Proof
  rewrite_tac [c2n_def,cv_div_def]
QED

Theorem mod_to_cv:
  m MOD n = c2n (cv_mod (Num m) (Num n))
Proof
  rewrite_tac [c2n_def,cv_mod_def]
QED

val cv_exp_def = new_definition("cv_exp_def",
  “cv_exp m n = Num (c2n m ** c2n n)”);

Theorem cv_exp_eq:
  cv_exp b e =
    cv_if e                                        (* e is a positive number *)
          (cv_if (cv_mod e (Num 2))                (* e is odd               *)
                 (cv_mul b (cv_exp b (cv_sub e (Num 1))))
                 (let x = cv_exp b (cv_div e (Num 2))
                  in cv_mul x x))
          (Num 1)
Proof
  Cases_on ‘e’
  \\ rewrite_tac [c2n_def,cv_exp_def,cv_if_def,EXP]
  \\ Cases_on ‘m’
  \\ rewrite_tac [c2n_def,cv_exp_def,cv_if_def,EXP,LET_THM]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rewrite_tac [cv_mul_def,cv_mod_def,cv_if_def]
  \\ Cases_on ‘SUC n MOD 2’
  \\ rewrite_tac [cv_if_def,Num_11,GSYM EXP_ADD, GSYM TIMES2,cv_div_def,cv_sub_def,
       GSYM PRE_SUB1,prim_recTheory.PRE,c2n_def]
  \\ rewrite_tac [GSYM EXP]
  >-
   (AP_TERM_TAC
    \\ ‘0 < 2’ by rewrite_tac [numeralTheory.numeral_distrib,numeralTheory.numeral_lt]
    \\ imp_res_tac DIVISION
    \\ pop_assum (K ALL_TAC)
    \\ first_x_assum $ Q.SPEC_THEN ‘SUC n’ mp_tac
    \\ asm_rewrite_tac [ADD_CLAUSES]
    \\ strip_tac
    \\ once_rewrite_tac [MULT_COMM]
    \\ pop_assum $ assume_tac o GSYM \\ asm_rewrite_tac [])
  \\ Cases_on ‘b’
  \\ rewrite_tac [cv_mul_def,c2n_def,EXP,MULT_CLAUSES]
QED

Theorem exp_to_cv:
  m ** n = c2n (cv_exp (Num m) (Num n))
Proof
  rewrite_tac [c2n_def,cv_exp_def]
QED

val _ = app Parse.permahide [“c2n”,“c2b”,“Num”,“Pair”];

val _ = app delete_const ["P0", "N0", "iscv", "cvrel", "cvrelf",
                          "cv_ABS", "cv_REP", "cvnum_map2", "cvnumval"];

val _ = export_theory();
