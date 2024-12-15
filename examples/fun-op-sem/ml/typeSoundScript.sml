open HolKernel boolLib bossLib Parse BasicProvers
     integerTheory stringTheory alistTheory listTheory pred_setTheory
     pairTheory optionTheory finite_mapTheory arithmeticTheory

fun term_rewrite tms = let
  fun f tm = ASSUME (list_mk_forall(free_vars tm,tm))
  in rand o concl o QCONV (REWRITE_CONV (map f tms)) end

(*
In this file, we demonstrate that the Functional Big-Step semantics
style is suitable for proofs of type soundness.  In particular, we
define an ML-like language, heavily inspired by Core ML in Wright and
Felleisen's "A Syntactic Approach to Type Soundness" (1992) (hereafter
W&F), using functional big-step semantics rather than small-step
semantics. We then prove the type soundness using the induction
theorem generated from the definition of the functional big-step
semantics.
*)

(* TODO: from CakeML's miscLib.sml *)
val SWAP_IMP = PROVE[]``(P ==> Q ==> R) ==> (Q ==> P ==> R)``
val IMP_IMP = METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``
val discharge_hyps = match_mp_tac IMP_IMP >> conj_tac
fun match_exists_tac tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val vs = map (fst o dest_var o variant (free_vars tm)) vs
    fun k (g as (_,w)) =
      let
        val (_,b) = strip_exists w
        val cs = strip_conj b val c = hd cs
        val (tms,_) = match_term c tm
        val xs = map #redex tms
        val ys = map #residue tms
        fun sorter ls = xs@(List.filter(not o Lib.C tmem xs)ls)
      in
        CONV_TAC(RESORT_EXISTS_CONV sorter) >>
        map_every exists_tac ys
      end g
  in
    CONV_TAC(RENAME_VARS_CONV vs) >> k
  end g
(* -- *)

val _ = new_theory"typeSound"

(* TODO: move to HOL standard lib *)
val LUPDATE_ID = store_thm("LUPDATE_ID",
  ``∀n ls. n < LENGTH ls ⇒ (LUPDATE (EL n ls) n ls = ls)``,
  rw[LIST_EQ_REWRITE,EL_LUPDATE] >> rw[])

val FLOOKUP_f_o_f = store_thm("FLOOKUP_f_o_f",
  ``FLOOKUP (f1 f_o_f f2) k =
    case FLOOKUP f2 k of
    | NONE => NONE
    | SOME v => FLOOKUP f1 v``,
  simp[FLOOKUP_DEF] >>
  simp[f_o_f_DEF] >> rw[] >> fs[])
(* -- *)

(* Syntax *)

val _ = Datatype`lit =
  Int int | Unit`

val _ = Datatype`exp =
  | Lit lit
  | Var string
  | App exp exp
  | Let string exp exp
  | Fun string exp
  | Funrec string string exp
  | Ref exp
  | Deref exp
  | Assign exp exp
  | Letexn string exp
  | Raise exp exp
  | Handle exp exp exp`

(* Differences from W&F:
   - we have specific constants (ints and unit)
   - we bind one exception at a time
   - we use Funrec rather than Y
   - we use explicit syntactic forms for applications of primitives like Ref,
     Raise, whereas they treat them as curried function values and re-use App to
     apply them; in our syntax we can of course achieve the same in e by:
       Let "ref" (Fun "x" (Ref (Var "x"))) e. *)

(*
The major difference is our separate class of values, which are not in mutual
recursion with expressions, and include closures. Using closures/environments
is a stylistic choice that works well with functional big-step and lets us
avoid defining capture-avoiding substitution over terms (which W&F gloss over
anyway).
*)

(* Values *)

val _ = Datatype`v =
  | Litv lit
  | Clos ((string,v) alist) string exp
  | Closrec ((string,v) alist) string string exp
  | Loc num
  | Exn num`

val v_induction = theorem"v_induction"
val v_ind =
  v_induction
  |> Q.SPECL[`P`,`EVERY (P o SND)`,`P o SND`]
  |> SIMP_RULE (srw_ss()) []
  |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
  |> GEN_ALL
  |> curry save_thm "v_ind"
val v_size_def = definition"v_size_def"

val _ = type_abbrev("env",``:(string,v) alist``)

(* Semantics *)

(*
The semantics has a state containing the clock, the store, and the number of
exceptions that have been created.  Whereas W&F's treatment of exceptions is
intimately tied up with the mechanics of their small-step semantics, we simply
generate a new exception value for every (dynamic) Letexn expression.
*)

val _ = Datatype`
  state = <| clock : num; refs : v list; next_exn : num |>`

val state_component_equality = theorem"state_component_equality"

(* machinery for the functional big-step definition *)

val check_clock_def = Define `
  check_clock s' s =
    s' with clock := (if s'.clock ≤ s.clock then s'.clock else s.clock)`;

val check_clock_id = prove(
  ``!s s'. s.clock ≤ s'.clock ⇒ check_clock s s' = s``,
 rw [check_clock_def, state_component_equality]);

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`;

val dec_clock_refs = store_thm("dec_clock_refs[simp]",
  ``(dec_clock s).refs = s.refs``,
  rw[dec_clock_def])

val dec_clock_next_exn = store_thm("dec_clock_next_exn[simp]",
  ``(dec_clock s).next_exn = s.next_exn``,
  rw[dec_clock_def])

val is_closure_def = Define`
  is_closure (Clos _ _ _) = T ∧
  is_closure (Closrec _ _ _ _) = T ∧
  is_closure _ = F`
val _ = export_rewrites["is_closure_def"]

(* results *)

val _ = Datatype`
  r = Rval v
    | Rraise num v
    | Rfail
    | Rtimeout`

(* big-step semantics as a function *)

Definition sem_def:
  (sem env s (Lit i) = (Rval (Litv i), s)) ∧
  (sem env s (Var x) =
    case ALOOKUP env x of
    | NONE => (Rfail, s)
    | SOME v => (Rval v, s)) ∧
  (sem env s (App e1 e2) =
   case sem env s e1 of
   | (Rval v1, s1) =>
       (case sem env (check_clock s1 s) e2 of
        | (Rval v2, s2) =>
            if s.clock ≠ 0 ∧ s2.clock ≠ 0 then
              (case v1 of
               | Clos env' x e =>
                 sem ((x,v2)::env') (dec_clock (check_clock s2 s)) e
               | Closrec env' f x e =>
                 sem ((x,v2)::(f,v1)::env') (dec_clock (check_clock s2 s)) e
               | _ => (Rfail, s2))
            else (Rtimeout, s2)
        | res => res)
   | res => res) ∧
  (sem env s (Let x e1 e2) =
   case sem env s e1 of
   | (Rval v1, s1) => sem ((x,v1)::env) (check_clock s1 s) e2
   | res => res) ∧
  (sem env s (Fun x e) = (Rval (Clos env x e), s)) ∧
  (sem env s (Funrec f x e) = (Rval (Closrec env f x e), s)) ∧
  (sem env s (Ref e) =
   case sem env s e of
   | (Rval v, s) => (Rval (Loc (LENGTH s.refs)), s with refs := s.refs ++ [v])
   | res => res) ∧
  (sem env s (Deref e) =
   case sem env s e of
   | (Rval (Loc n), s) => (if n < LENGTH s.refs then Rval (EL n s.refs) else Rfail, s)
   | (Rval _, s) => (Rfail, s)
   | res => res) ∧
  (sem env s (Assign e1 e2) =
   case sem env s e1 of
   | (Rval v1, s1) =>
     (case sem env (check_clock s1 s) e2 of
      | (Rval v2, s2) =>
          (case v1 of
           | Loc n =>
             if n < LENGTH s2.refs then
             (Rval (Litv Unit), s2 with refs := LUPDATE v2 n s2.refs)
             else (Rfail, s2)
           | _ => (Rfail, s2))
      | res => res)
   | res => res) ∧
  (sem env s (Letexn x e) =
   sem ((x,Exn (s.next_exn))::env) (s with next_exn := s.next_exn + 1) e) ∧
  (sem env s (Raise e1 e2) =
   case sem env s e1 of
   | (Rval v1, s1) =>
     (case sem env (check_clock s1 s) e2 of
      | (Rval v2, s2) =>
          (case v1 of
           | Exn n => (Rraise n v2, s2)
           | _ => (Rfail, s2))
      | res => res)
   | res => res) ∧
   (sem env s (Handle e3 e1 e2) =
    case sem env s e1 of
    | (Rval v1, s1) =>
      (case v1 of
       | Exn n =>
         (case sem env (check_clock s1 s) e2 of
          | (Rval v2, s2) =>
            if is_closure v2 then
              (case sem env (check_clock s2 s) e3 of
               | (Rraise n3 v3, s3) =>
                 if n3 = n then
                   if s.clock ≠ 0 ∧ s3.clock ≠ 0 then
                     (case v2 of
                      | Clos env' x e =>
                        sem ((x,v3)::env') (dec_clock (check_clock s3 s)) e
                      | Closrec env' f x e =>
                        sem ((x,v3)::(f,v2)::env') (dec_clock (check_clock s3 s)) e)
                   else (Rtimeout, s3)
                 else (Rraise n3 v3, s3)
               | res => res)
            else (Rfail, s2)
          | res => res)
       | _ => (Rfail, s1))
    | res => res)
Termination
 WF_REL_TAC`inv_image (measure I LEX measure exp_size)
                      (λ(env,s,e). (s.clock,e))` >>
 rpt strip_tac >> TRY DECIDE_TAC >>
 fs[check_clock_def,dec_clock_def] >>
 rw[] >> fsrw_tac[ARITH_ss][]
End

(*
clean-up of the definition and induction theorem, removing the check_clock
machinery that was used to get the function through the termination checker
*)

val sem_ind = theorem"sem_ind"

val sem_clock = store_thm("sem_clock",
  ``∀env s e r s'. sem env s e = (r, s') ⇒ s'.clock ≤ s.clock``,
  ho_match_mp_tac sem_ind >>
  rpt conj_tac >>
  simp[sem_def] >>
  rpt gen_tac >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[check_clock_def,dec_clock_def] >>
  rpt(IF_CASES_TAC >> simp[]) >>
  rpt strip_tac >> res_tac >> simp[] >> fs[])

val r = term_rewrite [``check_clock s1 s = s1``,
    ``s.clock <> 0 /\ s1.clock <> 0 <=> s1.clock <> 0``]

Theorem sem_def[allow_rebind]:
  ^(sem_def |> concl |> r)
Proof
  rpt strip_tac >>
  rw[Once sem_def] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac sem_clock >>
  simp[check_clock_id] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac sem_clock >>
  simp[check_clock_id] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  imp_res_tac sem_clock >>
  simp[check_clock_id] >>
  `F` suffices_by rw[] >>
  DECIDE_TAC
QED

Theorem sem_ind[allow_rebind]:
  ^(sem_ind |> concl |> r)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac sem_ind >>
  rw[] >>
  first_x_assum match_mp_tac >>
  rw[] >> fs[] >>
  res_tac >>
  imp_res_tac sem_clock >>
  fsrw_tac[ARITH_ss][check_clock_id] >> rfs[] >>
  fsrw_tac[ARITH_ss][check_clock_id]
QED

(* alternative un-clocked relational big-step semantics for comparison *)

val dest_closure_def = Define`
  (dest_closure v (Clos env x e) = SOME (((x,v)::env),e)) ∧
  (dest_closure v (Closrec env f x e) = SOME (((x,v)::(f,Closrec env f x e)::env),e)) ∧
  (dest_closure _ _ = NONE)`;
val _ = export_rewrites["dest_closure_def"];

val (eval_rules,eval_ind,eval_cases) = Hol_reln`
  (eval env s (Lit i) (Rval (Litv i), s)) ∧
  (ALOOKUP env x = NONE ⇒
   eval env s (Var x) (Rfail, s)) ∧
  (ALOOKUP env x = (SOME v) ⇒
   eval env s (Var x) (Rval v, s)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   dest_closure v2 v1 = SOME (env',e) ∧
   eval env' (dec_clock s2) e res
   ⇒
   eval env s (App e1 e2) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   dest_closure v2 v1 = NONE
   ⇒
   eval env s (App e1 e2) (Rfail,s2)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (App e1 e2) res) ∧
  (eval env s e1 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (App e1 e2) res) ∧
  (eval env s e1 (Rval v1,s1) ∧
   eval ((x,v1)::env) s1 e2 res ⇒
   eval env s (Let x e1 e2) res) ∧
  (eval env s e1 res ∧ (∀v. FST res ≠ Rval v) ⇒
   eval env s (Let x e1 e2) res) ∧
  (eval env s (Fun x e) (Rval (Clos env x e),s)) ∧
  (eval env s (Funrec f x e) (Rval (Closrec env f x e),s)) ∧
  (eval env s e (Rval v1,s1) ⇒
   eval env s (Ref e) (Rval (Loc (LENGTH s1.refs)), s1 with refs := s1.refs ++ [v1])) ∧
  (eval env s e res ∧ (∀v. FST res ≠ Rval v) ⇒
   eval env s (Ref e) res) ∧
  (eval env s e (Rval (Loc n), s1) ∧
   n < LENGTH s1.refs
   ⇒
   eval env s (Deref e) (Rval (EL n s1.refs),s1)) ∧
  (eval env s e (Rval (Loc n), s1) ∧
   ¬(n < LENGTH s1.refs)
   ⇒
   eval env s (Deref e) (Rfail,s1)) ∧
  (eval env s e (Rval v, s1) ∧ (∀n. v ≠ Loc n) ⇒
   eval env s (Deref e) (Rfail, s1)) ∧
  (eval env s e res ∧ (∀v. FST res ≠ Rval v) ⇒
   eval env s (Deref e) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   (v1 = Loc n) ∧ n < LENGTH s2.refs
   ⇒
   eval env s (Assign e1 e2) (Rval (Litv Unit), s2 with refs := LUPDATE v2 n s2.refs)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   (∀n. v1 = Loc n ⇒ ¬(n < LENGTH s2.refs))
   ⇒
   eval env s (Assign e1 e2) (Rfail, s2)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (Assign e1 e2) res) ∧
  (eval env s e1 res ∧ (∀v. FST res ≠ Rval v) ⇒
   eval env s (Assign e1 e2) res) ∧
  (eval ((x,Exn(s.next_exn))::env) (s with next_exn := s.next_exn + 1) e res ⇒
   eval env s (Letexn x e) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   (v1 = Exn n)
   ⇒
   eval env s (Raise e1 e2) (Rraise n v2, s2)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   (∀n. v1 ≠ Exn n)
   ⇒
   eval env s (Raise e1 e2) (Rfail, s2)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   eval env s1 e2 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (Raise e1 e2) res) ∧
  (eval env s e1 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (Raise e1 e2) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   (v1 = Exn n) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   dest_closure v3 v2 = SOME (env',e) ∧
   eval env s2 e3 (Rraise n v3, s3) ∧
   eval env' (dec_clock s3) e res
   ⇒
   eval env s (Handle e3 e1 e2) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   (v1 = Exn n) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   dest_closure v3 v2 = SOME (env',e) ∧
   eval env s2 e3 (Rraise n3 v3, s3) ∧
   (n3 ≠ n)
   ⇒
   eval env s (Handle e3 e1 e2) (Rraise n3 v3, s3)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   (v1 = Exn n) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   dest_closure v3 v2 = SOME (env',e) ∧
   eval env s2 e3 res ∧ (∀n v. FST res ≠ Rraise n v)
   ⇒
   eval env s (Handle e3 e1 e2) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   (v1 = Exn n) ∧
   eval env s1 e2 (Rval v2, s2) ∧
   dest_closure v3 v2 = NONE
   ⇒
   eval env s (Handle e3 e1 e2) (Rfail, s2)) ∧
  (eval env s e1 (Rval v1, s1) ∧
   (v1 = Exn n) ∧
   eval env s1 e2 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (Handle e3 e1 e2) res) ∧
  (eval env s e1 (Rval v1, s1) ∧
   (∀n. v1 ≠ Exn n)
   ⇒
   eval env s (Handle e3 e1 e2) (Rfail, s1)) ∧
  (eval env s e1 res ∧ (∀v. FST res ≠ Rval v)
   ⇒
   eval env s (Handle e3 e1 e2) res)`

(* sanity-check: equivalence of semantics *)

val v_distinct = theorem"v_distinct";
val v_nchotomy = theorem"v_nchotomy";
val v_11 = theorem"v_11";
val r_distinct = theorem"r_distinct";

val sem_imp_eval = Q.store_thm("sem_imp_eval",
  `∀env s e. FST (sem env s e) ≠ Rtimeout ⇒
      eval env s e (sem env s e)`,
  ho_match_mp_tac sem_ind >> rw[sem_def]
  >- rw[Once eval_cases]
  >- (
    rw[Once eval_cases] >>
    every_case_tac >> fs[]
    )
  >- (
    every_case_tac >> fs[] >> rw[] >> rfs[] >>
    rw[Once eval_cases] >>
    metis_tac[dest_closure_def]
    )
  >- (
    every_case_tac >> fs[] >> rw[] >>
    rw[Once eval_cases] >>
    metis_tac[]
    )
  >- rw[Once eval_cases]
  >- rw[Once eval_cases]
  >- (
    every_case_tac >> fs[] >> rw[] >>
    rw[Once eval_cases] >>
    metis_tac[]
    )
  >- (
    every_case_tac >> fs[] >> rw[] >>
    rw[Once eval_cases] >>
    metis_tac[v_distinct]
    )
  >- (
    every_case_tac >> fs[] >> rw[] >> rfs[] >>
    rw[Once eval_cases] >>
    metis_tac[v_distinct,FST,r_distinct,v_11]
    )
  >- rw[Once eval_cases]
  >- (
    every_case_tac >> fs[] >> rw[] >>
    rw[Once eval_cases] >>
    metis_tac[v_distinct,FST,r_distinct]
    )
  >- (
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    rw[Once eval_cases] >>
    every_case_tac >> fs[] >>
    metis_tac[is_closure_def,dest_closure_def,v_distinct,v_nchotomy]
    )
  );

val dest_closure_SOME_is_closure = Q.prove(
  `dest_closure x y = SOME z ⇒ is_closure y`,
  Cases_on`y`>>rw[])

val eval_imp_sem = Q.store_thm("eval_imp_sem",
  `∀env s e res.
    eval env s e res ⇒
      FST (sem env s e) = Rtimeout ∨
      sem env s e = res`,
  ho_match_mp_tac eval_ind >> rw[sem_def] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[] >>
  TRY(BasicProvers.CASE_TAC >> fs[] >> rw[]) >>
  TRY(BasicProvers.CASE_TAC >> fs[] >> rw[]) >>
  TRY(BasicProvers.CASE_TAC >> fs[] >> rw[]) >>
  TRY(BasicProvers.CASE_TAC >> fs[] >> rw[]) >>
  imp_res_tac dest_closure_SOME_is_closure >> fs[] >>
  every_case_tac >> fs[]);

(* Typing *)

(*
Whereas W&F use two categories of type variables (applicative and imperative),
we follow the more modern approach to making let-polymorphism sound with a
value restriction.
*)

val is_value_def = Define`
  is_value (Lit _) = T ∧
  is_value (Var _) = T ∧
  is_value (Fun _ _) = T ∧
  is_value (Funrec _ _ _) = T ∧
  is_value _ = F`
val _ = export_rewrites["is_value_def"]

(* syntax of types *)

val _ = Datatype`tctor =
  | TC_int
  | TC_fn
  | TC_ref
  | TC_unit
  | TC_exn`

val _ = Datatype`t =
  | Tvar string
  | Tapp (t list) tctor`

val t_size_def = definition"t_size_def"
val t_induction = theorem"t_induction"

val t_ind =
  t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss()) []
  |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
  |> GEN_ALL
  |> curry save_thm "t_ind"

val _ = overload_on("Tint",``Tapp [] TC_int``)
val _ = overload_on("Tfn",``λt1 t2. Tapp [t1;t2] TC_fn``)
val _ = overload_on("Tref",``λt. Tapp [t] TC_ref``)
val _ = overload_on("Tunit",``Tapp [] TC_unit``)
val _ = overload_on("Texn",``λt. Tapp [t] TC_exn``)

(* substitution for variables in a type *)

Definition tysubst_def0[induction=tysubst_ind]:
  (tysubst s (Tvar x) =
     (case FLOOKUP s x of
      | SOME t => t
      | NONE => Tvar x)) ∧
  tysubst s (Tapp ts tc) =
    Tapp (MAP (tysubst s) ts) tc
Termination
 WF_REL_TAC`measure (t_size o SND)` >>
 rpt gen_tac >> Induct_on`ts` >>
 rw[t_size_def] >> res_tac >>simp[]
End
Theorem tysubst_def[simp] =
  tysubst_def0
  |> SIMP_RULE (std_ss++boolSimps.ETA_ss)[]

(* free variables in a type *)

Definition tyvars_def0:
  (tyvars (Tvar x) = {x}) ∧
  (tyvars (Tapp ts _) = BIGUNION (IMAGE tyvars (set ts)))
Termination
 WF_REL_TAC`measure (t_size)` >>
 rpt gen_tac >> Induct_on`ts` >>
 rw[t_size_def] >> res_tac >>simp[]
End
Theorem tyvars_def[simp] =
  tyvars_def0
  |> SIMP_RULE (std_ss++boolSimps.ETA_ss)[]

(*
A type environment is a map from (expression) variables to type schemes, where
a type scheme is a type some of whose variables are considered bound. We
represent a type scheme by (tvs:string set, t:t), which is t with the variables
in tvs bound.
*)

(* free variables in a type environment *)

val tenv_vars_def = Define`
  tenv_vars tenv =
    BIGUNION (IMAGE ((λ(tvs,t). tyvars t DIFF tvs) o SND) (set tenv))`

val tenv_vars_cons = store_thm("tenv_vars_cons",
  ``tenv_vars ((x,tvs,t)::tenv) =
    tyvars t DIFF tvs ∪ tenv_vars tenv``,
  rw[tenv_vars_def])

(* typing relation *)

val (type_e_rules,type_e_ind,type_e_cases) = Hol_reln`
  (type_e tenv (Lit (Int i)) Tint) ∧
  (type_e tenv (Lit Unit) Tunit) ∧
  (ALOOKUP tenv x = SOME (tvs,t) ∧ FDOM s ⊆ tvs
    ⇒ type_e tenv (Var x) (tysubst s t)) ∧
  (type_e tenv e1 (Tfn t1 t2) ∧
   type_e tenv e2 t1
   ⇒ type_e tenv (App e1 e2) t2) ∧
  (is_value e1 ∧
   type_e tenv e1 t1 ∧
   type_e ((x,(tyvars t1 DIFF (tenv_vars tenv),t1))::tenv) e2 t2
   ⇒ type_e tenv (Let x e1 e2) t2) ∧
  (¬is_value e1 ∧
   type_e tenv e1 t1 ∧
   type_e ((x,({},t1))::tenv) e2 t2
   ⇒ type_e tenv (Let x e1 e2) t2) ∧
  (type_e ((x,({},t1))::tenv) e t2
   ⇒ type_e tenv (Fun x e) (Tfn t1 t2)) ∧
  (type_e ((x,({},t1))::(f,({},Tfn t1 t2))::tenv) e t2
   ⇒ type_e tenv (Funrec f x e) (Tfn t1 t2)) ∧
  (type_e tenv e t ⇒
   type_e tenv (Ref e) (Tref t)) ∧
  (type_e tenv e (Tref t) ⇒
   type_e tenv (Deref e) t) ∧
  (type_e tenv e1 (Tref t) ∧
   type_e tenv e2 t ⇒
   type_e tenv (Assign e1 e2) Tunit) ∧
  (type_e ((x,({},Texn t1))::tenv) e t2
   ⇒ type_e tenv (Letexn x e) t2) ∧
  (type_e tenv e1 (Texn t) ∧
   type_e tenv e2 t
   ⇒ type_e tenv (Raise e1 e2) t2) ∧
  (type_e tenv e3 t3 ∧
   type_e tenv e1 (Texn t1) ∧
   type_e tenv e2 (Tfn t1 t3)
   ⇒ type_e tenv (Handle e3 e1 e2) t3)`

(*
To state the type soundness theorem, we also need a typing relation on values.
The typing relation on values has two parameters, rt and et, indicating the
types of references and exceptions.
*)

val (type_v_rules,type_v_ind,type_v_cases) = Hol_reln`
  (type_v rt et (Litv (Int i)) Tint) ∧
  (type_v rt et (Litv (Unit)) Tunit) ∧
  (type_env rt et env tenv ∧
   type_e ((x,({},t1))::tenv) e t2
   ⇒ type_v rt et (Clos env x e) (Tfn t1 t2)) ∧
  (type_env rt et env tenv ∧
   type_e ((x,({},t1))::(f,({},Tfn t1 t2))::tenv) e t2
   ⇒ type_v rt et (Closrec env f x e) (Tfn t1 t2)) ∧
  (n < LENGTH rt
   ⇒ type_v rt et (Loc n) (Tref (EL n rt))) ∧
  (n < LENGTH et
   ⇒ type_v rt et (Exn n) (Texn (EL n et))) ∧
  (type_env rt et [] []) ∧
  (tvs ⊆ tyvars t ∧
   (∀s. FDOM s ⊆ tvs ⇒ type_v rt et v (tysubst s t)) ∧
   type_env rt et env tenv
   ⇒ type_env rt et ((x,v)::env) ((x,(tvs,t))::tenv))`

(* abbreviation for: a value has all the types represented by a type scheme *)
val _ = overload_on("type_v_ts",``λrt et v tvs t. ∀s. FDOM s ⊆ tvs ⇒ type_v rt et v (tysubst s t)``)

(* we now have a series of lemmas about the type system *)

val type_e_clauses =
  [``type_e tenv (Lit i) t``
  ,``type_e tenv (Var x) t``
  ,``type_e tenv (App e1 e2) t``
  ,``type_e tenv (Let x e1 e2) t``
  ,``type_e tenv (Fun x e) t``
  ,``type_e tenv (Funrec f x e) t``
  ,``type_e tenv (Ref e) t``
  ,``type_e tenv (Deref e) t``
  ,``type_e tenv (Assign e1 e2) t``
  ,``type_e tenv (Letexc x e) t``
  ,``type_e tenv (Raise e1 e2) t``
  ,``type_e tenv (Handle e3 e1 e2) t``
  ]
  |> List.map (SIMP_CONV (srw_ss()) [Once type_e_cases])
  |> LIST_CONJ

val type_v_clauses =
  [``type_v s z (Litv i) t``
  ,``type_v s z (Clos env x e) t``
  ,``type_v s z (Closrec env f x e) t``
  ,``type_v s z (Loc n) t``
  ,``type_v s z (Exn n) t``
  ]
  |> List.map (SIMP_CONV (srw_ss()) [Once type_v_cases])
  |> LIST_CONJ

val type_env_clauses =
  [``type_env s z [] tenv``
  ,``type_env s z (x::y) tenv``
  ]
  |> List.map (SIMP_CONV (srw_ss()) [Once type_v_cases])
  |> LIST_CONJ

val type_v_extend = store_thm("type_v_extend",
  ``(∀v t. type_v s e v t ⇒ type_v (s++s') (e++e') v t) ∧
    (∀env tenv. type_env s e env tenv ⇒ type_env (s++s') (e++e') env tenv)``,
  ho_match_mp_tac type_v_ind >>
  simp[type_v_clauses,type_env_clauses] >>
  rw[] >> simp[rich_listTheory.EL_APPEND1] >> metis_tac[])

val FINITE_tyvars = store_thm("FINITE_tyvars[simp]",
  ``∀t. FINITE (tyvars t)``,
  ho_match_mp_tac t_ind >> simp[] >>
  simp[EVERY_MEM,PULL_EXISTS])

val FINITE_tenv_vars = store_thm("FINITE_tenv_vars[simp]",
  ``FINITE (tenv_vars tenv)``,
  rw[tenv_vars_def,EXISTS_PROD] >> rw[])

val tysubst_tysubst = store_thm("tysubst_tysubst",
  ``∀s t s'. tysubst s' (tysubst s t) = tysubst ((tysubst s' o_f s) ⊌ s') t``,
  ho_match_mp_tac tysubst_ind >>
  conj_tac >- (
    simp[] >>
    rpt gen_tac >>
    simp[FLOOKUP_o_f,FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >> simp[] ) >>
  rw[MAP_MAP_o,MAP_EQ_f])

val tysubst_nil = store_thm("tysubst_nil[simp]",
  ``∀t. tysubst FEMPTY t = t``,
  ho_match_mp_tac t_ind >>
  simp[EVERY_MEM,LIST_EQ_REWRITE,EL_MAP,MEM_EL,PULL_EXISTS])

val tyvars_tysubst = store_thm("tyvars_tysubst",
  ``∀t. tyvars (tysubst s t) = (tyvars t DIFF FDOM s) ∪ BIGUNION { tyvars u | ∃x. x ∈ tyvars t ∧ FLOOKUP s x = SOME u }``,
  ho_match_mp_tac t_ind >> simp[] >> rw[] >>
  TRY BasicProvers.CASE_TAC >>
  TRY (fs[FLOOKUP_DEF] >> NO_TAC) >> rw[] >- (
    rw[Once EXTENSION,PULL_EXISTS] ) >>
  fs[PULL_EXISTS,EVERY_MEM] >>
  fs[Once EXTENSION,PULL_EXISTS,MEM_MAP] >>
  metis_tac[])

val tysubst_frees = store_thm("tysubst_frees",
  ``∀t. (∀x. x ∈ tyvars t ⇒
          FLOOKUP s1 x = FLOOKUP s2 x) ⇒
        tysubst s1 t = tysubst s2 t``,
  ho_match_mp_tac t_ind >> simp[] >>
  rw[LIST_EQ_REWRITE,EL_MAP] >>
  fs[EVERY_MEM,PULL_EXISTS,MEM_EL] >>
  metis_tac[])

val tysubst_frees_gen = store_thm("tysubst_frees_gen",
  ``∀t. (∀x. x ∈ tyvars t ⇒
          FLOOKUP (s1 ⊌ FUN_FMAP Tvar {x}) x = FLOOKUP (s2 ⊌ FUN_FMAP Tvar {x}) x) ⇒
        tysubst s1 t = tysubst s2 t``,
  ho_match_mp_tac t_ind >>
  conj_tac >- (
    simp[FLOOKUP_FUNION,FLOOKUP_FUN_FMAP] >>
    gen_tac >> BasicProvers.EVERY_CASE_TAC ) >>
  rw[LIST_EQ_REWRITE,EL_MAP] >>
  fs[EVERY_MEM,PULL_EXISTS,MEM_EL] >>
  metis_tac[])

(* alpha-equivalence of type schemes *)

Definition raconv_def0[induction=raconv_ind]:
  (raconv f tvs1 tvs2 (Tvar x1) (Tvar x2) ⇔
     if x1 ∈ tvs1 then f x1 = x2
     else x2 = x1 ∧ x1 ∉ tvs2) ∧
  (raconv f tvs1 tvs2 (Tapp ts1 tc1) (Tapp ts2 tc2) ⇔
     tc2 = tc1 ∧ LIST_REL (raconv f tvs1 tvs2) ts1 ts2) ∧
  (raconv _ _ _ _ _ = F)
Termination
(WF_REL_TAC`measure (t_size o SND o SND o SND o SND)` >>
 rpt gen_tac >> Induct_on`ts2` >> simp[t_size_def] >>
 rw[] >> res_tac >> simp[])
End
Theorem raconv_def[simp] =
  raconv_def0
  |> SIMP_RULE (std_ss++boolSimps.ETA_ss) []

val tsaconv_def = Define`
  tsaconv (ftvs1,t1) (ftvs2,t2) ⇔
    let tvs1 = ftvs1 ∩ tyvars t1 in
    let tvs2 = ftvs2 ∩ tyvars t2 in
    ∃f. BIJ f tvs1 tvs2 ∧
        raconv f tvs1 tvs2 t1 t2`

val raconv_refl = store_thm("raconv_refl",
  ``∀tvs t. raconv (λx. x) tvs tvs t t``,
  gen_tac >> ho_match_mp_tac t_ind >>
  simp[LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS])

val tsaconv_refl = store_thm("tsaconv_refl[simp]",
  ``∀ts. tsaconv ts ts``,
  Cases >> simp[tsaconv_def] >>
  qspec_tac(`q ∩ tyvars r`,`tvs`) >> gen_tac >>
  qexists_tac`λx. x` >>
  conj_tac >- simp[BIJ_ID] >>
  metis_tac[raconv_refl])

val tsaconv_sym = store_thm("tsaconv_sym",
  ``∀t1 t2. tsaconv t1 t2 ⇒ tsaconv t2 t1``,
  Cases >> Cases >> simp[tsaconv_def] >>
  qspec_tac(`q ∩ tyvars r`,`tvs1`) >> gen_tac >>
  qspec_tac(`q' ∩ tyvars r'`,`tvs2`) >> gen_tac >>
  strip_tac >>
  qexists_tac`LINV f tvs1` >>
  conj_tac >- simp[BIJ_LINV_BIJ] >>
  pop_assum mp_tac >>
  map_every qid_spec_tac[`r'`,`r`] >>
  ho_match_mp_tac t_ind >>
  conj_tac >- (
    gen_tac >> Cases >> simp[] >>
    `INJ f tvs1 tvs2` by fs[BIJ_DEF] >>
    rw[] >>
    imp_res_tac LINV_DEF >>
    imp_res_tac BIJ_LINV_INV >>
    metis_tac[INJ_DEF]) >>
  gen_tac >> strip_tac >>
  gen_tac >> Cases >> simp[] >>
  fs[EVERY_MEM,LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS])

val raconv_trans = store_thm("raconv_trans",
  ``∀f1 tvs1 tvs2 t1 t2 t3.
    BIJ f1 tvs1 tvs2 ⇒
    raconv f1 tvs1 tvs2 t1 t2 ⇒
    BIJ f2 tvs2 tvs3 ⇒
    raconv f2 tvs2 tvs3 t2 t3 ⇒
    raconv (f2 o f1) tvs1 tvs3 t1 t3``,
  ho_match_mp_tac raconv_ind >>
  conj_tac >- (
    ntac 5 gen_tac >>
    Cases >> simp[] >>
    rw[] >> fs[] >>
    metis_tac[BIJ_DEF,INJ_DEF] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    Cases >> simp[] >> rw[] >>
    fs[LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS] >>
    rw[] >> first_x_assum (match_mp_tac o MP_CANON) >>
    metis_tac[] ) >>
  simp[])

val tsaconv_trans = store_thm("tsaconv_trans",
  ``∀t1 t2 t3. tsaconv t1 t2 ∧ tsaconv t2 t3 ⇒ tsaconv t1 t3``,
  Cases >> Cases >> Cases >> rw[tsaconv_def] >> fs[LET_THM] >>
  PROVE_TAC[raconv_trans,BIJ_COMPOSE])

val raconv_tyvars_eq = prove(
  ``∀f tvs1 tvs2 t1 t2.
      BIJ f tvs1 tvs2 ⇒
        raconv f tvs1 tvs2 t1 t2 ⇒
          tyvars t1 DIFF tvs1 =
          tyvars t2 DIFF tvs2``,
  ho_match_mp_tac raconv_ind >> reverse(rw[]) >- (
    fs[Once EXTENSION,PULL_EXISTS] >>
    fs[LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS] >>
    metis_tac[] ) >>
  fs[BIJ_DEF,INJ_DEF] >> metis_tac[] )

val tsaconv_tyvars_eq = store_thm("tsaconv_tyvars_eq",
  ``∀t1 t2. tsaconv t1 t2 ⇒
      tyvars (SND t1) DIFF (FST t1) =
      tyvars (SND t2) DIFF (FST t2)``,
  Cases >> Cases >> simp[tsaconv_def] >>
  strip_tac >> imp_res_tac raconv_tyvars_eq >>
  fs[EXTENSION] >> metis_tac[])

val raconv_imp_tysubst = store_thm("raconv_imp_tysubst",
  ``∀f tvs1 tvs2 t1 t2.
      BIJ f tvs1 tvs2 ⇒
      FINITE tvs1 ⇒
      raconv f tvs1 tvs2 t1 t2 ⇒
      tysubst (FUN_FMAP (Tvar o f) tvs1) t1 = t2``,
  ho_match_mp_tac raconv_ind >>
  rw[] >>
  simp[FUN_FMAP_DEF,FLOOKUP_FUN_FMAP] >>
  fs[LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS,LIST_EQ_REWRITE,EL_MAP])

val tsaconv_imp_tysubst = store_thm("tsaconv_imp_tysubst",
  ``∀t1 t2. tsaconv t1 t2 ⇒
    FINITE (FST t1) ⇒
    ∃s. FDOM s = FST t1 ∩ tyvars (SND t1) ∧
        FRANGE s = IMAGE Tvar (FST t2 ∩ tyvars (SND t2)) ∧
        tysubst s (SND t1) = SND t2``,
  Cases >> Cases >> simp[tsaconv_def] >> rw[] >>
  qmatch_assum_rename_tac`BIJ f (tvs1 ∩ tyvars t1) (tvs2 ∩ tyvars t2)` >>
  imp_res_tac raconv_imp_tysubst >> rfs[] >>
  qexists_tac`FUN_FMAP (Tvar o f) (tvs1 ∩ tyvars t1)` >> rw[] >>
  fs[BIJ_DEF,IMAGE_COMPOSE,IMAGE_SURJ])

Theorem tysubst_imp_raconv:
  ∀f tvs1 tvs2 t1 t2.
      FINITE tvs1 ∧
      tysubst (FUN_FMAP (Tvar o f) tvs1) t1 = t2 ∧
      BIJ f tvs1 tvs2 ∧
      DISJOINT tvs2 (tyvars t1)
      ⇒
      raconv f tvs1 tvs2 t1 t2
Proof
  ho_match_mp_tac raconv_ind >> simp[] >>
  conj_tac >- (
    rw[] >> rfs[FLOOKUP_DEF,FLOOKUP_FUN_FMAP] ) >>
  rw[] >> fs[] >- (
    rw[LIST_REL_EL_EQN,EL_MAP] >>
    first_x_assum(match_mp_tac o MP_CANON) >>
    simp[MEM_MAP,PULL_EXISTS] >>
    qexists_tac`EL n ts1` >>
    simp[MEM_EL] >>
    fs[PULL_EXISTS,MEM_EL] >>
    metis_tac[] ) >>
  gs[AllCaseEqs()] >>
  spose_not_then strip_assume_tac >>
  gs[FLOOKUP_FUN_FMAP]
QED

val tysubst_imp_aconv = store_thm("tysubst_imp_aconv",
  ``∀f tvs1 t1 tvs2.
    FINITE tvs1 ∧
    BIJ f tvs1 tvs2 ∧
    DISJOINT tvs2 (tyvars t1)
    ⇒
    tsaconv (tvs1,t1) (tvs2,tysubst (FUN_FMAP (Tvar o f) tvs1) t1)``,
  rw[tsaconv_def] >>
  qexists_tac`f` >>
  conj_asm1_tac >- (
    unabbrev_all_tac >>
    fs[BIJ_IFF_INV,tyvars_tysubst,PULL_EXISTS,FLOOKUP_FUN_FMAP,IN_DISJOINT] >>
    qexists_tac`g` >>
    metis_tac[]) >>
  match_mp_tac tysubst_imp_raconv >>
  unabbrev_all_tac >> rw[] >- (
    match_mp_tac tysubst_frees >>
    simp[FLOOKUP_FUN_FMAP] ) >>
  fs[IN_DISJOINT,tyvars_tysubst,FLOOKUP_FUN_FMAP,PULL_EXISTS] >>
  metis_tac[])

val raconv_eq = prove(
  ``∀t1 t2. raconv f ∅ ∅ t1 t2 ⇒ t1 = t2``,
  ho_match_mp_tac t_ind >>
  conj_tac >- (
    gen_tac >> Cases >> simp[] ) >>
  gen_tac >> strip_tac >> gen_tac >>
  Cases >> simp[] >> rw[] >>
  fs[LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  rw[LIST_EQ_REWRITE])

val tsaconv_eq = store_thm("tsaconv_eq",
  ``tsaconv ({},t1) ({},t2) ⇔ t1 = t2``,
  reverse EQ_TAC >- metis_tac[tsaconv_refl] >>
  rw[tsaconv_def] >> metis_tac[raconv_eq])

val tsaconv_empty_imp = prove(
  ``tsaconv (∅,t) ts ⇒ FST ts ∩ tyvars (SND ts) = ∅``,
  Cases_on`ts`>> simp[tsaconv_def] >> rw[])

(* the typing rules respect alpha-equivalence *)

val ALOOKUP_MAP_FST_EQ_MAP_SND_REL = store_thm("ALOOKUP_MAP_FST_EQ_MAP_SND_REL",
  ``∀l1 l2 x y1.
    MAP FST l1 = MAP FST l2 ∧
    LIST_REL R (MAP SND l1) (MAP SND l2) ∧
    ALOOKUP l1 x = SOME y1 ⇒
    ∃y2. ALOOKUP l2 x = SOME y2 ∧ R y1 y2``,
  Induct >> simp[] >>
  Cases >> Cases >> simp[] >>
  Cases_on`h`>>rw[] >> rw[])

val type_e_aconv = store_thm("type_e_aconv",
  ``∀tenv e t. type_e tenv e t ⇒
      EVERY (FINITE o FST o SND) tenv ⇒
      ∀tenv'.
        EVERY (FINITE o FST o SND) tenv' ∧
        MAP FST tenv = MAP FST tenv' ∧
        LIST_REL tsaconv (MAP SND tenv) (MAP SND tenv') ⇒
        type_e tenv' e t``,
  ho_match_mp_tac type_e_ind >>
  conj_tac >- simp[type_e_clauses] >>
  conj_tac >- simp[type_e_clauses] >>
  conj_tac >- (
    simp[type_e_clauses] >> rw[] >>
    `∃z. ALOOKUP tenv' x = SOME z ∧ tsaconv (tvs,t) z` by
      metis_tac[ALOOKUP_MAP_FST_EQ_MAP_SND_REL] >>
    Cases_on`z`>>simp[]>>
    first_x_assum(strip_assume_tac o MATCH_MP tsaconv_sym) >>
    first_assum(mp_tac o MATCH_MP tsaconv_imp_tysubst) >> simp[] >>
    discharge_hyps >- (
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,FORALL_PROD] >>
      metis_tac[] ) >>
    rw[] >> rw[tysubst_tysubst] >>
    qexists_tac`tysubst s o_f s'` >> simp[] >>
    match_mp_tac tysubst_frees_gen >>
    simp[FLOOKUP_FUNION,FLOOKUP_o_f,FLOOKUP_FUN_FMAP] >>
    gen_tac >> BasicProvers.CASE_TAC >>
    strip_tac >>
    BasicProvers.CASE_TAC >>
    qmatch_assum_rename_tac`z ∈ tyvars t` >>
    `z ∉ q` by (rfs[FLOOKUP_DEF]>>fs[]) >>
    imp_res_tac tsaconv_tyvars_eq >> fs[] >>
    pop_assum mp_tac >>
    simp[EXTENSION] >>
    disch_then(qspec_then`z`mp_tac) >> simp[] >>
    `z ∉ FDOM s'` by fs[FLOOKUP_DEF] >> simp[] >>
    simp[tyvars_tysubst] >> strip_tac >>
    fs[SUBSET_DEF,PULL_EXISTS,FLOOKUP_DEF] >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[type_e_clauses] >>
    rw[] >> fs[] >> metis_tac[] ) >>
  conj_tac >- (
    simp[type_e_clauses] >> rw[] >> fs[] >>
    `tenv_vars tenv = tenv_vars tenv'` by (
      simp[tenv_vars_def,IMAGE_COMPOSE,GSYM LIST_TO_SET_MAP] >>
      simp[MAP_MAP_o] >>
      AP_TERM_TAC >> AP_TERM_TAC >>
      simp[MAP_EQ_f] >>
      pop_assum mp_tac >>
      simp[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP,GSYM AND_IMP_INTRO] >>
      rw[] >> res_tac >>
      imp_res_tac tsaconv_tyvars_eq >>
      simp[UNCURRY] ) >>
    qexists_tac`t` >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[] ) >>
  conj_tac >- (
    simp[type_e_clauses] >> rw[] >> fs[] >>
    qexists_tac`t` >> simp[] ) >>
  conj_tac >- ( simp[type_e_clauses] ) >>
  conj_tac >- ( simp[type_e_clauses] ) >>
  conj_tac >- ( simp[type_e_clauses] ) >>
  conj_tac >- ( simp[type_e_clauses] ) >>
  conj_tac >- (
    simp[type_e_clauses] >>
    rw[] >> fs[] >>
    metis_tac[]) >>
  conj_tac >- (
    simp[type_e_clauses] >> rw[] >> fs[] >>
    `tenv_vars tenv = tenv_vars tenv'` by (
      simp[tenv_vars_def,IMAGE_COMPOSE,GSYM LIST_TO_SET_MAP] >>
      simp[MAP_MAP_o] >>
      AP_TERM_TAC >> AP_TERM_TAC >>
      simp[MAP_EQ_f] >>
      pop_assum mp_tac >>
      simp[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP,GSYM AND_IMP_INTRO] >>
      rw[] >> res_tac >>
      imp_res_tac tsaconv_tyvars_eq >>
      simp[UNCURRY] ) >>
    qexists_tac`t1` >> simp[]) >>
  conj_tac >- (
    simp[type_e_clauses] >>
    rw[] >> fs[] >>
    metis_tac[]) >>
  simp[type_e_clauses] >>
  rw[] >> fs[] >>
  metis_tac[])

val type_v_ts_aconv = store_thm("type_v_ts_aconv",
  ``FINITE tvs ∧
    type_v_ts rt et v tvs t ∧ tsaconv (tvs,t) (tvs',t') ⇒
    type_v_ts rt et v tvs' t'``,
  rw[] >>
  imp_res_tac tsaconv_imp_tysubst >>
  rfs[] >> rw[] >>
  rw[tysubst_tysubst] >>
  Q.PAT_ABBREV_TAC`ss = X ⊌ s` >>
  `tysubst ss t = tysubst (DRESTRICT ss (tyvars t)) t` by (
    match_mp_tac tysubst_frees >> simp[FLOOKUP_DRESTRICT] ) >>
  pop_assum SUBST1_TAC >>
  first_x_assum match_mp_tac >>
  simp[FDOM_DRESTRICT,Abbr`ss`] >>
  imp_res_tac tsaconv_tyvars_eq >>
  fs[EXTENSION] >>
  fs[SUBSET_DEF] >> rw[] >>
  metis_tac[])

(* a type scheme that is fresh for any finite set of variables exists *)

val fresh_def = new_specification("fresh_def",["fresh"],
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])

Definition fresh_seq_def0:
  fresh_seq avoid n = fresh (avoid ∪ (IMAGE (fresh_seq avoid) (count n)))
Termination WF_REL_TAC`measure (I o SND)` >> simp[]
End
Theorem fresh_seq_def =
  fresh_seq_def0
  |> SIMP_RULE (std_ss++boolSimps.ETA_ss)[]

val fresh_seq_thm = store_thm("fresh_seq_thm",
  ``∀avoid n.
      FINITE avoid ⇒
      fresh_seq avoid n ∉ avoid ∧
      ∀k. k < n ⇒ fresh_seq avoid n ≠ fresh_seq avoid k``,
  simp[fresh_seq_def] >>
  rpt gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`s = avoid ∪ X` >>
  `FINITE s` by simp[Abbr`s`] >>
  qspec_then`s`mp_tac fresh_def >>
  simp[Abbr`s`] >> rw[] >>
  fs[fresh_seq_def] >>
  metis_tac[])

val ALL_DISTINCT_fresh_seq = prove(
  ``∀n avoid. FINITE avoid ⇒ ALL_DISTINCT (GENLIST (fresh_seq avoid) n)``,
  Induct >> simp[GENLIST,ALL_DISTINCT_SNOC,MEM_GENLIST] >>
  metis_tac[fresh_seq_thm])

val DISJOINT_fresh_seq = prove(
  ``∀n avoid. FINITE avoid ⇒ DISJOINT (set (GENLIST (fresh_seq avoid) n)) avoid``,
  Induct >> simp[GENLIST,LIST_TO_SET_SNOC] >>
  metis_tac[fresh_seq_thm])

val BIJ_UPDATE_NOTIN = store_thm("BIJ_UPDATE_NOTIN",
  ``BIJ f s t ∧ x ∉ s ⇒ BIJ ((x =+ y) f) s t``,
  rw[BIJ_DEF,INJ_DEF,SURJ_DEF,combinTheory.APPLY_UPDATE_THM] >> rw[] >>
  metis_tac[])

val BIJ_fresh_seq = prove(
  ``∀s. FINITE s ⇒ ∀a. FINITE a ⇒
      ∃f. BIJ f s (set (GENLIST (fresh_seq a) (CARD s)))``,
  ho_match_mp_tac FINITE_INDUCT >>
  conj_tac >- simp[] >>
  gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  first_x_assum(qspec_then`a`(fn th => first_assum(strip_assume_tac o MATCH_MP th))) >>
  simp[GENLIST,LIST_TO_SET_SNOC,BIJ_INSERT] >>
  qexists_tac`(e =+ fresh_seq a (CARD s)) f` >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  qmatch_assum_abbrev_tac`BIJ f s t` >>
  simp[DELETE_INSERT] >>
  Q.PAT_ABBREV_TAC`n = fresh_seq a Z` >>
  `n ∉ t` by (
    simp[Abbr`t`,MEM_GENLIST,Abbr`n`] >>
    spose_not_then strip_assume_tac >>
    qspecl_then[`SUC(CARD s)`,`a`]mp_tac ALL_DISTINCT_fresh_seq >>
    simp[ALL_DISTINCT_GENLIST] >>
    qexists_tac`CARD s` >>
    qexists_tac`m` >>
    simp[]) >>
  pop_assum(SUBST1_TAC o REWRITE_RULE[DELETE_NON_ELEMENT]) >>
  match_mp_tac BIJ_UPDATE_NOTIN >> rw[])

val fresh_ts_exists = prove(
  ``∃f. ∀avoid ts.
      FINITE avoid ∧
      FINITE (FST ts) ⇒
      DISJOINT avoid (FST (f avoid ts)) ∧
      tsaconv ts (f avoid ts) ∧
      FST(f avoid ts) ⊆ tyvars (SND(f avoid ts))``,
  simp[GSYM SKOLEM_THM] >>
  rw[RIGHT_EXISTS_IMP_THM] >>
  `∃f tvs2. BIJ f (FST ts) tvs2 ∧ DISJOINT tvs2 (tyvars (SND ts) ∪ avoid)` by (
    Q.PAT_ABBREV_TAC`a = X ∪ avoid` >>
    Q.PAT_ABBREV_TAC`s = FST ts` >>
    qabbrev_tac`ls = GENLIST (fresh_seq a) (CARD s)` >>
    Q.ISPEC_THEN`s`mp_tac BIJ_fresh_seq >> simp[] >>
    disch_then(qspec_then`a`mp_tac) >>
    discharge_hyps >- simp[Abbr`a`] >> strip_tac >>
    first_assum(match_exists_tac o concl) >>
    conj_tac >- simp[] >>
    simp[Abbr`ls`,DISJOINT_fresh_seq,Abbr`a`] ) >>
  qspecl_then[`f`,`FST ts`,`SND ts`,`tvs2`]mp_tac tysubst_imp_aconv >>
  simp[] >> fs[] >> simp[Once DISJOINT_SYM] >>
  strip_tac >>
  simp[EXISTS_PROD] >>
  qmatch_assum_abbrev_tac`tsaconv ts (tvs2,t2)` >>
  qexists_tac`tvs2 ∩ tyvars t2` >> qexists_tac`t2` >>
  fs[IN_DISJOINT] >>
  conj_tac >- metis_tac[] >>
  Cases_on`ts`>> fs[tsaconv_def,LET_THM] >>
  metis_tac[INTER_IDEMPOT,INTER_ASSOC])
val fresh_ts_def = new_specification("fresh_ts_def",["fresh_ts"],fresh_ts_exists)

(* capture-avoiding substitution on type schemes and environments *)

val tssubst_def = Define`
  tssubst s (tvs,t) (tvs2,t2) ⇔
    ∃t'.
      tvs2 ⊆ tyvars t2 ∧
      tsaconv (tvs,t) (tvs2,t') ∧
      DISJOINT (BIGUNION (IMAGE tyvars (FRANGE (DRESTRICT s (tyvars t' DIFF tvs2))))) tvs2 ∧
      t2 = tysubst (DRESTRICT s (tyvars t' DIFF tvs2)) t'`

val tssubst_tysubst = store_thm("tssubst_tysubst",
  ``tssubst s ({},t) ({},tysubst s t)``,
  simp[tssubst_def] >>
  qexists_tac`t` >> simp[] >>
  match_mp_tac tysubst_frees >>
  simp[FLOOKUP_DRESTRICT])

val tssubst_FINITE = store_thm("tssubst_FINITE",
  ``FINITE (FST ts) ∧ tssubst s ts ts' ⇒ FINITE (FST ts')``,
  Cases_on`ts`>>Cases_on`ts'`>>simp[tssubst_def] >>
  metis_tac[FINITE_tyvars,SUBSET_FINITE])

val tysubst_tssubst = store_thm("tysubst_tssubst",
  ``FINITE tvs ∧
    FDOM s ⊆ tvs ∧
    tssubst s' (tvs,t) (tvs',t')
    ⇒
    ∃s''. FDOM s'' ⊆ tvs' ∧
          tysubst s' (tysubst s t) = tysubst s'' t'``,
  rw[tssubst_def,PULL_EXISTS] >>
  fs[tsaconv_def,LET_THM] >>
  imp_res_tac raconv_imp_tysubst >> rfs[] >> res_tac >>
  BasicProvers.VAR_EQ_TAC >> pop_assum kall_tac >>
  Q.PAT_ABBREV_TAC`tvs1 = tyvars (tysubst X Y)` >>
  `tvs1 = IMAGE f (tvs ∩ tyvars t) ∪ (tyvars t DIFF tvs)` by (
    simp[Abbr`tvs1`,tyvars_tysubst,Once EXTENSION,PULL_EXISTS,FLOOKUP_FUN_FMAP] >>
    metis_tac[] ) >>
  BasicProvers.VAR_EQ_TAC >>
  pop_assum kall_tac >>
  qexists_tac`(tysubst s' o_f s ⊌ s' ⊌ FUN_FMAP Tvar tvs) f_o_f FUN_FMAP (LINV f (tvs ∩ tyvars t)) tvs'` >>
  `FINITE tvs'` by metis_tac[SUBSET_FINITE,FINITE_tyvars] >>
  conj_tac >- ( simp[f_o_f_DEF,FUN_FMAP_DEF] ) >>
  simp[tysubst_tysubst] >>
  match_mp_tac tysubst_frees_gen >>
  gen_tac >> strip_tac >>
  simp[FLOOKUP_FUNION,FLOOKUP_o_f,FLOOKUP_FUN_FMAP,FLOOKUP_f_o_f,FLOOKUP_DRESTRICT] >>
  IF_CASES_TAC >> simp[FLOOKUP_FUNION,FLOOKUP_o_f,FLOOKUP_f_o_f,FLOOKUP_FUN_FMAP,FLOOKUP_DRESTRICT] >- (
    `f x ∈ tvs'` by fs[BIJ_DEF,INJ_DEF] >> fs[] >>
    `LINV f (tvs ∩ tyvars t) (f x) = x` by metis_tac[LINV_DEF,BIJ_DEF,IN_INTER] >>
    simp[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    BasicProvers.CASE_TAC >> simp[] ) >>
  `FLOOKUP s x = NONE` by (
    fs[FLOOKUP_DEF,SUBSET_DEF,GSYM SUBSET_INTER_ABSORPTION] >>
    metis_tac[] ) >>
  simp[] >>
  `x ∉ tvs'` by (
    imp_res_tac raconv_tyvars_eq >>
    fs[EXTENSION] >>
    metis_tac[] ) >>
  simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  CONV_TAC(LAND_CONV(REWR_CONV(GSYM tysubst_nil))) >>
  match_mp_tac tysubst_frees_gen >>
  simp[FLOOKUP_FUNION,FLOOKUP_FUN_FMAP,FLOOKUP_f_o_f,FLOOKUP_o_f] >>
  rw[] >>
  fs[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS,IN_DISJOINT] >>
  metis_tac[])

val tssubst_frees = store_thm("tssubst_frees",
  ``FINITE (FST ts) ∧
    (∀x. x ∈ tyvars (SND ts) DIFF (FST ts) ⇒
         FLOOKUP s1 x = FLOOKUP s2 x) ∧
    tssubst s1 ts ts' ⇒
    tssubst s2 ts ts'``,
  map_every Cases_on[`ts`,`ts'`] >>
  rw[tssubst_def,PULL_EXISTS] >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  imp_res_tac tsaconv_tyvars_eq >> fs[EXTENSION] >>
  conj_tac >- (
    fs[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS] >>
    metis_tac[] ) >>
  match_mp_tac tysubst_frees >>
  simp[FLOOKUP_DRESTRICT])

val tssubst_exists = store_thm("tssubst_exists",
  ``∀s ts. FINITE (FST ts) ⇒ ∃ts'. tssubst s ts ts'``,
  rw[EXISTS_PROD] >>
  `∃tvs t. ts = (tvs,t)` by metis_tac[PAIR] >>
  rw[tssubst_def,PULL_EXISTS] >>
  qabbrev_tac`a = BIGUNION (IMAGE tyvars (FRANGE s))` >>
  qspecl_then[`a`,`tvs,t`]mp_tac fresh_ts_def >>
  discharge_hyps >- ( simp[PULL_EXISTS,Abbr`a`] ) >>
  strip_tac >>
  `∃tvs' t'. fresh_ts a (tvs,t) = (tvs',t')` by metis_tac[PAIR] >> fs[] >>
  rw[Once CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >>
  simp[IN_FRANGE_FLOOKUP,tyvars_tysubst,PULL_EXISTS,FLOOKUP_DRESTRICT,FDOM_DRESTRICT] >>
  fs[SUBSET_DEF,IN_DISJOINT,Abbr`a`,PULL_EXISTS,IN_FRANGE_FLOOKUP] >>
  metis_tac[])

val tenv_subst_def = Define`
  tenv_subst s tenv tenv' ⇔
    MAP FST tenv = MAP FST tenv' ∧
    LIST_REL (tssubst s) (MAP SND tenv) (MAP SND tenv')`

val tenv_subst_cons = store_thm("tenv_subst_cons",
  ``tenv_subst s tenv tenv' ∧
    tssubst s ts ts'
    ⇒ tenv_subst s ((x,ts)::tenv) ((x,ts')::tenv')``,
  rw[tenv_subst_def])

val tenv_subst_exists = store_thm("tenv_subst_exists",
  ``EVERY (FINITE o FST o SND) tenv ⇒
    ∃tenv'. tenv_subst s tenv tenv'``,
  rw[tenv_subst_def] >>
  simp[exists_list_GENLIST] >>
  qexists_tac`LENGTH tenv` >>
  qexists_tac`λn. FST(EL n tenv), @ts'. tssubst s (SND (EL n tenv)) ts'` >>
  simp[LIST_EQ_REWRITE,EL_MAP,EVERY2_MAP] >>
  simp[LIST_REL_EL_EQN] >> rw[] >>
  SELECT_ELIM_TAC >> simp[] >>
  fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  metis_tac[tssubst_exists])

val tyvars_tssubst_eq = store_thm("tyvars_tssubst_eq",
  ``tssubst s ts (bvs,b) ⇒ FINITE (FST ts) ⇒
    tyvars b DIFF bvs =
      (tyvars (SND ts) DIFF (FST ts ∪ FDOM s)) ∪
      BIGUNION (IMAGE tyvars (FRANGE (DRESTRICT s (tyvars (SND ts) DIFF (FST ts)))))``,
  `∃tvs t. ts = (tvs,t)` by metis_tac[PAIR] >>
  simp[tssubst_def,PULL_EXISTS] >> rw[] >>
  simp[Once EXTENSION,PULL_EXISTS,tyvars_tysubst,FLOOKUP_DRESTRICT,FDOM_DRESTRICT,IN_FRANGE_FLOOKUP] >>
  imp_res_tac tsaconv_tyvars_eq >> fs[] >>
  fs[tyvars_tysubst,SUBSET_DEF,PULL_EXISTS,FDOM_DRESTRICT,FLOOKUP_DRESTRICT,EXTENSION,IN_FRANGE_FLOOKUP,IN_DISJOINT] >>
  metis_tac[] )

val tenv_vars_tenv_subst_eq = store_thm("tenv_vars_tenv_subst_eq",
  ``EVERY (FINITE o FST o SND) tenv ⇒
    tenv_subst s tenv tenv' ⇒
    tenv_vars tenv' =
    (tenv_vars tenv DIFF FDOM s) ∪
      BIGUNION (IMAGE tyvars (FRANGE (DRESTRICT s (tenv_vars tenv))))``,
  qid_spec_tac`tenv'` >>
  Induct_on`tenv` >- simp[tenv_subst_def,tenv_vars_def,DRESTRICT_IS_FEMPTY] >>
  simp[FORALL_PROD] >>
  qx_genl_tac[`x`,`tvs`,`t`] >>
  fs[tenv_subst_def] >>
  Cases>>simp[]>>
  PairCases_on`h`>>simp[] >> rw[] >> fs[] >>
  first_x_assum(qspec_then`t'`mp_tac) >>
  rw[tenv_vars_cons] >>
  imp_res_tac tyvars_tssubst_eq >>
  simp[] >>
  pop_assum kall_tac >>
  fs[Once EXTENSION,PULL_EXISTS] >>
  fs[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS] >>
  `∀k v. FLOOKUP s k = SOME v ⇒ k ∈ FDOM s` by simp[FLOOKUP_DEF] >>
  metis_tac[])

val tssubst_id = store_thm("tssubst_id",
  ``FST ts ⊆ tyvars (SND ts) ∧
    DISJOINT (FDOM s) (tyvars (SND ts) DIFF (FST ts))
    ⇒ tssubst s ts ts``,
  Cases_on`ts`>>simp[tssubst_def] >> rw[] >>
  qexists_tac`r` >> rw[] >- (
    fs[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,IN_DISJOINT] >>
    fs[FLOOKUP_DEF] >> metis_tac[] ) >>
  `DRESTRICT s (tyvars r DIFF q) = FEMPTY` by (
    simp[FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_DRESTRICT] >>
    fs[IN_DISJOINT,FLOOKUP_DEF] >>
    metis_tac[] ) >>
  rw[])

val tenv_subst_id = store_thm("tenv_subst_id",
  ``EVERY (λ(tvs,t). tvs ⊆ tyvars t) (MAP SND tenv) ∧
    DISJOINT (FDOM s) (tenv_vars tenv)
    ⇒
    tenv_subst s tenv tenv``,
  Induct_on`tenv`>-simp[tenv_subst_def] >>
  Cases >> rw[] >> fs[] >>
  match_mp_tac tenv_subst_cons >>
  Cases_on`r` >> fs[tenv_vars_cons] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    fs[IN_DISJOINT,SUBSET_DEF] >>
    metis_tac[] ) >>
  match_mp_tac tssubst_id >>
  fs[IN_DISJOINT] >>
  metis_tac[])

(* lemmas about type environment and its relationship to value environment *)

val type_env_EVERY_SUBSET = prove(
  ``type_env rt et env tenv ⇒
    EVERY (λ(tvs,t). tvs ⊆ tyvars t) (MAP SND tenv)``,
  qid_spec_tac`tenv`>>
  Induct_on`env`>> simp[type_env_clauses] >>
  simp[PULL_EXISTS] >> rw[])

val type_env_EVERY_FINITE = prove(
  ``type_env rt et env tenv ⇒
    EVERY (FINITE o FST o SND) tenv``,
  rw[] >>
  imp_res_tac type_env_EVERY_SUBSET >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
  metis_tac[FINITE_tyvars,SUBSET_FINITE])

val type_env_ALOOKUP_tenv_SOME = prove(
  ``∀env tenv. type_env rt et env tenv ⇒
      ∀x tvs t.
      ALOOKUP tenv x = SOME (tvs,t) ⇒
      ∃v. ALOOKUP env x = SOME v ∧
          ∀s. FDOM s ⊆ tvs ⇒
              type_v rt et v (tysubst s t)``,
  Induct >> simp[type_env_clauses] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  PairCases_on`h`>>simp[] >>
  rw[] >> rw[] >> fs[] >>
  metis_tac[])

val type_env_ALOOKUP_env_SOME = prove(
  ``∀env tenv. type_env rt et env tenv ⇒
      ∀x v.
      ALOOKUP env x = SOME v ⇒
      ∃tvs t. ALOOKUP tenv x = SOME (tvs,t) ∧
          ∀s. FDOM s ⊆ tvs ⇒
              type_v rt et v (tysubst s t)``,
  Induct >> simp[type_env_clauses] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  PairCases_on`h`>>simp[] >>
  rw[] >> rw[] >> fs[] >>
  metis_tac[])

(* substitution lemma: typing rules respect substitution *)

val tysubst_Tfn = SIMP_CONV(srw_ss())[]``tysubst s (Tfn t1 t2)``
val tysubst_Texn = SIMP_CONV(srw_ss())[]``tysubst s (Texn t1)``

Theorem type_e_subst:
  ∀tenv e t.
    type_e tenv e t ⇒
    EVERY (FINITE o FST o SND) tenv ⇒
    ∀s tenv'. tenv_subst s tenv tenv' ⇒
              type_e tenv' e (tysubst s t)
Proof
  ho_match_mp_tac type_e_ind >>
  rpt conj_tac >>
  (* most cases *)
  TRY (
    simp[type_e_clauses] >> rw[] >> fs[] >>
    PROVE_TAC[tenv_subst_cons,tssubst_tysubst,tysubst_Tfn,tysubst_Texn]) >>
  (* var *)
  TRY (
    simp[type_e_clauses] >> rw[] >>
    fs[tenv_subst_def] >>
    imp_res_tac ALOOKUP_MAP_FST_EQ_MAP_SND_REL >>
    fs[] >> rw[] >> fs[] >> rw[] >>
    `∃tvs' t'. y2 = (tvs',t')` by metis_tac[PAIR] >>
    simp[] >>
    `FINITE tvs` by (
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,FORALL_PROD] >>
      metis_tac[] ) >>
    metis_tac[tysubst_tssubst] ) >>
  (* let value *)
  TRY  (
    qx_genl_tac[`e1`,`e2`,`t1`,`t2`] >>
    simp[type_e_clauses] >> rw[] >> fs[] >>
    qabbrev_tac`s1 = DRESTRICT s (tenv_vars tenv)` >>
    qabbrev_tac`a = BIGUNION (IMAGE tyvars (FRANGE s1)) ∪ tenv_vars tenv` >>
    qspecl_then[`a`,`tyvars t1 DIFF tenv_vars tenv,t1`]mp_tac fresh_ts_def >>
    discharge_hyps >- (
      simp[Abbr`a`,PULL_EXISTS] ) >>
    Q.PAT_ABBREV_TAC`tvs = tyvars t1 DIFF _` >>
    `∃tvs' t'. fresh_ts a (tvs,t1) = (tvs',t')` by metis_tac[PAIR] >>
    simp[] >> strip_tac >>
    `FINITE tvs` by simp[Abbr`tvs`] >>
    imp_res_tac tsaconv_imp_tysubst >> rfs[] >>
    qmatch_assum_rename_tac`FDOM r = _` >>
    qexists_tac`tysubst (s1 ⊌ r) t1` >>
    conj_tac >- (
      first_x_assum match_mp_tac >>
      fs[tenv_subst_def] >>
      match_mp_tac EVERY2_MEM_MONO >>
      qexists_tac`tssubst s` >>
      imp_res_tac LIST_REL_LENGTH >> fs[] >>
      simp[ZIP_MAP,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
      rw[] >>
      match_mp_tac (GEN_ALL tssubst_frees) >> simp[] >>
      simp[RIGHT_EXISTS_AND_THM] >>
      conj_tac >- (
        rfs[MEM_ZIP,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
        metis_tac[FST,SND] ) >>
      simp[Once CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[FLOOKUP_FUNION] >> rw[] >>
      simp[Abbr`s1`,FLOOKUP_DRESTRICT] >>
      IF_CASES_TAC >> simp[] >- (
        BasicProvers.CASE_TAC >>
        simp[FLOOKUP_DEF,Abbr`tvs`] ) >>
      imp_res_tac MEM_ZIP_MEM_MAP >> rfs[] >>
      fs[tenv_vars_def,FORALL_PROD,PULL_EXISTS] >>
      metis_tac[]) >>
    `tvs' ⊆ tyvars (tysubst (s1 ⊌ r) t1)` by (
      BasicProvers.VAR_EQ_TAC >>
      fs[tyvars_tysubst,SUBSET_DEF,PULL_EXISTS,Abbr`s1`,FDOM_DRESTRICT,FLOOKUP_DRESTRICT,FLOOKUP_FUNION] >>
      qx_gen_tac`z` >> strip_tac >>
      fs[IN_DISJOINT,Abbr`a`,PULL_EXISTS,IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,Abbr`tvs`] >>
      first_x_assum(qspec_then`z`mp_tac) >> simp[] >>
      imp_res_tac tsaconv_tyvars_eq >>
      fs[EXTENSION,PULL_EXISTS,tyvars_tysubst] >>
      strip_tac >- metis_tac[] >>
      disj2_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      IF_CASES_TAC >> simp[] >>
      fs[FLOOKUP_DEF] >>
      metis_tac[] ) >>
    `tssubst s (tvs,t1) (tvs',tysubst (s1 ⊌ r) t1)` by (
      simp[tssubst_def,PULL_EXISTS] >>
      qexists_tac`t'` >> simp[] >>
      conj_tac >- (
        BasicProvers.VAR_EQ_TAC >>
        imp_res_tac tsaconv_tyvars_eq >>
        simp[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS] >>
        fs[IN_DISJOINT,Abbr`a`,PULL_EXISTS,Abbr`s1`,IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT] >> rw[] >>
        first_x_assum match_mp_tac >>
        qexists_tac`k` >> simp[] >>
        fs[EXTENSION,Abbr`tvs`] >>
        metis_tac[] ) >>
      BasicProvers.VAR_EQ_TAC >>
      simp[tysubst_tysubst] >>
      match_mp_tac tysubst_frees >>
      simp[FLOOKUP_FUNION,FLOOKUP_DRESTRICT,FLOOKUP_o_f] >>
      qx_gen_tac`z` >> strip_tac >>
      simp[Abbr`s1`,FLOOKUP_DRESTRICT] >>
      IF_CASES_TAC >- (
        `FLOOKUP r z = NONE` by (
          simp[FLOOKUP_DEF,Abbr`tvs`] ) >>
        simp[] >>
        BasicProvers.CASE_TAC >> simp[] >>
        simp[tyvars_tysubst,PULL_EXISTS,Abbr`tvs`] >>
        fs[Abbr`a`,IN_DISJOINT,PULL_EXISTS,IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT] >>
        metis_tac[] ) >>
      simp[] >>
      BasicProvers.CASE_TAC >- (
        IF_CASES_TAC >> simp[] >>
        imp_res_tac tsaconv_tyvars_eq >>
        fs[Abbr`tvs`] >>
        fs[EXTENSION] >>
        metis_tac[] ) >>
      CONV_TAC(LAND_CONV(REWR_CONV(GSYM tysubst_nil))) >>
      match_mp_tac tysubst_frees >>
      simp[FLOOKUP_DRESTRICT] >>
      imp_res_tac tsaconv_tyvars_eq >>
      fs[Abbr`tvs`] >>
      qmatch_assum_rename_tac`FLOOKUP r z = SOME u` >>
      `u ∈ FRANGE r` by (simp[IN_FRANGE_FLOOKUP]>>metis_tac[])>>
      rfs[] ) >>
    first_x_assum match_mp_tac >>
    match_mp_tac tenv_subst_cons >>
    simp[] >>
    BasicProvers.VAR_EQ_TAC >>
    `tyvars (tysubst (s1 ⊌ r) t1) DIFF tenv_vars tenv' = tvs'` suffices_by simp[] >>
    simp[SET_EQ_SUBSET] >>
    conj_tac >- (
      imp_res_tac tsaconv_tyvars_eq >>
      pop_assum mp_tac >>
      qpat_assum`DISJOINT a tvs'`mp_tac >>
      simp[tyvars_tysubst,SUBSET_DEF,PULL_EXISTS,FLOOKUP_FUNION,Abbr`s1`,FLOOKUP_DRESTRICT,FDOM_DRESTRICT] >>
      simp[Abbr`a`,IN_DISJOINT,EXTENSION,IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS,Abbr`tvs`] >>
      rw[] >>
      pop_assum mp_tac >>
      imp_res_tac tenv_vars_tenv_subst_eq >>
      simp[PULL_EXISTS] >>
      simp[IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT,PULL_EXISTS] >>
      pop_assum kall_tac >>
      pop_assum mp_tac >>
      IF_CASES_TAC >> simp[] >- (
        qmatch_assum_rename_tac`y ∈ tenv_vars tenv` >>
        `FLOOKUP r y = NONE` by (
          simp[FLOOKUP_DEF] ) >>
        BasicProvers.CASE_TAC >> simp[] >>
        strip_tac >> BasicProvers.VAR_EQ_TAC >>
        metis_tac[] ) >>
      qmatch_assum_rename_tac`y ∉ tenv_vars tenv` >>
      strip_tac >>
      `u ∈ FRANGE r` by (
        simp[IN_FRANGE_FLOOKUP] >>
        metis_tac[] ) >>
      pop_assum mp_tac >> simp[PULL_EXISTS] >>
      gen_tac >> strip_tac >> fs[] ) >>
    fs[SUBSET_DEF] >>
    imp_res_tac tenv_vars_tenv_subst_eq >>
    spose_not_then strip_assume_tac >>
    pop_assum mp_tac >> simp[] >>
    fs[IN_DISJOINT,Abbr`a`,PULL_EXISTS,IN_FRANGE_FLOOKUP,Abbr`s1`,FLOOKUP_DRESTRICT] >>
    metis_tac[] )
QED

(*
We prove type soundness by induction on the semantics. This works because both
the typing relation and the semantics are syntax-directed. We establish that
well-typed expressions do not fail, if they terminate with a value then the
value has the same type as the original expression, and if they terminate with
an exception, the exception's parameter matches the type of the exception.
*)

Theorem type_soundness:
  ∀env s e tenv rt et t r s'.
    type_e tenv e t ⇒
    LIST_REL (type_v rt et) s.refs rt ⇒
    type_env rt et env tenv ⇒
    LENGTH et = s.next_exn ⇒
    sem env s e = (r,s') ⇒
    ∃rt' et'.
      LIST_REL (type_v (rt++rt') (et++et')) s'.refs (rt++rt') ∧
      type_env (rt++rt') (et++et') env tenv ∧
      LENGTH (et++et') = s'.next_exn ∧
      case r of
      | Rfail => F
      | Rval v => type_v (rt++rt') (et++et') v t
      | Rraise n v =>
          n < LENGTH (et++et') ∧
          type_v (rt++rt') (et++et') v (EL n (et++et'))
      | _ => T
Proof
  ho_match_mp_tac sem_ind >>
  (* Lit *)
  conj_tac
  >- (simp[sem_def,type_v_clauses,type_e_clauses,LENGTH_NIL] >>
      metis_tac[APPEND_NIL]) >>
  (* Var *)
  conj_tac >- (
    rw[sem_def,type_e_clauses] >>
    every_case_tac >> fs[] >> rw[] >>
    imp_res_tac type_env_ALOOKUP_tenv_SOME >>
    imp_res_tac type_env_ALOOKUP_env_SOME >> fs[LENGTH_NIL] >>
    metis_tac[APPEND_NIL] ) >>
  (* App *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
    simp[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gs[] >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rval (Litv _), _)’]
    >- (first_x_assum drule_all >> simp[type_v_clauses]) >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rfail, _)’]
    >- metis_tac[] >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rval (Loc _), _)’]
    >- (first_x_assum drule_all >> simp[type_v_clauses]) >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rtimeout, _)’]
    >- metis_tac[] >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rval (Exn _), _)’]
    >- (first_x_assum drule_all >> simp[type_v_clauses]) >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rraise _ _, _)’]
    >- metis_tac[] >~
    [‘type_e _ f_e (Tfn dty _)’, ‘type_e _ a_e dty’,
     ‘sem _ _ a_e = (Rraise _ _, _)’]
    >- (first_x_assum
        (qpat_assum ‘type_e _ f_e _’ o
         mp_then (Pos hd)
           (drule_then $ drule_then $ drule_then strip_assume_tac)) >>
        first_x_assum (drule_then drule) >> simp[] >> strip_tac >>
        gs [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
        first_assum $ irule_at Any >> gs[]) >~
    [‘type_e _ f_e (Tfn dty _)’, ‘type_e _ a_e dty’,
     ‘sem _ _ a_e = (Rfail, _)’]
    >- (first_x_assum $ drule_all_then strip_assume_tac >>
        first_x_assum $ drule >> simp[] >> first_assum $ irule_at Any >>
        simp[]) >~
    [‘type_e _ f_e (Tfn dty _)’, ‘type_e _ a_e dty’,
     ‘sem _ _ a_e = (Rtimeout, _)’]
    >- (first_x_assum $ drule_all_then strip_assume_tac >>
        first_x_assum (drule_then drule) >> simp[] >> strip_tac >>
        gs [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
        first_assum $ irule_at Any >> gs[]) >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rval (Clos _ _ _), _)’]
    >- (first_x_assum
          (qpat_assum ‘type_e _ f_e _’ o mp_then (Pos hd) drule_all) >>
        simp[type_v_clauses] >> rpt strip_tac >>
        rename [‘type_e _ f_e (Tfn dty _)’, ‘type_e _ a_e dty’] >>
        first_x_assum $ drule_then drule >> simp[] >> strip_tac >>
        first_x_assum drule >> disch_then drule >>
        simp[type_env_clauses, FDOM_EQ_EMPTY, type_v_clauses] >> impl_tac
        >- metis_tac[type_v_extend] >>
        simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", PULL_EXISTS] >>
        rpt strip_tac >> first_assum $ irule_at Any >>
        gs[] >>
        rpt (qpat_x_assum ‘_ = _.next_exn’ (assume_tac o SYM)) >> gs[] >>
        metis_tac[type_v_extend]) >~
    [‘type_e _ f_e (Tfn _ _)’, ‘sem _ _ f_e = (Rval (Closrec _ _ _ _), _)’]
    >- (first_x_assum
          (qpat_assum ‘type_e _ f_e _’ o mp_then (Pos hd) drule_all) >>
        simp[type_v_clauses] >> rpt strip_tac >>
        rename [‘type_e _ f_e (Tfn dty _)’, ‘type_e _ a_e dty’] >>
        first_x_assum $ drule_then drule >> simp[] >> strip_tac >>
        first_x_assum drule >> disch_then drule >>
        simp[type_env_clauses, FDOM_EQ_EMPTY, type_v_clauses] >> impl_tac
        >- metis_tac[type_v_extend] >>
        simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", PULL_EXISTS] >>
        rpt strip_tac >> first_assum $ irule_at Any >>
        gs[] >>
        rpt (qpat_x_assum ‘_ = _.next_exn’ (assume_tac o SYM)) >> gs[] >>
        metis_tac[type_v_extend]) >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    first_x_assum $ drule_then drule >> simp[] >> strip_tac >>
    gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >> first_assum $ irule_at Any >>
    gs[]) >>
  (* Let *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
    ntac 2 (BasicProvers.CASE_TAC >> fs[]) >> rw[] >>
    first_x_assum(fn th => last_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[] >> strip_tac >>
    first_x_assum(fn th => last_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[type_env_clauses,FDOM_EQ_EMPTY] >>
    TRY(discharge_hyps >- (
      rw[] >>
      qmatch_assum_rename_tac`FDOM ss ⊆ _` >>
      `tenv_subst ss tenv tenv` by (
        match_mp_tac tenv_subst_id >>
        conj_tac >- metis_tac[type_env_EVERY_SUBSET] >>
        fs[SUBSET_DEF,IN_DISJOINT] >>
        metis_tac[] ) >>
      `type_e tenv e (tysubst ss t1)` by (
        match_mp_tac (MP_CANON type_e_subst) >>
        metis_tac[type_env_EVERY_FINITE] ) >>
      Cases_on`e`>>fs[sem_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>
      rw[]>>fs[type_v_clauses,LENGTH_NIL]>>rw[]>>fs[]>>
      fs[type_e_clauses] >- (
        imp_res_tac type_env_ALOOKUP_tenv_SOME >>
        fs[] >> rw[] ) >>
      metis_tac[])) >>
    strip_tac >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[]) >>
  (* Fun *)
  conj_tac >- (
    simp[type_e_clauses,sem_def,type_v_clauses] >>
    rw[LENGTH_NIL] >> metis_tac[APPEND_NIL] ) >>
  (* Funrec *)
  conj_tac >- (
    simp[type_e_clauses,sem_def,type_v_clauses] >>
    rw[LENGTH_NIL] >> metis_tac[APPEND_NIL]) >>
  (* Ref *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
    ntac 2 (BasicProvers.CASE_TAC >> fs[]) >> rw[] >>
    first_x_assum(fn th => last_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[] >> strip_tac >>
    qexists_tac`rt'++[t']` >>
    qexists_tac`et'` >>
    conj_tac >- (
      ONCE_REWRITE_TAC[APPEND_ASSOC] >>
      match_mp_tac rich_listTheory.EVERY2_APPEND_suff >>
      simp[] >>
      reverse conj_tac >- metis_tac[type_v_extend,APPEND_NIL] >>
      match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
      metis_tac[type_v_extend,APPEND_NIL] ) >>
    imp_res_tac LIST_REL_LENGTH >>
    simp[rich_listTheory.EL_APPEND2,type_v_clauses] >>
    metis_tac[type_v_extend,APPEND_NIL]) >>
  (* Deref *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
    simp[AllCaseEqs(), PULL_EXISTS] >> rw[] >> first_x_assum drule >>
    simp[type_v_clauses] >> rpt (first_assum $ irule_at Any) >> simp[]
    >- (disch_then drule_all >> strip_tac >> rpt (first_assum $ irule_at Any) >>
        fs[LIST_REL_EL_EQN]) >>
    rw[] >> gs[LIST_REL_EL_EQN]) >>
  (* Assign *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
    simp[AllCaseEqs(), PULL_EXISTS] >> rw[] >>
    first_x_assum drule_all >> simp[type_v_clauses] >> strip_tac >>
    first_x_assum (drule_then drule) >> rpt strip_tac >~
    [‘sem env s0 e1 = (Rval (Locn n), s1)’,
     ‘sem env s1 e2 = (Rval v, s2)’]
    >- (pop_assum $ drule_then drule >> simp[] >> strip_tac >>
        gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
        first_assum $ irule_at Any >> simp[] >>
        gs[LIST_REL_EL_EQN, EL_LUPDATE] >> rw[] >>
        gs[EL_APPEND_EQN]) >~
    [‘¬(n < LENGTH s2.refs)’]
    >- (simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
        first_x_assum drule >> simp[] >> rpt strip_tac >>
        simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
        gs[LIST_REL_EL_EQN]) >~
    [‘sem env s1 e2 = (Rraise _ _, s2)’]
    >- (pop_assum $ drule_then drule >> simp[] >> strip_tac >>
        gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
        first_assum $ irule_at Any >> simp[]) >~
    [‘sem env s1 e2 = (Rfail, s2)’]
    >- (simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
        first_x_assum drule >> simp[] >> rpt strip_tac >>
        simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
        gs[LIST_REL_EL_EQN]) >>
    pop_assum $ drule_then drule >> simp[] >> strip_tac >>
    gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
    first_assum $ irule_at Any >> simp[]) >>
  (* Letexn *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >>
    first_x_assum(fn th => last_assum(mp_tac o MATCH_MP th)) >>
    disch_then(qspecl_then[`rt`,`et++[t1]`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
      metis_tac[type_v_extend,APPEND_NIL] ) >>
    discharge_hyps >- (
      simp[type_env_clauses,FDOM_EQ_EMPTY,type_v_clauses,rich_listTheory.EL_APPEND2] >>
      metis_tac[type_v_extend,APPEND_NIL] ) >>
    strip_tac >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[type_env_clauses] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[]) >>
  (* Raise *)
  conj_tac >- (
    rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
    simp[AllCaseEqs(), PULL_EXISTS] >> rw[] >>
    first_x_assum drule_all >> simp[type_v_clauses] >> strip_tac >>
    first_x_assum $ drule_then drule >>
    simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
    first_x_assum $ drule_then drule >> simp[] >>
    strip_tac >>
    gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
    first_assum $ irule_at Any >> simp[] >>
    rpt (qpat_x_assum ‘_ = _.next_exn’ (assume_tac o SYM)) >>
    gs[EL_APPEND_EQN]) >>
  (* Handle *)
  rw[type_e_clauses,sem_def] >> pop_assum mp_tac >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rw[] >>
  first_x_assum drule_all >> simp[type_v_clauses] >> rw[] >>
  gvs[METIS_PROVE[]“x = a.next_exn ⇔ a.next_exn = x”] >>
  first_x_assum drule >> simp[]
  >- (disch_then $ drule_then drule >> simp[] >> strip_tac >>
      first_x_assum $ drule_then $ drule_then drule >> simp[] >>
      strip_tac >> simp[] >> gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      first_assum $ irule_at Any >> gs[])
  >- (rename [‘sem env s1 hfn = (Rval (Clos env' bv bod), s2)’] >>
      simp[type_v_clauses] >> disch_then $ drule_then drule >> simp[] >>
      strip_tac >> first_x_assum $ drule_then $ drule_then drule >> simp[] >>
      strip_tac >> first_x_assum $ drule_then drule >>
      simp[type_env_clauses, FDOM_EQ_EMPTY] >> impl_tac
      >- (simp[type_v_extend] >> gs[EL_APPEND_EQN]) >>
      strip_tac >> CASE_TAC >> gs[] >>
      gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      rpt (first_assum $ irule_at Any) >> gs[type_v_extend])
  >- (rename [‘sem env s1 hfn = (Rval (Closrec env' bf bv bod), s2)’] >>
      simp[type_v_clauses] >> disch_then $ drule_then drule >> simp[] >>
      strip_tac >> first_x_assum $ drule_then $ drule_then drule >> simp[] >>
      strip_tac >> first_x_assum $ drule_then drule >>
      simp[type_env_clauses, FDOM_EQ_EMPTY] >> impl_tac
      >- (simp[type_v_extend, type_v_clauses] >> gs[EL_APPEND_EQN] >> rw[] >>
          metis_tac[type_v_extend]) >>
      strip_tac >> CASE_TAC >> gs[] >>
      gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      rpt (first_assum $ irule_at Any) >> gs[type_v_extend])
  >- (disch_then $ drule_then drule >> simp[] >> strip_tac >>
      first_x_assum $ drule_then $ drule_then drule >> simp[] >>
      strip_tac >> gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      rpt (first_assum $ irule_at Any) >> gs[type_v_extend])
  >- (disch_then $ drule_then drule >> simp[] >> strip_tac >>
      first_x_assum $ drule_then $ drule_then drule >> simp[] >>
      strip_tac >> gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      rpt (first_assum $ irule_at Any) >> gs[type_v_extend])
  >- (simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
      first_x_assum $ drule_then drule >> simp[] >>
      simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
      first_x_assum $ drule_then drule >> simp[])
  >- (disch_then $ drule_then drule >> simp[] >> strip_tac >>
      first_x_assum $ drule_then $ drule_then drule >> simp[] >>
      strip_tac >> gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      rpt (first_assum $ irule_at Any) >> gs[type_v_extend])
  >- (simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
      first_x_assum $ drule_then drule >>
      simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
      rename [‘type_v _ _ fv (Tfn _ _)’] >> Cases_on ‘fv’ >> gs[type_v_clauses])
  >- (disch_then $ drule_then drule >> simp[] >> strip_tac >>
      gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
      rpt (first_assum $ irule_at Any) >> gs[type_v_extend])
  >- (simp[DECIDE “~p ∨ q ⇔ p ⇒ q”] >> rpt strip_tac >>
      first_x_assum $ drule_then drule >> simp[]) >>
  disch_then $ drule_then drule >> simp[] >> strip_tac >>
  gs[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >>
  rpt (first_assum $ irule_at Any) >> gs[type_v_extend]
QED

(*
"Type soundness" on the un-clocked relational semantics, for comparison.
*)

val eval_strongind = theorem"eval_strongind";

val eval_type_soundness = Q.store_thm("eval_type_soundness",
  `∀env s e res. eval env s e res ⇒
     ∀tenv t rt et r s'.
       type_e tenv e t ∧
       LIST_REL (type_v rt et) s.refs rt ∧
       type_env rt et env tenv ∧
       LENGTH et = s.next_exn ∧
       res = (r,s')
       ⇒
       ∃rt' et'.
         LIST_REL (type_v (rt++rt') (et++et')) s'.refs (rt++rt') ∧
         type_env (rt++rt') (et++et') env tenv ∧
         LENGTH (et++et') = s'.next_exn ∧
         case r of
         | Rval v => type_v (rt ++ rt') (et++et') v t
         | Rraise n v' =>
             n < LENGTH (et++et') ∧
             type_v (rt++rt') (et++et') v' (EL n (et++et'))
         | _ => F`,
  ho_match_mp_tac eval_strongind >>
  (* Lit *)
  conj_tac >- ( simp[sem_def,type_v_clauses,type_e_clauses,LENGTH_NIL] >> metis_tac[APPEND_NIL]) >>
  (* Var *)
  conj_tac >- (
    rw[] >>
    simp[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac type_env_ALOOKUP_tenv_SOME >> fs[] ) >>
  conj_tac >- (
    simp[type_e_clauses] >>
    rw[] >>
    imp_res_tac type_env_ALOOKUP_tenv_SOME >> fs[] >>
    simp[LENGTH_NIL] >>
    qexists_tac`[]`>>rw[]) >>
  (* App *)
  conj_tac >- (
    rw[Once type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v1`>>fs[type_v_clauses]>>rw[]>>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
    (discharge_hyps >- (
       simp[type_env_clauses,type_v_clauses,FDOM_EQ_EMPTY] >>
       metis_tac[type_v_extend] )) >> rw[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    qexists_tac`rt'++rt''++rt'''` >>
    qexists_tac`et'++et''++et'''` >>
    simp[] >>
    metis_tac[type_v_extend]) >>
  conj_tac >- (
    rw[Once type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v1`>>fs[type_v_clauses]) >>
  conj_tac >- (
    rw[Once type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    first_x_assum(qspecl_then[`rt'++rt''`,`et'++et''`]mp_tac) >>
    simp[] >> BasicProvers.CASE_TAC >> fs[] >> simp[] ) >>
  conj_tac >- (
    rw[Once type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[] ) >>
  (* Let *)
  conj_tac >- (
    rw[Once type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[GSYM AND_IMP_INTRO,type_env_clauses,FDOM_EQ_EMPTY] >>
    TRY( discharge_hyps >- (
      rw[] >>
      qmatch_assum_rename_tac`FDOM ss ⊆ _` >>
      `tenv_subst ss tenv tenv` by (
        match_mp_tac tenv_subst_id >>
        conj_tac >- metis_tac[type_env_EVERY_SUBSET] >>
        fs[SUBSET_DEF,IN_DISJOINT] >>
        metis_tac[] ) >>
      `type_e tenv e (tysubst ss t1)` by (
        match_mp_tac (MP_CANON type_e_subst) >>
        metis_tac[type_env_EVERY_FINITE] ) >>
      last_x_assum mp_tac >>
      Cases_on`e`>>simp[Once eval_cases]>>fs[]>>rw[]>>
      fs[type_v_clauses,LENGTH_NIL]>>rw[]>>fs[]>>
      fs[type_e_clauses] >- (
        imp_res_tac type_env_ALOOKUP_tenv_SOME >>
        fs[] >> rw[] ) >>
      metis_tac[])) >>
    strip_tac >>
    BasicProvers.CASE_TAC >> fs[] >>
    qexists_tac`rt'++rt''` >>
    qexists_tac`et'++et''` >>
    simp[]) >>
  conj_tac >- (
    rw[Once type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[] ) >>
  (* Fun *)
  conj_tac >- (
    simp[type_e_clauses,type_v_clauses] >>
    rw[LENGTH_NIL] >> metis_tac[APPEND_NIL]) >>
  (* Funrec *)
  conj_tac >- (
    simp[type_e_clauses,type_v_clauses] >>
    rw[LENGTH_NIL] >> metis_tac[APPEND_NIL]) >>
  (* Ref *)
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    qexists_tac`rt'++[t']` >>
    qexists_tac`et'` >>
    conj_tac >- (
      ONCE_REWRITE_TAC[APPEND_ASSOC] >>
      match_mp_tac rich_listTheory.EVERY2_APPEND_suff >>
      simp[] >>
      reverse conj_tac >- metis_tac[type_v_extend,APPEND_NIL] >>
      match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
      metis_tac[type_v_extend,APPEND_NIL] ) >>
    imp_res_tac LIST_REL_LENGTH >>
    simp[type_v_clauses] >>
    simp[rich_listTheory.EL_APPEND2] >>
    metis_tac[type_v_extend,APPEND_NIL] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[] ) >>
  (* Deref *)
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[type_v_clauses] >>
    fs[LIST_REL_EL_EQN]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    fs[type_v_clauses] >>
    fs[LIST_REL_EL_EQN] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v`>>fs[type_v_clauses]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[] ) >>
  (* Assign *)
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    rw[type_v_clauses] >>
    Cases_on`n < LENGTH rt` >- (
      qexists_tac`rt' ++ rt''` >>
      qexists_tac`et' ++ et''` >> simp[] >>
      fs[type_v_clauses] >>
      fs[LIST_REL_EL_EQN,EL_LUPDATE] >> rw[] >>
      fs[rich_listTheory.EL_APPEND1] ) >>
    qexists_tac`LUPDATE t' (n-LENGTH rt) (rt' ++ rt'')` >>
    qexists_tac`et'++et''` >>
    imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[] >>
    reverse conj_tac >- metis_tac[type_v_extend,APPEND_ASSOC] >>
    simp[GSYM rich_listTheory.LUPDATE_APPEND2] >>
    match_mp_tac EVERY2_LUPDATE_same >>
    fs[type_v_clauses] >>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
    simp[rich_listTheory.LUPDATE_APPEND1,rich_listTheory.LUPDATE_APPEND2] >>
    simp[LUPDATE_ID] >> rw[] >>
    qpat_assum`type_v A X Y Z`mp_tac >>
    fs[arithmeticTheory.NOT_LESS] >>
    fs[rich_listTheory.EL_APPEND2]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v1`>>fs[type_v_clauses] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac LIST_REL_LENGTH >> fs[] >>
    DECIDE_TAC ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    qexists_tac`rt' ++ rt''` >>
    qexists_tac`et' ++ et''` >> simp[]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  (* Letexn *)
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(qspecl_then[`rt`,`et++[t1]`]mp_tac) >>
    simp[AND_IMP_INTRO] >>
    discharge_hyps >- (
      simp[type_env_clauses,FDOM_EQ_EMPTY,type_v_clauses,rich_listTheory.EL_APPEND2] >>
      conj_tac >- (
        match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
        metis_tac[type_v_extend,APPEND_NIL] ) >>
      metis_tac[type_v_extend,APPEND_NIL] ) >>
    strip_tac >>
    qexists_tac`rt'` >>
    qexists_tac`[t1]++et'` >>
    simp[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    fs[type_env_clauses] >> simp[] ) >>
  (* Raise *)
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    fs[type_v_clauses] >>
    qexists_tac`rt'++rt''`>>
    qexists_tac`et'++et''`>>
    rw[] >> simp[rich_listTheory.EL_APPEND1]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v1`>>fs[type_v_clauses] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    qexists_tac`rt'++rt''`>>
    qexists_tac`et'++et''`>>
    Cases_on`r`>>fs[] >> simp[] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    last_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`r`>>fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  (* Handle *)
  conj_tac >- (
    rw[type_e_clauses] >>
    qpat_assum`type_e tenv e' _`(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v2`>>fs[]>>rw[]>>fs[type_v_clauses]>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
    (discharge_hyps >- (
       fs[type_env_clauses,FDOM_EQ_EMPTY] >>
       rev_full_simp_tac(srw_ss()++ARITH_ss)[rich_listTheory.EL_APPEND1] >>
       fs[type_v_clauses] >>
       metis_tac[type_v_extend] )) >>
    strip_tac >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    Cases_on`r`>>fs[] >> simp[] >>
    metis_tac[type_v_extend]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    qpat_assum`type_e tenv e' _`(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    qpat_assum`type_e tenv e' _`(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    qpat_assum`type_e tenv e _`(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    spose_not_then strip_assume_tac >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v2`>>fs[type_v_clauses] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    qpat_assum`type_e tenv e _`(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    BasicProvers.CASE_TAC >> fs[] >> simp[] ) >>
  conj_tac >- (
    rw[type_e_clauses] >>
    spose_not_then strip_assume_tac >>
    qpat_assum`type_e tenv e _`(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
    Cases_on`v1`>>fs[type_v_clauses] ) >>
  rw[type_e_clauses] >>
  first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th o REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> rw[] >>
  full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  BasicProvers.CASE_TAC >> fs[] >> simp[])

val _ = export_theory()
