
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
open listTheory arithmeticTheory;
val ect = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "imp";

(*

This file defines a funcional big-step semantics for the IMP languages
of Nipkow and Klein's book Concrete Semantics.

http://www.concrete-semantics.org/

*)

val _ = temp_type_abbrev("vname",``:string``);

val _ = Datatype `
  aexp = N int | V vname | Plus aexp aexp`;

val _ = Datatype `
  bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp`;

val _ = Datatype `
  com = SKIP
      | Assign vname aexp
      | Seq com com
      | If bexp com com
      | While bexp com`

val aval_def = Define `
  (aval (N n) s = n) /\
  (aval (V x) s = s x) /\
  (aval (Plus a1 a2) s = aval a1 s + aval a2 s)`;

val bval_def = Define `
  (bval (Bc v) s = v) /\
  (bval (Not b) s = ~bval b s) /\
  (bval (And b1 b2) s = (bval b1 s /\ bval b2 s)) /\
  (bval (Less a1 a2) s = (aval a1 s < aval a2 s))`;

val STOP_def = Define `STOP x = x`;

(* The following function defines the semantics of statement evaluation.
   The clock decreases when entering the body of the While loop.

   NB: the definition mechanism in HOL4 is not smart enough to notice
   that the clock doesn't increase. In order to make the termination
   simple, we insert an extra `if t < t2 then t else t2` in the Seq
   case. In cval_def_with_stop below, we remove this redundant
   if-statement. *)

Definition cval_def:
  (cval SKIP s (t:num) = SOME (s,t)) /\
  (cval (Assign x a) s t = SOME ((x =+ aval a s) s,t)) /\
  (cval (Seq c1 c2) s t =
    case cval c1 s t of
    | NONE => NONE
    | SOME (s2,t2) => cval c2 s2 (if t < t2 then t else t2)) /\
  (cval (If b c1 c2) s t =
    cval (if bval b s then c1 else c2) s t) /\
  (cval (While b c) s t =
    if bval b s then
      if t = 0 then NONE else cval (Seq c (STOP (While b c))) s (t - 1)
    else SOME (s,t))
Termination
  WF_REL_TAC `inv_image (measure I LEX measure com_size)
                            (λ(c,s,t). (t,c))`
  \\ SRW_TAC [] [] \\ DECIDE_TAC
End

val clock_bound = prove(
  ``!c s t s' t'. (cval c s t = SOME (s',t')) ==> t' <= t``,
  recInduct (theorem "cval_ind") \\ rpt strip_tac
  \\ fs [cval_def] \\ ect \\ fs [] \\ decide_tac);

fun term_rewrite tms = let
  fun f tm = ASSUME (list_mk_forall(free_vars tm,tm))
  in rand o concl o QCONV (REWRITE_CONV (map f tms)) end

val r = term_rewrite [``(if t < t2 then t else t2) = t2:num``];

val cval_def_with_stop = store_thm("cval_def_with_stop",
  cval_def |> concl |> r,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once cval_def]
  \\ ect \\ imp_res_tac clock_bound \\ `r = t` by DECIDE_TAC \\ fs []);

Theorem cval_def[allow_rebind] =
        REWRITE_RULE [STOP_def] cval_def_with_stop

(* We also remove the redundant if-statement from the induction theorem. *)

val cval_ind = prove(
  cval_ind |> concl |> r,
  NTAC 2 STRIP_TAC \\ HO_MATCH_MP_TAC (theorem "cval_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [STOP_def]
  \\ RES_TAC \\ imp_res_tac clock_bound
  \\ Cases_on `t < t2` \\ fs []
  \\ `t = t2` by DECIDE_TAC \\ fs []) |> REWRITE_RULE [STOP_def];

Theorem cval_ind[allow_rebind] = cval_ind

Theorem lrg_clk:
    !c s t t' s1 t1. ((t <= t') /\ (cval c s t = SOME (s1, t1))) ==> (?t2.(cval c s t' = SOME (s1, t2)) /\ t1 <= t2)
Proof
  recInduct cval_ind >>
  rw[]
    >>~- ([`(If _ _ _)`], (first_x_assum $ qspecl_then [`t'`, `s1`, `t1`] assume_tac >> rfs[cval_def]))
    >- (qexists `t'` >> fs[cval_def])
    >- (qexists `t'` >> fs[cval_def])
    >- (Cases_on `cval c1 s t` >>
        Cases_on `cval c1 s t'`
            >- fs[cval_def]
            >- fs[cval_def]
            >- (Cases_on `x` >> first_x_assum $ qspecl_then [`t'`, `q`, `r`] assume_tac >> rfs[])
            >- (Cases_on `x` >>
                Cases_on `x'` >>
                first_x_assum $ qspec_then `t'` assume_tac >>
                rfs[] >>
                first_x_assum $ qspecl_then [`r'`, `s1`, `t1`] assume_tac >>
                fs[cval_def]
            )
    )
    >- (Cases_on `t` >>
        Cases_on `bval b s` >>
        fs[Once cval_def]
          >- (first_x_assum $ qspecl_then [`t'-1`, `s1`, `t1`] assume_tac >>
              Cases_on `cval c s n` >>
              gvs[Once cval_def]
          )
    )
QED


(* I think this should immediatly follow from the above theorem *)
(* NOTE this is provable without the above lemma ...though probably reconstructs the lemma in some way*)
Theorem cval_mono:
    !c s t t'. ((t <= t') /\ (cval c s t <> NONE)) ==> (OPTION_MAP FST (cval c s t)) = (OPTION_MAP FST (cval c s t'))
Proof
  rpt strip_tac >>
  Cases_on `cval c s t`
    >- fs[]
    >- (Cases_on `x` >>
        (* drule_then lrg_clk assume_tac *) (* type error?? *)
        qspecl_then [`c`, `s`, `t`, `t'`, `q`, `r`] assume_tac lrg_clk >>
        rfs[]
    )
QED


(* actually this proof might be good to do by contradiction *)
Theorem lrg_clk2:
  !c s t t' s1 t1 t2. ((t1 <= t2) /\ (cval c s t = SOME (s1, t1)) /\ (cval c s t' = SOME (s1, t2))) ==> t <= t'
Proof
  recInduct cval_ind >>
  rw[]
    >- fs[cval_def]
    >- fs[cval_def]
    >- (pop_assum mp_tac >>
        pop_assum mp_tac >>
        simp[cval_def] >>
        Cases_on `cval c1 s t` >>
        Cases_on `cval c1 s t'`
          >- simp[]
          >- simp[]
          >- simp[]
          >- (simp[] >>
              Cases_on `x` >>
              Cases_on `x'` >>
              simp[] >>
              disch_then assume_tac >>
              disch_then assume_tac >>
              first_x_assum irule >>
              last_x_assum $ irule_at Any >>
              rw[] >>
              qexists `t2` >>
              Cases_on `t <= t'`
                >- (qspecl_then [`c1`, `s`, `t`, `t'`] mp_tac cval_mono >>
                    rw[]
                )
                >- (fs[NOT_LESS_EQUAL] >>
                    qspecl_then [`c1`, `s`, `t'`, `t`] mp_tac cval_mono >>
                    rw[] >>
                    simp[]
                )
          )
    )
    >- (pop_assum mp_tac >>
        pop_assum mp_tac >>
        simp[cval_def]
    )
    >- (pop_assum mp_tac >>
        pop_assum mp_tac >>
        simp[cval_def]
    )
    >- (Cases_on `bval b s` >>
        Cases_on `t` >>
        Cases_on `t'`
          >- simp[]
          >- simp[]
          >- fs[Once cval_def]
          >- (fs[] >>
              pop_assum mp_tac >>
              pop_assum mp_tac >>
              pop_assum mp_tac >>
              once_rewrite_tac[cval_def] >>
              simp[] >>
              rw[] >>
              last_x_assum $ qspecl_then [`n'`, `s1`, `t1`, `t2`] assume_tac >>
              rfs[]
          )
          >- simp[]
          >- simp[]
          >- fs[Once cval_def]
          >- fs[Once cval_def]
    )
QED

Theorem arb_resc:
  !c s t s1 t1. cval c s t = SOME (s1, t1) ==> (!k. ?t'. cval c s t' = SOME (s1, k))
Proof
  recInduct cval_ind >>
  rw[]
    >- (qexists `k` >> fs[cval_def])
    >- (qexists `k` >> fs[cval_def])
    >- (fs[cval_def] >>
        Cases_on `cval c1 s t`
          >- fs[]
          >- (fs[] >>
              Cases_on `x` >>
              fs[] >>
              last_x_assum $ qspec_then `k` assume_tac >>
              fs[] >>
              last_x_assum $ qspec_then `t'` assume_tac >>
              fs[] >>
              qexists `t''` >>
              simp[]
          )
    )
    >- gvs[cval_def] (* got lazy doing the rewrites myself *)
    >- gvs[cval_def]
    >- (Cases_on `bval b s` >>
        Cases_on `t`
          >- fs[Once cval_def]
          >- (fs[] >>
              qpat_x_assum `cval _ _ _ = _` mp_tac >>
              once_rewrite_tac[cval_def] >>
              simp[] >>
              disch_then assume_tac >>
              last_x_assum $ qspecl_then [`s1`, `t1`] assume_tac >>
              rfs[] >>
              pop_assum $ qspec_then `k` assume_tac >>
              fs[] >>
              qexists `SUC t'` >>
              simp[]
          )
          >- fs[Once cval_def]
          >- fs[Once cval_def]
    )
QED


val _ = export_theory();
