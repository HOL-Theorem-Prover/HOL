structure relation_extraLib :> relation_extraLib =
struct

open HolKernel Parse boolLib bossLib
open relationSyntax relation_extraSyntax

val ERR = mk_HOL_ERR "relation_extraLib"

(* ------------------------------------------------------------------------- *)

local
  open relationTheory pred_setTheory relation_extraTheory
  val rel_rwts =
    simpLib.rewrites
      [RSUBSET, RUNION, RINTER, SUBSET_applied, RMINUS, RCROSS, semi, diag_def,
       FUN_EQ_THM, SPECIFICATION, RRANGE]
in
  fun rel_ss() = srw_ss()++rel_rwts
  fun xrw thms = rw_tac (rel_ss()) thms
  fun xsimp thms = asm_simp_tac (rel_ss()) thms
  fun xfs thms = full_simp_tac (rel_ss()) thms
end

local
  open relation_extraTheory
  fun rprove q =
    Feedback.trace ("notify type variable guesses",0)
       (Feedback.trace ("metis", 0) Q.prove)
          (q, xsimp [delift, restr_rel] \\ metis_tac []) |> GEN_ALL
  val thms = List.map rprove
    [`r2 RSUBSET r3 ==> (r1 RUNION r2) RSUBSET (r1 RUNION r3)`,
     `r1 RSUBSET r3 ==> (r1 RUNION r2) RSUBSET (r3 RUNION r2)`,
     `r2 RSUBSET r3 ==> (r1 RINTER r2) RSUBSET (r1 RINTER r3)`,
     `r1 RSUBSET r3 ==> (r1 RINTER r2) RSUBSET (r3 RINTER r2)`,
     `r2 RSUBSET r3 ==> (r1 ⨾ r2) RSUBSET (r1 ⨾ r3)`,
     `r1 RSUBSET r3 ==> (r1 ⨾ r2) RSUBSET (r3 ⨾ r2)`,
     `r1 RSUBSET r3 ==> (r1 RMINUS r2) RSUBSET (r3 RMINUS r2)`,
     `r1 RSUBSET r2 ==> (delift eqv r1) RSUBSET (delift eqv r2)`,
     `r1 RSUBSET r2 ==> (restr_rel cond r1) RSUBSET (restr_rel cond r2)`]
in
  val full_rsubset_trans = rprove
     `!r3 r4 r1 r2.
         r1 RSUBSET r3 /\ r4 RSUBSET r2 /\ r3 RSUBSET r4 ==> r1 RSUBSET r2`
  val acyclic_mon' = ONCE_REWRITE_RULE [boolTheory.CONJ_COMM] acyclic_mon
  val rsubset_refl = rprove `r RSUBSET r`
  val rsubset_tac =
    FIRST (List.map match_mp_tac (thms @ [inclusion_t_t, inclusion_rt_rt]))
end

local
  fun rewrite1 (args as (mtch, res)) cnt tm =
    case mtch tm of
      SOME (s1, s2) =>
         if cnt < 0 then
           (cnt, Term.subst s1 (Term.inst s2 res))
         else if 0 < cnt then
           (cnt - 1, Term.subst s1 (Term.inst s2 res))
         else
           (cnt, tm)
    | NONE =>
      (case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("relation$RUNION", [r1, r2]) =>
           let
             val (cnt1, tm1) = rewrite1 args cnt r1
             val (cnt2, tm2) = rewrite1 args cnt1 r2
           in
             (cnt2, relationSyntax.mk_runion (tm1, tm2))
           end
       | SOME ("relation$RINTER", [r1, r2]) =>
           let
             val (cnt1, tm1) = rewrite1 args cnt r1
             val (cnt2, tm2) = rewrite1 args cnt1 r2
           in
             (cnt2, relationSyntax.mk_rinter (tm1, tm2))
           end
       | SOME ("relation_extra$seq", [r1, r2]) =>
           let
             val (cnt1, tm1) = rewrite1 args cnt r1
             val (cnt2, tm2) = rewrite1 args cnt1 r2
           in
             (cnt2, relation_extraSyntax.mk_seq (tm1, tm2))
           end
       | SOME ("relation_extra$RMINUS", [r1, r2]) =>
           let
             val (cnt1, tm1) = rewrite1 args cnt r1
             val (cnt2, tm2) = rewrite1 args cnt1 r2
           in
             (cnt2, relation_extraSyntax.mk_rminus (tm1, tm2))
           end
       | SOME ("relation$TC", [r1]) =>
           (I ## relationSyntax.mk_tc) (rewrite1 args cnt r1)
       | SOME ("relation$RTC", [r1]) =>
           (I ## relationSyntax.mk_rtc) (rewrite1 args cnt r1)
       | SOME ("relation_extra$delift", [eqv, r1]) =>
           (I ## (fn t => relation_extraSyntax.mk_delift (eqv, t)))
              (rewrite1 args cnt r1)
       | SOME ("relation_extra$restr_rel", [cond, r1]) =>
           (I ## (fn t => relation_extraSyntax.mk_restr_rel (cond, t)))
              (rewrite1 args cnt r1)
       | _ => (cnt, tm))
  fun tac th =
    rpt (rsubset_tac \\ simp_tac bool_ss [th, rsubset_refl])
    \\ simp_tac bool_ss [th, rsubset_refl]
    \\ POP_ASSUM_LIST kall_tac
    \\ mp_tac th
    \\ xsimp []
    \\ metis_tac []
in
  fun gen_rewrite (l_cnt, r_cnt) th (gl as (asl,w)) =
    let
      val (l, r) = relationSyntax.dest_rsubset (Thm.concl th)
      val avoids = HOLset.fromList Term.compare (Term.free_vars w)
      val mtchl = Lib.total (Term.match_terml [] avoids l)
      val mtchr = Lib.total (Term.match_terml [] avoids r)
      val left = #2 o rewrite1 (mtchl, r) l_cnt
      val right = #2 o rewrite1 (mtchr, l) r_cnt
    in
      case Lib.total boolSyntax.dest_strip_comb w of
        SOME ("relation_extra$acyclic", [wl]) =>
          Q.ISPEC_THEN `^(left wl)` match_mp_tac acyclic_mon'
          \\ strip_tac
          >- tac th
      | SOME ("relation$RSUBSET", [wl, wr]) =>
          Q.ISPECL_THEN [`^(left wl)`, `^(right wr)`]
            match_mp_tac full_rsubset_trans
          \\ ntac 2 (strip_tac >- tac th)
      | _ => raise ERR "rewrite" "no rewrite"
    end gl
  val rewrite = gen_rewrite (~1, ~1)
  val left_rewrite = gen_rewrite (~1, 0)
  val right_rewrite = gen_rewrite (0, ~1)
end

(* ------------------------------------------------------------------------- *)

end
