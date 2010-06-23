(* ========================================================================= *)
(*                                                                           *)
(*     Inductive Definitions (John Harrison)                                 *)
(*                                                                           *)
(* ========================================================================= *)

structure InductiveDefinition :> InductiveDefinition =
struct

open HolKernel boolLib liteLib refuteLib AC Ho_Rewrite;

(* Fix the grammar used by this file *)
structure Parse =
struct
  open Parse
  val (Type,Term) = Parse.parse_from_grammars pairTheory.pair_grammars
  fun -- q x = Term q
  fun == q x = Type q
end
open Parse

(*---------------------------------------------------------------------------
    Variants. We re-define the kernel "variant" function here because
    of a subtle difference between Hol98 variant and Hol88/light
    variant functions: the former only looks at strings, while the
    latter look at variables. For example

       variant [`x:bool`] `x:'a`

    yields x' in Hol98, but `x` in the latter (I think). The following
    version of variant also does not vary away from constants with the
    same name, maybe it should.
 ---------------------------------------------------------------------------*)

local fun prime v = let val (n,ty) = dest_var v in mk_var(n^"'",ty) end
in
fun vary V v = if mem v V then vary V (prime v) else v
end

(* ------------------------------------------------------------------------- *)
(* Produces a sequence of variants, considering previous inventions.         *)
(* ------------------------------------------------------------------------- *)

fun variants av [] = []
  | variants av (h::t) =
      let val vh = vary av h
      in vh::variants (vh::av) t
      end;

(* ------------------------------------------------------------------------- *)
(* Apply a destructor as many times as elements in list.                     *)
(* ------------------------------------------------------------------------- *)

fun nsplit dest clist x =
  if null clist then ([],x) else
      let val (l,r) = dest x
          val (ll,y) = nsplit dest (tl clist) r
      in (l::ll,y)
      end;;

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)

val strip_ncomb =
    let fun strip(n,tm,acc) =
        if n < 1 then (tm,acc) else
            let val (l,r) = dest_comb tm
            in strip(n - 1,l,r::acc)
            end
    in fn n => fn tm => strip(n,tm,[])
    end;;

(* ------------------------------------------------------------------------- *)
(* Share out list according to pattern in list-of-lists.                     *)
(* ------------------------------------------------------------------------- *)

fun shareout [] _ = []
  | shareout (h::t) all =
      let val (l,r) = split_after (length h) all
      in l::shareout t r
      end;

(* ------------------------------------------------------------------------- *)
(* Produce a set of reasonably readable arguments, using variants if needed. *)
(* ------------------------------------------------------------------------- *)

val make_args =
  let fun margs n avoid tys =
    if null tys then [] else
        let val v = variant avoid (mk_var("a"^(int_to_string n),hd tys))
        in v::margs (n + 1) (v::avoid) (tl tys)
        end
  in margs 0 end;;

(* ------------------------------------------------------------------------- *)
(* Grabs conclusion of rule, whether or not it has an antecedant.            *)
(* ------------------------------------------------------------------------- *)

fun getconcl tm =
    let val bod = repeat (snd o dest_forall) tm
    in snd(dest_imp bod) handle HOL_ERR _ => bod
    end;;

(* ------------------------------------------------------------------------- *)
(* Likewise, but quantify afterwards.                                        *)
(* ------------------------------------------------------------------------- *)

fun HALF_BETA_EXPAND args th = GENL args (RIGHT_BETAS args th);;

(* ------------------------------------------------------------------------- *)
(* Converse of SIMPLE_DISJ_CASES, i.e. P \/ Q |- R  =>  P |- R, Q |- R       *)
(* ------------------------------------------------------------------------- *)

fun SIMPLE_DISJ_PAIR th =
    let val (l,r) = dest_disj(hd(hyp th))
    in (PROVE_HYP (DISJ1 (ASSUME l) r) th,PROVE_HYP (DISJ2 l (ASSUME r)) th)
    end;;

(* ------------------------------------------------------------------------- *)
(* Iterated FORALL_IMP_CONV: (!x1..xn. P[xs] ==> Q) => (?x1..xn. P[xs]) ==> Q*)
(* ------------------------------------------------------------------------- *)

val lhand = rand o rator;;

fun FORALL_IMPS_CONV tm =
  let val (avs,bod) = strip_forall tm
      val th1 = DISCH tm (UNDISCH(SPEC_ALL(ASSUME tm)))
      val th2 = itlist SIMPLE_CHOOSE avs th1
      val tm2 = hd(hyp th2)
      val th3 = DISCH tm2 (UNDISCH th2)
      val th4 = ASSUME (concl th3)
      val ant = lhand bod
      val th5 = itlist SIMPLE_EXISTS avs (ASSUME ant)
      val th6 = GENL avs (DISCH ant (MP th4 th5))
  in IMP_ANTISYM_RULE (DISCH_ALL th3) (DISCH_ALL th6) end;;

(* ------------------------------------------------------------------------- *)
(*    (!x1..xn. P1[xs] ==> Q[xs]) /\ ... /\ (!x1..xn. Pm[xs] ==> Q[xs])      *)
(* => (!x1..xn. P1[xs] \/ ... \/ Pm[xs] ==> Q[xs])                           *)
(* ------------------------------------------------------------------------- *)

fun AND_IMPS_CONV tm =
  let val ths = CONJUNCTS(ASSUME tm)
      val avs = fst(strip_forall(concl(hd ths)))
      val thl = map (DISCH tm o UNDISCH o SPEC_ALL) ths
      val th1 = end_itlist SIMPLE_DISJ_CASES thl
      val tm1 = hd(hyp th1)
      val th2 = GENL avs (DISCH tm1 (UNDISCH th1))
      val tm2 = concl th2
      val th3 = DISCH tm2 (UNDISCH (SPEC_ALL (ASSUME tm2)))
      val (thts,tht) =  nsplit SIMPLE_DISJ_PAIR (tl ths) th3
      fun proc_fn th =
          let val t = hd(hyp th) in GENL avs (DISCH t (UNDISCH th))
          end
      val th4 = itlist (CONJ o proc_fn) thts (proc_fn tht)
  in IMP_ANTISYM_RULE (DISCH_ALL th2) (DISCH_ALL th4) end;;

(* ------------------------------------------------------------------------- *)
(*      A, x = t |- P[x]                                                     *)
(*     ------------------ EXISTS_EQUATION                                    *)
(*        A |- ?x. P[x]                                                      *)
(* ------------------------------------------------------------------------- *)

val EXISTS_EQUATION = Prim_rec.EXISTS_EQUATION

(* ========================================================================= *)
(* Part 1: The main part of the inductive definitions package.               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Translates a single clause to have variable arguments, simplifying.       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  [JRH] Removed "Fail" constructor from handle trap.                       *)
(* ------------------------------------------------------------------------- *)

local fun getequs(avs,[]) = []
        | getequs(avs,(h as {redex=r,residue})::t) =
            if mem r avs
            then h::getequs(avs,filter (fn{redex,...} => not(r=redex)) t)
            else getequs(avs,t)
      fun calculate_simp_sequence avs plis =
        let val oks = getequs(avs,plis)
        in (oks,subtract plis oks)
        end
      fun mk_eq_of_bind{redex,residue} = mk_eq(residue,redex)
in
fun canonicalize_clause clause carg =
 let val (avs,bimp)  = strip_forall clause
     val (ant,con)   = dest_imp bimp handle HOL_ERR _ => (T,bimp)
     val (rel,xargs) = strip_comb con
     val plis        = map2 (curry op |->) xargs carg
     val (yes,no)    = calculate_simp_sequence avs plis
     val nvs         = filter (not o C mem (map #redex yes)) avs
     val eth =
        if is_imp bimp then
          let val atm = itlist (curry mk_conj o mk_eq_of_bind) (yes@no) ant
              val (ths,tth) = nsplit CONJ_PAIR plis (ASSUME atm)
              val thl = map(fn t => first(fn th => lhs(concl th) = t)ths) carg
              val th0 = MP (SPECL avs (ASSUME clause)) tth
              val th1 = rev_itlist (C (curry MK_COMB)) thl (REFL rel)
              val th2 = EQ_MP (SYM th1) th0
              val th3 = INST yes (DISCH atm th2)
              val tm4 = funpow (length yes) rand (lhand(concl th3))
              val th4 = itlist (CONJ o REFL o #residue) yes (ASSUME tm4)
              val th5 = GENL carg (GENL nvs (DISCH tm4 (MP th3 th4)))
              val th6 = SPECL nvs (SPECL (map #redex plis) (ASSUME(concl th5)))
              val th7 = itlist (CONJ o REFL o #redex) no (ASSUME ant)
              val th8 = GENL avs (DISCH ant (MP th6 th7))
          in IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
          end
        else
          let val atm = list_mk_conj(map mk_eq_of_bind (yes@no))
              val ths = CONJUNCTS (ASSUME atm)
              val thl = map(fn t => first(fn th => lhs(concl th) = t) ths) carg
              val th0 = SPECL avs (ASSUME clause)
              val th1 = rev_itlist (C (curry MK_COMB)) thl (REFL rel)
              val th2 = EQ_MP (SYM th1) th0
              val th3 = INST yes (DISCH atm th2)
              val tm4 = funpow (length yes) rand (lhand(concl th3))
              val th4 = itlist (CONJ o REFL o #residue) yes (ASSUME tm4)
              val th5 = GENL carg (GENL nvs (DISCH tm4 (MP th3 th4)))
              val th6 = SPECL nvs (SPECL (map #redex plis) (ASSUME(concl th5)))
              val th7 = end_itlist CONJ (map (REFL o #redex) no)
              val th8 = GENL avs (MP th6 th7)
          in IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
          end
     val ftm = funpow (length carg) (body o rand) (rand(concl eth))
 in TRANS eth (itlist MK_FORALL carg (FORALL_IMPS_CONV ftm))
 end
 handle e => raise (wrap_exn "InductiveDefinition" "canonicalize_clause" e)
end;

(* ------------------------------------------------------------------------- *)
(* Canonicalizes the set of clauses, disjoining compatible antecedants.      *)
(* ------------------------------------------------------------------------- *)

local fun assoc2 x (h1::t1,h2::t2) = if x = h1 then h2 else assoc2 x (t1,t2)
        | assoc2 x _ = fail()
in
fun canonicalize_clauses clauses =
  let val concls = map getconcl clauses
      val uncs = map strip_comb concls
      val rels = itlist (insert o fst) uncs []
      val xargs = map (C assoc uncs) rels
      val closed = list_mk_conj clauses
      val avoids = all_vars closed
      val flargs = make_args avoids (map type_of (end_foldr (op @) xargs))
      val vargs = shareout xargs flargs
      val cargs = map (C assoc2 (rels,vargs) o fst) uncs
      val cthms = map2 canonicalize_clause clauses cargs
      val pclauses = map (rand o concl) cthms
      fun collectclauses tm =
          mapfilter (fn t => if fst t = tm then snd t else fail())
          (zip (map fst uncs) pclauses)
      val clausell = map collectclauses rels
      val cclausel = map list_mk_conj clausell
      val cclauses = list_mk_conj cclausel
      and oclauses = list_mk_conj pclauses
      val pth = TRANS (end_itlist MK_CONJ cthms)
          (CONJ_ACI(mk_eq(oclauses,cclauses)))
  in TRANS pth (end_itlist MK_CONJ (map AND_IMPS_CONV cclausel))
  end
  handle e => raise (wrap_exn "InductiveDefinition" "canonicalize_clauses" e)
end;


(* ------------------------------------------------------------------------- *)
(* Prove definitions work for non-schematic relations with canonical rules.  *)
(* ------------------------------------------------------------------------- *)

fun derive_canon_inductive_relations pclauses =
    let val closed = list_mk_conj pclauses
        val pclauses = strip_conj closed
        val (vargs,bodies) = split(map strip_forall pclauses)
        val (ants,concs) = split(map dest_imp bodies)
        val rels = map (repeat rator) concs
        val avoids = all_vars closed
        val rels' = variants avoids rels
        val prime_fn = subst (map2 (curry op |->) rels rels' )
        val closed' = prime_fn closed
        fun mk_def arg con =
            mk_eq(repeat rator con,
                  list_mk_abs(arg,list_mk_forall(rels',
                                 mk_imp(closed',prime_fn con))))
        val deftms = map2 mk_def vargs concs
        val defthms = map2 HALF_BETA_EXPAND vargs (map ASSUME deftms)
        fun mk_ind args th =
            let val th1 = fst(EQ_IMP_RULE(SPEC_ALL th))
                val ant = lhand(concl th1)
                val th2 = SPECL rels' (UNDISCH th1)
            in GENL args (DISCH ant (UNDISCH th2))
            end
        val indthms = map2 mk_ind vargs defthms
        val indthmr = end_itlist CONJ indthms
        val indthm = GENL rels' (DISCH closed' indthmr)
        val mconcs = map2 (fn a => fn t =>
          list_mk_forall(a,mk_imp(t,prime_fn t))) vargs ants
        val monotm = mk_imp(concl indthmr,list_mk_conj mconcs)
        val monothm = ASSUME(list_mk_forall(rels,list_mk_forall(rels',monotm)))
        val closthm = ASSUME closed'
        val monothms = CONJUNCTS
            (MP (SPEC_ALL monothm) (MP (SPECL rels' indthm) closthm))
        val closthms = CONJUNCTS closthm
        fun prove_rule mth (cth,dth) =
            let val (avs,bod) = strip_forall(concl mth)
                val th1 = IMP_TRANS (SPECL avs mth) (SPECL avs cth)
                val th2 = GENL rels' (DISCH closed' (UNDISCH th1))
                val th3 = EQ_MP (SYM (SPECL avs dth)) th2
            in GENL avs (DISCH (lhand bod) th3)
            end
        val ruvalhms = map2 prove_rule monothms (zip closthms defthms)
        val ruvalhm = end_itlist CONJ ruvalhms
        val dtms = map2 (curry list_mk_abs) vargs ants
        val double_fn = subst (map2 (curry op |->) rels dtms)
        fun mk_unbetas tm dtm =
            let val (avs,bod) = strip_forall tm
                val (il,r) = dest_comb bod
                val (i,l) = dest_comb il
                val bth = RIGHT_BETAS avs (REFL dtm)
                val munb = AP_THM (AP_TERM i bth) r
                val iunb = AP_TERM (mk_comb(i,double_fn l)) bth
                val junb = AP_TERM (mk_comb(i,r)) bth
                val quantify = itlist MK_FORALL avs
            in (quantify munb,(quantify iunb,quantify junb))
            end
        val unths = map2 mk_unbetas pclauses dtms
        val irthm = EQ_MP (SYM(end_itlist MK_CONJ (map fst unths))) ruvalhm
        val mrthm = MP (SPECL rels (SPECL dtms monothm)) irthm
        val imrth = EQ_MP
          (SYM(end_itlist MK_CONJ (map (fst o snd) unths))) mrthm
        val ifthm = MP (SPECL dtms indthm) imrth
        val fthm = EQ_MP (end_itlist MK_CONJ (map (snd o snd) unths)) ifthm
        fun mk_case th1 th2 =
            let val avs = fst(strip_forall(concl th1))
            in GENL avs (IMP_ANTISYM_RULE (SPEC_ALL th1) (SPEC_ALL th2))
            end
        val casethm = end_itlist CONJ
               (map2 mk_case (CONJUNCTS fthm) (CONJUNCTS ruvalhm))
    in CONJ ruvalhm (CONJ indthm casethm)
    end
    handle e => raise (wrap_exn "InductiveDefinition"
                         "derive_canon_inductive_relations"e);

(* ------------------------------------------------------------------------- *)
(* General case for nonschematic relations; monotonicity & defn hyps.        *)
(* ------------------------------------------------------------------------- *)

fun derive_nonschematic_inductive_relations tm =
  let val clauses   = strip_conj tm
      val canonthm  = canonicalize_clauses clauses
      val canonthm' = SYM canonthm
      val pclosed   = rand(concl canonthm)
      val pclauses  = strip_conj pclosed
      val rawthm    = derive_canon_inductive_relations pclauses
      val (ruvalhm,otherthms) = CONJ_PAIR rawthm
      val (indthm,casethm)    = CONJ_PAIR otherthms
      val ruvalhm' = EQ_MP canonthm' ruvalhm
      and indthm'  = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV canonthm')) indthm
  in CONJ ruvalhm' (CONJ indthm' casethm)
  end
  handle e => raise (wrap_exn "InductiveDefinition"
                       "derive_nonschematic_inductive_relations" e);


(* ========================================================================= *)
(* Part 2: Tactic-integrated tools for proving monotonicity automatically.   *)
(* ========================================================================= *)


(* ----------------------------------------------------------------------
    MONO_ABS_TAC

        ?- (\x. P[x]) x1 .. xn ==> (\y. Q[y]) x1 .. xn
      ==================================================
          ?- P[x1] x2 .. xn ==> Q[x1] x2 .. xn

   ---------------------------------------------------------------------- *)

fun MONO_ABS_TAC (asl,w) =
    let val (ant,con) = dest_imp w
        val vars = snd(strip_comb con)
        val rnum = length vars - 1
        val (hd1,args1) = strip_ncomb rnum ant
        and (hd2,args2) = strip_ncomb rnum con
        val th1 = rev_itlist (C AP_THM) args1 (BETA_CONV hd1)
        and th2 = rev_itlist (C AP_THM) args1 (BETA_CONV hd2)
        val th3 = MK_COMB(AP_TERM boolSyntax.implication th1,th2)
    in CONV_TAC(REWR_CONV th3) (asl,w)
    end;;

(* ----------------------------------------------------------------------
    MONO_UNCURRY_TAC

         ?- UNCURRY f x1 .. xn ==> UNCURRY f' x1 .. xn
      ==================================================
        ?- f y1 y2 .. xn ==> f' y1 y2 .. xn

   ---------------------------------------------------------------------- *)

local
  val U = pairTheory.UNCURRY
in

fun MONO_UNCURRY_TAC (asl, w) = let
  val (ant, con) = dest_imp w
  val vars = snd (strip_comb con)
  val rnum = length vars - 2
  val (hd1, args1) = strip_ncomb rnum ant
  val (hd2, args2) = strip_ncomb rnum con
  val th1 = rev_itlist (C AP_THM) args1 (ISPECL (#2 (strip_comb hd1)) U)
  val th2 = rev_itlist (C AP_THM) args2 (ISPECL (#2 (strip_comb hd2)) U)
  val th3 = MK_COMB(AP_TERM boolSyntax.implication th1, th2)
in
  CONV_TAC (REWR_CONV th3) (asl, w)
end
end (* local *)


(* ------------------------------------------------------------------------- *)
(* Collection, so users can add their own rules.                             *)
(*                                                                           *)
(* As a simple speedup, the tactics are indexed by head operator in the      *)
(* relevant expression. If there isn't a head constant, use the empty string.*)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Simplified version of MATCH_MP_TAC to avoid quantifier troubles.          *)
(* ------------------------------------------------------------------------- *)

fun BACKCHAIN_TAC th =
    let val match_fn = HO_PART_MATCH (snd o dest_imp) th
    in fn (asl,w) =>
        let val th1 = match_fn w
            val (ant,con) = dest_imp(concl th1)
        in ([(asl,ant)],fn [t] => HO_MATCH_MP th1 t)
        end
    end;;

type monoset = (string * thm) list;

(*---------------------------------------------------------------------------
 * MONO_AND = |- (A ==> B) /\ (C ==> D) ==> (A /\ C ==> B /\ D)
 * MONO_OR  = |- (A ==> B) /\ (C ==> D) ==> (A \/ C ==> B \/ D)
 * MONO_IMP = |- (B ==> A) /\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))
 * MONO_NOT = |- (B ==> A) ==> (~A ==> ~B)
 * MONO_ALL = |- (!x. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))
 * MONO_EXISTS = |- (!x. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))
 *---------------------------------------------------------------------------*)


val MONO_EXISTS = prove (
  ``(!x:'a. P x ==> Q x) ==> ($? P ==> $? Q)``,
  DISCH_THEN(MP_TAC o HO_MATCH_MP MONO_EXISTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[])

val MONO_FORALL = prove (
  ``(!x:'a. P x ==> Q x) ==> ($! P ==> $! Q)``,
  DISCH_THEN(MP_TAC o HO_MATCH_MP MONO_ALL) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[])

val MONO_RESFORALL = prove(
  ``(!x:'a. P' x ==> P x) /\ (!x. Q x ==> Q' x) ==>
    (RES_FORALL P Q ==> RES_FORALL P' Q')``,
  REWRITE_TAC [RES_FORALL_THM, IN_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_REWRITE_TAC [])

val MONO_RESEXISTS = prove(
  ``(!x:'a. P x ==> P' x) /\ (!x. Q x ==> Q' x) ==>
    (RES_EXISTS P Q ==> RES_EXISTS P' Q')``,
  REWRITE_TAC [RES_EXISTS_THM, IN_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC ``x:'a`` THEN RES_TAC THEN ASM_REWRITE_TAC [])

val MONO_RTC = prove(
  ``(!x:'a y. R x y ==> R' x y) ==> (RTC R x y ==> RTC R' x y)``,
  STRIP_TAC THEN MATCH_MP_TAC relationTheory.RTC_MONOTONE THEN
  ASM_REWRITE_TAC []);

val MONO_TC = prove(
  ``(!x:'a y. R x y ==> R' x y) ==> (TC R x y ==> TC R' x y)``,
  STRIP_TAC THEN MATCH_MP_TAC relationTheory.TC_MONOTONE THEN
  ASM_REWRITE_TAC []);

val MONO_EQC = prove(
  ``(!x:'a y. R x y ==> R' x y) ==> (EQC R x y ==> EQC R' x y)``,
  STRIP_TAC THEN MATCH_MP_TAC relationTheory.EQC_MONOTONE THEN
  ASM_REWRITE_TAC []);

val MONO_SC = prove(
  ``(!x:'a y. R x y ==> R' x y) ==> (SC R x y ==> SC R' x y)``,
  STRIP_TAC THEN REWRITE_TAC [relationTheory.SC_DEF] THEN STRIP_TAC THEN
  RES_TAC THEN ASM_REWRITE_TAC []);


val bool_monoset =
 [("/\\", MONO_AND),
  ("\\/", MONO_OR),
  ("?",   MONO_EXISTS),
  ("!",   MONO_FORALL),
  ("==>", MONO_IMP),
  ("~",   MONO_NOT),
  ("RES_FORALL", MONO_RESFORALL),
  ("RES_EXISTS", MONO_RESEXISTS),
  ("RTC", MONO_RTC),
  ("TC", MONO_TC),
  ("EQC", MONO_EQC),
  ("SC", MONO_SC),
  ("OPTREL", optionTheory.OPTREL_MONO)]


val IMP_REFL = tautLib.TAUT_PROVE (--`!p. p ==> p`--)

fun APPLY_MONOTAC monoset (asl, w) = let
  val (a,c) = dest_imp w
in
  if aconv a c then ACCEPT_TAC (SPEC a IMP_REFL) (asl,w)
  else let
      val {Thy,Name,...} = dest_thy_const(repeat rator c)
                           handle HOL_ERR _ => {Thy = "", Name = "",
                                                Ty = Type.alpha}
    in
      case (Thy,Name) of
        ("","") => MONO_ABS_TAC (asl, w)
      | ("pair", "UNCURRY") => MONO_UNCURRY_TAC (asl, w)
      | _ => tryfind (fn (k,t) => if k = Name then BACKCHAIN_TAC t (asl,w)
                                  else fail())
                     monoset
    end
end

(* ------------------------------------------------------------------------- *)
(* Tactics to prove monotonicity automatically.                              *)
(* ------------------------------------------------------------------------- *)

fun MONO_STEP_TAC finisher monoset =
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    (APPLY_MONOTAC monoset ORELSE finisher)

fun MONO_TAC monoset = let
  (* first case is for monotonicity proving in making the definition, where
     there will be an assumption of the form
         !vs. P vs ==> P' vs
     to hand.
     The second case (after the ORELSE) is for proving strong induction, where
     there won't be any assumptions, but the goal will have reduced to
         con vs /\ con' vs ==> con vs
  *)
  val finisher = FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE
                 (REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC)
in
  REPEAT (MONO_STEP_TAC finisher monoset)
end

(* =========================================================================*)
(* Part 3: Utility functions to modify the basic theorems in various ways.  *)
(*                                                                          *)
(* There are various fnctions that can be applied to a theorem:             *)
(*                                                                          *)
(* (1) Attempt to prove the monotonicity hypotheses                         *)
(*                                                                          *)
(* (2) Generalize it over schematic variables                               *)
(*                                                                          *)
(* (3) Derive a raw existence assertion                                     *)
(*                                                                          *)
(* (4) Actually make definitions of the inductive relations.                *)
(*                                                                          *)
(* Generally one applies either or both of (1) and (2), then does (4).      *)
(* =========================================================================*)

(* ------------------------------------------------------------------------- *)
(* Attempt to dispose of the non-equational assumption(s) of a theorem.      *)
(* ------------------------------------------------------------------------- *)

fun prove_monotonicity_hyps monoset =
  let val tac = REPEAT GEN_TAC THEN
        DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
        REPEAT CONJ_TAC THEN (MONO_TAC monoset)
        fun prove_mth t = TAC_PROOF(([],t),tac)
  in fn th =>
      let val mths = mapfilter prove_mth (filter (not o is_eq) (hyp th))
      in itlist PROVE_HYP mths th
      end
  end
  handle e => raise (wrap_exn "InductiveDefinition"
                        "prove_monotonicity_hyps" e);

(* ------------------------------------------------------------------------- *)
(* Generalize definitions and theorem over given variables (all the same!)   *)
(* ------------------------------------------------------------------------- *)

fun generalize_schematic_variables vs =
  let fun generalize_def tm th =
      let val (l,r) = dest_eq tm
          val (lname,lty) = dest_var l
          val l' = mk_var(lname,itlist (curry (op -->) o type_of) vs lty)
          val r' = list_mk_abs(vs,r)
          val tm' = mk_eq(l',r')
          val th0 = RIGHT_BETAS vs (ASSUME tm')
          val th1 = INST [l |-> lhs(concl th0)] (DISCH tm th)
      in MP th1 th0
      end
  in fn th =>
    let val (defs,others) = partition is_eq (hyp th)
        val others' =
            map (fn t => let val fvs = free_vars t
                         in SPECL fvs (ASSUME (list_mk_forall(fvs,t)))
                         end)
            others
        val th1 = itlist generalize_def defs th
    in GENL vs (itlist PROVE_HYP others' th1)
    end
  end;

(* ------------------------------------------------------------------------- *)
(* Derive existence.                                                         *)
(* ------------------------------------------------------------------------- *)

fun derive_existence th = itlist EXISTS_EQUATION (filter is_eq (hyp th)) th

(* ------------------------------------------------------------------------- *)
(* Make definitions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun make_definitions stem th = let
  val defs = filter is_eq (hyp th)
  fun mkdef i tm = new_definition(stem ^ Int.toString i ^ !Defn.def_suffix, tm)
  val dths = if length defs = 1 then
               [new_definition(stem ^ !Defn.def_suffix, hd defs)]
             else
               mapi mkdef defs
  val insts = map2 (curry op |->) (map lhs defs) (map (lhs o concl) dths)
in
  rev_itlist (C MP) dths (INST insts (itlist DISCH defs th))
end

(* ------------------------------------------------------------------------- *)
(* "Unschematize" a set of clauses.                                          *)
(* ------------------------------------------------------------------------- *)

val inddef_strict = ref false;
val _ = Feedback.register_btrace ("inddef strict", inddef_strict);

fun indented_term_to_string n tm = let
  val nspaces = String.implode (List.tabulate(n, K #" "))
  fun pper pps tm = let
  in
    PP.add_string pps nspaces;
    Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal)
                  (Parse.pp_term pps)
                  tm
  end
in
  PP.pp_to_string (!Globals.linewidth) pper tm
end


local
  fun pare_comb qvs tm =
      if null (intersect (free_vars tm) qvs)
         andalso all is_var (snd(strip_comb tm))
      then tm
      else pare_comb qvs (rator tm)
  fun schem_head cls =
      let val (avs,bod) = strip_forall cls
      in pare_comb avs (snd(dest_imp bod) handle HOL_ERR _ => bod)
      end
  fun common_prefix0 acc l1 l2 =
      case (l1, l2) of
        ([], _) => acc
      | (_, []) => acc
      | (h1::t1, h2::t2) => if h1 = h2 then common_prefix0 (h1::acc) t1 t2
                            else acc
  fun common_prefix l1 l2 = List.rev (common_prefix0 [] l1 l2)
  fun lcommon_prefix0 acc l =
      case l of
        [] => acc
      | (h::t) => let
          val newprefix = common_prefix acc h
        in
          if null newprefix then []
          else lcommon_prefix0 newprefix t
        end
  fun lcommon_prefix [] = []
    | lcommon_prefix (h::t) = lcommon_prefix0 h t

in
fun unschematize_clauses clauses = let
  val schem = map schem_head clauses
  val schems = mk_set schem
  fun insert_list l s = foldl (fn (t,s) => HOLset.add(s,t)) s l
  val hdops = mk_set (map (#1 o strip_comb) schems)
  val schemv_extent = length (#2 (strip_comb (hd schems)))
  fun is_hdop_instance t = let
    val (f,args) = strip_comb t
  in
    mem f hdops andalso length args = schemv_extent
  end
  val all_instances =
      foldl (fn (t, s) => insert_list (find_terms is_hdop_instance t) s)
            empty_tmset clauses
  fun do_substitution schems = let
    val avoids = all_vars (list_mk_conj clauses)
    fun hack_fn tm = mk_var(fst(dest_var(repeat rator tm)),type_of tm)
    val grels = variants avoids (map hack_fn schems)
    val crels = map2 (curry op |->) schems grels
    val clauses' = map (subst crels) clauses
  in
    (clauses',snd(strip_comb(hd schems)))
  end
in
  if is_var(hd schem) then (clauses,[])
  else if !inddef_strict then
    if not (HOLset.numItems all_instances = 1) then let
        val instlist = HOLset.listItems all_instances
        val t1_s = trace("types", 1) (indented_term_to_string 2) (hd instlist)
        val t2_s =
            trace("types", 1) (indented_term_to_string 2) (hd (tl instlist))
      in
        failwith ("Schematic variable(s) not used consistently - witness\n"^
                  t1_s^"\nand\n"^t2_s)
      end
    else
      do_substitution schems
  else (* liberal definitions *) let
      val prefix_vars = HOLset.foldr (fn (t,l) => #2 (strip_comb t)::l)
                                     [] all_instances
      val prefix = lcommon_prefix prefix_vars
    in
      if null prefix then (clauses, [])
      else let
          val plist = String.concat (Lib.commafy
                                     (map (quote o #1 o dest_var) prefix))
          val _ = HOL_MESG ("Treating "^plist^" as schematic variable"^
                            (if length prefix > 1 then "s" else ""))
        in
          do_substitution (map (fn t => list_mk_comb(t, prefix)) hdops)
        end
    end
 end
end;

(* ========================================================================= *)
(* Part 4: The final user wrapper.                                           *)
(* ========================================================================= *)


fun check_definition schemevars clocs tm = let
  (* check that tm has no extra type variables or free variables other than *)
  (* the heads of clauses *)
  val clauses = strip_conj tm
  fun ind_concl tm = #2 (dest_imp tm) handle HOL_ERR _ => tm
  val relvars =
      HOLset.addList(empty_tmset,
                     map (#1 o strip_comb o ind_concl o #2 o strip_forall)
                         clauses)
  val okvars = foldl (fn (v,s) => HOLset.add(s,v)) relvars schemevars
  val empty_tyset = HOLset.empty Type.compare
  val reltyvars = HOLset.foldl (fn (tm,tyvset) =>
                                   HOLset.addList(tyvset,
                                                  type_vars_in_term tm))
                               empty_tyset relvars
  val reltyvars = List.foldl (fn (tm,tyvset) =>
                                 HOLset.addList(tyvset,
                                                type_vars_in_term tm))
                             reltyvars schemevars

  (* check that there aren't duplicate names in the forall chain *)
  fun check_clause_foralls n c = let
    val (vs, body) = strip_forall c
    val loc = List.nth(clocs, n) handle Subscript => locn.Loc_None
    fun foldthis (v, acc) = let
      val (nm, _) = dest_var v
    in
      if HOLset.member(acc, nm) then
        raise mk_HOL_ERRloc "InductiveDefinition"
                            "check_clause"
                            loc
                            ("Clause #"^Int.toString (n + 1)^
                             " contains duplicate name "^nm^
                             " in outermost universal quantification")
      else HOLset.add(acc, nm)
    end
  in
    ignore (List.foldl foldthis (HOLset.empty String.compare) vs)
  end
  val _ = appi check_clause_foralls clauses


  fun check_tyvars n c = let
    val tyvs = HOLset.addList(empty_tyset, type_vars_in_term c)
  in
    if not (HOLset.isSubset(tyvs, reltyvars)) then let
        val really_free = HOLset.difference(tyvs, reltyvars)
        val free_list0 = HOLset.foldr (fn (v,sl) => dest_vartype v :: sl)
                                      [] really_free
        val free_list = Lib.commafy free_list0
        val tmstring = trace ("types", 1) (indented_term_to_string 2) c
        val loc = List.nth (clocs, n) handle Subscript => locn.Loc_None
      in
        raise mk_HOL_ERRloc
                  "InductiveDefinition" "check_clause" loc
                  (String.concat ("Clause #" :: Int.toString (n + 1)::
                                  ":\n" :: tmstring ::
                                  "\ncontains free type variable"^
                                  (if length free_list > 1 then "s" else "")^
                                  ": " :: free_list))
      end
    else
      ()
  end
  val _ = appi check_tyvars clauses



  (* here, generalise on the extra free variables if we're not being strict *)
  fun check_clause n c = let
    val fvs = FVL [c] empty_tmset
  in
    if not (HOLset.isSubset(fvs, okvars)) then let
        val really_free = HOLset.difference(fvs, okvars)
        val free_list0 =
            HOLset.foldr (fn (v,sl) => Lib.quote (#1 (dest_var v)) :: sl)
                         [] really_free
        val free_list = Lib.commafy free_list0
        val loc = List.nth(clocs, n) handle Subscript => locn.Loc_None
      in
        if !inddef_strict then let
            val tmstring = trace ("types", 1) (indented_term_to_string 2) c
          in
            raise mk_HOL_ERRloc
                      "InductiveDefinition"
                      "check_clause"
                      loc
                      (String.concat ("Clause #" :: Int.toString n ::
                                      ",\n" :: tmstring ::
                                      "\ncontains free variables: " ::
                                      free_list))
          end
        else
          (HOL_MESG ("Generalising variable" ^
                     (if length free_list > 1 then "s " else " ")^
                     String.concat free_list ^
                     " in clause #"^Int.toString n ^
                     (if loc = locn.Loc_None then ""
                      else " ("^locn.toShortString loc^")"));
           list_mk_forall (HOLset.listItems really_free, c))
      end
    else c
  end
in
  list_mk_conj (mapi check_clause clauses)
end



fun prove_nonschematic_inductive_relations_exist monoset tm = let
  val th0 = derive_nonschematic_inductive_relations tm
  val th1 = prove_monotonicity_hyps monoset th0
in
  derive_existence th1
end
  handle e =>
         raise (wrap_exn "InductiveDefinition"
                         "prove_nonschematic_inductive_relations_exist" e);

(* ------------------------------------------------------------------------- *)
(* The schematic case.                                                       *)
(*                                                                           *)
(* All relations in a given call must have the same schematic args (if they  *)
(* aren't mutually inductive, use separate definitions), which must occur as *)
(* the first arguments to each relation, in the same order(!)                *)
(* ------------------------------------------------------------------------- *)

fun prove_inductive_relations_exist monoset tm =
 let val clauses = strip_conj tm
     val (clauses',fvs) = unschematize_clauses clauses
     val th0 = derive_nonschematic_inductive_relations
                 (check_definition fvs [] (list_mk_conj clauses'))
     val th1 = prove_monotonicity_hyps monoset th0
     val th2 = generalize_schematic_variables fvs th1
 in derive_existence th2
 end
 handle e => raise (wrap_exn "InductiveDefinition"
                             "prove_inductive_relations_exist" e);


fun new_inductive_definition monoset stem (tm,clocs) =
 let val clauses = strip_conj tm
     val (clauses',fvs) = unschematize_clauses clauses
     val th0 = derive_nonschematic_inductive_relations
                 (check_definition fvs clocs (list_mk_conj clauses'))
     val th1 = prove_monotonicity_hyps monoset th0
     val th2 = generalize_schematic_variables fvs th1
     val th3 = make_definitions stem th2
     val avs = fst(strip_forall(concl th3))
     val (r,ic) = CONJ_PAIR(SPECL avs th3)
     val (i,c)  = CONJ_PAIR ic
 in (GENL avs r, GENL avs i, GENL avs c)
 end
 handle e => raise wrap_exn "InductiveDefinition" "new_inductive_definition" e;

end (* InductiveDefinition *)
