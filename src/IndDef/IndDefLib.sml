structure IndDefLib :> IndDefLib =
struct

 type term = Term.term
 type fixity = Parse.fixity
 type thm = Thm.thm
 type tactic = Abbrev.tactic
 type thm_tactic = Abbrev.thm_tactic


open refuteLib ; (* ancestor libraries *)
open HolKernel Parse basicHol90Lib liteLib AC Ho_rewrite Ho_resolve Psyntax;

infix |->;
infix THEN THENC

fun WRAP_ERR x = STRUCT_WRAP "Ind_defs" x;

val (Type,Term) = parse_from_grammars combinTheory.combin_grammars
fun -- q x = Term q
fun == q x = Type q

(* ------------------------------------------------------------------------- *)
(* Apply a destructor as many times as elements in list.                     *)
(* ------------------------------------------------------------------------- *)

fun nsplit dest clist x =
  if null clist then ([],x) else
      let val (l,r) = dest x
          val (ll,y) = nsplit dest (tl clist) r
      in (l::ll,y) end;;

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)

val strip_ncomb =
    let fun strip(n,tm,acc) =
        if n < 1 then (tm,acc) else
            let val (l,r) = dest_comb tm
            in strip(n - 1,l,r::acc)
            end
    in fn n => fn tm => strip(n,tm,[]) end;;

(* ------------------------------------------------------------------------- *)
(* Share out list according to pattern in list-of-lists.                     *)
(* ------------------------------------------------------------------------- *)

fun shareout pat all =
  if pat = [] then [] else
      let val (l,r) = split_after (length (hd pat)) all
      in l::(shareout (tl pat) r) end;;

(* ------------------------------------------------------------------------- *)
(* Gets all variables (free and/or bound) in a term.                         *)
(* ------------------------------------------------------------------------- *)

val variables =
  let fun vars(acc,tm) =
    if is_var tm then insert tm acc
    else if is_const tm then acc
    else if is_abs tm then
      let val (v,bod) = dest_abs tm
      in vars(insert v acc,bod)
      end
    else
        let val (l,r) = dest_comb tm
        in vars(vars(acc,l),r)
        end
  in fn tm => vars([],tm) end;;

(* ------------------------------------------------------------------------- *)
(* Produce a set of reasonably readable arguments, using variants if needed. *)
(* ------------------------------------------------------------------------- *)

val make_args =
  let fun margs n avoid tys =
    if null tys then [] else
        let val v = variant avoid (mk_var("a"^(int_to_string n),hd tys))
        in v::(margs (n + 1) (v::avoid) (tl tys))
        end
  in margs 0 end;;

(* ------------------------------------------------------------------------- *)
(* Grabs conclusion of rule, whether or not it has an antecedant.            *)
(* ------------------------------------------------------------------------- *)
fun repeat f pty =
    (repeat f (f pty)
     handle Interrupt => raise Interrupt
          |         _ => pty);


fun getconcl tm =
    let val bod = repeat (snd o dest_forall) tm
    in snd(dest_imp bod) handle Interrupt => raise Interrupt
                              |         _ => bod end;;

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

fun SIMPLE_CHOOSE v th =
  CHOOSE(v,ASSUME (mk_exists(v,hd(hyp th)))) th;

fun SIMPLE_EXISTS v th =
  EXISTS (mk_exists(v,concl th),v) th;

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

fun SIMPLE_DISJ_CASES th1 th2 =
  DISJ_CASES (ASSUME(mk_disj(hd(hyp th1),hd(hyp th2)))) th1 th2;

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

val EXISTS_EQUATION =
    let val pth = prove
     (--`!P t. (!x:'a. (x = t) ==> P x) ==> $? P`--,
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBST1_TAC(SYM (ETA_CONV (--`\x. (P:'a->bool) x`--))) THEN
      EXISTS_TAC (--`t:'a`--) THEN FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC)
    in fn tm => fn th =>
        let val (l,r) = dest_eq tm
            val P = mk_abs(l,concl th)
            val th1 = BETA_CONV(mk_comb(P,l))
            val th2 = ISPECL [P, r] pth
            val th3 = EQ_MP (SYM th1) th
            val th4 = GEN l (DISCH tm th3)
        in MP th2 th4
        end
    end;;

(* ========================================================================= *)
(* Part 1: The main part of the inductive definitions package.               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Translates a single clause to have variable arguments, simplifying.       *)
(* ------------------------------------------------------------------------- *)


infixr -->;
fun a --> b = mk_type("fun",[a,b]);

val MK_FORALL =
    let val aty = mk_vartype "'a"
    in fn v => fn th => AP_TERM (mk_const("!",(type_of v --> bool) --> bool))
(ABS v th)
    end;;

val conj_tm = (--`$/\`--);

(* ------------------------------------------------------------------------- *)
(*  [JRH] Removed "Fail" constructor from handle trap.                       *)
(* ------------------------------------------------------------------------- *)


local fun getequs(avs,plis) =
            if null plis then [] else
                let val h::t = plis
                    val r = redex h
                in if mem r avs then
                    h::(getequs(avs,filter (fn x => not (r = redex x)) t))
                   else
                       getequs(avs,t)
                end
      fun calculate_simp_sequence avs plis =
        let val oks = getequs(avs,plis)
        in (oks,subtract plis oks)
        end
in
fun canonicalize_clause clause carg =
        let val (avs,bimp) = strip_forall clause
            val (ant,con) = dest_imp bimp
              handle Interrupt => raise Interrupt
                   |         _ => ((--`T`--),bimp)
            val (rel,xargs) = strip_comb con
            val plis = map2 (curry op |->) xargs carg
            val (yes,no) = calculate_simp_sequence avs plis
            val nvs = filter (not o C mem (map redex yes)) avs
            val eth =
                if is_imp bimp then
                    let val atm = itlist (curry mk_conj o mk_eq) (yes@no) ant

                    val (ths,tth) = nsplit CONJ_PAIR plis (ASSUME atm)
                    val thl = map
                      (fn t => first (fn th => lhs(concl th) = t) ths) carg
                    val th0 = MP (SPECL avs (ASSUME clause)) tth
                    val th1 = rev_itlist (C (curry MK_COMB)) thl (REFL rel)
                    val th2 = EQ_MP (SYM th1) th0
                    val th3 = INST yes (DISCH atm th2)
                    val tm4 = funpow (length yes) rand (lhand(concl th3))
                    val th4 = itlist (CONJ o REFL o residue) yes (ASSUME tm4)
                    val th5 = GENL carg (GENL nvs (DISCH tm4 (MP th3 th4)))
                    val th6 = SPECL nvs
                      (SPECL (map redex plis) (ASSUME (concl th5)))
                    val th7 = itlist (CONJ o REFL o redex) no (ASSUME ant)
                    val th8 = GENL avs (DISCH ant (MP th6 th7))
                    in IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
                    end
                else
                        let val atm = list_mk_conj(map mk_eq (yes@no))
                        val ths = CONJUNCTS (ASSUME atm)
                        val thl = map
                          (fn t => first (fn th => lhs(concl th) = t) ths) carg
                        val th0 = SPECL avs (ASSUME clause)
                        val th1 = rev_itlist (C (curry MK_COMB)) thl (REFL rel)
                        val th2 = EQ_MP (SYM th1) th0
                        val th3 = INST yes (DISCH atm th2)
                        val tm4 = funpow (length yes) rand (lhand(concl th3))
                        val th4 = itlist (CONJ o REFL o residue) yes
                                         (ASSUME tm4)
                        val th5 = GENL carg (GENL nvs (DISCH tm4 (MP th3 th4)))
                        val th6 = SPECL nvs (SPECL (map redex plis)
                                    (ASSUME (concl th5)))
                        val th7 = end_itlist CONJ (map (REFL o redex) no)
                        val th8 = GENL avs (MP th6 th7)
                    in IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th8)
                    end
            val ftm = funpow (length carg) (body o rand) (rand(concl eth))
        in TRANS eth (itlist MK_FORALL carg (FORALL_IMPS_CONV ftm))
        end
    handle Interrupt => raise Interrupt
          |        e => WRAP_ERR("canonicalize_clause",e)
end;;

(* ------------------------------------------------------------------------- *)
(* Canonicalizes the set of clauses, disjoining compatible antecedants.      *)
(* ------------------------------------------------------------------------- *)

fun canonicalize_clauses clauses =
  let fun assoc2 x ([],_) = fail()
        | assoc2 x (h1::t1,h2::t2) = if (x = h1) then h2 else assoc2 x (t1,t2)
      val concls = map getconcl clauses
      val uncs = map strip_comb concls
      val rels = itlist (insert o fst) uncs []
      val xargs = map (C assoc uncs) rels
      val closed = list_mk_conj clauses
      val avoids = variables closed
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
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("canonicalize_clauses",e);;

(* ------------------------------------------------------------------------- *)
(* Produces a sequence of variants, considering previous inventions.         *)
(* ------------------------------------------------------------------------- *)

fun variants av vs =
  if null vs then [] else
  let val vh = variant av (hd vs) in vh::(variants (vh::av) (tl vs)) end;;

(* ------------------------------------------------------------------------- *)
(* Prove definitions work for non-schematic relations with canonical rules.  *)
(* ------------------------------------------------------------------------- *)

fun derive_canon_inductive_relations pclauses =
    let val closed = list_mk_conj pclauses
        val pclauses = strip_conj closed
        val (vargs,bodies) = split(map strip_forall pclauses)
        val (ants,concs) = split(map dest_imp bodies)
        val rels = map (repeat rator) concs
        val avoids = variables closed
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
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("derive_canon_inductive_relations",e);

(* ------------------------------------------------------------------------- *)
(* General case for nonschematic relations; monotonicity & defn hyps.        *)
(* ------------------------------------------------------------------------- *)

fun derive_nonschematic_inductive_relations tm =
  let val clauses = strip_conj tm
      val canonthm = canonicalize_clauses clauses
      val canonthm' = SYM canonthm
      val pclosed = rand(concl canonthm)
      val pclauses = strip_conj pclosed
      val rawthm = derive_canon_inductive_relations pclauses
      val (ruvalhm,otherthms) = CONJ_PAIR rawthm
      val (indthm,casethm) = CONJ_PAIR otherthms
      val ruvalhm' = EQ_MP canonthm' ruvalhm
      and indthm' = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV canonthm')) indthm
  in CONJ ruvalhm' (CONJ indthm' casethm)
  end
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("derive_nonschematic_inductive_relations",e);;

(* ========================================================================= *)
(* Part 2: Tactic-integrated tools for proving monotonicity automatically.   *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(*   ?- (\x. P[x]) x1 .. xn ==> (\y. Q[y]) x1 .. xn                          *)
(* ==================================================                        *)
(*     ?- !x1. P[x1] x2 .. xn ==> Q[x1] x2 .. xn                             *)
(* ------------------------------------------------------------------------- *)

val imp_tm = (--`$==>`--);

fun MONO_ABS_TAC (asl,w) =
    let val (ant,con) = dest_imp w
        val vars = snd(strip_comb con)
        val rnum = length vars - 1
        val (hd1,args1) = strip_ncomb rnum ant
        and (hd2,args2) = strip_ncomb rnum con
        val th1 = rev_itlist (C AP_THM) args1 (BETA_CONV hd1)
        and th2 = rev_itlist (C AP_THM) args1 (BETA_CONV hd2)
        val th3 = MK_COMB(AP_TERM imp_tm th1,th2)
    in CONV_TAC(REWR_CONV th3) (asl,w)
    end;;

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
    let val match_fn = PART_MATCH (snd o dest_imp) th
    in fn (asl,w) =>
        let val th1 = match_fn w
            val (ant,con) = dest_imp(concl th1)
        in ([(asl,ant)],fn [t] => MATCH_MP th1 t)
        end
    end;;

type monoset = (string * tactic) list;

(*---------------------------------------------------------------------------
 * MONO_AND = |- (A ==> B) /\ (C ==> D) ==> (A /\ C ==> B /\ D)
 * MONO_OR  = |- (A ==> B) /\ (C ==> D) ==> (A \/ C ==> B \/ D)
 * MONO_IMP = |- (B ==> A) /\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))
 * MONO_NOT = |- (B ==> A) ==> (~A ==> ~B)
 * MONO_ALL = |- (!x. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))
 * MONO_EXISTS = |- (!x. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))
 *---------------------------------------------------------------------------*)
val MONO_AND = Ho_boolTheory.MONO_AND;
val MONO_OR  = Ho_boolTheory.MONO_OR;
val MONO_IMP = Ho_boolTheory.MONO_IMP;
val MONO_NOT = Ho_boolTheory.MONO_NOT;
val MONO_ALL = Ho_boolTheory.MONO_ALL;
val MONO_EXISTS = Ho_boolTheory.MONO_EXISTS;

local val pth = prove
 (--`(!x:'a. P x ==> Q x) ==> ($? P ==> $? Q)`--,
  DISCH_THEN(MP_TAC o MATCH_MP MONO_EXISTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[])
in
val MONO_EXISTS_TAC =
  MATCH_MP_TAC pth THEN
  CONV_TAC(RAND_CONV(ABS_CONV
   (RAND_CONV(TRY_CONV BETA_CONV) THENC
    RATOR_CONV(RAND_CONV(TRY_CONV BETA_CONV)))))
end;

local val pth = prove
 (--`(!x:'a. P x ==> Q x) ==> ($! P ==> $! Q)`--,
  DISCH_THEN(MP_TAC o MATCH_MP MONO_ALL) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[])
in
val MONO_FORALL_TAC =
  MATCH_MP_TAC pth THEN
  CONV_TAC(RAND_CONV(ABS_CONV
   (RAND_CONV(TRY_CONV BETA_CONV) THENC
    RATOR_CONV(RAND_CONV(TRY_CONV BETA_CONV)))))
end;

val bool_monoset =
 [("/\\",BACKCHAIN_TAC MONO_AND THEN CONJ_TAC),
  ("\\/",BACKCHAIN_TAC MONO_OR THEN CONJ_TAC),
  ("?",MONO_EXISTS_TAC),
  ("!",MONO_FORALL_TAC),

  ("",MONO_ABS_TAC),
  ("==>",BACKCHAIN_TAC MONO_IMP THEN CONJ_TAC),
  ("~",BACKCHAIN_TAC MONO_NOT)];;

val APPLY_MONOTAC =
    let val IMP_REFL = TAUT (--`!p. p ==> p`--)
    in fn monoset => fn (asl,w) =>
        let val (a,c) = dest_imp w
        in if aconv a c then ACCEPT_TAC (SPEC a IMP_REFL) (asl,w) else
            let val cn = fst (dest_const(repeat rator c))
                         handle Interrupt => raise Interrupt
                              |         _ => ""
            in tryfind (fn (k,t) => if k = cn then t (asl,w) else fail())
                monoset
            end
        end
    end;;

(* ------------------------------------------------------------------------- *)
(* Tactics to prove monotonicity automatically.                              *)
(* ------------------------------------------------------------------------- *)

fun MONO_STEP_TAC monoset =
  REPEAT GEN_TAC THEN (APPLY_MONOTAC monoset);;

fun MONO_TAC monoset =
  REPEAT (MONO_STEP_TAC monoset) THEN ASM_REWRITE_TAC[];;

(* ========================================================================= *)
(* Part 3: Utility fnctions to modify the basic theorems in various ways.   *)
(*                                                                           *)
(* There are various fnctions that can be applied to a theorem:             *)
(*                                                                           *)
(* (1) Attempt to prove the monotonicity hypotheses                          *)
(*                                                                           *)
(* (2) Generalize it over schematic variables                                *)
(*                                                                           *)
(* (3) Derive a raw existence assertion                                      *)
(*                                                                           *)
(* (4) Actually make definitions of the inductive relations.                 *)
(*                                                                           *)
(* Generally one applies either or both of (1) and (2), then does (4).       *)
(* ========================================================================= *)

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
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("prove_monotonicity_hyps",e);;

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
  end;;

(* ------------------------------------------------------------------------- *)
(* Derive existence.                                                         *)
(* ------------------------------------------------------------------------- *)

fun derive_existence th =
    let val defs = filter is_eq (hyp th)
    in itlist EXISTS_EQUATION defs th
    end;;

(* ------------------------------------------------------------------------- *)
(* Make definitions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun make_definitions th =
  let val defs = filter is_eq (hyp th)
      val dths = map (fn tm => new_definition(fst(dest_var
                                  (fst(strip_comb(lhs tm)))),tm)) defs
      val insts = map2 (curry op |->) (map lhs defs) (map (lhs o concl) dths)
  in rev_itlist (C MP) dths (INST insts (itlist DISCH defs th))
  end;;

(* ------------------------------------------------------------------------- *)
(* "Unschematize" a set of clauses.                                          *)
(* ------------------------------------------------------------------------- *)

val unschematize_clauses =
  let fun pare_comb qvs tm =
      if null (intersect (free_vars tm) qvs) andalso all is_var
(snd(strip_comb tm))
          then tm
      else pare_comb qvs (rator tm)
  in fn clauses =>
      let val schem = map (fn cls =>
          let val (avs,bod) = strip_forall cls
          in pare_comb avs (snd(dest_imp bod)
              handle Interrupt => raise Interrupt
                   |         _ => bod)
          end) clauses
          val schems = mk_set schem
      in if is_var(hd schem) then (clauses,[]) else
         if not (length(mk_set (map (snd o strip_comb) schems)) = 1)
             then failwith "Schematic variables not used consistently" else
         let val avoids = variables (list_mk_conj clauses)
             fun hack_fn tm = mk_var(fst(dest_var(repeat rator tm)),type_of tm)
             val grels = variants avoids (map hack_fn schems)
             val crels = map2 (curry op |->) grels schems
             val clauses' = map (subst crels) clauses
         in (clauses',snd(strip_comb(hd schems)))
         end
      end
  end;;

(* ========================================================================= *)
(* Part 4: The final user wrapper.                                           *)
(* ========================================================================= *)

fun prove_nonschematic_inductive_relations_exist monoset tm =
    let val th0 = derive_nonschematic_inductive_relations tm
        val th1 = prove_monotonicity_hyps monoset th0
    in derive_existence th1
    end
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("prove_nonschematic_inductive_relations_exist",e);;

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
                    (list_mk_conj clauses')
        val th1 = prove_monotonicity_hyps monoset th0
        val th2 = generalize_schematic_variables fvs th1
    in derive_existence th2
    end
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("prove_inductive_relations_exist",e);;

fun gen_new_inductive_definition monoset tm =
    let val clauses = strip_conj tm
        val (clauses',fvs) = unschematize_clauses clauses
        val th0 = derive_nonschematic_inductive_relations
                    (list_mk_conj clauses')
        val th1 = prove_monotonicity_hyps monoset th0
        val th2 = generalize_schematic_variables fvs th1
        val th3 = make_definitions th2
        val avs = fst(strip_forall(concl th3))
        val (r,ic) = CONJ_PAIR(SPECL avs th3)
        val (i,c) = CONJ_PAIR ic
    in (GENL avs r,GENL avs i,GENL avs c)
    end
handle Interrupt => raise Interrupt
     |         e => WRAP_ERR("gen_new_inductive_definition",e);;

(* ------------------------------------------------------------------------- *)
(* A rule induction tactic.                                                  *)
(* ------------------------------------------------------------------------- *)

fun RULE_INDUCT_THEN indthm ttac =
    let val th = GEN_ALL(DISCH_ALL(SPEC_ALL(UNDISCH(SPEC_ALL indthm))))
    in MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
        TRY(DISCH_THEN ttac)
    end;;

fun RULE_INDUCT_TAC indthm = RULE_INDUCT_THEN indthm ASSUME_TAC;;

(* -------------------------------------------------------------------------
 * Simpler interfaces
 * ------------------------------------------------------------------------- *)

fun new_simple_inductive_definition specs =
    let fun mk_spec spec =
        let val R = fst(strip_comb(snd(strip_imp spec)))
        in list_mk_forall (subtract (free_vars spec) [R], spec)
        end
    in gen_new_inductive_definition bool_monoset (list_mk_conj (map mk_spec specs))
    end;

(* ------------------------------------------------------------------------- *)
(* [JRH] Wrapper for approximate compatibility with hol90 library.           *)
(* ------------------------------------------------------------------------- *)

fun new_inductive_definition{fixity = f, name = s, patt = p, rules = r} =
  let val svs = (fst(strip_comb(fst p)))::(snd p)
      fun mk_rule{hypotheses=h,conclusion=c,side_conditions=s} =
        let val hyps = h @ s
            val bod = if hyps = [] then c else mk_imp(list_mk_conj hyps,c)
            val gvs = subtract (free_vars bod) svs
         in list_mk_forall(gvs,bod) end
      val rtm = list_mk_conj (map mk_rule r)
      val dth = gen_new_inductive_definition bool_monoset rtm
   in dth end;

(*
local
fun basic_gen_RULE_INDUCT_THEN ith pcont scont (asl,w) =
  let val (rtm,otm) = dest_imp w
      val (r,vars) = strip_comb rtm
      val r' = list_mk_abs(vars,otm)
      val rth = HALF_BETA_EXPAND vars (REFL r')
      val r0' = fst(strip_comb(rand(snd(strip_forall(rand(snd(strip_forall
                 (concl ith))))))))
      val cjs = strip_conj(fst(dest_imp(snd(strip_forall(concl ith)))))
      fun mk_cont t =
        let val bod = snd(strip_forall t)
            val hyp = (strip_conj(fst(dest_imp bod))
                      handle Interrupt => raise Interrupt
                           |         _ => [])
            val cts = map (fn t => if free_in r0' t then pcont else scont) hyp
         in fn th => EVERY (map2 I cts (CONJUNCTS th)) end
      val th1 = ISPEC r' ith
      val th2 = GEN_REWRITE_RULE ONCE_DEPTH_CONV empty_rewrites [rth] th1
   in (MATCH_MP_TAC th2 THEN REPEAT CONJ_TAC THENL
        (map (fn c => REPEAT GEN_TAC THEN DISCH_THEN c) (map mk_cont cjs)))
      (asl,w)
  end
in
fun RULE_INDUCT_THEN ith pcont scont =
  REPEAT GEN_TAC THEN (basic_gen_RULE_INDUCT_THEN ith pcont scont)
end;

fun RULE_INDUCT_TAC ith = gen_RULE_INDUCT_THEN ith ASSUME_TAC ASSUME_TAC;
*)


end (* struct *)
