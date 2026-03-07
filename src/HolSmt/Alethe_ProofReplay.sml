(* Proof reconstruction for cvc5/Alethe: replaying Alethe proofs in HOL *)

structure Alethe_ProofReplay =
struct

local

  open boolLib

  val ERR = Feedback.mk_HOL_ERR "Alethe_ProofReplay"
  val WARNING = Feedback.HOL_WARNING "Alethe_ProofReplay"

  val op |-> = Lib.|->

  (***************************************************************************)
  (* state                                                                   *)
  (***************************************************************************)

  type state = {
    asserted_hyps   : Term.term HOLset.set,
    definition_hyps : Term.term HOLset.set,
    step_cache      : (string, Thm.thm) Redblackmap.dict,
    thm_cache       : Thm.thm Net.net,
    prev_thm        : Thm.thm option
  }

  fun initial_state () : state = {
    asserted_hyps   = Term.empty_tmset,
    definition_hyps = Term.empty_tmset,
    step_cache      = Redblackmap.mkDict String.compare,
    thm_cache       = Net.empty,
    prev_thm        = NONE
  }

  fun cache_step (s : state) (id : string) (thm : Thm.thm) : state =
    {
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      step_cache = Redblackmap.insert (#step_cache s, id, thm),
      thm_cache = #thm_cache s,
      prev_thm = SOME thm
    }

  fun state_assert (s : state) (t : Term.term) : state =
    {
      asserted_hyps = HOLset.add (#asserted_hyps s, t),
      definition_hyps = #definition_hyps s,
      step_cache = #step_cache s,
      thm_cache = #thm_cache s,
      prev_thm = #prev_thm s
    }

  fun state_cache_thm (s : state) (thm : Thm.thm) : state =
    {
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      step_cache = #step_cache s,
      thm_cache = Net.insert (Thm.concl thm, thm) (#thm_cache s),
      prev_thm = #prev_thm s
    }

  fun lookup_step (s : state) (id : string) : Thm.thm =
    Redblackmap.find (#step_cache s, id)
    handle Redblackmap.NotFound =>
      raise ERR "lookup_step" ("step '" ^ id ^ "' not found in cache")

  fun lookup_premises (s : state) (ids : string list) : Thm.thm list =
    List.map (lookup_step s) ids

  (***************************************************************************)
  (* clause representation                                                   *)
  (***************************************************************************)

  (* Alethe clauses (cl l1 ... ln) represent disjunctions.
     - (cl)       = empty clause = F
     - (cl l)     = unit clause  = l
     - (cl l1 l2) = l1 \/ l2
     We build right-associated disjunctions. *)

  fun clause_to_disj [] = boolSyntax.F
    | clause_to_disj [t] = t
    | clause_to_disj (t :: ts) = boolSyntax.mk_disj (t, clause_to_disj ts)

  fun disj_to_clause t =
    if Feq t then []
    else boolSyntax.strip_disj t

  (***************************************************************************)
  (* auxiliary proof functions                                               *)
  (***************************************************************************)

  (* A static simpset for real arithmetic. We avoid srw_ss() because it is
     dynamic (its contents change as theories are loaded), which is
     undesirable in a decision procedure. real_ss is static and covers
     most real-number simplification; we add REAL_ADD_LINV/RINV for
     goals like -(1*x) + x = 0 that arise from Alethe proofs. *)
  val alethe_ss =
    simpLib.++ (realSimps.real_ss,
    simpLib.rewrites [realTheory.REAL_ADD_LINV, realTheory.REAL_ADD_RINV,
                      realTheory.POW_ONE])

  (* prove |- t by trying various automation *)
  fun auto_prove name t =
    let val (l, r) = boolSyntax.dest_eq t
    in if Term.aconv l r then Thm.REFL l
       else raise ERR "auto_prove" "not reflexive"
    end
    handle Feedback.HOL_ERR _ =>
    tautLib.TAUT_PROVE t
    handle Feedback.HOL_ERR _ =>
    Drule.EQT_ELIM (bossLib.EVAL t)
    handle Feedback.HOL_ERR _ =>
    simpLib.SIMP_PROVE bossLib.std_ss [] t
    handle Feedback.HOL_ERR _ =>
    simpLib.SIMP_PROVE alethe_ss [] t
    handle Feedback.HOL_ERR _ =>
    raise ERR name ("failed to prove: " ^ Hol_pp.term_to_string t)

  (* prove an arithmetic tautology *)
  fun arith_prove t =
    intLib.ARITH_PROVE t
    handle Feedback.HOL_ERR _ =>
    RealField.REAL_ARITH t
    handle Feedback.HOL_ERR _ =>
    (* nonlinear arithmetic fallback *)
    if Library.is_nonlinear t then Library.nla_prove t
    else raise ERR "arith_prove" ("failed: " ^ Hol_pp.term_to_string t)

  (* try to prove a tautology by METIS *)
  (* METIS with a time/inference limit to avoid non-termination *)
  val metis_limit : mlibMeter.limit = {time = SOME 0.2, infs = SOME 500}

  fun metis_prove thms t =
    Lib.with_flag (metisTools.limit, metis_limit)
      (fn () => metisLib.METIS_PROVE thms t) ()
    handle Feedback.HOL_ERR _ =>
    raise ERR "metis_prove" ("failed: " ^ Hol_pp.term_to_string t)

  (* Direct clause resolution, adapted from Z3_ProofReplay.unit_resolution.
     Given thms = [clause, unit1, unit2, ...], derives t by resolving
     the clause against the unit clauses (negation-complementary literals). *)
  val NOT_FALSE = HolSmtTheory.NOT_FALSE  (* |- !p. p ==> ~p ==> F *)

  fun unit_resolution (thms, t) =
  let
    val _ = if List.null thms then
        raise ERR "unit_resolution" ""
      else ()
    (* Build a dictionary mapping each disjunct of t to a proof of t
       from that disjunct *)
    fun disjuncts dict (disj, thm) =
    let
      val (l, r) = boolSyntax.dest_disj disj
      val thm = Thm.DISCH disj thm
      val l_imp_concl = Thm.MP thm (Thm.DISJ1 (Thm.ASSUME l) r)
      val r_imp_concl = Thm.MP thm (Thm.DISJ2 l (Thm.ASSUME r))
    in
      disjuncts (disjuncts dict (l, l_imp_concl)) (r, r_imp_concl)
    end
    handle Feedback.HOL_ERR _ =>
      Redblackmap.insert (dict, disj, thm)
    fun prove_from_disj dict disj =
      Redblackmap.find (dict, disj)
      handle Redblackmap.NotFound =>
        let
          val (l, r) = boolSyntax.dest_disj disj
          val l_th = prove_from_disj dict l
          val r_th = prove_from_disj dict r
        in
          Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
        end
    val dict = disjuncts (Redblackmap.mkDict Term.compare) (t, Thm.ASSUME t)
    (* For each resolvent, add its negation as a way to derive t.
       We insert both the canonical neg_lit and the literal form
       ¬lit to handle double negation: if lit = ¬A, then neg_lit = A
       but the clause may contain ¬¬A = ¬lit instead. *)
    val dict = List.foldl (fn (th, dict) =>
      let
        val lit = Thm.concl th
        val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
          handle Feedback.HOL_ERR _ =>
            (false, boolSyntax.mk_neg lit)
        val th' = if is_neg then
            Thm.NOT_ELIM th
          else
            Thm.MP (Thm.SPEC lit NOT_FALSE) th
        val resolved = Thm.CCONTR t (Thm.MP th' (Thm.ASSUME neg_lit))
        val dict = Redblackmap.insert (dict, neg_lit, resolved)
        (* Also insert ¬lit for double-negation matching *)
        val double_neg = boolSyntax.mk_neg lit
        val dict = if Term.compare (neg_lit, double_neg) = EQUAL then dict
                   else
                     let val dn_th = Thm.CCONTR t
                           (Thm.MP (Thm.NOT_ELIM (Thm.ASSUME double_neg)) th)
                     in Redblackmap.insert (dict, double_neg, dn_th) end
                   handle Feedback.HOL_ERR _ => dict
      in
        dict
      end) dict (List.tl thms)
    val dict = Redblackmap.insert
      (dict, boolSyntax.F, Thm.CCONTR t (Thm.ASSUME boolSyntax.F))
    val clause = Thm.concl (List.hd thms)
    val clause_imp_t = prove_from_disj dict clause
  in
    Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
  end

  (* Build |- t from |- lhs = rhs when t is lhs = rhs *)
  fun prove_eq t =
  let
    val (l, r) = boolSyntax.dest_eq t
  in
    if Term.aconv l r then Thm.REFL l
    else
      (* try ALPHA *)
      Thm.ALPHA l r
      handle Feedback.HOL_ERR _ =>
      auto_prove "prove_eq" t
  end

  (* |- l1 \/ l2 \/ ... \/ ln from thms resolving complementary lits *)
  fun resolution_prove (thms, target_clause) =
  let
    val target = clause_to_disj target_clause
  in
    if List.null thms then
      raise ERR "resolution_prove" "no premises"
    else if List.length thms = 1 andalso
            Term.aconv (Thm.concl (List.hd thms)) target then
      List.hd thms
    else
      (* Use METIS as a robust fallback for resolution *)
      metis_prove (List.map Thm.ASSUME
        (List.map Thm.concl thms @ List.map Thm.concl thms)) target
      handle Feedback.HOL_ERR _ =>
      let
        (* manual resolution via unit_resolution style *)
        val clause_thm = List.hd thms
        val units = List.tl thms
        (* try to derive target from clause + units *)
        fun try_resolve () =
        let
          val concl_terms = List.map Thm.concl (clause_thm :: units)
        in
          Lib.with_flag (metisTools.limit, metis_limit) (fn () =>
            Tactical.TAC_PROOF ((concl_terms, target),
              Tactical.THEN (
                Tactical.MAP_EVERY Tactic.ASSUME_TAC (clause_thm :: units),
                metisLib.METIS_TAC []))) ()
        end
      in
        try_resolve ()
      end
  end

  (* Prove a simple propositional tautology (no premises) *)
  fun prove_tautology clause =
  let
    val t = clause_to_disj clause
  in
    tautLib.TAUT_PROVE t
    handle Feedback.HOL_ERR _ =>
    auto_prove "prove_tautology" t
  end

  (* Given |- conj (a conjunction), extract the i-th conjunct (0-based) *)
  fun extract_conjunct thm i =
  let
    fun go th 0 = th
      | go th n =
        let
          val (_, r) = boolSyntax.dest_conj (Thm.concl th)
              handle Feedback.HOL_ERR _ =>
                raise ERR "extract_conjunct" "not enough conjuncts"
        in
          go (Thm.CONJUNCT2 th) (n - 1)
        end
        handle Feedback.HOL_ERR _ =>
          raise ERR "extract_conjunct" "not enough conjuncts"
  in
    if i = 0 then
      (Thm.CONJUNCT1 thm handle Feedback.HOL_ERR _ => thm)
    else
      go thm i
  end

  (* from |- A /\ B /\ ... /\ Z, extract the conjunct matching t *)
  fun find_conjunct thm t =
    Library.conj_elim (thm, t)

  (***************************************************************************)
  (* rule replay functions                                                   *)
  (***************************************************************************)

  (* --- assume --- *)
  fun replay_assume (s : state) (id : string) (t : Term.term) =
  let
    val thm = Thm.ASSUME t
    val s' = state_assert s t
  in
    (cache_step s' id thm, thm)
  end

  (* --- true --- *)
  fun replay_true (s : state) (id : string) =
  let
    val thm = boolTheory.TRUTH
  in
    (cache_step s id thm, thm)
  end

  (* --- refl --- *)
  fun replay_refl (s : state) (id : string) (clause : Term.term list) =
  let
    val t = clause_to_disj clause
    val (l, _) = boolSyntax.dest_eq t
    val thm = Thm.REFL l
  in
    (cache_step s id thm, thm)
  end

  (* --- trans --- *)
  fun replay_trans (s : state) (id : string)
                   (prems : Thm.thm list) (clause : Term.term list) =
  let
    val thm = case prems of
        [th1, th2] => Thm.TRANS th1 th2
      | _ =>
        let
          val target = clause_to_disj clause
        in
          metis_prove prems target
        end
  in
    (cache_step s id thm, thm)
  end

  (* --- cong --- *)
  (* Build |- f(a1,...,an) = f(b1,...,bn) from premises ai = bi,
     inserting REFL for unchanged arguments. *)
  (* Alethe 'cong' rule: given premises a1=b1, ..., an=bn,
     prove f(a1,...,an) = f(b1,...,bn).
     Handles n-ary Alethe functions mapped to binary HOL4 operators
     by recursively decomposing via dest_comb. *)
  fun replay_cong (s : state) (id : string)
                  (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val (lhs, rhs) = boolSyntax.dest_eq target

    (* Premise lookup: find ⊢ a = b among premises *)
    val prem_list = List.map (fn th =>
      let val (l, r) = boolSyntax.dest_eq (Thm.concl th)
      in ((l, r), th) end
      handle Feedback.HOL_ERR _ =>
        raise ERR "replay_cong" "premise not eq") prems

    fun find_prem (a, b) =
      if Term.aconv a b then Thm.REFL a
      else
        case List.find (fn ((l,r),_) =>
               (Term.aconv l a andalso Term.aconv r b) orelse
               (Term.aconv l b andalso Term.aconv r a)) prem_list of
          SOME ((l,_), th) =>
            if Term.aconv l a then th else Thm.SYM th
        | NONE =>
            Thm.ALPHA a b
            handle Feedback.HOL_ERR _ =>
            raise ERR "replay_cong" "no matching premise"

    (* Recursively decompose and build equality via MK_COMB.
       Handles n-ary Alethe ops → nested binary HOL4 ops. *)
    fun build_eq (l, r) =
      if Term.aconv l r then Thm.REFL l
      else
        (* Try direct premise match first *)
        find_prem (l, r)
        handle Feedback.HOL_ERR _ =>
        (* Decompose: (f_l arg_l) = (f_r arg_r) *)
        let
          val (fl, al) = Term.dest_comb l
          val (fr, ar) = Term.dest_comb r
          val fun_eq = build_eq (fl, fr)
          val arg_eq = find_prem (al, ar)
                       handle Feedback.HOL_ERR _ => build_eq (al, ar)
        in
          Thm.MK_COMB (fun_eq, arg_eq)
        end

    val thm = build_eq (lhs, rhs)
              handle Feedback.HOL_ERR _ =>
              metis_prove prems target
  in
    (cache_step s id thm, thm)
  end

  (* --- eq_reflexive --- *)
  fun replay_eq_reflexive (s : state) (id : string) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case clause of
        [eq] =>
          let val (l, _) = boolSyntax.dest_eq eq
          in Thm.REFL l end
      | _ => prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- eq_transitive --- *)
  fun replay_eq_transitive (s : state) (id : string) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- eq_congruent --- *)
  fun replay_eq_congruent (s : state) (id : string) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- eq_congruent_pred --- *)
  fun replay_eq_congruent_pred (s : state) (id : string)
                               (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- resolution / th_resolution --- *)

  (* Quick check: is lit the negation of neg_lit? *)
  fun is_neg_of lit neg_lit =
    (Term.aconv lit (boolSyntax.dest_neg neg_lit))
    handle Feedback.HOL_ERR _ =>
    (Term.aconv (boolSyntax.dest_neg lit) neg_lit)
    handle Feedback.HOL_ERR _ =>
    false

  fun replay_resolution (s : state) (id : string)
                        (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm =
      if List.null prems then
        prove_tautology clause
      else
        (* try: if target matches a single premise, done *)
        Lib.tryfind (fn p =>
          if Term.aconv (Thm.concl p) target then p
          else raise ERR "" "") prems
        handle Feedback.HOL_ERR _ =>
        (* try direct unit_resolution (fast, no search) *)
        unit_resolution (prems, target)
        handle Feedback.HOL_ERR _ =>
        (* For reordering: premise is just a permutation of the target *)
        (case prems of
           [p] =>
             let val p_lits = boolSyntax.strip_disj (Thm.concl p)
                 val t_lits = boolSyntax.strip_disj target
             in
               if length p_lits = length t_lits andalso
                  List.all (fn t => List.exists (fn p => Term.aconv t p) p_lits) t_lits
               then
                 Thm.MP (tautLib.TAUT_PROVE
                   (boolSyntax.mk_imp (Thm.concl p, target))) p
               else raise ERR "" ""
             end
         | _ => raise ERR "" "")
        handle Feedback.HOL_ERR _ =>
        (* General multi-clause resolution: Alethe's resolution rule is
           hyper-resolution (not just unit resolution). Multiple multi-literal
           clauses resolve simultaneously by canceling complementary literals.
           METIS_PROVE implements exactly this — propositional resolution. *)
        metisLib.METIS_PROVE prems target
  in
    (cache_step s id thm, thm)
  end

  (* --- and --- *)
  fun replay_and (s : state) (id : string)
                 (prems : Thm.thm list) (clause : Term.term list)
                 (args : Term.term list) =
  let
    val thm = case prems of
        [conj_thm] =>
        let
          val target = clause_to_disj clause
        in
          (* extract matching conjunct *)
          find_conjunct conj_thm target
          handle Feedback.HOL_ERR _ =>
          (* try with index from args *)
          (case args of
             [idx] =>
               let val i = Arbnum.toInt (numSyntax.dest_numeral idx)
               in extract_conjunct conj_thm i end
           | _ => raise ERR "replay_and" "cannot extract conjunct")
        end
      | _ => raise ERR "replay_and" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- not_or --- *)
  fun replay_not_or (s : state) (id : string)
                    (prems : Thm.thm list) (clause : Term.term list) =
  let
    val thm = case prems of
        [not_disj_thm] =>
        let
          val target = clause_to_disj clause
          val neg_disj = Thm.concl not_disj_thm
        in
          (* From |- ~(A \/ B \/ ...), derive |- ~Ai *)
          metis_prove [not_disj_thm] target
          handle Feedback.HOL_ERR _ =>
          auto_prove "replay_not_or" target
        end
      | _ => raise ERR "replay_not_or" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- or --- *)
  fun replay_or (s : state) (id : string)
                (prems : Thm.thm list) (clause : Term.term list) =
  let
    val thm = case prems of
        [p] =>
        let
          val target = clause_to_disj clause
          val pc = Thm.concl p
        in
          if Term.aconv pc target then p
          else
            (* from |- A \/ B \/ ..., just re-associate *)
            metis_prove [p] target
            handle Feedback.HOL_ERR _ =>
            Library.disj_intro (p, target)
        end
      | _ => raise ERR "replay_or" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- not_and --- *)
  fun replay_not_and (s : state) (id : string)
                     (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case prems of
        [p] => metis_prove [p] target
      | _ => raise ERR "replay_not_and" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- implies --- *)
  (* Alethe implies: from |- (p ==> q) or |- (l1 \/ ... \/ ln),
     derive the clausified form. Use unit_resolution when possible,
     else TAUT_PROVE for the propositional structure. *)
  fun replay_implies (s : state) (id : string)
                     (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case prems of
        [p] =>
          (* Try: from |- p ==> q, derive |- ~p \/ q *)
          (let val c = Thm.concl p
               val (ant, con) = boolSyntax.dest_imp c
               (* |- p ==> q  means  |- ~p \/ q  propositionally *)
               val not_ant = boolSyntax.mk_neg ant
           in
             if Term.aconv target (boolSyntax.mk_disj (not_ant, con)) then
               Thm.DISJ_CASES (Thm.SPEC ant boolTheory.EXCLUDED_MIDDLE)
                 (Thm.DISJ2 not_ant (Thm.MP p (Thm.ASSUME ant)))
                 (Thm.DISJ1 (Thm.ASSUME not_ant) con)
             else
               unit_resolution ([p], target)
           end
           handle Feedback.HOL_ERR _ =>
           unit_resolution ([p], target)
           handle Feedback.HOL_ERR _ =>
           metis_prove [p] target)
      | _ => unit_resolution (prems, target)
        handle Feedback.HOL_ERR _ =>
        prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- not_implies1 / not_implies2 --- *)
  fun replay_not_implies (s : state) (id : string)
                         (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case prems of
        [p] =>
          metis_prove [p] target
          handle Feedback.HOL_ERR _ =>
          (* unfold Abbrev markers and retry *)
          let val p' = CONV_RULE (REWRITE_CONV [markerTheory.Abbrev_def]) p
          in metis_prove [p'] target end
      | _ => raise ERR "replay_not_implies" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- equiv1 / equiv2 --- *)
  fun replay_equiv (s : state) (id : string)
                   (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case prems of
        [p] =>
          metis_prove [p] target
          handle Feedback.HOL_ERR _ =>
          let
            val (l, r) = boolSyntax.dest_eq (Thm.concl p)
                handle Feedback.HOL_ERR _ =>
                  raise ERR "replay_equiv" "premise not an equality"
            val eq_imp = Thm.MP (Thm.SPEC r (Thm.SPEC l boolTheory.EQ_IMP_THM)) p
            val imp1 = Thm.CONJUNCT1 eq_imp
            val imp2 = Thm.CONJUNCT2 eq_imp
          in
            (* try building the target clause from imp1/imp2 *)
            metis_prove [imp1, imp2] target
          end
      | _ => raise ERR "replay_equiv" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- not_equiv1 / not_equiv2 --- *)
  fun replay_not_equiv (s : state) (id : string)
                       (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case prems of
        [p] => metis_prove [p] target
      | _ => raise ERR "replay_not_equiv" "expected 1 premise"
  in
    (cache_step s id thm, thm)
  end

  (* --- ite1 / ite2 / not_ite1 / not_ite2 --- *)
  fun replay_ite (s : state) (id : string)
                 (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = case prems of
        [p] => metis_prove [p] target
      | _ => prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- forall_inst --- *)
  (* Alethe forall_inst: ¬(∀x1...xn. P) ∨ P[t1/x1,...,tn/xn]
     from :args (t1 ... tn) *)
  fun replay_forall_inst (s : state) (id : string)
                         (clause : Term.term list) (args : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm =
      prove_tautology clause
      handle Feedback.HOL_ERR _ =>
      let
        (* Find the negated forall among disjuncts *)
        val disjs = boolSyntax.strip_disj target
        val (neg_forall, forall_tm) =
          Lib.tryfind (fn d =>
            let val inner = boolSyntax.dest_neg d
                val _ = boolSyntax.dest_forall inner
            in (d, inner) end) disjs
        (* Instantiate: ∀x1...xn. P ⊢ P[t1/x1,...,tn/xn] *)
        val spec_thm = List.foldl (fn (arg, th) => Thm.SPEC arg th)
                         (Thm.ASSUME forall_tm) args
        val body_inst = Thm.concl spec_thm
        (* Build ⊢ ¬∀_tm ∨ body_inst via excluded middle *)
        val em = Thm.SPEC forall_tm boolTheory.EXCLUDED_MIDDLE
        val right = Thm.DISJ2 neg_forall spec_thm
        val left = Thm.DISJ1 (Thm.ASSUME neg_forall) body_inst
        val result = Thm.DISJ_CASES em right left
      in
        if Term.aconv (Thm.concl result) target then result
        else
          (* SPEC result may differ from parser's body_inst;
             use resolution to bridge the gap *)
          let val imp = tautLib.TAUT_PROVE
                (boolSyntax.mk_imp (Thm.concl result, target))
          in Thm.MP imp result end
          handle Feedback.HOL_ERR _ =>
          auto_prove "replay_forall_inst" target
      end
      handle Feedback.HOL_ERR _ =>
      auto_prove "replay_forall_inst" target
  in
    (cache_step s id thm, thm)
  end

  (* --- Tautology rules (no premises) ---
     and_pos, and_neg, or_pos, or_neg,
     implies_pos, implies_neg1, implies_neg2,
     equiv_pos1, equiv_pos2, equiv_neg1, equiv_neg2,
     ite_pos1, ite_pos2, ite_neg1, ite_neg2,
     xor_pos1, xor_pos2, xor_neg1, xor_neg2 *)
  fun replay_tautology_rule (s : state) (id : string)
                            (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- not_not --- *)
  fun replay_not_not (s : state) (id : string) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- rewrite --- *)
  fun replay_rewrite (s : state) (id : string) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm =
      (* Try REFL first *)
      (let val (l, r) = boolSyntax.dest_eq target
       in if Term.aconv l r then Thm.REFL l
          else raise ERR "" "" end)
      handle Feedback.HOL_ERR _ =>
      (* Try alpha equivalence *)
      (let val (l, r) = boolSyntax.dest_eq target
       in Thm.ALPHA l r end)
      handle Feedback.HOL_ERR _ =>
      (* Try proforma theorems *)
      Z3_ProformaThms.prove Z3_ProformaThms.rewrite_thms target
      handle Feedback.HOL_ERR _ =>
      (* Try TAUT *)
      tautLib.TAUT_PROVE target
      handle Feedback.HOL_ERR _ =>
      (* Try arithmetic *)
      arith_prove target
      handle Feedback.HOL_ERR _ =>
      (* Try EVAL *)
      Drule.EQT_ELIM (bossLib.EVAL target)
      handle Feedback.HOL_ERR _ =>
      raise ERR "replay_rewrite" ("failed: " ^
        Library.term_to_string target)
    val s' = state_cache_thm s thm
  in
    (cache_step s' id thm, thm)
  end

  (* --- la_generic / lia_generic / la_tautology --- *)
  fun replay_arith (s : state) (id : string) (clause : Term.term list)
                   (prems : Thm.thm list) =
  let
    val target = clause_to_disj clause
    val thm =
      if List.null prems then
        arith_prove target
        handle Feedback.HOL_ERR _ =>
        prove_tautology clause
      else
        metis_prove prems target
        handle Feedback.HOL_ERR _ =>
        let val hyps = List.map Thm.concl prems
            val imp_thm = arith_prove (boolSyntax.list_mk_imp (hyps, target))
            val thm = Lib.funpow (List.length prems) (fn th =>
                Thm.MP th (List.hd prems)) imp_thm
        in thm end
        handle Feedback.HOL_ERR _ =>
        raise ERR "replay_arith" ("failed: " ^
          Library.term_to_string target)
    val s' = state_cache_thm s thm
  in
    (cache_step s' id thm, thm)
  end

  (* --- la_disequality --- *)
  fun replay_la_disequality (s : state) (id : string)
                            (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = arith_prove target
      handle Feedback.HOL_ERR _ =>
      prove_tautology clause
  in
    (cache_step s id thm, thm)
  end

  (* --- distinct_elim --- *)
  fun replay_distinct_elim (s : state) (id : string)
                           (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = if List.null prems then
        auto_prove "replay_distinct_elim" target
      else
        metis_prove prems target
  in
    (cache_step s id thm, thm)
  end

  (* --- bind --- *)
  (* Alethe 'bind' rule: within a quantifier scope, sub-steps prove
     body_old = body_new. The bind step wraps this with the quantifier:
     (∀x. body_old) = (∀x. body_new).
     The body equality is cached from sub-steps in the state. *)
  fun replay_bind (s : state) (id : string)
                  (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    (* First try: direct proof (handles simple cases) *)
    fun direct () =
      case prems of
        [p] => if Term.aconv (Thm.concl p) target then p
               else (prove_eq target
                     handle Feedback.HOL_ERR _ =>
                     metis_prove [p] target)
      | [] => prove_eq target
      | ps => metis_prove ps target
    (* Second try: peel quantifiers, find body equality in cache,
       wrap with FORALL_EQ / EXISTS_EQ *)
    fun quantifier_lift () =
    let
      val (lhs, rhs) = boolSyntax.dest_eq target
      (* Peel matching quantifiers from both sides *)
      fun peel (l, r) =
        (* try ∀ *)
        (let val (lv, lb) = boolSyntax.dest_forall l
             val (rv, rb) = boolSyntax.dest_forall r
             val rb' = Term.subst [rv |-> lv] rb
             val (vars, body_thm) = peel (lb, rb')
         in (lv :: vars, body_thm) end)
        handle Feedback.HOL_ERR _ =>
        (* try ∃ *)
        (let val (lv, lb) = boolSyntax.dest_exists l
             val (rv, rb) = boolSyntax.dest_exists r
             val rb' = Term.subst [rv |-> lv] rb
             val (vars, body_thm) = peel (lb, rb')
         in (lv :: vars, body_thm) end)
        handle Feedback.HOL_ERR _ =>
        (* Base: find body equality in cache or prove it *)
        let
          val body_eq = boolSyntax.mk_eq (l, r)
          val body_thm =
            (* Search cached sub-steps for the body equality *)
            Lib.tryfind (fn (_, th) =>
              if Term.aconv (Thm.concl th) body_eq then th
              else raise ERR "" "")
              (Redblackmap.listItems (#step_cache s))
            handle Feedback.HOL_ERR _ =>
            auto_prove "bind_body" body_eq
        in
          ([], body_thm)
        end
      val (vars, body_thm) = peel (lhs, rhs)
      val _ = if List.null vars then raise ERR "replay_bind" "no quantifiers"
              else ()
      (* Determine quantifier type from target's LHS *)
      fun is_forall t = (boolSyntax.dest_forall t; true)
                        handle Feedback.HOL_ERR _ => false
      val wrap_eq = if is_forall lhs then Drule.FORALL_EQ
                    else Drule.EXISTS_EQ
      val thm = List.foldr (fn (v, th) => wrap_eq v th) body_thm vars
    in
      thm
    end
    val thm = direct ()
              handle Feedback.HOL_ERR _ => quantifier_lift ()
  in
    (cache_step s id thm, thm)
  end

  (* --- sko_ex / sko_forall --- *)
  fun replay_sko (s : state) (id : string) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm =
      prove_eq target
      handle Feedback.HOL_ERR _ =>
      auto_prove "replay_sko" target
  in
    (cache_step s id thm, thm)
  end

  (* --- hole (cvc5 proof gap, typically TRUST_THEORY_REWRITE) ---
     These are rewrites cvc5 considers valid but doesn't prove.
     We replay them using the same automation as 'rewrite' steps. *)
  (* Prove a quantified propositional equivalence:
     ∀x. body1 = ∀x. body2  where body1 ⟺ body2 propositionally.
     Strips matching quantifiers, proves body equivalence with TAUT_PROVE,
     then wraps back with FORALL_EQ / EXISTS_EQ. *)
  fun prove_quant_body_eq target =
    let
      val (lhs, rhs) = boolSyntax.dest_eq target
      fun strip_match l r =
        if boolSyntax.is_forall l andalso boolSyntax.is_forall r then
          let val (vl, bl) = boolSyntax.dest_forall l
              val (vr, br) = boolSyntax.dest_forall r
              val br' = Term.subst [vr |-> vl] br
              val body_thm = strip_match bl br'
          in Drule.FORALL_EQ vl body_thm end
        else if boolSyntax.is_exists l andalso boolSyntax.is_exists r then
          let val (vl, bl) = boolSyntax.dest_exists l
              val (vr, br) = boolSyntax.dest_exists r
              val br' = Term.subst [vr |-> vl] br
              val body_thm = strip_match bl br'
          in Drule.EXISTS_EQ vl body_thm end
        else
          tautLib.TAUT_PROVE (boolSyntax.mk_eq (l, r))
    in
      strip_match lhs rhs
    end

  (* Check if any free variable or subterm has a word type *)
  fun has_word_type tm =
    Lib.can (HolKernel.find_term
      (fn t => wordsSyntax.is_word_type (Term.type_of t))) tm

  fun replay_hole (s : state) (id : string)
                  (prems : Thm.thm list) (clause : Term.term list) =
    replay_rewrite s id clause
    handle Feedback.HOL_ERR _ =>
    let
      val target = clause_to_disj clause
      val is_bv = has_word_type target
      val thm =
        (* 1. Try premises-based METIS *)
        (if not (List.null prems) then
           metis_prove prems target
         else
           raise ERR "" "")
        handle Feedback.HOL_ERR _ =>
        (* 2. Bitvector: skip other tactics, go straight to WORD_DECIDE *)
        (if is_bv then wordsLib.WORD_DECIDE target
         else raise ERR "" "")
        handle Feedback.HOL_ERR _ =>
        (* 3. Propositional tautology *)
        tautLib.TAUT_PROVE target
        handle Feedback.HOL_ERR _ =>
        (* 4. Quantified propositional: strip quantifiers, TAUT body *)
        prove_quant_body_eq target
        handle Feedback.HOL_ERR _ =>
        (* 5. METIS with no premises (handles first-order quantifiers) *)
        metis_prove [] target
        handle Feedback.HOL_ERR _ =>
        (* 6. Simplifier (handles e.g. -(1*x) + x = 0) *)
        simpLib.SIMP_PROVE alethe_ss [] target
        handle Feedback.HOL_ERR _ =>
        (* 7. Evaluation *)
        Drule.EQT_ELIM (bossLib.EVAL target)
        handle Feedback.HOL_ERR _ =>
        (* 8. Nonlinear arithmetic (handles ARITH_MULT_SIGN etc.) *)
        (if Library.is_nonlinear target then Library.nla_prove target
         else raise ERR "" "")
        handle Feedback.HOL_ERR _ =>
        raise ERR "replay_hole" ("step '" ^ id ^ "' failed: " ^
          Library.term_to_string target)
    in
      (cache_step s id thm, thm)
    end

  (* --- subproof (from anchor) --- *)
  fun replay_subproof (s : state) (id : string) (sub_thm : Thm.thm)
                      (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm =
      if Term.aconv (Thm.concl sub_thm) target then sub_thm
      else
        metis_prove [sub_thm] target
        handle Feedback.HOL_ERR _ =>
        (* discharge any hypotheses that were local to subproof *)
        let
          val hyps = HOLset.listItems (Thm.hypset sub_thm)
          val local_hyps = List.filter
            (fn h => not (HOLset.member (#asserted_hyps s, h))) hyps
          val discharged = List.foldl (fn (h, th) =>
            Thm.DISCH h th) sub_thm local_hyps
        in
          metis_prove [discharged] target
          handle Feedback.HOL_ERR _ =>
          sub_thm  (* best effort *)
        end
  in
    (cache_step s id thm, thm)
  end

  (***************************************************************************)
  (* main dispatch                                                           *)
  (***************************************************************************)

  fun replay_step (s : state) (step : Alethe_Proof.step) : state * Thm.thm =
  let
    val {id, clause, rule, premises, args, discharge} = step
    val prems = lookup_premises s premises
    val _ = if !Library.trace > 2 then
              Feedback.HOL_MESG ("Alethe: replaying step '" ^ id ^
                "' rule='" ^ rule ^ "' premises=[" ^
                String.concatWith "," premises ^ "]")
            else ()
  in
    (case rule of
      "assume"             => replay_assume s id (clause_to_disj clause)
    | "true"               => replay_true s id
    | "false"              => replay_tautology_rule s id clause
    | "not_not"            => replay_not_not s id clause
    | "and_pos"            => replay_tautology_rule s id clause
    | "and_neg"            => replay_tautology_rule s id clause
    | "or_pos"             => replay_tautology_rule s id clause
    | "or_neg"             => replay_tautology_rule s id clause
    | "implies_pos"        => replay_tautology_rule s id clause
    | "implies_neg1"       => replay_tautology_rule s id clause
    | "implies_neg2"       => replay_tautology_rule s id clause
    | "equiv_pos1"         => replay_tautology_rule s id clause
    | "equiv_pos2"         => replay_tautology_rule s id clause
    | "equiv_neg1"         => replay_tautology_rule s id clause
    | "equiv_neg2"         => replay_tautology_rule s id clause
    | "ite_pos1"           => replay_tautology_rule s id clause
    | "ite_pos2"           => replay_tautology_rule s id clause
    | "ite_neg1"           => replay_tautology_rule s id clause
    | "ite_neg2"           => replay_tautology_rule s id clause
    | "xor_pos1"           => replay_tautology_rule s id clause
    | "xor_pos2"           => replay_tautology_rule s id clause
    | "xor_neg1"           => replay_tautology_rule s id clause
    | "xor_neg2"           => replay_tautology_rule s id clause
    | "resolution"         => replay_resolution s id prems clause
    | "th_resolution"      => replay_resolution s id prems clause
    | "and"                => replay_and s id prems clause args
    | "not_or"             => replay_not_or s id prems clause
    | "or"                 => replay_or s id prems clause
    | "not_and"            => replay_not_and s id prems clause
    | "implies"            => replay_implies s id prems clause
    | "not_implies1"       => replay_not_implies s id prems clause
    | "not_implies2"       => replay_not_implies s id prems clause
    | "equiv1"             => replay_equiv s id prems clause
    | "equiv2"             => replay_equiv s id prems clause
    | "not_equiv1"         => replay_not_equiv s id prems clause
    | "not_equiv2"         => replay_not_equiv s id prems clause
    | "ite1"               => replay_ite s id prems clause
    | "ite2"               => replay_ite s id prems clause
    | "not_ite1"           => replay_ite s id prems clause
    | "not_ite2"           => replay_ite s id prems clause
    | "eq_reflexive"       => replay_eq_reflexive s id clause
    | "eq_transitive"      => replay_eq_transitive s id clause
    | "eq_congruent"       => replay_eq_congruent s id clause
    | "eq_congruent_pred"  => replay_eq_congruent_pred s id clause
    | "refl"               => replay_refl s id clause
    | "trans"              => replay_trans s id prems clause
    | "cong"               => replay_cong s id prems clause
    | "rewrite"            => replay_rewrite s id clause
    | "forall_inst"        => replay_forall_inst s id clause args
    | "bind"               => replay_bind s id prems clause
    | "sko_ex"             => replay_sko s id clause
    | "sko_forall"         => replay_sko s id clause
    | "la_generic"         => replay_arith s id clause prems
    | "lia_generic"        => replay_arith s id clause prems
    | "la_tautology"       => replay_arith s id clause prems
    | "la_disequality"     => replay_la_disequality s id clause
    | "distinct_elim"      => replay_distinct_elim s id prems clause
    | "hole"               => replay_hole s id prems clause
    | "let"                => replay_bind s id prems clause
    | "reordering"         => replay_resolution s id prems clause
    | "contraction"        => replay_resolution s id prems clause
    | "rare_rewrite"       => replay_rewrite s id clause
    | "la_mult_pos"        => replay_arith s id clause prems
    | "la_mult_neg"        => replay_arith s id clause prems
    | "connective_def"     => replay_rewrite s id clause
    | "and_simplify"       => replay_rewrite s id clause
    | "or_simplify"        => replay_rewrite s id clause
    | "not_simplify"       => replay_rewrite s id clause
    | "implies_simplify"   => replay_rewrite s id clause
    | "equiv_simplify"     => replay_rewrite s id clause
    | "bool_simplify"      => replay_rewrite s id clause
    | "ite_simplify"       => replay_rewrite s id clause
    | "qnt_simplify"       => replay_rewrite s id clause
    | "ac_simp"            => replay_rewrite s id clause
    | "all_simplify"      => replay_rewrite s id clause (* cvc5 1.1.2 *)
    | "comp_simplify"      => replay_rewrite s id clause
    | "qnt_rm_unused"      => replay_rewrite s id clause
    | "minus_simplify"     => replay_rewrite s id clause
    | "sum_simplify"       => replay_rewrite s id clause
    | "prod_simplify"      => replay_rewrite s id clause
    | "div_simplify"       => replay_rewrite s id clause
    | "unary_minus_simplify" => replay_rewrite s id clause
    | "nary_elim"          => replay_rewrite s id clause
    | "bfun_elim"          => replay_rewrite s id clause
    | "qnt_cnf"            => replay_tautology_rule s id clause
    | "subproof"           =>
        (* Closing step of a subproof with :discharge.
           The previous step proved some conclusion under discharged
           assumptions. We DISCH each assumption, converting to
           ¬A1 ∨ ... ∨ ¬An ∨ conclusion. *)
        let
          val target = clause_to_disj clause
          (* Discharge assumptions and convert imp to disjunction *)
          fun discharge_and_disj base_thm [] = base_thm
            | discharge_and_disj base_thm (did :: rest) =
              let
                val assume_thm = lookup_step s did
                val hyp_tm = Thm.concl assume_thm
                val discharged = Thm.DISCH hyp_tm base_thm
                (* ⊢ hyp ⇒ concl, convert to ⊢ ¬hyp ∨ concl *)
                val as_disj = Thm.MP
                  (tautLib.TAUT_PROVE
                    (boolSyntax.mk_imp
                      (boolSyntax.mk_imp (hyp_tm, Thm.concl base_thm),
                       boolSyntax.mk_disj
                         (boolSyntax.mk_neg hyp_tm, Thm.concl base_thm))))
                  discharged
              in
                discharge_and_disj as_disj rest
              end
          val thm =
            if List.null discharge then
              metis_prove prems target
              handle Feedback.HOL_ERR _ =>
              prove_tautology clause
            else
              let
                val sub_thm = case #prev_thm s of
                    SOME th => th
                  | NONE => raise ERR "subproof" "no previous step"
                val result = discharge_and_disj sub_thm discharge
              in
                if Term.aconv (Thm.concl result) target then result
                else
                  let val imp = tautLib.TAUT_PROVE
                        (boolSyntax.mk_imp (Thm.concl result, target))
                  in Thm.MP imp result end
              end
              handle Feedback.HOL_ERR _ =>
              metis_prove prems target
              handle Feedback.HOL_ERR _ =>
              prove_tautology clause
        in (cache_step s id thm, thm) end
    | "symm"               =>
        let val thm = case prems of
              [p] => Thm.SYM p
                handle Feedback.HOL_ERR _ =>
                metis_prove [p] (clause_to_disj clause)
            | _ => prove_tautology clause
        in (cache_step s id thm, thm) end
    | "not_symm"           =>
        (* ⊢ ¬(a = b) from premise ⊢ ¬(b = a), or vice versa *)
        let val target = clause_to_disj clause
            val thm = case prems of
              [p] =>
                let val inner = boolSyntax.dest_neg (Thm.concl p)
                    val (a, b) = boolSyntax.dest_eq inner
                    val sym_eq = boolSyntax.mk_eq (b, a)
                    val sym_imp = tautLib.TAUT_PROVE
                      (boolSyntax.mk_imp
                        (boolSyntax.mk_neg inner,
                         boolSyntax.mk_neg sym_eq))
                in Thm.MP sym_imp p end
                handle Feedback.HOL_ERR _ =>
                metis_prove [p] target
            | _ => prove_tautology clause
        in (cache_step s id thm, thm) end
    | other =>
        raise ERR "replay_step"
          ("unknown rule '" ^ other ^ "' at step '" ^ id ^ "'"))
    handle e =>
      let
        val _ = WARNING "replay_step"
                  ("step '" ^ id ^ "' rule='" ^ rule ^
                   "' FAILED: " ^ exnMessage e)
      in
        raise e
      end
  end

  (* Replay a single command *)
  fun replay_command (s : state) (cmd : Alethe_Proof.command) : state * Thm.thm =
    case cmd of
      Alethe_Proof.ASSUME (id, t) =>
        replay_assume s id t
    | Alethe_Proof.STEP step =>
        replay_step s step
    | Alethe_Proof.ANCHOR ({step_id, args = _}, sub_cmds) =>
      let
        (* Replay all subproof commands in the current state *)
        val (s', last_thm) = replay_commands s sub_cmds
      in
        (* The last step in the subproof should produce the anchor's result *)
        replay_subproof s' step_id last_thm
          (disj_to_clause (Thm.concl last_thm))
      end

  and replay_commands (s : state) (cmds : Alethe_Proof.command list)
                      : state * Thm.thm =
    case cmds of
      [] => raise ERR "replay_commands" "empty proof"
    | [cmd] => replay_command s cmd
    | cmd :: rest =>
      let val (s', _) = replay_command s cmd
      in replay_commands s' rest end

  (***************************************************************************)
  (* post-processing                                                         *)
  (***************************************************************************)

  (* Remove hypotheses of the form `p = p` (trivially true).
     Modeled on Z3_ProofReplay.remove_extra_hyps *)
  fun remove_trivial_hyps (asserted, thm) =
  let
    val extra_hyps = HOLset.difference (Thm.hypset thm, asserted)
    fun remove_hyp (hyp, thm) =
      if boolSyntax.is_eq hyp then
        let val (lhs, rhs) = boolSyntax.dest_eq hyp
        in
          if Term.term_eq lhs rhs then
            Drule.PROVE_HYP (Thm.REFL lhs) thm
          else thm
        end
      else thm
  in
    HOLset.foldl remove_hyp thm extra_hyps
  end

  (* Remove hypotheses not in the expected set.
     Tries lightweight methods first, then METIS_TAC as last resort.
     Modeled on Z3_ProofReplay.remove_hyps. *)
  fun remove_hyps (asl, g, thm) =
  let
    val hyps = Thm.hypset thm
    val expected = HOLset.addList (Term.empty_tmset,
      boolSyntax.mk_neg g :: asl)
    val bad_hyps = HOLset.difference (hyps, expected)
    fun try_prove_hyp hyp =
      (* Try REFL for x = x *)
      (if boolSyntax.is_eq hyp then
        let val (l, r) = boolSyntax.dest_eq hyp
        in if Term.term_eq l r then SOME (Thm.REFL l) else NONE end
       else NONE)
      handle Feedback.HOL_ERR _ => NONE
    fun try_prove_hyp_hard hyp =
      (* Try EVAL for definitional truths *)
      SOME (Drule.EQT_ELIM (bossLib.EVAL hyp))
      handle Feedback.HOL_ERR _ =>
      (* Try METIS_TAC with the assumptions as context *)
      SOME (Tactical.TAC_PROOF ((asl, hyp), metisLib.METIS_TAC []))
      handle Feedback.HOL_ERR _ => NONE
    fun remove_hyp (hyp, thm) =
      case try_prove_hyp hyp of
        SOME hyp_thm => Drule.PROVE_HYP hyp_thm thm
      | NONE =>
        (case try_prove_hyp_hard hyp of
           SOME hyp_thm => Drule.PROVE_HYP hyp_thm thm
         | NONE => thm)
  in
    HOLset.foldl remove_hyp thm bad_hyps
  end

in

  fun check_proof (asl : Term.term list, g : Term.term,
                   proof : Alethe_Proof.proof) : Thm.thm =
  let
    val s0 = initial_state ()
    val (s_final, thm) = replay_commands s0 proof
    val thm_concl = Thm.concl thm

    (* The final theorem should conclude F (empty clause) *)
    val thm =
      if Feq thm_concl then thm
      else
        let val neg_g = boolSyntax.mk_neg g
        in
          if Term.aconv thm_concl neg_g then
            Thm.MP (Thm.NOT_ELIM (Thm.ASSUME (boolSyntax.mk_neg thm_concl)))
                   thm
          else thm
        end
        handle Feedback.HOL_ERR _ => thm

    (* Collect asserted hypotheses from ASSUME steps *)
    val asserted = #asserted_hyps s_final

    (* Remove trivial hyps like p = p *)
    val thm = remove_trivial_hyps (asserted, thm)

    (* Remove any remaining extra hyps *)
    val thm = remove_hyps (asl, g, thm)
  in
    thm
  end

end

end
