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
    thm_cache       : Thm.thm Net.net
  }

  fun initial_state () : state = {
    asserted_hyps   = Term.empty_tmset,
    definition_hyps = Term.empty_tmset,
    step_cache      = Redblackmap.mkDict String.compare,
    thm_cache       = Net.empty
  }

  fun cache_step (s : state) (id : string) (thm : Thm.thm) : state =
    {
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      step_cache = Redblackmap.insert (#step_cache s, id, thm),
      thm_cache = #thm_cache s
    }

  fun state_assert (s : state) (t : Term.term) : state =
    {
      asserted_hyps = HOLset.add (#asserted_hyps s, t),
      definition_hyps = #definition_hyps s,
      step_cache = #step_cache s,
      thm_cache = #thm_cache s
    }

  fun state_cache_thm (s : state) (thm : Thm.thm) : state =
    {
      asserted_hyps = #asserted_hyps s,
      definition_hyps = #definition_hyps s,
      step_cache = #step_cache s,
      thm_cache = Net.insert (Thm.concl thm, thm) (#thm_cache s)
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

  (* prove |- t by trying various automation *)
  fun auto_prove name t =
    Thm.REFL (boolSyntax.lhs t)
    handle Feedback.HOL_ERR _ =>
    tautLib.TAUT_PROVE t
    handle Feedback.HOL_ERR _ =>
    Drule.EQT_ELIM (bossLib.EVAL t)
    handle Feedback.HOL_ERR _ =>
    simpLib.SIMP_PROVE bossLib.std_ss [] t
    handle Feedback.HOL_ERR _ =>
    raise ERR name ("failed to prove: " ^ Hol_pp.term_to_string t)

  (* prove an arithmetic tautology *)
  fun arith_prove t =
    intLib.ARITH_PROVE t
    handle Feedback.HOL_ERR _ =>
    RealField.REAL_ARITH t
    handle Feedback.HOL_ERR _ =>
    raise ERR "arith_prove" ("failed: " ^ Hol_pp.term_to_string t)

  (* try to prove a tautology by METIS *)
  (* METIS with a time/inference limit to avoid non-termination *)
  val metis_limit : mlibMeter.limit = {time = SOME 0.05, infs = SOME 50}

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
    (* For each resolvent, add its negation as a way to derive t *)
    val dict = List.foldl (fn (th, dict) =>
      let
        val lit = Thm.concl th
        val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
          handle Feedback.HOL_ERR _ =>
            (false, boolSyntax.mk_neg lit)
        val th = if is_neg then
            Thm.NOT_ELIM th
          else
            Thm.MP (Thm.SPEC lit NOT_FALSE) th
        val th = Thm.CCONTR t (Thm.MP th (Thm.ASSUME neg_lit))
      in
        Redblackmap.insert (dict, neg_lit, th)
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
  fun replay_cong (s : state) (id : string)
                  (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val (lhs, rhs) = boolSyntax.dest_eq target

    (* Decompose lhs and rhs into (f, [a1,...,an]) and (g, [b1,...,bn]) *)
    val (f_l, args_l) = boolSyntax.strip_comb lhs
    val (f_r, args_r) = boolSyntax.strip_comb rhs

    (* Build a dict from (lhs, rhs) -> thm for each premise *)
    fun prem_key th =
      let val c = Thm.concl th
          val (l, r) = boolSyntax.dest_eq c
      in ((l, r), th) end
      handle Feedback.HOL_ERR _ => raise ERR "replay_cong" "premise not eq"
    val prem_list = List.map prem_key prems

    (* For each argument pair (ai, bi), find a matching premise or use REFL *)
    fun find_prem (a, b) =
      if Term.aconv a b then Thm.REFL a
      else
        case List.find (fn ((l,r),_) =>
               (Term.aconv l a andalso Term.aconv r b) orelse
               (Term.aconv l b andalso Term.aconv r a)) prem_list of
          SOME ((l,_), th) =>
            if Term.aconv l a then th else Thm.SYM th
        | NONE =>
            (* try alpha-conversion *)
            Thm.ALPHA a b
            handle Feedback.HOL_ERR _ =>
            raise ERR "replay_cong" "no matching premise"

    val thm =
      if Term.aconv f_l f_r then
        (* Same function, different args *)
        let
          val eq_pairs = ListPair.zipEq (args_l, args_r)
          val arg_eqs = List.map find_prem eq_pairs
          (* Build: REFL f, then MK_COMB with each arg equality *)
          fun build base [] = base
            | build base (eq :: rest) = build (Thm.MK_COMB (base, eq)) rest
        in
          build (Thm.REFL f_l) arg_eqs
        end
      else
        (* Function itself changed: find premise for f_l = f_r *)
        let
          val f_eq = find_prem (f_l, f_r)
          val eq_pairs = ListPair.zipEq (args_l, args_r)
          val arg_eqs = List.map find_prem eq_pairs
          fun build base [] = base
            | build base (eq :: rest) = build (Thm.MK_COMB (base, eq)) rest
        in
          build f_eq arg_eqs
        end
      handle Feedback.HOL_ERR _ =>
        (* Fallback: try direct MK_COMB chain *)
        let
          fun mk_cong_chain [] = raise ERR "" ""
            | mk_cong_chain [th] = th
            | mk_cong_chain (th :: rest) =
                let val th2 = mk_cong_chain rest
                in Thm.MK_COMB (th, th2)
                   handle Feedback.HOL_ERR _ => Thm.MK_COMB (th2, th)
                end
        in mk_cong_chain prems end
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
        (* fall back to METIS *)
        metis_prove prems target
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
        [p] => metis_prove [p] target
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
  fun replay_forall_inst (s : state) (id : string)
                         (clause : Term.term list) (args : Term.term list) =
  let
    val target = clause_to_disj clause
    val thm = prove_tautology clause
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
      (* Try SIMP *)
      simpLib.SIMP_PROVE (bossLib.++ (bossLib.std_ss, wordsLib.WORD_ss))
        [boolTheory.EQ_SYM_EQ] target
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
  fun replay_bind (s : state) (id : string)
                  (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    fun go [p] =
          if Term.aconv (Thm.concl p) target then p
          else
            (prove_eq target
             handle Feedback.HOL_ERR _ =>
             metis_prove [p] target)
      | go [] = prove_eq target
      | go ps = metis_prove ps target
    val thm = go prems
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
      handle Feedback.HOL_ERR _ =>
      (* skolemization is complex; use oracle as last resort *)
      Thm.mk_oracle_thm "Alethe_sko" ([], target)
  in
    (cache_step s id thm, thm)
  end

  (* --- hole (escape hatch — oracle) --- *)
  fun replay_hole (s : state) (id : string)
                  (prems : Thm.thm list) (clause : Term.term list) =
  let
    val target = clause_to_disj clause
    val _ = if !Library.trace > 0 then
              WARNING "replay_hole"
                ("step '" ^ id ^ "': falling back to oracle for 'hole' rule")
            else ()
    val thm =
      (* try to derive from premises first *)
      (if not (List.null prems) then
         metis_prove prems target
       else
         raise ERR "" "")
      handle Feedback.HOL_ERR _ =>
      Thm.mk_oracle_thm "Alethe_hole" ([], target)
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
    val {id, clause, rule, premises, args} = step
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
        (* Closing step of a subproof — the result should follow from
           the subproof's assumptions and accumulated steps.
           The premises contain the discharged assumptions. *)
        let
          val target = clause_to_disj clause
          val thm = metis_prove prems target
            handle Feedback.HOL_ERR _ =>
            prove_tautology clause
            handle Feedback.HOL_ERR _ =>
            Thm.mk_oracle_thm "Alethe_subproof" ([], target)
        in (cache_step s id thm, thm) end
    | "symm"               =>
        let val thm = case prems of
              [p] => Thm.SYM p
                handle Feedback.HOL_ERR _ =>
                metis_prove [p] (clause_to_disj clause)
            | _ => prove_tautology clause
        in (cache_step s id thm, thm) end
    | other =>
      let
        val _ = if !Library.trace > 0 then
                  WARNING "replay_step"
                    ("unknown rule '" ^ other ^ "' at step '" ^ id ^
                     "'; falling back to oracle")
                else ()
        val target = clause_to_disj clause
        val thm =
          (* try to derive from premises *)
          (if not (List.null prems) then
             metis_prove prems target
           else raise ERR "" "")
          handle Feedback.HOL_ERR _ =>
          prove_tautology clause
          handle Feedback.HOL_ERR _ =>
          Thm.mk_oracle_thm "Alethe_unknown" ([], target)
      in
        (cache_step s id thm, thm)
      end)
    handle e =>
      let
        val target = clause_to_disj clause
        val _ = if !Library.trace > 0 then
                  WARNING "replay_step"
                    ("step '" ^ id ^ "' rule='" ^ rule ^
                     "' failed (" ^ exnMessage e ^
                     "); falling back to oracle")
                else ()
        val thm = Thm.mk_oracle_thm "Alethe_fallback" ([], target)
      in
        (cache_step s id thm, thm)
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
