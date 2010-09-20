(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: replaying Z3's proofs in HOL *)

structure Z3_ProofReplay =
struct

local

  open Z3_Proof

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofReplay"
  val WARNING = Feedback.HOL_WARNING "Z3_ProofReplay"

  val ALL_DISTINCT_NIL = HolSmtTheory.ALL_DISTINCT_NIL
  val ALL_DISTINCT_CONS = HolSmtTheory.ALL_DISTINCT_CONS
  val NOT_MEM_NIL = HolSmtTheory.NOT_MEM_NIL
  val NOT_MEM_CONS = HolSmtTheory.NOT_MEM_CONS
  val NOT_MEM_CONS_SWAP = HolSmtTheory.NOT_MEM_CONS_SWAP
  val AND_T = HolSmtTheory.AND_T
  val T_AND = HolSmtTheory.T_AND
  val F_OR = HolSmtTheory.F_OR
  val CONJ_CONG = HolSmtTheory.CONJ_CONG
  val NOT_NOT_ELIM = HolSmtTheory.NOT_NOT_ELIM
  val NOT_FALSE = HolSmtTheory.NOT_FALSE
  val NNF_CONJ = HolSmtTheory.NNF_CONJ
  val NNF_DISJ = HolSmtTheory.NNF_DISJ
  val NNF_NOT_NOT = HolSmtTheory.NNF_NOT_NOT
  val NEG_IFF_1 = HolSmtTheory.NEG_IFF_1
  val NEG_IFF_2 = HolSmtTheory.NEG_IFF_2
  val DISJ_ELIM_1 = HolSmtTheory.DISJ_ELIM_1
  val DISJ_ELIM_2 = HolSmtTheory.DISJ_ELIM_2
  val IMP_DISJ_1 = HolSmtTheory.IMP_DISJ_1
  val IMP_DISJ_2 = HolSmtTheory.IMP_DISJ_2
  val IMP_FALSE = HolSmtTheory.IMP_FALSE

  (* a simpset that deals with function (i.e., array) updates when the
     indices are integer or word literals *)
  val update_ss = simpLib.&& (simpLib.++ (intSimps.int_ss,
      simpLib.std_conv_ss {name = "word_EQ_CONV", pats = [``(x :'a word) = y``],
        conv = wordsLib.word_EQ_CONV}),
    [combinTheory.UPDATE_def, boolTheory.EQ_SYM_EQ])

  (***************************************************************************)
  (* functions that manipulate/access "global" state                         *)
  (***************************************************************************)

  type state = {
    (* keeps track of assumptions; (only) these may remain in the
       final theorem *)
    asserted_hyps : Term.term HOLset.set,
    (* keeps track of definitions "sk = ..." (where sk is a variable)
       introduced for Skolemization; these are eliminated at the end
       of proof reconstruction *)
    skolem_defs : Term.term list,
    (* stores certain theorems (proved by 'rewrite' or 'th_lemma') for
       later retrieval, to avoid re-reproving them *)
    thm_cache : Thm.thm Net.net
  }

  fun state_assert (s : state) (t : Term.term) : state =
    {
      asserted_hyps = HOLset.add (#asserted_hyps s, t),
      skolem_defs = #skolem_defs s,
      thm_cache = #thm_cache s
    }

  fun state_add_skolem_def (s : state) (t : Term.term) : state =
    {
      asserted_hyps = #asserted_hyps s,
      skolem_defs = t :: #skolem_defs s,
      thm_cache = #thm_cache s
    }

  fun state_cache_thm (s : state) (thm : Thm.thm) : state =
    {
      asserted_hyps = #asserted_hyps s,
      skolem_defs = #skolem_defs s,
      thm_cache = Net.insert (Thm.concl thm, thm) (#thm_cache s)
    }

  fun state_inst_cached_thm (s : state) (t : Term.term) : Thm.thm =
    Lib.tryfind  (* may fail *)
      (fn thm => Drule.INST_TY_TERM (Term.match_term (Thm.concl thm) t) thm)
      (Net.match t (#thm_cache s))

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  (* e.g.,   (A --> B) --> C --> D   ==>   [A, B, C, D] *)
  fun strip_fun_tys ty =
    let
      val (dom, rng) = Type.dom_rng ty
    in
      strip_fun_tys dom @ strip_fun_tys rng
    end
    handle Feedback.HOL_ERR _ => [ty]

  (* approximate: only descends into combination terms and function types *)
  fun term_contains_real_ty tm =
    let val (rator, rand) = Term.dest_comb tm
    in
      term_contains_real_ty rator orelse term_contains_real_ty rand
    end
    handle Feedback.HOL_ERR _ =>
      List.exists (Lib.equal realSyntax.real_ty)
        (strip_fun_tys (Term.type_of tm))

  (* returns "|- l = r", provided 'l' and 'r' are conjunctions that can be
     obtained from each other using associativity, commutativity and
     idempotence of conjunction, and identity of "T" wrt. conjunction.

     If 'r' is "F", 'l' must either contain "F" as a conjunct, or 'l'
     must contain both a literal and its negation. *)
  fun rewrite_conj (l, r) =
    let
      val Tl = boolSyntax.mk_conj (boolSyntax.T, l)
      val Tr = boolSyntax.mk_conj (boolSyntax.T, r)
      val Tl_eq_Tr = Drule.CONJUNCTS_AC (Tl, Tr)
    in
      Thm.MP (Drule.SPECL [l, r] T_AND) Tl_eq_Tr
    end
    handle Feedback.HOL_ERR _ =>
      if r = boolSyntax.F then
        let
          val l_imp_F = Thm.DISCH l (Library.gen_contradiction (Thm.ASSUME l))
        in
          Drule.EQF_INTRO (Thm.NOT_INTRO l_imp_F)
        end
      else
        raise ERR "rewrite_conj" ""

  (* returns "|- l = r", provided 'l' and 'r' are disjunctions that can be
     obtained from each other using associativity, commutativity and
     idempotence of disjunction, and identity of "F" wrt. disjunction.

     If 'r' is "T", 'l' must contain "T" as a disjunct, or 'l' must contain
     both a literal and its negation. *)
  fun rewrite_disj (l, r) =
    let
      val Fl = boolSyntax.mk_disj (boolSyntax.F, l)
      val Fr = boolSyntax.mk_disj (boolSyntax.F, r)
      val Fl_eq_Fr = Drule.DISJUNCTS_AC (Fl, Fr)
    in
      Thm.MP (Drule.SPECL [l, r] F_OR) Fl_eq_Fr
    end
    handle Feedback.HOL_ERR _ =>
      if r = boolSyntax.T then
        Drule.EQT_INTRO (Library.gen_excluded_middle l)
      else
        raise ERR "rewrite_disj" ""

  (* Returns "|- ALL_DISTINCT [x, y, z] = x <> y /\ x <> z /\ y <> z"; if
     'swap' is true, then each inequation "x <> y" is swapped to "y <> x" if
     y < x (according to Term.compare); if 'swap' is true, the resulting
     conjunction may contain parentheses; may raise Conv.UNCHANGED *)
  fun ALL_DISTINCT_CONV swap tm =
  let 
    fun not_mem_conv tm =
    let
      val (x, list) = listSyntax.dest_mem (boolSyntax.dest_neg tm)
    in
      if listSyntax.is_nil list then
        (* |- ~MEM x [] = T *)
        Drule.ISPEC x NOT_MEM_NIL
      else
        let
          val (h, t) = listSyntax.dest_cons list
          (* |- ~MEM x (h::t) = (x <> h) /\ ~MEM x t *)
          val th1 = Drule.ISPECL [x, h, t] (if swap andalso
                Term.compare (h, x) = LESS then
              NOT_MEM_CONS_SWAP
            else
              NOT_MEM_CONS)
          val (neq, notmem) = boolSyntax.dest_conj
            (boolSyntax.rhs (Thm.concl th1))
          (* |- ~MEM x t = rhs *)
          val th2 = not_mem_conv notmem
          (* |- ~MEM x (h::t) = (x <> h) /\ rhs *)
          val th3 = Thm.TRANS th1 (Thm.AP_TERM (Term.mk_comb
            (boolSyntax.conjunction, neq)) th2)
        in
          if boolSyntax.rhs (Thm.concl th2) = boolSyntax.T then
            Thm.TRANS th3 (Thm.SPEC neq AND_T)
          else
            th3
        end
    end
    fun all_distinct_conv tm =
    let
      val list = listSyntax.dest_all_distinct tm
    in
      if listSyntax.is_nil list then
        (* |- ALL_DISTINCT [] = T *)
        Thm.INST_TYPE [{redex = Type.alpha, residue = listSyntax.dest_nil list}]
          ALL_DISTINCT_NIL
      else
        let
          val (h, t) = listSyntax.dest_cons list
          (* |- ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t *)
          val th1 = Drule.ISPECL [h, t] ALL_DISTINCT_CONS
          val (notmem, alldistinct) = boolSyntax.dest_conj
            (boolSyntax.rhs (Thm.concl th1))
          (* |- ~MEM h t = something *)
          val th2 = not_mem_conv notmem
          (* |- ALL_DISTINCT t = rhs *)
          val th3 = all_distinct_conv alldistinct
          val th4 = Drule.SPECL [notmem, boolSyntax.rhs (Thm.concl th2),
            alldistinct, boolSyntax.rhs (Thm.concl th3)] CONJ_CONG
          (* ~MEM h t /\ ALL_DISTINCT t = something /\ rhs *)
          val th5 = Thm.MP (Thm.MP th4 th2) th3
          val th6 = Thm.TRANS th1 th5
        in
          if boolSyntax.rhs (Thm.concl th3) = boolSyntax.T then
            Thm.TRANS th6 (Thm.SPEC (boolSyntax.rhs (Thm.concl th2)) AND_T)
          else
            th6
        end
    end
    val thm = all_distinct_conv tm
  in
    if swap then
      thm
    else
      (* get rid of parentheses *)
      let
        val conj = boolSyntax.rhs (Thm.concl thm)
        val conj' = boolSyntax.list_mk_conj (boolSyntax.strip_conj conj)
      in
        Thm.TRANS thm (Drule.CONJUNCTS_AC (conj, conj'))
      end
  end
  handle Feedback.HOL_ERR _ =>
    raise Conv.UNCHANGED

  (* replaces distinct if-then-else terms by distinct variables;
     returns the generalized term and a map from ite-subterms to
     variables (treating anything but combinations as atomic, i.e.,
     this function does NOT descend into lambda-abstractions) *)
  fun generalize_ite t =
  let 
    fun aux (dict, t) =
      if boolSyntax.is_cond t then (
        case Redblackmap.peek (dict, t) of
          SOME var =>
          (dict, var)
        | NONE =>
          let
            val var = Term.genvar (Term.type_of t)
          in
            (Redblackmap.insert (dict, t, var), var)
          end
      ) else (
        let
          val (l, r) = Term.dest_comb t
          val (dict, l) = aux (dict, l)
          val (dict, r) = aux (dict, r)
        in
          (dict, Term.mk_comb (l, r))
        end
        handle Feedback.HOL_ERR _ =>
          (* 't' is not a combination *)
          (dict, t)
      )
  in
    aux (Redblackmap.mkDict Term.compare, t)
  end

  (***************************************************************************)
  (* implementation of Z3's inference rules                                  *)
  (***************************************************************************)

  (* The Z3 documentation is rather outdated (as of version 2.11) and
     imprecise with respect to the semantics of Z3's inference rules.
     Ultimately, the most reliable way to determine the semantics is
     by observation: I applied Z3 to a large collection of SMT-LIB
     benchmarks, and from the resulting proofs I inferred what each
     inference rule does.  Therefore the implementation below may not
     cover rare corner cases that were not exercised by any benchmark
     in the collection. *)

  fun z3_and_elim (state, thm, t) =
    (state, Library.conj_elim (thm, t))

  fun z3_asserted (state, t) =
    (state_assert state t, Thm.ASSUME t)

  fun z3_commutativity (state, t) =
  let
    val (x, y) = boolSyntax.dest_eq (boolSyntax.lhs t)
  in
    (state, Drule.ISPECL [x, y] boolTheory.EQ_SYM_EQ)
  end

  (* Instances of Tseitin-style propositional tautologies:
     (or (not (and p q)) p)
     (or (not (and p q)) q)
     (or (and p q) (not p) (not q))
     (or (not (or p q)) p q)
     (or (or p q) (not p))
     (or (or p q) (not q))
     (or (not (iff p q)) (not p) q)
     (or (not (iff p q)) p (not q))
     (or (iff p q) (not p) (not q))
     (or (iff p q) p q)
     (or (not (ite a b c)) (not a) b)
     (or (not (ite a b c)) a c)
     (or (ite a b c) (not a) (not b))
     (or (ite a b c) a (not c))
     (or (not (not a)) (not a))
     (or (not a) a)

     Also
     (or p (= x (ite p y x)))

     Also
     ~ALL_DISTINCT [x; y; z] \/ (x <> y /\ x <> z /\ y <> z)

     There is a complication: 't' may contain arbitarily many
     irrelevant (nested) conjuncts/disjuncts, i.e.,
     conjunction/disjunction in the above tautologies can be of
     arbitrary arity.

     For the most part, 'z3_def_axiom' could be implemented by a
     single call to TAUT_PROVE.  The (partly less general)
     implementation below, however, is considerably faster.
  *)
  fun z3_def_axiom (state, t) =
    (state, Z3_ProformaThms.prove Z3_ProformaThms.def_axiom_thms t)
    handle Feedback.HOL_ERR _ =>
    (* or (or ... p ...) (not p) *)
    (* or (or ... (not p) ...) p *)
    (state, Library.gen_excluded_middle t)
    handle Feedback.HOL_ERR _ =>
    (* (or (not (and ... p ...)) p) *)
    let
      val (lhs, rhs) = boolSyntax.dest_disj t
      val conj = boolSyntax.dest_neg lhs
      (* conj |- rhs *)
      val thm = Library.conj_elim (Thm.ASSUME conj, rhs)  (* may fail *)
    in
      (* |- lhs \/ rhs *)
      (state, Drule.IMP_ELIM (Thm.DISCH conj thm))
    end
    handle Feedback.HOL_ERR _ =>
    (* ~ALL_DISTINCT [x; y; z] \/ x <> y /\ x <> z /\ y <> z *)
    let
      val (not_all_distinct, _) = boolSyntax.dest_disj t
      val all_distinct = boolSyntax.dest_neg not_all_distinct
      val all_distinct_th = ALL_DISTINCT_CONV false all_distinct
        handle Conv.UNCHANGED =>
          raise ERR "z3_def_axiom" ""
    in
      (state, Drule.IMP_ELIM (Lib.fst (Thm.EQ_IMP_RULE all_distinct_th)))
    end

  (* (!x y z. P) = P *)
  fun z3_elim_unused (state, t) =
  let
    val (lhs, rhs) = boolSyntax.dest_eq t
    fun strip_some_foralls forall =
    let
      val (var, body) = boolSyntax.dest_forall forall
      val th1 = Thm.DISCH forall (Thm.SPEC var (Thm.ASSUME forall))
      val th2 = Thm.DISCH body (Thm.GEN var (Thm.ASSUME body))
      val strip_th = Drule.IMP_ANTISYM_RULE th1 th2
    in
      if body = rhs then
        strip_th  (* stripped enough quantifiers *)
      else
        Thm.TRANS strip_th (strip_some_foralls body)
      end
  in
    (state, strip_some_foralls lhs)
  end

  (* introduces a local hypothesis (which must be discharged by
     'z3_lemma' at some later point in the proof) *)
  fun z3_hypothesis (state, t) =
    (state, Thm.ASSUME t)

  (*  [l1, ..., ln] |- F
     --------------------
     |- ~l1 \/ ... \/ ~ln

     'z3_lemma' could be implemented (essentially) by a single call to
     'TAUT_PROVE'.  The (less general) implementation below, however,
     is considerably faster. *)
  fun z3_lemma (state, thm, t) =
  let
    fun prove_literal maybe_no_hyp (th, lit) =
    let
      val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
        handle Feedback.HOL_ERR _ => (false, boolSyntax.mk_neg lit)
    in
      if maybe_no_hyp orelse HOLset.member (Thm.hypset th, neg_lit) then
        let
          val concl = Thm.concl th
          val th1 = Thm.DISCH neg_lit th
        in
          if is_neg then (
            if concl = boolSyntax.F then
              (* [...] |- ~neg_lit *)
              Thm.NOT_INTRO th1
            else
              (* [...] |- ~neg_lit \/ concl *)
              Thm.MP (Drule.SPECL [neg_lit, concl] IMP_DISJ_1) th1
          ) else
            if concl = boolSyntax.F then
              (* [...] |- lit *)
              Thm.MP (Thm.SPEC lit IMP_FALSE) th1
            else
              (* [...] |- lit \/ concl *)
              Thm.MP (Drule.SPECL [lit, concl] IMP_DISJ_2) th1
        end
      else
        raise ERR "z3_lemma" ""
    end
    fun prove (th, disj) =
      prove_literal false (th, disj)
        handle Feedback.HOL_ERR _ =>
          let
            val (l, r) = boolSyntax.dest_disj disj
          in
            (* We do NOT break 'l' apart recursively (because that would be
               slightly tricky to implement, and require associativity of
               disjunction).  Thus, 't' must be parenthesized to the right
               (e.g., "l1 \/ (l2 \/ l3)"). *)
            prove_literal true (prove (th, r), l)
          end
  in
    (state, prove (thm, t))
  end

  fun z3_monotonicity (state, thms, t) =
    (state,
      let
        val l_r_thms = List.map (fn thm =>
          (boolSyntax.dest_eq (Thm.concl thm), thm)) thms
        fun make_equal (l, r) =
          Thm.ALPHA l r
          handle Feedback.HOL_ERR _ =>
            Lib.tryfind (fn ((l', r'), thm) =>
              Thm.TRANS (Thm.ALPHA l l') (Thm.TRANS thm (Thm.ALPHA r' r))
                handle Feedback.HOL_ERR _ =>
                  Thm.TRANS (Thm.ALPHA l r')
                    (Thm.TRANS (Thm.SYM thm) (Thm.ALPHA l' r))) l_r_thms
          handle Feedback.HOL_ERR _ =>
            let
              val (l_op, l_arg) = Term.dest_comb l
              val (r_op, r_arg) = Term.dest_comb r
            in
              Thm.MK_COMB (make_equal (l_op, r_op), make_equal (l_arg, r_arg))
            end
      in
        make_equal (boolSyntax.dest_eq t)
      end)

  fun z3_mp (state, thm1, thm2, t) =
    (state, Thm.MP thm2 thm1 handle Feedback.HOL_ERR _ => Thm.EQ_MP thm2 thm1)

  (* ~(... \/ p \/ ...)
     ------------------
             ~p         *)
  fun z3_not_or_elim (state, thm, t) =
  let
    val (is_neg, neg_t) = (true, boolSyntax.dest_neg t)
      handle Feedback.HOL_ERR _ =>
        (false, boolSyntax.mk_neg t)
    val disj = boolSyntax.dest_neg (Thm.concl thm)
    (* neg_t |- disj *)
    val th1 = Library.disj_intro (Thm.ASSUME neg_t, disj)
    (* |- ~disj ==> ~neg_t *)
    val th1 = Drule.CONTRAPOS (Thm.DISCH neg_t th1)
    (* |- ~neg_t *)
    val th1 = Thm.MP th1 thm
  in
    (state, if is_neg then th1 else Thm.MP (Thm.SPEC t NOT_NOT_ELIM) th1)
  end

  (*         P = Q
     ---------------------
     (!x. P x) = (!y. Q y) *)
  fun z3_quant_intro (state, thm, t) =
  let
    val (lhs, rhs) = boolSyntax.dest_eq t
    val (bvars, _) = boolSyntax.strip_forall lhs
    (* P may be a quantified proposition itself; only retain *new*
       quantifiers *)
    val (P, _) = boolSyntax.dest_eq (Thm.concl thm)
    val bvars = List.take (bvars, List.length bvars -
      List.length (Lib.fst (boolSyntax.strip_forall P)))
    (* P and Q in the conclusion may require variable renaming to match
       the premise -- we only look at P and hope Q will come out right *)
    fun strip_some_foralls 0 term =
      term
      | strip_some_foralls n term =
      strip_some_foralls (n - 1) (Lib.snd (boolSyntax.dest_forall term))
    val len = List.length bvars
    val (tmsubst, _) = Term.match_term P (strip_some_foralls len lhs)
    val thm = Thm.INST tmsubst thm
    (* add quantifiers (on both sides) *)
    val thm = List.foldr (fn (bvar, th) => Drule.FORALL_EQ bvar th)
      thm bvars
    (* rename bvars on rhs if necessary *)
    val (_, intermediate_rhs) = boolSyntax.dest_eq (Thm.concl thm)
    val thm = Thm.TRANS thm (Thm.ALPHA intermediate_rhs rhs)
  in
    (state, thm)
  end

  fun z3_symm (state, thm, t) =
    (state, Thm.SYM thm)

  fun th_lemma_wrapper (name : string)
    (th_lemma_implementation : Term.term -> Thm.thm * (Thm.thm -> Thm.thm))
    (state, thms, t) : state * Thm.thm =
  let
    val t' = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
    val (state, thm) = (* proforma theorems *)
      (state, Profile.profile ("th_lemma[" ^ name ^ "](proforma)") (fn () =>
          Z3_ProformaThms.prove Z3_ProformaThms.th_lemma_thms t') ()
        handle Feedback.HOL_ERR _ =>
          (* cached theorems *)
          Profile.profile ("th_lemma[" ^ name ^ "](cache)") (fn () =>
            state_inst_cached_thm state t') ())
      handle Feedback.HOL_ERR _ =>
        let
          val (cache_thm, post_fn) = th_lemma_implementation t'
        in
          (* cache result theorem, apply 'post_fn' to it *)
          (state_cache_thm state cache_thm, post_fn cache_thm)
        end
  in
    (state, Drule.LIST_MP thms thm)
  end

  val z3_th_lemma_arith = th_lemma_wrapper "arith" (fn t =>
    let
      val (dict, gen_t) = generalize_ite t
      val thm = if term_contains_real_ty gen_t then
          (* this is just a heuristic - it is quite conceivable that a
             term that contains type real is provable by integer
             arithmetic *)
          Profile.profile "th_lemma[arith](real)" realLib.REAL_ARITH gen_t
        else
          Profile.profile "th_lemma[arith](int)" intLib.ARITH_PROVE gen_t
      val subst = List.map (fn (term, var) => {redex = var, residue = term})
        (Redblackmap.listItems dict)
    in
      (thm, Thm.INST subst)
    end)

  val z3_th_lemma_array = th_lemma_wrapper "array" (fn t =>
    (Profile.profile "th_lemma[array](simp)" (fn () =>
      simpLib.SIMP_PROVE update_ss [] t) (), Lib.I))

  val z3_th_lemma_basic = th_lemma_wrapper "basic" (fn t =>
    raise ERR "th_lemma[basic]" "")

  val z3_th_lemma_bv =
  let
    val COND_SIMP_TAC = simpLib.SIMP_TAC simpLib.empty_ss
      [boolTheory.COND_RAND, boolTheory.COND_RATOR]
    val TAC = Tactical.THEN (Profile.profile "COND_SIMP_TAC" COND_SIMP_TAC,
      Profile.profile "BBLAST_TAC" blastLib.BBLAST_TAC)
  in
    th_lemma_wrapper "bv" (fn t =>
      Profile.profile "th_lemma[bv](bblast)" (fn () =>
        (Tactical.prove (t, TAC), Lib.I)) ()
      handle Empty => raise ERR "th_lemma[bv]" "bblast: Empty")  (*TODO*)
  end

(* TODO
  fun old_th_lemma_arith (state, thms, t) =
  let
    val concl = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
  in
    let val (dict, concl) = generalize_ite concl
        handle Feedback.HOL_ERR _ =>

          (*TODO*) Profile.profile "th_lemma(WORD_ARITH_CONV)" (fn () =>
          Drule.EQT_ELIM (wordsLib.WORD_ARITH_CONV concl)
            handle Conv.UNCHANGED =>
              raise (Feedback.mk_HOL_ERR "" "" "")) ()
        handle Feedback.HOL_ERR _ =>

          (*TODO*) Profile.profile "th_lemma(WORD_BIT_EQ)" (fn () =>
          Drule.EQT_ELIM (Conv.THENC (simpLib.SIMP_CONV (simpLib.++
            (simpLib.++ (bossLib.std_ss, wordsLib.WORD_ss),
            wordsLib.WORD_BIT_EQ_ss)) [],
            tautLib.TAUT_CONV) concl)) ()
        handle Feedback.HOL_ERR _ =>

          (*TODO*) Profile.profile "th_lemma(WORD_DECIDE)"
            wordsLib.WORD_DECIDE concl
        handle Feedback.HOL_ERR _ =>

          (*TODO*) Profile.profile "th_lemma(WORD_DP)" (fn () =>
          wordsLib.WORD_DP (bossLib.SIMP_CONV (bossLib.++
            (bossLib.srw_ss(), wordsLib.WORD_EXTRACT_ss)) [])
            (Drule.EQT_ELIM o (bossLib.SIMP_CONV bossLib.arith_ss [])) concl) ()
(*
        handle Feedback.HOL_ERR _ =>

          (*TODO*) Profile.profile "th_lemma(BBLAST_TAC)"
            Tactical.prove (concl, blastLib.BBLAST_TAC)
*)
        val subst = List.map (fn (term, var) =>
          {redex = var, residue = term}) (Redblackmap.listItems dict)
    in
      (state_cache_thm state th, Drule.LIST_MP thms (Thm.INST subst th))
    end
  end
*)

  fun z3_trans (state, thm1, thm2, t) =
    (state, Thm.TRANS thm1 thm2)

  fun z3_true_axiom (state, t) =
    (state, boolTheory.TRUTH)

  (* l1 \/ l2 \/ ... \/ ln \/ t   ~l1   ~l2   ...   ~ln
     --------------------------------------------------
                              t

     The input clause (including "t") is really treated as a set of
     literals: the resolvents need not be in the correct order, "t"
     need not be the rightmost disjunct (and if "t" is a disjunction,
     its disjuncts may even be spread throughout the input clause).
     Note also that "t" may be F, in which case it need not be present
     in the input clause.

     We treat all "~li" as atomic, even if they are negated
     disjunctions. *)
  fun z3_unit_resolution (state, thms, t) =
  let
    val _ = if List.null thms then
        raise ERR "" ""  (* to be handled below *)
      else ()
    fun disjuncts dict (disj, thm) =
    let
      val (l, r) = boolSyntax.dest_disj disj
      (* |- l \/ r ==> ... *)
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
    (* derive 't' from each negated resolvent *)
    val dict = List.foldl (fn (th, dict) =>
      let
        val lit = Thm.concl th
        val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
          handle Feedback.HOL_ERR _ =>
            (false, boolSyntax.mk_neg lit)
        (* |- neg_lit ==> F *)
        val th = if is_neg then
            Thm.NOT_ELIM th
          else
            Thm.MP (Thm.SPEC lit NOT_FALSE) th
        (* neg_lit |- t *)
        val th = Thm.CCONTR t (Thm.MP th (Thm.ASSUME neg_lit))
      in
        Redblackmap.insert (dict, neg_lit, th)
      end) dict (List.tl thms)
    (* derive 't' from ``F`` (just in case ``F`` is a disjunct) *)
    val dict = Redblackmap.insert
      (dict, boolSyntax.F, Thm.CCONTR t (Thm.ASSUME boolSyntax.F))
    val clause = Thm.concl (List.hd thms)
    val clause_imp_t = prove_from_disj dict clause
  in
    (state, Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms))
  end

  fun z3_rewrite (state, t) =
  let
    val (l, r) = boolSyntax.dest_eq t
  in
    if l = r then
      (state, Thm.REFL l)
    else
      (* proforma theorems *)
      (*Profile.profile "rewrite(proforma)"*) (fn () =>
        (state, Z3_ProformaThms.prove Z3_ProformaThms.rewrite_thms t)) ()
      handle Feedback.HOL_ERR _ =>

      (* re-ordering conjunctions and disjunctions *)
      (if boolSyntax.is_conj l then
        (state, (*Profile.profile "rewrite(conj)"*) rewrite_conj (l, r))
      else if boolSyntax.is_disj l then
        (state, (*Profile.profile "rewrite(disj)"*) rewrite_disj (l, r))
      else
        raise (Feedback.mk_HOL_ERR "" "" ""))
      handle Feedback.HOL_ERR _ =>

      (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn) *)
      (* Note that p <=> q may be negated to q <=> ~p. *)
      (*Profile.profile "rewrite(nnf)"*) (fn () =>
        let val disj = boolSyntax.dest_neg r
            val disj_th = Thm.ASSUME disj
            val conj_ths = Drule.CONJUNCTS (Thm.ASSUME l)
            (* (p <=> q) ==> ~(q <=> ~p) *)
            val neg_iffs = List.mapPartial (Lib.total (fn th =>
              let val (p, q, ty) = boolSyntax.dest_eq_ty (Thm.concl th)
                  val _ = (ty = Type.bool) orelse
                    raise (Feedback.mk_HOL_ERR "" "" "")
              in
                Thm.MP (Drule.SPECL [p, q] NEG_IFF_1) th
              end)) conj_ths
            val (state, False) = z3_unit_resolution
              (state, disj_th :: conj_ths @ neg_iffs, boolSyntax.F)

            fun disjuncts dict (thmfun, concl) =
              let val (l, r) = boolSyntax.dest_disj concl
              in
                disjuncts (disjuncts dict (fn th => thmfun (Thm.DISJ1 th r),
                  l)) (fn th => thmfun (Thm.DISJ2 l th), r)
              end
              handle Feedback.HOL_ERR _ =>
                let (* |- concl ==> disjunction *)
                    val th = Thm.DISCH concl (thmfun (Thm.ASSUME concl))
                    (* ~disjunction |- ~concl *)
                    val th = Drule.UNDISCH (Drule.CONTRAPOS th)
                    val th = let val neg_concl = boolSyntax.dest_neg concl
                      in
                        Thm.MP (Thm.SPEC neg_concl NOT_NOT_ELIM) th
                      end
                      handle Feedback.HOL_ERR _ =>
                        th
                    val dict = Redblackmap.insert (dict, Thm.concl th, th)
                    (* ~(p <=> ~q) ==> (q <=> p) *)
                    val dict = let val (p, neg_q) = boolSyntax.dest_eq
                      (boolSyntax.dest_neg (Thm.concl th))
                                   val q = boolSyntax.dest_neg neg_q
                                   val th = Thm.MP (Drule.SPECL [p, q]
                                     NEG_IFF_2) th
                               in
                                 Redblackmap.insert (dict, Thm.concl th, th)
                               end
                               handle Feedback.HOL_ERR _ =>
                                 dict
                in
                  dict
                end
            fun prove dict conj =
              Redblackmap.find (dict, conj)
                handle Redblackmap.NotFound =>
                  let val (l, r) = boolSyntax.dest_conj conj
                  in
                    Thm.CONJ (prove dict l) (prove dict r)
                  end
            val empty = Redblackmap.mkDict Term.compare
            val dict = disjuncts empty (Lib.I, disj)
            val r_imp_l = Thm.DISCH r (prove dict l)
            val l_imp_r = Thm.DISCH l (Thm.NOT_INTRO (Thm.DISCH disj False))
        in
          (state, Drule.IMP_ANTISYM_RULE l_imp_r r_imp_l)
        end) ()
      handle Feedback.HOL_ERR _ =>

      (* ALL_DISTINCT [x, y, z] = ... *)
      (*Profile.profile "rewrite(all_distinct)"*) (fn () =>
        let val l_eq_l' = ALL_DISTINCT_CONV true l
              handle Conv.UNCHANGED =>
                raise (Feedback.mk_HOL_ERR "" "" "")
            val r_eq_r' = ALL_DISTINCT_CONV true r
              handle Conv.UNCHANGED =>
                Thm.REFL r
            val l' = boolSyntax.rhs (Thm.concl l_eq_l')
            val r' = boolSyntax.rhs (Thm.concl r_eq_r')
            val l'_eq_r' = Drule.CONJUNCTS_AC (l', r')
        in
          (state, Thm.TRANS (Thm.TRANS l_eq_l' l'_eq_r') (Thm.SYM r_eq_r'))
        end) ()
      handle Feedback.HOL_ERR _ =>

      (state, (*Profile.profile "rewrite(TAUT_PROVE)"*) tautLib.TAUT_PROVE t)
      handle Feedback.HOL_ERR _ =>

      (state, (*Profile.profile "rewrite(update)"*) (fn () =>
        simpLib.SIMP_PROVE update_ss [] t) ())
      handle Feedback.HOL_ERR _ =>

      (state, (*Profile.profile "rewrite(cache)"*) (fn () =>
        state_inst_cached_thm state t) ())
      handle Feedback.HOL_ERR _ =>

      let val th = if term_contains_real_ty t then
              (*Profile.profile "rewrite(REAL_ARITH)"*) realLib.REAL_ARITH t
            else
              (*Profile.profile "rewrite(ARITH_PROVE)"*) intLib.ARITH_PROVE t
          handle Feedback.HOL_ERR _ =>

            (*TODO*) Profile.profile "rewrite(WORD_ARITH_CONV)" (fn () =>
            Drule.EQT_ELIM (wordsLib.WORD_ARITH_CONV t)
              handle Conv.UNCHANGED =>
                raise (Feedback.mk_HOL_ERR "" "" "")) ()
          handle Feedback.HOL_ERR _ =>

            (*TODO*) Profile.profile "rewrite(WORD_BIT_EQ)" (fn () =>
            Drule.EQT_ELIM (Conv.THENC (simpLib.SIMP_CONV (simpLib.++
              (simpLib.++ (bossLib.std_ss, wordsLib.WORD_ss),
              wordsLib.WORD_BIT_EQ_ss)) [],
              tautLib.TAUT_CONV) t)) ()
          handle Feedback.HOL_ERR _ =>

            (*TODO*) Profile.profile "rewrite(WORD_DECIDE)"
              wordsLib.WORD_DECIDE t
          handle Feedback.HOL_ERR _ =>

            (*TODO*) Profile.profile "rewrite(WORD_DP)" (fn () =>
            wordsLib.WORD_DP (bossLib.SIMP_CONV (bossLib.++
              (bossLib.srw_ss(), wordsLib.WORD_EXTRACT_ss)) [])
              (Drule.EQT_ELIM o (bossLib.SIMP_CONV bossLib.arith_ss [])) t) ()
(*
          handle Feedback.HOL_ERR _ =>

            (*TODO*) Profile.profile "rewrite(BBLAST_TAC)"
              Tactical.prove (t, blastLib.BBLAST_TAC)
*)
      in
        (state_cache_thm state th, th)
      end
    end

  (* end of inference rule implementations *)

  (***************************************************************************)

  fun check_thm (name, thm, concl) =
  (
    if !SolverSpec.trace > 0 andalso Thm.concl thm <> concl then
      (*TODO: WARNING*) raise ERR "check_thm"
        (name ^ ": conclusion is " ^ Hol_pp.term_to_string (Thm.concl thm) ^
        ", expected: " ^ Hol_pp.term_to_string concl)
    else ();
    if !SolverSpec.trace > 2 then
      Feedback.HOL_MESG
        ("HolSmtLib: " ^ name ^ " proved: " ^ Hol_pp.thm_to_string thm)
    else ()
  )

  fun zero_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * Term.term -> state * Thm.thm)
      (concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
  let
    val (state, thm) = Profile.profile name z3_rule_fn (state, concl)
      handle Feedback.HOL_ERR _ =>
        raise ERR name (Hol_pp.term_to_string concl)
    val _ = Profile.profile "check_thm" check_thm (name, thm, concl)
  in
    continuation ((state, proof), thm)
  end

  fun one_prem (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm * Term.term -> state * Thm.thm)
      (pt : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt) (continuation o
      (fn ((state, proof), thm) =>
        let
          val (state, thm) = Profile.profile name z3_rule_fn (state, thm, concl)
            handle Feedback.HOL_ERR _ =>
              raise ERR name (Hol_pp.thm_to_string thm ^ ", " ^
                Hol_pp.term_to_string concl)
          val _ = Profile.profile "check_thm" check_thm (name, thm, concl)
        in
          ((state, proof), thm)
        end))

  and two_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm * Thm.thm * Term.term -> state * Thm.thm)
      (pt1 : proofterm, pt2 : proofterm, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt1) (continuation o
      (fn (state_proof, thm1) =>
        thm_of_proofterm (state_proof, pt2) (fn ((state, proof), thm2) =>
          let
            val (state, thm) = Profile.profile name z3_rule_fn
              (state, thm1, thm2, concl)
                handle Feedback.HOL_ERR _ =>
                  raise ERR name (Hol_pp.thm_to_string thm1 ^ ", " ^
                    Hol_pp.thm_to_string thm2 ^ ", " ^
                    Hol_pp.term_to_string concl)
            val _ = Profile.profile "check_thm" check_thm (name, thm, concl)
          in
            ((state, proof), thm)
          end)))

  and list_prems (state : state, proof : proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm list * Term.term -> state * Thm.thm)
      ([] : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : Thm.thm list)
      : (state * proof) * Thm.thm =
    let
      val acc = List.rev acc
      val (state, thm) = Profile.profile name z3_rule_fn (state, acc, concl)
        handle Feedback.HOL_ERR _ =>
          raise ERR name ("[" ^ String.concatWith ", " (List.map
            Hol_pp.thm_to_string acc) ^ "], " ^ Hol_pp.term_to_string concl)
      val _ = Profile.profile "check_thm" check_thm (name, thm, concl)
    in
      continuation ((state, proof), thm)
    end
    | list_prems (state_proof : state * proof)
      (name : string)
      (z3_rule_fn : state * Thm.thm list * Term.term -> state * Thm.thm)
      (pt :: pts : proofterm list, concl : Term.term)
      (continuation : (state * proof) * Thm.thm -> (state * proof) * Thm.thm)
      (acc : Thm.thm list)
      : (state * proof) * Thm.thm =
    thm_of_proofterm (state_proof, pt) (fn (state_proof, thm) =>
      list_prems state_proof name z3_rule_fn (pts, concl) continuation
        (thm :: acc))

  and thm_of_proofterm (state_proof, AND_ELIM x) continuation =
        one_prem state_proof "and_elim" z3_and_elim x continuation
    | thm_of_proofterm (state_proof, ASSERTED x) continuation =
        zero_prems state_proof "asserted" z3_asserted x continuation
    | thm_of_proofterm (state_proof, COMMUTATIVITY x) continuation =
        zero_prems state_proof "commutativity" z3_commutativity x continuation
    | thm_of_proofterm (state_proof, DEF_AXIOM x) continuation =
        zero_prems state_proof "def_axiom" z3_def_axiom x continuation
    | thm_of_proofterm (state_proof, ELIM_UNUSED x) continuation =
        zero_prems state_proof "elim_unused" z3_elim_unused x continuation
    | thm_of_proofterm (state_proof, HYPOTHESIS x) continuation =
        zero_prems state_proof "hypothesis" z3_hypothesis x continuation
    | thm_of_proofterm (state_proof, LEMMA x) continuation =
        one_prem state_proof "lemma" z3_lemma x continuation
    | thm_of_proofterm (state_proof, MONOTONICITY x) continuation =
        list_prems state_proof "monotonicity" z3_monotonicity x continuation []
    | thm_of_proofterm (state_proof, MP x) continuation =
        two_prems state_proof "mp" z3_mp x continuation
    | thm_of_proofterm (state_proof, NOT_OR_ELIM x) continuation =
        one_prem state_proof "not_or_elim" z3_not_or_elim x continuation
    | thm_of_proofterm (state_proof, QUANT_INTRO x) continuation =
        one_prem state_proof "quant_intro" z3_quant_intro x continuation
    | thm_of_proofterm (state_proof, REWRITE x) continuation =
        zero_prems state_proof "rewrite" z3_rewrite x continuation
    | thm_of_proofterm (state_proof, SYMM x) continuation =
        one_prem state_proof "symm" z3_symm x continuation
    | thm_of_proofterm (state_proof, TH_LEMMA_ARITH x) continuation =
        list_prems state_proof "th_lemma[arith]" z3_th_lemma_arith x
          continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_ARRAY x) continuation =
        list_prems state_proof "th_lemma[array]" z3_th_lemma_array x
          continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BASIC x) continuation =
        list_prems state_proof "th_lemma[basic]" z3_th_lemma_basic x
          continuation []
    | thm_of_proofterm (state_proof, TH_LEMMA_BV x) continuation =
        list_prems state_proof "th_lemma[bv]" z3_th_lemma_bv x continuation []
    | thm_of_proofterm (state_proof, TRANS x) continuation =
        two_prems state_proof "trans" z3_trans x continuation
    | thm_of_proofterm (state_proof, TRUE_AXIOM x) continuation =
        zero_prems state_proof "true_axiom" z3_true_axiom x continuation
    | thm_of_proofterm (state_proof, UNIT_RESOLUTION x) continuation =
        list_prems state_proof "unit_resolution" z3_unit_resolution x
          continuation []
    | thm_of_proofterm ((state, proof), ID id) continuation =
        (case Redblackmap.peek (proof, id) of
          SOME (THEOREM thm) =>
            continuation ((state, proof), thm)
        | SOME pt =>
            thm_of_proofterm ((state, proof), pt) (continuation o
              (* update the proof, replacing the original proofterm with
                 the theorem just derived *)
              (fn ((state, proof), thm) =>
                (
                  if !SolverSpec.trace > 2 then
                    Feedback.HOL_MESG
                      ("HolSmtLib: updating proof at ID " ^ Int.toString id)
                  else ();
                  ((state, Redblackmap.insert (proof, id, THEOREM thm)), thm)
                )))
        | NONE =>
            raise ERR "thm_of_proofterm"
              ("proof has no proofterm for ID " ^ Int.toString id))
    | thm_of_proofterm (state_proof, THEOREM thm) continuation =
        continuation (state_proof, thm)

in

  fun check_proof proof : Thm.thm =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: checking Z3 proof"
      else ()

    (* initial state *)
    val state = {
      asserted_hyps = Term.empty_tmset,
      skolem_defs = [],
      thm_cache = Net.empty
    }

    (* ID 0 denotes the proof's root node *)
    val ((state, _), thm) = thm_of_proofterm ((state, proof), ID 0) Lib.I

    val _ = if !SolverSpec.trace > 0 andalso Thm.concl thm <> boolSyntax.F then
        WARNING "check_proof" "final conclusion is not 'F'"
      else ()

    (* eliminate Skolemization hypotheses "sk = def" (cf. function
       'z3_sk' above), assuming that sk does not occur anywhere else
       in 'thm' *)
    val thm = (*Profile.profile "check_proof(skolem_defs)"*) (fn () =>
      List.foldl (fn (sk_def, thm) =>
        let
          val (sk, def) = boolSyntax.dest_eq sk_def
          val thm = Thm.INST [{redex = sk, residue = def}] thm
          val def_thm = Thm.REFL def
          val _ = if !SolverSpec.trace > 0 andalso
                not (HOLset.member (Thm.hypset thm, Thm.concl def_thm)) then
              WARNING "check_proof" "Skolem hypothesis not found"
            else ()
        in
          Drule.PROVE_HYP def_thm thm
        end) thm (#skolem_defs state)) ()

    (* check that the final theorem contains no hyps other than those
       that have been asserted *)
    val _ = (*Profile.profile "check_proof(hypcheck)"*) (fn () =>
      if !SolverSpec.trace > 0 andalso
          not (HOLset.isSubset (Thm.hypset thm, #asserted_hyps state)) then
        WARNING "check_proof" "final theorem contains additional hyp(s)"
      else ()) ()
  in
    thm
  end

end  (* local *)

end
