(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: replaying Z3's proofs in HOL *)

structure Z3_ProofReplay =
struct

  open Z3_Proof

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

  val update_ss = simpLib.&& (simpLib.++ (intSimps.int_ss,
      simpLib.std_conv_ss {name = "word_EQ_CONV", pats = [``(x :'a word) = y``],
        conv = wordsLib.word_EQ_CONV}),
    [combinTheory.UPDATE_def, boolTheory.EQ_SYM_EQ])

  fun check_proof prf =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: checking Z3 proof"
      else ()

    (*** references storing "global" state ***)
    (* stores definitions "sk = ..." (where sk is a variable) introduced for
       Skolemization; these are eliminated at the end of proof reconstruction *)
    val skolem_defs = ref ([] : Term.term list)
    (* stores assumptions, (only) these may remain in the final theorem *)
    val asserted_hyps = ref Term.empty_tmset
    (* stores certain theorems (proved by 'rewrite' or 'th_lemma') for later
       retrieval, to avoid re-reproving them *)
    val theorem_cache = ref Net.empty

    fun cache_theorem th =
      theorem_cache := Net.insert (Thm.concl th, th) (!theorem_cache)

    (*** auxiliary functions ***)
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
        List.exists (fn ty => ty = realSyntax.real_ty)
          (strip_fun_tys (Term.type_of tm))
    (* returns "|- l = r", provided 'l' and 'r' are conjunctions that can be
       obtained from each other using associativity, commutativity and
       idempotence of conjunction, and identity of "T" wrt. conjunction.

       If 'r' is "F", 'l' must either contain "F" as a conjunct, or 'l'
       must contain both a literal and its negation.
    *)
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
          raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
            "rewrite_conj")
    (* returns "|- l = r", provided 'l' and 'r' are disjunctions that can be
       obtained from each other using associativity, commutativity and
       idempotence of disjunction, and identity of "F" wrt. disjunction.

       If 'r' is "T", 'l' must contain "T" as a disjunct, or 'l' must contain
       both a literal and its negation.
    *)
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
          raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
            "rewrite_disj")
    (* Returns "|- ALL_DISTINCT [x, y, z] = x <> y /\ x <> z /\ y <> z"; if
       'swap' is true, then each inequation "x <> y" is swapped to "y <> x" if
       y < x (according to Term.compare); if 'swap' is true, the resulting
       conjunction may contain parentheses; may raise Conv.UNCHANGED *)
    fun ALL_DISTINCT_CONV swap tm =
      let fun not_mem_conv tm =
            let val (x, list) = listSyntax.dest_mem (boolSyntax.dest_neg tm)
            in
              if listSyntax.is_nil list then
                (* |- ~MEM x [] = T *)
                Drule.ISPEC x NOT_MEM_NIL
              else
                let val (h, t) = listSyntax.dest_cons list
                    (* |- ~MEM x (h::t) = (x <> h) /\ ~MEM x t *)
                    val th1 = Drule.ISPECL [x, h, t] (if swap andalso
                      Term.compare (h, x) = LESS then
                        NOT_MEM_CONS_SWAP
                      else
                        NOT_MEM_CONS)
                    val (neq, notmem) = boolSyntax.dest_conj (boolSyntax.rhs
                      (Thm.concl th1))
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
            let val list = listSyntax.dest_all_distinct tm
            in
              if listSyntax.is_nil list then
                (* |- ALL_DISTINCT [] = T *)
                Thm.INST_TYPE [{redex = Type.alpha, residue =
                  listSyntax.dest_nil list}] ALL_DISTINCT_NIL
              else
                let val (h, t) = listSyntax.dest_cons list
                    (* |- ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t *)
                    val th1 = Drule.ISPECL [h, t] ALL_DISTINCT_CONS
                    val (notmem, alldistinct) = boolSyntax.dest_conj
                      (boolSyntax.rhs (Thm.concl th1))
                    (* |- ~MEM h t = something *)
                    val th2 = not_mem_conv notmem
                    (* |- ALL_DISTINCT t = rhs *)
                    val th3 = all_distinct_conv alldistinct
                    val th4 = Drule.SPECL [notmem, boolSyntax.rhs (Thm.concl
                      th2), alldistinct, boolSyntax.rhs (Thm.concl th3)]
                      CONJ_CONG
                    (* ~MEM h t /\ ALL_DISTINCT t = something /\ rhs *)
                    val th5 = Thm.MP (Thm.MP th4 th2) th3
                    val th6 = Thm.TRANS th1 th5
                in
                  if boolSyntax.rhs (Thm.concl th3) = boolSyntax.T then
                    Thm.TRANS th6 (Thm.SPEC (boolSyntax.rhs (Thm.concl th2))
                      AND_T)
                  else
                    th6
                end
            end
          val th1 = all_distinct_conv tm
      in
        if swap then
          th1
        else
          (* get rid of parentheses *)
          let val conj = boolSyntax.rhs (Thm.concl th1)
              val new = boolSyntax.list_mk_conj (boolSyntax.strip_conj conj)
              val th2 = Drule.CONJUNCTS_AC (conj, new)
          in
            Thm.TRANS th1 th2
          end
      end
      handle Feedback.HOL_ERR _ =>
        raise Conv.UNCHANGED
    (* replaces distinct if-then-else terms by distinct variables; returns the
       generalized term and a map from ite-subterms to variables; treats
       anything but combinations as atomic (i.e., does NOT descend into
       lambda-abstractions) *)
    fun generalize_ite t =
    let fun aux (dict, t) =
          if boolSyntax.is_cond t then
            (case Redblackmap.peek (dict, t) of
              SOME var =>
              (dict, var)
            | NONE =>
              let val var = Term.genvar (Term.type_of t)
              in
                (Redblackmap.insert (dict, t, var), var)
              end)
          else
            (let val (l, r) = Term.dest_comb t
                 val (dict, l) = aux (dict, l)
                 val (dict, r) = aux (dict, r)
             in
               (dict, Term.mk_comb (l, r))
             end
             handle Feedback.HOL_ERR _ =>
               (* 't' is not a combination *)
               (dict, t))
    in
      aux (Redblackmap.mkDict Term.compare, t)
    end

    (*** implementation of Z3's inference rules ***)
    fun and_elim (thm, t) =
      Library.conj_elim (thm, t)
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("and_elim: "
          ^ Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun asserted t =
      let val _ = asserted_hyps := HOLset.add (!asserted_hyps, t)
      in
        Thm.ASSUME t
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("asserted: "
          ^ Hol_pp.term_to_string t))
    fun commutativity t =
      let val (x, y) = boolSyntax.dest_eq (boolSyntax.lhs t)
      in
        Drule.ISPECL [x, y] boolTheory.EQ_SYM_EQ
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("commutativity: " ^ Hol_pp.term_to_string t))
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

       There is a complication: 't' may contain arbitarily many irrelevant
       (nested) conjuncts/disjuncts, i.e., conjunction/disjunction in the above
       tautologies can be of arbitrary arity.

       For the most part, 'def_axiom' could be implemented by a single call to
       TAUT_PROVE. The (partly less general) implementation below, however, is
       considerably faster.
    *)
    fun def_axiom t =
      Z3_ProformaThms.prove Z3_ProformaThms.def_axiom_thms t
      handle Feedback.HOL_ERR _ =>
      (* or (or ... p ...) (not p) *)
      (* or (or ... (not p) ...) p *)
      Library.gen_excluded_middle t
      handle Feedback.HOL_ERR _ =>
      (* (or (not (and ... p ...)) p) *)
      let val (lhs, rhs) = boolSyntax.dest_disj t
          val conj = boolSyntax.dest_neg lhs
          (* conj |- rhs *)
          val thm = Library.conj_elim (Thm.ASSUME conj, rhs)  (* may fail *)
      in
        (* |- lhs \/ rhs *)
        Drule.IMP_ELIM (Thm.DISCH conj thm)
      end
      handle Feedback.HOL_ERR _ =>
      (* ~ALL_DISTINCT [x; y; z] \/ x <> y /\ x <> z /\ y <> z *)
      let val (not_all_distinct, _) = boolSyntax.dest_disj t
          val all_distinct = boolSyntax.dest_neg not_all_distinct
          val all_distinct_th = ALL_DISTINCT_CONV false all_distinct
            handle Conv.UNCHANGED =>
              raise (Feedback.mk_HOL_ERR "" "" "")
      in
        Drule.IMP_ELIM (Lib.fst (Thm.EQ_IMP_RULE all_distinct_th))
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("def_axiom: "
          ^ Hol_pp.term_to_string t))
    fun elim_unused t =  (* (!x y z. P) = P *)
      let val (lhs, rhs) = boolSyntax.dest_eq t
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
        strip_some_foralls lhs
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("elim_unused: " ^ Hol_pp.term_to_string t))
    fun hypothesis t =
      Thm.ASSUME t
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("hypothesis: " ^ Hol_pp.term_to_string t))
    fun iff_false (thm, t) =
      Drule.EQF_INTRO thm
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("iff_false: "
          ^ Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun iff_true (thm, t) =
      Drule.EQT_INTRO thm
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("iff_true: "
          ^ Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    (*  [l1, ..., ln] |- F
       --------------------
       |- ~l1 \/ ... \/ ~ln

       'lemma' could be implemented by a single call to 'TAUT_PROVE'. The (less
       general) implementation below, however, is considerably faster.
    *)
    fun lemma (thm, t) =
    let fun prove_literal maybe_no_hyp (th, lit) =
          let val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
                handle Feedback.HOL_ERR _ => (false, boolSyntax.mk_neg lit)
          in
            if maybe_no_hyp orelse HOLset.member (Thm.hypset th, neg_lit) then
              let val concl = Thm.concl th
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
              raise (Feedback.mk_HOL_ERR "" "" "")
          end
        fun prove (th, disj) =
          prove_literal false (th, disj)
            handle Feedback.HOL_ERR _ =>
              let val (l, r) = boolSyntax.dest_disj disj
              in
                (* We do NOT break 'l' apart recursively (because that would be
                   slightly tricky to implement, and require associativity of
                   disjunction).  Thus, 't' must be parenthesized to the right
                   (e.g., "l1 \/ (l2 \/ l3)"). *)
                prove_literal true (prove (th, r), l)
              end
    in
      prove (thm, t)
    end
    handle Feedback.HOL_ERR _ =>
      raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("lemma: " ^
        Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun monotonicity (thms, t) =
      let val l_r_thms = List.map (fn thm =>
            (boolSyntax.dest_eq (Thm.concl thm), thm)) thms
          fun make_equal (l, r) =
            Thm.ALPHA l r
            handle Feedback.HOL_ERR _ =>
            Lib.tryfind (fn ((l', r'), thm) =>
              Thm.TRANS (Thm.ALPHA l l') (Thm.TRANS thm (Thm.ALPHA r' r))
              handle Feedback.HOL_ERR _ =>
              Thm.TRANS (Thm.ALPHA l r') (Thm.TRANS (Thm.SYM thm)
                (Thm.ALPHA l' r))) l_r_thms
            handle Feedback.HOL_ERR _ =>
            let val (l_op, l_arg) = Term.dest_comb l
                val (r_op, r_arg) = Term.dest_comb r
            in
              Thm.MK_COMB (make_equal (l_op, r_op), make_equal (l_arg, r_arg))
            end
      in
        make_equal (boolSyntax.dest_eq t)
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("monotonicity: " ^ String.concatWith ", " (List.map
          Hol_pp.thm_to_string thms) ^ ", " ^ Hol_pp.term_to_string t))
    fun mp (thm1, thm2, t) =
      Thm.MP thm2 thm1
      handle Feedback.HOL_ERR _ =>
        Thm.EQ_MP thm2 thm1
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("mp: " ^
          Hol_pp.thm_to_string thm1 ^ ", " ^ Hol_pp.thm_to_string thm2 ^ ", "
          ^ Hol_pp.term_to_string t))
    fun mp_tilde (thm1, thm2, t) =
      Thm.EQ_MP thm2 thm1
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("mp~: " ^
          Hol_pp.thm_to_string thm1 ^ ", " ^ Hol_pp.thm_to_string thm2 ^ ", " ^
          Hol_pp.term_to_string t))
    (*      |- ~s1 = r1  ...  |- ~sn = rn
       ---------------------------------------
       |- ~(s1 /\ ... /\ sn) = r1 \/ ... \/ rn

            |- ~s1 = r1  ...  |- ~sn = rn
       ---------------------------------------
       |- ~(s1 \/ ... \/ sn) = r1 /\ ... /\ rn

       |- ~s1 = r1  |- ~s2 = r2  |- s1 = r1'  |- s2 = r2'
       --------------------------------------------------
           |- ~(s1 = s2) = (r1 \/ r2) /\ (r1' \/ r2')

        |- s = r
       ----------
       |- ~~s = r

       'nnf_neg' could be implemented by a single call to 'TAUT_PROVE', but the
       (less general) implementation below is considerably faster.
    *)
    fun nnf_neg (thms, t) =
      let fun nnf_aux is_conj (thms, t) =
            let val _ = if List.null thms then
                    raise (Feedback.mk_HOL_ERR "" "" "")
                  else ()
                val th = List.hd thms
                val (neg_p, r) = boolSyntax.dest_eq (Thm.concl th)
            in
              if boolSyntax.dest_neg neg_p = t then
                (* |- ~t = r *)
                th
              else
                let val (p, q) = (if is_conj then boolSyntax.dest_conj else
                      boolSyntax.dest_disj) t
                    (* |- ~q = s *)
                    val q_th = nnf_aux is_conj (List.tl thms, q)
                    val s = boolSyntax.rhs (Thm.concl q_th)
                    val nnf_th = if is_conj then NNF_CONJ else NNF_DISJ
                in
                    (* |- ~t = r op s, where op is /\ or \/ *)
                    Thm.MP (Thm.MP (Drule.SPECL [p, q, r, s] nnf_th) th) q_th
                end
            end
          val neg_l = boolSyntax.dest_neg (boolSyntax.lhs t)
      in
        Thm.MP (Drule.SPECL [boolSyntax.dest_neg neg_l, boolSyntax.rhs t]
          NNF_NOT_NOT) (List.hd thms)
        handle Feedback.HOL_ERR _ =>
          nnf_aux (boolSyntax.is_conj neg_l) (thms, neg_l)
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("nnf_neg: " ^
          String.concatWith ", " (List.map Hol_pp.thm_to_string thms) ^ ", " ^
          Hol_pp.term_to_string t))
    fun nnf_pos (thms, t) =
      let val concl = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
          val th = tautLib.TAUT_PROVE concl
      in
        Drule.LIST_MP thms th
      end
      handle Feedback.HOL_ERR _ =>
        (if List.length thms = 1 then
           quant_intro (List.hd thms, t)
         else
           raise (Feedback.mk_HOL_ERR "" "" ""))
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("nnf_pos: " ^
          String.concatWith ", " (List.map Hol_pp.thm_to_string thms) ^ ", " ^
          Hol_pp.term_to_string t))
    (* ~(... \/ p \/ ...)
       ------------------
               ~p         *)
    and not_or_elim (thm, t) =
      let val (is_neg, neg_t) = (true, boolSyntax.dest_neg t)
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
        if is_neg then
          th1
        else
          Thm.MP (Thm.SPEC t NOT_NOT_ELIM) th1
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("not_or_elim: " ^ Hol_pp.thm_to_string thm ^ ", " ^
          Hol_pp.term_to_string t))
    (* (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))) *)
    and pull_quant t =
      Thm.REFL (boolSyntax.lhs t) (* TODO *)
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("pull_quant: " ^ Hol_pp.term_to_string t))
    and quant_inst t =  (* ~(!x. P x) \/ P a *)
      let val (lhs, rhs) = boolSyntax.dest_disj t
          val Px = boolSyntax.dest_neg lhs
          val (bvars, _) = boolSyntax.strip_forall Px
          (* "P a" may be a quantified proposition itself; only retain *new*
             quantifiers *)
          val bvars = List.take (bvars, List.length bvars -
            List.length (Lib.fst (boolSyntax.strip_forall rhs)))
          fun strip_some_foralls 0 term =
            term
            | strip_some_foralls n term =
            strip_some_foralls (n - 1) (Lib.snd (boolSyntax.dest_forall term))
          val len = List.length bvars
          val (tmsubst, _) = Term.match_term (strip_some_foralls len Px) rhs
          val bvars' = List.map (Term.subst tmsubst) bvars
      in
        Drule.IMP_ELIM (Thm.DISCH Px (Drule.SPECL bvars' (Thm.ASSUME Px)))
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("quant_inst: " ^ Hol_pp.term_to_string t))
    and quant_intro (thm, t) =  (* from P = Q derive (!x. P x) = (!y. Q y) *)
      let val (lhs, rhs) = boolSyntax.dest_eq t
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
        thm
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("quant_intro: " ^ Hol_pp.thm_to_string thm ^ ", " ^
          Hol_pp.term_to_string t))
    fun refl t =
      Thm.REFL (boolSyntax.lhs t)
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("refl: " ^
          Hol_pp.term_to_string t))
    fun rewrite t =
      let val (l, r) = boolSyntax.dest_eq t
      in
        if l = r then
          Thm.REFL l
        else

        (* proforma theorems *)
        (*Profile.profile "rewrite(proforma)"*) (fn () =>
          Z3_ProformaThms.prove Z3_ProformaThms.rewrite_thms t) ()
        handle Feedback.HOL_ERR _ =>

        (* re-ordering conjunctions and disjunctions *)
        (if boolSyntax.is_conj l then
          (*Profile.profile "rewrite(conj)"*) rewrite_conj (l, r)
        else if boolSyntax.is_disj l then
          (*Profile.profile "rewrite(disj)"*) rewrite_disj (l, r)
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
              val False = unit_resolution (disj_th :: conj_ths @ neg_iffs,
                boolSyntax.F)

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
            Drule.IMP_ANTISYM_RULE l_imp_r r_imp_l
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
            Thm.TRANS (Thm.TRANS l_eq_l' l'_eq_r') (Thm.SYM r_eq_r')
          end) ()
        handle Feedback.HOL_ERR _ =>

        (*Profile.profile "rewrite(TAUT_PROVE)"*) tautLib.TAUT_PROVE t
        handle Feedback.HOL_ERR _ =>

        (*Profile.profile "rewrite(update)"*) (fn () =>
          simpLib.SIMP_PROVE update_ss [] t) ()
        handle Feedback.HOL_ERR _ =>

        (*Profile.profile "rewrite(cache)"*) (fn () =>
          Z3_ProformaThms.prove (!theorem_cache) t) ()
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
            handle Feedback.HOL_ERR _ =>

              (*TODO*) Profile.profile "rewrite(BBLAST_TAC)"
                Tactical.prove (t, blastLib.BBLAST_TAC)
        in
          cache_theorem th;
          th
        end
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("rewrite: " ^
          Hol_pp.term_to_string t))
    and rewrite_star (thms, t) =
      raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("rewrite*: " ^
        String.concatWith ", " (List.map Hol_pp.thm_to_string thms) ^ ", " ^
        Hol_pp.term_to_string t))
    and sk t = (* (~ (not (forall x (p x y))) (not (p (sk y) y)))
                  (~ (exists x (p x y)) (p (sk y) y)) *)
      let fun NOT_FORALL_CONV tm =  (* |- ~(!x y z. P) = (?x y z. ~P) *)
            let val thm = Conv.NOT_FORALL_CONV tm
                (* transform the rhs recursively *)
                val rhs = boolSyntax.rhs (Thm.concl thm)
                val (var, body) = boolSyntax.dest_exists rhs
            in
              Thm.TRANS thm (Drule.EXISTS_EQ var (NOT_FORALL_CONV body))
                handle Feedback.HOL_ERR _ => thm
            end
          val (not_forall, skolemized) = boolSyntax.dest_eq t
          (* we assume that p is not universally quantified, so that we may
             turn *all* universal quantifiers into existential ones *)
          val not_forall_eq_exists_th = NOT_FORALL_CONV not_forall
          val exists = boolSyntax.rhs (Thm.concl not_forall_eq_exists_th)
          val (vars, body) = boolSyntax.strip_exists exists
          (* 'tmsubst' maps (existentially quantified) variables to Skolem
             functions applied to some arguments. *)
          val (tmsubst, _) = Term.match_term body skolemized
          (* replaces existentially quantified variables by Skolem functions,
             assuming suitable definitions in terms of HOL's SELECT operator *)
          (* [...] |- P[skx/x, sky/y, skz/z] = (?x y z. P) *)
          fun SKOLEM_CONV tm =
            let val (var, body) = boolSyntax.dest_exists tm
                val select = boolSyntax.mk_select (var, body)
                val thm = Conv.SELECT_CONV (Term.subst [{redex = var,
                  residue = select}] body)

                val (sk, args) = boolSyntax.strip_comb (Term.subst tmsubst var)
                val sk_def =
                  boolSyntax.mk_eq (sk, boolSyntax.list_mk_abs (args, select))
                (* store definition in global ref *)
                val _ = skolem_defs := sk_def :: !skolem_defs

                val def_th = Thm.ASSUME sk_def
                val rewrite_th = List.foldl (fn (arg, th) =>
                  let val ap_th = Thm.AP_THM th arg
                      val beta_th = Thm.BETA_CONV (boolSyntax.rhs
                        (Thm.concl ap_th))
                  in
                    Thm.TRANS ap_th beta_th
                  end) def_th args (* [.] |- sk x y z = select *)
                val thm = Thm.SUBST
                  [{redex = var, residue = Thm.SYM rewrite_th}]
                  (boolSyntax.mk_eq (body, tm)) thm
            in
              (* transform the lhs recursively *)
              Thm.TRANS (SKOLEM_CONV (boolSyntax.lhs (Thm.concl thm))) thm
                handle Feedback.HOL_ERR _ => thm
            end
          val skolemized_eq_exists_th = SKOLEM_CONV exists
      in
        Thm.TRANS not_forall_eq_exists_th (Thm.SYM skolemized_eq_exists_th)
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("sk: " ^
          Hol_pp.term_to_string t))
    and symm (thm, t) =
      Thm.SYM thm
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("symm: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    and th_lemma (thms, t) =
      let val concl = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
      in
        (* proforma theorems *)
        (*Profile.profile "th_lemma(proforma)"*)
          (fn () => Drule.LIST_MP thms
            (Z3_ProformaThms.prove Z3_ProformaThms.th_lemma_thms concl)) ()
        handle Feedback.HOL_ERR _ =>

        (* cache *)
        Drule.LIST_MP thms (Z3_ProformaThms.prove (!theorem_cache) concl)
        handle Feedback.HOL_ERR _ =>

        (*Profile.profile "th_lemma(update)"*) (fn () => Drule.LIST_MP thms 
          (simpLib.SIMP_PROVE update_ss [] concl)) ()
        handle Feedback.HOL_ERR _ =>

        let val (dict, concl) = generalize_ite concl
            val th = if term_contains_real_ty concl then
                (*Profile.profile "th_lemma(REAL_ARITH)"*)
                  realLib.REAL_ARITH concl
              else
                (*Profile.profile "th_lemma(ARITH_PROVE)"*)
                  intLib.ARITH_PROVE concl
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
            handle Feedback.HOL_ERR _ =>

              (*TODO*) Profile.profile "th_lemma(BBLAST_TAC)"
                Tactical.prove (concl, blastLib.BBLAST_TAC)

            val subst = List.map (fn (term, var) =>
              {redex = var, residue = term}) (Redblackmap.listItems dict)
        in
          cache_theorem th;
          Drule.LIST_MP thms (Thm.INST subst th)
        end
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("th_lemma: "
          ^ String.concatWith ", " (List.map Hol_pp.thm_to_string thms) ^ ", " ^
          Hol_pp.term_to_string t))
    and trans (thm1, thm2, t) =
      Thm.TRANS thm1 thm2
      handle Feedback.HOL_ERR _ =>
      if Thm.concl thm2 = t then
        thm2  (* oddly enough, thm1 is sometimes not needed -- this is arguably
                 a bug in Z3 *)
      else
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof" ("trans: " ^
          Hol_pp.thm_to_string thm1 ^ ", " ^ Hol_pp.thm_to_string thm2 ^ ", " ^
          Hol_pp.term_to_string t))
    and true_axiom t =
      boolTheory.TRUTH
    (* l1 \/ l2 \/ ... \/ ln \/ t   ~l1   ~l2   ...   ~ln
       --------------------------------------------------
                                t

       The input clause (including "t") is really treated as a set of literals:
       the resolvents need not be in the correct order, "t" need not be the
       rightmost disjunct (and if "t" is a disjunction, its disjuncts may even
       be spread throughout the input clause).  Note also that "t" may be F, in
       which case it need not be present in the input clause.

       We treat all "~li" as atomic, even if they are negated disjunctions.
    *)
    and unit_resolution (thms, t) =
    let val _ = if List.null thms then
            raise (Feedback.mk_HOL_ERR "" "" "")
          else ()
          fun disjuncts dict (disj, thm) =
            let val (l, r) = boolSyntax.dest_disj disj
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
              let val (l, r) = boolSyntax.dest_disj disj
                  val l_th = prove_from_disj dict l
                  val r_th = prove_from_disj dict r
              in
                Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
              end
          val empty = Redblackmap.mkDict Term.compare
          val dict = disjuncts empty (t, Thm.ASSUME t)
        (* derive 't' from each negated resolvent *)
        val dict = List.foldl (fn (th, dict) =>
          let val lit = Thm.concl th
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
      Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
    end
    handle Feedback.HOL_ERR _ =>
      raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
        ("unit_resolution: " ^ String.concatWith ", " (List.map
        Hol_pp.thm_to_string thms) ^ ", " ^ Hol_pp.term_to_string t))
    (*** end of inference rule implementations ***)

    fun verify_theorem rule id t thm =
      (*Profile.profile "verify_theorem"*) (fn () =>
        (if !SolverSpec.trace > 0 andalso Thm.concl thm <> t then
          Feedback.HOL_WARNING "Z3_ProofReplay" "check_proof" ("#" ^
            Int.toString id ^ " (" ^ rule ^ "): conclusion is " ^
            Hol_pp.term_to_string (Thm.concl thm) ^ ", expected: " ^
            Hol_pp.term_to_string t)
        else ();
        if !SolverSpec.trace > 2 then
          Feedback.HOL_MESG ("HolSmtLib: proved #" ^ Int.toString id ^ " (" ^
            rule ^ "): " ^ Hol_pp.thm_to_string thm)
        else ())) ()
    fun check_proof_id (prf, id) =
      case Redblackmap.peek (prf, id) of
        SOME (AND_ELIM (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "and_elim"*) and_elim (thm, t)
            val _ = verify_theorem "and_elim" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (ASSERTED t) =>
        let val thm = (*Profile.profile "asserted"*) asserted t
            val _ = verify_theorem "asserted" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (COMMUTATIVITY t) =>
        let val thm = (*Profile.profile "commutativity"*) commutativity t
            val _ = verify_theorem "commutativity" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (DEF_AXIOM t) =>
        let val thm = (*Profile.profile "def_axiom"*) def_axiom t
            val _ = verify_theorem "def-axiom" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (ELIM_UNUSED t) =>
        let val thm = (*Profile.profile "elim_unused"*) elim_unused t
            val _ = verify_theorem "elim-unused" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (IFF_FALSE (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "iff_false"*) iff_false (thm, t)
            val _ = verify_theorem "iff-false" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (IFF_TRUE (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "iff_true"*) iff_true (thm, t)
            val _ = verify_theorem "iff-true" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (LEMMA (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "lemma"*) lemma (thm, t)
            val _ = verify_theorem "lemma" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (HYPOTHESIS t) =>
        let val thm = (*Profile.profile "hypothesis"*) hypothesis t
            val _ = verify_theorem "hypothesis" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (MONOTONICITY (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = (*Profile.profile "monotonicity"*) monotonicity (thms, t)
            val _ = verify_theorem "monotonicity" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (MP (id1, id2, t)) =>
        let val (prf, thm1) = check_proof_id (prf, id1)
            val (prf, thm2) = check_proof_id (prf, id2)
            val thm = (*Profile.profile "mp"*) mp (thm1, thm2, t)
            val _ = verify_theorem "mp" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (MP_TILDE (id1, id2, t)) =>
        let val (prf, thm1) = check_proof_id (prf, id1)
            val (prf, thm2) = check_proof_id (prf, id2)
            val thm = (*Profile.profile "mp~"*) mp_tilde (thm1, thm2, t)
            val _ = verify_theorem "mp~" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (NNF_NEG (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = (*Profile.profile "nnf_neg"*) nnf_neg (thms, t)
            val _ = verify_theorem "nnf-neg" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (NNF_POS (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = (*Profile.profile "nnf_pos"*) nnf_pos (thms, t)
            val _ = verify_theorem "nnf-pos" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (NOT_OR_ELIM (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "not_or_elim"*) not_or_elim (thm, t)
            val _ = verify_theorem "not-or-elim" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (PULL_QUANT t) =>
        let val thm = (*Profile.profile "pull_quant"*) pull_quant t
            val _ = verify_theorem "pull-quant" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (QUANT_INST t) =>
        let val thm = (*Profile.profile "quant_inst"*) quant_inst t
            val _ = verify_theorem "quant-inst" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (QUANT_INTRO (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "quant_intro"*) quant_intro (thm, t)
            val _ = verify_theorem "quant-intro" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (REFL t) =>
        let val thm = (*Profile.profile "refl"*) refl t
            val _ = verify_theorem "refl" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (REWRITE t) =>
        let val thm = (*Profile.profile "rewrite"*) rewrite t
            val _ = verify_theorem "rewrite" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (REWRITE_STAR (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = (*Profile.profile "rewrite_star"*) rewrite_star (thms, t)
            val _ = verify_theorem "rewrite-star" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (SK t) =>
        let val thm = (*Profile.profile "sk"*) sk t
            val _ = verify_theorem "sk" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (SYMM (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = (*Profile.profile "symm"*) symm (thm, t)
            val _ = verify_theorem "symm" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (TH_LEMMA (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = (*Profile.profile "th_lemma"*) th_lemma (thms, t)
            val _ = verify_theorem "th-lemma" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (TRANS (id1, id2, t)) =>
        let val (prf, thm1) = check_proof_id (prf, id1)
            val (prf, thm2) = check_proof_id (prf, id2)
            val thm = (*Profile.profile "trans"*) trans (thm1, thm2, t)
            val _ = verify_theorem "trans" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (TRUE_AXIOM t) =>
        let val thm = (*Profile.profile "true_axiom"*) true_axiom t
            val _ = verify_theorem "true-axiom" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (UNIT_RESOLUTION (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = (*Profile.profile "unit_resolution"*) unit_resolution
              (thms, t)
            val _ = verify_theorem "unit-resolution" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (THEOREM thm) =>
        (prf, thm)
      | NONE =>
        raise (Feedback.mk_HOL_ERR "Z3_ProofReplay" "check_proof"
          ("no proofterm with ID " ^ Int.toString id))
    val thm = Lib.snd (check_proof_id (prf, 0))
    val _ = if !SolverSpec.trace > 0 andalso Thm.concl thm <> boolSyntax.F then
        Feedback.HOL_WARNING "Z3_ProofReplay" "check_proof"
          "final conclusion is not 'F'"
      else ()
    (* eliminate Skolemization hypotheses "sk = def"; cf. function 'sk' above *)
    val thm = List.foldl (fn (sk_def, th) =>
      let val (sk, def) = boolSyntax.dest_eq sk_def
          val th = Thm.INST [{redex = sk, residue = def}] th
          val def_th = Thm.REFL def
          val _ = if !SolverSpec.trace > 0 andalso
                not (HOLset.member (Thm.hypset th, Thm.concl def_th)) then
              Feedback.HOL_WARNING "Z3_ProofReplay" "check_proof"
                "Skolem hyp not found"
            else ()
      in
        Drule.PROVE_HYP def_th th
      end) thm (!skolem_defs)
      (* check that the final theorem contains no hyps other than those that
         have been asserted *)
      val _ = (*Profile.profile "check_proof(hypcheck)"*) (fn () =>
        if !SolverSpec.trace > 0 andalso not (HOLset.isSubset (Thm.hypset thm,
          !asserted_hyps)) then
          Feedback.HOL_WARNING "Z3_ProofReplay" "check_proof"
            "final theorem contains additional hyp(s)"
        else ()) ()
  in
    thm
  end

end
