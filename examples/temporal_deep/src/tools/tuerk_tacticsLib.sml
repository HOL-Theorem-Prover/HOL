structure tuerk_tacticsLib :> tuerk_tacticsLib =
struct


  open HolKernel boolLib bossLib Abbrev metisLib pred_setTheory numLib schneiderUtils

   val ERR = mk_HOL_ERR "tuerk_tacticsLib";

   val SET_INDUCT_TAC = PSet_ind.SET_INDUCT_TAC FINITE_INDUCT;

   val EXISTS_EQ_STRIP_TAC :tactic = fn (asl,t) =>

      let val (lhs,rhs) = dest_eq t
         val (lvar,LBody) = dest_exists lhs
         val (rvar,RBody) = dest_exists rhs
         val newVar = variant (free_varsl (t::asl)) lvar
         val newLBody = subst[lvar |-> newVar] LBody
         val newRBody = subst[rvar |-> newVar] RBody
         val result = mk_eq(newLBody, newRBody)
      in ([(asl, result)],
         fn thList => EXISTS_EQ newVar (hd(thList)))
      end
      handle HOL_ERR _ => raise ERR "EXISTS_EQ_STRIP_TAC" "";


   val FORALL_EQ_STRIP_TAC :tactic = fn (asl,t) =>

      let val (lhs,rhs) = dest_eq t
         val (lvar,LBody) = dest_forall lhs
         val (rvar,RBody) = dest_forall rhs
         val newVar = variant (free_varsl (t::asl)) lvar
         val newLBody = subst[lvar |-> newVar] LBody
         val newRBody = subst[rvar |-> newVar] RBody
         val result = mk_eq(newLBody, newRBody)
      in ([(asl, result)],
         fn thList => FORALL_EQ newVar (hd thList))
      end
      handle HOL_ERR _ => raise ERR "FORALL_EQ_STRIP_TAC" "";


   val REWRITE_ASSUMPTIONS_TAC = fn rwts =>
      POP_ASSUM_LIST (MAP_EVERY (fn thm => STRIP_ASSUME_TAC (REWRITE_RULE rwts thm))) THEN
      POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC);


   val CLEAN_ASSUMPTIONS_TAC =
      REWRITE_ASSUMPTIONS_TAC[DE_MORGAN_THM, FORALL_AND_THM, EXISTS_OR_THM];


   val ONCE_REWRITE_ASSUMPTIONS_TAC = fn rwts =>
      POP_ASSUM_LIST (MAP_EVERY (fn thm => STRIP_ASSUME_TAC (ONCE_REWRITE_RULE rwts thm))) THEN
      POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC);

   val REWRITE_ALL_TAC = fn rwts =>
      REWRITE_ASSUMPTIONS_TAC rwts THEN
      REWRITE_TAC rwts;

   val ONCE_REWRITE_ALL_TAC = fn rwts =>
      ONCE_REWRITE_ASSUMPTIONS_TAC rwts THEN
      ONCE_REWRITE_TAC rwts;

   val SIMP_ASSUMPTIONS_TAC = fn simp => fn rwts =>
      POP_ASSUM_LIST (MAP_EVERY (fn thm => STRIP_ASSUME_TAC (SIMP_RULE simp rwts thm))) THEN
      POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC);

   val SIMP_ALL_TAC = fn simp => fn rwts =>
      SIMP_ASSUMPTIONS_TAC simp rwts THEN
      SIMP_TAC simp rwts;



   fun findMatch ([], l2, c) = raise ERR "findMatch" ""
     | findMatch (l1, [], c) = raise ERR "findMatch" ""
     | findMatch (a::l1, b::l2, []) = findMatch (l1, b::l2, b::l2)
     | findMatch (a::l1, l2, b::c) = if a ~~ b then a
                                     else findMatch (a::l1, l2, c)


   val DISJ_EQ_STRIP_TAC :tactic = fn (asl,t) =>
      let val (lhs,rhs) = dest_eq t
         val l1 = strip_disj lhs
         val l2 = strip_disj rhs
         val m = findMatch (l1, l2, l2)
      in
         (DISJ_CASES_TAC (REWRITE_RULE [EQ_CLAUSES] (SPEC m BOOL_CASES_AX)) THEN ASM_REWRITE_TAC[]) (asl, t)
      end
      handle HOL_ERR _ => raise ERR "OR_EQ_STRIP_TAC" "";


   val CONJ_EQ_STRIP_TAC :tactic = fn (asl,t) =>
      let val (lhs,rhs) = dest_eq t
         val l1 = strip_conj lhs
         val l2 = strip_conj rhs
         val m = findMatch (l1, l2, l2)
      in
         (DISJ_CASES_TAC (REWRITE_RULE [EQ_CLAUSES] (SPEC m BOOL_CASES_AX)) THEN ASM_REWRITE_TAC[]) (asl, t)
      end
      handle HOL_ERR _ => raise ERR "CONJ_EQ_STRIP_TAC" "";

   val C_IMP_EQ_STRIP_TAC :tactic = fn (asl,t) =>
      let val (lhs,rhs) = dest_eq t
          val (la, lc) = dest_imp lhs;
          val (ra, rc) = dest_imp rhs;
          val l1 = strip_disj lc
          val l2 = strip_disj rc
          val m = findMatch (l1, l2, l2)
      in
         (DISJ_CASES_TAC (REWRITE_RULE [EQ_CLAUSES] (SPEC m BOOL_CASES_AX)) THEN ASM_REWRITE_TAC[]) (asl, t)
      end
      handle HOL_ERR _ => raise ERR "IMP_EQ_STRIP_TAC" "";

   val A_IMP_EQ_STRIP_TAC :tactic = fn (asl,t) =>
      let val (lhs,rhs) = dest_eq t
          val (la, lc) = dest_imp lhs;
          val (ra, rc) = dest_imp rhs;
          val l1 = strip_conj la
          val l2 = strip_conj ra
          val m = findMatch (l1, l2, l2)
      in
         (DISJ_CASES_TAC (REWRITE_RULE [EQ_CLAUSES] (SPEC m BOOL_CASES_AX)) THEN ASM_REWRITE_TAC[]) (asl, t)
      end
      handle HOL_ERR _ => raise ERR "IMP_EQ_STRIP_TAC" "";


   val BOOL_EQ_STRIP_TAC = FIRST [DISJ_EQ_STRIP_TAC, CONJ_EQ_STRIP_TAC,
    A_IMP_EQ_STRIP_TAC, C_IMP_EQ_STRIP_TAC, CHANGED_TAC (REWRITE_TAC [DE_MORGAN_THM])];

   fun UNDISCH_KEEP_NO_TAC i =
    POP_NO_ASSUM i (fn x=> (ASSUME_TAC x THEN UNDISCH_TAC (concl x) THEN ASSUME_TAC x))


   val UNDISCH_HD_TAC = schneiderUtils.UNDISCH_HD_TAC
   val UNDISCH_ALL_TAC = schneiderUtils.UNDISCH_ALL_TAC
   val UNDISCH_NO_TAC = schneiderUtils.UNDISCH_NO_TAC
   val POP_NO_ASSUM = schneiderUtils.POP_NO_ASSUM
   val LEFT_DISJ_TAC = schneiderUtils.LEFT_DISJ_TAC
   val RIGHT_DISJ_TAC = schneiderUtils.RIGHT_DISJ_TAC
   val LEFT_CONJ_TAC = schneiderUtils.LEFT_CONJ_TAC
   val RIGHT_CONJ_TAC = schneiderUtils.RIGHT_CONJ_TAC

   val WEAKEN_HD_TAC = WEAKEN_TAC (fn f => true);
   val WEAKEN_NO_TAC = schneiderUtils.POP_NO_TAC
   val IMP_TAC = fn t => ASSUME_TAC t THEN UNDISCH_HD_TAC;
   fun GSYM_NO_TAC i = POP_NO_ASSUM i (fn x=> ASSUME_TAC (GSYM x));

   fun SUBGOAL_TAC q = Q.SUBGOAL_THEN q STRIP_ASSUME_TAC
   fun REMAINS_TAC q = Tactical.REVERSE (SUBGOAL_TAC q)
   val SPEC_NO_ASSUM = (fn n => fn S => POP_NO_ASSUM n (fn x=> ASSUME_TAC (SPEC S x)));
   val SPECL_NO_ASSUM = (fn n => fn S => POP_NO_ASSUM n (fn x=> ASSUME_TAC (SPECL S x)));


   fun Q_SPEC_NO_ASSUM n = Q_TAC (SPEC_NO_ASSUM n);

   fun Q_SPECL_NO_ASSUM n [] = ALL_TAC
     | Q_SPECL_NO_ASSUM n (h::l) = (Q_SPEC_NO_ASSUM n h THEN Q_SPECL_NO_ASSUM 0 l);

   val IMP_TO_EQ_TAC = MATCH_MP_TAC (prove (``(a = b) ==> (a ==> b)``, SIMP_TAC std_ss []));

   fun store_simp_thm(name,term,tac) = save_thm(name,
            SIMP_RULE std_ss [] (prove(term, tac)));


  fun EXISTS_LEAST_TAC___GEN t tac =
    let
      val thm = EXISTS_LEAST_CONV t;
      val (lhs, rhs) = dest_eq (concl thm)
      fun ASSUME_MP_TAC thm2 = ASSUME_TAC (EQ_MP thm thm2)
    in
      SUBGOAL_THEN lhs ASSUME_MP_TAC THEN1 tac
    end;

  fun EXISTS_LEAST_TAC t = EXISTS_LEAST_TAC___GEN t (METIS_TAC[]);
  val Q_EXISTS_LEAST_TAC = Q_TAC EXISTS_LEAST_TAC;



  fun PROVE_CONDITION_TAC thm (asl, t) =
    let
      val (p, c) = dest_imp (concl thm);
      fun mp_thm thms =
        let
          val thm_p = el 1 thms;
          val thm_t = el 2 thms;
          val thm = MP thm thm_p;
          val result = DISCH (concl thm) thm_t;
          val result = MP result thm
        in
          result
        end
    in
      ([(asl, p), (c::asl, t)], mp_thm)
    end;

  fun PROVE_CONDITION_NO_ASSUM i = POP_NO_ASSUM i PROVE_CONDITION_TAC

  fun MATCH_LEFT_EQ_MP_TAC thm =
    let
      val thm = UNDISCH_ALL (SPEC_ALL thm);
      val thm = fst (EQ_IMP_RULE thm);
      val thm = GEN_ALL (DISCH_ALL thm)
      val thm = REWRITE_RULE [AND_IMP_INTRO] thm
    in
      MATCH_MP_TAC thm
    end

  fun MATCH_RIGHT_EQ_MP_TAC thm =
    let
      val thm = UNDISCH_ALL (SPEC_ALL thm);
      val thm = snd (EQ_IMP_RULE thm);
      val thm = GEN_ALL (DISCH_ALL thm)
      val thm = REWRITE_RULE [AND_IMP_INTRO] thm
    in
      MATCH_MP_TAC thm
    end

end
