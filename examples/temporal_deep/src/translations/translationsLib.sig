signature translationsLib =
sig

  (******************************************************************
   *
   * ltl2omega_rewrite t ltl
   * translates the ltl term ltl into an omega automaton and
   * returns a theorem that states the equivalence of the automaton
   * and the ltl formula. The parameter t is used to determine the kind
   * of omega automaton. For t = TRUE an existential automaton
   * otherwise an universal automaton is used.
   *
   * It uses only rewrite rules for this translation.
   * Notice, that this is just a proof of concept. In practice
   * ltl2omega should be used, since it is much more efficient.
   *
   *******************************************************************)
  val ltl2omega_rewrite : bool -> Abbrev.term -> Abbrev.thm

  (******************************************************************
   *
   * ltl2omega fast fast t ltl
   * This function does the same translation as ltl2omega_rewrite.
   * However, the implementation is more advanced. The parameter fast
   * tells the function whether to search for multiple occurences of
   * terms in the ltl formula. This may reduce the number of needed
   * states of the resulting automaton. However, it slows down the
   * translation in general.
   *
   *******************************************************************)
  val ltl2omega : bool -> bool -> Abbrev.term -> Abbrev.thm


  (******************************************************************
   * ltl2omega_interal fast fast t ltl
   * This function is similar to ltl2omega.
   * It in fact forms the main part of the translation done by ltl2omega.
   * In contrast to ltl2omega, it returns some internal data, that contain
   * more informations than the theorem returned by ltl2omega.
   * This function is used to implement rltl2fctl and ltl2fctl
   *******************************************************************)
  val ltl2omega_internal : bool -> bool -> bool -> Abbrev.term -> (Abbrev.term * Abbrev.thm * Abbrev.thm * Abbrev.term * Abbrev.term * bool * bool)


  (********************************************************************
   * These functions translate some ltl problems to an check whether there is
   * an fair path through a kripke structure. This problem can be handeled by
   * a model checker. The first parameter is always the knows fast switch
   ********************************************************************)

  val ltl_ks_sem2ks_fair_emptyness___no_ks : bool -> Abbrev.term -> Abbrev.thm
  val ltl_ks_sem2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.term -> Abbrev.thm

  val ltl_contradiction2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.thm
  val ltl_equivalent2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.term -> Abbrev.thm
  val ltl_equivalent_initial2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.term -> Abbrev.thm



  (********************************************************************
   * These functions translate some ltl problems to an check whether there is
   * an fair path through a kripke structure. Thereby they replace all variables
   * by natural numbers, such that a lot of ugly precondition like INJ or
   * ITERATORS are not necessary any more. There are different modes for this
   * functions. mode 1 generates an implication theorem. mode 2 an equational
   * theorem and all other mode both therorem. Additionally these functions
   * return a list, that tells which numbers represent the original varibales
   ********************************************************************)
  val ltl_contradiction2ks_fair_emptyness___num: int -> bool -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))
  val ltl_equivalent2ks_fair_emptyness___num: int -> bool -> Abbrev.term -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))
  val ltl_equivalent_initial2ks_fair_emptyness___num: int -> bool -> Abbrev.term -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))

  val ltl_ks_sem2ks_fair_emptyness___num : int -> bool -> Abbrev.term -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))




  (********************************************************************
   * Similar functions for PSL, that internally use the LTL versions
   ********************************************************************)


  val psl_ks_sem2ks_fair_emptyness___no_ks : bool -> Abbrev.term -> Abbrev.thm
  val psl_ks_sem2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.term -> Abbrev.thm

  val psl_contradiction2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.thm
  val psl_equivalent2ks_fair_emptyness : bool -> Abbrev.term -> Abbrev.term -> Abbrev.thm

  val psl_contradiction2ks_fair_emptyness___num: int -> bool -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))
  val psl_equivalent2ks_fair_emptyness___num: int -> bool -> Abbrev.term -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))

  val psl_ks_sem2ks_fair_emptyness___num : int -> bool -> Abbrev.term -> Abbrev.term -> (Abbrev.thm * ((int * Abbrev.term) list))
end

