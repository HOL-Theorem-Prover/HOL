signature Rules =
sig
 type term = Term.term
 type hol_type = Type.hol_type
 type thm = Thm.thm
 type tactic = Abbrev.tactic

  (* Inference rules *)
  val REFL      :term -> thm
  val ASSUME    :term -> thm
  val MP        :thm -> thm -> thm
  val MATCH_MP  :thm -> thm -> thm
  val CONJUNCT1 :thm -> thm
  val CONJUNCT2 :thm -> thm
  val CONJUNCTS :thm -> thm list
  val DISCH     :term -> thm -> thm
  val UNDISCH   :thm  -> thm
  val INST_TYPE :(hol_type,hol_type) USyntax.binding list -> thm -> thm
  val SPEC      :term -> thm -> thm
  val ISPEC     :term -> thm -> thm
  val ISPECL    :term list -> thm -> thm
  val GEN       :term -> thm -> thm
  val GENL      :term list -> thm -> thm
  val BETA_RULE :thm -> thm
  val LIST_CONJ :thm list -> thm

  val SYM : thm -> thm
  val DISCH_ALL : thm -> thm
  val FILTER_DISCH_ALL : (term -> bool) -> thm -> thm
  val SPEC_ALL  : thm -> thm
  val GEN_ALL   : thm -> thm
  val IMP_TRANS : thm -> thm -> thm
  val PROVE_HYP : thm -> thm -> thm

  val CHOOSE : term * thm -> thm -> thm
  val EXISTS : term * term -> thm -> thm
  val EXISTL : term list -> thm -> thm
  val IT_EXISTS : (term,term) USyntax.binding list -> thm -> thm

  val EVEN_ORS : thm list -> thm list
  val DISJ_CASESL : thm -> thm list -> thm

  val SUBS : thm list -> thm -> thm
  val simplify : thm list -> thm -> thm
  val simpl_conv : thm list -> term -> thm

(* For debugging my isabelle solver in the conditional rewriter *)
(*
  val term_ref : term list ref
  val thm_ref : thm list ref
  val mss_ref : meta_simpset list ref
  val tracing :bool ref
*)
  val CONTEXT_REWRITE_RULE : term * term list
                             -> {thms:thm list,congs: thm list, th:thm} 
                             -> thm * term list
  val RIGHT_ASSOC : thm -> thm 

  val prove : term * tactic -> thm
end;
