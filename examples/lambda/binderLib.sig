signature binderLib =
sig

  include Abbrev

  val NEW_TAC : string -> term -> tactic
  val NEW_ELIM_TAC : tactic

  val recursive_term_function_existence : term -> thm
  val prove_recursive_term_function_exists : term -> thm
  val define_recursive_term_function :
      term quotation -> thm * thm

  val define_recursive_term_function' :
      conv -> term quotation -> thm * thm

  (* stores recursion theorems for types *)
  val type_db : (string,thm) Binarymap.dict ref

  type range_type_info = {nullfv : term,
                          inst : {redex : string, residue : unit -> term} list,
                          rewrites : thm list}
  val range_database : (string, range_type_info) Binarymap.dict ref

end;
