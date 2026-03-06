signature binderLib =
sig

  include Abbrev

  val find_avoids : (term * (term HOLset.set * term HOLset.set)) ->
                    term HOLset.set * term HOLset.set

  val NEW_TAC : string -> term -> tactic
  val NEW_ELIM_TAC : tactic
  val FRESH_TAC : tactic

  datatype nominaltype_info =
         NTI of { recursion_thm : thm option,
                  (* recursion theorems are stored in SPEC_ALL form, with
                     preconditions as one big set of conjuncts (rather than
                     iterated implications) *)
                  nullfv : term,
                  pm_constant : term,
                  pm_rewrites : thm list,
                  fv_rewrites : thm list,
                  binders : (term * int * thm) list }
  val enc_nti : nominaltype_info ThyDataSexp.enc
  val dec_nti : nominaltype_info ThyDataSexp.dec
  val nameless_nti : nominaltype_info

  (* stores information per type *)
  val getTypeDB : unit -> nominaltype_info KNametab.table
  val export_nomtype : hol_type * nominaltype_info -> unit
  val local_update : hol_type * nominaltype_info -> unit

  val recursive_term_function_existence : term -> thm
  val prove_recursive_term_function_exists : term -> thm
  val define_recursive_term_function :
      term quotation -> thm * thm

  val define_recursive_term_function' :
      conv -> term quotation -> thm * thm



end;
