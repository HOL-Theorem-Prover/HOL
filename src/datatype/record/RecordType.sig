signature RecordType =
sig
 val create_term_fn 
    : string -> Thm.thm -> ((string * Term.term) list -> Term.term)

  val create_term_fn_base 
    : bool -> string -> Thm.thm -> ((string * Term.term) list -> Term.term)

  val create_term_fn_vars 
    : string -> Thm.thm -> ((string * Term.term) list -> Term.term)

  val create_record 
    : string -> (string * Type.hol_type) list ->
      {acc_upd_thm : Thm.thm, accessor_fns : Thm.thm, cases_thm : Thm.thm,
       cons_11_thm : Thm.thm, create_fn :
         (string * Term.term) list -> Term.term, fn_upd_thm : Thm.thm list,
       type_axiom : Thm.thm, upd_acc_thm : Thm.thm, upd_canon_thm : Thm.thm,
       upd_upd_thm : Thm.thm, update_fns : Thm.thm}
end
