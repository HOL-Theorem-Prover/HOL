signature Refute_RegistrationData = sig
  type operator = {Thy : string, Tyop : string}
  datatype descriptor =
      Codata of {tyop : operator, case_const : Term.term,
                 constructors : Term.term list, witness : Thm.thm option}
    | Typedef of {ty : Type.hol_type, abs : Term.term, rep : Term.term,
                  absrep_thms : Thm.thm list}
    | Quotient of {qty : Type.hol_type, rty : Type.hol_type,
                   abs : Term.term, rep : Term.term, equiv_thm : Thm.thm}
  val operator : descriptor -> operator
  val encode : descriptor -> ThyDataSexp.t
  val fresh : descriptor -> bool
  (* Ordered history, rather than an unchecked last-writer map. *)
  val history : Context.t -> operator -> (string * descriptor) list
  val operators : Context.t -> operator list
  val identity : (string * descriptor) list -> ThyDataSexp.t
  (* All encoding and value construction precede the returned commit.
     The caller excludes interrupts and enforces theory-authoring rules. *)
  val prepare : Context.t -> string -> descriptor list -> (unit -> unit)
end
