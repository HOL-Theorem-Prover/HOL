signature REFUTE_MODEL_FINDER_MONO = sig
  val trace : bool ref
  val formulas_monotonic :
    Refute_ModelFinder_HOL.mf_context -> bool -> Type.hol_type ->
    Term.term list * Term.term list -> bool

  (* Inlined rather than a named signature: help/src-sml/makebase parses
     at most one signature declaration per .sig file. *)
  structure Test : sig
    datatype sign = Plus | Minus
    datatype annotation = Gen | New | Fls | Tru
    datatype annotation_atom = A of annotation | V of int
    datatype mtyp =
        MAlpha
      | MFun of mtyp * annotation_atom * mtyp
      | MPair of mtyp * mtyp
      | MType of string * mtyp list
      | MRec of Type.hol_type
    datatype comp_op = Eq | Neq | Leq

    type assign_literal = int * (sign * annotation)
    type comp = annotation_atom * annotation_atom * comp_op * int list
    type assign_clause = assign_literal list
    type constraint_set = comp list * assign_clause list
    type mdata

    exception UNSOLVABLE of unit

    val empty_constraints : constraint_set
    val initial_mdata :
      Refute_ModelFinder_HOL.mf_context -> bool -> Type.hol_type -> mdata
    val mtype_of_type : mdata -> Type.hol_type -> mtyp
    val mtype_of_type_all_minus : mdata -> bool -> Type.hol_type -> mtyp
    val mtype_for_constr : mdata -> Term.term -> mtyp
    val mtype_for_term : mdata -> Term.term -> mtyp * constraint_set
    val max_fresh : mdata -> int
    val caches_repaired : mdata -> bool

    val add_annotation_atom_comp :
      comp_op -> int list -> annotation_atom -> annotation_atom ->
      constraint_set -> constraint_set
    val add_assign_clause :
      assign_clause -> constraint_set -> constraint_set
    val add_mtypes_equal :
      mtyp -> mtyp -> constraint_set -> constraint_set
    val add_is_sub_mtype :
      mtyp -> mtyp -> constraint_set -> constraint_set
    val add_mtype_is_concrete :
      assign_clause -> mtyp -> constraint_set -> constraint_set
    val add_mtype_is_complete :
      assign_clause -> mtyp -> constraint_set -> constraint_set

    val prop_for_assign :
      int * annotation -> Refute_PropSat.prop_formula
    val prop_for_comp : comp -> Refute_PropSat.prop_formula
    val encode : constraint_set -> Refute_PropSat.prop_formula
    val solve :
      Time.time -> int -> constraint_set ->
      (int * annotation) list option
  end
end
