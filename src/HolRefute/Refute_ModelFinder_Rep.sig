signature Refute_ModelFinder_Rep = sig
  type polarity = Refute_ModelFinder_Util.polarity
  type hol_type = Type.hol_type
  type scope = Refute_ModelFinder_Scope.scope
  type offset_table = Refute_ModelFinder_Scope.offset_table

  datatype rep =
    Any
  | Formula of polarity
  | Atom of int * int
  | Struct of rep list
  | Vect of int * rep
  | Func of rep * rep
  | Opt of rep

  exception REP of string * rep list

  val string_for_rep : rep -> string
  val is_Func : rep -> bool
  val is_Opt : rep -> bool
  val is_opt_rep : rep -> bool
  val flip_rep_polarity : rep -> rep
  val card_of_rep : rep -> int
  val arity_of_rep : rep -> int
  val min_univ_card_of_rep : rep -> int
  val is_one_rep : rep -> bool
  val is_lone_rep : rep -> bool
  val dest_Func : rep -> rep * rep
  val lazy_range_rep :
    offset_table -> hol_type -> (unit -> int) -> rep -> rep
  val binder_reps : rep -> rep list
  val body_rep : rep -> rep
  val one_rep : offset_table -> hol_type -> rep -> rep
  val opt_rep : offset_table -> hol_type -> rep -> rep
  val unopt_rep : rep -> rep
  val min_rep : rep -> rep -> rep
  val card_of_domain_from_rep : int -> rep -> int
  val rep_to_binary_rel_rep : offset_table -> hol_type -> rep -> rep
  val best_one_rep_for_type : scope -> hol_type -> rep
  val best_opt_set_rep_for_type : scope -> hol_type -> rep
  val best_non_opt_set_rep_for_type : scope -> hol_type -> rep
  val best_set_rep_for_type : scope -> hol_type -> rep
  val atom_schema_of_rep : rep -> (int * int) list
  val atom_schema_of_reps : rep list -> (int * int) list
  val type_schema_of_rep : hol_type -> rep -> hol_type list
  val all_combinations_for_rep : rep -> int list list
end
