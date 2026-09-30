signature Refute_ModelFinder_Nut = sig
  type hol_type = Type.hol_type
  type term = Term.term
  type context = Refute_ModelFinder_HOL.mf_context
  type scope = Refute_ModelFinder_Scope.scope
  type name_pool = Refute_ModelFinder_Peephole.name_pool
  type rep = Refute_ModelFinder_Rep.rep

  datatype cst =
    False | True | Iden | Num of int | Unknown | Unrep | Suc | Add |
    Subtract | Multiply | Divide | Gcd | Lcm | Fracs | NormFrac |
    NatToInt | IntToNat |
    (* Word operations with no arithmetic reading.  [Add], [Subtract] and
       [Multiply] serve the modular ring at a word type, and the rest of the
       direct tier reduces to those. *)
    NatToWord | WordToNat | WordAnd | WordOr | WordXor |
    WordShl | WordShr | WordAsr |
    (* The two morphisms of the [:char] carrier: the numbering that makes
       atom [j] denote [CHR j], and its inverse. *)
    NatToChar | CharToNat

  datatype op1 =
    Not | Finite | Converse | Closure | SingletonSet | IsUnknown |
    SafeThe | First | Second | Cast

  datatype op2 =
    All | Exist | Or | And | Less | DefEq | Eq | Triad | Composition |
    Apply | Lambda

  datatype op3 = Let | If

  datatype nut =
    Cst of cst * hol_type * rep
  | Op1 of op1 * hol_type * rep * nut
  | Op2 of op2 * hol_type * rep * nut * nut
  | Op3 of op3 * hol_type * rep * nut * nut * nut
  | Tuple of hol_type * rep * nut list
  | Construct of nut list * hol_type * rep * nut list
  | BoundName of int * hol_type * rep * string
  | FreeName of string * hol_type * rep
  | ConstName of string * hol_type * rep
  | BoundRel of Refute_Forl.n_ary_index * hol_type * rep * string
  | FreeRel of Refute_Forl.n_ary_index * hol_type * rep * string
  | RelReg of int * hol_type * rep
  | FormulaReg of int * hol_type * rep

  structure NameTable : TABLE
  exception NUT of string * nut list

  val type_of : nut -> hol_type
  val rep_of : nut -> rep
  val nickname_of : nut -> string
  val is_skolem_name : nut -> bool
  val is_eval_name : nut -> bool
  val is_Cst : cst -> nut -> bool
  val fold_nut : (nut -> 'a -> 'a) -> nut -> 'a -> 'a
  val untuple : (nut -> 'a) -> nut -> 'a list
  val add_free_and_const_names :
    nut -> nut list * nut list -> nut list * nut list
  val name_ord : nut * nut -> order
  val the_name : 'a NameTable.table -> nut -> 'a
  val the_rel : nut NameTable.table -> nut -> Refute_Forl.n_ary_index
  val nut_from_term : context -> op2 -> term -> nut
  val is_fully_representable_set : nut -> bool
  val choose_reps_for_free_vars :
    scope -> nut list -> rep NameTable.table ->
    nut list * rep NameTable.table
  val choose_reps_for_consts :
    scope -> bool -> nut list -> rep NameTable.table ->
    nut list * rep NameTable.table
  val choose_reps_for_all_sels :
    scope -> rep NameTable.table -> nut list * rep NameTable.table
  val choose_reps_in_nut :
    scope -> bool -> rep NameTable.table -> bool -> nut -> nut
  val rename_free_vars :
    nut list -> name_pool -> nut NameTable.table ->
    nut list * name_pool * nut NameTable.table
  val rename_vars_in_nut :
    name_pool -> nut NameTable.table -> nut -> nut
  val selector_const_names : term -> nut list
end
