structure Parsetree =
struct

type a_component = string
type read_write_decl = (bool * string list * string list) option

datatype a_expression =
    Aexp_ident of string
  | Aexp_old_ident of string
  | Aexp_num of int
  | Aexp_hol of string
  | Aexp_infix of string * a_expression * a_expression

datatype a_genpredarg =
    Aspred_arg_exp of a_expression
  | Aspred_arg_string_list of string list
  | Aspred_arg_comma
  | Aspred_arg_colon
  | Aspred_arg_semi

datatype a_genpredargType =
    Aspred_arg_ty_tag
  | Aspred_arg_ty_exp
  | Aspred_arg_ty_hol
  | Aspred_arg_ty_list of a_genpredargType
  | Aspred_arg_ty_comma
  | Aspred_arg_ty_colon
  | Aspred_arg_ty_semi

datatype a_space_pred =
    Aspred_genpred of string * a_genpredarg list * (int * int)
  | Aspred_empty
  | Aspred_hol of string
  | Aspred_boolhol of string
  | Aspred_pointsto of a_expression * (a_component * a_expression) list


datatype a_proposition =
   Aprop_infix of string * a_expression * a_expression
          (* string is one of "<", "<=", ">", ">=", "==", "!=" *)
  | Aprop_false
  | Aprop_ifthenelse of a_proposition * a_proposition * a_proposition
  | Aprop_star of a_proposition * a_proposition
  | Aprop_map of string list * a_proposition * string
  | Aprop_spred of a_space_pred


datatype p_condition =
    Pcond_true
  | Pcond_false
  | Pcond_neg of p_condition
  | Pcond_and of p_condition * p_condition
  | Pcond_or of p_condition * p_condition
  | Pcond_compare of string * a_expression * a_expression
  | Pcond_hol of string


type a_invariant = a_proposition option
type actual_params = string list * a_expression list

datatype p_statement =
    Pstm_assign of string * a_expression
  | Pstm_fldlookup of string * a_expression * a_component
  | Pstm_fldassign of a_expression * a_component * a_expression
  | Pstm_new of string * a_expression * string list
  | Pstm_dispose of a_expression * a_expression
  | Pstm_block of p_statement list
  | Pstm_if of p_condition * p_statement * p_statement
  | Pstm_while of
      int * read_write_decl * a_invariant * p_condition * p_statement
  | Pstm_block_spec of
      bool * int * read_write_decl * a_proposition * p_statement * a_proposition
  | Pstm_withres of string * p_condition * p_statement
  | Pstm_fcall of string * actual_params
  | Pstm_parallel_fcall of string * actual_params * string * actual_params
  | Pstm_assert of a_proposition
  | Pstm_diverge
  | Pstm_fail
  | Pstm_ndet of p_statement * p_statement


datatype p_item =
    Pfundecl of bool * string * (string list * string list) *
      read_write_decl * a_invariant *
      string list * p_statement list * a_invariant
  | Presource of string * string list * a_proposition

(*
type fun_item =
    { fid : string,
      param: string list * string list,
      pre: a_invariant,
      body: p_statement list,
      post: a_invariant}
*)

datatype p_top =
    Pprogram of a_component list * a_component list * p_item list
  | Pentailments of (string * a_proposition * a_proposition) list

end;
