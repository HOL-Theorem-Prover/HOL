structure Parsetree =
struct

type a_component = string

datatype a_expression =
    Aexp_ident of string
  | Aexp_num of int
  | Aexp_hol of string
  | Aexp_uminus of a_expression
  | Aexp_infix of string * a_expression * a_expression
	  (* string is one of "+", "-", "*", "/", "%" *)

datatype dlink_kind = DL | XL

datatype a_space_pred =
    Aspred_list of a_component * a_expression
  | Aspred_listseg of a_component * a_expression * a_expression
  | Aspred_data_list of a_component * a_expression * a_component * string
  | Aspred_data_listseg of a_component * a_expression * a_component * string * a_expression
  | Aspred_dlseg of dlink_kind * a_component * a_expression * a_expression * a_component * a_expression * a_expression
  | Aspred_tree of a_component * a_component * a_expression
  | Aspred_empty
  | Aspred_hol of string
  | Aspred_pointsto of a_expression * (a_component * a_expression) list

datatype a_proposition =
   Aprop_infix of string * a_expression * a_expression
	  (* string is one of "<", "<=", ">", ">=" *)
  | Aprop_equal of a_expression * a_expression
  | Aprop_not_equal of a_expression * a_expression
  | Aprop_false
  | Aprop_ifthenelse of a_proposition * a_proposition * a_proposition
  | Aprop_star of a_proposition * a_proposition
  | Aprop_spred of a_space_pred



datatype p_expression =
    Pexp_ident of string
  | Pexp_num of int
  | Pexp_prefix of string * p_expression
  | Pexp_infix of string * p_expression * p_expression


type a_invariant = a_proposition option
type actual_params = string list * p_expression list

datatype p_statement =
    Pstm_assign of string * p_expression
  | Pstm_fldlookup of string * p_expression * a_component
  | Pstm_fldassign of p_expression * a_component * p_expression
  | Pstm_new of string
  | Pstm_dispose of p_expression
  | Pstm_block of p_statement list
  | Pstm_if of p_expression * p_statement * p_statement
  | Pstm_while of a_invariant * p_expression * p_statement
  | Pstm_withres of string * p_expression * p_statement
  | Pstm_fcall of string * actual_params
  | Pstm_parallel_fcall of string * actual_params * string * actual_params


datatype p_item =
    Pfundecl of string * (string list * string list) * a_invariant *
      string list * p_statement list * a_invariant
  | Presource of string * string list * a_proposition


type fun_item =
    { fid : string,
      param: string list * string list,
      pre: a_invariant,
      body: p_statement list,
      post: a_invariant}

datatype p_program =
    Pprogram of a_component list * p_item list

end;
