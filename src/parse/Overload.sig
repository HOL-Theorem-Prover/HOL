type overloaded_op_info = {overloaded_op: string,
                           base_type : Type.hol_type,
                           actual_ops : (Type.hol_type * string) list}
type overload_info = overloaded_op_info list

exception OVERLOAD_ERR of string

val add_overloaded_form :
  string -> Type.hol_type -> overload_info -> overload_info
val remove_overloaded_form : string -> overload_info -> overload_info

val info_for_name : overload_info -> string -> overloaded_op_info option
val is_overloaded : overload_info -> string -> bool
val overloading_of_term : overload_info -> Term.term -> string option
val overloading_of_nametype :
  overload_info -> (string * Type.hol_type) -> string option

val add_actual_overloading:
  {opname: string, realname: string, realtype: Type.hol_type} ->
  overload_info -> overload_info