signature Overload =
sig
 type hol_type = HolKernel.hol_type
 type term     = HolKernel.term

 type overloaded_op_info =
    {overloaded_op : string,
     base_type : hol_type,
     actual_ops : (hol_type * string * string) list}

  type overload_info = overloaded_op_info list

  val fupd_actual_ops
    : ((hol_type * string * string) list -> (hol_type * string * string) list)
       -> overloaded_op_info
        -> overloaded_op_info

  exception OVERLOAD_ERR of string

  val remove_overloaded_form : string -> overload_info -> overload_info

  val info_for_name : overload_info -> string -> overloaded_op_info option
  val is_overloaded : overload_info -> string -> bool
  val overloading_of_term : overload_info -> Term.term -> string option
  val overloading_of_nametype :
    overload_info -> {Name : string, Thy : string, Ty : hol_type} ->
    string option

  val add_actual_overloading:
    {opname: string, realname: string, realthy : string,
     realtype: Type.hol_type} ->
    overload_info -> overload_info

  val merge_oinfos : overload_info -> overload_info -> overload_info

end
