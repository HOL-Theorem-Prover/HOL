signature Overload =
sig
 type hol_type = HolKernel.hol_type
 type term     = HolKernel.term

 type const_rec = {Name : string, Ty : hol_type, Thy : string}
 type nthy_rec = {Name : string, Thy : string}
 type overloaded_op_info =
    {base_type : hol_type,
     actual_ops : const_rec list}


  type overload_info

  val null_oinfo : overload_info

  (* the parse map, taking strings to possible constants *)
  val oinfo_ops : overload_info -> (string * overloaded_op_info) list

  (* the print map, taking constants to at most one string *)
  val print_map : overload_info -> (nthy_rec * string) list



  val fupd_actual_ops :
    (const_rec list -> const_rec list) -> overloaded_op_info ->
    overloaded_op_info

  exception OVERLOAD_ERR of string

  val remove_overloaded_form :
    string -> overload_info ->
    overload_info * (nthy_rec list * nthy_rec list)

  val raw_map_insert :
    string -> (nthy_rec list * nthy_rec list) ->
    overload_info -> overload_info

  val info_for_name : overload_info -> string -> overloaded_op_info option
  val is_overloaded : overload_info -> string -> bool
  val overloading_of_term : overload_info -> Term.term -> string option
  val overloading_of_nametype :
    overload_info -> {Name : string, Thy : string} ->
    string option

  val add_actual_overloading:
    {opname: string, realname: string, realthy : string} ->
    overload_info -> overload_info

  val send_to_back_overloading:
    {opname: string, realname: string, realthy : string} ->
    overload_info -> overload_info

  val bring_to_front_overloading:
    {opname: string, realname: string, realthy : string} ->
    overload_info -> overload_info

  val merge_oinfos : overload_info -> overload_info -> overload_info

  val known_constants : overload_info -> string list

  val remove_mapping :
    string -> {Name:string, Thy:string} -> overload_info -> overload_info

end
