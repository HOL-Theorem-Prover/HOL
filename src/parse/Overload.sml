type overloaded_op_info = {overloaded_op: string,
                           base_type : Type.hol_type,
                           actual_ops : (Type.hol_type * string) list}
type overload_info = overloaded_op_info list

exception OVERLOAD_ERR of string

fun fupd_actual_ops f {overloaded_op, base_type, actual_ops} =
  {overloaded_op = overloaded_op, base_type = base_type,
   actual_ops = f actual_ops}

fun fupd_list_at_P P f list =
  case list of
    [] => NONE
  | x::xs => if P x then SOME (f x :: xs)
             else Option.map (fn xs' => x::xs) (fupd_list_at_P P f xs)

fun info_for_name (overloads:overload_info) s =
  List.find (fn x => #overloaded_op x = s) overloads
fun is_overloaded (overloads:overload_info) s =
  List.exists (fn x => #overloaded_op x = s) overloads

fun add_overloaded_form opname basety oinfo =
  if is_overloaded oinfo opname then
    raise OVERLOAD_ERR ("add_op_form: " ^ opname ^ " already present")
  else
    {overloaded_op = opname, base_type = basety, actual_ops = []}::
    oinfo

fun add_actual_overloading {opname, realname, realtype} oinfo =
  if is_overloaded oinfo opname then let
    val {base_type, ...} = valOf (info_for_name oinfo opname)
  in
    if Lib.can (Type.match_type base_type) realtype then
      valOf (fupd_list_at_P (fn x => #overloaded_op x = opname)
             (fupd_actual_ops (fn ops => (realtype, realname)::ops)) oinfo)
    else
      raise OVERLOAD_ERR "Given type is not instance of type pattern"
  end
  else
    raise OVERLOAD_ERR ("No such op: "^opname)

fun myfind f [] = NONE
  | myfind f (x::xs) = case f x of (v as SOME _) => v | NONE => myfind f xs

fun overloading_of_term (oinfo:overload_info) t =
  if not (Term.is_const t) then NONE
  else let
    val {Name,Ty} = Term.dest_const t
  in
    myfind (fn {actual_ops,overloaded_op,...} =>
            myfind (fn (t,s) =>
                    if s = Name andalso Lib.can (Type.match_type t) Ty then
                      SOME overloaded_op
                    else
                      NONE)
            actual_ops)
    oinfo
  end
