type overloaded_op_info = {overloaded_op: string,
                           base_type : Type.hol_type,
                           actual_ops : (Type.hol_type * string) list}
type overload_info = overloaded_op_info list

exception OVERLOAD_ERR of string

fun fupd_actual_ops f {overloaded_op, base_type, actual_ops} =
  {overloaded_op = overloaded_op, base_type = base_type,
   actual_ops = f actual_ops}

fun fupd_base_type f {overloaded_op, base_type, actual_ops} =
  {overloaded_op = overloaded_op, base_type = f base_type,
   actual_ops = actual_ops}

fun fupd_list_at_P P f list =
  case list of
    [] => NONE
  | x::xs => if P x then SOME (f x :: xs)
             else Option.map (fn xs' => x::xs') (fupd_list_at_P P f xs)

fun info_for_name (overloads:overload_info) s =
  List.find (fn x => #overloaded_op x = s) overloads
fun is_overloaded (overloads:overload_info) s =
  List.exists (fn x => #overloaded_op x = s) overloads

fun type_compare (ty1, ty2) = let
  val ty1_gte_ty2 = Lib.can (Type.match_type ty1) ty2
  val ty2_gte_ty1 = Lib.can (Type.match_type ty2) ty1
in
  case (ty1_gte_ty2, ty2_gte_ty1) of
    (true, true) => SOME EQUAL
  | (true, false) => SOME GREATER
  | (false, true) => SOME LESS
  | (false, false) => NONE
end

fun add_overloaded_form opname basety oinfo =
  if is_overloaded oinfo opname then let
    val oldtype = #base_type (valOf (info_for_name oinfo opname))
  in
    case type_compare (basety, oldtype) of
      NONE => raise OVERLOAD_ERR "New basetype incomparable with old"
    | SOME LESS => raise OVERLOAD_ERR "New basetype less general than old"
    | _ => valOf (fupd_list_at_P (fn x => #overloaded_op x = opname)
                  (fupd_base_type (fn x => basety)) oinfo)
  end
  else
    {overloaded_op = opname, base_type = basety, actual_ops = []}::
    oinfo

fun remove_overloaded_form s (oinfo:overload_info) =
  List.filter (fn x => #overloaded_op x <> s) oinfo

(* a predicate on pairs of operations and types that returns true if
   they're equal, given that two types are equal if they can match
   each other *)
fun compare_real_things (ty1,n1:string) (ty2,n2) =
  type_compare (ty1, ty2) = SOME EQUAL andalso n1 = n2


fun add_actual_overloading {opname, realname, realtype} oinfo =
  if is_overloaded oinfo opname then let
    val {base_type, ...} = valOf (info_for_name oinfo opname)
  in
    if Lib.can (Type.match_type base_type) realtype then
      valOf (fupd_list_at_P (fn x => #overloaded_op x = opname)
             (fupd_actual_ops
              (fn ops =>
               Lib.op_insert compare_real_things (realtype, realname) ops))
             oinfo)
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

fun overloading_of_nametype (oinfo: overload_info) (n, ty) =
  myfind (fn {actual_ops, overloaded_op, ...} =>
          myfind (fn (t, s) =>
                  if s = n andalso Lib.can (Type.match_type t) ty then
                    SOME overloaded_op
                  else
                    NONE)
          actual_ops)
  oinfo

fun rev_append [] rest = rest
  | rev_append (x::xs) rest = rev_append xs (x::rest)

fun merge_oinfos O1 O2 = let
  fun cmp (op1:overloaded_op_info, op2:overloaded_op_info) =
    String.compare(#overloaded_op op1, #overloaded_op op2)
  val O1_sorted = Listsort.sort cmp O1
  val O2_sorted = Listsort.sort cmp O2
  fun merge acc op1s op2s =
    case (op1s, op2s) of
      ([], x) => rev_append acc x
    | (x, []) => rev_append acc x
    | (op1::op1s', op2::op2s') => let
      in
        case String.compare (#overloaded_op op1, #overloaded_op op2) of
          LESS => merge (op1::acc) op1s' op2s
        | EQUAL => let
            val name = #overloaded_op op1
            val ty1 = #base_type op1
            val ty2 = #base_type op2
            val newty =
              case type_compare(ty1, ty2) of
                NONE =>
                  raise OVERLOAD_ERR ("Incompatible types for operator "^ name)
              | SOME LESS => ty2
              | _ => ty1
            val newopinfo =
              {overloaded_op = name, base_type = newty,
               actual_ops =
               Lib.op_union compare_real_things
               (#actual_ops op1) (#actual_ops op2)}
          in
            merge (newopinfo::acc) op1s' op2s'
          end
        | GREATER => merge (op2::acc) op1s op2s'
      end
in
  merge [] O1_sorted O2_sorted
end


