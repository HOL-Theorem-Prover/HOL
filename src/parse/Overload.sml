structure Overload :> Overload =
struct

open HolKernel Lexis

(* invariant on the type overloaded_op_info;
     base_type is the anti-unification of all the types in the actual_ops
     list
   invariant on the overload_info list:
     all members of the list have non-empty actual_ops lists
*)

type overloaded_op_info = {
  overloaded_op: string,
  base_type : Type.hol_type,
  actual_ops : (Type.hol_type * string * string) list}
type overload_info = overloaded_op_info list

exception OVERLOAD_ERR of string

local
  open stmonad Lib Type
  infix >- >>
  fun lookup n (env,avds) =
    case assoc1 n env of
      NONE => ((env,avds), NONE)
    | SOME (_,v) => ((env,avds), SOME v)
  fun extend x (env,avds) = ((x::env,avds), ())
  (* invariant on type generation part of state:
       not (next_var MEM sofar)
  *)
  fun newtyvar (env, (next_var, sofar)) = let
    val new_sofar = next_var::sofar
    val new_next = gen_variant tyvar_vary sofar (tyvar_vary next_var)
    (* new_next can't be in new_sofar because gen_variant ensures that
       it won't be in sofar, and tyvar_vary ensures it won't be equal to
       next_var *)
  in
    ((env, (new_next, new_sofar)), mk_vartype next_var)
  end

  fun au (ty1, ty2) =
    if ty1 = ty2 then return ty1
    else
      lookup (ty1, ty2) >-
      (fn result =>
       case result of
         NONE =>
           if not (is_vartype ty1) andalso not (is_vartype ty2) then let
             val {Tyop = tyop1, Args = args1} = dest_type ty1
             val {Tyop = tyop2, Args = args2} = dest_type ty2
           in
             if tyop1 = tyop2 then
               mmap au (ListPair.zip (args1, args2)) >-
               (fn tylist => return (mk_type{Tyop = tyop1, Args = tylist}))
             else
               newtyvar >- (fn new_ty =>
                            extend ((ty1, ty2), new_ty) >>
                            return new_ty)
           end
           else
             newtyvar >- (fn new_ty =>
                          extend ((ty1, ty2), new_ty) >>
                          return new_ty)
        | SOME v => return v)

  fun initial_state (ty1, ty2) = let
    val avoids = map dest_vartype (type_varsl [ty1, ty2])
    val first_var = gen_variant tyvar_vary avoids "'a"
  in
    ([], (first_var, avoids))
  end
  fun generate_iterates n f x =
    if n <= 0 then []
    else x::generate_iterates (n - 1) f (f x)

  fun canonicalise ty = let
    val tyvars = type_vars ty
    val replacements =
      map mk_vartype (generate_iterates (length tyvars) tyvar_vary "'a")
    val subst =
      ListPair.map (fn (ty1, ty2) => Lib.|->(ty1, ty2)) (tyvars, replacements)
  in
    type_subst subst ty
  end
in
  fun anti_unify ty1 ty2 = let
    val (_, result) = au (ty1, ty2) (initial_state (ty1, ty2))
  in
    canonicalise result
  end
end

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

fun remove_overloaded_form s (oinfo:overload_info) =
  List.filter (fn x => #overloaded_op x <> s) oinfo

(* a predicate on pairs of operations and types that returns true if
   they're equal, given that two types are equal if they can match
   each other *)
fun ntys_equal (ty1,n1,thy1) (ty2,n2,thy2) =
  type_compare (ty1, ty2) = SOME EQUAL andalso n1 = n2 andalso thy1 = thy2


(* put a new overloading resolution into the database.  If it's already
   there for a given operator, don't mind.  In either case, make sure that
   it's at the head of the list, meaning that it will be the first choice
   in ambigous resolutions. *)
fun add_actual_overloading {opname, realname, realtype, realthy} oinfo =
  if is_overloaded oinfo opname then let
    val {base_type, ...} = valOf (info_for_name oinfo opname)
    val newbase = anti_unify base_type realtype
  in
    valOf (fupd_list_at_P (fn x => #overloaded_op x = opname)
           ((fupd_actual_ops
             (fn ops =>
              (realtype, realname, realthy) ::
              Lib.op_set_diff ntys_equal ops [(realtype,realname,realthy)])) o
            (fupd_base_type (fn b => newbase)))
           oinfo)
  end
  else
    {actual_ops = [(realtype, realname, realthy)],
     overloaded_op = opname,
     base_type = realtype} ::
    oinfo


fun myfind f [] = NONE
  | myfind f (x::xs) = case f x of (v as SOME _) => v | NONE => myfind f xs

fun overloading_of_term (oinfo:overload_info) t =
  if not (Term.is_const t) then NONE
  else let
    val {Name,Ty,Thy} = Term.dest_thy_const t
  in
    myfind (fn {actual_ops,overloaded_op,...} =>
            myfind (fn (t,s,thy) =>
                    if s = Name andalso thy = Thy andalso
                       Lib.can (Type.match_type t) Ty
                    then
                      SOME overloaded_op
                    else
                      NONE)
            actual_ops)
    oinfo
  end

fun overloading_of_nametype oinfo {Name = n, Thy = th, Ty = ty} =
  myfind (fn {actual_ops, overloaded_op, ...} =>
          myfind (fn (t, s, th') =>
                  if s = n andalso th' = th andalso
                     Lib.can (Type.match_type t) ty
                  then
                    SOME overloaded_op
                  else
                    NONE)
          actual_ops)
  (oinfo : overload_info)

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
            val newty = anti_unify ty1 ty2
            val newopinfo =
              {overloaded_op = name, base_type = newty,
               actual_ops =
               Lib.op_union ntys_equal (#actual_ops op1) (#actual_ops op2)}
          in
            merge (newopinfo::acc) op1s' op2s'
          end
        | GREATER => merge (op2::acc) op1s op2s'
      end
in
  merge [] O1_sorted O2_sorted
end


end (* Overload *)