structure Overload :> Overload =
struct

open HolKernel Lexis

(* invariant on the type overloaded_op_info;
     base_type is the anti-unification of all the types in the actual_ops
     list
   invariant on the overload_info list:
     all members of the list have non-empty actual_ops lists
*)

type const_rec = {Name : string, Ty : hol_type, Thy : string}

fun lose_constrec_ty {Name,Ty,Thy} = {Name = Name, Thy = Thy}

type overloaded_op_info =
  {overloaded_op: string, base_type : Type.hol_type,
   actual_ops : const_rec list}
type overload_info = (overloaded_op_info list *
                      ({Name:string,Thy:string} * string) list)

val null_oinfo = ([],[])

fun oinfo_ops (oi,_) = oi

fun update_assoc k v [] = [(k,v)]
  | update_assoc k v ((k',v')::kvs) = if k = k' then (k,v)::kvs
                                      else (k',v')::update_assoc k v kvs

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
             val (tyop1,args1) = dest_type ty1
             val (tyop2,args2) = dest_type ty2
           in
             if tyop1 = tyop2 then
               mmap au (ListPair.zip (args1, args2)) >-
               (fn tylist => return (mk_type(tyop1, tylist)))
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
  List.find (fn x => #overloaded_op x = s) (#1 overloads)
fun is_overloaded (overloads:overload_info) s =
  List.exists (fn x => #overloaded_op x = s) (#1 overloads)

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

fun remove_overloaded_form s (oinfo:overload_info) = let
  val (op2cnst, cnst2op) = oinfo
  val (okopc, badopc) = Lib.partition (fn x => #overloaded_op x <> s) op2cnst
  (* will keep okopc, but should now remove from cnst2op all pairs of the form
       (c, s)
     where c is an actual op from one of the badopc and s is the s above *)
  val allbad_ops =
    List.concat (map (map lose_constrec_ty o #actual_ops) badopc)
  fun goodcop (crec, str) =
    str <> s orelse
    Lib.mem crec allbad_ops
  val okcop = List.filter goodcop cnst2op
in
  (okopc, okcop)
end

(* a predicate on pairs of operations and types that returns true if
   they're equal, given that two types are equal if they can match
   each other *)
fun ntys_equal {Ty = ty1,Name = n1, Thy = thy1}
               {Ty = ty2, Name = n2, Thy = thy2} =
  type_compare (ty1, ty2) = SOME EQUAL andalso n1 = n2 andalso thy1 = thy2


(* put a new overloading resolution into the database.  If it's already
   there for a given operator, don't mind.  In either case, make sure that
   it's at the head of the list, meaning that it will be the first choice
   in ambigous resolutions. *)
fun add_actual_overloading {opname, realname, realthy} oinfo = let
  val cnst = prim_mk_const{Name = realname, Thy = realthy}
    handle HOL_ERR _ =>
      raise OVERLOAD_ERR ("No such constant: "^realthy^"$"^realname)
  val newrec = {Ty = type_of cnst, Name = realname, Thy = realthy}
  val newrec' = lose_constrec_ty newrec
  val (opc0, cop0) = oinfo
  val opc =
    if is_overloaded oinfo opname then let
      val {base_type, ...} = valOf (info_for_name oinfo opname)
      val newbase = anti_unify base_type (#Ty newrec)
    in
      valOf (fupd_list_at_P (fn x => #overloaded_op x = opname)
             ((fupd_actual_ops
               (fn ops =>
                newrec :: Lib.op_set_diff ntys_equal ops [newrec])) o
              (fupd_base_type (fn b => newbase)))
             opc0)
    end
    else
      {actual_ops = [newrec], overloaded_op = opname,
       base_type = #Ty newrec} ::
      opc0
  val cop = if opname <> realname then update_assoc newrec' opname cop0
            else (* opname = realname - possible that newrec binds to some
                                        other in the map; need to remove
                                        this *)
              List.filter (fn (r,v) => r <> newrec') cop0
in
  (opc, cop)
end


fun myfind f [] = NONE
  | myfind f (x::xs) = case f x of (v as SOME _) => v | NONE => myfind f xs

fun overloading_of_term (oinfo:overload_info) t =
  if not (Term.is_const t) then NONE
  else
    Option.map #2
    (Lib.assoc1 (lose_constrec_ty (Term.dest_thy_const t)) (#2 oinfo))

fun overloading_of_nametype (oinfo:overload_info) r =
  Option.map #2 (Lib.assoc1 r (#2 oinfo))

fun rev_append [] rest = rest
  | rev_append (x::xs) rest = rev_append xs (x::rest)

fun compare_crec ({Name = n1, Thy = thy1},
                  {Name = n2, Thy = thy2}) =
  case String.compare(thy1, thy2) of
    EQUAL => String.compare (n1, n2)
  | x => x

fun merge_oinfos (O1:overload_info) (O2:overload_info) = let
  fun cmp (op1:overloaded_op_info, op2:overloaded_op_info) =
    String.compare(#overloaded_op op1, #overloaded_op op2)
  val O1ops_sorted = Listsort.sort cmp (#1 O1)
  val O2ops_sorted = Listsort.sort cmp (#1 O2)
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
    infix ##
    val O1cops_sorted = Listsort.sort (compare_crec o (#1 ## #1)) (#2 O1)
    val O2cops_sorted = Listsort.sort (compare_crec o (#1 ## #1)) (#2 O2)
    fun merge_cops acc cop1s cop2s =
      case (cop1s, cop2s) of
        ([], x) => rev_append acc x
      | (x, []) => rev_append acc x
      | (r1::r1s, r2::r2s) => let
        in
          case compare_crec(#1 r1, #1 r2) of
            LESS => merge_cops (r1::acc) r1s cop2s
          | GREATER => merge_cops (r2::acc) cop1s r2s
          | EQUAL => let
            in
              if #2 r1 <> #2 r2 then
                HOL_MESG ("Merging overload information: "^
                          "arbitrarily choosing to map "^
                          #Thy (#1 r1)^"$"^ #Name (#1 r1)^" to "^ #2 r2)
              else ();
              merge_cops (r1::acc) r1s r2s
            end
        end
in
  (merge [] O1ops_sorted O2ops_sorted,
   merge_cops [] O1cops_sorted O2cops_sorted)
end

fun known_constants (oi:overload_info) = map #overloaded_op (#1 oi)

fun remove_omapping crec str oplist =
  case oplist of
    [] => []
  | (r::rs) =>
      if #overloaded_op r = str then let
        fun ok_actual oprec = lose_constrec_ty oprec <> crec
        val new_rec0 = fupd_actual_ops (List.filter ok_actual) r
      in
        if (null (#actual_ops new_rec0)) then rs
        else new_rec0::rs
      end
      else r::remove_omapping crec str rs


fun remove_mapping str crec (oi:overload_info) =
  (remove_omapping crec str (#1 oi),
   List.filter (fn (r,str') => r <> crec orelse str <> str') (#2 oi))


end (* Overload *)