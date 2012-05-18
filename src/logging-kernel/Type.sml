structure Type :> Type =
struct

open Feedback Lib

infix |->
infixr -->

val WARN = HOL_WARNING "Type";
fun ERR f msg = HOL_ERR {origin_structure = "Type",
                         origin_function = f,
                         message = msg}

type type_key = {Thy : string, Tyop : string }
type type_info = KernelSig.kernelid * int

val operator_table = KernelSig.new_table()

fun prim_delete_type (k as {Thy, Tyop}) =
    ignore (KernelSig.retire_name(operator_table, {Thy = Thy, Name = Tyop}))

fun prim_new_type {Thy,Tyop} n = let
  val _ = n >= 0 orelse failwith "invalid arity"
in
  ignore (KernelSig.insert(operator_table,{Thy=Thy,Name=Tyop},n))
end

fun thy_types s = let
  fun foldthis (kn,(_,arity),acc) =
      if #Thy kn = s then (#Name kn, arity) :: acc
      else acc
in
  KernelSig.foldl foldthis [] operator_table
end

fun del_segment s = KernelSig.del_segment(operator_table, s)

fun minseg s = {Thy = "min", Tyop = s}
val _ = prim_new_type (minseg "fun") 2
val _ = prim_new_type (minseg "bool") 0
val _ = prim_new_type (minseg "ind") 0

val funref = #1 (KernelSig.find(operator_table, {Thy="min", Name = "fun"}))

datatype hol_type = Tyv of string
                  | Tyapp of KernelSig.kernelid * hol_type list

fun uptodate_type (Tyv s) = true
  | uptodate_type (Tyapp(info, args)) = KernelSig.uptodate_id info andalso
                                        List.all uptodate_type args

fun dest_vartype (Tyv s) = s
  | dest_vartype _ = raise ERR "dest_vartype" "Type not a vartype"

fun is_vartype (Tyv _) = true
  | is_vartype _ = false

val gen_tyvar_prefix = "%%gen_tyvar%%"

fun num2name i = gen_tyvar_prefix ^ Lib.int_to_string i
val nameStrm = Lib.mk_istream (fn x => x + 1) 0 num2name

fun gen_tyvar () = Tyv (state(next nameStrm))

fun is_gen_tyvar (Tyv name) = String.isPrefix gen_tyvar_prefix name
  | is_gen_tyvar _ = false;

fun first_decl caller s = let
  val possibilities = KernelSig.listName operator_table s
in
  case possibilities of
    [] => raise ERR caller ("No such type: "^s)
  | [x] => #2 x
  | x::xs => (WARN caller ("More than one possibility for "^s); #2 x)
end

fun mk_type (opname, args) = let
  val (id,aty) = first_decl "mk_type" opname
in
  if length args = aty then
    Tyapp (id, args)
  else
    raise ERR "mk_type"
              ("Expecting "^Int.toString aty^" arguments for "^opname)
end

val bool = mk_type("bool", [])
val ind = mk_type("ind", [])

fun dest_type (Tyv _) = raise ERR "dest_type" "Type a variable"
  | dest_type (Tyapp(id, args)) = let
      val {Thy, Name} = KernelSig.name_of_id id
    in
      (Name, args)
    end

fun is_type (Tyapp _) = true | is_type _ = false

fun mk_thy_type {Thy, Tyop, Args} =
    case KernelSig.peek(operator_table, {Thy = Thy, Name = Tyop}) of
      NONE => raise ERR "mk_thy_type" ("No such type: "^Thy ^ "$" ^ Tyop)
    | SOME (i,arity) =>
      if arity = length Args then Tyapp(i, Args)
      else raise ERR "mk_thy_type" ("Expecting "^Int.toString arity^
                                    " arguments for "^Tyop)

fun dest_thy_type (Tyv _) = raise ERR "dest_thy_type" "Type a variable"
  | dest_thy_type (Tyapp(id, args)) =
    {Thy = KernelSig.seg_of id, Tyop = KernelSig.name_of id, Args = args}

fun decls s = let
  fun foldthis ({Thy,Name},v,acc) = if Name = s then {Thy=Thy,Tyop=Name}::acc
                                    else acc
in
  KernelSig.foldl foldthis [] operator_table
end

fun op_arity {Thy,Tyop} =
    Option.map (#2) (KernelSig.peek(operator_table, {Thy=Thy,Name=Tyop}))

fun type_vars_set acc [] = acc
  | type_vars_set acc ((t as Tyv s) :: rest) =
      type_vars_set (HOLset.add(acc, t)) rest
  | type_vars_set acc (Tyapp(_, args) :: rest) =
      type_vars_set acc (args @ rest)

fun compare0 (Tyv s1, Tyv s2) = String.compare(s1, s2)
  | compare0 (Tyv _, _) = LESS
  | compare0 (Tyapp _, Tyv _) = GREATER
  | compare0 (Tyapp(i, iargs), Tyapp(j, jargs)) = let
    in
      case KernelSig.id_compare(i,j) of
        EQUAL => Lib.list_compare compare0 (iargs, jargs)
      | x => x
    end

fun compare p = if Portable.pointer_eq p then EQUAL
                else compare0 p

val empty_tyset = HOLset.empty compare

fun type_vars ty = HOLset.listItems (type_vars_set empty_tyset [ty])

val type_varsl = HOLset.listItems o type_vars_set empty_tyset

fun exists_tyvar P = let
  fun occ (w as Tyv _) = P w
    | occ (Tyapp(_, Args)) = List.exists occ Args
in
  occ
end

fun type_var_in v =
  if is_vartype v then exists_tyvar (equal v)
                  else raise ERR "type_var_in" "not a type variable"

val polymorphic = exists_tyvar (fn _ => true)

fun (ty1 --> ty2) = Tyapp(funref, [ty1, ty2])

fun dom_rng (Tyv _)  = raise ERR "dom_rng" "Type a variable"
  | dom_rng (Tyapp(i, args)) = if i = funref then (hd args, hd (tl args))
                               else raise ERR "dom_rng"
                                              "Type not a function type"

val alpha  = Tyv "'a"
val beta   = Tyv "'b";
val gamma  = Tyv "'c"
val delta  = Tyv "'d"
val etyvar = Tyv "'e"
val ftyvar = Tyv "'f"

val varcomplain = ref true
val _ = register_btrace ("Vartype Format Complaint", varcomplain)

fun mk_vartype "'a" = alpha  | mk_vartype "'b" = beta
  | mk_vartype "'c" = gamma  | mk_vartype "'d" = delta
  | mk_vartype "'e" = etyvar | mk_vartype "'f" = ftyvar
  | mk_vartype s = if Lexis.allowed_user_type_var s then Tyv s
                   else (if !varcomplain then
                           WARN "mk_vartype" "non-standard syntax"
                         else (); Tyv s)

fun ty_sub [] _ = SAME
  | ty_sub theta (Tyapp(tyc,Args))
      = (case delta_map (ty_sub theta) Args
          of SAME => SAME
           | DIFF Args' => DIFF (Tyapp(tyc, Args')))
  | ty_sub theta v =
      case Lib.subst_assoc (equal v) theta
       of NONE    => SAME
        | SOME ty => DIFF ty

fun type_subst theta = delta_apply (ty_sub theta)

(* val type_subst0 = type_subst
fun type_subst theta = Profile.profile "type_subst" (type_subst0 theta) *)


local
  fun MERR s = raise ERR "raw_match_type" s
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
in
fun tymatch [] [] Sids = Sids
  | tymatch ((v as Tyv _)::ps) (ty::obs) (Sids as (S,ids)) =
     tymatch ps obs
       (case lookup v ids S
         of NONE => if v=ty then (S,v::ids) else ((v |-> ty)::S,ids)
          | SOME ty1 => if ty1=ty then Sids else MERR "double bind")
  | tymatch (Tyapp(c1,A1)::ps) (Tyapp(c2,A2)::obs) Sids =
      if c1=c2 then tymatch (A1@ps) (A2@obs) Sids
               else MERR "different tyops"
  | tymatch any other thing = MERR "different constructors"
end
(*
fun raw_match_type (v as Tyv _) ty (Sids as (S,ids)) =
       (case lookup v ids S
         of NONE => if v=ty then (S,v::ids) else ((v |-> ty)::S,ids)
          | SOME ty1 => if ty1=ty then Sids else MERR "double bind")
  | raw_match_type (Tyapp(c1,A1)) (Tyapp(c2,A2)) Sids =
       if c1=c2 then rev_itlist2 raw_match_type A1 A2 Sids
                else MERR "different tyops"
  | raw_match_type _ _ _ = MERR "different constructors"
*)
fun raw_match_type pat ob Sids = tymatch [pat] [ob] Sids

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = match_type_in_context pat ob []


fun size acc tylist =
    case tylist of
      [] => acc
    | [] :: tys => size acc tys
    | (ty::tys1) :: tys2 => let
      in
        case ty of
          Tyv _ => size (1 + acc) (tys1 :: tys2)
        | Tyapp(_, args) => size (1 + acc) (args :: tys1 :: tys2)
      end

fun type_size ty = size 0 [[ty]]

end (* struct *)
