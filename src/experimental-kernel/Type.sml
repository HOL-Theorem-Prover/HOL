structure Type :> Type =
struct

open Feedback Lib Type_dtype KernelTypes

infix |->
infixr -->

type hol_type = Type_dtype.hol_type

val WARN = HOL_WARNING "Type"
val ERR = mk_HOL_ERR "Type"

fun typesig () = Context.typesig (Context.snapshot())
fun upd_typesig f = Context.update (Context.map_typesig f)
fun genupd_typesig f =
    Context.gen_update (fn c =>
      let val (new, r) = f (Context.typesig c)
      in (Context.map_typesig (fn _ => new) c, r) end)

fun type_epoch () = KernelSig.symtab_epoch (typesig())
fun display_name_of_id id = KernelSig.display_name_of_id (typesig()) id

fun prim_delete_type (k as {Thy, Tyop}) =
    if KernelSig.is_sealed_thy Thy then
      raise ERR "prim_delete_type"
            ("target theory \"" ^ Thy ^
             "\" is sealed; cross-theory deletes are refused")
    else
      upd_typesig (#1 o KernelSig.retire_name {Thy = Thy, Name = Tyop})

fun prim_new_type {Thy,Tyop} n = let
  val _ = n >= 0 orelse failwith "invalid arity"
  val _ = not (KernelSig.is_sealed_thy Thy) orelse
          raise ERR "prim_new_type"
                ("target theory \"" ^ Thy ^
                 "\" is sealed; cross-theory mints are refused")
in
  upd_typesig (#1 o KernelSig.insert ({Thy=Thy,Name=Tyop}, n))
end

fun thy_types s = let
  fun foldthis (kn,(_,arity),acc) =
      if #Thy kn = s then (#Name kn, arity) :: acc
      else acc
in
  KernelSig.foldl foldthis [] (typesig())
end

fun del_segment s =
    if KernelSig.is_sealed_thy s then
      raise ERR "del_segment"
            ("theory \"" ^ s ^ "\" is sealed; segment delete refused")
    else
      upd_typesig (KernelSig.del_segment s)

(*---------------------------------------------------------------------------*
 * Builtin type operators (fun, bool, ind). These are in every HOL           *
 * signature, and it is convenient to nail them down here.                   *
 *---------------------------------------------------------------------------*)

local
  fun insert knm_aty = genupd_typesig (KernelSig.insert knm_aty)
in
val fun_tyid  = insert({Thy = "min", Name = "fun"},  2)
val fun_tyc   = (fun_tyid, 2)
val bool_tyid = insert({Thy = "min", Name = "bool"}, 0)
val ind_tyid  = insert({Thy = "min", Name = "ind"},  0)
end

val bool = Tyapp ((bool_tyid, 0), [])
val ind  = Tyapp ((ind_tyid,  0), [])

fun uptodate_kname knm =
    KernelSig.isSuccess (KernelSig.peek (typesig(), knm))
fun uptodate_type (Tyv s) = true
  | uptodate_type (Tyapp((info,_), args)) =
    KernelSig.uptodate_id (typesig()) info andalso
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
  val possibilities = KernelSig.listName (typesig()) s
in
  case possibilities of
    [] => raise ERR caller ("No such type: "^s)
  | [x] => #2 x
  | x::xs => (WARN caller ("More than one possibility for "^s); #2 x)
end

fun make_type (tyc as (_,arity)) Args (fnstr,name) =
    if arity = length Args then Tyapp(tyc,Args)
    else raise ERR fnstr
         (String.concat
            [name," needs ", int_to_string arity,
             " arguments, but was given ", int_to_string(length Args)])

fun mk_type (opname, args) =
    make_type (first_decl "mk_type" opname) args ("mk_type", opname)

fun is_type (Tyapp _) = true | is_type _ = false

fun mk_thy_type {Thy, Tyop, Args} =
    let
      open KernelSig
      val knm = {Thy=Thy, Name = Tyop}
    in
      case peek(typesig(), knm) of
          Failure (NoSuchThy _) =>
          raise ERR "mk_thy_type" ("theory " ^ Thy ^ " is not in ancestry")
        | Failure _ =>
          raise ERR "mk_thy_type"
                ("the type operator "^quote Tyop^
                 " has not been declared in theory "^quote Thy^".")
        | Success const =>
          make_type const Args ("mk_thy_type", name_toString knm)
    end

fun dest_thy_typeid (Tyv _) =
    raise ERR "dest_thy_typeid" "Type a variable"
  | dest_thy_typeid (Tyapp((tyc,_), args)) =
    {Thy = KernelSig.seg_of tyc, Tyop = tyc, Args = args}

(* Skips the uptodate/display check — see the corresponding note in
   src/0/Type.sml. *)
fun dest_thy_type (Tyv _) = raise ERR "dest_thy_type" "Type a variable"
  | dest_thy_type (Tyapp((tyc,_), args)) =
    {Thy = KernelSig.seg_of tyc, Tyop = KernelSig.name_of tyc, Args = args}

fun dest_type (ty as Tyapp _) =
    let val {Tyop,Args,...} = dest_thy_type ty
    in
      (Tyop, Args)
    end
  | dest_type _ = raise ERR "dest_type" ""

fun decls s = let
  fun foldthis ({Thy,Name},v,acc) = if Name = s then {Thy=Thy,Tyop=Name}::acc
                                    else acc
in
  KernelSig.foldl foldthis [] (typesig())
end

fun op_arity {Thy,Tyop} =
    case KernelSig.peek(typesig(), {Thy=Thy,Name=Tyop}) of
        KernelSig.Success(_,i) => SOME i
      | _ => NONE

fun compare (Tyv s1, Tyv s2) = String.compare(s1, s2)
  | compare (Tyv _, _) = LESS
  | compare (Tyapp _, Tyv _) = GREATER
  | compare (Tyapp((i,_), iargs), Tyapp((j,_), jargs)) =
      case KernelSig.id_compare(i,j) of
        EQUAL => Lib.list_compare compare (iargs, jargs)
      | x => x

val empty_tyset = HOLset.empty compare

(*---------------------------------------------------------------------------*
 * The variables in a type.                                                  *
 *---------------------------------------------------------------------------*)

fun type_vars_acc (Tyapp(_,Args)) vlist = type_varsl_acc Args vlist
  | type_vars_acc v vlist = Lib.insert v vlist
and type_varsl_acc L vlist = rev_itlist type_vars_acc L vlist

fun type_vars ty = type_vars_acc ty []
fun type_varsl L = type_varsl_acc L []

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

fun (ty1 --> ty2) = Tyapp(fun_tyc, [ty1, ty2])

fun dom_rng (Tyv _)  = raise ERR "dom_rng" "Type a variable"
  | dom_rng (Tyapp(tyc, [X,Y])) =
      if tyc = fun_tyc then (X, Y)
      else raise ERR "dom_rng" "Type not a function type"
  | dom_rng _ = raise ERR "dom_rng" "Type not a function type"

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
                           WARN "mk_vartype"
                                ("non-standard syntax: \""^ String.toString s ^
                                 "\"")
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
