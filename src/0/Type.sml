(* ===================================================================== *)
(* FILE          : Type.sml                                              *)
(* DESCRIPTION   : HOL types.                                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Type signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* Modified      : September 22, 1997, Ken Larsen  (functor removal)     *)
(*                 April 12, 1998, Konrad Slind                          *)
(*                 July, 2000, Konrad Slind                              *)
(* ===================================================================== *)

structure Type :> Type =
struct

open Feedback Lib KernelTypes;   infix |->;

type hol_type = KernelTypes.hol_type;

val ERR = mk_HOL_ERR "Type";
val WARN = HOL_WARNING "Type";


(*---------------------------------------------------------------------------
              Create the signature for HOL types
 ---------------------------------------------------------------------------*)

val typesig = KernelSig.new_table()


(*---------------------------------------------------------------------------*
 * Builtin type operators (fun, bool, ind). These are in every HOL           *
 * signature, and it is convenient to nail them down here.                   *
 *---------------------------------------------------------------------------*)

local open KernelSig
in
val fun_tyid = insert(typesig, {Thy = "min", Name = "fun"}, 2)
val fun_tyc = (fun_tyid, 2)
val bool_tyid = insert(typesig, {Thy = "min", Name = "bool"}, 0)
val ind_tyid = insert(typesig, {Thy = "min", Name = "ind"}, 0)
end


(*---------------------------------------------------------------------------
        Some basic values
 ---------------------------------------------------------------------------*)

val bool = Tyapp ((bool_tyid,0),[])
val ind  = Tyapp ((ind_tyid,0), []);

(*---------------------------------------------------------------------------
       Function types
 ---------------------------------------------------------------------------*)

infixr 3 -->;
fun (X --> Y) = Tyapp (fun_tyc, [X,Y]);

fun dom_rng (Tyapp(tyc,[X,Y])) =
      if tyc=fun_tyc then (X,Y)
      else raise ERR "dom_rng" "not a function type"
  | dom_rng _ = raise ERR "dom_rng" "not a function type";

(*---------------------------------------------------------------------------*
 * Create a compound type, in a specific segment, and in the current theory. *
 *---------------------------------------------------------------------------*)

fun make_type (tyc as (_,arity)) Args (fnstr,name) =
  if arity = length Args then Tyapp(tyc,Args) else
  raise ERR fnstr (String.concat
      [name," needs ", int_to_string arity,
       " arguments, but was given ", int_to_string(length Args)]);

fun mk_thy_type {Thy,Tyop,Args} = let
  open KernelSig
  val knm = {Thy=Thy, Name = Tyop}
in
  case peek(typesig,{Thy=Thy,Name=Tyop}) of
    SOME const => make_type const Args ("mk_thy_type", name_toString knm)
  | NONE => raise ERR "mk_thy_type"
                      ("the type operator "^quote Tyop^
                       " has not been declared in theory "^quote Thy^".")
end

fun decls nm = let
  fun foldthis({Thy,Name},_,acc) = if Name = nm then
                                     {Tyop=Name,Thy=Thy} :: acc
                                   else acc
in
  KernelSig.foldl foldthis [] typesig
end

local
  fun first_decl Tyop = let
    fun foldthis({Thy,Name},tycon,acc) =
        if Name = Tyop then tycon :: acc
        else acc
  in
    case KernelSig.foldl foldthis [] typesig of
      [] => raise ERR "mk_type" (Lib.quote Tyop^" has not been declared")
    | [c] => c
    | c::_ => (WARN "mk_type" "more than one possibility"; c)
  end
in

fun mk_type (Tyop,Args) =
    make_type (first_decl Tyop) Args ("mk_type",Tyop);
end

(*---------------------------------------------------------------------------*
 * Take a type apart.                                                        *
 *---------------------------------------------------------------------------*)

local open KernelTypes KernelSig
in
fun break_type (Tyapp p) = p | break_type _ = raise ERR "break_type" "";

fun dest_thy_type (Tyapp((tyc,_),A)) = {Thy=seg_of tyc,Tyop=name_of tyc,Args=A}
  | dest_thy_type _ = raise ERR "dest_thy_type" "";

fun dest_type (Tyapp((tyc,_),A)) = (name_of tyc, A)
  | dest_type _ = raise ERR "dest_type" ""
end;

(*---------------------------------------------------------------------------*
 * Return arity of putative type operator                                    *
 *---------------------------------------------------------------------------*)

fun op_arity {Thy,Tyop} =
    case KernelSig.peek(typesig,{Thy=Thy,Name=Tyop}) of
      SOME (id, a) => SOME a
    | NONE => NONE

(*---------------------------------------------------------------------------
       Declared types in a theory segment
 ---------------------------------------------------------------------------*)

fun thy_types s = let
  fun xlate (knm, (id,arity)) = (KernelSig.name_of id, arity)
in
  map xlate (KernelSig.listThy typesig s)
end;


(*---------------------------------------------------------------------------*
 *         Type variables                                                    *
 *---------------------------------------------------------------------------*)

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

fun dest_vartype (Tyv s) = s
  | dest_vartype _ = raise ERR "dest_vartype" "not a type variable";

fun is_vartype (Tyv _) = true | is_vartype _ = false;
val is_type = not o is_vartype;

(*---------------------------------------------------------------------------*
 * The variables in a type.                                                  *
 *---------------------------------------------------------------------------*)

local fun tyvars (Tyapp(_,Args)) vlist = tyvarsl Args vlist
        | tyvars v vlist = Lib.insert v vlist
      and tyvarsl L vlist = rev_itlist tyvars L vlist
in
fun type_vars ty = rev(tyvars ty [])
fun type_varsl L = rev(tyvarsl L [])
end;


(*---------------------------------------------------------------------------
    Does there exist a type variable v in a type such that P(v) holds.
    Returns false if there are no type variables in the type.
 ---------------------------------------------------------------------------*)

fun exists_tyvar P =
 let fun occ (w as Tyv _) = P w
       | occ (Tyapp(_,Args)) = Lib.exists occ Args
 in occ end;

(*---------------------------------------------------------------------------
     Does a type variable occur in a type
 ---------------------------------------------------------------------------*)

fun type_var_in v =
  if is_vartype v then exists_tyvar (equal v)
                  else raise ERR "type_var_occurs" "not a type variable"

(*---------------------------------------------------------------------------*
 * Substitute in a type, trying to preserve existing structure.              *
 *---------------------------------------------------------------------------*)

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


(*---------------------------------------------------------------------------*
 * Is a type polymorphic?                                                    *
 *---------------------------------------------------------------------------*)

fun polymorphic (Tyv _) = true
  | polymorphic (Tyapp(_,Args)) = exists polymorphic Args


(*---------------------------------------------------------------------------
         This matching algorithm keeps track of identity bindings
         v |-> v in a separate area. This eliminates the need for
         post-match normalization of substitutions coming from the
         matching algorithm.
 ---------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_type" s
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
in
fun tymatch [] [] Sids = Sids
  | tymatch ((v as Tyv name)::ps) (ty::obs) (Sids as (S,ids)) =
     tymatch ps obs
       (case lookup v ids S
         of NONE => if v=ty then (S,v::ids) else ((v |-> ty)::S,ids)
          | SOME ty1 => if ty1=ty then Sids else
                        MERR ("double bind on type variable "^name))
  | tymatch (Tyapp(c1,A1)::ps) (Tyapp(c2,A2)::obs) Sids =
      if c1=c2 then tymatch (A1@ps) (A2@obs) Sids
      else let val n1 = KernelSig.id_toString (fst c1)
               val n2 = KernelSig.id_toString (fst c2)
           in MERR ("attempt to match different tyops: "^n1^" against "^n2)
           end
  | tymatch any other thing = MERR "different constructors"
end

fun raw_match_type pat ob Sids = tymatch [pat] [ob] Sids

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = match_type_in_context pat ob []



(*---------------------------------------------------------------------------
        An order on types
 ---------------------------------------------------------------------------*)

fun compare (Tyv s1, Tyv s2) = String.compare (s1,s2)
  | compare (Tyv _, _) = LESS
  | compare (Tyapp _, Tyv _) = GREATER
  | compare (Tyapp((c1,_),A1), Tyapp((c2,_),A2)) =
      case KernelSig.id_compare (c1, c2)
       of EQUAL => Lib.list_compare compare (A1,A2)
        |   x   => x;

(*---------------------------------------------------------------------------
     Automatically generated type variables. The unusual names make
     it unlikely that the names will clash with user-created
     type variables.
 ---------------------------------------------------------------------------*)

local val gen_tyvar_prefix = "%%gen_tyvar%%"
      fun num2name i = gen_tyvar_prefix^Lib.int_to_string i
      val nameStrm   = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun gen_tyvar () = Tyv(state(next nameStrm))

fun is_gen_tyvar (Tyv name) = String.isPrefix gen_tyvar_prefix name
  | is_gen_tyvar _ = false;
end;

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

end (* Type *)
