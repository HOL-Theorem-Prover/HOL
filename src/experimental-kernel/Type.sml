structure Type :> Type =
struct

(*
In *scratch*, type
(hol-set-executable sml-executable)
or
(hol-set-executable (concat hol-home "/bin/hol.bare"))

and type Ctrl-j.

quotation := true;
loadPath := "/usr/local/hol/hol" ^ "/sigobj" :: !loadPath;
loadPath := "/usr/local/hol/hol" ^ "/src/experimental-kernel" :: !loadPath;

app load ["Feedback","Lib","Kind","KernelSig","Lexis","Redblackmap","Binarymap","HOLset"];
*)

open Feedback Lib Rank Kind

infix |->  :>=:  :=:
infixr -->
infixr 3 ==>

val WARN = HOL_WARNING "Type";
fun ERR f msg = HOL_ERR {origin_structure = "Type",
                         origin_function = f,
                         message = msg}

(* UNCHANGEDTY is thrown internally by functions that modify types; only seen in kernel *)
exception UNCHANGEDTY;

(* used internally to avoid term rebuilding during substitution and
   type instantiation; exported to Term.inst and subst *)
exception Unchanged = Kind.Unchanged

val qcomb = Kind.qcomb
(*
(* apply a function f under "constructor" con, handling Unchanged *)
fun qcomb con f (x,y) = let
  val fx = f x
in
  let val fy = f y
  in
    con(fx, fy)
  end handle Unchanged => con(fx, y)
end handle Unchanged => let val fy = f y
                        in
                          con(x, fy)
                        end
*)


type type_key = {Thy : string, Tyop : string }
type type_info = KernelSig.kernelid * kind

val operator_table = KernelSig.new_table()

fun prim_delete_type (k as {Thy, Tyop}) =
    ignore (KernelSig.retire_name(operator_table, {Thy = Thy, Name = Tyop}))

fun prim_new_type_opr {Thy,Tyop} kd =
  ignore (KernelSig.insert(operator_table,{Thy=Thy,Name=Tyop},kd))

fun prim_new_type (r as {Thy,Tyop}) n = let
  val _ = n >= 0 orelse failwith "invalid arity"
in
  prim_new_type_opr r (mk_arity n)
end

fun thy_types s = let
  fun foldthis (kn,(_,kind),acc) =
      if #Thy kn = s then (#Name kn, arity_of kind) :: acc handle HOL_ERR _ =>
                raise ERR "thy_types" "non-arity kind in theory - use thy_type_oprs"
      else acc
in
  KernelSig.foldl foldthis [] operator_table
end

fun thy_type_oprs s = let
  fun foldthis (kn,(_,kind),acc) =
      if #Thy kn = s then (#Name kn, kind) :: acc
      else acc
in
  KernelSig.foldl foldthis [] operator_table
end

fun del_segment s = KernelSig.del_segment(operator_table, s)

fun minseg s = {Thy = "min", Tyop = s}
val _ = prim_new_type_opr (minseg "fun" ) (mk_arity 2)
val _ = prim_new_type_opr (minseg "bool") (mk_arity 0)
val _ = prim_new_type_opr (minseg "ind" ) (mk_arity 0)

(*---------------------------------------------------------------------------
                Declare the SML type of HOL types
 ---------------------------------------------------------------------------*)

type id = KernelSig.kernelid
type tyconst  =  id * kind
type tyvar = string * kind

datatype hol_type = Tyv of tyvar
                  | TyCon of tyconst
                  | TyApp of hol_type * hol_type
                  | TyAll of tyvar * hol_type
                  | TyExi of tyvar * hol_type
                  | TyAbs of tyvar * hol_type

val funref = #1 (KernelSig.find(operator_table, {Thy="min", Name = "fun"}))
val fun_tyc = TyCon (funref, mk_arity 2)

fun same_tyconst (TyCon (id1,_)) (TyCon (id2,_)) = id1 = id2
  | same_tyconst _ _ = false

fun uptodate_type (Tyv s) = true
  | uptodate_type (TyCon(info,kd)) = KernelSig.uptodate_id info
  | uptodate_type (TyApp(opr,arg)) = uptodate_type opr andalso uptodate_type arg
  | uptodate_type (TyAll(bv,body)) = uptodate_type body
  | uptodate_type (TyExi(bv,body)) = uptodate_type body
  | uptodate_type (TyAbs(bv,body)) = uptodate_type body


(*---------------------------------------------------------------------------*
 * Computing the kind or rank of a type, assuming it is well-kinded.         *
 *---------------------------------------------------------------------------*)

local
  val max = Rank.max
  val suc = Rank.suc

  fun knd_of ty k =
      case ty of
        Tyv  (_, kd) => k kd
      | TyCon(_, kd) => k kd
(*    | TyApp(opr, arg) => knd_of opr (fn kd => k (#2 (kind_dom_rng kd))) *)
(* or, if promotion, *)
      | TyApp(opr, arg) => knd_of opr (fn oprk =>
                           knd_of arg (fn argk =>
                             let val (dom,rng) = kind_dom_rng oprk
                                 val (rkS,kdS) = match_kind dom argk
                                 val _ = if null kdS then ()
                                         else raise ERR "kind_of" "malformed type application"
                                 (* val rkS = [max(rank_of argk - rank_of dom, 0)] *)
                             in k (Kind.inst_rank rkS rng)
                             end))
      | TyAbs((_, kd1), body) => knd_of body (fn kd2 => k (kd1 ==> kd2))
      | TyAll((_, kd1), body) => k (typ (rnk_of ty Lib.I)) (* NOT knd_of body k *)
      | TyExi((_, kd1), body) => k (typ (rnk_of ty Lib.I)) (* NOT knd_of body k *)
  and rnk_of ty k =
      case ty of
        TyAll((_, kd1), body) => rnk_of body (fn rk => k (max(suc(rank_of kd1), rk)))
      | TyExi((_, kd1), body) => rnk_of body (fn rk => k (max(suc(rank_of kd1), rk)))
      | _ => k (rank_of (knd_of ty Lib.I))

in
fun kind_of ty = knd_of ty Lib.I
fun kd_of ty E = kind_of ty
fun rank_of_type ty = rnk_of ty Lib.I
fun rk_of ty E = rank_of_type ty
end

fun rank_of_univ_dom (TyAll((_,kd),_)) = rank_of kd
  | rank_of_univ_dom _ = raise ERR "rank_of_univ_dom" "not a universal type"

fun rank_of_exist_dom (TyExi((_,kd),_)) = rank_of kd
  | rank_of_exist_dom _ = raise ERR "rank_of_exist_dom" "not an existential type"

(*---------------------------------------------------------------------------*
 * Computing the kind of a type, not assuming it is well-kinded.             *
 *---------------------------------------------------------------------------*)

local
  val max = Rank.max
  val suc = Rank.suc

  fun knd_of ty k =
      case ty of
        Tyv  (_, kd) => k kd
      | TyCon(_, kd) => k kd
      | TyApp(opr, arg) => knd_of opr (fn kd1 =>
             let val (dom,rng) = kind_dom_rng kd1
                                 handle HOL_ERR _ =>
                     raise ERR "check_kind_of" "type is not well-kinded"
             in knd_of arg (fn kd2 =>
                   if dom :>=: kd2 then k rng
                   else raise ERR "check_kind_of" "type is not well-kinded")
             end)
      | TyAbs((_, kd1), body) => knd_of body (fn kd2 => k (kd1 ==> kd2))
      | TyAll((_, kd1), body) => k (typ (rnk_of ty Lib.I)) (* NOT knd_of body k *)
      | TyExi((_, kd1), body) => k (typ (rnk_of ty Lib.I)) (* NOT knd_of body k *)
  and rnk_of ty k =
      case ty of
        TyAll((_, kd1), body) => rnk_of body (fn rk => k (max(suc(rank_of kd1), rk)))
      | TyExi((_, kd1), body) => rnk_of body (fn rk => k (max(suc(rank_of kd1), rk)))
      | _ => rank_of (knd_of ty Lib.I)

in
fun check_kind_of ty = knd_of ty Lib.I
fun check_rank_of ty = rnk_of ty Lib.I
end

(*---------------------------------------------------------------------------*
 * Checking that a type is well-kinded.                                      *
 * This fn should never be needed, as long as the type constructors check.   *
 *---------------------------------------------------------------------------*)

fun is_well_kinded ty = (check_kind_of ty; true) handle HOL_ERR _ => false


(*-----------------------------------------------------------------------------*
 * The kind variables of a type. Tail recursive (from Ken Larsen).             *
 *-----------------------------------------------------------------------------*)

local fun kdV (Tyv(s,kd)) k          = k (Kind.kind_vars kd)
        | kdV (TyCon(s,kd)) k        = k (Kind.kind_vars kd)
        | kdV (TyApp(opr, arg)) k    = kdV arg (fn q1 =>
                                       kdV opr (fn q2 => k (union q2 q1)))
        | kdV (TyAbs((s,kd),Body)) k = kdV Body (fn q =>
                                       k (union (Kind.kind_vars kd) q))
        | kdV (TyAll((s,kd),Body)) k = kdV Body (fn q =>
                                       k (union (Kind.kind_vars kd) q))
        | kdV (TyExi((s,kd),Body)) k = kdV Body (fn q =>
                                       k (union (Kind.kind_vars kd) q))
      fun kdVs (ty::tys) k           = kdV ty (fn q1 =>
                                       kdVs tys (fn q2 => k (union q2 q1)))
        | kdVs [] k                  = k []
in
fun kind_vars ty = kdV ty Lib.I
fun kind_varsl tys = kdVs tys Lib.I
end


(*---------------------------------------------------------------------------
                Discriminators
 ---------------------------------------------------------------------------*)

fun is_vartype   (Tyv   _) = true | is_vartype   _ = false
fun is_var_type  (Tyv   _) = true | is_var_type  _ = false
fun is_con_type  (TyCon _) = true | is_con_type  _ = false
fun is_type      (TyApp (opr,_)) = is_type opr
  | is_type      (TyCon _) = true
  | is_type      _ = false
fun is_app_type  (TyApp _) = true
  | is_app_type  _ = false
fun is_abs_type  (TyAbs _) = true
  | is_abs_type  _ = false
fun is_univ_type (TyAll _) = true
  | is_univ_type _ = false
fun is_exist_type (TyExi _) = true
  | is_exist_type _ = false

(*---------------------------------------------------------------------------*
 * Types, as seen by the user, should satisfy exactly one of                 *
 * is_var_type, is_con_type, is_app_type, is_abs_type, is_univ_type,         *
 * or is_exist_type.                                                         *
 * Legacy types will be seen as exactly one of is_vartype or is_type.        *
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*
 * Substituting kinds for kind variables of a type.                          *
 *---------------------------------------------------------------------------*)

fun prim_kind_of_tyc tyc =
  let open KernelSig
  in case peek(operator_table,KernelSig.name_of_id tyc) of
        SOME (_,kd) => kd
      | NONE => raise ERR "prim_kind_of_tyc" "not a defined type constant"
  end

fun prim_kind_of {Thy,Tyop} =
  let open KernelSig
  in case peek(operator_table,{Thy=Thy,Name=Tyop}) of
        SOME (_,kd) => kd
      | NONE => raise ERR "prim_kind_of" "not a defined type constant"
  end

(* Commenting out vacuum code:

local

fun strip_app_type ty =
   let fun strip (TyApp (Opr,Ty)) A = strip Opr (Ty::A)
         | strip ty A = (ty,A)
   in strip ty []
   end

fun make_app_type Opr Arg (fnstr,name) = TyApp(Opr,Arg)

fun list_make_app_type Opr Args (fnstr,name) =
    List.foldl (fn (Arg,acc) => make_app_type acc Arg (fnstr,name)) Opr Args

fun list_mk_app_type (Opr,Args) =
    list_make_app_type Opr Args ("list_mk_app_type","");

fun kinds_to_string (kd::kds) = " " ^ kind_to_string kd ^ "," ^ kinds_to_string kds
  | kinds_to_string    []     = ""

fun map_chg f [] = raise UNCHANGEDTY
  | map_chg f [ty] = [f ty]
  | map_chg f (ty::tys) =
      let val ty' = f ty (* may throw UNCHANGEDTY *)
          val tys' = map_chg f tys handle UNCHANGEDTY => tys
      in ty'::tys'
      end handle UNCHANGEDTY => (ty::map_chg f tys)

in

fun vacuum_opr E (opr,args) =
  if is_con_type opr then
    if null args then
      let
        val TyCon(tyc,kd) = opr (* kd will be replaced *)
val tyname = KernelSig.id_toString tyc
        val pkd = prim_kind_of_tyc tyc
        val _ = if pkd = kd then raise UNCHANGEDTY else ()
        val pkd_vars = Kind.kind_vars pkd
      in if null pkd_vars then raise ERR "vacuum_opr" ("no args: TyCon("^tyname^",pkd)") (* TyCon(tyc,pkd) *) (* set kind to primitive kind & rank *)
         else if null (Kind.kind_vars kd) then
            let (* match the primitive kind with the current kind *)
                val (rkS,kdS) = Kind.match_kind pkd kd
                (*val pkd_vars' = map (inst_rank rkS) pkd_vars*)
                fun orig_kdvar s = Lib.first (fn kd => #1(dest_var_kind kd) = s) pkd_vars
                fun revar kd = orig_kdvar (#1(dest_var_kind kd))
                fun revar_match {redex,residue} = {redex=revar redex, residue=residue}
                val kdS' = List.map revar_match kdS
                val kd' = Kind.inst_kind kdS' pkd
                val _ = if kd'=kd then raise UNCHANGEDTY else ()
            in raise ERR "vacuum_opr" ("no args: TyCon("^tyname^",kd')") (* TyCon(tyc,kd') *)
            end
         else raise UNCHANGEDTY (* opr *) (* unchanged when kind vars present *)
      end
      handle HOL_ERR _ => raise UNCHANGEDTY (* opr *) (* if eg, prim_kind_of fails *)
    else
      let
        val TyCon(tyc,kd) = opr (* kd will be replaced *)
val tyname = KernelSig.id_toString tyc
        val pkd = prim_kind_of_tyc tyc
        val _ = if pkd=kd then raise UNCHANGEDTY else ()
        (* val (c_rkS,c_kdS) = match_kind pkd kd *)
        val argkds = List.map (fn ty => kd_of ty E) args
        val (pargkds,reskd) = strip_arrow_kind pkd
        val pargkds0 = List.take(pargkds, length argkds)
        val (rkS,kdS) = match_kinds (List.map op |-> (zip pargkds0 argkds))
        (* val _ = assert null kdS *)
        val kd' = Kind.inst_rank_kind rkS kdS pkd
        val _ = if kd'=kd then raise UNCHANGEDTY else ()
        val opr' = TyCon(tyc,kd')
      in
        raise ERR "vacuum_opr" (Int.toString(length args)^" args: TyCon("^tyname^",kd')") (* list_mk_app_type (opr', args) *)
      end
      handle e as HOL_ERR {origin_function="vacuum_opr",...} => Raise e (* if eg, prim_kind_of fails *)
           | HOL_ERR _ => list_mk_app_type (opr, args) (* if eg, prim_kind_of fails *)
  else raise ERR "vacuum_head" "head of type is not a constant type"

fun vacuum_head ty = vacuum_opr [] (strip_app_type ty) handle UNCHANGEDTY => ty

val vacuum =
  let fun vac E (ty as TyApp _) =
          let val (opr,args) = strip_app_type ty in
            let val args' = map_chg (vac E) args (* may throw UNCHANGEDTY *)
            in vacuum_opr E (opr,args')
               (* if opr is not a constant type, an exception is raised *)
               handle HOL_ERR {origin_function="vacuum_head",...} => (list_mk_app_type (vac E opr, args')
                                    handle UNCHANGEDTY => list_mk_app_type (opr, args'))
                    | UNCHANGEDTY => list_mk_app_type (opr, args')
            end
            handle UNCHANGEDTY => let
            in vacuum_opr E (opr,args)
               (* if opr is not a constant type, an exception is raised *)
               handle HOL_ERR {origin_function="vacuum_head",...} => list_mk_app_type (vac E opr, args)
            end
          end
        | vac E (opr as TyCon _) = vacuum_opr E (opr,[])
        | vac E (TyAll(Bvar as (_,kd),Body)) = TyAll(Bvar,vac (kd::E) Body)
        | vac E (TyExi(Bvar as (_,kd),Body)) = TyExi(Bvar,vac (kd::E) Body)
        | vac E (TyAbs(Bvar as (_,kd),Body)) = TyAbs(Bvar,vac (kd::E) Body)
        | vac _ ty = raise UNCHANGEDTY
  in fn ty => vac [] ty handle UNCHANGEDTY => ty
  end

end (* local *)

End of vacuum code. *)


fun dest_var_type (Tyv (s,kind)) = (s,kind)
  | dest_var_type _ = raise ERR "dest_var_type" "not a type variable";

fun dest_vartype (Tyv (s,kind)) = if kind = typ 0 then s else
           raise ERR "dest_vartype" "type variable not of base kind - use dest_var_type"
  | dest_vartype _ = raise ERR "dest_vartype" "not a type variable";

val gen_tyvar_prefix = "%%gen_tyvar%%"

fun num2name i = gen_tyvar_prefix ^ Lib.int_to_string i
val nameStrm = Lib.mk_istream (fn x => x + 1) 0 num2name

fun gen_var_type kind =
       Tyv(state(next nameStrm), kind)
fun gen_tyvar () = gen_var_type (typ rho)

fun is_gen_tyvar (Tyv(name,_)) = String.isPrefix gen_tyvar_prefix name
  | is_gen_tyvar _ = false;


(*---------------------------------------------------------------------------*
 * Create a compound type, in a specific segment, and in the current theory. *
 *---------------------------------------------------------------------------*)

local
fun dest_con_type (TyCon (tyc,kd)) = (KernelSig.name_of tyc,kd)
  | dest_con_type _ = raise ERR "dest_con_type" "not a constant type"

fun namestr nm Opr = if nm <> "" then nm
                 else if is_con_type Opr then #1(dest_con_type Opr)
                 else if is_var_type Opr then #1(dest_var_type Opr)
                 else "type"
in
fun make_app_type Opr Arg (fnstr,name) =
  let val (dom,rng) = kind_dom_rng (kind_of Opr)
                      handle HOL_ERR e =>
                        raise ERR fnstr (String.concat
         ["type not well-kinded: ", namestr name Opr,
          " is not a type operator, but is applied as one:\n",
          #origin_structure e, ".", #origin_function e, ":\n", #message e])
      val kn = kind_of Arg
  in if dom :>=: kn then TyApp(Opr,Arg) else
     raise ERR fnstr (String.concat
         ["type not well-kinded: ", namestr name Opr, " needs kind ", kind_to_string dom,
          ", but was given kind ", kind_to_string kn])
  end
end

fun list_make_app_type Opr Args (fnstr,name) =
    List.foldl (fn (Arg,acc) => make_app_type acc Arg (fnstr,name)) Opr Args

fun make_type tyc Args (fnstr,name) =
  list_make_app_type (TyCon tyc) Args (fnstr,name);

(* fun mk_tyconst (id,(kind)) = (id,kind) :tyconst *)

fun prim_mk_thy_con_type {Thy,Tyop} = let
  open KernelSig
in
  case peek(operator_table,{Thy=Thy,Name=Tyop}) of
    SOME const => TyCon const
  | NONE => raise ERR "mk_thy_con_type"
                ("the type operator "^quote Tyop^
                 " has not been declared in theory "^quote Thy^".")
end

fun mk_thy_con_type {Thy,Tyop,Kind} = let
  open KernelSig
in
  case peek(operator_table,{Thy=Thy,Name=Tyop}) of
    SOME (const as (id,(kind0))) =>
           (let val (rkS,kdS) = Kind.match_kind kind0 Kind
                val Kind' = Kind.inst_rank_kind rkS kdS kind0
            in TyCon (id,Kind')
            end handle HOL_ERR _ =>
                raise ERR "mk_thy_con_type"
                            ("Not a kind instance: the type operator "^id_toString id^
                             " cannot have kind "^Kind.kind_to_string Kind^"."))
  | NONE => raise ERR "mk_thy_con_type"
                ("the type operator "^quote Tyop^
                 " has not been declared in theory "^quote Thy^".")
end

fun first_decl caller s = let
  val possibilities = KernelSig.listName operator_table s
in
  case possibilities of
    [] => raise ERR caller ("No such type: "^s)
  | [x] => #2 x
  | x::xs => (WARN caller ("More than one possibility for "^s); #2 x)
end

fun prim_mk_con_type Tyop = TyCon (first_decl "mk_con_type" Tyop)

fun mk_con_type {Tyop,Kind} = let
  open KernelSig
  val c = prim_mk_con_type Tyop
  val (id,Kind0) = case c of TyCon p => p
                           | _ => raise ERR "mk_con_type" "impossible"
in
  if can (Kind.match_kind Kind0) Kind
     then TyCon (id,Kind)
     else raise ERR "mk_con_type"
                  ("Not a kind instance: the type operator "^id_toString id^
                   " cannot have kind "^Kind.kind_to_string Kind^".")
end

fun dest_con_type (TyCon (tyc,kd)) = (KernelSig.name_of tyc,kd)
  | dest_con_type _ = raise ERR "dest_con_type" "not a constant type"

fun dest_thy_con_type (TyCon (tyc,kd)) =
      {Thy=KernelSig.seg_of tyc,Tyop=KernelSig.name_of tyc,Kind=kd}
  | dest_thy_con_type _ = raise ERR "dest_thy_con_type" "not a constant type"

fun mk_app_type (Opr,Arg) = make_app_type Opr Arg ("mk_app_type","")

fun list_mk_app_type (Opr,Args) =
    list_make_app_type Opr Args ("list_mk_app_type","")

fun dest_app_type (TyApp (Opr,Ty)) = (Opr,Ty)
  | dest_app_type _ = raise ERR "dest_app_type" "not a type application"

fun strip_app_type ty =
   let fun strip (TyApp (Opr,Ty)) A = strip Opr (Ty::A)
         | strip ty A = (ty,A)
   in strip ty []
   end

fun mk_abs_type(Tyv v, body) = TyAbs(v, body)
  | mk_abs_type _ = raise ERR "mk_abs_type" "First argument is not a variable"

fun dest_abs_type(TyAbs(v, body)) = (Tyv v, body)
  | dest_abs_type _ = raise ERR "dest_abs_type" "Not a type abstraction"

fun strip_abs_binder binder = let
  val f = case binder of
            NONE => (fn ty => if is_abs_type ty then SOME ty else NONE)
          | SOME c => (fn ty => let
                            val (rator, rand) = dest_app_type ty
                          in
                            if same_tyconst rator c andalso is_abs_type rand then
                              SOME rand
                            else NONE
                          end handle HOL_ERR _ => NONE)
  fun recurse acc ty =
      case f ty of
        NONE => (List.rev acc, ty)
      | SOME abs => let
          val (v, body) = dest_abs_type abs
        in
          recurse (v::acc) body
        end
in
  recurse []
end

val strip_abs_type = strip_abs_binder NONE

(* Universal types *)

fun mk_univ_type(Tyv v, body) =
    if is_type_kind (kind_of body) then TyAll(v, body)
    else raise ERR "mk_univ_type" "kind of body is not the base kind"
  | mk_univ_type _ = raise ERR "mk_univ_type" "First argument is not a variable"

fun dest_univ_type(TyAll(v, body)) = (Tyv v, body)
  | dest_univ_type _ = raise ERR "dest_univ_type" "Not a universal type"

fun strip_univ_binder binder = let
  val f = case binder of
            NONE => (fn ty => if is_univ_type ty then SOME ty else NONE)
          | SOME c => (fn ty => let
                            val (rator, rand) = dest_app_type ty
                          in
                            if same_tyconst rator c andalso is_univ_type rand then
                              SOME rand
                            else NONE
                          end handle HOL_ERR _ => NONE)
  fun recurse acc ty =
      case f ty of
        NONE => (List.rev acc, ty)
      | SOME univ => let
          val (v, body) = dest_univ_type univ
        in
          recurse (v::acc) body
        end
in
  recurse []
end

val strip_univ_type = strip_univ_binder NONE

(* Existential types *)

fun mk_exist_type(Tyv v, body) =
    if is_type_kind (kind_of body) then TyExi(v, body)
    else raise ERR "mk_exist_type" "kind of body is not the base kind"
  | mk_exist_type _ = raise ERR "mk_exist_type" "First argument is not a variable"

fun dest_exist_type(TyExi(v, body)) = (Tyv v, body)
  | dest_exist_type _ = raise ERR "dest_exist_type" "Not an existential type"

fun strip_exist_binder binder = let
  val f = case binder of
            NONE => (fn ty => if is_exist_type ty then SOME ty else NONE)
          | SOME c => (fn ty => let
                            val (rator, rand) = dest_app_type ty
                          in
                            if same_tyconst rator c andalso is_exist_type rand then
                              SOME rand
                            else NONE
                          end handle HOL_ERR _ => NONE)
  fun recurse acc ty =
      case f ty of
        NONE => (List.rev acc, ty)
      | SOME exist => let
          val (v, body) = dest_exist_type exist
        in
          recurse (v::acc) body
        end
in
  recurse []
end

val strip_exist_type = strip_exist_binder NONE


fun argkds_string [] = "..."
  | argkds_string (arg::args) = "(" ^ kind_to_string (kind_of arg) ^ ") => " ^ argkds_string args

fun mk_type (opname, args) =
  let val (c_id,prim_kd) = first_decl "mk_type" opname
      val (argkds,reskd) = strip_arrow_kind prim_kd
      val argkds0 = List.take(argkds, length args)
                    handle Subscript => raise ERR "mk_type"
                           ("too many arguments to type operator "^quote opname)
      val (rkS,kdS) = match_kinds (map op |-> (zip argkds0 (map kind_of args))) (* can fail *)
                      handle HOL_ERR e => raise ERR "mk_type"
                             ("the type operator "^quote opname^
                              " cannot have kind "^argkds_string args)
      val kd' = Kind.inst_rank_kind rkS kdS prim_kd
      val const' = (c_id,kd')
  in
    make_type const' args ("mk_type",opname)
  end;

fun mk_thy_type {Thy, Tyop, Args} =
    case KernelSig.peek(operator_table, {Thy = Thy, Name = Tyop}) of
      NONE => raise ERR "mk_thy_type" ("No such type: "^Thy ^ "$" ^ Tyop)
    | SOME (id,kind) =>
      let val (argkds,reskd) = strip_arrow_kind kind
          val argkds0 = List.take(argkds, length Args)
                        handle Subscript => raise ERR "mk_thy_type"
                               ("too many arguments to type operator "^Thy^"$"^Tyop)
          val (rkS,kdS) = match_kinds (map op |-> (zip argkds0 (map kind_of Args))) (* can fail *)
                          handle HOL_ERR e => raise ERR "mk_thy_type"
                                 ("the type operator "^Thy^"$"^Tyop^
                                  " cannot have kind "^argkds_string Args)
          val kind' = Kind.inst_rank_kind rkS kdS kind
          val const' = (id,kind')
          val knm = KernelSig.name_toString {Thy=Thy, Name = Tyop}
      in make_type const' Args ("mk_thy_type", (*Tyop*)knm)
      end

val bool = mk_type("bool", [])
val ind = mk_type("ind", [])

local open KernelSig
fun break_ty0 f acc (TyCon c) = (c,acc)
  | break_ty0 f acc (TyApp (Opr,Arg)) = break_ty0 f (Arg::acc) Opr
  | break_ty0 f _ _ = raise ERR f "not a sequence of type applications of a \
                                  \type constant"
fun break_ty f ty = break_ty0 f [] ty
fun check_kd f kd =
   let val s = "; use " ^ quote (f ^ "_opr") ^ " instead."
   in if is_arity kd then () else raise ERR f ("kind of type operator is not an arity" ^ s)
   end
in
fun break_type ty = break_ty "break_type" ty;

fun dest_thy_type_opr ty =
       let val ((tyc,kd),A) = break_ty "dest_thy_type_opr" ty
       in
        {Thy=seg_of tyc,Tyop=name_of tyc,Kind=kd,Args=A}
       end;

fun dest_thy_type ty =
       let val ((tyc,kd),A) = break_ty "dest_thy_type" ty
           (* val _ = check_kd "dest_thy_type" kd *)
       in
        {Thy=seg_of tyc,Tyop=name_of tyc,Args=A}
       end;

fun dest_type_opr ty =
       let val ((tyc,kd),A) = break_ty "dest_type_opr" ty
       in (name_of tyc, kd, A)
       end;

fun dest_type ty =
       let val ((tyc,kd),A) = break_ty "dest_type" ty
           (* val _ = check_kd "dest_type" kd *)
       in (name_of tyc, A)
       end;
end;

fun decls s = let
  fun foldthis ({Thy,Name},v,acc) = if Name = s then {Thy=Thy,Tyop=Name}::acc
                                    else acc
in
  KernelSig.foldl foldthis [] operator_table
end

(*---------------------------------------------------------------------------*
 * Return kind or arity of putative type operator                            *
 *---------------------------------------------------------------------------*)

fun op_kind {Thy,Tyop} =
    case KernelSig.peek(operator_table,{Thy=Thy,Name=Tyop}) of
      SOME (id, kind) => SOME kind
    | NONE => NONE

fun op_arity r = case op_kind r
                  of SOME kind => (SOME (arity_of kind)
                                   handle HOL_ERR _ => NONE)
                   | NONE      => NONE

(*---------------------------------------------------------------------------*
 * Return rank of putative type operator                                     *
 *---------------------------------------------------------------------------*)

fun op_rank {Thy,Tyop} =
    case KernelSig.peek(operator_table,{Thy=Thy,Name=Tyop}) of
      SOME (id, kind) => SOME (rank_of kind)
    | NONE => NONE

(*---------------------------------------------------------------------------
     Support for efficient sets of type variables
 ---------------------------------------------------------------------------*)

fun safe_delete(s, i) = HOLset.delete(s, i) handle HOLset.NotFound => s

fun tyvar_compare ((s1,k1), (s2,k2)) =
       (case String.compare (s1,s2)
         of EQUAL => kind_compare (k1,k2)
          | x => x)

(*
fun tyvar_subtype ((s1,k1), (s2,k2)) =
       (s1 = s2) andalso (k2 :>=: k1)
*)

val empty_tyvarset = HOLset.empty tyvar_compare
fun tyvar_eq t1 t2 = tyvar_compare(t1,t2) = EQUAL

fun tyvar_ge ((s1,k1), (s2,k2)) =
       (s1 = s2) andalso k1 :>=: k2

fun type_var_compare (Tyv u, Tyv v) = tyvar_compare (u,v)
  | type_var_compare _ = raise ERR "type_var_compare" "variables required"

fun type_var_ge (Tyv u, Tyv v) = tyvar_ge (u,v)
  | type_var_ge _ = raise ERR "type_var_ge" "variables required";

(*
fun type_var_subtype (Tyv u, Tyv v) = tyvar_subtype (u,v)
  | type_var_subtype _ = raise ERR "type_var_subtype" "variables required"
*)

fun prim_type_con_compare (TyCon(c1,k1), TyCon(c2,k2)) =
       (case KernelSig.id_compare (c1,c2)
         of EQUAL => kind_compare (k1,k2)
          | x => x)
  | prim_type_con_compare _ = raise ERR "prim_type_con_compare" "constants required";

fun type_con_compare (TyCon(c1,k1), TyCon(c2,k2)) =
       (case KernelSig.id_compare (c1,c2)
         of EQUAL => (* kind_compare *) tycon_kind_compare (k1,k2)
          | x => x)
  | type_con_compare _ = raise ERR "type_con_compare" "constants required";

fun type_con_ge (TyCon(c1,k1), TyCon(c2,k2)) =
       (case KernelSig.id_compare (c1,c2)
         of EQUAL => k1 :=: (* :>=: *) k2
          | x => false)
  | type_con_ge _ =raise ERR "type_con_ge" "constants required";

(* ----------------------------------------------------------------------
    A total, "symmetric" ordering on types that respects alpha equivalence.
    Tyv < TyCon < TyApp < TyAll < TyExi < TyAbs
   ---------------------------------------------------------------------- *)

structure Map = Binarymap
val empty_env = Map.mkDict type_var_compare

local open Map
in
fun map_type_var_compare (env1, env2) (u,v) =
  case (peek(env1, u), peek(env2, v)) of
    (NONE, NONE) => type_var_compare(u,v)
  | (SOME _, NONE) => GREATER
  | (NONE, SOME _) => LESS
  | (SOME i, SOME j) => Int.compare(j, i)
              (* flipping i & j deliberate; mimics deBruijn implementation's
                 behaviour, which would number variables in reverse order
                 from that done here *)

fun map_type_var_ge (env1, env2) (u,v) =
  case (peek(env1, u), peek(env2, v)) of
    (NONE, NONE) => type_var_ge(u,v)
  | (SOME i, SOME j) => j = i
              (* flipping i & j deliberate; mimics deBruijn implementation's
                 behaviour, which would number variables in reverse order
                 from that done here *)
  | _ => false

fun prim_compare0 n E (u as Tyv _, v as Tyv _)     = map_type_var_compare E (u,v)
  | prim_compare0 n E (Tyv _, _)                   = LESS
  | prim_compare0 n E (TyCon _, Tyv _)             = GREATER
  | prim_compare0 n E (u as TyCon _, v as TyCon _) = prim_type_con_compare (u,v)
  | prim_compare0 n E (TyCon _, _)                 = LESS
  | prim_compare0 n E (TyApp _, Tyv _)             = GREATER
  | prim_compare0 n E (TyApp _, TyCon _)           = GREATER
  | prim_compare0 n E (TyApp p1, TyApp p2)         = Lib.pair_compare(prim_compare0 n E,prim_compare0 n E)(p1,p2)
  | prim_compare0 n E (TyApp _, _)                 = LESS
  | prim_compare0 n E (TyAll _, TyAbs _)           = LESS
  | prim_compare0 n E (TyAll _, TyExi _)           = LESS
  | prim_compare0 n (E as (env1, env2))
                 (TyAll(x1 as (_,k1),ty1),
                  TyAll(x2 as (_,k2),ty2)) =
        Lib.pair_compare(kind_compare,
                         prim_compare0 (n + 1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                        ((k1,ty1), (k2,ty2))
  | prim_compare0 n E (TyAll _, _)                 = GREATER
  | prim_compare0 n E (TyExi _, TyAbs _)           = LESS
  | prim_compare0 n (E as (env1, env2))
                 (TyExi(x1 as (_,k1),ty1),
                  TyExi(x2 as (_,k2),ty2)) =
        Lib.pair_compare(kind_compare,
                         prim_compare0 (n + 1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                        ((k1,ty1), (k2,ty2))
  | prim_compare0 n E (TyExi _, _)                 = GREATER
  | prim_compare0 n (E as (env1, env2))
                 (TyAbs(x1 as (_,k1),ty1),
                  TyAbs(x2 as (_,k2),ty2)) =
        Lib.pair_compare(kind_compare,
                         prim_compare0 (n + 1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                        ((k1,ty1), (k2,ty2))
  | prim_compare0 n E (TyAbs _, _)                 = GREATER

fun prim_compare p = if Portable.pointer_eq p then EQUAL
                     else prim_compare0 0 (empty_env, empty_env) p

fun compare0 n E (u as Tyv _, v as Tyv _)     = map_type_var_compare E (u,v)
  | compare0 n E (Tyv _, _)                   = LESS
  | compare0 n E (TyCon _, Tyv _)             = GREATER
  | compare0 n E (u as TyCon _, v as TyCon _) = type_con_compare (u,v)
  | compare0 n E (TyCon _, _)                 = LESS
  | compare0 n E (TyApp _, Tyv _)             = GREATER
  | compare0 n E (TyApp _, TyCon _)           = GREATER
  | compare0 n E (TyApp p1, TyApp p2)         = Lib.pair_compare(compare0 n E,compare0 n E)(p1,p2)
  | compare0 n E (TyApp _, _)                 = LESS
  | compare0 n E (TyAll _, TyAbs _)           = LESS
  | compare0 n E (TyAll _, TyExi _)           = LESS
  | compare0 n (E as (env1, env2))
                 (TyAll(x1 as (_,k1),ty1),
                  TyAll(x2 as (_,k2),ty2)) =
        Lib.pair_compare(kind_compare,
                         compare0 (n + 1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                        ((k1,ty1), (k2,ty2))
  | compare0 n E (TyAll _, _)                 = GREATER
  | compare0 n E (TyExi _, TyAbs _)           = LESS
  | compare0 n (E as (env1, env2))
                 (TyExi(x1 as (_,k1),ty1),
                  TyExi(x2 as (_,k2),ty2)) =
        Lib.pair_compare(kind_compare,
                         compare0 (n + 1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                        ((k1,ty1), (k2,ty2))
  | compare0 n E (TyExi _, _)                 = GREATER
  | compare0 n (E as (env1, env2))
                 (TyAbs(x1 as (_,k1),ty1),
                  TyAbs(x2 as (_,k2),ty2)) =
        Lib.pair_compare(kind_compare,
                         compare0 (n + 1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                        ((k1,ty1), (k2,ty2))
  | compare0 n E (TyAbs _, _)                 = GREATER

fun compare p = if Portable.pointer_eq p then EQUAL
                else compare0 0 (empty_env, empty_env) p

end (* local *)

(* Alternative definition of "compare", using lists as environments (slower):

(* L and R are lists of type variables *)
fun env_type_var_compare (x::L) (y::R) (u,v) =
       if u=x then if v=y then EQUAL
                          else GREATER
              else if v=y then LESS
                          else env_type_var_compare L R (u,v)
  | env_type_var_compare [] [] (u,v) = type_var_compare (u,v)
  | env_type_var_compare _ _ _ = raise ERR "env_type_var_compare" "environments of different lengths"

fun compare0 L R (u as Tyv _, v as Tyv _)     = env_type_var_compare L R (u,v)
  | compare0 L R (Tyv _, _)                   = LESS
  | compare0 L R (TyCon _, Tyv _)             = GREATER
  | compare0 L R (u as TyCon _, v as TyCon _) = type_con_compare (u,v)
  | compare0 L R (TyCon _, _)                 = LESS
  | compare0 L R (TyApp _, Tyv _)             = GREATER
  | compare0 L R (TyApp _, TyCon _)           = GREATER
  | compare0 L R (TyApp p1, TyApp p2)         = Lib.pair_compare(compare0 L R,compare0 L R)(p1,p2)
  | compare0 L R (TyApp _, _)                 = LESS
  | compare0 L R (TyAll _, TyAbs _)           = LESS
  | compare0 L R (TyAll _, TyExi _)           = LESS
  | compare0 L R (TyAll(x1 as (_,k1),ty1),
            TyAll(x2 as (_,k2),ty2))      =
                                 Lib.pair_compare(kind_compare,compare0 (Tyv x1::L) (Tyv x2::R))
                                                 ((k1,ty1),(k2,ty2))
  | compare0 L R (TyAll _, _)                 = GREATER
  | compare0 L R (TyExi _, TyAbs _)           = LESS
  | compare0 L R (TyExi(x1 as (_,k1),ty1),
            TyExi(x2 as (_,k2),ty2))      =
                                 Lib.pair_compare(kind_compare,compare0 (Tyv x1::L) (Tyv x2::R))
                                                 ((k1,ty1),(k2,ty2))
  | compare0 L R (TyExi _, _)                 = GREATER
  | compare0 L R (TyAbs(x1 as (_,k1),ty1),
            TyAbs(x2 as (_,k2),ty2))      =
                                 Lib.pair_compare(kind_compare,compare0 (Tyv x1::L) (Tyv x2::R))
                                                 ((k1,ty1),(k2,ty2))
  | compare0 L R (TyAbs _, _)                 = GREATER

fun compare p = if Portable.pointer_eq p then EQUAL
                else compare0 [] [] p
*)


val empty_tyset = HOLset.empty compare

local val EQ = Portable.pointer_eq
in
fun aconv_ty t1 t2 = compare(t1, t2) = EQUAL
val type_eq = aconv_ty
(*
fun asubtype t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (u as Tyv _, v as Tyv _ ) => type_var_subtype(u,v)
   | (u as TyCon _,v as TyCon _) => type_con_compare(u,v) = EQUAL
   | (TyApp(p,t1),TyApp(q,t2)) => asubtype p q andalso asubtype t1 t2
   | (TyAll((_,k1,r1),t1),
      TyAll((_,k2,r2),t2)) => k1 = k2 andalso r1 <= r2 andalso asubtype t1 t2
   | (TyExi((_,k1,r1),t1),
      TyExi((_,k2,r2),t2)) => k1 = k2 andalso r1 <= r2 andalso asubtype t1 t2
   | (TyAbs((_,k1,r1),t1),
      TyAbs((_,k2,r2),t2)) => k1 = k2 andalso r1 <= r2 andalso asubtype t1 t2
   | (M,N)       => (M=N)
*)
end

fun type_vars_set acc bvs [] = acc
  | type_vars_set acc bvs ((t as Tyv s) :: rest) =
      if HOLset.member(bvs,t) then type_vars_set acc bvs rest
      else type_vars_set (HOLset.add(acc, t)) bvs rest
  | type_vars_set acc bvs (TyCon _ :: rest) =
      type_vars_set acc bvs rest
  | type_vars_set acc bvs (TyApp(opr,arg) :: rest) =
      type_vars_set acc bvs (opr :: arg :: rest)
  | type_vars_set acc bvs (TyAbs(bv,body) :: rest) =
      type_vars_set (type_vars_set acc (HOLset.add(bvs, Tyv bv)) [body]) bvs rest
  | type_vars_set acc bvs (TyAll(bv,body) :: rest) =
      type_vars_set (type_vars_set acc (HOLset.add(bvs, Tyv bv)) [body]) bvs rest
  | type_vars_set acc bvs (TyExi(bv,body) :: rest) =
      type_vars_set (type_vars_set acc (HOLset.add(bvs, Tyv bv)) [body]) bvs rest

fun type_vars ty = HOLset.listItems (type_vars_set empty_tyset empty_tyset [ty])

val type_varsl = HOLset.listItems o type_vars_set empty_tyset empty_tyset

fun exists_tyvar P = let
  fun occ E (w as Tyv _) = not (mem w E) andalso P w
    | occ E (TyCon _) = false
    | occ E (TyApp(opr,arg)) = occ E opr orelse occ E arg
    | occ E (TyAbs(bv,body)) = occ (Tyv bv::E) body
    | occ E (TyAll(bv,body)) = occ (Tyv bv::E) body
    | occ E (TyExi(bv,body)) = occ (Tyv bv::E) body
in
  occ []
end

(* ----------------------------------------------------------------------
    type_var_in ty TY : does ty occur free in TY?
   ---------------------------------------------------------------------- *)

fun type_var_in ty =
   let fun f1 (TyApp(opr,ty)) = (f2 opr) orelse (f2 ty)
         | f1 (TyAll(bv,Body)) = not (Tyv bv = ty) andalso f2 Body
         | f1 (TyExi(bv,Body)) = not (Tyv bv = ty) andalso f2 Body
         | f1 (TyAbs(bv,Body)) = not (Tyv bv = ty) andalso f2 Body
         | f1 _ = false
       and f2 t = type_eq t ty orelse f1 t
   in if is_var_type ty then f2
                        else raise ERR "type_var_in" "not a type variable"
   end;

(*
fun type_var_in v =
  if is_var_type v then exists_tyvar (equal v)
                   else raise ERR "type_var_in" "not a type variable"
*)

fun polymorphic (TyCon (_,Kd))    = Kind.polymorphic Kd
  | polymorphic (Tyv _)           = true
  | polymorphic (TyApp (Opr,Arg)) = polymorphic Opr orelse polymorphic Arg
  | polymorphic (TyAll (_,Body))  = true (* alt: polymorphic Body *)
  | polymorphic (TyExi (_,Body))  = true (* alt: polymorphic Body *)
  | polymorphic (TyAbs (_,Body))  = true (* alt: polymorphic Body *)

fun universal (TyAll _)         = true
  | universal (TyApp (Opr,Arg)) = universal Opr orelse universal Arg
  | universal (TyAbs (_,Body))  = universal Body
  | universal (TyExi (_,Body))  = universal Body
  | universal _                 = false

fun existential (TyExi _)         = true
  | existential (TyApp (Opr,Arg)) = existential Opr orelse existential Arg
  | existential (TyAbs (_,Body))  = existential Body
  | existential (TyAll (_,Body))  = existential Body
  | existential _                 = false

fun abstraction (TyAbs _)         = true
  | abstraction (TyApp (Opr,Arg)) = abstraction Opr orelse abstraction Arg
  | abstraction (TyAll (_,Body))  = abstraction Body
  | abstraction (TyExi (_,Body))  = abstraction Body
  | abstraction _                 = false

fun is_omega (TyAbs _)         = true
  | is_omega (TyAll _)         = true
  | is_omega (TyExi _)         = true
  | is_omega (TyApp (Opr,Arg)) = is_omega Opr orelse is_omega Arg
  | is_omega (Tyv  (_,k))      = not (k = Kind.typ 0)
  | is_omega (TyCon(_,k))      = not (Kind.is_arity k andalso Kind.rank_of k = 0)

(*---------------------------------------------------------------------------
       Function types
 ---------------------------------------------------------------------------*)

(* mk_fun_type is for internal use only *)
(* Must instantiate the function type constant's rank
   to match the rank of its arguments. *)
fun mk_fun_type(X,Y) =
  let (* val rkS = raw_match_rank rho (rank_of_type Y) (match_rank rho (rank_of_type X))
         val kd = mk_type_kind (mk_rank rkS) *)
      val kd = typ (max(rank_of_type X, rank_of_type Y))
      val fun_tyc' = (funref, kd ==> kd ==> kd)
  in TyApp (TyApp (TyCon fun_tyc', X), Y)
  end;

fun (X --> Y) = if not (is_type_kind (kind_of X))
                  then raise ERR "-->" ("domain of --> needs kind ty, but was given kind "
                                        ^ kind_to_string (kind_of X))
                else if not (is_type_kind (kind_of Y))
                  then raise ERR "-->" ("range of --> needs kind ty, but was given kind "
                                        ^ kind_to_string (kind_of Y))
                else mk_fun_type(X,Y);

local
fun dom_of (TyApp(c as TyCon _, Y)) =
      if same_tyconst c fun_tyc then Y
      else raise ERR "dom_rng" "not a function type"
  | dom_of _ = raise ERR "dom_rng" "not a function type"
in
fun dom_rng (TyApp(funX, Y)) = (dom_of funX, Y)
  | dom_rng _ = raise ERR "dom_rng" "not a function type"
end;

val alpha  = Tyv ("'a", typ 0)
val beta   = Tyv ("'b", typ 0)
val gamma  = Tyv ("'c", typ 0)
val delta  = Tyv ("'d", typ 0)
val etyvar = Tyv ("'e", typ 0)
val ftyvar = Tyv ("'f", typ 0)

val varcomplain = ref true
val _ = register_btrace ("Vartype Format Complaint", varcomplain)

fun mk_var_type (s, kind) =
                (if kind = typ rho then
                   case s
                    of "'a" => alpha
                     | "'b" => beta
                     | "'c" => gamma
                     | "'d" => delta
                     | "'e" => etyvar
                     | "'f" => ftyvar
                     | _ => raise ERR "mk_var_type" "not a precreated type var"
                 else raise ERR "mk_var_type" "not a precreated type var")
                handle HOL_ERR _ =>
                if Lexis.allowed_user_type_var s then Tyv (s, kind)
                else (if !varcomplain then
                        WARN "mk_var_type" ("non-standard syntax: " ^ s)
                      else (); Tyv (s, kind))

fun mk_vartype s = mk_var_type (s, typ rho)

fun inST s = let
  fun foldthis({Thy,Name},_,acc) = (acc orelse (Name = s))
in
  KernelSig.foldl foldthis false operator_table
end

fun mk_primed_var_type (Name, Kind) =
  let val next = Lexis.tyvar_vary
      fun spin s = if inST s then spin (next s) else s
  in mk_var_type(spin Name, Kind)
  end;

fun mk_primed_vartype s = mk_primed_var_type (s, typ rho);


(*---------------------------------------------------------------------------*
 * Given a type variable and a list of type variables, if the type variable  *
 * does not exist on the list, then return the type variable. Otherwise,     *
 * rename the type variable and try again. Note well that the variant uses   *
 * only the name of the variable as a basis for testing equality. Experience *
 * has shown that basing the comparison on all of the name, the arity, the   *
 * rank, and the type arguments of the variable resulted in needlessly       *
 * confusing formulas occasionally being displayed in interactive sessions.  *
 *---------------------------------------------------------------------------*)

fun gen_variant P caller =
  let fun var_name (Tyv(Name,_)) = Name
        | var_name _ = raise ERR caller "not a variable"
      fun vary vlist (Tyv(Name,Kind)) =
          let val L = map var_name vlist
              val next = Lexis.gen_variant Lexis.tyvar_vary L
              fun loop name =
                 let val s = next name
                 in if P s then loop s else s
                 end
          in trace ("Vartype Format Complaint",0) mk_var_type(loop Name, Kind)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a type variable"
  in vary
  end;

val variant_type       = gen_variant inST "variant_type"
val prim_variant_type  = gen_variant (K false) "prim_variant_type";

fun variant_tyvar tys tyv =
       let val ty0 = Tyv tyv
           val ty = variant_type tys ty0
        in dest_var_type ty
       end;


(*---------------------------------------------------------------------------*
 *    Replace arbitrary subtypes in a type. Non-renaming.                    *
 *---------------------------------------------------------------------------*)

exception NeedToRename of tyvar

(* two different substs; monomorphism restriction bites again; later code
   gives these different types *)
structure Map = Binarymap
val emptyvsubst = Map.mkDict compare
val emptysubst = Map.mkDict compare

(* it's hard to calculate free names simply by traversing a type because
   of the situation where \:a:kd1. body has a:kd1 and a:kd2 as free type variables
   in body.  So, though it may be slightly less efficient, my solution here
   is to just calculate the free type variables and then calculate the image of
   this set under name extraction *)
val empty_stringset = HOLset.empty String.compare
val free_names = let
  fun fold_name (tyv, acc) = HOLset.add(acc, #1 (dest_var_type tyv))
in
  (fn ty => HOLset.foldl fold_name empty_stringset (type_vars_set empty_tyset empty_tyset [ty]))
end

fun set_name_variant nmset n = let
  val next = Lexis.tyvar_vary
  fun loop n = if HOLset.member(nmset, n) then loop (next n)
               else n
in
  loop n
end


local
  open Map Susp

  type typeset = hol_type HOLset.set
  val fvsingle = HOLset.singleton compare

  datatype fvinfo = FVI of { current : typeset,
                             left   : fvinfo option,
                             right  : fvinfo option,
                             inabs  : fvinfo option }
  fun leaf s = FVI {current = s, left = NONE, right = NONE, inabs = NONE}
  fun left (FVI r) = valOf (#left r)
  fun right (FVI r) = valOf (#right r)
  fun inabs (FVI r) = valOf (#inabs r)
  fun current (FVI r) = #current r
  fun calculate_fvinfo ty =
      case ty of
        v as Tyv _ => leaf (fvsingle v)
      | TyCon _ => leaf empty_tyset
      | TyApp(opr, arg) => let
          val opr_vs = calculate_fvinfo opr
          val arg_vs = calculate_fvinfo arg
        in
          FVI {current = HOLset.union(current opr_vs, current arg_vs),
               left = SOME opr_vs, right = SOME arg_vs, inabs = NONE}
        end
      | TyAbs(v, body) => let
          val bodyvs = calculate_fvinfo body
        in
          FVI {current = safe_delete(current bodyvs, Tyv v),
               left = NONE, right = NONE, inabs = SOME bodyvs}
        end
      | TyAll(v, body) => let
          val bodyvs = calculate_fvinfo body
        in
          FVI {current = safe_delete(current bodyvs, Tyv v),
               left = NONE, right = NONE, inabs = SOME bodyvs}
        end
      | TyExi(v, body) => let
          val bodyvs = calculate_fvinfo body
        in
          FVI {current = safe_delete(current bodyvs, Tyv v),
               left = NONE, right = NONE, inabs = SOME bodyvs}
        end

  fun filtertheta theta fvset = let
    (* Removes entries in theta for things not in fvset.  theta likely to
       be much smaller than fvset, so fold over that rather than the
       other *)
    fun foldthis (k,v,acc) = if HOLset.member(fvset, k) then insert(acc, k, v)
                             else acc
  in
    foldl foldthis emptyvsubst theta
  end

  fun maptyset f = HOLset.foldr (fn (v,acc) => HOLset.add(acc, f v)) (HOLset.empty compare)
  fun inst_tyv f (v as Tyv(s,kd)) = (Tyv(s,f kd) handle Unchanged => v)
    | inst_tyv _ _ = raise ERR "filtertheta_rkt" "impossible" (* impossible case *)
  fun inst_tyset f = maptyset (inst_tyv f)

  fun filtertheta_rkt rkS kdS tyS fvset = let
    (* Removes entries in tyS for things not in fvset.  tyS likely to
       be much smaller than fvset, so fold over that rather than the
       other *)
    val inst_kd = Kind.vsubst_rk_kd rkS kdS
    val fvset' = inst_tyset inst_kd fvset
    fun foldthis (k,v,acc) = if HOLset.member(fvset', k) then insert(acc, k, v)
                             else acc
  in
    foldl foldthis emptyvsubst tyS
  end



  fun augvsubst theta fvi ty =
      case ty of
        Tyv _ => (case peek(theta, ty) of NONE => raise Unchanged
                                        | SOME (_, t) => t)
      | TyCon _ => raise Unchanged
      | TyApp(f, a) => let
          val xfvi = right fvi
        in
          let
            val ffvi = left fvi
            val f' = augvsubst theta ffvi f
          in
            let val a' = augvsubst theta xfvi a
            in
              TyApp(f', a')
            end handle Unchanged => TyApp(f', a)
          end handle Unchanged => let val a' = augvsubst theta xfvi a
                                  in
                                    TyApp(f, a')
                                  end
        end
      | TyAbs(v, body) => let
          val tyv = Tyv v
          val theta = #1 (remove(theta, tyv)) handle NotFound => theta
          val (vname, vkd) = v
          val currentfvs = current fvi
          (* first calculate the new names we are about to introduce into
             the type *)
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset theta
          val new_fvi = inabs fvi
        in
          if HOLset.member(newnames, vname) then let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames (current fvi)
              val new_vname = set_name_variant allfreenames vname
              val new_v = (new_vname, vkd)
              val new_theta =
                  if HOLset.member(current new_fvi, tyv) then let
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(theta, tyv, (Susp.delay (fn () => singleton),
                                          mk_var_type new_v))
                    end
                  else theta
            in
              TyAbs(new_v, augvsubst new_theta new_fvi body)
            end
          else
            TyAbs(v, augvsubst theta new_fvi body)
        end
      | TyAll(v, body) => let
          val tyv = Tyv v
          val theta = #1 (remove(theta, tyv)) handle NotFound => theta
          val (vname, vkd) = v
          val currentfvs = current fvi
          (* first calculate the new names we are about to introduce into
             the type *)
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset theta
          val new_fvi = inabs fvi
        in
          if HOLset.member(newnames, vname) then let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames (current fvi)
              val new_vname = set_name_variant allfreenames vname
              val new_v = (new_vname, vkd)
              val new_theta =
                  if HOLset.member(current new_fvi, tyv) then let
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(theta, tyv, (Susp.delay (fn () => singleton),
                                          mk_var_type new_v))
                    end
                  else theta
            in
              TyAll(new_v, augvsubst new_theta new_fvi body)
            end
          else
            TyAll(v, augvsubst theta new_fvi body)
        end
      | TyExi(v, body) => let
          val tyv = Tyv v
          val theta = #1 (remove(theta, tyv)) handle NotFound => theta
          val (vname, vkd) = v
          val currentfvs = current fvi
          (* first calculate the new names we are about to introduce into
             the type *)
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset theta
          val new_fvi = inabs fvi
        in
          if HOLset.member(newnames, vname) then let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames (current fvi)
              val new_vname = set_name_variant allfreenames vname
              val new_v = (new_vname, vkd)
              val new_theta =
                  if HOLset.member(current new_fvi, tyv) then let
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(theta, tyv, (Susp.delay (fn () => singleton),
                                          mk_var_type new_v))
                    end
                  else theta
            in
              TyExi(new_v, augvsubst new_theta new_fvi body)
            end
          else
            TyExi(v, augvsubst theta new_fvi body)
        end

  fun augment_vsubst theta ty = let
          val fvi = calculate_fvinfo ty
          val theta' = filtertheta theta (current fvi)
        in
          if numItems theta' = 0 then raise Unchanged
          else augvsubst theta' fvi ty
        end

  fun vsubst theta ty =
      case ty of
        Tyv _ => (case peek(theta, ty) of NONE => raise Unchanged
                                        | SOME (_, t) => t)
      | TyCon _ => raise Unchanged
      | TyApp p  => qcomb TyApp (vsubst theta) p
      | TyAbs _ => augment_vsubst theta ty
      | TyAll _ => augment_vsubst theta ty
      | TyExi _ => augment_vsubst theta ty


  fun vsub_insert(fm, k, v) =
      insert(fm, k, (delay (fn () => free_names v), v))



  fun augvsubst_rkt rkS kdS tyS ctxt fvi ty =
    let
      val inst_kd = Kind.vsubst_rk_kd rkS kdS
      fun augvsubst tyS ctxt fvi ty =
      case ty of
        Tyv(v as (s,kd)) =>
          let val (changed, nv) = (true, (s,inst_kd kd))
                                  handle Unchanged => (false, v)
              val ty' = Tyv nv
          in
            case peek (ctxt, nv) of
              SOME old => if old = kd then ()
                          else raise NeedToRename nv
            | NONE => ();
            case peek (tyS, ty') of NONE => if changed then ty'
                                            else raise Unchanged
                                  | SOME (_, t) => t
          end
      | TyCon(c,kd) => TyCon(c,inst_kd kd)
      | TyApp(f, a) => let
          val xfvi = right fvi
        in
          let
            val ffvi = left fvi
            val f' = augvsubst tyS ctxt ffvi f
          in
            let val a' = augvsubst tyS ctxt xfvi a
            in
              TyApp(f', a')
            end handle Unchanged => TyApp(f', a)
          end handle Unchanged => let val a' = augvsubst tyS ctxt xfvi a
                                  in
                                    TyApp(f, a')
                                  end
        end
      | TyAbs(v as (vname,vkd), body) => let
          val (changed,v') = (true, (vname,inst_kd vkd))
                             handle Unchanged => (false, v)
          val tyv = Tyv v'
          val tyS = #1 (remove(tyS, tyv)) handle NotFound => tyS
          val (_, vkd') = v'
          val currentfvs = inst_tyset inst_kd (current fvi)
          (* first calculate the new names we are about to introduce into
             the type *)
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset tyS
          val new_fvi = inabs fvi
          val new_ctxt = insert(ctxt, v', vkd)
        in
          let val (new_v,body') =
            if HOLset.member(newnames, vname) then let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames currentfvs (*(inst_tyset inst_kd (current fvi))*)
              val new_vname = set_name_variant allfreenames vname
              val new_v = (new_vname, vkd')
              val new_tyS =
                  if HOLset.member(inst_tyset inst_kd (current new_fvi), tyv) then let
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(tyS, tyv, (Susp.delay (fn () => singleton),
                                          mk_var_type new_v))
                    end
                  else tyS
              in
                (new_v, SOME(augvsubst new_tyS new_ctxt new_fvi body)
                        handle Unchanged => NONE)
              end
            else
              (v', SOME(augvsubst tyS new_ctxt new_fvi body)
                   handle Unchanged => NONE)
          in
            case (body', changed) of
              (SOME t, _) => TyAbs(new_v, t)
            | (NONE, true) => TyAbs(new_v, body)
            | (NONE, false) => raise Unchanged
          end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names ty
                         val new_name = set_name_variant free_names vname
                         val newv = (new_name, vkd)
                         val swap_theta = vsub_insert(emptyvsubst, Tyv v, Tyv newv)
(*
                       in
                         augvsubst tyS ctxt fvi (TyAbs(newv, vsubst swap_theta body))
                       end
*)
                         val sw_ctxt = mkDict tyvar_compare : (string * kind, kind) dict
                         val sw_fvi = inabs fvi
                         val body' = augvsubst_rkt 0 [] swap_theta sw_ctxt sw_fvi body
                                     handle Unchanged => body
                         val ty' = TyAbs(newv, body')
                         val fvi' = calculate_fvinfo ty'
                       in
                         augvsubst tyS ctxt fvi' ty'
                       end
                     else raise e
        end
      | TyAll(v as (vname,vkd), body) => let
          val (changed,v') = (true, (vname,inst_kd vkd))
                             handle Unchanged => (false, v)
          val tyv = Tyv v'
          val tyS = #1 (remove(tyS, tyv)) handle NotFound => tyS
          val (_, vkd') = v'
          val currentfvs = inst_tyset inst_kd (current fvi)
          (* first calculate the new names we are about to introduce into
             the type *)
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset tyS
          val new_fvi = inabs fvi
          val new_ctxt = insert(ctxt, v', vkd)
        in
          let val (new_v,body') =
            if HOLset.member(newnames, vname) then let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames currentfvs (*(inst_tyset inst_kd (current fvi))*)
              val new_vname = set_name_variant allfreenames vname
              val new_v = (new_vname, vkd')
              val new_tyS =
                  if HOLset.member(inst_tyset inst_kd (current new_fvi), tyv) then let
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(tyS, tyv, (Susp.delay (fn () => singleton),
                                          mk_var_type new_v))
                    end
                  else tyS
              in
                (new_v, SOME(augvsubst new_tyS new_ctxt new_fvi body)
                        handle Unchanged => NONE)
              end
            else
              (v', SOME(augvsubst tyS new_ctxt new_fvi body)
                   handle Unchanged => NONE)
          in
            case (body', changed) of
              (SOME t, _) => TyAll(new_v, t)
            | (NONE, true) => TyAll(new_v, body)
            | (NONE, false) => raise Unchanged
          end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names ty
                         val new_name = set_name_variant free_names vname
                         val newv = (new_name, vkd)
                         val swap_theta = vsub_insert(emptyvsubst, Tyv v, Tyv newv)
(*
                       in
                         augvsubst tyS ctxt fvi (TyAll(newv, vsubst swap_theta body))
                       end
*)
                         val sw_ctxt = mkDict tyvar_compare : (string * kind, kind) dict
                         val sw_fvi = inabs fvi
                         val body' = augvsubst_rkt 0 [] swap_theta sw_ctxt sw_fvi body
                                     handle Unchanged => body
                         val ty' = TyAll(newv, body')
                         val fvi' = calculate_fvinfo ty'
                       in
                         augvsubst tyS ctxt fvi' ty'
                       end
                     else raise e
        end
      | TyExi(v as (vname,vkd), body) => let
          val (changed,v') = (true, (vname,inst_kd vkd))
                             handle Unchanged => (false, v)
          val tyv = Tyv v'
          val tyS = #1 (remove(tyS, tyv)) handle NotFound => tyS
          val (_, vkd') = v'
          val currentfvs = inst_tyset inst_kd (current fvi)
          (* first calculate the new names we are about to introduce into
             the type *)
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset tyS
          val new_fvi = inabs fvi
          val new_ctxt = insert(ctxt, v', vkd)
        in
          let val (new_v,body') =
            if HOLset.member(newnames, vname) then let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames currentfvs (*(inst_tyset inst_kd (current fvi))*)
              val new_vname = set_name_variant allfreenames vname
              val new_v = (new_vname, vkd')
              val new_tyS =
                  if HOLset.member(inst_tyset inst_kd (current new_fvi), tyv) then let
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(tyS, tyv, (Susp.delay (fn () => singleton),
                                          mk_var_type new_v))
                    end
                  else tyS
              in
                (new_v, SOME(augvsubst new_tyS new_ctxt new_fvi body)
                        handle Unchanged => NONE)
              end
            else
              (v', SOME(augvsubst tyS new_ctxt new_fvi body)
                   handle Unchanged => NONE)
          in
            case (body', changed) of
              (SOME t, _) => TyExi(new_v, t)
            | (NONE, true) => TyExi(new_v, body)
            | (NONE, false) => raise Unchanged
          end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names ty
                         val new_name = set_name_variant free_names vname
                         val newv = (new_name, vkd)
                         val swap_theta = vsub_insert(emptyvsubst, Tyv v, Tyv newv)
(*
                       in
                         augvsubst tyS ctxt fvi (TyExi(newv, vsubst swap_theta body))
                       end
*)
                         val sw_ctxt = mkDict tyvar_compare : (string * kind, kind) dict
                         val sw_fvi = inabs fvi
                         val body' = augvsubst_rkt 0 [] swap_theta sw_ctxt sw_fvi body
                                     handle Unchanged => body
                         val ty' = TyExi(newv, body')
                         val fvi' = calculate_fvinfo ty'
                       in
                         augvsubst tyS ctxt fvi' ty'
                       end
                     else raise e
        end
    in
      augvsubst tyS ctxt fvi ty
    end

  fun augment_vsubst_rkt rkS kdS tyS ty = let
          val fvi = calculate_fvinfo ty
          val tyS' = filtertheta_rkt rkS kdS tyS (current fvi)
          val ctxt = mkDict tyvar_compare : (string * kind, kind) dict
        in
          augvsubst_rkt rkS kdS tyS' ctxt fvi ty
        end

  fun vsubst_rkt 0   []  tyS = vsubst tyS
    | vsubst_rkt rkS kdS tyS =
    let
      val inst = Kind.vsubst_rk_kd rkS kdS
      fun vsub ty =
        case ty of
          Tyv(s,kd) => (let val ty' = Tyv(s,inst kd)
                        in case peek(tyS, ty') of NONE => ty'
                                                | SOME (_, t) => t
                        end handle Unchanged =>
                        case peek(tyS, ty) of NONE => raise Unchanged
                                            | SOME (_, t) => t)
        | TyCon(c,kd) => TyCon(c,inst kd)
        | TyApp p  => qcomb TyApp vsub p
        | TyAbs _ => augment_vsubst_rkt rkS kdS tyS ty
        | TyAll _ => augment_vsubst_rkt rkS kdS tyS ty
        | TyExi _ => augment_vsubst_rkt rkS kdS tyS ty
    in vsub
    end

  fun ssubst theta t =
      (* only used to substitute in fresh variables (genvars), so no
         capture check.  *)
      if numItems theta = 0 then raise Unchanged
      else
        case peek(theta, t) of
          SOME v => v
        | NONE => let
          in
            case t of
              TyApp p => qcomb TyApp (ssubst theta) p
            | TyAbs(v, body) => let
                fun modify_theta (k,value,newtheta) =
                    if type_var_in (Tyv v) k then newtheta
                    else insert(newtheta, k, value)
                val newtheta = foldl modify_theta emptysubst theta
              in
                TyAbs(v, ssubst newtheta body)
              end
            | TyAll(v, body) => let
                fun modify_theta (k,value,newtheta) =
                    if type_var_in (Tyv v) k then newtheta
                    else insert(newtheta, k, value)
                val newtheta = foldl modify_theta emptysubst theta
              in
                TyAll(v, ssubst newtheta body)
              end
            | TyExi(v, body) => let
                fun modify_theta (k,value,newtheta) =
                    if type_var_in (Tyv v) k then newtheta
                    else insert(newtheta, k, value)
                val newtheta = foldl modify_theta emptysubst theta
              in
                TyExi(v, ssubst newtheta body)
              end
            | _ => raise Unchanged
          end

in

(* may throw Unchanged *)
fun prim_type_subst theta =
    if null theta then I
    else if List.all (is_var_type o #redex) theta then let
        fun foldthis  ({redex,residue}, acc) = let
          val _ = kind_of redex :>=: kind_of residue
                  orelse raise ERR "vsubst" "Bad substitution list"
        in
          if redex = residue then acc
          else vsub_insert(acc, redex, residue)
        end
        val atheta = List.foldl foldthis emptyvsubst theta
      in
        if numItems atheta = 0 then I
        else vsubst atheta
      end
    else let
        fun foldthis ({redex,residue}, (theta1, theta2)) = let
          val _ = kind_of redex :>=: kind_of residue
                  orelse raise ERR "vsubst" "Bad substitution list"
          val gv = gen_var_type (kind_of redex)
        in
          (insert(theta1, redex, gv), vsub_insert (theta2, gv, residue))
        end
        val (theta1, theta2) =
            List.foldl foldthis (emptysubst, emptyvsubst) theta
      in
        vsubst theta2 o ssubst theta1
      end

(* prim_type_var_subst properly ignores type redexes which are not variables,
   but does not throw an error from them if any are included. *)
(* may throw Unchanged *)
fun prim_type_var_subst theta =
  prim_type_subst (filter (is_var_type o #redex) theta)

(* may throw Unchanged *)
fun prim_rk_kd_ty_subst rkS kdS theta =
    if null kdS andalso rkS=0 then prim_type_subst theta
    else if List.all (is_var_type o #redex) theta then let
        fun foldthis1  (r as {redex,residue}, acc) = let
          val _ = rank_of redex >= rank_of residue
                  orelse raise ERR "vsubst_rk_kd_ty" "Bad kind substitution list"
        in
          if redex = residue then acc
          else r::acc
        end
        val akdS = List.foldr foldthis1 [] kdS
        fun foldthis  ({redex,residue}, acc) = let
          val _ = kind_of redex :>=: kind_of residue
                  orelse raise ERR "vsubst_rk_kd_ty" "Bad substitution list"
        in
          if redex = residue then acc
          else vsub_insert(acc, redex, residue)
        end
        val atheta = List.foldl foldthis emptyvsubst theta
      in
        vsubst_rkt rkS akdS atheta
      end
    else let
        fun foldthis1  (r as {redex,residue}, acc) = let
          val _ = rank_of redex >= rank_of residue
                  orelse raise ERR "vsubst_rk_kd_ty" "Bad kind substitution list"
        in
          if redex = residue then acc
          else r::acc
        end
        val akdS = List.foldr foldthis1 [] kdS
        fun foldthis ({redex,residue}, (theta1, theta2)) = let
          val _ = kind_of redex :>=: kind_of residue
                  orelse raise ERR "vsubst_rk_kd_ty" "Bad substitution list"
          val gv = gen_var_type (kind_of redex)
        in
          (insert(theta1, redex, gv), vsub_insert (theta2, gv, residue))
        end
        val (theta1, theta2) =
            List.foldl foldthis (emptysubst, emptyvsubst) theta
      in
        vsubst_rkt rkS akdS theta2 o ssubst theta1
      end

(* prim_rk_kd_ty_var_subst properly ignores type redexes which are not variables,
   but does not throw an error from them if any are included. *)
(* may throw Unchanged *)
fun prim_rk_kd_ty_var_subst rkS kdS theta =
  prim_rk_kd_ty_subst rkS kdS (filter (is_var_type o #redex) theta)

fun inst_rank_kind1 rkS kdS ctxt = (* requires context; may throw Unchanged, NeedToRename *)
  let
    fun prim_rk_kd_subst ty =
      let
        val fvi = calculate_fvinfo ty
      in
        augvsubst_rkt rkS kdS emptyvsubst ctxt fvi ty
      end
  in
    (* vacuum o *) prim_rk_kd_subst
  end

fun qapp s f x = f x handle Unchanged => x
                          | HOL_ERR {message, ...} => raise ERR s message

fun inst_rank rkS = qapp "inst_rank" ((* vacuum o *) prim_rk_kd_ty_subst rkS [] [])
                          handle HOL_ERR {message, ...} => raise ERR "inst_rank" message
fun pure_inst_kind kdS = qapp "pure_inst_kind" ((* vacuum o *) prim_rk_kd_ty_subst 0 kdS [])
                          handle HOL_ERR {message, ...} => raise ERR "pure_inst_kind" message
fun inst_rank_kind rkS kdS = qapp "inst_rank_kind" ((* vacuum o *) prim_rk_kd_ty_subst rkS kdS [])
                          handle HOL_ERR {message, ...} => raise ERR "inst_rank_kind" message

(* pure_type_subst properly ignores type redexes which are not variables,
   but does not throw an error from them if any are included. *)
fun pure_type_subst theta = qapp "pure_type_subst" ((* vacuum o *) prim_type_var_subst theta)
                          handle HOL_ERR {message, ...} => raise ERR "pure_type_subst" message

(* inst_rk_kd_ty properly ignores type redexes which are not variables,
   but does not throw an error if any are included. *)
fun inst_rk_kd_ty rkS kdS theta = qapp "inst_rk_kd_ty" ((* vacuum o *) prim_rk_kd_ty_var_subst rkS kdS theta)
                          handle HOL_ERR {message, ...} => raise ERR "inst_rk_kd_ty" message

(* full_type_subst substitutes type expressions for type expressions.
   Unlike pure_type_subst, the redexes do not have to be type variables.
   This function cannot be used inside terms, lest type-checking be violated. *)
fun full_type_subst theta = qapp "full_type_subst" ((* vacuum o *) prim_type_subst theta)
                          handle HOL_ERR {message, ...} => raise ERR "full_type_subst" message

fun qdiff s f x = DIFF (f x) handle Unchanged => SAME
                                  | HOL_ERR {message, ...} => raise ERR s message

fun pure_ty_sub theta = qdiff "pure_ty_sub" ((* vacuum o *) prim_type_subst theta)
                          handle HOL_ERR {message, ...} => raise ERR "pure_ty_sub" message
fun rk_kd_ty_sub rkS kdS theta = qdiff "rk_kd_ty_sub" ((* vacuum o *) prim_rk_kd_ty_subst rkS kdS theta)
                          handle HOL_ERR {message, ...} => raise ERR "rk_kd_ty_sub" message

(* expose vsubst for use in Term.subst *)
val vsubst = vsubst
(* expose vsubst_rkt for use in Term.subst *)
val vsubst_rkt = vsubst_rkt
(* expose ssubst for use in Term.inst  *)
val ssubst = ssubst

end (* local *)


(* old version:

(*---------------------------------------------------------------------------*
 * Increasing the rank of a type.                                            *
 *---------------------------------------------------------------------------*)
            

fun inst_rank [] = Lib.I
  | inst_rank [0] = Lib.I
  | inst_rank (_ :: _ :: _) = raise ERR "inst_rank" "invalid rank substitution"
  | inst_rank rkS =
  let val inst_kd = Kind.inst_rank rkS
      fun inc_rk (Tyv  (s,kd))        = Tyv  (s,inst_kd kd)
        | inc_rk (TyCon(s,kd))        = TyCon(s,inst_kd kd) (* current design DOES inst this kd's rank *)
        | inc_rk (TyApp(opr, ty))     = TyApp(inc_rk opr,  inc_rk ty)
        | inc_rk (TyAll((s,kd),Body)) = TyAll((s,inst_kd kd), inc_rk Body)
        | inc_rk (TyExi((s,kd),Body)) = TyExi((s,inst_kd kd), inc_rk Body)
        | inc_rk (TyAbs((s,kd),Body)) = TyAbs((s,inst_kd kd), inc_rk Body)
  in (* vacuum o *) inc_rk
  end

(*---------------------------------------------------------------------------*
 *    Matching ranks, determining the necessary delta to make proper.        *
 *---------------------------------------------------------------------------*)

(*
fun subst_rank [] = []
  | subst_rank ({redex,residue} :: s) =
      raw_match_rank false (rank_of_type redex) (rank_of_type residue) (subst_rank s)

fun inst_rank_subst r [] = []
  | inst_rank_subst r ({redex,residue} :: s) =
      {redex=inst_rank r redex, residue=residue} :: inst_rank_subst r s
*)

(*---------------------------------------------------------------------------*
 *     Instantiate the rank variable and kind variables in a type            *
 *---------------------------------------------------------------------------*)

local
  structure Map = struct open Binarymap end
  fun inst1 rkS theta ctxt t =
      case t of
        (c as TyCon(r, kd)) => (case kd_sub rkS theta kd of
                                      SAME => raise Unchanged
                                    | DIFF kd => TyCon(r, kd))
      | Tyv (v as (name, kd)) => let
          val (changed, nv) = case kd_sub rkS theta kd of
                                      SAME => (false, v)
                                    | DIFF kd' => (true, (name, kd'))
        in
          case Map.peek (ctxt, nv) of
            SOME old => if old = kd then ()
                        else raise NeedToRename nv
          | NONE => ();
          if changed then Tyv nv
          else raise Unchanged
        end
      | TyApp p => qcomb TyApp (inst1 rkS theta ctxt) p
      | TyAbs (v as (name, kd), body) => let
            val (changed, v') = case kd_sub rkS theta kd of
                                  SAME => (false, v)
                                | DIFF kd' => (true, (name, kd'))
        in let
             val body' = SOME (inst1 rkS theta (Map.insert(ctxt, v', kd)) body)
                 handle Unchanged => NONE
           in
             case (body', changed) of
               (SOME t, _) => TyAbs(v', t)
             | (NONE, true) => TyAbs(v', body)
             | (NONE, false) => raise Unchanged
           end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names t
                         val new_name = set_name_variant free_names name
                         val newv = (new_name, kd)
                       in
                         inst1 rkS theta ctxt (TyAbs(newv, pure_type_subst [Tyv v |-> Tyv newv] body))
                       end
                     else raise e
        end
      | TyAll (v as (name, kd), body) => let
            val (changed, v') = case kd_sub rkS theta kd of
                                  SAME => (false, v)
                                | DIFF kd' => (true, (name, kd'))
        in let
             val body' = SOME (inst1 rkS theta (Map.insert(ctxt, v', kd)) body)
                 handle Unchanged => NONE
           in
             case (body', changed) of
               (SOME t, _) => TyAll(v', t)
             | (NONE, true) => TyAll(v', body)
             | (NONE, false) => raise Unchanged
           end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names t
                         val new_name = set_name_variant free_names name
                         val newv = (new_name, kd)
                       in
                         inst1 rkS theta ctxt (TyAll(newv, pure_type_subst [Tyv v |-> Tyv newv] body))
                       end
                     else raise e
        end
      | TyExi (v as (name, kd), body) => let
            val (changed, v') = case kd_sub rkS theta kd of
                                  SAME => (false, v)
                                | DIFF kd' => (true, (name, kd'))
        in let
             val body' = SOME (inst1 rkS theta (Map.insert(ctxt, v', kd)) body)
                 handle Unchanged => NONE
           in
             case (body', changed) of
               (SOME t, _) => TyExi(v', t)
             | (NONE, true) => TyExi(v', body)
             | (NONE, false) => raise Unchanged
           end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names t
                         val new_name = set_name_variant free_names name
                         val newv = (new_name, kd)
                       in
                         inst1 rkS theta ctxt (TyExi(newv, pure_type_subst [Tyv v |-> Tyv newv] body))
                       end
                     else raise e
        end
in

val inst_rank_kind1 = inst1 (* requires context; may throw Unchanged, NeedToRename *)

fun inst_rank_kind rank [] ty = inst_rank rank ty
  | inst_rank_kind rank theta ty = inst1 rank theta (Map.mkDict tyvar_compare) ty handle Unchanged => ty
end

val pure_inst_kind : (kind, kind) Lib.subst -> hol_type -> hol_type = inst_rank_kind [0]

end of old version *)


(* inst_kind aligns the ranks and kinds of its substitution *)
fun inst_kind kdS =
  let val (rktheta,kdtheta) = align_kinds kdS
  in inst_rank_kind rktheta kdtheta
  end


local
  val FORMAT = ERR "list_mk_abs_type_binder"
   "expected first arg to be a type constant of kind :(<kd>_1 => <kd>_2) => <kd>_3"
  fun check_opt NONE = Lib.I
    | check_opt (SOME c) =
      if not(is_con_type c) then raise FORMAT
      else case total (fst o Kind.kind_dom_rng o fst o Kind.kind_dom_rng o kind_of) c of
             NONE => raise FORMAT
           | SOME kd => (fn abs =>
                            let val dom = fst(Kind.kind_dom_rng(kind_of abs))
                            in mk_app_type (inst_kind[kd |-> dom] c, abs)
                            end)
in
fun list_mk_abs_type_binder binder caller = let
  val f = check_opt binder
  (* As of Mosml2.00, List.foldr is clearly not tail recursive, and you can
     blow the stack with big lists here.  Thus, the reversing of the list and
     the use of foldl instead, relying on the fact that it's hard to imagine
     not writing foldl tail-recursively *)
in
  fn (vlist, ty) =>
    if not (all is_var_type vlist) then raise ERR caller "bound variable arg not a type variable"
    else List.foldl (f o mk_abs_type) ty (List.rev vlist)
end
end (* local *)

val list_mk_abs_type = list_mk_abs_type_binder NONE "list_mk_abs_type"

local
  val FORMAT = ERR "list_mk_univ_type_binder"
   "expected first arg to be a type constant of kind :(<kd>_1 => <kd>_2) => <kd>_3"
  fun check_opt NONE = Lib.I
    | check_opt (SOME c) =
      if not(is_con_type c) then raise FORMAT
      else case total (fst o Kind.kind_dom_rng o fst o Kind.kind_dom_rng o kind_of) c of
             NONE => raise FORMAT
           | SOME kd => (fn univ =>
                            let val dom = fst(Kind.kind_dom_rng(kind_of univ))
                            in mk_app_type (inst_kind[kd |-> dom] c, univ)
                            end)
in
fun list_mk_univ_type_binder binder caller = let
  val f = check_opt binder
  (* As of Mosml2.00, List.foldr is clearly not tail recursive, and you can
     blow the stack with big lists here.  Thus, the reversing of the list and
     the use of foldl instead, relying on the fact that it's hard to imagine
     not writing foldl tail-recursively *)
in
  fn (vlist, ty) =>
    if not (all is_var_type vlist) then raise ERR caller "bound variable arg not a type variable"
    else if not (is_type_kind (kind_of ty)) then raise ERR caller "kind of body is not the base kind"
    else List.foldl (f o mk_univ_type) ty (List.rev vlist)
end
end (* local *)

val list_mk_univ_type = list_mk_univ_type_binder NONE "list_mk_univ_type"

local
  val FORMAT = ERR "list_mk_exist_type_binder"
   "expected first arg to be a type constant of kind :(<kd>_1 => <kd>_2) => <kd>_3"
  fun check_opt NONE = Lib.I
    | check_opt (SOME c) =
      if not(is_con_type c) then raise FORMAT
      else case total (fst o Kind.kind_dom_rng o fst o Kind.kind_dom_rng o kind_of) c of
             NONE => raise FORMAT
           | SOME kd => (fn exist =>
                            let val dom = fst(Kind.kind_dom_rng(kind_of exist))
                            in mk_app_type (inst_kind[kd |-> dom] c, exist)
                            end)
in
fun list_mk_exist_type_binder binder caller = let
  val f = check_opt binder
  (* As of Mosml2.00, List.foldr is clearly not tail recursive, and you can
     blow the stack with big lists here.  Thus, the reversing of the list and
     the use of foldl instead, relying on the fact that it's hard to imagine
     not writing foldl tail-recursively *)
in
  fn (vlist, ty) =>
    if not (all is_var_type vlist) then raise ERR caller "bound variable arg not a type variable"
    else if not (is_type_kind (kind_of ty)) then raise ERR caller "kind of body is not the base kind"
    else List.foldl (f o mk_exist_type) ty (List.rev vlist)
end
end (* local *)

val list_mk_exist_type = list_mk_exist_type_binder NONE "list_mk_exist_type"


(* ---------------------------------------------------------------------*)
(* Beta conversion section, including conversionals for depth search    *)
(* ---------------------------------------------------------------------*)

fun beta_conv_ty (TyApp (TyAbs (btyv,body), N))
       = pure_type_subst [Tyv btyv |-> N] body
  | beta_conv_ty _ = raise ERR "beta_conv_ty" "not a type beta redex"

fun eta_conv_ty (ty as TyAbs (tyv, TyApp(M, Tyv tyv')))
     = if tyv = tyv' then
         let val a = Tyv tyv
             val M' = fst (dest_app_type (beta_conv_ty (TyApp(ty, a))))
                      handle HOL_ERR _ => raise ERR "eta_conv_ty" "not a type eta redex"
         in if type_var_in a M' then raise ERR "eta_conv_ty" "not a type eta redex"
            else M'
         end
       else raise ERR "eta_conv_ty" "not a type eta redex"
  | eta_conv_ty _ = raise ERR "eta_conv_ty" "not a type eta redex"

exception UNCHANGEDTY;

fun qconv_ty c ty = c ty handle UNCHANGEDTY => ty

fun ifnotvarcon_ty c (Tyv  _) = raise UNCHANGEDTY
  | ifnotvarcon_ty c (TyCon _) = raise UNCHANGEDTY
  | ifnotvarcon_ty c ty = c ty

(* ---------------------------------------------------------------------*)
(* rand_conv_ty conv ``:t2 t1`` applies conv to t2                      *)
(* ---------------------------------------------------------------------*)

fun rand_conv_ty conv (TyApp(Rator,Rand)) = let
  val Newrand = conv Rand
(*
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "rand_conv_ty" message
      else
        raise ERR "rand_conv_ty" (origin_function ^ ": " ^ message)
*)
in
  TyApp(Rator, Newrand)
end
  | rand_conv_ty _ _ = raise ERR "rand_conv_ty" "not a type app"

(* ---------------------------------------------------------------------*)
(* rator_conv_ty conv ``:t2 t1`` applies conv to t1                     *)
(* ---------------------------------------------------------------------*)

fun rator_conv_ty conv (TyApp(Rator,Rand)) = let
  val Newrator = conv Rator
(*
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "rator_conv_ty" message
      else
        raise ERR "rator_conv_ty" (origin_function ^ ": " ^ message)
*)
in
  TyApp(Newrator, Rand)
end
  | rator_conv_ty _ _ = raise ERR "rator_conv_ty" "not a type app"

(* ---------------------------------------------------------------------*)
(* app_conv_ty conv ``:t2 t1`` applies conv to t1 and to t2             *)
(* ---------------------------------------------------------------------*)

fun app_conv_ty conv (TyApp(Rator, Rand)) = let in
  let
    val Rator' = conv Rator
  in
    TyApp(Rator', conv Rand) handle UNCHANGEDTY => TyApp(Rator', Rand)
  end handle UNCHANGEDTY => TyApp(Rator, conv Rand)
  end
  | app_conv_ty _ _ = raise ERR "app_conv_ty" "Not a type app"

(* ----------------------------------------------------------------------
    abs_conv_ty conv ``: \'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun abs_conv_ty conv (TyAbs(Bvar,Body)) = let
  val Newbody = conv Body
(*
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "abs_conv_ty" message
      else
        raise ERR "abs_conv_ty" (origin_function ^ ": " ^ message)
*)
in
  TyAbs(Bvar, Newbody)
end
  | abs_conv_ty _ _ = raise ERR "abs_conv_ty" "not a type abstraction"

(* ----------------------------------------------------------------------
    univ_conv_ty conv ``: !'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun univ_conv_ty conv (TyAll(Bvar,Body)) = let
  val Newbody = conv Body
(*
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "univ_conv_ty" message
      else
        raise ERR "univ_conv_ty" (origin_function ^ ": " ^ message)
*)
in
  TyAll(Bvar, Newbody)
end
  | univ_conv_ty _ _ = raise ERR "univ_conv_ty" "not a universal type"

(* ----------------------------------------------------------------------
    exist_conv_ty conv ``: !'a. t['a]`` applies conv to t['a]
   ---------------------------------------------------------------------- *)

fun exist_conv_ty conv (TyExi(Bvar,Body)) = let
  val Newbody = conv Body
(*
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function
           ["rand_conv_ty", "rator_conv_ty", "abs_conv_ty", "univ_conv_ty", "exist_conv_ty"]
         andalso origin_structure = "Type"
      then
        raise ERR "exist_conv_ty" message
      else
        raise ERR "exist_conv_ty" (origin_function ^ ": " ^ message)
*)
in
  TyExi(Bvar, Newbody)
end
  | exist_conv_ty _ _ = raise ERR "exist_conv_ty" "not an existential type"

(*---------------------------------------------------------------------------
 * Conversion that always fails;  identity element for orelse_ty.
 *---------------------------------------------------------------------------*)

fun no_conv_ty _ = raise ERR "no_conv_ty" "";

(* ----------------------------------------------------------------------
    Conversion that always succeeds, but does nothing.
    Indicates this by raising the UNCHANGEDTY exception.
   ---------------------------------------------------------------------- *)

fun all_conv_ty _ = raise UNCHANGEDTY;

(* ----------------------------------------------------------------------
    Apply two conversions in succession;  fail if either does.  Handle
    UNCHANGED appropriately.
   ---------------------------------------------------------------------- *)

infix then_ty orelse_ty;

fun (conv1 then_ty conv2) ty = let
  val ty1 = conv1 ty
in
  conv2 ty1 handle UNCHANGEDTY => ty1
end handle UNCHANGEDTY => conv2 ty

(* ----------------------------------------------------------------------
    Apply conv1;  if it raises a HOL_ERR then apply conv2. Note that
    interrupts and other exceptions (including UNCHANGEDTY) will sail on
    through.
   ---------------------------------------------------------------------- *)

fun (conv1 orelse_ty conv2) ty = conv1 ty handle HOL_ERR _ => conv2 ty;


(*---------------------------------------------------------------------------*
 * Perform the first successful conversion of those in the list.             *
 *---------------------------------------------------------------------------*)

fun first_conv_ty [] ty = no_conv_ty ty
  | first_conv_ty (a::rst) ty = a ty handle HOL_ERR _ => first_conv_ty rst ty;

(*---------------------------------------------------------------------------
 * Perform every conversion in the list.
 *---------------------------------------------------------------------------*)

fun every_conv_ty convl ty =
   itlist (curry (op then_ty)) convl all_conv_ty ty
   handle HOL_ERR _ => raise ERR "every_conv_ty" "";


(*---------------------------------------------------------------------------
 * Cause the conversion to fail if it does not change its input.
 *---------------------------------------------------------------------------*)

fun changed_conv_ty conv ty =
   let val ty1 = conv ty
           handle UNCHANGEDTY => raise ERR "changed_conv_ty" "Input type unchanged"
   in if aconv_ty ty ty1 then raise ERR "changed_conv_ty" "Input type unchanged"
      else ty1
   end;

(* ----------------------------------------------------------------------
    Cause a failure if the conversion causes the UNCHANGED exception to
    be raised.  Doesn't "waste time" doing an equality check.  Mnemonic:
    "quick changed_conv".
   ---------------------------------------------------------------------- *)

fun qchanged_conv_ty conv ty =
    conv ty
    handle UNCHANGEDTY => raise ERR "qchanged_conv_ty" "Input type unchanged"

(*---------------------------------------------------------------------------
 * Apply a conversion zero or more times.
 *---------------------------------------------------------------------------*)

fun repeat_ty conv ty =
    ((qchanged_conv_ty conv then_ty (repeat_ty conv)) orelse_ty all_conv_ty) ty;

fun try_conv_ty conv = conv orelse_ty all_conv_ty;

fun sub_conv_ty conv =
    try_conv_ty (app_conv_ty conv orelse_ty abs_conv_ty conv
                 orelse_ty univ_conv_ty conv orelse_ty exist_conv_ty conv)

fun head_betan_ty (TyApp(M as TyAbs _, N))
       = let val (btyv,body) = dest_abs_type M
         in qconv_ty head_betan_ty (pure_type_subst [btyv |-> N] body)
         end
  | head_betan_ty (ty as TyApp(ty1 as TyApp _, ty2))
       = let val ty' = TyApp(head_betan_ty ty1,ty2) (* may throw UNCHANGEDTY *)
         in try_conv_ty (beta_conv_ty then_ty qconv_ty head_betan_ty) ty' (* cannot throw UNCHANGEDTY *)
         end
  | head_betan_ty _ = raise UNCHANGEDTY

(* fun head_betan_ty = (try_conv_ty (rator_conv_ty head_betan_ty)
                           then_ty try_conv_ty (beta_conv_ty
                                                then_ty head_betan_ty)) ty *)

fun head_beta_etan_ty (TyApp(M as TyAbs _, N))
       = let val (btyv,body) = dest_abs_type M
         in qconv_ty head_beta_etan_ty (pure_type_subst [btyv |-> N] body)
         end
  | head_beta_etan_ty (ty as TyApp(ty1 as TyApp _, ty2))
       = let val ty' = TyApp(head_beta_etan_ty ty1,ty2) (* may throw UNCHANGEDTY *)
         in qconv_ty (try_conv_ty (beta_conv_ty then_ty head_beta_etan_ty)) ty' (* cannot throw UNCHANGEDTY *)
         end
  | head_beta_etan_ty (ty as TyAbs (tyv, body))
       = (abs_conv_ty head_beta_etan_ty then_ty
          try_conv_ty (abs_conv_ty (rand_conv_ty head_beta_etan_ty) then_ty
                       eta_conv_ty then_ty head_beta_etan_ty)) ty
  | head_beta_etan_ty _ = raise UNCHANGEDTY

(* ----------------------------------------------------------------------
    traversal conversionals.

    depth_conv_ty c
      bottom-up, recurse over sub-terms, and then repeatedly apply c at
      top-level.

    redepth_conv_ty c
      bottom-up. recurse over sub-terms, apply c at top, and if this
      succeeds, repeat from start.

    top_depth_conv_ty c
      top-down. Repeatdly apply c at top-level, then descend.  If descending
      doesn't change anything then stop.  If there was a change then
      come back to top and try c once more at top-level.  If this succeeds
      repeat.

    top_sweep_conv_ty c
      top-down.  Like top_depth_conv_ty but only makes one pass over the term,
      never coming back to the top level once descent starts.

    once_depth_conv_ty c
      top-down (confusingly).  Descends term looking for position at
      which c works.  Does this "in parallel", so c may be applied multiple
      times at highest possible positions in distinct sub-terms.

   ---------------------------------------------------------------------- *)

fun depth_conv_ty conv ty =
    (sub_conv_ty (depth_conv_ty conv) then_ty repeat_ty conv) ty

fun redepth_conv_ty conv ty =
    (sub_conv_ty (redepth_conv_ty conv) then_ty
     try_conv_ty (conv then_ty redepth_conv_ty conv)) ty

fun top_depth_conv_ty conv ty =
    (repeat_ty conv then_ty
     try_conv_ty (changed_conv_ty (sub_conv_ty (top_depth_conv_ty conv)) then_ty
                  try_conv_ty (conv then_ty top_depth_conv_ty conv))) ty

fun once_depth_conv_ty conv ty =
    try_conv_ty (conv orelse_ty sub_conv_ty (once_depth_conv_ty conv)) ty

fun top_sweep_conv_ty conv ty =
    (repeat_ty conv then_ty sub_conv_ty (top_sweep_conv_ty conv)) ty

val deep_beta_ty = qconv_ty (top_depth_conv_ty beta_conv_ty)

val deep_eta_ty = qconv_ty (top_depth_conv_ty eta_conv_ty)

val deep_beta_eta_ty = qconv_ty (top_depth_conv_ty (beta_conv_ty orelse_ty eta_conv_ty))

fun strip_app_beta_eta_type ty = strip_app_type (deep_beta_eta_ty ty)

(*  head_beta1_ty reduces the head beta redex; fails if one does not exist. *)
fun head_beta1_ty ty = (rator_conv_ty head_beta1_ty orelse_ty beta_conv_ty) ty

(*  head_beta_ty repeatedly reduces any head beta redexes; never fails *)
(*  result has at its top level its actual shape *)
(* val head_beta_ty = qconv_ty (repeat_ty head_beta1_ty) *)
val head_beta_ty = qconv_ty head_betan_ty
val head_beta_eta_ty = qconv_ty head_beta_etan_ty


local
open Map
val EQ = Portable.pointer_eq

fun abconv0_ty n E (t1,t2) = abconv1_ty n E (head_beta_ty t1, head_beta_ty t2)
and abconv1_ty n (E as (env1,env2)) p = EQ p orelse
     case p
      of (u as Tyv _, v as Tyv _) => map_type_var_compare E (u,v) = EQUAL
       | (u as TyCon _,v as TyCon _) => type_con_compare (u,v) = EQUAL
       | (TyApp(p,t1),TyApp(q,t2)) => abconv1_ty n E (p,q) andalso abconv0_ty n E (t1,t2)
       | (TyAbs(x1 as (_,k1),ty1),
          TyAbs(x2 as (_,k2),ty2)) => k1 = k2 andalso
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abconv0_ty (n+1) E' (ty1,ty2)
                                      end
       | (TyAll(x1 as (_,k1),ty1),
          TyAll(x2 as (_,k2),ty2)) => k1 = k2 andalso
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abconv0_ty (n+1) E' (ty1,ty2)
                                      end
       | (TyExi(x1 as (_,k1),ty1),
          TyExi(x2 as (_,k2),ty2)) => k1 = k2 andalso
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abconv0_ty (n+1) E' (ty1,ty2)
                                      end
       | _ => false

fun abeconv0_ty n E (t1,t2) = abeconv1_ty n E (head_beta_eta_ty t1, head_beta_eta_ty t2)
and abeconv1_ty n (E as (env1,env2)) p = EQ p orelse
     case p
      of (u as Tyv _, v as Tyv _) => map_type_var_compare E (u,v) = EQUAL
       | (u as TyCon _,v as TyCon _) => type_con_compare (u,v) = EQUAL
       | (TyApp(p,t1),TyApp(q,t2)) => abeconv1_ty n E (p,q) andalso abeconv0_ty n E (t1,t2)
       | (TyAbs(x1 as (_,k1),ty1),
          TyAbs(x2 as (_,k2),ty2)) => k1 = k2 andalso
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abeconv0_ty (n+1) E' (ty1,ty2)
                                      end
       | (TyAll(x1 as (_,k1),ty1),
          TyAll(x2 as (_,k2),ty2)) => k1 = k2 andalso
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abeconv0_ty (n+1) E' (ty1,ty2)
                                      end
       | (TyExi(x1 as (_,k1),ty1),
          TyExi(x2 as (_,k2),ty2)) => k1 = k2 andalso
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abeconv0_ty (n+1) E' (ty1,ty2)
                                      end
       | _ => false

fun abeconv_ge0_ty n E (t1,t2) = abeconv_ge1_ty n E (head_beta_eta_ty t1, head_beta_eta_ty t2)
and abeconv_ge1_ty n (E as (env1,env2)) p = EQ p orelse
     case p
      of (u as Tyv _, v as Tyv _) => map_type_var_ge E (u,v)
       | (u as TyCon _,v as TyCon _) => type_con_ge (u,v)
       | (TyApp(p,t1),TyApp(q,t2)) => abeconv_ge1_ty n E (p,q) andalso abeconv_ge0_ty n E (t1,t2)
       | (TyAbs(x1 as (_,k1),ty1),
          TyAbs(x2 as (_,k2),ty2)) => k1 = k2 andalso
       (* TyAbs(x2 as (_,k2),ty2)) => k1 :>=: k2 andalso *)
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abeconv_ge0_ty (n+1) E' (ty1,ty2)
                                      end
       | (TyAll(x1 as (_,k1),ty1),
          TyAll(x2 as (_,k2),ty2)) => k1 = k2 andalso
       (* TyAll(x2 as (_,k2),ty2)) => k1 :>=: k2 andalso *)
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abeconv_ge0_ty (n+1) E' (ty1,ty2)
                                      end
       | (TyExi(x1 as (_,k1),ty1),
          TyExi(x2 as (_,k2),ty2)) => k1 = k2 andalso
       (* TyExi(x2 as (_,k2),ty2)) => k1 :>=: k2 andalso *)
                                      let val E' = (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n))
                                      in abeconv_ge0_ty (n+1) E' (ty1,ty2)
                                      end
       | _ => false

in
fun abconv_ty t1 t2  = abconv0_ty 0 (empty_env, empty_env) (t1,t2)
                   (*  aconv_ty (deep_beta_ty t1) (deep_beta_ty t2)  *)
fun abeconv_ty t1 t2 = abeconv0_ty 0 (empty_env, empty_env) (t1,t2)
                  (*   aconv_ty (deep_beta_eta_ty t1) (deep_beta_eta_ty t2)  *)
fun ge_ty t1 t2 = abeconv_ge0_ty 0 (empty_env, empty_env) (t1,t2)
end

val eq_ty = abeconv_ty

(* fun subtype t1 t2 = asubtype (deep_beta_eta_ty t1) (deep_beta_eta_ty t2) *)

local
fun align_types0 [] = ((0,false),([],[]))
  | align_types0 ({redex,residue} :: s) =
      Kind.raw_match_kind (kind_of redex) (kind_of residue) (align_types0 s)
in
fun align_types theta = let
        val ((rkS,_),(kdS,_)) = Kind.norm_subst (align_types0 theta)
        val inst_fn = inst_rank_kind rkS kdS
        fun inst_redex [] = []
          | inst_redex ({redex,residue} :: s) = let
                val redex' = inst_fn redex
              in
                if eq_ty redex' residue then inst_redex s
                else (redex' |-> residue) :: inst_redex s
              end
      in
        (rkS, kdS, if rkS=0 andalso null kdS then theta else inst_redex theta)
      end
      handle e as HOL_ERR _ => raise ERR "align_types" "alignment failed"
end

(* type_subst aligns the ranks and kinds of its substitution *)
fun type_subst theta =
  let val (rktheta,kdtheta,tytheta) = align_types theta
  in inst_rk_kd_ty rktheta kdtheta tytheta
  end

(* ty_sub aligns the ranks and kinds of its substitution *)
fun ty_sub theta =
  let val (rktheta,kdtheta,tytheta) = align_types theta
  in rk_kd_ty_sub rktheta kdtheta tytheta
  end

(* val type_subst0 = type_subst
fun type_subst theta = Profile.profile "type_subst" (type_subst0 theta) *)


(*---------------------------------------------------------------------------
   Redefine the comparison relations and substitution functions
   to involve beta reduction for external use.
 ---------------------------------------------------------------------------*)

val raw_dom_rng = dom_rng
val dom_rng = fn ty => raw_dom_rng ty handle HOL_ERR _ => raw_dom_rng (head_beta_eta_ty ty)

local open Map
in
val raw_compare0 = compare0
(* fun compare0 m (env1, env2) (ty1, ty2) =
      raw_compare0 m (env1, env2) (deep_beta_eta_ty ty1, deep_beta_eta_ty ty2) *)
fun compare0 n E (t1,t2) = compare1 n E (head_beta_eta_ty t1, head_beta_eta_ty t2)
and compare1 n (E as (env1,env2)) p =
     case p
      of (u as Tyv _, v as Tyv _)    => map_type_var_compare E (u,v)
       | (Tyv _, _)                  => LESS
       | (TyCon _, Tyv _)            => GREATER
       | (u as TyCon _,v as TyCon _) => type_con_compare (u,v)
       | (TyCon _, _)                => LESS
       | (TyApp _, Tyv _)            => GREATER
       | (TyApp _, TyCon _)          => GREATER
       | (TyApp p1,TyApp p2)         => Lib.pair_compare(compare0 n E,compare0 n E)(p1,p2)
       | (TyApp _, _)                => LESS
       | (TyAll _, TyAbs _)          => LESS
       | (TyAll _, TyExi _)          => LESS
       | (TyAll(x1 as (_,k1),ty1),
          TyAll(x2 as (_,k2),ty2))   =>
              Lib.pair_compare(kind_compare,
                               compare0 (n+1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                              ((k1,ty1),(k2,ty2))
       | (TyAll _, _)                => GREATER
       | (TyExi _, TyAbs _)          => LESS
       | (TyExi(x1 as (_,k1),ty1),
          TyExi(x2 as (_,k2),ty2))   =>
              Lib.pair_compare(kind_compare,
                               compare0 (n+1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                              ((k1,ty1),(k2,ty2))
       | (TyExi _, _)                => GREATER
       | (TyAbs(x1 as (_,k1),ty1),
          TyAbs(x2 as (_,k2),ty2))   =>
              Lib.pair_compare(kind_compare,
                               compare0 (n+1) (insert(env1, Tyv x1, n), insert(env2, Tyv x2, n)))
                              ((k1,ty1),(k2,ty2))
       | (TyAbs _, _)                => GREATER
end (* local *)

val raw_compare = compare
fun compare p = if Portable.pointer_eq p then EQUAL
                else compare0 0 (empty_env, empty_env) p
val raw_empty_tyset = empty_tyset
val empty_tyset = HOLset.empty compare
val raw_type_eq = type_eq
fun type_eq t1 t2 = compare(t1,t2) = EQUAL;


(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for types.                                      *
 *---------------------------------------------------------------------------*)

val dot     = "."
val dollar  = "$"
val percent = "%";

fun pp_raw_type pps ty =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_kind = Kind.pp_kind pps
     fun pp_kind_p kind =
          ( if kind = typ rho then ()
            else (add_string ":"; pp_kind kind) )
(*
     fun pp_kind_rank (kind,rank) =
          ( if kind = typ then ()
            else (add_string "::"; pp_kind kind);
            if rank = 0 then ()
            else add_string ("/"^Lib.int_to_string rank) )
*)
     fun pp (TyAbs(Btyvar,Body)) =
          ( add_string "(\\:";
            pp (Tyv Btyvar); add_string dot; add_break(1,0);
            pp Body; add_string ")" )
      | pp (TyAll(Btyvar,Body)) =
          ( add_string "(!:";
            pp (Tyv Btyvar); add_string dot; add_break(1,0);
            pp Body; add_string ")" )
      | pp (TyExi(Btyvar,Body)) =
          ( add_string "(?:";
            pp (Tyv Btyvar); add_string dot; add_break(1,0);
            pp Body; add_string ")" )
      | pp (TyApp(Rator as TyApp(TyCon(id,_),Rand1),Rand2)) =
          if KernelSig.name_of id = "fun"
          then
          ( add_string "("; pp Rand1;
            add_string " ->"; add_break(1,0);
            pp Rand2; add_string ")" )
          else
          ( add_string "("; pp Rand2; add_break(1,0);
                            pp Rator; add_string ")")
      | pp (ty as TyApp(Rator,Rand)) =
          let val (c,args) = strip_app_type ty
          in if length args = 1 then
          ( add_string "("; pp Rand; add_break(1,0);
                            pp Rator; add_string ")")
             else
          ( add_string "(("; pps args; add_string ")";
            add_break(1,0); pp c; add_string ")" )
          end
      | pp (Tyv (name,kind)) =
         ( add_string name;
           add_string ":";
           pp_kind kind )
      | pp (TyCon (id,kind)) =
         ( add_string ( (* seg_of id^dollar^ *) KernelSig.name_of id);
           add_string ":";
           pp_kind kind )
    and pps [] = ()
      | pps [ty] = pp ty
      | pps (ty :: tys) = (pp ty; add_string ",";
                           add_break(0,0); pps tys)
 in
   begin_block INCONSISTENT 0;
   add_string "`:";
   pp ty;
   add_string "`";
   end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to a string                            *)
(*---------------------------------------------------------------------------*)

fun sprint pp x = HOLPP.pp_to_string 80 pp x

val type_to_string = sprint pp_raw_type;


(*---------------------------------------------------------------------------
       Higher order matching (from jrh via Michael Norrish - June 2001)
       Adapted to HOL-Omega types by PVH - July 18, 2008
 ---------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_type error" s
  val trace_complex_matching = ref 0
  val _ = Feedback.register_trace ("Type.trace_complex_matching",
                                   trace_complex_matching, 1)
  exception NOT_FOUND
  val eq_ty = abeconv_ty (* beta- and eta-reduction NOT ASSUMMED before entering these functions *)
  fun find_residue red [] = raise NOT_FOUND
    | find_residue red ({redex,residue}::rest) = if red = redex then residue
                                                    else find_residue red rest
  fun find_residue_ty red [] = raise NOT_FOUND
    | find_residue_ty red ({redex,residue}::rest) = if eq_ty red redex then residue
                                                    else find_residue_ty red rest
  fun in_dom x [] = false
    | in_dom x ({redex,residue}::rest) = (x = redex) orelse in_dom x rest
  fun safe_insert_ty (n as {redex,residue}) l = let
    val z = find_residue(*_ty*) redex l
  in
    if residue = z then l
    else raise ERR "safe_insert_ty" "match"
  end handle NOT_FOUND => n::l
  fun safe_insert_tya (n as {redex,residue}) l = let
    val z = find_residue(*_ty*) redex l
  in
    if eq_ty residue z then l
    else raise ERR "safe_insert_tya" "match"
  end handle NOT_FOUND => n::l
  fun mk_fresh_dummy_ty () = let
    val name = dest_vartype(gen_tyvar())
  in fn kd => with_flag (varcomplain,false) mk_var_type(name, kd)
  end
  val mk_dummy_ty = mk_fresh_dummy_ty ()
(**)
  val dummy_name = fst(dest_var_type (mk_dummy_ty (typ 0)))
  fun is_dummy_ty ty = (*is_gen_tyvar ty andalso*) not (fst(dest_var_type ty) = dummy_name)
(**)
  val mk_con_dummy_ty = mk_fresh_dummy_ty ()
  val con_dummy_name = fst(dest_var_type (mk_con_dummy_ty (typ 0)))
  fun is_con_dummy_ty ty = (fst(dest_var_type ty) = con_dummy_name)
  fun var_cmp (x as Tyv(xs,xkd)) (Tyv(ys,ykd)) =
      (xs = ys) andalso (if is_con_dummy_ty x then xkd :=: ykd
                         else if xs=dummy_name then ykd :>=: xkd
                         else xkd = ykd)
    | var_cmp anything other = false

  fun rator_type ty = fst (dest_app_type ty)
  fun kindE [] = ([],[])
    | kindE ({redex,residue}::s) =
        let val (E1,E2) = kindE s
        in (kind_of redex::E1, kind_of residue::E2)
        end


(*
  fun type_pmatch lconsts env pat ob sofar
      = type_pmatch_1 lconsts env (head_beta_ty pat) (head_beta_ty ob) sofar

  and type_pmatch_1 lconsts env vty cty (sofar as (insts,homs)) =
    if is_var_type vty then let
        val cty' = find_residue_ty vty env
      in
        if eq_ty cty' cty then sofar else MERR "type variable mismatch"
      end handle NOT_FOUND =>
                 if HOLset.member(lconsts, vty) then
                   if cty = vty then sofar
                   else MERR "can't instantiate local constant type"
                 else (safe_insert_tya (vty |-> cty) insts, homs)
               | HOL_ERR _ => MERR "free type variable mismatch"
    else if is_con_type vty then let
        val {Thy = vthy, Tyop = vname, Kind = vkd, Rank = vrk} = dest_thy_con_type vty
        val {Thy = cthy, Tyop = cname, Kind = ckd, Rank = crk} = dest_thy_con_type cty
                handle HOL_ERR _ => MERR "type constant mismatched with non-constant"
      in
        if vname = cname andalso vthy = cthy then
          if ckd = vkd andalso crk = vrk then sofar
          else (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
        else MERR "type constant mismatch"
      end
    else if is_abs_type vty then let
        val (vv,vbod) = dest_abs_type vty
        val (cv,cbod) = dest_abs_type cty
                handle HOL_ERR _ => MERR "abstraction type mismatched with non-abstraction type"
        val (_, vkd, vrk) = dest_var_type vv
        val (_, ckd, crk) = dest_var_type cv
        val sofar' = (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
      in
        type_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else if is_univ_type vty then let
        val (vv,vbod) = dest_univ_type vty
        val (cv,cbod) = dest_univ_type cty
                handle HOL_ERR _ => MERR "universal type mismatched with non-universal type"
        val (_, vkd, vrk) = dest_var_type vv
        val (_, ckd, crk) = dest_var_type cv
        val sofar' = (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
      in
        type_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else if is_exist_type vty then let
        val (vv,vbod) = dest_exist_type vty
        val (cv,cbod) = dest_exist_type cty
                handle HOL_ERR _ => MERR "existential type mismatched with non-existential type"
        val (_, vkd, vrk) = dest_var_type vv
        val (_, ckd, crk) = dest_var_type cv
        val sofar' = (safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts, homs)
      in
        type_pmatch lconsts ((vv |-> cv)::env) vbod cbod sofar'
      end
    else (* is_app_type *) let
        val vhop = repeat rator_type vty
      in
        if is_var_type vhop andalso not (HOLset.member(lconsts, vhop)) andalso
           not (in_dom vhop env)
        then let (* kind_of and rank_of can fail if given an open type with free bound variables, as cty might be *)
            val vkd = kd_of vty (map (kind_of o #redex  ) env)
            val vrk = rk_of vty (map (rank_of o #redex  ) env)
            val ckd = kd_of cty (map (kind_of o #residue) env)
            val crk = rk_of cty (map (rank_of o #residue) env)
            val insts' = if vkd = ckd andalso vrk = crk then insts
                         else safe_insert_tya (mk_dummy_ty(vkd,vrk) |-> mk_dummy_ty(ckd,crk)) insts
          in
            (insts', (env,cty,vty)::homs)
          end
        else let
            val (lv,rv) = dest_app_type vty
            val (lc,rc) = dest_app_type cty
                handle HOL_ERR _ => MERR "application type mismatched with non-application type"
            val sofar' = type_pmatch lconsts env lv lc sofar
          in
            type_pmatch lconsts env rv rc sofar'
          end
      end
*)

  fun type_pmatch lconsts env pat ob sofar
      = type_pmatch_1 lconsts env (head_beta_eta_ty pat) (head_beta_eta_ty ob) sofar

  and type_pmatch_1 lconsts env (vty as Tyv(_,kd)) cty (sofar as (insts,homs))
      = (let
           val cty' = find_residue vty env
         in
           if cty' = cty then sofar else MERR "free type variable mismatch"
         end handle NOT_FOUND =>
                 if HOLset.member(lconsts, vty) then
                   if cty = vty then sofar
                   else MERR "can't instantiate local constant type"
                 else (safe_insert_tya (vty |-> cty) insts, homs)
               | HOL_ERR _ => MERR "free type variable mismatch")
    | type_pmatch_1 lconsts env (vty as TyCon(vc,vkd)) cty (sofar as (insts,homs))
      = (case cty of
            TyCon(cc,ckd) =>
              if vc = cc then
                if ckd = vkd then sofar
                else let val mk_dummy_ty = mk_con_dummy_ty
                     in (safe_insert_tya (mk_dummy_ty vkd |-> mk_dummy_ty ckd) insts, homs)
                     end
              else MERR "type constant mismatch"
          | _ => MERR "type constant mismatched with non-constant")
    | type_pmatch_1 lconsts env (vty as TyApp(lv,rv)) cty (sofar as (insts,homs))
      = let
          val vhop = repeat rator_type lv
        in
          if is_var_type vhop andalso not (HOLset.member(lconsts, vhop)) andalso
             not (in_dom vhop env)
          then
            let
              val vkd = kind_of vty
              val ckd = kind_of cty
              val insts' = if vkd = ckd then insts
                           else safe_insert_tya (mk_dummy_ty vkd |-> mk_dummy_ty ckd) insts
            in
              (insts', (env,cty,vty)::homs)
            end
          else
            case cty of
               TyApp(lc,rc) =>
                 let
                   val sofar' = type_pmatch_1 lconsts env lv lc sofar (* lv,lc are head-beta-eta-reduced *)
                 in
                   type_pmatch lconsts env rv rc sofar'
                 end
             | _ => MERR "application type mismatched with non-application type"
        end
    | type_pmatch_1 lconsts env (vty as TyAbs((_,vkd),_)) cty (insts,homs)
      = (case cty of
           TyAbs((_,ckd),_) =>
             let
               val (vv,vbody) = dest_abs_type vty
               val (cv,cbody) = dest_abs_type cty
               val sofar' = (safe_insert_tya (mk_dummy_ty vkd |-> mk_dummy_ty ckd) insts, homs)
             in
               type_pmatch_1 lconsts ((vv |-> cv)::env) vbody cbody sofar' (* bodies are head-beta-eta reduced *)
             end
         | _ => MERR "abstraction type mismatched with non-abstraction type")
    | type_pmatch_1 lconsts env (vty as TyAll((_,vkd),_)) cty (insts,homs)
      = (case cty of
           TyAll((_,ckd),_) =>
             let
               val (vv,vbody) = dest_univ_type vty
               val (cv,cbody) = dest_univ_type cty
               val sofar' = (safe_insert_tya (mk_dummy_ty vkd |-> mk_dummy_ty ckd) insts, homs)
             in
               type_pmatch lconsts ((vv |-> cv)::env) vbody cbody sofar'
             end
         | _ => MERR "universal type mismatched with non-universal type")
    | type_pmatch_1 lconsts env (vty as TyExi((_,vkd),_)) cty (insts,homs)
      = (case cty of
           TyExi((_,ckd),_) =>
             let
               val (vv,vbody) = dest_exist_type vty
               val (cv,cbody) = dest_exist_type cty
               val sofar' = (safe_insert_tya (mk_dummy_ty vkd |-> mk_dummy_ty ckd) insts, homs)
             in
               type_pmatch lconsts ((vv |-> cv)::env) vbody cbody sofar'
             end
         | _ => MERR "existential type mismatched with non-existential type")


fun get_rank_kind_insts avoids (env:(hol_type,hol_type)subst) L (rk,(kdS,Id)) =
      itlist (fn {redex,residue} =>
                prim_match_kind (is_con_dummy_ty redex)
                                (kind_of redex  )
                                (kind_of residue))
             L (rk,(kdS,union avoids Id))

fun separate_insts_ty lift rk kdavoids kdS env
         (insts :{redex : hol_type, residue : hol_type} list) = let
  val (realinsts, patterns) = partition (is_var_type o #redex) insts
  val betacounts =
      if patterns = [] then []
      else
        itlist (fn {redex = p,...} =>
                   fn sof => let
                        val (hop,args) = strip_app_type p
                      in
                        safe_insert_ty (hop |-> length args) sof
                      end handle _ =>
                                 (HOL_WARNING "" ""
                                  "Inconsistent patterning in h.o. type match";
                                  sof))
        patterns []
  val rk_kd_ins as (rkin as (rkS',_),kdins) = get_rank_kind_insts kdavoids env realinsts (rk,kdS)
  val kdins' as (kdS',_) = snd (Kind.norm_subst rk_kd_ins)
  val inst_rk_kd = Kind.inst_rank_kind rkS' kdS'
in
  (betacounts,
   mapfilter (fn {redex = x, residue = t} => let
                   val x' = let val (xs,xkd) = dest_var_type x
                            in with_flag (varcomplain,false)
                              mk_var_type(xs, inst_rk_kd xkd)
                            end
                 in
                   if var_cmp t x' (* orelse ge_ty x' t (*not t = x'*) *) then raise ERR "separate_insts_ty" ""
                             else {redex = if lift then x' else x, residue = t}
             end) realinsts,
   if lift then kdins' else kdins,
   rkin)
end


fun kdenv_in_dom x (env, idlist) = mem x idlist orelse in_dom x env
fun kdenv_find_residue x (env, idlist) = if mem x idlist then x
                                         else find_residue x env
fun kdenv_safe_insert (t as {redex,residue}) (E as (env, idlist)) = let
  val existing = kdenv_find_residue redex E
in
  if existing = residue then E else raise ERR "kdenv_safe_insert" "Kind bindings clash"
end handle NOT_FOUND => if redex = residue then (env, redex::idlist)
                        else (t::env, idlist)


fun all_abconv [] [] = true
  | all_abconv [] _ = false
  | all_abconv _ [] = false
  | all_abconv (h1::t1) (h2::t2) = eq_ty h1 h2 andalso all_abconv t1 t2

fun freeze_operators vhops insts =
  List.foldr (fn (ty,insts) => safe_insert_tya (ty |-> ty) insts) insts vhops

fun map_redexes f =
  map (fn {redex,residue} => f redex |-> residue)
fun subst_redexes theta = map_redexes (type_subst theta)
fun map_insts f =
  map (fn {redex,residue} => f redex |-> f residue)
fun swap_subst theta =
  map (fn {redex,residue} => residue |-> redex) theta

fun split_insts vhops insts =
  partition (fn {redex, residue} =>
             op_mem eq_ty (fst (strip_app_type redex)) vhops) insts

fun print_insts str insts =
  (print (str ^ " insts:\n");
   print_insts0 insts)
and
    print_insts0 [] = ()
  | print_insts0 (inst::insts) = (print_inst inst; print_insts0 insts)
and
    print_inst {redex,residue} =
             print ("   " ^ type_to_string redex ^
                    " |-> " ^ type_to_string residue ^ "\n") ;


fun type_homatch kdavoids lconsts rkin kdins (insts, homs) = let
  (* local constants of kinds and types never change *)
  val (var_homs,nvar_homs) = partition (fn (env,cty,vty) => is_var_type vty) homs
  fun args_are_fixed (env,cty,vty) = let
       val (vhop, vargs) = strip_app_type vty
       val afvs = type_varsl vargs
    in all (fn a => can (find_residue_ty a) env orelse can (find_residue_ty a) insts
                    orelse HOLset.member(lconsts, a)) afvs
    end
  val (fixed_homs,basic_homs) = partition args_are_fixed nvar_homs
  fun args_are_distinct_vars (env,cty,vty) = let
       val (vhop, vargs) = strip_app_type vty
       fun distinct (x::xs) = not (mem x xs) andalso distinct xs
         | distinct _ = true
    in all is_var_type vargs andalso distinct vargs
    end
  val (distv_homs,real_homs) = partition args_are_distinct_vars fixed_homs
  val ordered_homs = var_homs @ distv_homs @ real_homs @ basic_homs
  val (_,kdins') = Kind.norm_subst(rkin,kdins)
  val inst_fn = inst_rank_kind (fst rkin) (fst kdins')
  fun fix_con_dummy_ty (i as {redex,residue}) =
    if is_con_dummy_ty redex
      (* then equalize the ranks of the "floating" constant instances *)
      then let val redex' = inst_fn redex
               val inc = Int.max(rank_of_type redex' - rank_of_type residue, 0)
           in redex |-> inst_rank inc residue
           end
      else i
  fun homatch rkin kdins (insts, homs) =
  if homs = [] then insts
  else let
      val (env,cty,vty) = hd homs
    in
      if is_var_type vty then
        if eq_ty cty vty then homatch rkin kdins (insts, tl homs)
        else let
            val vkd = kind_of vty (* kd_of vty (map (kind_of o #redex  ) env) *)
            val ckd = kd_of cty (map (kind_of o #residue) env)
            val (newrkin,kdins')  = raw_match_kind vkd ckd (rkin,kdins)
            val newkdins = kdenv_safe_insert (vkd |-> ckd) kdins'
            val newinsts = safe_insert_tya (vty |-> cty) insts (* (vty |-> cty)::insts *)
          in
            homatch newrkin newkdins (newinsts, tl homs)
          end
      else (* vty not a type var *) let
          val (vhop, vargs) = strip_app_type vty (* vhop should be a type variable *)
          val afvs = type_varsl vargs
          val (_,kdins') = Kind.norm_subst(rkin,kdins)
          val inst_fn = inst_rank_kind (fst rkin) (fst kdins')
        in
          (let
             val tyins =
                 map (fn a =>
                         (inst_fn a |->
                                  (find_residue(*_ty*) a env
                                   handle _ =>
                                          find_residue(*_ty*) a insts
                                   handle _ =>
                                          if HOLset.member(lconsts, a)
                                          then a
                                          else raise ERR "type_homatch" "not bound"))) afvs
             val pats0 = map inst_fn vargs
             val pats = map (pure_type_subst tyins) pats0
             val vhop' = inst_fn vhop
             val icty = list_mk_app_type(vhop', pats)
             val ni = let
               val (chop,cargs) = strip_app_type cty
             in
               if all_abconv cargs pats then
                 if eq_ty chop vhop then insts
                 else safe_insert_tya (vhop |-> chop) insts
               else let
                   val ginsts = map (fn p => (p |->
                                                (if is_var_type p then p
                                                 else gen_var_type(kd_of p (map (kind_of o #redex) env)))))
                                    pats
                   val cty' = full_type_subst ginsts cty
                   val gvs = map #residue ginsts
                   val absty = list_mk_abs_type(gvs,cty')
                   val vinsts = safe_insert_tya (vhop |-> absty) insts
                   val icpair = (list_mk_app_type(vhop',gvs) |-> cty')
                 in
                   (* safe_insert_tya icpair *) vinsts
                   (* icpair::vinsts *)
                 end
             end
           in
             homatch rkin kdins (ni,tl homs)
           end) handle HOL_ERR _ => (
                       let
                         val chop = find_residue(*_ty*) vhop insts (* may raise NOT_FOUND *)
                         val _ = if eq_ty vhop chop then raise NOT_FOUND else ()
                         val vty1 = deep_beta_eta_ty (pure_type_subst (map_redexes inst_fn (env@insts)) (inst_fn vty))
                                        handle HOL_ERR _ => vty
                       in
                         if eq_ty vty1 cty then
                           (* drop this hom as subsumed by current insts *)
                           homatch rkin kdins (insts,tl homs)
                         else let
                           val _ = if !trace_complex_matching = 0 then () else
                                     (print ("Complex match " ^ type_to_string vty ^ "\n" ^
                                             "           to " ^ type_to_string cty ^ "\n"))
                           fun types_to_string (ty::tys) = " " ^ type_to_string ty ^ types_to_string tys
                             | types_to_string    []     = ""
                           val lconstsl = HOLset.listItems lconsts
                           val fixed = map #redex env @ lconstsl
                           val vfixed = vhop :: fixed
                           val pat_tyvars = subtract (type_vars vty) vfixed
                           val vfixed1 = map inst_fn vfixed
                           val freeze_tyvars = subtract (type_vars chop) (map #residue env @ lconstsl)
                           val all_pvars = Lib.U [pat_tyvars, fixed,
                                                  filter is_var_type (map #redex insts)]
                           val all_pvars1 = map inst_fn all_pvars
                           val all_tvars = Lib.U [freeze_tyvars, type_vars cty, map #residue env,
                                                  type_varsl (map #residue insts)]
                           val all_vars = union all_pvars1 all_tvars
                           fun new_tyvar (v,vs) = (if mem v freeze_tyvars
                                                      then variant_type (vs @ all_vars) v
                                                           (* gen_var_type(kind_of v,rank_of v) *)
                                                      else v) :: vs
                           val mod_pvars = intersect (subtract all_pvars1 vfixed1) freeze_tyvars
                           val mod_pvars' = foldr new_tyvar [] mod_pvars
                           (* now there are no tyvars in both all_pvars1 and freeze_tyvars *)
                           val theta = map (op |->) (zip mod_pvars mod_pvars')
                           val vhop' = inst_fn vhop
                           val vty'  = inst_fn vty
                           val vty1' = deep_beta_eta_ty (pure_type_subst ((vhop' |-> chop)::theta) vty')
                                         handle HOL_ERR _ =>
                                            (if !trace_complex_matching = 0 then () else
                                                (print ("Formation of new pattern failed: " ^
                                                 type_to_string vty' ^ " [" ^ type_to_string chop ^
                                                 " / " ^ type_to_string vhop' ^ "]\n"));
                                             raise NOT_FOUND)
                           val (vhop_str,_) = dest_var_type vhop
                           val _ = if !trace_complex_matching = 0 then () else
                                     (print ("  Expanding type operator " ^ vhop_str
                                             ^ " |-> " ^ type_to_string chop ^ "\n");
                                      print ("     Matching " ^ type_to_string vty1' ^ "\n" ^
                                             "           to " ^ type_to_string cty   ^ "\n");
                                      print ("  freezing:" ^ types_to_string freeze_tyvars ^ "\n");
                                      print ("  pattern: " ^ types_to_string pat_tyvars  ^ "\n");
                                      print ("  modifying pat tyvars:" ^ types_to_string mod_pvars  ^ "\n");
                                      if mod_pvars = mod_pvars' then () else
                                      print ("            renamed as:" ^ types_to_string mod_pvars' ^ "\n");
                                      if map #redex env = map #residue env then () else
                                      print_insts "environment" env)
                           val (f_insts0,nf_insts0) = split_insts freeze_tyvars insts
                           val nf_insts1 = map_redexes (fn ty => if is_var_type ty then inst_fn ty
                                                                 else ty)
                                                       nf_insts0
                           val nf_insts2 = subst_redexes theta nf_insts1
                           val _ = if !trace_complex_matching = 0 then () else
                                     (print_insts "all original" insts;
                                      print_insts "pre-freeze" f_insts0;
                                      print_insts "instantiated" nf_insts1;
                                      if mod_pvars = mod_pvars' then () else
                                      print_insts "renamed" nf_insts2)
                           val env' = map_redexes inst_fn env
                           val insts' = freeze_operators freeze_tyvars nf_insts2
                                        handle HOL_ERR _ =>
                                          (* conflicts with existing inst? should never happen *)
                                          (if !trace_complex_matching = 0 then () else
                                             print "  Freezing operators failed.\n";
                                           raise NOT_FOUND)
                           val _ = if !trace_complex_matching = 0 then () else
                                     (print_insts "subproblem" insts')
                         in let
                           val pinsts_homs' =
                             type_pmatch lconsts env' vty1' cty (insts', [] (* note NOT tl homs! *))
                           val (rkin',kdins') =
                             get_rank_kind_insts kdavoids env'
                                        (fst pinsts_homs')
                                        ((0, false), ([], []))
                           val new_insts = homatch rkin' kdins' pinsts_homs'
                           (* new_insts is the answer from the subproblem *)
                           val (_,nf_insts3) = split_insts freeze_tyvars new_insts
                           val nf_insts4 = subst_redexes (swap_subst theta) nf_insts3
                           val inv_inst = zip all_pvars1 all_pvars
                           fun lookup v = assoc v inv_inst handle _ => v
                           val nf_insts5 = map_redexes lookup nf_insts4
                           val insts' = f_insts0 @ nf_insts5
                           val _ = if !trace_complex_matching = 0 then () else
                                     (print ("Expanding type operator " ^ vhop_str ^ " succeeded!\n");
                                      print_insts "subproblem yielded" new_insts;
                                      print_insts "non-frozen new" nf_insts3;
                                      if mod_pvars = mod_pvars' then () else
                                      print_insts "un-renamed new" nf_insts4;
                                      print_insts "un-instantiated" nf_insts5;
                                      print_insts "final result" insts';
                                      print "\n")
                         in
                           homatch rkin' kdins' (insts', tl homs)
                         end
                         handle e => (if !trace_complex_matching = 0 then () else
                                        (print "Subproblem failed.\n";
                                         print ("Expanding type operator " ^ vhop_str ^ " failed:" ^
                                                Feedback.exn_to_string e ^ "\n"));
                                      raise NOT_FOUND)
                         end
                       end
                handle NOT_FOUND => let
                         val (lc,rc) = dest_app_type cty
                         val (lv,rv) = dest_app_type vty
                         val pinsts_homs' =
                             type_pmatch lconsts env rv rc
                                         (insts, (env,lc,lv)::(tl homs))
                         val (rkin',kdins') =
                             get_rank_kind_insts kdavoids env
                                            (fst pinsts_homs')
                                            ((0, false), ([], []))
                       in
                         homatch rkin' kdins' pinsts_homs'
                       end)
        end
    end
in
  homatch rkin kdins (map fix_con_dummy_ty insts, ordered_homs)
end

in

val type_pmatch = type_pmatch
val get_rank_kind_insts = get_rank_kind_insts
val type_homatch = type_homatch
val separate_insts_ty = separate_insts_ty

fun ho_match_type1 lift kdavoids lconsts vty cty insts_homs rk_kd_insts_ids = let
  val pinsts_homs = type_pmatch lconsts [] vty cty insts_homs
  val (rkin,kdins) = get_rank_kind_insts kdavoids [] (fst pinsts_homs) rk_kd_insts_ids
  val insts = type_homatch kdavoids lconsts rkin kdins pinsts_homs
in
  separate_insts_ty lift rkin kdavoids kdins [] insts
end

fun ho_match_type0 lift rkfixed kdavoids lconsts vty cty = let
  val (bcs, tyins, kdins, rkin) = ho_match_type1 lift kdavoids lconsts vty cty ([], []) ((0,rkfixed), ([], []))
in
  (tyins, fst kdins, fst rkin)
end handle e => raise (wrap_exn "HolKernel" "ho_match_type" e)

(* Note this checks with ge_ty for greater than or equal (of ranks), not eq_ty *)
fun check_achieves_target (tyins, kdins, rkin) vty cty =
  if ge_ty (inst_rk_kd_ty rkin kdins tyins vty) cty then ()
  else raise ERR "ho_match_type" "higher-order type matching failed to achieve target type"

fun ho_match_type rkfixed kdavoids lconsts vty cty = let
(*
  val vty' = deep_beta_eta_ty vty
  val cty' = deep_beta_eta_ty cty
*)
  val (tyins, kdins, rkin) = ho_match_type0 true rkfixed kdavoids lconsts vty cty
  val _ = check_achieves_target (tyins, kdins, rkin) vty cty
in (tyins, kdins, rkin)
end

end (* local *)

(* We redefine the main type matching functions here to use higher order matching. *)

fun prim_kind_match_type pat ob ((tyS,tyId), (kdS,kdId), rkS) =
    let val tyfixed = HOLset.addList(empty_tyset, tyId)
        val (_,tyS',(kdS',kdId'),rkS') = ho_match_type1 false kdId tyfixed pat ob (tyS,[]) (rkS,(kdS,kdId))
     in ((tyS',tyId), (kdS',kdId'), rkS')
    end;


(*--------------------------------------------------------------------------------
    Matching (first order) of types, including sets of type variables to avoid binding.
    Does not attempt to match kinds or ranks, only checks they are equal.
    The general algorithm is higher order matching of types, modulo alpha-beta-eta conversion.
    This is used as a first try for matching, since faster than higher order matching.
    Throws HIGHER_ORDER if a more complex type is found in the pattern type.
 --------------------------------------------------------------------------------*)

exception HIGHER_ORDER
local
  fun MERR s = raise ERR "raw_match_type error" s
(*
  fun free (TyApp(Opr,Arg)) n = free Opr n andalso free Arg n
    | free (TyAll(_,Body)) n  = free Body (n+1)
    | free (TyExi(_,Body)) n  = free Body (n+1)
    | free (TyAbs(_,Body)) n  = free Body (n+1)
    | free _ _                = true
  fun bound_by_scope scoped M = if scoped then not (free M 0) else false
*)
(* for "ids" a HOLset: *)
  fun lookup x ids =
   let fun look [] = if HOLset.member(ids,x) then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
(* for "ids" a list:
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
*)
  val kdmatch = Kind.raw_match_kind
(*
  fun tymatch pat ob ((lctys,env,insts_homs),kdS,rkS) =
        let val insts_homs' = type_pmatch lctys env pat ob insts_homs
            val (rkS',kdS') = get_rank_kind_insts [] env (fst insts_homs') (rkS,kdS)
        in ((lctys,env,insts_homs'),kdS',rkS')
        end
  fun add_env mp (lctys,env,insts_homs) = (lctys,mp::env,insts_homs)
  fun drop_env ((lctys,env,insts_homs),kdS,rkS) = ((lctys,tl env,insts_homs),kdS,rkS)
  fun tasks (ty1::tys1) (ty2::tys2) s rst = (ty1,ty2,s)::tasks tys1 tys2 s rst
    | tasks [] [] s rst = rst
    | tasks _ _ _ _ = MERR "different arities of type operators"
*)
in
fun RM [] [] theta = theta
  | RM (pat::pats) (ob::obs) theta =
      RM0 (head_beta_eta_ty pat::pats) (head_beta_eta_ty ob::obs) theta
  | RM all others _       = MERR "different constructors"
(* RM0 can only be called with non-null type lists,
   the first elements of which are head-beta-eta reduced. *)
and RM0 ((TyApp (opr1,arg1))::ps) ((TyApp (opr2,arg2))::obs) tyS
      = let
        in case opr1 of
              Tyv _ => raise HIGHER_ORDER
            | _ => RM0 (opr1::arg1::ps) (opr2::arg2::obs) tyS
        end
  | RM0 ((TyCon(c1,kd1))::ps) ((TyCon(c2,kd2))::obs) (tyS (*,kdS,rkS*) )
      = RM ps obs
        (if c1 = c2 then
           let (* val (rkS',kdS') = kdmatch kd1 kd2 (rkS,kdS) *)
               val _ = if kd1=kd2 then () else raise HIGHER_ORDER
           in (tyS (*, kdS, rkS*) (* kdS', rkS' *) )
           end
         else
           let val n1 = KernelSig.id_toString c1
               val n2 = KernelSig.id_toString c2
           in MERR ("attempt to match different type constants: "
                    ^n1^" against "^n2)
           end
        )
  | RM0 ((v as Tyv(name,Kd))::ps) (ty::obs) ((S1 as ((tyS,tyId))) (*,kdS,rkS*) )
     = let (*val (rkS',kdS') = kdmatch Kd (kind_of ty) (rkS,kdS)*)
           val _ = if Kd=kind_of ty handle HOL_ERR _ => raise HIGHER_ORDER
                   then () else raise HIGHER_ORDER
            in
               RM ps obs
               ((case lookup v tyId tyS
                  of NONE => if v=ty then (* (tyS,v::tyId) *) (tyS,HOLset.add(tyId,v))
                                     else ((v |-> ty)::tyS,tyId)
                   | SOME ty' => if eq_ty ty' ty then S1
                                 else MERR ("double bind on type variable "^name))
                (*,kdS,rkS*) (*, kdS',rkS' *) )
            end
  | RM0 ((TyAll _)::_) _ _ = raise HIGHER_ORDER
  | RM0 ((TyExi _)::_) _ _ = raise HIGHER_ORDER
  | RM0 ((TyAbs _)::_) _ _ = raise HIGHER_ORDER
  | RM0 all others _       = MERR "different constructors"
end


fun raw_kind_match_type pat ob ((tyS,tyId), (kdS,kdId), (rkS,rkfixed)) =
    let val tyfixed = HOLset.addList(empty_tyset, tyId)
    in (* works fast for traditional HOL types; throws HIGHER_ORDER for others *)
      let val _ = if null kdS andalso rkS=0 then () else raise HIGHER_ORDER
          (* val (tyS',tyId') = RM [pat] [ob] (tyS,tyId) *)
          val (tyS',tyfixed') = RM [pat] [ob] (tyS,tyfixed)
          val tyId' = HOLset.listItems tyfixed'
      in ((tyS',tyId'), (kdS,kdId), (rkS,rkfixed))
      end
    handle HIGHER_ORDER => (* correct but slow: *)
      let
          val (_,tyS',(kdS',kdId'),(rkS',_)) =
                  ho_match_type1 true kdId tyfixed pat ob (tyS,[]) ((rkS,rkfixed),(kdS,kdId))
          val _ = check_achieves_target (tyS', kdS', rkS') pat ob
          val pat_vars' = map (inst_rank_kind rkS' kdS') (type_vars pat)
          val tyId' = Lib.subtract (Lib.union pat_vars' tyId) (map #redex tyS')
      in ((tyS',tyId'), (kdS',kdId'), (rkS',rkfixed))
      end
    end;

(* pure higher-order type matching: correct but slow:
fun raw_kind_match_type pat ob ((tyS,tyId), (kdS,kdId), rkS) =
    let val tyfixed = HOLset.addList(empty_tyset, tyId)
        val (_,tyS',(kdS',kdId'),(rkS',_)) =
                  ho_match_type1 true kdId tyfixed pat ob (tyS,[]) ((rkS,rkfixed),(kdS,kdId))
        val _ = check_achieves_target (tyS', kdS', rkS') pat ob
        val pat_vars' = map (inst_rank_kind rkS' kdS') (type_vars pat)
        val tyId' = Lib.subtract (Lib.union pat_vars' tyId) (map #redex tyS')
     in ((tyS',tyId'), (kdS',kdId'), (rkS',rkfixed))
    end;
*)

fun clean_subst ((tyS,_),(kdS,_),(rkS,_)) =
 let fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (if eq_ty residue redex then A else (redex |-> residue)::A) rst
 in (del [] tyS,kdS,rkS)
 end

fun kind_match_type pat ob =
      clean_subst (raw_kind_match_type pat ob (([],[]), ([],[]), (0,false)))

fun kind_match_types theta =
 let fun match ({redex,residue},matches) = raw_kind_match_type redex residue matches
 in clean_subst (List.foldr match (([],[]), ([],[]), (0,false)) theta)
 end

fun raw_match_type pat ob (tyS,tyId) =
    let val ((tyS',tyId'),(kdS',kdId'),(rkS',_)) =
              raw_kind_match_type pat ob ((tyS,tyId),([],[]),(0,false))
    in if null kdS' andalso null kdId' andalso rkS' = 0 then (tyS',tyId')
       else raise ERR "raw_match_type"
                  "kind and/or rank variable matches: use raw_kind_match_type instead"
    end;

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = fst (raw_match_type pat ob ([],[]))


(* Old matching:
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

End of old matching. *)


fun size acc tylist =
    case tylist of
      [] => acc
    | [] :: tys => size acc tys
    | (ty::tys1) :: tys2 => let
      in
        case ty of
          Tyv _ => size (1 + acc) (tys1 :: tys2)
        | TyCon _ => size (1 + acc) (tys1 :: tys2)
        | TyApp(ty1,ty2) => size (1 + acc) ((ty1 :: ty2 :: tys1) :: tys2)
        | TyAbs(_, body) => size (1 + acc) ((body :: tys1) :: tys2)
        | TyAll(_, body) => size (1 + acc) ((body :: tys1) :: tys2)
        | TyExi(_, body) => size (1 + acc) ((body :: tys1) :: tys2)
      end

fun type_size ty = size 0 [[ty]]

(* for testing:

val inst_rk_kd_ty = fn rkS => fn kdS => fn tyS => fn ty =>
  let val old = pure_type_subst tyS (inst_rank_kind rkS kdS ty)
      val new = inst_rk_kd_ty rkS kdS tyS ty
  in if old = new then new
     else (*if eq_ty old new
          then (WARN "inst_rk_kd_ty" ("new algorithm differs:\n"
                                      ^type_to_string old^"\n"
                                      ^"is alpha-beta-eta convertable to, but not equal to\n"
                                      ^type_to_string new^"\n");
                new)
          else *) raise ERR "inst_rk_kd_ty" ("new algorithm fails:\n"
                                      ^type_to_string old^"\n"
                                      ^"is not alpha-beta-eta convertable to\n"
                                      ^type_to_string new^"\n")
  end
*)

end (* struct *)
