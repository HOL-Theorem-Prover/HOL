structure Preterm :> Preterm =
struct

open Feedback Lib GrammarSpecials;

val ERR = mk_HOL_ERR "Preterm"
val ERRloc = mk_HOL_ERRloc "Preterm"

type pretype = Pretype.pretype
type kind = Kind.kind
type hol_type = Type.hol_type
type term = Term.term
type overinfo = {Name:string, Ty:pretype,
                 Info:Overload.overloaded_op_info, Locn:locn.locn}
fun tmlist_kdvs tlist =
  List.foldl (fn (t,acc) => Lib.union (Term.kind_vars_in_term t) acc) [] tlist
fun tmlist_tyvs tlist =
  List.foldl (fn (t,acc) => Lib.union (Term.type_vars_in_term t) acc) [] tlist

(* set_trace "debug_type_inference" must be between 0 and 4, inclusive;
     0 - no tracing of type inference
     1 - trace checking of higher order type inference
     2 - also trace checking of preterms
     3 - also trace checking of pretypes and type inference
     4 - also trace checking of prekinds and kind inference
     5 - also trace checking of preranks and rank inference
   Replaces "debug_preterm", "debug_pretype, "debug_prekind", and "debug_prerank".
*)

fun is_debug() = current_trace "debug_type_inference" >= 2;

val debug_overloading = ref false
val _ = register_btrace ("overload", debug_overloading)
fun over_print s = if !debug_overloading then Lib.say s else ()

val show_typecheck_errors = ref true
val _ = register_btrace ("show_typecheck_errors", show_typecheck_errors)
fun tcheck_say s = if !show_typecheck_errors then Lib.say s else ()

datatype tcheck_error =
         AppFail of term * term
       | NotUnivFail of term * hol_type
       | TyAppFail of term * hol_type
       | TyAppKindFail of term * hol_type
       | TyAppRankFail of term * hol_type
       | VarKindFail of string * hol_type
       | ConstKindFail of string * string * hol_type
       | ConstrainKindFail of term * hol_type
       | ConstrainFail of term * hol_type
       | OvlNoType of string * hol_type
       | TyAbsFail of hol_type * term

val last_tcerror : (tcheck_error * locn.locn) option ref = ref NONE

datatype preterm = Var   of {Name:string,  Ty:pretype, Locn:locn.locn}
                 | Const of {Name:string,  Thy:string, Ty:pretype, Locn:locn.locn}
                 | Overloaded of overinfo
                 | Comb   of {Rator:preterm, Rand:preterm, Locn:locn.locn}
                 | TyComb of {Rator:preterm, Rand:pretype, Locn:locn.locn}
                 | Abs    of {Bvar:preterm, Body:preterm, Locn:locn.locn}
                 | TyAbs  of {Bvar:pretype, Body:preterm, Locn:locn.locn}
                 | Constrained of {Ptm:preterm, Ty:pretype, Locn:locn.locn}
                 | Antiq  of {Tm:Term.term, Locn:locn.locn}
                 | Pattern of {Ptm:preterm, Locn:locn.locn}
              (* | HackHack of bool -> bool *)
              (* Because of the Locn fields, preterms should *not* be compared
                 with the built-in equality, but should use eq defined below.
                 To check this has been done everywhere, uncomment this constructor. *)

fun dest_var (Var record) = record
  | dest_var (Constrained {Ptm, ...}) = dest_var Ptm
  | dest_var _ = raise ERR "dest_var" "not a variable"

val op--> = Pretype.mk_fun_ty

(*
fun preterm_to_string (Var{Name,Ty,Locn}) = Name
  | preterm_to_string (Const{Name,Thy,Ty,Locn}) = Name
  | preterm_to_string (Constrained{Ptm,Ty,Locn}) = preterm_to_string Ptm
  | preterm_to_string (Pattern{Ptm,Locn}) = preterm_to_string Ptm
  | preterm_to_string _ = raise ERR "preterm_to_string" "undefined case"
*)

local
  open Pretype
in
fun ptype_of (Var{Ty, ...}) = Ty
  | ptype_of (Const{Ty, ...}) = Ty
  | ptype_of (Comb{Rator, ...}) = chase (ptype_of Rator)
  | ptype_of (TyComb{Rator, Rand, ...}) =
      let val rator_ty = ptype_of Rator
      in let val (Bvar,Body) = dest_univ_type rator_ty
             val Bvar1 = the_var_type Bvar
         in type_subst [Bvar1 |-> Rand] Body
         end
      end
  | ptype_of (Abs{Bvar,Body,...}) = ptype_of Bvar --> ptype_of Body
  | ptype_of (TyAbs{Bvar,Body,...}) = mk_univ_type(Bvar, ptype_of Body)
  | ptype_of (Constrained{Ty,...}) = Ty
  | ptype_of (Antiq{Tm,...}) = fromType (Term.type_of Tm)
  | ptype_of (Overloaded {Ty,...}) = Ty
  | ptype_of (Pattern{Ptm,...}) = ptype_of Ptm
end;

val bogus = locn.Loc_None
fun term_to_preterm kdavds avds t = let
  open optmonad
  infix >> >-
  fun gen avds ty = Pretype.rename_tv kdavds avds (Pretype.fromType ty)
  open HolKernel
  fun recurse avds t =
      case dest_term t of
        VAR(n,ty) => gen avds ty >- (fn pty =>
                     return (Var{Name = n, Locn = bogus, Ty = pty}))
      | CONST{Ty,Thy,Name} => gen avds Ty >- (fn pty =>
                              return (Const{Ty = pty, Name = Name,
                                            Thy = Thy, Locn = bogus}))
      | COMB(f,x) => recurse avds f >- (fn f' =>
                     recurse avds x >- (fn x' =>
                     return (Comb{Rand = x', Rator = f', Locn = bogus})))
      | TYCOMB(f,a) => recurse avds f >- (fn f' =>
                       gen avds a >- (fn a' =>
                       return (TyComb{Rator = f', Rand = a', Locn = bogus})))
      | LAMB(v,bod) => recurse avds v >- (fn v' =>
                       recurse avds bod >- (fn bod' =>
                       return (Abs{Body = bod', Bvar = v', Locn = bogus})))
      | TYLAMB(a,bod) => let val (s,_) = dest_var_type a
                             val avds' = s::avds
                         in gen avds' a >- (fn a' =>
                            recurse avds' bod >- (fn bod' =>
                            return (TyAbs{Bvar = a', Body = bod', Locn = bogus})))
                         end
in
  valOf (#2 (recurse avds t ([],[],[])))
end



(*---------------------------------------------------------------------------
     Read the location from a preterm.
 ---------------------------------------------------------------------------*)

fun locn (Var{Locn,...})         = Locn
  | locn (Const{Locn,...})       = Locn
  | locn (Overloaded{Locn,...})  = Locn
  | locn (Comb{Locn,...})        = Locn
  | locn (TyComb{Locn,...})      = Locn
  | locn (Abs{Locn,...})         = Locn
  | locn (TyAbs{Locn,...})       = Locn
  | locn (Constrained{Locn,...}) = Locn
  | locn (Antiq{Locn,...})       = Locn
  | locn (Pattern{Locn,...})     = Locn

fun pty_locn (Pretype.PT(_,locn)) = locn

(*---------------------------------------------------------------------------
     Location-ignoring equality for preterms.
 ---------------------------------------------------------------------------*)

val eq_type = Pretype.eq

fun eq_info {actual_ops=ops1, base_type=bty1, kdavoids=kdavds1, tyavoids=avds1}
            {actual_ops=ops2, base_type=bty2, kdavoids=kdavds2, tyavoids=avds2}
    = all2 Term.eq ops1 ops2 andalso Type.eq_ty bty1 bty2 andalso all2 equal kdavds1 kdavds2
                             andalso all2 Type.eq_ty avds1 avds2

fun eq (Var{Name=Name,Ty=Ty,...})                  (Var{Name=Name',Ty=Ty',...})                   = Name=Name' andalso eq_type Ty Ty'
  | eq (Const{Name=Name,Thy=Thy,Ty=Ty,...})        (Const{Name=Name',Thy=Thy',Ty=Ty',...})        = Name=Name' andalso Thy=Thy' andalso eq_type Ty Ty'
  | eq (Overloaded{Name=Name,Ty=Ty,Info=Info,...}) (Overloaded{Name=Name',Ty=Ty',Info=Info',...}) = Name=Name' andalso eq_type Ty Ty' andalso eq_info Info Info'
  | eq (Comb{Rator=Rator,Rand=Rand,...})           (Comb{Rator=Rator',Rand=Rand',...})            = eq Rator Rator' andalso eq Rand Rand'
  | eq (TyComb{Rator=Rator,Rand=Rand,...})         (TyComb{Rator=Rator',Rand=Rand',...})          = eq Rator Rator' andalso eq_type Rand Rand'
  | eq (Abs{Bvar=Bvar,Body=Body,...})              (Abs{Bvar=Bvar',Body=Body',...})               = eq Bvar Bvar' andalso eq Body Body'
  | eq (TyAbs{Bvar=Bvar,Body=Body,...})            (TyAbs{Bvar=Bvar',Body=Body',...})             = eq_type Bvar Bvar' andalso eq Body Body'
  | eq (Constrained{Ptm=Ptm,Ty=Ty,...})            (Constrained{Ptm=Ptm',Ty=Ty',...})             = eq Ptm Ptm' andalso Ty=Ty'
  | eq (Antiq{Tm=Tm,...})                          (Antiq{Tm=Tm',...})                            = Term.aconv Tm Tm'
  | eq (Pattern{Ptm,...})                          (Pattern{Ptm=Ptm',...})                        = eq Ptm Ptm'
  | eq  _                                           _                                             = false

fun rator (Comb{Rator, ...}) = Rator
  | rator _ = raise ERR "rator" "not a Comb"

fun strip_pcomb pt = let
  fun recurse acc t =
      case t of
        Comb{Rator, Rand, ...} => recurse (Rand::acc) Rator
      | _ => (t, acc)
in
  recurse [] pt
end


(* ----------------------------------------------------------------------

     Simple map from a preterm to a term. The argument "shr" maps from
     pretypes to types. Overloaded nodes cause failure if one is
     encountered, as Overloaded nodes should be gone by the time clean
     is called.

     shr takes a location for now, until Preterm has a location built-in.

     Handles the beta-conversion that occurs into Pattern terms.

   ---------------------------------------------------------------------- *)

val clean_type = Pretype.toType

fun clean shr = let
  open Term
  fun cl t =
      case t of
        Var{Name,Ty,Locn}            => mk_var(Name, shr Locn Ty)
      | Const{Name,Thy,Ty,Locn}      => mk_thy_const{Name=Name,
                                                     Thy=Thy,
                                                     Ty=shr Locn Ty}
      | Comb{Rator,Rand,...}         => let
          val (f, args0) = strip_pcomb t
          val args = map cl args0
        in
          case f of
            Pattern{Ptm,...} => let
              val t = cl Ptm
              val (bvs, _) = strip_abs t
              val inst = ListPair.map (fn (p,a) => p |-> a) (bvs, args)
              val result0 = funpow (length inst) (#2 o dest_abs) t
            in
              list_mk_comb(Term.subst inst result0,
                           List.drop(args, length inst))
            end
          | _ => list_mk_comb(cl f, args)
        end
      | TyComb{Rator,Rand,...}       => mk_tycomb(cl Rator,clean_type Rand)
      | Abs{Bvar,Body,...}           => mk_abs(cl Bvar, cl Body)
      | TyAbs{Bvar,Body,...}         => mk_tyabs(clean_type Bvar, cl Body)
      | Antiq{Tm,...}                => Tm
      | Constrained{Ptm,...}         => cl Ptm
      | Overloaded{Name,Ty,Locn,...} =>
          raise ERRloc "clean" Locn "Overload term remains"
      | Pattern {Ptm,...}            => cl Ptm
 in
  cl
 end

(*---------------------------------------------------------------------------*
 * The free variables of a preterm. Tail recursive (from Ken Larsen).        *
 *---------------------------------------------------------------------------*)

fun from_term_var tm = let val (s,ty) = Term.dest_var tm
                       in Var{Name=s, Ty=Pretype.fromType ty, Locn=locn.Loc_None}
                       end

fun the_var (v as Var{Name,Ty,Locn}) = v
  | the_var (Constrained{Ptm,Ty,Locn}) = the_var Ptm
  | the_var (Pattern{Ptm,Locn}) = the_var Ptm
  | the_var (Antiq{Tm,Locn}) = from_term_var Tm
  | the_var _ = raise ERR "the_var" "not a variable"

local fun FV (v as Var _) A k              = k (Lib.op_insert eq (the_var v) A)
        | FV (Comb{Rator,Rand,...}) A k    = FV Rator A (fn q => FV Rand q k)
        | FV (TyComb{Rator,Rand,...}) A k  = FV Rator A k
        | FV (Abs{Bvar,Body,...}) A k      = FV Body A (fn q => k (Lib.op_subtract eq q [the_var Bvar]))
        | FV (TyAbs{Bvar,Body,...}) A k    = FV Body A k
        | FV (Constrained{Ptm,Ty,...}) A k = FV Ptm A k
        | FV (Pattern{Ptm,...}) A k        = FV Ptm A k
        | FV (Antiq{Tm,...}) A k = k (Lib.op_union eq (map from_term_var (Term.free_vars Tm)) A)
        | FV _ A k = k A
in
fun free_vars tm = FV tm [] Lib.I
end;

val has_free_uvar = Pretype.has_free_uvar

fun kindVars ptm =  (* the prekind variable names in a preterm *)
  case ptm of
    Var{Ty,...}             => Pretype.kindvars Ty
  | Const{Ty,...}           => Pretype.kindvars Ty
  | Comb{Rator,Rand,...}    => Lib.union (kindVars Rator) (kindVars Rand)
  | TyComb{Rator,Rand,...}  => Lib.union (kindVars Rator) (Pretype.kindvars Rand)
  | Abs{Bvar,Body,...}      => Lib.union (kindVars Bvar) (kindVars Body)
  | TyAbs{Bvar,Body,...}    => Lib.union (Pretype.kindvars Bvar) (kindVars Body)
  | Antiq{Tm,...}           => map (#1 o Kind.dest_var_kind) (Term.kind_vars_in_term Tm)
  | Constrained{Ptm,Ty,...} => Lib.union (kindVars Ptm) (Pretype.kindvars Ty)
  | Pattern{Ptm,...}        => kindVars Ptm
  | Overloaded _            => raise Fail "Preterm.kindVars: applied to Overloaded";

fun tyVars ptm =  (* the pretype variable names in a preterm *)
  case ptm of
    Var{Ty,...}             => Pretype.tyvars Ty
  | Const{Ty,...}           => Pretype.tyvars Ty
  | Comb{Rator,Rand,...}    => Lib.union (tyVars Rator) (tyVars Rand)
  | TyComb{Rator,Rand,...}  => Lib.union (tyVars Rator) (Pretype.tyvars Rand)
  | Abs{Bvar,Body,...}      => Lib.union (tyVars Bvar) (tyVars Body)
  | TyAbs{Bvar,Body,...}    => Lib.union (Pretype.tyvars Bvar) (tyVars Body)
  | Antiq{Tm,...}           => map (#1 o Type.dest_var_type) (Term.type_vars_in_term Tm)
  | Constrained{Ptm,Ty,...} => Lib.union (tyVars Ptm) (Pretype.tyvars Ty)
  | Pattern{Ptm,...}        => tyVars Ptm
  | Overloaded _            => raise Fail "Preterm.tyVars: applied to Overloaded";

(*-----------------------------------------------------------------------------*
 * The free type variables of a lambda term. Tail recursive (from Ken Larsen). *
 *-----------------------------------------------------------------------------*)

local val union = Lib.op_union Pretype.eq
      val subtract = Lib.op_set_diff Pretype.eq
      val type_vars = Pretype.type_vars
      val the_var_type = Pretype.the_var_type
      fun tyV (Var{Ty,...}) k             = k (type_vars Ty)
        | tyV (Const{Ty,...}) k           = k (type_vars Ty)
        | tyV (Comb{Rator,Rand,...}) k    = tyV Rand (fn q1 =>
                                            tyV Rator(fn q2 => k (union q2 q1)))
        | tyV (TyComb{Rator,Rand,...}) k  = tyV Rator (fn q  =>
                                            k (union q (type_vars Rand)))
        | tyV (Abs{Bvar,Body,...}) k      = tyV Body (fn q1 =>
                                            tyV Bvar (fn q2 => k (union q2 q1)))
        | tyV (TyAbs{Bvar,Body,...}) k    = tyV Body (fn q => k (subtract q [the_var_type Bvar]))
        | tyV (Antiq{Tm,...}) k           = map Pretype.fromType (Term.type_vars_in_term Tm)
        | tyV (Constrained{Ptm,Ty,...}) k = tyV Ptm (fn q =>
                                            k (union q (type_vars Ty)))
        | tyV (Pattern{Ptm,...}) k        = tyV Ptm k
        | tyV (Overloaded {Ty,...}) k     = k (type_vars Ty)
      fun tyVs (t::ts) k           = tyV t (fn q1 =>
                                     tyVs ts (fn q2 => k (union q2 q1)))
        | tyVs [] k                = k []
in
fun type_vars_in_term tm = tyV tm Lib.I
fun type_vars_in_terml tms = tyVs tms Lib.I
end;


local val deepty = Pretype.deep_beta_eta_ty
      fun deep (Var{Name,Ty,Locn})        = Var{Name=Name,Ty=deepty Ty,Locn=Locn}
        | deep (Const{Thy,Name,Ty,Locn})  = Const{Thy=Thy,Name=Name,Ty=deepty Ty,Locn=Locn}
        | deep (Comb{Rator,Rand,Locn})    = Comb{Rator=deep Rator,Rand=deep Rand,Locn=Locn}
        | deep (TyComb{Rator,Rand,Locn})  = TyComb{Rator=deep Rator,Rand=deepty Rand,Locn=Locn}
        | deep (Abs{Bvar,Body,Locn})      = Abs{Bvar=deep Bvar,Body=deep Body,Locn=Locn}
        | deep (TyAbs{Bvar,Body,Locn})    = TyAbs{Bvar=deepty Bvar,Body=deep Body,Locn=Locn}
        | deep (Antiq{Tm,Locn})           = Antiq{Tm=Term.beta_eta_conv_ty_in_term Tm,Locn=Locn}
        | deep (Constrained{Ptm,Ty,Locn}) = Constrained{Ptm=deep Ptm,Ty=deepty Ty,Locn=Locn}
        | deep (Pattern{Ptm,Locn})        = Pattern{Ptm=deep Ptm,Locn=Locn}
        | deep (Overloaded{Name,Ty,Info,Locn}) = Overloaded{Name=Name,Ty=deepty Ty,Info=Info,Locn=Locn}
      fun deeps (t::ts)           = deep t :: deeps ts
        | deeps []                = []
in
val beta_eta_conv_ty_in_term = deep
val beta_eta_conv_ty_in_terml = deeps
end;


local
open Pretype
fun toTypePair {redex,residue} = {redex=toType redex, residue=toType residue}
fun toTypeSubst theta = map toTypePair theta
fun residue_tyvs theta = flatten (map (type_vars o #residue) theta)
fun remove v theta = filter (fn {redex,residue} => not (eq redex v)) theta
in
fun inst [] tm = tm
  | inst theta tm =
    let fun inst0 (Const{Name,Thy,Ty,Locn}) =
              Const{Name=Name, Thy=Thy, Ty=type_subst theta Ty, Locn=Locn}
          | inst0 (Var{Name,Ty,Locn}) =
              Var{Name=Name, Ty=type_subst theta Ty, Locn=Locn}
          | inst0 (Comb{Rator,Rand,Locn}) =
              Comb{Rator=inst0 Rator, Rand=inst0 Rand, Locn=Locn}
          | inst0 (TyComb{Rator,Rand,Locn}) =
              TyComb{Rator=inst0 Rator, Rand=type_subst theta Rand, Locn=Locn}
          | inst0 (Abs{Bvar,Body,Locn}) =
              Abs{Bvar=inst0 Bvar, Body=inst0 Body, Locn=Locn}
          | inst0 (tm as TyAbs{Bvar,Body,Locn}) =
              let val Bvar0 = the_var_type Bvar
                  val theta' = remove Bvar0 theta
                  val ctvs = residue_tyvs theta'
              in if op_mem eq Bvar0 ctvs then
                    let val bodytvs = type_vars_in_term tm
                        val Bvar' = variant_type (op_union eq ctvs bodytvs) Bvar0
                        val phi = (Bvar0 |-> Bvar') :: theta'
                    in TyAbs{Bvar=type_subst phi Bvar, Body=inst phi Body, Locn=Locn}
                    end
                 else TyAbs{Bvar=Bvar, Body=inst theta' Body, Locn=Locn}
              end
          | inst0 (Antiq{Tm,Locn}) =
              Antiq{Tm=Term.inst (toTypeSubst theta) Tm, Locn=Locn}
          | inst0 (Constrained{Ptm,Ty,Locn}) =
              Constrained{Ptm=inst0 Ptm, Ty=type_subst theta Ty, Locn=Locn}
          | inst0 (Pattern{Ptm,Locn}) =
              Pattern{Ptm=inst0 Ptm, Locn=Locn}
          | inst0 tm = tm
    in
      inst0 tm
    end
end;

(* ---------------------------------------------------------------------- *)
(* "remove_case_magic", located here to be called within "to_term":       *)
(* This does not traverse into the body of type abstractions, as this     *)
(* function is called separately within "to_term" for type abstractions.  *)
(* This is because "mk_tyabs" tests the free variables of the body, which *)
(* may change under "remove_case_magic".                                  *)
(* ---------------------------------------------------------------------- *)

local

(* ---------------------------------------------------------------------- *)
(* function to do the equivalent of strip_conj, but where the "conj" is   *)
(* the magic binary operator bool$<GrammarSpecials.case_split_special     *)
(* ---------------------------------------------------------------------- *)

open HolKernel
fun dest_binop n c t = let
  val (f,args) = strip_comb t
  val {Name,Thy,...} = dest_thy_const f
      handle HOL_ERR _ =>
             raise ERR ("dest_case"^n) ("Not a "^n^" term")
  val _ = (Name = c andalso Thy = "bool") orelse
          raise ERR ("dest_case"^n) ("Not a "^n^" term")
  val _ = length args = 2 orelse
          raise ERR ("dest_case_"^n) ("case "^n^" 'op' with bad # of args")
in
  (hd args, hd (tl args))
end

val dest_case_split = dest_binop "split" case_split_special
val dest_case_arrow = dest_binop "arrow" case_arrow_special

fun strip_splits t0 = let
  fun trav acc t = let
    val (l,r) = dest_case_split t
  in
    trav (trav acc r) l
  end handle HOL_ERR _ => t::acc
in
  trav [] t0
end

fun mk_conj(t1, t2) = let
  val c = mk_thy_const{Name = "/\\", Thy = "bool",
                       Ty = Type.bool --> Type.bool --> Type.bool}
in
  mk_comb(mk_comb(c,t1), t2)
end

fun list_mk_conj [] = raise ERR "list_mk_conj" "empty list"
  | list_mk_conj [h] = h
  | list_mk_conj (h::t) = mk_conj(h, list_mk_conj t)
fun mk_eq(t1, t2) = let
  val ty = type_of t1
  val c = mk_thy_const{Name = "=", Thy = "min", Ty = ty --> ty --> Type.bool}
in
  mk_comb(mk_comb(c,t1),t2)
end

datatype rcm_action = Input of term
                    | Ab of term * term
                    | Cmb of int * term
                    | TyAb of term
                    | TyCmb of hol_type list * term
datatype rcm_out = Ch of term | Unch of term
fun is_unch (Unch _) = true | is_unch _ = false
fun dest_out (Ch t) = t | dest_out (Unch t) = t
fun Pprefix P list = let
  fun recurse pfx rest =
      case rest of
        [] => (list, [])
      | h::t => if P h then recurse (h::pfx) t
                else (List.rev pfx, rest)
in
  recurse [] list
end

fun recomb (outf, outargs, orig) = let
  fun lmk(base, args) = List.foldl (fn (out,t) => mk_comb(t,dest_out out))
                                   base args
in
  case outf of
    Ch f => Ch (lmk(f, outargs))
  | Unch f => let
      val (_, badargs) = Pprefix is_unch outargs
    in
      if null badargs then Unch orig
      else Ch (lmk(funpow (length badargs) rator orig, badargs))
    end
end

fun remove_case_magic0 tm0 = let
  fun traverse acc actions =
      case actions of
        [] => dest_out (hd acc)
      | act :: rest => let
        in
          case act of
            Input t => let
            in
              if is_abs t then let
                  val (v,body) = dest_abs t
                in
                  traverse acc (Input body :: Ab (v,t) :: rest)
                end
              else if is_comb t then let
                  val (f,args) = strip_comb t
                  val in_args = map Input args
                in
                  traverse acc (in_args @
                                [Input f, Cmb(length args, t)] @ rest)
                end
              else if is_tyabs t then let
                  val (v,body) = dest_tyabs t
                in
                  traverse acc (TyAb t :: rest)
                end
              else if is_tycomb t then let
                  val (f,args) = strip_tycomb t
                in
                  traverse acc ([Input f, TyCmb(args, t)] @ rest)
                end
              else
                traverse (Unch t::acc) rest
            end
          | Ab (v,orig) => let
            in
              case acc of
                Ch bod' :: acc0 => traverse (Ch (mk_abs(v,bod'))::acc0)
                                            rest
              | Unch _ :: acc0 => traverse (Unch orig :: acc0) rest
              | [] => raise Fail "Preterm.rcm: inv failed!"
            end
          | TyAb orig => let
            in traverse (Unch orig :: acc) rest
            end
          | TyCmb(tyargs, orig) => let
            in
              case acc of
                Ch f' :: acc0 => traverse (Ch (list_mk_tycomb(f',tyargs))::acc0)
                                            rest
              | Unch _ :: acc0 => traverse (Unch orig :: acc0) rest
              | [] => raise Fail "Preterm.rcm: inv failed!"
            end (* TyCmb *)
          | Cmb(arglen, orig) => let
              val out_f = hd acc
              val f = dest_out out_f
              val acc0 = tl acc
              val acc_base = List.drop(acc0, arglen)
              val out_args = List.rev (List.take(acc0, arglen))
              val args = map dest_out out_args
              val newt = let
                val {Name,Thy,Ty} = dest_thy_const f
                    handle HOL_ERR _ => {Name = "", Thy = "", Ty = alpha}
              in
                if Name = case_special andalso Thy = "bool" then let
                    val _ = length args >= 2 orelse
                            raise ERR "remove_case_magic"
                                      "case constant has wrong # of args"
                    val split_on_t = hd args
                    val cases = strip_splits (hd (tl args))
                    val patbody_pairs = map dest_case_arrow cases
                        handle HOL_ERR _ =>
                               raise ERR "remove_case_magic"
                                         ("Case expression has invalid syntax \
                                          \where there should be arrows")
                    val split_on_t_ty = type_of split_on_t
                    val result_ty =
                        type_of (list_mk_comb(f, List.take(args,2)))
                    val fakef = genvar (split_on_t_ty --> result_ty)
                    val fake_eqns =
                        list_mk_conj(map (fn (l,r) =>
                                             mk_eq(mk_comb(fakef, l), r))
                                         patbody_pairs)
                    val functional =
                        GrammarSpecials.compile_pattern_match fake_eqns
                    val func = snd (dest_abs functional)
                    val (v,case_t0) = dest_abs func
                    val case_t = subst [v |-> split_on_t] case_t0
                  in
                    Ch (list_mk_comb(case_t, tl (tl args)))
                  end
                else
                  recomb(out_f, out_args, orig)
              end (* newt *)
            in
              traverse (newt::acc_base) rest
            end (* Cmb *)
        end (* act :: rest *) (* end traverse *)
in
  traverse [] [Input tm0]
end

in

fun remove_case_magic tm =
    if GrammarSpecials.case_initialised() then remove_case_magic0 tm
    else tm

end; (* local *)


(*---------------------------------------------------------------------------*
 *    Converting preterms to strings, for printing.                          *
 *---------------------------------------------------------------------------*)
local open Prerank Prekind Pretype Portable
in
fun default_kind (PK(Typekind Zerorank,_)) = true
  | default_kind _ = false
fun pp_if_prekind add_string pp_prekind kd =
      if default_kind kd then ()
      else (add_string ": ";
            pp_prekind kd)
fun kind_to_string (PK(Typekind Zerorank,_)) = ""
  | kind_to_string kd = ": " ^ prekind_to_string kd
fun default_rank Zerorank = true
  | default_rank _ = false
fun add_rank_string Zerorank = ""
  | add_rank_string rk = ":" ^ prerank_to_string rk
fun pp_if_prerank add_string pp_prerank rk =
      if current_trace "ranks" + (if default_rank rk then 0 else 1) < 3 then ()
      else (add_string " : ";
            pp_prerank rk)
fun pp_if_prekind_rank add_string pp_prekind pp_prerank kd =
  let val pr_kd = current_trace "kinds" + (if default_kind kd then 0 else 1) > 1
      val rk = Prekind.prank_of kd handle Fail _ => Prerank.new_uvar()
      val pr_rk = if pr_kd then false
                  else current_trace "ranks" + (if default_rank rk then 0 else 1) > 2
  in
      if not pr_kd then ()
      else (add_string ": ";
            pp_prekind kd);
      if not pr_rk then ()
      else (add_string ":<=";
            pp_prerank rk)
  end
fun print_prerank rk = print (prerank_to_string rk ^ "; ")
fun print_prekind kd = print (prekind_to_string kd ^ "; ")
end

datatype pp_pty_state = none | left | right | uvar

fun pp_preterm pps tm =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val checkref = Portable.ref_to_int
     val pp_prekind = Prekind.pp_prekind pps
     val pp_prerank = Prerank.pp_prerank pps
     val pp_if_prekind = pp_if_prekind add_string pp_prekind
     val pp_if_prerank = pp_if_prerank add_string pp_prerank
     val pp_if_prekind_rank = pp_if_prekind_rank add_string pp_prekind pp_prerank
     val pp_pretype = Pretype.pp_pretype pps
     fun pppreterm tm =
       case tm of
           Var{Name,Ty,...} => (add_string "(";
                                begin_block INCONSISTENT 0;
                                add_string (Name^":");
                                add_break(1,0);
                                pp_pretype Ty;
                                end_block();
                                add_string ")")
         | Const {Thy, Name, Ty, ...} => (if current_trace "ranks" < 3 then () else add_string "[";
                                          if Thy = "bool" orelse Thy = "min" then
                                              add_string Name
                                            else add_string (Thy ^ "$" ^ Name);
                                            if current_trace "ranks" < 3 then ()
                                                 else (add_string ":"; pp_pretype Ty);
                                            pp_if_prerank (Pretype.prank_of_type Ty);
                                            if current_trace "ranks" < 3 then () else add_string "]" )
         | Comb{Rator, Rand, ...} => (add_string "(";
                               begin_block INCONSISTENT 0;
                               pppreterm Rator;
                               add_break(1,0);
                               pppreterm Rand;
                               end_block();
                               add_string ")")
         | TyComb{Rator, Rand, ...} => (add_string "(";
                               begin_block INCONSISTENT 0;
                               pppreterm Rator;
                               add_break(1,0);
                               add_string "[:";
                               pp_pretype Rand;
                               add_string ":]";
                               end_block();
                               add_string ")")
         | Abs{Bvar,Body,...} => (add_string "\\";
                               pppreterm Bvar;
                               add_string ".";
                               add_break(1,0);
                               begin_block INCONSISTENT 0;
                               pppreterm Body;
                               end_block())
         | TyAbs{Bvar,Body,...} => (add_string "\\:";
                               pp_pretype Bvar;
                               add_string ".";
                               add_break(1,0);
                               begin_block INCONSISTENT 0;
                               pppreterm Body;
                               end_block())
         | Constrained{Ptm,Ty,...} => (add_string "(";
                               begin_block INCONSISTENT 0;
                               pppreterm Ptm;
                               add_string " :";
                               add_break(1,2);
                               pp_pretype Ty;
                               end_block();
                               add_string ")")
         | Overloaded {Name,Ty,...} => (add_string "<";
                               begin_block INCONSISTENT 0;
                               add_string ("overloaded " ^ Name ^ ":");
                               add_break(1,2);
                               pp_pretype Ty;
                               end_block();
                               add_string ">")
         | Antiq {Tm,...} => add_string "<antiq>"
         | Pattern{Ptm,...} => pppreterm Ptm
 in
   begin_block INCONSISTENT 0;
   pppreterm tm;
   end_block()
 end;

val preterm_to_string = Portable.pp_to_string 80 pp_preterm
fun print_preterm tm = Portable.output(Portable.std_out, preterm_to_string tm);

fun pp_preterms pps tms =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_preterm = pp_preterm pps
     fun pppreterms0 [] = ()
       | pppreterms0 (tm::tms) = (add_string ",";
                                  add_break(0,0);
                                  pp_preterm tm;
                                  pppreterms0 tms)
     fun pppreterms [] = ()
       | pppreterms (tm::tms) =  (begin_block INCONSISTENT 0;
                                  pp_preterm tm;
                                  pppreterms0 tms;
                                  end_block())
 in
   add_string "[";
   pppreterms tms;
   add_string "]"
 end;

val preterms_to_string = Portable.pp_to_string 80 pp_preterms
fun print_preterms tms = Portable.output(Portable.std_out, preterms_to_string tms);

val debug_term = Thm.debug_term
fun debug_terms tms =
 let fun debug_terms0 [] = ()
       | debug_terms0 (tm::tms) = (print ", ";
                                   debug_term tm;
                                   debug_terms0 tms)
     fun debug_terms [] = ()
       | debug_terms (tm::tms)  = (debug_term tm;
                                   debug_terms0 tms)
 in
   print "[";
   debug_terms tms;
   print "]"
 end;

val debug_type = Thm.debug_type
fun debug_types tys =
 let fun debug_types0 [] = ()
       | debug_types0 (ty::tys) = (print ", ";
                                   debug_type ty;
                                   debug_types0 tys)
     fun debug_types [] = ()
       | debug_types (ty::tys)  = (debug_type ty;
                                   debug_types0 tys)
 in
   print "[";
   debug_types tys;
   print "]"
 end;

fun debug_kind kd = Thm.debug_kind kd
fun debug_kinds kds =
 let fun debug_kinds0 [] = ()
       | debug_kinds0 (kd::kds) = (print ", ";
                                   debug_kind kd;
                                   debug_kinds0 kds)
     fun debug_kinds1 [] = ()
       | debug_kinds1 (kd::kds) = (debug_kind kd;
                                   debug_kinds0 kds)
 in
   print "[";
   debug_kinds1 kds;
   print "]"
 end;


(*---------------------------------------------------------------------------
    Translate a preterm to a term. Will "guess type variables"
    (assign names to type variables created during type inference),
    if a flag is set. No "Overloaded" nodes are allowed in the preterm:
    overloading resolution should already have gotten rid of them.
 ---------------------------------------------------------------------------*)

(* --------------------------------------------------------------------------------- *)
(* "to_term" has been modified to cause the body of a type abstraction (TyAbs) to    *)
(* remove the case magic from its body before trying to create the type abstraction. *)
(* Because of the check that this construction requires, that there are no free      *)
(* variables involving the type variable being bound, such case magic removal is     *)
(* mandatory, as it changes the free variable set.                                   *)
(* --------------------------------------------------------------------------------- *)

val _ =
    register_btrace ("notify type variable guesses",
                     Globals.notify_on_tyvar_guess)

fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained{Ptm,...}) = is_atom Ptm
(*| is_atom (Pattern{Ptm,...}) = is_atom Ptm*)
  | is_atom (Overloaded _) = true
  | is_atom (t as Comb{Rator,Rand,...}) = false
  | is_atom t = false

fun to_term pfns tm =
    if !Globals.guessing_tyvars then let
  fun default_kdprinter x = "<kind>"
  fun default_typrinter x = "<hol_type>"
  fun default_tmprinter x = "<term>"
  val (ptm, pty, pkd) =
      case pfns
       of SOME (x,y,z) =>
          let val kdprint = z
              fun typrint ty =
                  if Type.is_con_type ty
                  then (y ty ^ " :" ^ z (Type.kind_of ty))
                  else y ty
              fun tmprint tm = x tm
                (*if Term.is_const tm
                  then (x tm ^ " " ^ y (Term.type_of tm))
                  else x tm*)
          in
            (tmprint, typrint, kdprint)
          end
        | NONE => (default_tmprinter, default_typrinter, default_kdprinter)

        fun const_error_report (r as {Name, Thy, Ty, Locn}) real_type (e:exn) =
          let
          in raise e
          end
          handle (e as Feedback.HOL_ERR{message,...}) =>
          let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val ty_locn = pty_locn Ty
              val prim = Term.prim_mk_const {Thy=Thy, Name=Name}
              val prim_ty = Term.type_of prim
              val message =
                  String.concat
                      [
                       "\nType inference failure: the constant ",
                       Thy^"$"^Name,
                       "\n\n"^locn.toString Locn^"\n\n",

                       "is inferred to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "but this is not an instance of the constant's primitive type:\n\n",
                        pty prim_ty, "\n\n"]
            in
              Feedback.set_trace "kinds" tmp;
              Feedback.set_trace "ranks" tmp2;
              tcheck_say message;
              last_tcerror := SOME (ConstKindFail(Name, Thy, real_type), ty_locn);
              raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
            end

        fun comb_error_report (tm, f, args) (f',args') (e:exn) =
          let
          in raise e
          end
          handle (e as Feedback.HOL_ERR{message,...}) =>
          let val tmp = !Globals.show_types
              val _   = Globals.show_types := true
(*
              val show_kinds = Feedback.get_tracefn "kinds"
              val tmp1 = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
*)
              fun ratorn 0 t = t
                | ratorn n t = ratorn (n-1) (rator t)
              fun try_combs f' ((arg,arg')::rest) =
                  (try_combs (Term.mk_comb(f', arg')) rest
                   handle e as HOL_ERR _ =>
                   (ratorn (length rest + 1) tm, f', arg, arg'))
                | try_combs f' [] = raise ERR "try_combs" "impossible"
              val (Rator, Rator', Rand, Rand') = try_combs f' (zip args args')
              val message =
                  String.concat
                      [
                       "\nType inference failure: unable to infer a type \
                       \for the application of\n\n",
                       ptm Rator',
                       "\n\n"^locn.toString (locn Rator)^"\n\n",
                       if (is_atom Rator) then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rator') ^ "\n\n"),

                       "to\n\n",
                       ptm Rand',
                       "\n\n"^locn.toString (locn Rand)^"\n\n",

                       if (is_atom Rand) then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rand') ^ "\n\n"),

                       "unification failure message: ", message, "\n"]
            in
              Globals.show_types := tmp;
(*
              Feedback.set_trace "kinds" tmp1;
              Feedback.set_trace "ranks" tmp2;
*)
              tcheck_say message;
              last_tcerror := SOME (AppFail(Rator', Rand'), locn tm);
              raise ERRloc"typecheck" (locn tm (* arbitrary *)) message
            end

        fun tyabs_error_report (r as {Bvar, Body, Locn}) (Bvar_ty,Body_tm) e =
          let
          in raise e
          end
          handle (e as Feedback.HOL_ERR _) =>
          let val tmp1 = Feedback.current_trace "kinds"
              val _   = Feedback.set_trace "kinds" 1
              val tmp = !Globals.show_types
              val _   = Globals.show_types := true
              val tyabs_tm = TyAbs r
              val ty_locn = pty_locn Bvar
              val fpvs = free_vars Body
              val fvs = Term.free_vars Body_tm
              val fv = first (fn v => mem Bvar_ty (Type.type_vars (Term.type_of v))) fvs
                         handle e' as HOL_ERR{origin_structure="Lib",
                                              origin_function="first",message} =>
                           (Globals.show_types := tmp; Feedback.set_trace "kinds" tmp1;
                            Raise e)
              val fv = Term.beta_eta_conv_ty_in_term fv
              val fpv = first (eq (from_term_var fv)) fpvs
                         handle e' as HOL_ERR{origin_structure="Lib",
                                              origin_function="first",message} =>
                           (Globals.show_types := tmp; Feedback.set_trace "kinds" tmp1;
                            Raise e)
              val message =
                  String.concat
                      [
                       "\nType variable scoping failure: the abstraction ",
                       "by the type variable\n\n",
                       pty Bvar_ty,
                       "\n\n"^locn.toString ty_locn^"\n\n",
                       "of the term\n\n",
                       ptm Body_tm,
                       "\n\n"^locn.toString Locn^"\n\n",
                       "contains the free term variable\n\n",
                       ptm fv,
                       "\n\n"^locn.toString (locn fpv)^"\n\n",
                       "whose type contains freely the type variable being abstracted,\n\n",
                       pty Bvar_ty,
                       "\n\n"^locn.toString ty_locn^"\n\n"]
          in
            Globals.show_types := tmp;
            Feedback.set_trace "kinds" tmp1;
            tcheck_say message;
            last_tcerror := SOME (TyAbsFail(Bvar_ty,Body_tm), Locn);
            raise ERRloc"typecheck" Locn message
          end

        fun cleanup tm = let
          open optmonad
          infix >> >-
          val clean = (*Type.vacuum o*) Pretype.clean o Pretype.remove_made_links
(*
          fun clean ty = (print "\ncleaning type:\n  ";
                          set_trace "ranks" 1;
                          Pretype.print_pretype ty; print "\n";
                          let val ty' = Pretype.clean (Pretype.remove_made_links ty)
                          in print "to:\n  ";
                             Pretype.print_pretype ty; print "\n";
                             Thm.debug_type ty'; print "\n";
                             ty'
                          end)
*)
          fun prepare Ty =
              let 
                  val tyf = if Pretype.do_beta_conv_types()
                            then Pretype.deep_beta_eta_ty
                            else I
              in Pretype.replace_null_links Ty >- (fn _ => return (tyf Ty))
              end
(*
          val _ = if not (is_debug()) then () else
                    (print "\nto_term:\n"; set_trace "ranks" 3; print_preterm tm; print "\n")
*)
        in
          case tm of
            Var{Name,Ty,...} => prepare Ty >- (fn Ty' =>
                                return (Term.mk_var(Name, clean Ty')))
            (* in this Var case, and in the Const case below, have to use
               "... >- (fn _ => ..." rather than the >> 'equivalent' because
               the former ensures that the references in Ty get updated
               before the call to clean occurs. *)
          | Const(r as {Name,Thy,Ty,...}) =>
                (* the creation of a constant may introduce beta-redexes in its type;
                   these will be reduced here. *)
                prepare Ty >- (fn Ty' =>
                let val cTy' = clean Ty'
                in return (Term.mk_thy_const{Name=Name, Thy=Thy, Ty=cTy'})
                             handle e as HOL_ERR _ => const_error_report r cTy' e
                end)
(*
                                if not (is_debug()) then raise e else
                                (print ("ERROR in cleanup(Const) of "^Thy^"$"^Name^":\n");
                                 set_trace "kinds" 2;
                                 Pretype.print_pretype Ty'; print "\n";
                                 print "Const type: "; debug_type (clean Ty'); print "\n";
                                 Raise e)))
*)
          | Comb{Rator, Rand, Locn} => let
              val (f, args) = strip_pcomb tm
              open Term
            in
              case f of
                Pattern{Ptm,...} => let
                  fun doit f_t args = let
                    val (bvs, _) = strip_abs f_t
                    val inst = ListPair.map Lib.|-> (bvs, args)
                    val res0 = funpow (length inst) (#2 o dest_abs) f_t
                  in
                    list_mk_comb(Term.subst inst res0,
                                 List.drop(args, length inst))
                             handle e as HOL_ERR _ => if not (is_debug()) then raise e else
                                (print "ERROR in cleanup(Pattern):\n";
                                 set_trace "ranks" 3;
                                 print_preterm tm; print "\n";
                                 print "Oper term: "; debug_term f_t; print "\n";
                                 print "Arg terms: "; debug_terms args; print "\n";
                                 print "Oper type: "; debug_type (type_of f_t); print "\n";
                                 print "Arg types: "; debug_types (map type_of args); print "\n";
                                 Raise e)
                  end
                in
                  cleanup Ptm >- (fn f =>
                  mmap cleanup args >- (fn args' =>
                  return (doit f args')))
                end
              | _ => cleanup f >- (fn f' =>
                     mmap cleanup args >- (fn args' =>
                     return ((list_mk_comb(f', args'))
                             handle e as HOL_ERR _ => if not (is_debug()) then raise e else
                                (let fun strip_fun_type ty = let val (d,r) = Type.dom_rng ty
                                                                 val (ds,base) = strip_fun_type r
                                                             in (d::ds,base)
                                                             end handle HOL_ERR _ => ([],ty)
                                     val (f_arg_tys,_) = strip_fun_type (type_of f')
(*
                                     val arg1 = el 1 args'
                                     val (o_mapf_tm,unit_tycmb) = dest_comb arg1
                                     val (o_tm,mapf_tm) = dest_comb o_mapf_tm
                                     val unit_tycmb_ty = type_of unit_tycmb
                                     val _ = (print "unit_tycmb_ty: "; debug_type unit_tycmb_ty; print "\n")
                                     val bad_a = fst(Type.dom_rng unit_tycmb_ty)
                                     val (unit_tm,alpha_arg) = dest_tycomb unit_tycmb
                                     val _ = (print "alpha_arg: "; debug_type alpha_arg; print "\n")
                                     val unit_ty = type_of unit_tm
                                     val _ = (print "unit_ty: "; debug_type unit_ty; print "\n")
*)
                                 in
                                 print "ERROR in cleanup:\n";
                                 set_trace "ranks" 3;
                                 print_preterm f; print "\n";
                                 debug_term f'; print " "; debug_terms args'; print "\n";
                                 print "Oper type: "; debug_type (type_of f'); print "\n";
                                 print "Oper dtypes: "; debug_types f_arg_tys; print "\n";
                                 print "Arg types: "; debug_types (map type_of args'); print "\n";
                                 print "Oper kind: "; print_prekind (Pretype.pkind_of(ptype_of f)); print "\n";
                                 print "Oper dkinds: "; debug_kinds (map Type.kind_of f_arg_tys); print "\n";
                                 print "Arg  dkinds: "; debug_kinds (map (Type.kind_of o type_of) args'); print "\n";
                                 print "Arg kinds: "; (map (print_prekind o Pretype.pkind_of o ptype_of) args); print "\n";
                                 print "Oper rank: "; print_prerank (Pretype.prank_of_type(ptype_of f)); print "\n";
                                 print "Arg ranks: "; (map (print_prerank o Pretype.prank_of_type o ptype_of) args); print "\n";
                                 Raise e
                                 end))
                             handle e as HOL_ERR _ => comb_error_report (tm,f,args) (f',args') e
                     ))
            end
          | TyComb{Rator, Rand,...} => cleanup Rator >- (fn Rator'
                                    => prepare Rand >- (fn Rand'
                                    => return (Term.mk_tycomb(Rator', clean Rand'))))
          | Abs{Bvar, Body,...} => cleanup Bvar >- (fn Bvar'
                                => cleanup Body >- (fn Body'
                                => return (Term.mk_abs(Bvar', Body'))))
          | TyAbs(r as {Bvar, Body, Locn}) =>
                                       prepare Bvar >- (fn Bvar'
                                    => cleanup Body >- (fn Body'
                                    => 
                 (* return (Term.mk_tyabs(clean Bvar', remove_case_magic Body')) *)
                 let val Bvar'' = clean Bvar'
                     val Body'' = remove_case_magic Body'
                 in return (Term.mk_tyabs(Bvar'', Body''))
                             handle e as HOL_ERR _ =>
                             tyabs_error_report r (Bvar'',Body'') e
                 end))
(*
                     val fvs = map from_term_var (Term.free_vars Body'')
                 in if op_mem Pretype.eq Bvar
                         (Pretype.type_varsl (map ptype_of fvs))
                    then tyabs_error_report ({Bvar=Bvar',Body=Body',Locn=Locn},fvs)
                    else return (Term.mk_tyabs(clean Bvar', Body''))
                 end))
*)
          | Antiq{Tm,...} => return Tm
          | Constrained{Ptm,...} => cleanup Ptm
          | Overloaded _ => raise ERRloc "to_term" (locn tm)
                                         "applied to Overloaded"
          | Pattern{Ptm,...} => cleanup Ptm
        end handle e as HOL_ERR _ => if not (is_debug()) then raise e else
                                       (print "ERROR in cleanup:\n"; print_preterm tm; print "\n"; Raise e)
        val K = kindVars tm
        val V = tyVars tm
        val ((newK,newV), result) = cleanup tm (K,V)
                   handle e as HOL_ERR _ => if not (is_debug()) then raise e else
                                              (print "ERROR in to_term:\n"; print_preterm tm; print "\n"; Raise e)
        val guessed_kindvars = List.take(newK, length newK - length K)
        val guessed_vars = List.take(newV, length newV - length V)
        val _ =
           (if not (null guessed_kindvars) andalso !Globals.notify_on_tyvar_guess
               andalso !Globals.interactive
            then Feedback.HOL_MESG (String.concat
                                      ("inventing new kind variable names: "
                                       :: Lib.commafy (List.rev guessed_kindvars)))
            else ();
            if not (null guessed_vars) andalso !Globals.notify_on_tyvar_guess
               andalso !Globals.interactive
            then Feedback.HOL_MESG (String.concat
                                      ("inventing new type variable names: "
                                       :: Lib.commafy (List.rev guessed_vars)))
            else ())
      in
        valOf result
      end
    else let
        fun shr l ty =
            if has_free_uvar ty then
              raise ERRloc "typecheck.to_term" l
                           "Unconstrained type variable (and Globals.\
                           \guessing_tyvars is false)"
            else Pretype.toType ty
      in
        clean shr tm
      end;


(*---------------------------------------------------------------------------*
 *                                                                           *
 * Overloading removal.  Th function "remove_overloading_phase1" will        *
 * replace Overloaded _ nodes with Consts where it can be shown that only    *
 * one of the possible constants has a type compatible with the type of the  *
 * term as it has been inferred during the previous phase of type inference. *
 * This may in turn constrain other overloaded terms elsewhere in the tree.  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

exception phase1_exn of locn.locn * string * hol_type
(* In earlier stages, the base_type of any overloaded preterms will have been
   become more instantiated through the process of type inference.  This
   first phase of resolving overloading removes those operators that are
   no longer compatible with this type.  If this results in no operators,
   this is an error.  If it results in one operator, this can be chosen
   as the result.  If there are more than one, this is passed on so that
   later phases can figure out which are possible given all the other
   overloaded sub-terms in the term. *)
fun remove_overloading_phase1 ptm =
  case ptm of
    Comb{Rator, Rand, Locn} => Comb{Rator = remove_overloading_phase1 Rator,
                                    Rand = remove_overloading_phase1 Rand,
                                    Locn = Locn}
  | TyComb{Rator, Rand, Locn} => TyComb{Rator = remove_overloading_phase1 Rator,
                                    Rand = Rand, Locn = Locn}
  | Abs{Bvar, Body, Locn} => Abs{Bvar = remove_overloading_phase1 Bvar,
                                 Body = remove_overloading_phase1 Body,
                                 Locn = Locn}
  | TyAbs{Bvar, Body, Locn} => TyAbs{Bvar = Bvar,
                                 Body = remove_overloading_phase1 Body, Locn = Locn}
  | Constrained{Ptm, Ty, Locn} =>
      Constrained{Ptm = remove_overloading_phase1 Ptm, Ty = Ty, Locn = Locn}
(*| Pattern{Ptm, Locn} => Pattern{Ptm = remove_overloading_phase1 Ptm, Locn = Locn}*) (* should this be here? *)
  | Overloaded{Name,Ty,Info,Locn} => let
      val _ = over_print ("\nResolving (phase1) overloaded "^Name^" of type\n"^Pretype.pretype_to_string Ty^"\n")
      fun testfn t = let
        open Term Pretype
        val possty = type_of t
        val fvs = free_vars t
        val kdavds = map (#1 o Kind.dest_var_kind) (tmlist_kdvs fvs)
        val avds = map (#1 o Type.dest_var_type) (tmlist_tyvs fvs)
        val pty0 = Pretype.fromType possty
        val _ = over_print ("Testing (phase1) possible type\n"^pretype_to_string pty0^"\n")
        val pty = Pretype.rename_typevars kdavds avds pty0
        val Ty1 = Pretype.reconcile_univ_types Ty pty
        val _ = if not (is_debug()) then () else
                print ("\nChecking (phase1) overloaded term " ^ Name ^ ":\n"
                        ^ "Pattern type: " ^ Pretype.pretype_to_string Ty1 ^ "\n"
                        ^ "Possibl type: " ^ Pretype.pretype_to_string pty ^ "\n")
        val res = Pretype.can_unify Ty1 pty
        val _ = over_print ("Attempted unification with type for "^Name^" ")
        val _ = over_print ((if res then "succeeded" else "failed")^".\n\n")
      in
        (*Pretype.can_unify Ty pty*) res
      end
      val possible_ops = List.filter testfn (#actual_ops Info)
    in
      case possible_ops of
        [] => let
          val ty = Pretype.toType Ty
        in
          last_tcerror := SOME (OvlNoType(Name,ty), Locn);
          raise phase1_exn(Locn,
                           "No possible type for overloaded constant "^Name^
                           "\n",
                           Pretype.toType Ty)
        end
      | [t] => let
          open Term
        in
          if is_const t then let
              val {Ty = ty,Name,Thy} = dest_thy_const t
              val pty0 = Pretype.fromType ty
              val _ = over_print ("Testing (phase1) possible const type\n"^Pretype.pretype_to_string pty0^"\n")
              val pty = Pretype.rename_typevars [] [] pty0
              val Ty1 = Pretype.reconcile_univ_types Ty pty
              val _ = if not (is_debug()) then () else
                print ("\nChecking (phase1) overloaded constant " ^ Name ^ ":\n"
                        ^ "Pattern type: " ^ Pretype.pretype_to_string Ty1 ^ "\n"
                        ^ "Possibl type: " ^ Pretype.pretype_to_string pty ^ "\n")
              val _ = Pretype.ho_unify Ty1 pty (* or Pretype.ho_unify_le? *)
            in
              Const{Name=Name, Thy=Thy, Ty=pty, Locn=Locn}
            end
          else let
              val fvs = free_vars t
              val kdavds = map (#1 o Kind.dest_var_kind) (tmlist_kdvs fvs)
              val avds = map (#1 o Type.dest_var_type) (tmlist_tyvs fvs)
              val ptm = term_to_preterm kdavds avds t
              val pty = ptype_of ptm
        val _ = if not (is_debug()) then () else
                print ("\nChecking (phase1) overloaded non-constant:\n"
                        ^ "Preterm of t: " ^ preterm_to_string ptm ^ "\n"
                        ^ "Pattern type: " ^ Pretype.pretype_to_string Ty ^ "\n"
                        ^ "Possibl type: " ^ Pretype.pretype_to_string pty ^ "\n")
              val _ = Pretype.ho_unify Ty pty (* or Pretype.ho_unify_le? *)
            in
              Pattern{Ptm = ptm, Locn = Locn}
            end
        end
      | _ =>
        Overloaded{Name=Name, Ty=Ty,
                   Info=Overload.fupd_actual_ops (fn _ => possible_ops) Info,
                   Locn=Locn}
     end
  | _ => ptm;


fun remove_overloading ptm = let
  open seqmonad
  infix >- >> ++
  fun opt2seq m env =
    case m env of
      (env', NONE) => seq.empty
    | (env', SOME result) => seq.result (env', result)
  fun unify t1 t2 = opt2seq (Pretype.ho_safe_unify t1 t2)
  (* Note that the order of the term traversal here is very important as
     the sub-terms "pulled out" will be "put back in" later under the
     assumption that the list is in the right order.  The traversal that
     puts the constants into the place of the Overloaded nodes must also
     traverse in the same order:
       Rator before Rand, Bvar before Body
     In accumulator style, that looks as below *)
  fun overloaded_subterms acc ptm =
    let
    in
(*
    if (is_debug()) then print ("\n?? overloading traversal on\n" ^ preterm_to_string ptm ^ "\n")
          else ();
*)
    case ptm of
      Overloaded x => x::acc
    | Comb{Rator, Rand, ...} =>
        overloaded_subterms (overloaded_subterms acc Rand) Rator
    | TyComb{Rator, Rand, ...} =>
        overloaded_subterms acc Rator
    | Abs{Bvar,Body,...} =>
        overloaded_subterms (overloaded_subterms acc Body) Bvar
    | TyAbs{Bvar,Body,...} =>
        overloaded_subterms acc Body
    | Constrained{Ptm,...} => overloaded_subterms acc Ptm
    | _ => acc
    end
  val overloads = overloaded_subterms [] ptm
  val _ = if List.length overloads >= 30
          then HOL_WARNING "Preterm" "remove_overloading"
                           "many overloaded symbols in term: \
                           \overloading resolution might take a long time."
          else ()
  fun workfunction list =
    case list of
      [] => return []
    | ({Name,Ty,Info,Locn,...}:overinfo)::xs => let
        val actual_ops = #actual_ops Info
        open Term
        fun tryit t =
            if is_const t then let
                val {Ty = ty, Name = n, Thy = thy} = Term.dest_thy_const t
                val pty0 = Pretype.fromType ty
                val _ = over_print ("Trying possible const type\n"^Pretype.pretype_to_string pty0^"\n")
                val pty  = Pretype.rename_typevars [] [] pty0
                val Ty1 = Pretype.reconcile_univ_types Ty pty (* may be unnecessary since came from term *)
        val _ = if not (is_debug()) then () else
                print ("\nTrying overloaded constant " ^ Name ^ ":\n\n"
                        ^ "Pattern type: " ^ Pretype.pretype_to_string Ty1 ^ "\n\n"
                        ^ "Possibl type: " ^ Pretype.pretype_to_string pty ^ "\n\n")
              in
                unify pty Ty1 >>
                return (Const{Name=n, Ty=Ty, Thy=thy, Locn=Locn})
              end
            else let
                val fvs = free_vars t
                val kdavds = List.map (#1 o Kind.dest_var_kind) (tmlist_kdvs fvs)
                val avds = List.map (#1 o Type.dest_var_type) (tmlist_tyvs fvs)
                val ptm = term_to_preterm kdavds avds t
                val pty = ptype_of ptm
                val Ty1 = Pretype.reconcile_univ_types Ty pty (* may be unnecessary since came from term *)
        val _ = if not (is_debug()) then () else
                print ("\nTrying overloaded non-constant:\n"
                        ^ "Preterm of t: " ^ preterm_to_string ptm ^ "\n"
                        ^ "Pattern type: " ^ Pretype.pretype_to_string Ty1 ^ "\n"
                        ^ "Possibl type: " ^ Pretype.pretype_to_string pty ^ "\n")
              in
                unify pty Ty1 >>
                return (Pattern{Ptm = ptm, Locn = Locn})
              end
      in
        tryall tryit actual_ops >- (fn c =>
        workfunction xs >- (fn cs =>
        return (c::cs)))
      end
in
  workfunction overloads
end

fun do_overloading_removal ptm0 = let
  open seq
  val ptm = remove_overloading_phase1 ptm0
  val result = remove_overloading ptm ([],[],[])
  fun clean_rsubst rs ((r, ord_value)::rest) =
    if mem r rs then clean_rsubst rs rest
                else (r, ord_value)::clean_rsubst (r::rs) rest
    | clean_rsubst _ [] = []
  fun apply_tsubst subst = app (fn (r, value) => r := (*Pretype.SOMEU*) value) subst
  fun apply_ksubst subst = app (fn (r, value) => r := (*Prekind.SOMEK*) value) subst
  fun apply_rsubst subst = app (fn (r, ord_value) => r := SOME ord_value) subst
  fun apply_subst(rsubst, ksubst, tsubst) =
      (apply_rsubst (clean_rsubst [] rsubst); apply_ksubst ksubst; apply_tsubst tsubst)
  fun do_csubst clist ptm =
    case clist of
      [] => (ptm, [])
    | (c::cs) => let
      in
        (* must take care to keep order of traversal same as traversal in
           overloaded_subterms above *)
(*
        if (is_debug()) then print ("\n?? overloading removal on\n" ^ preterm_to_string ptm ^ "\n")
          else ();
*)
        case ptm of
          Comb{Rator, Rand, Locn} => let
            (* Rator before Rand *)
            val (Rator', clist') = do_csubst clist Rator
            val (Rand', clist'') = do_csubst clist' Rand
          in
            (Comb{Rator = Rator', Rand = Rand', Locn = Locn}, clist'')
          end
        | TyComb{Rator, Rand, Locn} => let
            (* Rator only *)
            val (Rator', clist') = do_csubst clist Rator
          in
            (TyComb{Rator = Rator', Rand = Rand, Locn = Locn}, clist')
          end
        | Abs{Bvar, Body, Locn} => let
            (* Bvar before Body *)
            val (Bvar', clist') = do_csubst clist Bvar
            val (Body', clist'') = do_csubst clist' Body
          in
            (Abs{Bvar = Bvar', Body = Body', Locn = Locn}, clist'')
          end
        | TyAbs{Bvar, Body, Locn} => let
            (* Body only *)
            val (Body', clist') = do_csubst clist Body
          in
            (TyAbs{Bvar = Bvar, Body = Body', Locn = Locn}, clist')
          end
        | Constrained{Ptm,Ty,Locn} => let
            val (Ptm', clist') = do_csubst clist Ptm
          in
            (Constrained{Ptm = Ptm', Ty = Ty, Locn = Locn}, clist')
          end
        | Overloaded {Ty,...} => let
        val _ = if not (is_debug()) then () else
                print ("\nDoing overloading removal:\n\n"
                        ^ "Pattern type: " ^ Pretype.pretype_to_string Ty ^ "\n\n"
                        ^ "Possibl type: " ^ Pretype.pretype_to_string (ptype_of c) ^ "\n\n")
                                 in Pretype.ho_unify (ptype_of c) Ty;
                                    (c,cs)
                                 end
        | _ => (ptm, clist)
      end
in
  case cases result of
    NONE => raise ERRloc "do_overloading_removal" (locn ptm0)
                         "Couldn't find a sensible resolution for \
                         \overloaded constants"
  | SOME ((env as (renv,kenv,tenv),clist),xs) =>
      if not (!Globals.guessing_overloads)
         orelse !Globals.notify_on_tyvar_guess
      then
        case cases xs of
          NONE => (apply_subst env; #1 (do_csubst clist ptm))
        | SOME _ => let
          in
            if not (!Globals.guessing_overloads) then
              raise ERRloc "do_overloading_removal" (locn ptm0)
                           "More than one resolution of overloading possible"
            else ();
            if !Globals.interactive then
              Feedback.HOL_MESG
                "more than one resolution of overloading was possible"
            else ();
            apply_subst env;
            #1 (do_csubst clist ptm)
          end
      else
        (apply_subst env; #1 (do_csubst clist ptm))
end

fun remove_elim_magics ptm =
  case ptm of
    Var _ => ptm
  | Const _ => ptm
  | Antiq _ => ptm
  | Comb{Rator = (rator as Const{Name, ...}), Rand = ptm1, Locn} =>
      if Name = nat_elim_term then ptm1
      else Comb{Rator = rator, Rand = remove_elim_magics ptm1, Locn = Locn}
  | Comb{Rator, Rand, Locn} => Comb{Rator = remove_elim_magics Rator,
                                    Rand = remove_elim_magics Rand, Locn = Locn}
  | TyComb{Rator, Rand, Locn} => TyComb{Rator = remove_elim_magics Rator,
                                        Rand = Rand, Locn = Locn}
  | Abs{Bvar, Body, Locn} => Abs{Bvar = remove_elim_magics Bvar,
                                 Body = remove_elim_magics Body, Locn = Locn}
  | TyAbs{Bvar, Body, Locn} => TyAbs{Bvar = Bvar,
                                     Body = remove_elim_magics Body, Locn = Locn}
  | Constrained{Ptm, Ty, Locn} => Constrained{Ptm = remove_elim_magics Ptm,
                                              Ty = Ty, Locn = Locn}
  | Overloaded _ => raise Fail "Preterm.remove_elim_magics on Overloaded"
  | Pattern _ => ptm


val overloading_resolution0 = remove_elim_magics o do_overloading_removal

fun overloading_resolution ptm =
    overloading_resolution0 ptm
    handle phase1_exn(l,s,ty) =>
           (tcheck_say (locn.toString l ^ ": " ^ s);
            raise ERRloc "overloading_resolution" l s)

(*---------------------------------------------------------------------------
 * Type inference for HOL terms. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

local
  open Prekind Prerank Pretype
  val zero = Zerorank
  val inc  = Sucrank
  val max  = mk_Maxrank

(*
fun check_zero_ty0 (Vartype(s,kd)) = kd
  | check_zero_ty0 (Contype{Kind, ...}) = Kind
  | check_zero_ty0 (TyApp(opr,arg)) = chase (check_zero_ty opr)
  | check_zero_ty0 (ty as TyUniv _) = typ (prank_of0 ty) (* NOT check_zero_ty body *)
  | check_zero_ty0 (ty as TyExis _) = typ (prank_of0 ty) (* NOT check_zero_ty body *)
  | check_zero_ty0 (TyAbst(Bvar,Body)) = check_zero_ty Bvar ==> check_zero_ty Body
  | check_zero_ty0 (TyKindConstr{Ty,Kind}) = Kind
  | check_zero_ty0 (TyRankConstr{Ty,Rank}) = check_zero_ty Ty
  | check_zero_ty0 (UVar (ref (NONEU kd))) = kd
  | check_zero_ty0 (UVar (ref (SOMEU ty))) = check_zero_ty ty
and check_zero_ty (pty as PT(ty,locn)) = check_zero_ty0 ty
*)
in
fun check_zero_ty pty = Prerank.eq zero (prank_of_type pty)
fun check_zero tm = let 
fun check_zero0 (Var{Ty, ...}) = false
  | check_zero0 (Const{Ty, Name, ...}) = Name="!" andalso check_zero_ty Ty
  | check_zero0 (Comb{Rator, Rand, ...}) = (check_zero1 Rator orelse check_zero1 Rand)
  | check_zero0 (TyComb{Rator, Rand, ...}) = (check_zero1 Rator orelse check_zero_ty Rand)
  | check_zero0 (Abs{Bvar,Body,...}) = (check_zero1 Bvar orelse check_zero1 Body)
  | check_zero0 (TyAbs{Bvar,Body,...}) = (check_zero_ty Bvar orelse check_zero1 Body)
  | check_zero0 (Constrained{Ty,Ptm,...}) = (check_zero_ty Ty orelse check_zero1 Ptm)
  | check_zero0 (Antiq{Tm,...}) = false
  | check_zero0 (Overloaded {Ty,...}) = check_zero_ty Ty
  | check_zero0 (Pattern{Ptm,...}) = check_zero1 Ptm
and check_zero1 tm =
      check_zero0 tm (*andalso (print "\nFound Zero rank in:\n";
                              print_preterm tm;
                              print "\n";
                              true)*)
in check_zero1 tm
end
end;

fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained{Ptm,...}) = is_atom Ptm
(*| is_atom (Pattern{Ptm,...}) = is_atom Ptm*)
  | is_atom (Overloaded _) = true
  | is_atom (t as Comb{Rator,Rand,...}) =
      Literal.is_numeral (to_term NONE (overloading_resolution t)) orelse
      Literal.is_numeral (to_term NONE (overloading_resolution Rand)) andalso
        (case Rator
          of Overloaded{Name,...} => Name = fromNum_str
           | Const{Name,...} => Name = nat_elim_term
           | _ => false)
  | is_atom t = false

fun mk_tycomb(tm,ty) = TyComb{Rator=tm, Rand=ty, Locn=locn.Loc_None}

fun list_mk_tycomb(tm,[]) = tm
  | list_mk_tycomb(tm,ty::tys) = list_mk_tycomb(mk_tycomb(tm,ty),tys)

val univcomplain = ref true
val _ = register_btrace ("Var of Universal Type Complaint", univcomplain)

(*
fun high_o (Const{Thy="combin", Name="o", Ty=Ty, ...}) =
       current_trace "debug_type_inference" > 0 andalso
          Prerank.leq (Prerank.Sucrank Prerank.Zerorank) (Pretype.prank_of_type Ty)
  | high_o _ = false

fun high_unit (Var{Name="unit", Ty=Ty, ...}) =
       current_trace "debug_type_inference" > 0 andalso
          Prerank.leq (Prerank.Sucrank Prerank.Zerorank) (Pretype.prank_of_type Ty)
  | high_unit _ = false

fun check_for_high_o (Const{Thy="combin", Name="o", Ty=Ty, ...}) =
       if current_trace "debug_type_inference" > 0 andalso
          Prerank.leq (Prerank.Sucrank Prerank.Zerorank) (Pretype.prank_of_type Ty)
         then Raise (ERR "check_for_high_o"
                ("found combin$o of rank " ^ Prerank.prerank_to_string(Pretype.prank_of_type Ty) ^
                 " of type\n" ^ Pretype.pretype_to_string Ty ^ "\n"))
         else ()
  | check_for_high_o (Overloaded{Ty,...}) = ()
(*
       if current_trace "debug_type_inference" > 0 andalso
          Prerank.leq (Prerank.Sucrank Prerank.Zerorank) (Pretype.prank_of_type Ty)
         then Raise (ERR "check_for_high_o"
                ("found overloaded combin$o of rank " ^ Prerank.prerank_to_string(Pretype.prank_of_type Ty) ^
                 " of type\n" ^ Pretype.pretype_to_string Ty ^ "\n"))
         else ()
*)
  | check_for_high_o (Comb{Rator,Rand,...}) = (check_for_high_o Rator; check_for_high_o Rand)
  | check_for_high_o (TyComb{Rator,...}) = check_for_high_o Rator
  | check_for_high_o (Abs{Bvar,Body,...}) = (check_for_high_o Bvar; check_for_high_o Body)
  | check_for_high_o (TyAbs{Body,...}) = check_for_high_o Body
  | check_for_high_o (Constrained{Ptm,...}) = check_for_high_o Ptm
  | check_for_high_o (Pattern{Ptm,...}) = check_for_high_o Ptm
  | check_for_high_o _ = ()
*)

fun check_for f (c as Const _) = f c
  | check_for f (v as Var _) = f v
  | check_for f (t as Overloaded{Ty,...}) = f t
  | check_for f (Comb{Rator,Rand,...}) = (check_for f Rator orelse check_for f Rand)
  | check_for f (TyComb{Rator,...}) = check_for f Rator
  | check_for f (Abs{Bvar,Body,...}) = (check_for f Bvar orelse check_for f Body)
  | check_for f (TyAbs{Body,...}) = check_for f Body
  | check_for f (Constrained{Ptm,...}) = check_for f Ptm
  | check_for f (Pattern{Ptm,...}) = check_for f Ptm
  | check_for f _ = false

local
  val op --> = Pretype.-->
  val op ==> = Prekind.==>
  fun default_kdprinter x = "<kind>"
  fun default_typrinter x = "<hol_type>"
  fun default_tmprinter x = "<term>"
in
fun TC printers = let
  val to_term = to_term printers
  val (ptm, pty, pkd) =
      case printers
       of SOME (x,y,z) =>
          let val kdprint = z
              fun typrint ty =
                  if Type.is_con_type ty
                  then (y ty ^ " :" ^ z (Type.kind_of ty))
                  else y ty
              fun tmprint tm = x tm
               (* if Term.is_const tm
                  then (x tm ^ " " ^ y (Term.type_of tm))
                  else x tm *)
          in
            (tmprint, typrint, kdprint)
          end
        | NONE => (default_tmprinter, default_typrinter, default_kdprinter)
  val prk = Rank.rank_to_string
  (* ptype_of should only be applied to preterms which have been checked. *)
  fun ptype_of (Var{Ty, ...}) = Ty
    | ptype_of (Const{Ty, ...}) = Ty
    | ptype_of (Tm as Comb{Rator, ...}) = Pretype.chase (ptype_of Rator)
                                          (* chase can fail if applied to a non-function type *)
    | ptype_of (TyComb{Rator, Rand, ...}) =
        let val rator_ty = ptype_of Rator
        in let val (Bvar,Body) = Pretype.dest_univ_type rator_ty
               val Bvar1 = Pretype.the_var_type Bvar
           in Pretype.type_subst [Bvar1 |-> Rand] Body
           end
           handle Feedback.HOL_ERR {origin_structure="Pretype",
                                    origin_function="dest_univ_type",message}
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val Rator_ty = Type.deep_beta_eta_ty (Pretype.toType (ptype_of Rator))
                             handle e => raise (wrap_exn "Preterm" "ptype_of.TyComb" e)
              val Rator' = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator))
                           handle e => (Globals.show_types := tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand' = (Type.deep_beta_eta_ty (Pretype.toType Rand)
                           handle e => raise (wrap_exn "Preterm" "ptype_of.TyComb" e))
                handle e => (Globals.show_types := tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: unable to form \
                       \the application of the term\n\n",
                       ptm Rator',
                       "\n\n"^locn.toString (locn Rator)^"\n\n",
                       if (is_atom Rator) then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rator') ^ "\n\n"),

                       "to the type\n\n",
                       pty Rand',
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       "since the term does not have a universal type.\n",

                       "unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            tcheck_say message;
            last_tcerror := SOME (NotUnivFail(Rator',Rand'), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) message
          end
        end
    | ptype_of (Abs{Bvar,Body,...}) = ptype_of Bvar --> ptype_of Body
    | ptype_of (TyAbs{Bvar,Body,...}) = Pretype.mk_univ_type(Bvar, ptype_of Body)
    | ptype_of (Constrained{Ty,...}) = Ty
    | ptype_of (Pattern{Ptm,...}) = ptype_of Ptm
    | ptype_of (Antiq{Tm,...}) = Pretype.fromType (Term.type_of Tm)
    | ptype_of (Overloaded {Ty,...}) = Ty
  val checkkind = Pretype.checkkind (case printers of SOME (x,y,z) => SOME (y,z) | NONE => NONE)
  fun mk_not_tyabs tm =
       let open Pretype
           val ty = deep_beta_eta_ty (ptype_of tm)
           val (bvars,body) = strip_univ_type ty
           val args = map (fn bvar => new_uvar(pkind_of bvar)) bvars
       in list_mk_tycomb(tm, args)
       end

  fun Comb_error_report (Rator', Rand') (e:exn) =
      let
      in raise e
      end
             handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                           origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _   = Globals.show_types := true
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                handle e => (Globals.show_types := tmp; raise e)
              val Rand_tm  = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rand'))
                handle e => (Globals.show_types := tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: unable to infer a type \
                       \for the application of\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator')^"\n\n",
                       if (is_atom Rator') then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rator_tm) ^ "\n\n"),

                       "to\n\n",
                       ptm Rand_tm,
                       "\n\n"^locn.toString (locn Rand')^"\n\n",

                       if (is_atom Rand') then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rand_tm) ^ "\n\n"),

                       "unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            tcheck_say message;
            last_tcerror := SOME (AppFail(Rator_tm,Rand_tm), locn Rand');
            raise ERRloc"typecheck" (locn Rand' (* arbitrary *)) message
          end

  fun TyComb_error_report (Rator', Rand) (e:exn) =
      let
      in raise e
      end
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                         handle e => (Globals.show_types := tmp; Raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Type.deep_beta_eta_ty (Pretype.toType Rand)
                         handle e => (Globals.show_types := tmp; Raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: unable to form \
                              \the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n", locn.toString (locn Rator'), "\n\n",
                       if (is_atom Rator') then ""
                       else("which has type\n\n" ^
                            pty(Term.type_of Rator_tm) ^ "\n\n"),
                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n", locn.toString rand_locn, "\n\n",
                       "since the term does not have a universal type.\n\n",
                       "unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            tcheck_say message;
            last_tcerror := SOME (TyAppFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify_le",message})
       => let val show_ranks = Feedback.get_tracefn "ranks"
              val show_kinds = Feedback.get_tracefn "kinds"
              val tmp0 = !Globals.show_types
              val _ = Globals.show_types := true
              val tmp1 = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                       handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; Raise e)
              val Rator_ty = Term.type_of Rator_tm
              val Rator_btyv = fst (Type.dest_univ_type Rator_ty)
              val (name,kind) = Type.dest_var_type Rator_btyv
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Type.deep_beta_eta_ty (Pretype.toType Rand)
                       handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; Raise e)
              val message =
                if Kind.rank_of kind < Type.rank_of_type Rand_ty then
                  String.concat
                      [
                       "\nRank inference failure: unable to infer a rank \
                       \for the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator')^"\n\n",
                       (* if (is_atom Rator') then ""
                       else ("with type\n\n" ^
                             pty(Term.type_of Rator_tm) ^ "\n\n"), *)
                       "which expects a type of rank ",
                       prk (Kind.rank_of kind),"\n\n",

                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       "which has rank ",
                             prk(Type.rank_of_type Rand_ty), "\n\n",

                       "rank unification failure message: ", message, "\n"]
                else
                  String.concat
                      [
                       "\nKind inference failure: unable to infer a kind \
                       \for the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator')^"\n\n",
                       (* if (is_atom Rator') then ""
                       else ("with type\n\n" ^
                             pty(Term.type_of Rator_tm) ^ "\n\n"), *)
                       "which expects a type of kind\n\n",
                       pkd kind,"\n\n",

                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       if (Pretype.is_atom Rand) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of Rand_ty) ^ "\n\n"),

                       "kind unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp0;
            Feedback.set_trace "kinds" tmp1;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (TyAppKindFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify_le",message})
       => let val tmp0 = !Globals.show_types
              val _ = Globals.show_types := true
              val show_kinds = Feedback.get_tracefn "kinds"
              val tmp1 = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                             handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; Raise e)
              val Rator_ty = Type.deep_beta_eta_ty (Term.type_of Rator_tm)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Type.deep_beta_eta_ty (Pretype.toType Rand)
                            handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; Raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: unable to infer a rank \
                       \for the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator')^"\n\n",

                       if Type.is_univ_type Rator_ty then
                           "whose argument must have rank <= " ^
                           prk(Type.rank_of_type (#1 (Type.dest_univ_type Rator_ty))) ^ "\n\n"
                       else "which is not a universal type\n\n",
                       if (is_atom Rator') then ""
                       else ("which has type\n\n" ^
                             pty Rator_ty ^ "\n\n"),
                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       if (Pretype.is_atom Rand) then ""
                       else ("which has rank\n\n" ^
                             prk(Type.rank_of_type Rand_ty) ^ "\n\n"),

                       "rank unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp0;
            Feedback.set_trace "kinds" tmp1;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (TyAppRankFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end

  fun Var_error_report {Name, Ty, Locn} (e:exn) =
      let
      in raise e
      end
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val ty_locn = pty_locn Ty
              val real_type = (Type.deep_beta_eta_ty (Pretype.toType Ty)
                         handle e => Raise (wrap_exn "Preterm" "typecheck.Var" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the variable ", Name,
                       "\n\n"^locn.toString Locn^"\n\n",

                       "is constrained to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "which has kind\n\n", pkd(Type.kind_of real_type), "\n\n",

                       "but the type of a term must have kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (VarKindFail(Name, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end

  fun Const_error_report {Name, Thy, Ty, Locn} (e:exn) =
      let
      in raise e
      end
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val ty_locn = pty_locn Ty
              val real_type = (Type.deep_beta_eta_ty (Pretype.toType Ty)
                         handle e => Raise (wrap_exn "Preterm" "typecheck.Const" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the constant ",
                       Thy^"$"^Name,
                       "\n\n"^locn.toString Locn^"\n\n",

                       "is constrained to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "which has kind\n\n", pkd(Type.kind_of real_type), "\n\n",

                       "but the type of a term must have kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (ConstKindFail(Name, Thy, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end

  fun Constrained_error_report1 {Ptm, Ty, Locn} (e:exn) =
      let
      in raise e
      end
         handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                       origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val real_term = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Ptm))
                              handle e => (Feedback.set_trace "kinds" tmp; Raise e)
              val ty_locn = pty_locn Ty
              val real_type = Type.deep_beta_eta_ty (Pretype.toType Ty)
                              handle e => (Feedback.set_trace "kinds" tmp; Raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the term\n\n",
                       ptm real_term,
                       "\n\n"^locn.toString (locn Ptm)^"\n\n",

                       "is constrained to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "which has kind\n\n", pkd(Type.kind_of real_type), "\n\n",

                       "but the type of a term must have kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (ConstrainKindFail(real_term, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end

  fun Constrained_error_report2 {Ptm, Ty, Locn} (e:exn) =
      let
      in raise e
      end
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val real_term = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Ptm))
                              handle e => (Globals.show_types := tmp; Raise e)
              val real_type = Type.deep_beta_eta_ty (Pretype.toType Ty)
                              handle e => (Globals.show_types := tmp; Raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: the term\n\n",
                       ptm real_term,
                       "\n\n", locn.toString (locn Ptm), "\n\n",
                       if (is_atom Ptm) then ""
                       else("which has type\n\n" ^
                            pty(Term.type_of real_term) ^ "\n\n"),
                       "can not be constrained to be of type\n\n",
                       pty real_type,
                       "\n\nunification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            last_tcerror := SOME (ConstrainFail(real_term, real_type), Locn);
            tcheck_say message;
            raise ERRloc"typecheck" Locn message
          end

  fun check(tm as Comb{Rator, Rand, Locn}) =
      (let val Rator' = check Rator;
           val Rand'  = check Rand;
           val Rator_ty = Pretype.deep_beta_eta_ty (ptype_of Rator')
           val Rand_ty = Pretype.deep_beta_eta_ty (ptype_of Rand')
           fun univ_str ty = (if Pretype.is_univ_type ty then "IS"
                              else if Pretype.with_homs_is_not_univ_type ty then "IS DEFINITELY NOT"
                              else "IS NOT CLEARLY") ^ " universal"
       in if Pretype.is_univ_type Rator_ty then
            (if not(is_debug()) then () else
               print ("\nInserting type arguments to the rator term\n" ^ preterm_to_string Rator' ^ "\n");
             check (Comb{Rator=mk_not_tyabs Rator', Rand=Rand', Locn=Locn}))
          else if Pretype.is_univ_type Rand_ty andalso
                 (let val dom_ty = fst (Pretype.dom_rng Rator_ty)
                  in Pretype.with_homs_is_not_univ_type dom_ty
                  end handle HOL_ERR _ => false) (* dom_rng can fail *)
               then
            (if not(is_debug()) then () else
               print ("\nInserting type arguments to the rand term\n" ^ preterm_to_string Rand' ^ "\n");
                 check (Comb{Rator=Rator', Rand=mk_not_tyabs Rand', Locn=Locn}))
          else
             (if not (!univcomplain) then () else
              (* Test if Rator is a var with universal or existential type but no constraint *)
              let val {Name, Ty, Locn} = dest_var Rand'
                  open Pretype
                  fun the_uvar_ref(PT(UVar (r as ref (NONEU _)),_)) = r
                    | the_uvar_ref _ = raise ERR "the_uvar_ref" "not a UVar (NONE)"
                  val r = the_uvar_ref (the_var_type Rand_ty)
                  val dom_ty = #1 (dom_rng Rator_ty)
                  fun is_uvar_type(PT(UVar r,loc)) = true
                    | is_uvar_type _ = false
                  fun deref_uvar r = the_var_type (PT(UVar r,locn.Loc_None))
                  val uvars = exists is_uvar_type (map deref_uvar (uvars_of dom_ty))
              in if not uvars orelse not (is_universal dom_ty) then ()
                 else
                   HOL_WARNING "Preterm" "type checking"
                          (locn.toString (locn Rand) ^ ",\n  " ^ Name ^
                           " should have its universal type indicated by a type constraint.")
              end handle _ => ();
              (* end of test to warn if var with universal type but no constraint *)
              if not (is_debug()) then () else
                print ("\n(Checking application:\n" ^ preterm_to_string Rator ^ "\napplied to\n"
                        ^ preterm_to_string Rand ^ "\n"
                        ^ "Types: rator     " ^ univ_str Rator_ty ^ "\n"
                        ^ "  and: rand      " ^ univ_str Rand_ty ^ "\n"
                        ^ (if Pretype.is_fun_type Rator_ty then
                             "  and: rator dom " ^ univ_str (fst (Pretype.dom_rng Rator_ty)) ^ "\n"
                           else "")
                        ^ "Types: rator:\n" ^ Pretype.pretype_to_string Rator_ty ^ "\n"
                        ^ "   to: rand :\n" ^ Pretype.pretype_to_string Rand_ty ^ "\n");
              Pretype.set_error_report (preterm_to_string (beta_eta_conv_ty_in_term tm),
                                        Comb_error_report (Rator',Rand'));
              if Pretype.is_fun_type Rator_ty (* optimize; cut out unnecessary unifications *)
              then Pretype.unify_le Rand_ty (* :<=: *) (fst (Pretype.dom_rng Rator_ty))
              else
                let in
                   Pretype.begin_homs();
                   Pretype.unify_le (Rand_ty --> Pretype.all_new_uvar())
                                                  (* Pretype.new_uvar(Prekind.new_uvar(
                                                       Pretype.prank_of_type Rator_ty)) *)
                              (* :<=: *) Rator_ty;
                   Pretype.resolve_ho_matches();
                   Pretype.end_homs();
                   ()
                end;
              if not (is_debug()) then () else
                print ("\n)Checked application:\n" ^ preterm_to_string Rator ^ "\napplied to\n"
                        ^ preterm_to_string Rand ^ "\n"
                        ^ "Types: rator:\n" ^ Pretype.pretype_to_string Rator_ty ^ "\n"
                        ^ "   to: rand :\n" ^ Pretype.pretype_to_string Rand_ty ^ "\n");
              Comb{Rator=Rator', Rand=Rand', Locn=Locn})
             handle e as HOL_ERR _ => Comb_error_report (Rator',Rand') e
(*
             handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                           origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _   = Globals.show_types := true
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                handle e => (check Rator'; Globals.show_types := tmp; raise e)
              val Rand_tm  = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rand'))
                handle e => (check Rand';  Globals.show_types := tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: unable to infer a type \
                       \for the application of\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator)^"\n\n",
                       if (is_atom Rator') then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rator_tm) ^ "\n\n"),

                       "to\n\n",
                       ptm Rand_tm,
                       "\n\n"^locn.toString (locn Rand)^"\n\n",

                       if (is_atom Rand') then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rand_tm) ^ "\n\n"),

                       "unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            tcheck_say message;
            last_tcerror := SOME (AppFail(Rator_tm,Rand_tm), locn Rand);
            raise ERRloc"typecheck" (locn Rand' (* arbitrary *)) message
          end
*)
       end)
    | check(tm as TyComb{Rator, Rand, Locn}) =
         (let val Rator' = check Rator
              val _  = checkkind Rand
              val Rator_ty = ptype_of Rator'
              val _ = if not (is_debug()) then () else
                print ("\nChecking application of term to type:\n" ^ preterm_to_string Rator ^ " applied to\n"
                        ^ Pretype.pretype_to_string Rand ^ "\n"
                        ^ "Checking kind of type:\n"
                        ^ Prekind.prekind_to_string (Pretype.pkind_of Rand) ^ "\n")
          in
          Pretype.set_error_report (preterm_to_string (beta_eta_conv_ty_in_term tm),
                                    TyComb_error_report (Rator',Rand));
          let val (bvar,body) = Pretype.dest_univ_type Rator_ty
                                handle HOL_ERR _ => let
                                     val Rator_str = " (" ^ preterm_to_string Rator' ^ ")" handle HOL_ERR _ => ""
                                     val s = "'a"
                                     val kd = Prekind.all_new_uvar() (* new_var_uvar() *)
                                     val bvar = Pretype.PT(Pretype.Vartype(s,kd),locn.Loc_None) (* choose either this or next line *)
                                     (*val bvar = new_uvar kd*)
                                     val body = Pretype.mk_app_type(Pretype.all_new_uvar(), bvar)
                                     val univ_ty = Pretype.mk_univ_type(bvar, body)
                                 in (* if not (!univcomplain) then () else
                                    HOL_WARNING "Preterm" "type checking"
                                      (locn.toString (locn Rator) ^ ",\n  " ^
                                       "expression" ^ Rator_str ^
                                       " needs its universal type indicated by a type constraint."); *)
                                    checkkind univ_ty;
                                    Pretype.unify Rator_ty univ_ty;
                                    (bvar,body)
                                 end
          in
             if not (is_debug()) then () else
                print ("\nChecking application of term to type:\n" ^ preterm_to_string Rator ^ "\napplied to\n"
                        ^ Pretype.pretype_to_string Rand ^ "\n"
                        ^ "Operand kind : " ^ Prekind.prekind_to_string (Pretype.pkind_of Rand) ^ "\nwhere\n"
                        ^ "Type of term :\n" ^ Pretype.pretype_to_string Rator_ty ^ "\n"
                        ^ "Kind of bvar : " ^ Prekind.prekind_to_string (Pretype.pkind_of bvar) ^ "\n");
             Prekind.unify_le (Pretype.pkind_of Rand) (* :<=: *) (Pretype.pkind_of bvar);
             if not (is_debug()) then () else
                print ("\nChecked application of term to type:\n" ^ preterm_to_string Rator ^ "\napplied to\n"
                        ^ Pretype.pretype_to_string Rand ^ "\n"
                        ^ "Operand kind : " ^ Prekind.prekind_to_string (Pretype.pkind_of Rand) ^ "\nwhere\n"
                        ^ "Type of term :\n" ^ Pretype.pretype_to_string Rator_ty ^ "\n"
                        ^ "Kind of bvar : " ^ Prekind.prekind_to_string (Pretype.pkind_of bvar) ^ "\n");
             TyComb{Rator=Rator', Rand=Rand, Locn=Locn}
          end
             handle e as HOL_ERR _ => TyComb_error_report (Rator',Rand) e
(*
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                         handle e => (Globals.show_types := tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Type.deep_beta_eta_ty (Pretype.toType Rand)
                         handle e => (Globals.show_types := tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: unable to form \
                              \the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n", locn.toString (locn Rator), "\n\n",
                       if (is_atom Rator') then ""
                       else("which has type\n\n" ^
                            pty(Term.type_of Rator_tm) ^ "\n\n"),
                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n", locn.toString rand_locn, "\n\n",
                       "since the term does not have a universal type.\n\n",
                       "unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            tcheck_say message;
            last_tcerror := SOME (TyAppFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_ranks = Feedback.get_tracefn "ranks"
              val show_kinds = Feedback.get_tracefn "kinds"
              val tmp0 = !Globals.show_types
              val _ = Globals.show_types := true
              val tmp1 = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                       handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Type.deep_beta_eta_ty (Pretype.toType Rand)
                       handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: unable to infer a type \
                       \for the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator)^"\n\n",
                       if (is_atom Rator') then ""
                       else ("which has type\n\n" ^
                             pty(Term.type_of Rator_tm) ^ "\n\n"),

                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       if (Pretype.is_atom Rand) then ""
                       else ("which has kind\n\n" ^
                             pkd(Type.kind_of Rand_ty) ^ "\n\n"),

                       "kind unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp0;
            Feedback.set_trace "kinds" tmp1;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (TyAppKindFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify_le",message})
       => let val tmp0 = !Globals.show_types
              val _ = Globals.show_types := true
              val show_kinds = Feedback.get_tracefn "kinds"
              val tmp1 = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val Rator_tm = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Rator'))
                             handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; raise e)
              val Rator_ty = Type.deep_beta_eta_ty (Term.type_of Rator_tm)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Type.deep_beta_eta_ty (Pretype.toType Rand)
                            handle e => (Globals.show_types := tmp0; Feedback.set_trace "kinds" tmp1;
                                    Feedback.set_trace "ranks" tmp2; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: unable to infer a type \
                       \for the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator)^"\n\n",

                       if Type.is_univ_type Rator_ty then
                           "whose argument must have rank <= " ^
                           prk(Type.rank_of_type (#1 (Type.dest_univ_type Rator_ty))) ^ "\n\n"
                       else "which is not a universal type\n\n",
                       if (is_atom Rator') then ""
                       else ("which has type\n\n" ^
                             pty Rator_ty ^ "\n\n"),
                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       if (Pretype.is_atom Rand) then ""
                       else ("which has rank\n\n" ^
                             prk(Type.rank_of_type Rand_ty) ^ "\n\n"),

                       "rank unification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp0;
            Feedback.set_trace "kinds" tmp1;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (TyAppRankFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
*)
          end)
    | check (  Abs{Bvar, Body, Locn}) = let 
                                            val _ = if not (is_debug()) then () else
                print ("\nChecking abstraction of term by term variable: (1/2) bound variable:\n"
                        ^ preterm_to_string Bvar ^ "\n")
                                            val Bvar' = check Bvar
                                            val _ = if not (is_debug()) then () else
                print ("\nChecking abstraction of term by term variable: (2/2) body:\n"
                        ^ preterm_to_string Body ^ "\n")
                                            val Body' = check Body
                                         in Abs{Bvar=Bvar', Body=Body', Locn=Locn}
                                        end
    | check (TyAbs{Bvar, Body, Locn}) = let
                                            val _ = Pretype.begin_homs()
                                            val _ = if not (is_debug()) then () else
                print ("\nChecking abstraction of term by type variable: (1/2):\n"
                        ^ "Checking kind of type variable:\n"
                        ^ Pretype.pretype_to_string Bvar ^ "\n")
                                            val _ = checkkind Bvar
                                            val Bvar' = Pretype.the_var_type Bvar
                                            val _ = if not (is_debug()) then () else
                print ("\nChecking abstraction of term by type variable: (2/2) body:\n"
                        ^ preterm_to_string Body ^ "\n")
                                            val Body' = check Body
                                            val _ = Pretype.resolve_ho_matches()
                                            val _ = Pretype.end_homs()
                                         in if mem Bvar' (Pretype.type_varsl (map ptype_of (free_vars Body)))
                                            then raise ERRloc "typecheck.TyAbs" Locn
                                                   "bound type variable occurs free in the type of a free variable of the body"
                                            else TyAbs{Bvar=Bvar, Body=Body', Locn=Locn}
                                        end
    | check (v as Var (r as {Name, Ty, Locn})) =
       ((if not (is_debug()) then () else
                print ("\nChecking type of term var " ^ Name ^ ":\n"
                        ^ "  " ^ Pretype.pretype_to_string Ty ^ "\n");
         checkkind Ty;
         if not (is_debug()) then () else
                print ("\nChecked type of term var " ^ Name ^ ":\n"
                        ^ "  " ^ Pretype.pretype_to_string Ty ^ "\n");
(*
         if not (is_debug()) then () else
                print ("\nChecking kind of type of " ^ Name ^ " has kind ty.\n");
*)
         Prekind.unify (Pretype.pkind_of Ty) (Prekind.typ (Prerank.new_uvar()));
(*
         if not (is_debug()) then () else
                print ("\nChecked kind of type of " ^ Name ^ " has kind ty.\n");
*)
         v)
       handle e as HOL_ERR _ => Var_error_report r e
(*
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val ty_locn = pty_locn Ty
              val real_type = (Type.deep_beta_eta_ty (Pretype.toType Ty)
                         handle e => raise (wrap_exn "Preterm" "check.Var" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the variable ", Name,
                       "\n\n"^locn.toString Locn^"\n\n",

                       "is constrained to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "which has kind\n\n", pkd(Type.kind_of real_type), "\n\n",

                       "but the type of a term must have kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (VarKindFail(Name, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end
*)
        )
    | check (c as Const (r as {Name, Thy, Ty, Locn})) =
       ((if not (is_debug()) then () else
                print ("\nChecking type of term const " ^ Name ^ ":\n"
                        ^ "  " ^ Pretype.pretype_to_string Ty ^ "\n");
         checkkind Ty;
         if not (is_debug()) then () else
                print ("\nChecked type of term const " ^ Name ^ ":\n"
                        ^ "  " ^ Pretype.pretype_to_string Ty ^ "\n");
(*
         if not (is_debug()) then () else
                print ("\nChecking kind of type of " ^ Name ^ " has kind ty.\n");
*)
         Prekind.unify (Pretype.pkind_of Ty) (Prekind.typ (Prerank.new_uvar()));
(*
         if not (is_debug()) then () else
                print ("\nChecked kind of type of " ^ Name ^ " has kind ty.\n");
*)
         c)
       handle e as HOL_ERR _ => Const_error_report r e
(*
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val ty_locn = pty_locn Ty
              val real_type = (Type.deep_beta_eta_ty (Pretype.toType Ty)
                         handle e => raise (wrap_exn "Preterm" "check.Const" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the constant ",
                       Thy^"$"^Name,
                       "\n\n"^locn.toString Locn^"\n\n",

                       "is constrained to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "which has kind\n\n", pkd(Type.kind_of real_type), "\n\n",

                       "but the type of a term must have kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (ConstKindFail(Name, Thy, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end
*)
        )
    | check (tm as Constrained {Ptm,Ty,Locn}) =
        (if is_debug() then print ("\nChecking type constraint of term:\n" ^
                                   Pretype.pretype_to_string Ty ^ "\n") else ();
         checkkind Ty;
         if is_debug() then print ("\nChecking type constraint of term has kind ty:\n" ^
                                   Pretype.pretype_to_string Ty ^ "\n") else ();
         Prekind.unify (Pretype.pkind_of Ty) (Prekind.typ (Prerank.new_uvar()))
         handle e as HOL_ERR _ => Constrained_error_report1 {Ptm=Ptm,Ty=Ty,Locn=Locn} e
(*
         handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                       origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 1
              val show_ranks = Feedback.get_tracefn "ranks"
              val tmp2 = show_ranks()
              val _   = Feedback.set_trace "ranks" 1
              val real_term = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Ptm))
                              handle e => (check Ptm; Feedback.set_trace "kinds" tmp; raise e)
              val ty_locn = pty_locn Ty
              val real_type = Type.deep_beta_eta_ty (Pretype.toType Ty)
                              handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nKind inference failure: the term\n\n",
                       ptm real_term,
                       "\n\n"^locn.toString (locn Ptm)^"\n\n",

                       "is constrained to have the type\n\n",
                       pty real_type,
                       "\n\n"^locn.toString ty_locn^"\n\n",

                       "which has kind\n\n", pkd(Type.kind_of real_type), "\n\n",

                       "but the type of a term must have kind ty\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            Feedback.set_trace "ranks" tmp2;
            tcheck_say message;
            last_tcerror := SOME (ConstrainKindFail(real_term, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end
*)
          ;
          if is_debug() then print ("\nChecking term that has type constraint:\n" ^
                                   preterm_to_string Ptm ^ "\n") else ();
         let val Ptm' = check Ptm
             val Ptm_ty = Pretype.deep_beta_eta_ty (ptype_of Ptm')
         in if Pretype.is_univ_type Ptm_ty andalso Pretype.is_not_univ_type Ty then
            (if not(is_debug()) then () else
               print ("\nInserting type arguments to the constrained term\n" ^ preterm_to_string Ptm' ^ "\n");
               check (Constrained{Ptm=mk_not_tyabs Ptm', Ty=Ty, Locn=Locn}))
            else
               (if is_debug() then print ("\nChecking term has same type as type constraint:\n")
                              else ();
                Pretype.set_error_report (preterm_to_string (beta_eta_conv_ty_in_term tm),
                                          Constrained_error_report2 {Ptm=Ptm',Ty=Ty,Locn=Locn});
                Pretype.unify Ptm_ty Ty;
                Constrained{Ptm=Ptm', Ty=Ty, Locn=Locn})
       handle e as HOL_ERR _ => Constrained_error_report2 {Ptm=Ptm',Ty=Ty,Locn=Locn} e
(*
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val real_term = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 Ptm'))
                              handle e => (check Ptm; Globals.show_types := tmp; raise e)
              val real_type = Type.deep_beta_eta_ty (Pretype.toType Ty)
                              handle e => (Globals.show_types := tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nType inference failure: the term\n\n",
                       ptm real_term,
                       "\n\n", locn.toString (locn Ptm), "\n\n",
                       if (is_atom Ptm') then ""
                       else("which has type\n\n" ^
                            pty(Term.type_of real_term) ^ "\n\n"),
                       "can not be constrained to be of type\n\n",
                       pty real_type,
                       "\n\nunification failure message: ", message, "\n"]
          in
            Globals.show_types := tmp;
            last_tcerror := SOME (ConstrainFail(real_term, real_type), Locn);
            tcheck_say message;
            raise ERRloc"typecheck" Locn message
          end
*)
         end)
    | check (tm as Overloaded{Name,Ty,Info,Locn}) =
        (if is_debug() then print ("\nChecking overloaded term " ^ Name ^ "'s type:\n"
                                      ^ Pretype.pretype_to_string Ty ^ "\n") else ();
         checkkind Ty;
         if is_debug() then print ("\nChecked  overloaded term " ^ Name ^ "'s type:\n"
                                      ^ Pretype.pretype_to_string Ty ^ "\n") else ();
         tm
        )
    | check (tm as Pattern{Ptm,Locn}) =
        (if is_debug() then print ("\nChecking pattern term:\n") else ();
         let val Ptm' = check Ptm
         in
           if is_debug() then print ("\nChecked  pattern term:\n") else ();
           Pattern{Ptm = Ptm', Locn = Locn}
         end
        )
(*
    | check tm = (if not (is_debug()) then ()
                          else print "<<< otherwise term pattern\n";
                        let val tm' = tm
                        in if not (is_debug()) then ()
                             else print (">>> " ^ preterm_to_string tm' ^ "\n");
                           tm'
                         end)
*)
    | check tm = tm
  fun ho_check tm =
    let val _ = Pretype.begin_homs()
        val tm' = check tm
        val _ = Pretype.resolve_ho_matches()
        val _ = Pretype.end_homs()
    in tm'
    end
    handle e as HOL_ERR{origin_structure="Pretype",
                        origin_function="unify",message}
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val real_term = Term.beta_eta_conv_ty_in_term (to_term (overloading_resolution0 tm))
                              handle e => (check tm; Globals.show_types := tmp; raise e)
              val Locn = locn tm
              val message =
                  String.concat
                      [
                       "\nType inference failure: the term\n\n",
                       ptm real_term,
                       "\n\n", locn.toString Locn, "\n\n",
                       "which has type\n\n" ^
                            pty(Term.type_of real_term) ^ "\n\n",
                       "can not have its types be unified by higher-order matching",
                       "\n\nunification failure message: ", message, "\n"]
          in
            Pretype.end_homs();
            Globals.show_types := tmp;
            (* last_tcerror := SOME (TyHOmatchFail, Locn); *)
            tcheck_say message;
            raise ERRloc"typecheck" Locn message
          end
       | e as HOL_ERR _ => (Pretype.end_homs(); raise e)
in
  ho_check
end
end (* local *)

(**)
fun evade_free_tvs tm =
(*   inst (map (fn tv => (Pretype.all_new_uvar() |-> tv)) (type_vars_in_term tm)) tm *)
  let val dbvs = Pretype.distinguish_btyvars
      fun evad cx (Var{Name,Ty,Locn}) =
                   Var{Name=Name,Ty=dbvs cx Ty,Locn=Locn}
        | evad cx (Const{Name,Thy,Ty,Locn}) =
                   Const{Name=Name,Thy=Thy,Ty=dbvs cx Ty,Locn=Locn}
        | evad cx (Comb{Rator,Rand,Locn}) =
                   Comb{Rator=evad cx Rator,Rand=evad cx Rand,Locn=Locn}
        | evad cx (TyComb{Rator,Rand,Locn}) =
                   TyComb{Rator=evad cx Rator,Rand=dbvs cx Rand,Locn=Locn}
        | evad cx (Abs{Bvar,Body,Locn}) =
                   Abs{Bvar=evad cx Bvar,Body=evad cx Body,Locn=Locn}
        | evad cx (TyAbs{Bvar,Body,Locn}) =
               let open Pretype
                   val Bvar0 = the_var_type Bvar
                   val fvs = Lib.op_set_diff eq (type_vars_in_term Body) [Bvar0]
                   val Bvar' = variant_type (Lib.op_union eq cx fvs) Bvar0
                   val cx' = Bvar'::cx
               in if eq Bvar0 Bvar' then TyAbs{Bvar=Bvar,Body=evad cx' Body,Locn=Locn}
                  else let val theta = [Bvar0 |-> Bvar']
                           val Bvar1 = type_subst theta Bvar
                           val Body1 = inst theta Body
                       in TyAbs{Bvar=Bvar1,Body=evad cx' Body1,Locn=Locn}
                       end
               end
        | evad cx (tm as Antiq{Tm,Locn}) =
                   Antiq{Tm=(*Term.evade_tyvs cx*) Tm,Locn=Locn}
        | evad cx (Constrained{Ptm,Ty,Locn}) =
                   Constrained{Ptm=evad cx Ptm,Ty=dbvs cx Ty,Locn=Locn}
        | evad cx (Pattern{Ptm,Locn}) =
                   Pattern{Ptm=evad cx Ptm,Locn=Locn}
        | evad cx (Overloaded{Name,Ty,Info,Locn}) =
                   Overloaded{Name=Name,Ty=dbvs cx Ty,Info=Info,Locn=Locn}
  in evad (type_vars_in_term tm) tm
  end
(**)


fun typecheck_phase1 pfns ptm =
    TC pfns (*ptm*) (**) (evade_free_tvs ptm) (**)
    handle phase1_exn(l,s,ty) => let
           in
             case pfns of
               NONE => (tcheck_say s; raise ERRloc "typecheck" l s)
             | SOME (_, typ, _) =>
               (tcheck_say
                    (String.concat [s , "Wanted it to have type:  ",
                                    typ ty, "\n"]);
                raise ERRloc "typecheck" l s)
           end


val post_process_term = ref (I : term -> term);

fun typecheck pfns ptm0 = let
  val ptm1 = TC pfns (*ptm0*) (**) (evade_free_tvs ptm0) (**)
  val _ = if not (is_debug()) then () else
           (print "\n=== End of Parsing Pass 1; Beginning of Pass 2 ===\n")
  val ptm2 = overloading_resolution0 ptm1
  val ptm = TC pfns ptm2
in
  !post_process_term (remove_case_magic (to_term pfns ptm))
end handle phase1_exn(l,s,ty) =>
           case pfns of
             NONE => (tcheck_say (locn.toString l ^ ": " ^ s);
                      raise ERRloc "typecheck" l s)
           | SOME (_, typ, _) =>
             (tcheck_say
                  (String.concat [locn.toString l, ": ", s,
                                  "Wanted it to have type:  ",
                                  typ ty, "\n"]);
              raise ERRloc "typecheck" l s)

end; (* Preterm *)
