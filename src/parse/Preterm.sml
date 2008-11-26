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
fun tmlist_tyvs tlist = 
  List.foldl (fn (t,acc) => Lib.union (Term.type_vars_in_term t) acc) [] tlist


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

val op --> = Pretype.-->

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
fun term_to_preterm avds t = let 
  open optmonad
  infix >> >-
  fun gen avds ty = Pretype.rename_tv avds (Pretype.fromType ty)
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
      | TYLAMB(a,bod) => let val (s,_,_) = dest_vartype_opr a
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

fun eq_info {actual_ops=ops1, base_type=bty1, tyavoids=avds1}
            {actual_ops=ops2, base_type=bty2, tyavoids=avds2}
    = all2 Term.eq ops1 ops2 andalso Type.abconv_ty bty1 bty2 andalso all2 Type.abconv_ty avds1 avds2

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
      | Pattern {Ptm,...}            => cl Ptm
      | Overloaded{Name,Ty,Locn,...} => 
          raise ERRloc "clean" Locn "Overload term remains"
 in 
  cl
 end

(*---------------------------------------------------------------------------*
 * The free variables of a preterm. Tail recursive (from Ken Larsen).        *
 *---------------------------------------------------------------------------*)

fun from_term_var tm = let val (s,ty) = Term.dest_var tm
                       in Var{Name=s, Ty=Pretype.fromType ty, Locn=locn.Loc_None}
                       end

local fun FV (v as Var _) A k              = k (Lib.op_insert eq v A)
        | FV (Comb{Rator,Rand,...}) A k    = FV Rator A (fn q => FV Rand q k)
        | FV (TyComb{Rator,Rand,...}) A k  = FV Rator A k
        | FV (Abs{Bvar,Body,...}) A k      = FV Body A k
        | FV (TyAbs{Bvar,Body,...}) A k    = FV Body A k
        | FV (Constrained{Ptm,Ty,...}) A k = FV Ptm A k
        | FV (Pattern{Ptm,...}) A k        = FV Ptm A k
        | FV (Antiq{Tm,...}) A k = k (Lib.op_union eq (map from_term_var (Term.free_vars Tm)) A)
        | FV _ A k = k A
in
fun free_vars tm = FV tm [] Lib.I
end;

val has_free_uvar = Pretype.has_free_uvar

fun kindVars ptm =  (* the prekind variables in a preterm *)
  case ptm of
    Var{Ty,...}             => Pretype.kindvars Ty
  | Const{Ty,...}           => Pretype.kindvars Ty
  | Comb{Rator,Rand,...}    => Lib.union (kindVars Rator) (kindVars Rand)
  | TyComb{Rator,Rand,...}  => Lib.union (kindVars Rator) (Pretype.kindvars Rand)
  | Abs{Bvar,Body,...}      => Lib.union (kindVars Bvar) (kindVars Body)
  | TyAbs{Bvar,Body,...}    => Lib.union (Pretype.kindvars Bvar) (kindVars Body)
  | Antiq{Tm,...}           => [] (* kindVars (fromTerm Tm) *)
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
  | Antiq{Tm,...}           => map Type.dest_vartype (Term.type_vars_in_term Tm)
  | Constrained{Ptm,Ty,...} => Lib.union (tyVars Ptm) (Pretype.tyvars Ty)
  | Pattern{Ptm,...}        => tyVars Ptm
  | Overloaded _            => raise Fail "Preterm.tyVars: applied to \
                                          \Overloaded";

(*-----------------------------------------------------------------------------*
 * The free type variables of a lambda term. Tail recursive (from Ken Larsen). *
 *-----------------------------------------------------------------------------*)

local val union = Lib.op_union Pretype.eq
      val subtract = Lib.op_set_diff Pretype.eq
      val type_vars = Pretype.type_vars
      fun tyV (Var{Ty,...}) k             = k (type_vars Ty)
        | tyV (Const{Ty,...}) k           = k (type_vars Ty)
        | tyV (Comb{Rator,Rand,...}) k    = tyV Rand (fn q1 =>
                                            tyV Rator(fn q2 => k (union q2 q1)))
        | tyV (TyComb{Rator,Rand,...}) k  = tyV Rator (fn q  =>
                                            k (union q (type_vars Rand)))
        | tyV (Abs{Bvar,Body,...}) k      = tyV Body (fn q1 =>
                                            tyV Bvar (fn q2 => k (union q2 q1)))
        | tyV (TyAbs{Bvar,Body,...}) k    = tyV Body (fn q => k (subtract q [Bvar]))
        | tyV (Antiq{Tm,...}) k           = map Pretype.fromType (Term.type_vars_in_term Tm)
        | tyV (Constrained{Ptm,Ty,...}) k = tyV Ptm (fn q =>
                                            k (union q (type_vars Ty)))
        | tyV (Pattern{Ptm,...}) k        = tyV Ptm k
        | tyV (Overloaded _) k            = k []
      fun tyVs (t::ts) k           = tyV t (fn q1 =>
                                     tyVs ts (fn q2 => k (union q2 q1)))
        | tyVs [] k                = k []
in
fun type_vars_in_term tm = tyV tm Lib.I
fun type_vars_in_terml tms = tyVs tms Lib.I
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

fun to_term tm =
    if !Globals.guessing_tyvars then let
        fun cleanup tm = let
          open optmonad
          infix >> >-
          val clean = Pretype.clean o Pretype.remove_made_links
          fun prepare Ty =
              let val Ty' = if Pretype.do_beta_conv_types()
                            then Pretype.deep_beta_conv_ty Ty
                            else Ty
              in Pretype.replace_null_links Ty' >- (fn _ => return Ty')
              end
        in
          case tm of
            Var{Name,Ty,...} => prepare Ty >- (fn Ty' =>
                                return (Term.mk_var(Name, clean Ty')))
            (* in this Var case, and in the Const case below, have to use 
               "... >- (fn _ => ..." rather than the >> 'equivalent' because 
               the former ensures that the references in Ty get updated 
               before the call to clean occurs. *)
          | Const{Name,Thy,Ty,...} =>
                prepare Ty >- (fn Ty' =>
                return (Term.mk_thy_const{Name=Name, Thy=Thy, Ty=clean Ty'}))
          | Comb{Rator, Rand,...} => let 
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
                  end
                in
                  cleanup Ptm >- (fn f => 
                  mmap cleanup args >- (fn args' => 
                  return (doit f args')))
                end
              | _ => cleanup f >- (fn f_t => 
                     mmap cleanup args >- (fn args' => 
                     return (list_mk_comb(f_t, args'))))
            end
          | TyComb{Rator, Rand,...} => cleanup Rator >- (fn Rator'
                                  => prepare Rand >- (fn Rand'
                                  => return (Term.mk_tycomb(Rator', clean Rand'))))
          | Abs{Bvar, Body,...} => cleanup Bvar >- (fn Bvar'
                                => cleanup Body >- (fn Body'
                                => return (Term.mk_abs(Bvar', Body'))))
          | TyAbs{Bvar, Body,...} => prepare Bvar >- (fn Bvar'
                                => cleanup Body >- (fn Body'
                                => return (Term.mk_tyabs(clean Bvar', remove_case_magic Body'))))
          | Antiq{Tm,...} => return Tm
          | Constrained{Ptm,...} => cleanup Ptm
          | Overloaded _ => raise ERRloc "to_term" (locn tm)
                                         "applied to Overloaded"
          | Pattern{Ptm,...} => cleanup Ptm
        end
        val K = kindVars tm
        val V = tyVars tm
        val ((newK,newV), result) = cleanup tm (K,V)
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
                (* let val ty = if Pretype.do_beta_conv_types()
                                then Pretype.deep_beta_conv_ty ty
                                else ty
                        val _ = Pretype.replace_null_links ty (Pretype.kindvars ty, Pretype.tyvars ty)
                 in Pretype.clean (Pretype.remove_made_links ty)
                 end *)
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
  | Constrained{Ptm, Ty, Locn} => Constrained{Ptm = remove_overloading_phase1 Ptm, Ty = Ty, Locn = Locn}
(*| Pattern{Ptm, Locn} => Pattern{Ptm = remove_overloading_phase1 Ptm, Locn = Locn}*) (* should this be here? *)
  | Overloaded{Name,Ty,Info,Locn} => let 
      fun testfn t = let
        open Term
        val possty = type_of t
        val avds = map Type.dest_vartype (tmlist_tyvs (free_vars t))
        val pty0 = Pretype.fromType possty
        val pty = Pretype.rename_typevars avds pty0
      in
        Pretype.can_unify Ty pty
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
              val pty = Pretype.rename_typevars [] (Pretype.fromType ty)
              val _ = Pretype.unify pty Ty
            in
              Const{Name=Name, Thy=Thy, Ty=pty, Locn=Locn}
            end
          else let 
              val avds = map Type.dest_vartype (tmlist_tyvs (free_vars t))
            in
              Pattern{Ptm = term_to_preterm avds t, Locn = Locn}
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
  fun unify t1 t2 = opt2seq (Pretype.safe_unify t1 t2)
  (* Note that the order of the term traversal here is very important as
     the sub-terms "pulled out" will be "put back in" later under the
     assumption that the list is in the right order.  The traversal that
     puts the constants into the place of the Overloaded nodes must also
     traverse in the same order:
       Rator before Rand, Bvar before Body
     In accumulator style, that looks as below *)
  fun overloaded_subterms acc ptm =
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
  val overloads = overloaded_subterms [] ptm
  val _ = if length overloads >= 30
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
                val pty = Pretype.rename_typevars [] pty0
              in
                unify pty Ty >> 
                return (Const{Name=n, Ty=Ty, Thy=thy, Locn=Locn})
              end
            else let 
                val avds = map Type.dest_vartype (tmlist_tyvs (free_vars t))
                val ptm = term_to_preterm avds t 
                val pty = ptype_of ptm
              in
                unify pty Ty >>
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
  fun apply_subst subst = app (fn (r, value) => r := Pretype.SOMEU value) subst
  fun do_csubst clist ptm =
    case clist of
      [] => (ptm, [])
    | (c::cs) => let
      in
        (* must take care to keep order of traversal same as traversal in
           overloaded_subterms above *)
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
        | Overloaded _ => (c,cs)
        | _ => (ptm, clist)
      end
in
  case cases result of
    NONE => raise ERRloc "do_overloading_removal" (locn ptm0)
                         "Couldn't find a sensible resolution for \
                         \overloaded constants"
  | SOME ((env as (kenv,renv,tenv),clist),xs) =>
      if not (!Globals.guessing_overloads)
         orelse !Globals.notify_on_tyvar_guess
      then
        case cases xs of
          NONE => (apply_subst tenv; #1 (do_csubst clist ptm))
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
            apply_subst tenv;
            #1 (do_csubst clist ptm)
          end
      else
        (apply_subst tenv; #1 (do_csubst clist ptm))
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
           (tcheck_say s ; raise ERRloc "overloading_resolution" l s)

(*---------------------------------------------------------------------------
 * Type inference for HOL terms. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained{Ptm,...}) = is_atom Ptm
(*| is_atom (Pattern{Ptm,...}) = is_atom Ptm*)
  | is_atom (Overloaded _) = true
  | is_atom (t as Comb{Rator,Rand,...}) =
      Literal.is_numeral (to_term (overloading_resolution t)) orelse
      Literal.is_numeral (to_term (overloading_resolution Rand)) andalso
        (case Rator
          of Overloaded{Name,...} => Name = fromNum_str
           | Const{Name,...} => Name = nat_elim_term
           | _ => false)
  | is_atom t = false

fun mk_tycomb(tm,ty) = TyComb{Rator=tm, Rand=ty, Locn=locn.Loc_None}

fun list_mk_tycomb(tm,[]) = tm
  | list_mk_tycomb(tm,ty::tys) = list_mk_tycomb(mk_tycomb(tm,ty),tys)

local
  val op --> = Pretype.-->
  val op ==> = Prekind.==>
  fun default_kdprinter x = "<kind>"
  fun default_typrinter x = "<hol_type>"
  fun default_tmprinter x = "<term>"
in
fun TC printers = let
  val (ptm, pty, pkd) =
      case printers
       of SOME (x,y,z) =>
          let val kdprint = z
              fun typrint ty =
                  if Type.is_con_type ty
                  then (y ty ^ " " ^ z (Type.kind_of ty)
                             ^ " :<= " ^ Int.toString (Type.rank_of ty))
                  else y ty
              fun tmprint tm = x tm
                (*if Term.is_const tm
                  then (x tm ^ " " ^ y (Term.type_of tm))
                  else x tm*)
          in
            (tmprint, typrint, kdprint)
          end
        | NONE => (default_tmprinter, default_typrinter, default_kdprinter)
  fun prk rk = Int.toString rk
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
              val Rator_ty = Pretype.toType (ptype_of Rator)
                             handle e => raise (wrap_exn "Preterm" "ptype_of.TyComb" e)
              val Rator' = to_term (overloading_resolution0 Rator)
                           handle e => (Globals.show_types := tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand' = (Pretype.toType Rand
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
           val ty = Pretype.deep_beta_conv_ty (ptype_of tm)
           val (bvars,body) = strip_univ_type ty
           val args = map (fn bvar => new_uvar(pkind_of bvar,Prerank.new_uvar())) bvars
       in list_mk_tycomb(tm, args)
       end
  fun check(Comb{Rator, Rand, Locn}) =
      (let val Rator' = check Rator;
           val Rand'  = check Rand;
           val Rator_ty = Pretype.deep_beta_conv_ty (ptype_of Rator')
           val Rand_ty = Pretype.deep_beta_conv_ty (ptype_of Rand')
       in if Pretype.is_univ_type Rator_ty then
             check (Comb{Rator=mk_not_tyabs Rator', Rand=Rand', Locn=Locn})
          else if Pretype.is_univ_type Rand_ty andalso
                  (Pretype.is_not_univ_type (fst (Pretype.dom_rng Rator_ty)) handle HOL_ERR _ => false) then
             check (Comb{Rator=Rator', Rand=mk_not_tyabs Rand', Locn=Locn})
          else
             (Pretype.unify Rator_ty (Rand_ty --> Pretype.all_new_uvar());
              Comb{Rator=Rator', Rand=Rand', Locn=Locn})
             handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                           origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _   = Globals.show_types := true
              val Rator_tm = to_term (overloading_resolution0 Rator')
                handle e => (check Rator'; Globals.show_types := tmp; raise e)
              val Rand_tm  = to_term (overloading_resolution0 Rand')
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
       end)
    | check(TyComb{Rator, Rand, Locn}) =
         (let val Rator' = check Rator
              val _  = checkkind Rand
              val Rator_ty = ptype_of Rator'
              val (bvar,body) = Pretype.dest_univ_type Rator_ty
                                handle HOL_ERR _ => let
                                     val s = "'a"
                                     val kd = Prekind.new_uvar()
                                     val rk = Prerank.new_uvar()
                                     val bvar = Pretype.PT(Pretype.Vartype(s,kd,rk),locn.Loc_None) (* choose either this or next line *)
                                     (*val bvar = new_uvar(kd,rk)*)
                                     val body = Pretype.mk_app_type(Pretype.all_new_uvar(), bvar)
                                     val univ_ty = Pretype.mk_univ_type(bvar, body)
                                 in checkkind univ_ty;
                                    Pretype.unify Rator_ty univ_ty;
                                    (bvar,body)
                                 end
          in
             Prekind.unify (Pretype.pkind_of Rand) (Pretype.pkind_of bvar);
             Prerank.unify_le (Pretype.prank_of Rand) (* <= *) (Pretype.prank_of bvar);
             TyComb{Rator=Rator', Rand=Rand, Locn=Locn}
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val Rator_tm = to_term (overloading_resolution0 Rator')
                         handle e => (Globals.show_types := tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Pretype.toType Rand
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
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val Rator_tm = to_term (overloading_resolution0 Rator')
                       handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Pretype.toType Rand
                       handle e => (Feedback.set_trace "kinds" tmp; raise e)
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
            Feedback.set_trace "kinds" tmp;
            tcheck_say message;
            last_tcerror := SOME (TyAppKindFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify_le",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val Rator_tm = to_term (overloading_resolution0 Rator')
                             handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val Rator_ty = Type.deep_beta_conv_ty (Term.type_of Rator_tm)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand_ty = Pretype.toType Rand
                            handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val message =
                  String.concat
                      [
                       "\nRank inference failure: unable to infer a type \
                       \for the application of the term\n\n",
                       ptm Rator_tm,
                       "\n\n"^locn.toString (locn Rator)^"\n\n",

                       if Type.is_univ_type Rator_ty then
                           "whose argument must have rank <= " ^
                           prk(Type.rank_of (#1 (Type.dest_univ_type Rator_ty))) ^ "\n\n"
                       else "which is not a universal type\n\n",
                       if (is_atom Rator') then ""
                       else ("which has type\n\n" ^
                             pty Rator_ty ^ "\n\n"),
                       "to the type\n\n",
                       pty Rand_ty,
                       "\n\n"^locn.toString rand_locn^"\n\n",

                       if (Pretype.is_atom Rand) then ""
                       else ("which has rank\n\n" ^
                             prk(Type.rank_of Rand_ty) ^ "\n\n"),

                       "rank unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            tcheck_say message;
            last_tcerror := SOME (TyAppRankFail(Rator_tm,Rand_ty), rand_locn);
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
          end)
    | check (  Abs{Bvar, Body, Locn}) = let val Bvar' = check Bvar
                                            val Body' = check Body
                                         in Abs{Bvar=Bvar', Body=Body', Locn=Locn}
                                        end
    | check (TyAbs{Bvar, Body, Locn}) = let val _ = checkkind Bvar
                                            val Bvar' = Pretype.the_var_type Bvar
                                            val Body' = check Body
                                         in if mem Bvar' (Pretype.type_varsl (map ptype_of (free_vars Body)))
                                            then raise ERRloc "typecheck.TyAbs" Locn
                                                   "bound type variable occurs free in the type of a free variable of the body"
                                            else TyAbs{Bvar=Bvar, Body=Body', Locn=Locn}
                                        end
    | check (v as Var {Name, Ty, Locn}) =
       ((checkkind Ty; Prekind.unify (Pretype.pkind_of Ty) Prekind.typ;
         v)
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val ty_locn = pty_locn Ty
              val real_type = (Pretype.toType Ty
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

                       "but the type of a term must have kind ", pkd Kind.typ, "\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            tcheck_say message;
            last_tcerror := SOME (VarKindFail(Name, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end)
    | check (c as Const {Name, Thy, Ty, Locn}) =
       ((checkkind Ty; Prekind.unify (Pretype.pkind_of Ty) Prekind.typ; c)
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val ty_locn = pty_locn Ty
              val real_type = (Pretype.toType Ty
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

                       "but the type of a term must have kind ", pkd Kind.typ, "\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            tcheck_say message;
            last_tcerror := SOME (ConstKindFail(Name, Thy, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end)
    | check (Constrained{Ptm,Ty,Locn}) =
        (checkkind Ty;
         Prekind.unify (Pretype.pkind_of Ty) Prekind.typ
         handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                       origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_term = to_term (overloading_resolution0 Ptm)
                              handle e => (check Ptm; Feedback.set_trace "kinds" tmp; raise e)
              val ty_locn = pty_locn Ty
              val real_type = Pretype.toType Ty
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

                       "but the type of a term must have kind ", pkd Kind.typ, "\n\n",

                       "kind unification failure message: ", message, "\n"]
          in
            Feedback.set_trace "kinds" tmp;
            tcheck_say message;
            last_tcerror := SOME (ConstrainKindFail(real_term, real_type), ty_locn);
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end;
         let val Ptm' = check Ptm
             val Ptm_ty = Pretype.deep_beta_conv_ty (ptype_of Ptm')
         in if Pretype.is_univ_type Ptm_ty andalso Pretype.is_not_univ_type Ty then
               check (Constrained{Ptm=mk_not_tyabs Ptm', Ty=Ty, Locn=Locn})
            else
               (Pretype.unify Ptm_ty Ty;
                Constrained{Ptm=Ptm', Ty=Ty, Locn=Locn})
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val real_term = to_term (overloading_resolution0 Ptm')
                              handle e => (check Ptm; Globals.show_types := tmp; raise e)
              val real_type = Pretype.toType Ty
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
         end)
    | check tm = tm
in 
  check
end
end (* local *)

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
        

fun typecheck_phase1 pfns ptm =
    TC pfns (evade_free_tvs ptm)
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
  val ptm0' = TC pfns (evade_free_tvs ptm0)
  val ptm = overloading_resolution0 ptm0'
in
  !post_process_term (remove_case_magic (to_term ptm))
end handle phase1_exn(l,s,ty) =>
           case pfns of
             NONE => (tcheck_say s; raise ERRloc "typecheck" l s)
           | SOME (_, typ, _) =>
             (tcheck_say
                  (String.concat [s, "Wanted it to have type:  ",
                                  typ ty, "\n"]);
              raise ERRloc "typecheck" l s)


end; (* Preterm *)
