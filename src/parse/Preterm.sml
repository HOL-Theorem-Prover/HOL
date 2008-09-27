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

datatype preterm = Var    of {Name:string,  Ty:pretype, Locn:locn.locn}
                 | Const  of {Name:string,  Thy:string, Ty:pretype, Locn:locn.locn}
                 | Overloaded of overinfo
                 | Comb   of {Rator:preterm, Rand:preterm, Locn:locn.locn}
                 | TyComb of {Rator:preterm, Rand:pretype, Locn:locn.locn}
                 | Abs    of {Bvar:preterm, Body:preterm, Locn:locn.locn}
                 | TyAbs  of {Bvar:pretype, Body:preterm, Locn:locn.locn}
                 | Constrained of {Ptm:preterm, Ty:pretype, Locn:locn.locn}
                 | Antiq  of {Tm:Term.term, Locn:locn.locn}
              (* | HackHack of bool -> bool *)
              (* Because of the Locn fields, preterms should *not* be compared
                 with the built-in equality, but should use eq defined below.
                 To check this has been done everywhere, uncomment this constructor. *)

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

fun pty_locn (Pretype.PT(_,locn)) = locn

(*---------------------------------------------------------------------------
     Location-ignoring equality for preterms.
 ---------------------------------------------------------------------------*)

val eq_type = Pretype.eq

fun eq (Var{Name=Name,Ty=Ty,...})                  (Var{Name=Name',Ty=Ty',...})                   = Name=Name' andalso eq_type Ty Ty'
  | eq (Const{Name=Name,Thy=Thy,Ty=Ty,...})        (Const{Name=Name',Thy=Thy',Ty=Ty',...})        = Name=Name' andalso Thy=Thy' andalso eq_type Ty Ty'
  | eq (Overloaded{Name=Name,Ty=Ty,Info=Info,...}) (Overloaded{Name=Name',Ty=Ty',Info=Info',...}) = Name=Name' andalso eq_type Ty Ty' andalso Info=Info'
  | eq (Comb{Rator=Rator,Rand=Rand,...})           (Comb{Rator=Rator',Rand=Rand',...})            = eq Rator Rator' andalso eq Rand Rand'
  | eq (TyComb{Rator=Rator,Rand=Rand,...})         (TyComb{Rator=Rator',Rand=Rand',...})          = eq Rator Rator' andalso eq_type Rand Rand'
  | eq (Abs{Bvar=Bvar,Body=Body,...})              (Abs{Bvar=Bvar',Body=Body',...})               = eq Bvar Bvar' andalso eq Body Body'
  | eq (TyAbs{Bvar=Bvar,Body=Body,...})            (TyAbs{Bvar=Bvar',Body=Body',...})             = eq_type Bvar Bvar' andalso eq Body Body'
  | eq (Constrained{Ptm=Ptm,Ty=Ty,...})            (Constrained{Ptm=Ptm',Ty=Ty',...})             = eq Ptm Ptm' andalso Ty=Ty'
  | eq (Antiq{Tm=Tm,...})                          (Antiq{Tm=Tm',...})                            = Tm=Tm'
  | eq  _                                           _                                             = false

(*---------------------------------------------------------------------------
     Simple map from a preterm to a term. The argument "shr" maps from
     pretypes to types. Should Overloaded nodes be translated, or
     should the process fail if one is encountered? Currently, we
     attempt to make some sort of constant (non-deterministic), but we
     could just as well fail, since Overloaded nodes should be gone
     by the time clean is called.

     shr takes a location for now, until Preterm has a location built-in.
 ---------------------------------------------------------------------------*)

val clean_type = fn ty => Pretype.toType ty

fun clean shr =
 let fun
   cl(Var{Name,Ty,Locn})            = Term.mk_var(Name, shr Locn Ty)
 | cl(Const{Name,Thy,Ty,Locn})      = (Term.mk_thy_const{Name=Name,Thy=Thy,Ty=shr Locn Ty}
             handle e => raise (wrap_exn "Preterm" "clean" e))
 | cl(Comb{Rator,Rand,...})         = Term.mk_comb(cl Rator,cl Rand)
 | cl(TyComb{Rator,Rand,...})       = Term.mk_tycomb(cl Rator,clean_type Rand)
 | cl(Abs{Bvar,Body,...})           = Term.mk_abs(cl Bvar, cl Body)
 | cl(TyAbs{Bvar,Body,...})         = Term.mk_tyabs(clean_type Bvar, cl Body)
 | cl(Antiq{Tm,...})                = Tm
 | cl(Constrained{Ptm,...})         = cl Ptm
 | cl(Overloaded{Name,Ty,Locn,...}) = Term.mk_const(Name, shr Locn Ty)
 in cl
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
  | Overloaded _            => raise Fail "Preterm.kindVars: applied to Overloaded";

fun tyVars ptm =  (* the pretype variables in a preterm *)
  case ptm of
    Var{Ty,...}             => Pretype.tyvars Ty
  | Const{Ty,...}           => Pretype.tyvars Ty
  | Comb{Rator,Rand,...}    => Lib.union (tyVars Rator) (tyVars Rand)
  | TyComb{Rator,Rand,...}  => Lib.union (tyVars Rator) (Pretype.tyvars Rand)
  | Abs{Bvar,Body,...}      => Lib.union (tyVars Bvar) (tyVars Body)
  | TyAbs{Bvar,Body,...}    => Lib.union (Pretype.tyvars Bvar) (tyVars Body)
  | Antiq{Tm,...}           => map Type.dest_vartype (Term.type_vars_in_term Tm)
  | Constrained{Ptm,Ty,...} => Lib.union (tyVars Ptm) (Pretype.tyvars Ty)
  | Overloaded _            => raise Fail "Preterm.tyVars: applied to Overloaded";


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
        in
          case tm of
            Var{Name,Ty,...} => Pretype.replace_null_links Ty >- (fn _ =>
                                return (Term.mk_var(Name, clean Ty)))
          | Const{Name,Thy,Ty,...} =>
                Pretype.replace_null_links Ty >- (fn _ =>
                return (Term.mk_thy_const{Name=Name, Thy=Thy, Ty=clean Ty}))
          | Comb{Rator, Rand,...} => cleanup Rator >- (fn Rator'
                                  => cleanup Rand  >- (fn Rand'
                                  => return (Term.mk_comb(Rator', Rand'))))
          | TyComb{Rator, Rand,...} => cleanup Rator >- (fn Rator'
                                  => Pretype.replace_null_links Rand >- (fn _
                                  => return (Term.mk_tycomb(Rator', clean Rand))))
          | Abs{Bvar, Body,...} => cleanup Bvar >- (fn Bvar'
                                => cleanup Body >- (fn Body'
                                => return (Term.mk_abs(Bvar', Body'))))
          | TyAbs{Bvar, Body,...} => Pretype.replace_null_links Bvar >- (fn _
                                => cleanup Body >- (fn Body'
                                => return (Term.mk_tyabs(clean Bvar, remove_case_magic Body'))))
          | Antiq{Tm,...} => return Tm
          | Constrained{Ptm,...} => cleanup Ptm
       (* | Constrained{Ptm,Ty,...} => Pretype.replace_null_links Ty >- (fn _
                                    => cleanup Ptm) *)
          | Overloaded _ => raise ERRloc "to_term" (locn tm)
                                         "applied to Overloaded"
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
                 (* let val _ = Pretype.replace_null_links ty (Pretype.kindvars ty, Pretype.tyvars ty)
                 in Pretype.clean (Pretype.remove_made_links ty)
                 end *)
      in
        clean shr tm
      end


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
fun remove_overloading_phase1 ptm =
  case ptm of
    Comb{Rator, Rand, Locn} => Comb{Rator = remove_overloading_phase1 Rator,
                                    Rand = remove_overloading_phase1 Rand, Locn = Locn}
  | TyComb{Rator, Rand, Locn} => TyComb{Rator = remove_overloading_phase1 Rator,
                                    Rand = Rand, Locn = Locn}
  | Abs{Bvar, Body, Locn} => Abs{Bvar = remove_overloading_phase1 Bvar,
                                 Body = remove_overloading_phase1 Body, Locn = Locn}
  | TyAbs{Bvar, Body, Locn} => TyAbs{Bvar = Bvar,
                                 Body = remove_overloading_phase1 Body, Locn = Locn}
  | Constrained{Ptm, Ty, Locn} => Constrained{Ptm = remove_overloading_phase1 Ptm, Ty = Ty, Locn = Locn}
  | Overloaded{Name,Ty,Info,Locn} =>
     let fun testfn possty =
           let val pty0 = Pretype.fromType possty
               val pty = Pretype.rename_typevars pty0
           in Pretype.can_unify Ty pty
           end
         val possible_ops =
           List.filter (testfn o #Ty) (#actual_ops Info)
     in
      case possible_ops of
        [] =>
        raise phase1_exn(Locn, "No possible type for overloaded constant "^Name^"\n",
                         Pretype.toType Ty
                         handle e => raise (wrap_exn "Preterm" "remove_overloading_phase1" e))
      | [{Ty = ty,Name,Thy}] => let
          val pty = Pretype.rename_typevars (Pretype.fromType ty)
          val _ = Pretype.unify pty Ty
        in
          Const{Name=Name, Thy=Thy, Ty=pty, Locn=Locn (*??*) }
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
           (String.concat["many overloaded symbols in term: ",
                          "overloading resolution might take a long time."])
          else ()
  fun workfunction list =
    case list of
      [] => return []
    | ({Name,Ty,Info,Locn,...}:overinfo)::xs => let
        val actual_ops = #actual_ops Info
        fun tryit {Ty = ty, Name = n, Thy = thy} =
          let val pty0 = Pretype.fromType ty
              val pty = Pretype.rename_typevars pty0
          in unify pty Ty >> return (Const{Name=n, Ty=Ty, Thy=thy, Locn=Locn})
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
      "Couldn't find a sensible resolution for overloaded constants"
  | SOME ((env as (kenv,renv,tenv),clist),xs) =>
      if not (!Globals.guessing_overloads)
         orelse !Globals.notify_on_tyvar_guess
      then
        case cases xs
         of NONE => (apply_subst tenv; #1 (do_csubst clist ptm))
          | SOME _ => let in
              if not (!Globals.guessing_overloads)
                 then raise ERRloc "do_overloading_removal" (locn ptm0)
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
  | Constrained{Ptm, Ty, Locn} => Constrained{Ptm = remove_elim_magics Ptm, Ty = Ty, Locn = Locn}
  | Overloaded _ => raise Fail "Preterm.remove_elim_magics on Overloaded"


val overloading_resolution0 = remove_elim_magics o do_overloading_removal

fun overloading_resolution ptm =
    overloading_resolution0 ptm
    handle phase1_exn(l,s,ty) =>
           (Lib.say s ; raise ERRloc "overloading_resolution" l s)

(*---------------------------------------------------------------------------
 * Type inference for HOL terms. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained{Ptm,...}) = is_atom Ptm
  | is_atom (Overloaded _) = true
  | is_atom (t as Comb{Rator,Rand,...}) =
      Literal.is_numeral (to_term (overloading_resolution t)) orelse
      Literal.is_numeral (to_term (overloading_resolution Rand)) andalso
        (case Rator
          of Overloaded{Name,...} => Name = fromNum_str
           | Const{Name,...} => Name = nat_elim_term
           | _ => false)
  | is_atom t = false


local
  val op --> = Pretype.-->
in
fun ptype_of (Var{Ty, ...}) = Ty
  | ptype_of (Const{Ty, ...}) = Ty
  | ptype_of (Comb{Rator, ...}) = Pretype.chase (ptype_of Rator)
  | ptype_of (TyComb{Rator, Rand, ...}) =
      let val rator_ty = ptype_of Rator
      in let val (Bvar,Body) = Pretype.dest_univ_type rator_ty
             val Bvar1 = Pretype.the_var_type Bvar
         in Pretype.type_subst [Bvar1 |-> Rand] Body
         end (*handle Feedback.HOL_ERR {origin_structure="Pretype",
                                      origin_function="dest_univ_type",message}
             => raise ERR "ptype_of" message*)
      end
  | ptype_of (Abs{Bvar,Body,...}) = ptype_of Bvar --> ptype_of Body
  | ptype_of (TyAbs{Bvar,Body,...}) = Pretype.mk_univ_type(Bvar, ptype_of Body)
  | ptype_of (Constrained{Ty,...}) = Ty
  | ptype_of (Antiq{Tm,...}) = Pretype.fromType (Term.type_of Tm)
  | ptype_of (Overloaded {Ty,...}) = Ty
end;


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
          let val kdprint = Lib.say o z
              fun typrint ty =
                  if Type.is_con_type ty
                  then (Lib.say (y ty ^ " " ^ z (Type.kind_of ty)
                                      ^ " :<= " ^ Int.toString (Type.rank_of ty)))
                  else Lib.say (y ty)
              fun tmprint tm =
                  if Term.is_const tm
                  then (Lib.say (x tm ^ " " ^ y (Term.type_of tm)))
                  else Lib.say (x tm)
          in
            (tmprint, typrint, kdprint)
          end
        | NONE => (Lib.say o default_tmprinter, Lib.say o default_typrinter, Lib.say o default_kdprinter)
  fun prk rk = Lib.say (Int.toString rk)
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
          in
            Lib.say "\nType inference failure: unable to form \
                              \the application of the term\n\n";
            ptm Rator';
            Lib.say ("\n\n"^locn.toString (locn Rator)^"\n\n");

            (*if (is_atom Rator) then ()
            else*)(Lib.say"which has type\n\n";
                 pty(Term.type_of Rator');
                 Lib.say"\n\n");

            Lib.say "to the type\n\n"; pty Rand';
            Lib.say ("\n\n"^locn.toString rand_locn^"\n\n");
            Lib.say ("since the term does not have a universal type.\n");
            Globals.show_types := tmp;
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        end
    | ptype_of (Abs{Bvar,Body,...}) = ptype_of Bvar --> ptype_of Body
    | ptype_of (TyAbs{Bvar,Body,...}) = Pretype.mk_univ_type(Bvar, ptype_of Body)
    | ptype_of (Constrained{Ty,...}) = Ty
    | ptype_of (Antiq{Tm,...}) = Pretype.fromType (Term.type_of Tm)
    | ptype_of (Overloaded {Ty,...}) = Ty
  val checkkind = Pretype.checkkind (case printers of SOME (x,y,z) => SOME (y,z) | NONE => NONE)
  fun check(Comb{Rator, Rand, Locn}) =
      (check Rator;
       check Rand;
       Pretype.unify (ptype_of Rator)
       (ptype_of Rand --> Pretype.all_new_uvar())
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _   = Globals.show_types := true
              val Rator' = to_term (overloading_resolution0 Rator)
                handle e => (Globals.show_types := tmp; raise e)
              val Rand'  = to_term (overloading_resolution0 Rand)
                handle e => (Globals.show_types := tmp; raise e)
          in
            Lib.say "\nType inference failure: unable to infer a type \
                              \for the application of\n\n";
            ptm Rator';
            Lib.say ("\n\n"^locn.toString (locn Rator)^"\n\n");

            if (is_atom Rator) then ()
            else(Lib.say"which has type\n\n";
                 pty(Term.type_of Rator');
                 Lib.say"\n\n");

            Lib.say "to\n\n"; ptm Rand';
            Lib.say ("\n\n"^locn.toString (locn Rand)^"\n\n");

            if (is_atom Rand) then ()
            else(Lib.say"which has type\n\n";
                 pty(Term.type_of Rand');
                 Lib.say"\n\n");

            Lib.say ("unification failure message: "^message^"\n");
            Globals.show_types := tmp;
            raise ERRloc"typecheck" (locn Rand (* arbitrary *)) "failed"
          end)
    | check(TyComb{Rator, Rand, Locn}) =
         (check Rator;
          checkkind Rand;
          let open Pretype
              val rator_ty = ptype_of Rator
              val (bvar,body) = dest_univ_type rator_ty
                                handle HOL_ERR _ => let
                                     val s = "'a"
                                     val kd = Prekind.new_uvar()
                                     val rk = Prerank.new_uvar()
                                     val bvar = PT(Vartype(s,kd,rk),locn.Loc_None) (* choose either this or next line *)
                                     (*val bvar = new_uvar(kd,rk)*)
                                     val body = all_new_uvar()
                                 in Pretype.unify rator_ty (mk_univ_type(bvar, body));
                                    (bvar,body)
                                 end
          in
             Prekind.unify (pkind_of Rand) (pkind_of bvar);
             Prerank.unify_le (prank_of Rand) (* <= *) (prank_of bvar)
          end
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val Rator_ty = Pretype.toType (ptype_of Rator)
                         handle e => raise (wrap_exn "Preterm" "check.TyComb(Rator)" e)
              val Rator' = to_term (overloading_resolution0 Rator)
                handle e => (Globals.show_types := tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand' = Pretype.toType Rand
                         handle e => raise (wrap_exn "Preterm" "check.TyComb(Rand)" e)
                handle e => (Globals.show_types := tmp; raise e)
          in
            Lib.say "\nType inference failure: unable to form \
                              \the application of the term\n\n";
            ptm Rator';
            Lib.say ("\n\n"^locn.toString (locn Rator)^"\n\n");

            if (is_atom Rator) then ()
            else(Lib.say"which has type\n\n";
                 pty(Term.type_of Rator');
                 Lib.say"\n\n");

            Lib.say "to the type\n\n"; pty Rand';
            Lib.say ("\n\n"^locn.toString rand_locn^"\n\n");
            Lib.say ("since the term does not have a universal type.\n");
            Globals.show_types := tmp;
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val Rator_ty = Pretype.toType (ptype_of Rator)
                         handle e => raise (wrap_exn "Preterm" "check.TyComb3" e)
              val Rator' = to_term (overloading_resolution0 Rator)
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val Pretype.PT(_,rand_locn) = Rand
              val Rand' = (Pretype.toType Rand
                         handle e => raise (wrap_exn "Preterm" "check.TyComb4" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
          in
            Lib.say "\nKind inference failure: unable to infer a type \
                              \for the application of the term\n\n";
            ptm Rator';
            Lib.say ("\n\n"^locn.toString (locn Rator)^"\n\n");

            (*if (is_atom Rator) then ()
            else*)(Lib.say"which has type\n\n";
                 pty(Term.type_of Rator');
                 Lib.say"\n\n");

            Lib.say "to the type\n\n";
            pty Rand';
            Lib.say ("\n\n"^locn.toString rand_locn^"\n\n");

            if (Pretype.is_atom Rand) then ()
            else(Lib.say"which has kind\n\n";
                 pkd(Type.kind_of Rand');
                 Lib.say"\n\n");

            Lib.say ("unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end
        | (e as Feedback.HOL_ERR{origin_structure="Prerank",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val Rator_ty = Pretype.toType (ptype_of Rator)
                         handle e => raise (wrap_exn "Preterm" "check.TyComb5" e)
              val Rator' = to_term (overloading_resolution0 Rator)
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
              val Rator_ty' = Term.type_of Rator'
              val Pretype.PT(_,rand_locn) = Rand
              val Rand' = (Pretype.toType Rand
                         handle e => raise (wrap_exn "Preterm" "check.TyComb6" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
          in
            Lib.say "\nRank inference failure: unable to infer a type \
                              \for the application of\n\n";
            ptm Rator';
            Lib.say ("\n\n"^locn.toString (locn Rator)^"\n\n");

            if (Type.is_univ_type Rator_ty') then
                 (*if (is_atom Rator) then ()
                 else*)(Lib.say"whose argument must have rank <= ";
                      prk(Type.rank_of (#1 (Type.dest_univ_type Rator_ty')));
                      Lib.say"\n\n")
            else (Lib.say"which is not a universal type\n\n");

            Lib.say "to the type\n\n";
            pty Rand';
            Lib.say ("\n\n"^locn.toString rand_locn^"\n\n");

            if (Pretype.is_atom Rand) then ()
            else(Lib.say"which has rank ";
                 prk(Type.rank_of Rand');
                 Lib.say"\n\n");

            Lib.say ("unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc"typecheck" (rand_locn (* arbitrary *)) "failed"
          end)
    | check (  Abs{Bvar, Body, Locn}) = (check Bvar; check Body)
    | check (TyAbs{Bvar, Body, Locn}) = (checkkind Bvar; check Body)
    | check (Var {Name, Ty, Locn}) =
       (checkkind Ty; Prekind.unify (Pretype.pkind_of Ty) Prekind.typ
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = (Pretype.toType Ty
                         handle e => raise (wrap_exn "Preterm" "check.Var" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
          in
            Lib.say "\nKind inference failure: the variable ";
            Lib.say (Name^"\n\n");
            Lib.say ("\n\n"^locn.toString Locn^"\n\n");

            Lib.say "\n\nis constrained to have the type\n\n";
            pty real_type;
            Lib.say ("\n\n"^locn.toString (pty_locn Ty)^"\n\n");

            Lib.say"which has kind\n\n";
            pkd(Type.kind_of real_type);
            Lib.say"\n\n";

            Lib.say "but the type of a term must have kind "; pkd Kind.typ; Lib.say "\n\n";
            Lib.say ("kind unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end)
    | check (Const {Name, Thy, Ty, Locn}) =
       (checkkind Ty; Prekind.unify (Pretype.pkind_of Ty) Prekind.typ
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = (Pretype.toType Ty
                         handle e => raise (wrap_exn "Preterm" "check.Const" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
          in
            Lib.say "\nKind inference failure: the constant ";
            Lib.say (Thy^"$"^Name^"\n\n");
            Lib.say ("\n\n"^locn.toString Locn^"\n\n");

            Lib.say "\n\nis constrained to have the type\n\n";
            pty real_type;
            Lib.say ("\n\n"^locn.toString (pty_locn Ty)^"\n\n");

            if (Pretype.is_atom Ty) then ()
            else(Lib.say"which has kind\n\n";
                 pkd(Type.kind_of real_type);
                 Lib.say"\n\n");

            Lib.say "but the type of a term must have kind "; pkd Kind.typ; Lib.say "\n\n";
            Lib.say ("kind unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end)
    | check (Constrained{Ptm,Ty,Locn}) =
       ((checkkind Ty;
         Prekind.unify (Pretype.pkind_of Ty) Prekind.typ;
         check Ptm;
         Pretype.unify (ptype_of Ptm) Ty)
       handle (e as Feedback.HOL_ERR{origin_structure="Prekind",
                                     origin_function="unify",message})
       => let val real_term = to_term (overloading_resolution0 Ptm)
              val show_kinds = Feedback.get_tracefn "kinds"
              val tmp = show_kinds()
              val _   = Feedback.set_trace "kinds" 2
              val real_type = (Pretype.toType Ty
                         handle e => raise (wrap_exn "Preterm" "check.Constrained" e))
                handle e => (Feedback.set_trace "kinds" tmp; raise e)
          in
            Lib.say "\nKind inference failure: the term\n\n";
            ptm real_term;
            Lib.say ("\n\n"^locn.toString (locn Ptm)^"\n\n");

            Lib.say "is constrained to have the type\n\n";
            pty real_type;
            Lib.say ("\n\n"^locn.toString (pty_locn Ty)^"\n\n");

            Lib.say"which has kind\n\n";
            pkd(Type.kind_of real_type);
            Lib.say"\n\n";

            Lib.say "but the type of a term must have kind "; pkd Kind.typ; Lib.say "\n\n";
            Lib.say ("kind unification failure message: "^message^"\n");
            Feedback.set_trace "kinds" tmp;
            raise ERRloc"kindcheck" (pty_locn Ty (* arbitrary *)) "failed"
          end
       | (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val real_term = to_term (overloading_resolution0 Ptm)
                handle e => (Globals.show_types := tmp; raise e)
              val real_type = (Pretype.toType Ty
                         handle e => raise (wrap_exn "Preterm" "check.Constrained2" e))
                handle e => (Globals.show_types := tmp; raise e)
          in
            Lib.say "\nType inference failure: the term\n\n";
            ptm real_term;
            Lib.say ("\n\n"^locn.toString (locn Ptm)^"\n\n");
            if (is_atom Ptm) then ()
            else(Lib.say"which has type\n\n";
                 pty(Term.type_of real_term);
                 Lib.say"\n\n");
            Lib.say "can not be constrained to be of type\n\n";
            pty real_type;
            Lib.say ("\n\nunification failure message: "^message^"\n");
            Globals.show_types := tmp;
            raise ERRloc"typecheck" Locn "failed"
          end)
    | check _ = ()
in check
end end;

fun typecheck_phase1 pfns ptm =
    TC pfns ptm
    handle phase1_exn(l,s,ty) => let
           in
             case pfns of
               NONE => (Lib.say s; raise ERRloc "typecheck" l s)
             | SOME (_, typ, _) =>
               (Lib.say s;
                Lib.say "Wanted it to have type:  ";
                Lib.say (typ ty);
                Lib.say "\n";
                raise ERRloc "typecheck" l s)
           end


val post_process_term = ref (I : term -> term);

fun typecheck pfns ptm0 = let
  val () = TC pfns ptm0
  val ptm = overloading_resolution0 ptm0
in
  !post_process_term (remove_case_magic (to_term ptm))
end handle phase1_exn(l,s,ty) =>
           case pfns of
             NONE => (Lib.say s; raise ERRloc "typecheck" l s)
           | SOME (_, typ, _) =>
             (Lib.say s;
              Lib.say "Wanted it to have type:  ";
              Lib.say (typ ty);
              Lib.say "\n";
              raise ERRloc "typecheck" l s)


end; (* Preterm *)
