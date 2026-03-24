structure computeLib :> computeLib =
struct

open HolKernel boolSyntax boolTheory Abbrev clauses compute_rules equations;

(*
   An old version of this library is the subject of the paper [Barras2000]. Most
   of that description is still applicable.

   - [Barras2000] B. Barras (2000) “Programming and Computing in HOL” in
     “Theorem Proving in Higher Order Logics”.
     https://doi.org/10.1007/3-540-44659-1_2
*)

val auto_import_definitions = ref true;
val _ = Feedback.register_btrace
          ("computeLib.auto_import_definitions", auto_import_definitions)

(* re-exporting types from clauses *)

type compset = clauses.compset;
type transform = clauses.transform

val new_compset = from_list;

val listItems = clauses.deplist;
val unmapped  = clauses.no_transform;
val seal      = clauses.seal;
val copy      = clauses.copy;

datatype cbv_stack =
    Cbv_top
  | Cbv_rator of
    { Rand: (thm->thm->thm) * (thm * db fterm),
      Ctx: cbv_stack }
  | Cbv_rand of
    { Rator: (thm->thm->thm) * bool * (thm * db fterm),
      Ctx: cbv_stack  }
  | Cbv_abs of
    { Bvar: (thm->thm),
      Ctx: cbv_stack }
  | Cbv_ant of
    { Thm: thm, (* The theorem of the expression whose reduction requires the
                proving of antecedents *)
      Cl: db fterm, (* Information about `Thm`. *)
      Proved: thm list,
      Pending: (term * db fterm) list,
      Mk_thm: thm list -> thm,
      Const_info:
        { Head : term,
          Args : (term * db fterm) list,
          Rws  : db,
          Skip : int option },
      Ctx: cbv_stack }

val ERR = mk_HOL_ERR "computeLib"

(*---------------------------------------------------------------------------
 * Precondition: f(arg) is a closure corresponding to b.
 * Given   (arg,(|- M = (a b), Stk)),
 * returns (|- a = a, (<fun>,(|- b = b, f(arg)))::Stk)
 * where   <fun> =  (|- a = a' , |- b = b') |-> |- M = (a' b')
 *---------------------------------------------------------------------------*)
fun push_in_stk f (arg,(th,stk)) =
      let val (tha,thb,mka) = Mk_comb th in
      (tha, Cbv_rator{Rand=(mka,(thb,f arg)), Ctx=stk})
      end

fun push_skip_stk f (arg,(th,stk)) =
      let val (tha,thb,mka) = Mk_comb th in
      (tha, Cbv_rand{Rator=(Lib.C mka,true,(thb,f arg)), Ctx=stk})
      end

fun push_lam_in_stk (th, stk) =
      let val (_,thb,mkl) = Mk_abs th in
      (thb, Cbv_abs{Bvar=try_eta o mkl, Ctx=stk})
      end

fun stack_out(th, Cbv_top) =
    th
  | stack_out(th, Cbv_rator{Rand=(mka,(thb,_)), Ctx}) =
    stack_out(mka th thb,Ctx)
  | stack_out(th, Cbv_rand{Rator=(mka,_,(tha,_)),Ctx}) =
    stack_out(mka tha th, Ctx)
  | stack_out(th, Cbv_abs{Bvar=mkl, Ctx}) =
    stack_out (mkl th, Ctx)
  | stack_out(_, Cbv_ant _) =
    raise DEAD_CODE "stack_out"

(* initial_state returns the updated compset along with the initial state.
   The compset may be updated if new constants are encountered in the term. *)
fun initial_state rws t =
  let val (rws', dt) = from_term (rws,[],t)
  in (rws', ((refl_thm t, mk_clos([],dt)), Cbv_top : cbv_stack))
  end;

(*
   `cbv_wk rws ((thm, cl), stk)` puts the closure `cl` (useful information about
   the rhs of `thm`) in head normal form (weak reduction). It returns either a
   closure which term is an abstraction, in a context other than Zappl, a
   variable applied to strongly reduced arguments, or a constant applied to
   weakly reduced arguments which does not match any rewriting rule.
   - Substitution is propagated through applications.
   - If the RHS is an abstraction and there is one arg on the stack, this means
     we found a beta redex. `mka` rebuilds the application of the function to
     its argument, and Beta does the actual beta step.
   - For an applied constant, we look for a rewrite matching it. If we found
     one, then we apply the instantiated rule, and go on. Otherwise, we try to
     rebuild the thm.
   - For an already strongly normalized term or an unapplied abstraction,
     we try to rebuild the thm.

   The whole argument of `cbv_wk` is the state of the computation. `thm` is an
   equational theorem `|- lhs = rhs` where `lhs` is the term currently being
   evaluated before evaluation and `rhs` is the result of the evaluation so far.
   `cl` is information about `rhs`.

   `stk` represents the continuation of the evaluation. It is a stack
   implemented as a linked list of with the following interpretation.
   - `Cbv_top`: The end of the stack.
   - `Cbv_rator {Rand = (mk_thm, (thm2, thm2_cl)), ...}`: The continuation
     after descending into the operand of a combination.
   - `Cbv_rand`: The continuation after descending into the operator of a
     combination.
   - `Cbv_abs`: The continuation after descending into the body of an
     abstraction.

   `rws` is the compset, threaded through for use in wrapping conversion results.
*)
fun cbv_wk rws ((th,CLOS{Env, Term=App(a,args)}), stk) =
  (* *Combination.* Descend into operator immediately. Descend into operand in
     the combination, i.e.: when applying `cbv_up`. *)
      let val (tha,stka) =
            foldl (push_in_stk (curry mk_clos Env)) (th,stk) args in
      cbv_wk rws ((tha, mk_clos(Env,a)), stka)
      end
  (* *Abstraction.* Descend into the body. *)
  | cbv_wk rws ((th,CLOS{Env, Term=Abs body}),
            Cbv_rator{Rand=(mka,(thb,cl)), Ctx=s'}) =
      cbv_wk rws ((beta_thm(mka th thb), mk_clos(cl :: Env, body)), s')
  (* Combination where the operator is a constant that we can reduce. *)
  | cbv_wk rws ((th,CST cargs), stk) =
      let
        val (reduced_p, t', cl', ants, mk_thm) = reduce_cst rws (th, cargs)
      in
        if reduced_p then
          prove_ants rws (th, cl', [], ants, mk_thm, cargs, stk)
        else
          cbv_up rws ((th, cl'), stk)
      end
  | cbv_wk rws (clos, stk) = cbv_up rws (clos,stk)

and prove_ants rws (th, cl, proved_acc, ants_left, mk_thm, cargs, stk) =
  case ants_left of
    (* All antecedents proved. *)
    [] => cbv_wk rws ((mk_thm (rev proved_acc), cl), stk)
  | ((ant, ant_cl)::ants_rest) =>
    (* Try to prove the first remaining antecedent. Leave the rest in the
    continuation. *)
    cbv_wk rws ((refl_thm ant, ant_cl),
            Cbv_ant { Thm = th,
                      Cl = cl,
                      Proved = proved_acc,
                      Pending = ants_rest,
                      Mk_thm = mk_thm,
                      Const_info = cargs,
                      Ctx = stk})

(*
   Tries to rebuild the thm, knowing that the closure has been weakly
   normalized, until it finds term still to reduce, or if a strong reduction
   may be required.
   - If we are done with a Rator, we start reducing the Rand
   - If we are done with the Rand of a const, we rebuild the application and
     look if it created a redex
   - An application to a NEUTR can be rebuilt only if the argument has been
     strongly reduced, which we now for sure only if itself is a NEUTR.
*)
and cbv_up rws (hcl, Cbv_rator{Rand=(mka,clos), Ctx}) =
  (* We have already descended into the operator. Now descend into the
  operand. *)
      let val new_state = (clos, Cbv_rand{Rator=(mka,false,hcl), Ctx=Ctx}) in
      if is_skip hcl then cbv_up rws new_state else cbv_wk rws new_state
      end
  (* We have already descended into the operator and operand. Schedule the
  application for being reduced with the equation for the head constant. *)
  | cbv_up rws ((thb,v), Cbv_rand{Rator=(mka,false,(th,CST cargs)), Ctx=stk}) =
      cbv_wk rws ((mka th thb, comb_ct cargs (rhs_concl thb, v)), stk)
  | cbv_up rws ((thb,NEUTR), Cbv_rand{Rator=(mka,false,(th,NEUTR)), Ctx=stk}) =
      cbv_up rws ((mka th thb, NEUTR), stk)
  | cbv_up rws ((current_thm, _),
            Cbv_ant {Thm=thm,Cl,Proved,Pending,Mk_thm,Const_info,Ctx}) =
      let
        fun next_rw () =
          (* In this code path `cargs` is a `Try` because `reduce_cst` returned
          `reduced_p = true`. Note that the following pops the `Cbv_ant` from
          the stack. *)
          case Const_info of
            {Head, Args, Rws=Try{Hcst,Rws=Rewrite rls,Tail},Skip} =>
              cbv_wk rws ((thm, CST {Head=Head,Args=Args,Rws=Tail,Skip=Skip}),Ctx)
          | _ => raise DEAD_CODE "cbv_wk"
      in
        case Ctx of
           Cbv_top =>
             (if aconv T (rhs (concl current_thm)) then
                (* This antecedent proved. Add it to the accumulator and try to
                prove next antecedent. *)
                prove_ants rws (thm,Cl,current_thm::Proved,Pending,Mk_thm,Const_info,Ctx)
              else
                (* The current antecedent did not reduce to `T`; abandon this
                rewrite rule. *)
                next_rw ())
         | _ => next_rw ()
      end
  | cbv_up _ (clos, stk) = (clos,stk)

(*---------------------------------------------------------------------------
 * [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 * precondition: the closure should be the output of cbv_wk
 *---------------------------------------------------------------------------*)

fun strong rws ((th, CLOS{Env,Term=Abs t}), stk) =
      let val (thb,stk') = push_lam_in_stk(th,stk) in
      strong rws (cbv_wk rws ((thb, mk_clos(NEUTR :: Env, t)), stk'))
      end
  | strong _ (clos as (_,CLOS _), stk) = raise DEAD_CODE "strong"
  | strong rws ((th,CST {Skip,Args,...}), stk) =
      let val (argssk, argsrd) = partition_skip Skip Args
          val (th',stk') = foldl (push_skip_stk snd) (th,stk) argssk
          val (th'',stk'') = foldl (push_in_stk snd) (th',stk') argsrd in
      strong_up rws (th'',stk'')
      end
  | strong rws ((th, NEUTR), stk) = strong_up rws (th,stk)

and strong_up _ (th, Cbv_top) = th
  | strong_up rws (th, Cbv_rand{Rator=(mka,false,(tha,NEUTR)), Ctx}) =
      strong rws (cbv_wk rws ((mka tha th,NEUTR), Ctx))
  | strong_up _ (th, Cbv_rand{Rator=(mka,false,clos), Ctx}) =
      raise DEAD_CODE "strong_up"
  | strong_up rws (th, Cbv_rator{Rand=(mka,clos), Ctx}) =
      strong rws (cbv_wk rws (clos, Cbv_rand{Rator=(mka,true,(th,NEUTR)), Ctx=Ctx}))
  | strong_up rws (th, Cbv_rand{Rator=(mka,true,(tha,_)), Ctx}) =
      strong_up rws (mka tha th, Ctx)
  | strong_up rws (th, Cbv_abs{Bvar=mkl, Ctx}) = strong_up rws (mkl th, Ctx)
  | strong_up _ (_, _) = raise DEAD_CODE "strong_up"

(*---------------------------------------------------------------------------
 * [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *---------------------------------------------------------------------------*)

fun CBV_CONV rws t =
  let val (rws', init) = initial_state rws t
  in evaluate (strong rws' (cbv_wk rws' init))
  end;

(*---------------------------------------------------------------------------
 * WEAK_CBV_CONV is the same as CBV_CONV except that it does not reduce
 * under abstractions, and reduce weakly the arguments of constants.
 * Reduction whenever we reach a state where a strong reduction is needed.
 *---------------------------------------------------------------------------*)

fun WEAK_CBV_CONV rws t =
  let val (rws', init) = initial_state rws t
      val ((th,_),stk) = cbv_wk rws' init
  in evaluate (stack_out(th,stk))
  end;

fun CBVn_CONV n rws t =
    let val counter = ref n
        val old : term -> bool =
            case !stoppers of
                NONE => (fn _ => false)
              | SOME f => f
        fun stop_test t = if !counter <= 0 then true
                          else (counter := !counter - 1; old t)
    in
      with_flag(stoppers, SOME stop_test) (CBV_CONV rws) t
    end

(*---------------------------------------------------------------------------
 * Adding an arbitrary conv. The conversion result is wrapped with from_term
 * at invocation time in reduce_cst, using the current compset.
 *---------------------------------------------------------------------------*)

fun add_conv (cst,arity,conv) rws = add_extern (cst,arity,conv) rws;

fun set_skip compset c opt =
 let val {Name,Thy,...} = dest_thy_const c
 in clauses.set_skip compset (Name,Thy) opt
 end
 handle e as HOL_ERR _ => raise wrap_exn "computeLib" "set_skip" e


(*---------------------------------------------------------------------------
       Support for a global compset.
 ---------------------------------------------------------------------------*)

val bool_redns =
 strictify_thm LET_DEF
 :: strictify_thm literal_case_DEF
 :: List.map lazyfy_thm
      [COND_CLAUSES, COND_ID, NOT_CLAUSES,
       AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES];

val bool_compset =
  (* change NONE to SOME 1 to stop CBV_CONV looking at conditionals'
     branches before the guard is fully true or false *)
  seal (set_skip (from_list bool_redns) boolSyntax.conditional NONE);

val the_compset = ref (copy bool_compset);

fun add_funs thms = the_compset := add_thms thms (!the_compset);
fun add_convs convs =
  the_compset := foldl (fn (c, cs) => add_conv c cs) (!the_compset) convs;

fun del_consts cs =
  the_compset := foldl (fn (c, cset) => scrub_const cset c) (!the_compset) cs;
fun del_funs thms = the_compset := scrub_thms thms (!the_compset);

fun EVAL_CONV t = CBV_CONV (!the_compset) t;
fun EVALn_CONV n t = CBVn_CONV n (!the_compset) t
val EVAL_RULE = Conv.CONV_RULE EVAL_CONV;
val EVAL_TAC  = Tactic.CONV_TAC EVAL_CONV;

infix Orelse;
fun (p Orelse q) x = p x orelse q x;

fun OR [] = K false
  | OR [x] = same_const x
  | OR (h::t) = same_const h Orelse OR t;

fun RESTR_EVAL_CONV clist =
  Lib.with_flag (stoppers,SOME (OR clist)) EVAL_CONV;

val RESTR_EVAL_TAC  = Tactic.CONV_TAC o RESTR_EVAL_CONV;
val RESTR_EVAL_RULE = Conv.CONV_RULE o RESTR_EVAL_CONV;

(*---------------------------------------------------------------------------
      Support for persistence of the_compset
 ---------------------------------------------------------------------------*)

local
   val get_f =
      fst o boolSyntax.strip_comb o boolSyntax.lhs o
      snd o boolSyntax.strip_forall o List.hd o boolSyntax.strip_conj o
      Thm.concl
   val translate_convs =
      List.mapPartial
        (fn {key = SOME ([], t), conv, ...} : simpfrag.convdata =>
           (case Lib.total boolSyntax.strip_comb t of
               SOME (f, l) =>
                 SOME (f, List.length l, conv (Lib.K Conv.ALL_CONV) [])
             | NONE => NONE)
          | _ => NONE)
in
   fun add_datatype_info cs tyinfo =
    let open TypeBasePure Drule
        val size_opt =
          case size_of0 tyinfo of
             SOME (_, ORIG def) => [def]
           | _ => []
        val boolify_opt =
          case encode_of0 tyinfo of
             SOME (_, ORIG def) => [def]
           | _ => []
        val case_const = Lib.total case_const_of tyinfo
        val {rewrs = simpls, convs} = simpls_of tyinfo
        fun tmopt_eq NONE NONE = true
          | tmopt_eq (SOME t1) (SOME t2) = aconv t1 t2
          | tmopt_eq _ _ = false
        val (case_thm, simpls) =
           List.partition (fn thm => tmopt_eq (Lib.total get_f thm) case_const)
                          simpls
        val case_thm = List.map lazyfy_thm case_thm
        val cs' = foldl (fn (c, cset) => add_conv c cset) cs (translate_convs convs)
    in
        add_thms (size_opt @ boolify_opt @ case_thm @ simpls) cs'
    end
    fun write_datatype_info tyi =
        the_compset := add_datatype_info (!the_compset) tyi
end

val _ = TypeBase.register_update_fn (fn tyi => (write_datatype_info tyi; tyi))

(*---------------------------------------------------------------------------*)
(* Usage note: call this before export_theory().                             *)
(*---------------------------------------------------------------------------*)

open LoadableThyData
val {export,...} =
    ThmSetData.new_exporter {
      settype = "compute",
      efns = {add = (fn {named_thm,...} => add_funs [#2 named_thm]),
              remove = fn _ => ()}
    }
val add_persistent_funs = app export


(* ----------------------------------------------------------------------
    Other exported changes: set_skip and del_consts
   ---------------------------------------------------------------------- *)

datatype clib_delta = CLD_set_skip of term * int option
                    | CLD_delconst of term
fun uptodate_delta (CLD_set_skip(t,_)) = uptodate_term t
  | uptodate_delta (CLD_delconst t) = uptodate_term t

fun encdelta cld =
    let open ThyDataSexp
    in
      case cld of
          CLD_set_skip d => pair_encode (Term, option_encode Int) d
        | CLD_delconst t => Term t
    end

fun decdelta d =
    let open ThyDataSexp
    in
      case d of
          Term t => SOME (CLD_delconst t)
        | _ => (pair_decode(term_decode, option_decode int_decode) >>
                CLD_set_skip) d
    end

fun apply_delta cld () =
    case cld of
        CLD_set_skip (t, iopt) =>
          the_compset := set_skip (!the_compset) t iopt
      | CLD_delconst t => del_consts [t]

val {record_delta,get_deltas=thy_updates,...} =
    AncestryData.fullmake {
      adinfo = {tag = "computeLib.delta",
                initial_values = [("min", ())],
                apply_delta = apply_delta},
      uptodate_delta = uptodate_delta,
      sexps = {dec = decdelta, enc = encdelta},
      globinfo = {apply_to_global = apply_delta,
                  thy_finaliser = NONE,
                  initial_value = ()}
    }

fun set_EVAL_skip t i = record_delta (CLD_set_skip(t,i))
fun temp_set_EVAL_skip t i =
    the_compset := set_skip (!the_compset) t i
fun del_persistent_consts cs = app (fn c => record_delta(CLD_delconst c)) cs

(* ----------------------------------------------------------------------
    compset pretty-printer
   ---------------------------------------------------------------------- *)

fun pp_compset c = HOLPP.add_string "<compset>"

(* ----------------------------------------------------------------------
   Help for building up compsets and creating new compset based conversions
   ---------------------------------------------------------------------- *)

datatype compset_element =
    Convs of (term * int * conv) list
  | Defs of thm list
  | Tys of hol_type list
  | Extenders of (compset -> compset) list

local
  fun add_datatype cmp ty =
      add_datatype_info cmp (Option.valOf (TypeBase.fetch ty))
in
  fun extend_compset frags cmp =
    foldl (fn (frag, cs) =>
             case frag of
               Convs l => foldl (fn (x, cs') => add_conv x cs') cs l
             | Defs l => add_thms l cs
             | Tys l => foldl (fn (ty, cs') => add_datatype cs' ty) cs l
             | Extenders l => foldl (fn (f, cs') => f cs') cs l)
          cmp frags
end

fun compset_conv cmp l = CBV_CONV (extend_compset l cmp)

end
