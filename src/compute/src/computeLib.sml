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

fun initial_state rws t =
  ((refl_thm t, mk_clos([],from_term (rws,[],t))), Cbv_top : cbv_stack);

(*
   `cbv_wk ((thm, cl), stk)` puts the closure `cl` (useful information about
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
*)
fun cbv_wk ((th,CLOS{Env, Term=App(a,args)}), stk) =
  (* *Combination.* Descend into operator immediately. Descend into operand in
     the combination, i.e.: when applying `cbv_up`. *)
      let val (tha,stka) =
            foldl (push_in_stk (curry mk_clos Env)) (th,stk) args in
      cbv_wk ((tha, mk_clos(Env,a)), stka)
      end
  (* *Abstraction.* Descend into the body. *)
  | cbv_wk ((th,CLOS{Env, Term=Abs body}),
            Cbv_rator{Rand=(mka,(thb,cl)), Ctx=s'}) =
      cbv_wk ((beta_thm(mka th thb), mk_clos(cl :: Env, body)), s')
  (* Combination where the operator is a constant that we can reduce. *)
  | cbv_wk ((th,CST cargs), stk) =
      let
        val (reduced_p, t', cl', ants, mk_thm) = reduce_cst (th, cargs)
      in
        if reduced_p then
          prove_ants (th, cl', [], ants, mk_thm, cargs, stk)
        else
          cbv_up ((th, cl'), stk)
      end
  | cbv_wk (clos, stk) = cbv_up (clos,stk)

and prove_ants (th, cl, proved_acc, ants_left, mk_thm, cargs, stk) =
  case ants_left of
    (* All antecedents proved. *)
    [] => cbv_wk ((mk_thm (rev proved_acc), cl), stk)
  | ((ant, ant_cl)::ants_rest) =>
    (* Try to prove the first remaining antecedent. Leave the rest in the
    continuation. *)
    cbv_wk ((refl_thm ant, ant_cl),
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
and cbv_up (hcl, Cbv_rator{Rand=(mka,clos), Ctx}) =
  (* We have already descended into the operator. Now descend into the
  operand. *)
      let val new_state = (clos, Cbv_rand{Rator=(mka,false,hcl), Ctx=Ctx}) in
      if is_skip hcl then cbv_up new_state else cbv_wk new_state
      end
  (* We have already descended into the operator and operand. Schedule the
  application for being reduced with the equation for the head constant. *)
  | cbv_up ((thb,v), Cbv_rand{Rator=(mka,false,(th,CST cargs)), Ctx=stk}) =
      cbv_wk ((mka th thb, comb_ct cargs (rhs_concl thb, v)), stk)
  | cbv_up ((thb,NEUTR), Cbv_rand{Rator=(mka,false,(th,NEUTR)), Ctx=stk}) =
      cbv_up ((mka th thb, NEUTR), stk)
  | cbv_up ((current_thm, _),
            Cbv_ant {Thm=thm,Cl,Proved,Pending,Mk_thm,Const_info,Ctx}) =
      let
        fun next_rw () =
          (* In this code path `cargs` is a `Try` because `reduce_cst` returned
          `reduced_p = true`. Note that the following pops the `Cbv_ant` from
          the stack. *)
          case Const_info of
            {Head, Args, Rws=Try{Hcst,Rws=Rewrite rls,Tail},Skip} =>
              cbv_wk ((thm, CST {Head=Head,Args=Args,Rws=Tail,Skip=Skip}),Ctx)
          | _ => raise DEAD_CODE "cbv_wk"
      in
        case Ctx of
           Cbv_top =>
             (if aconv T (rhs (concl current_thm)) then
                (* This antecedent proved. Add it to the accumulator and try to
                prove next antecedent. *)
                prove_ants (thm,Cl,current_thm::Proved,Pending,Mk_thm,Const_info,Ctx)
              else
                (* The current antecedent did not reduce to `T`; abandon this
                rewrite rule. *)
                next_rw ())
         | _ => next_rw ()
      end
  | cbv_up (clos, stk) = (clos,stk)

(*---------------------------------------------------------------------------
 * [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 * precondition: the closure should be the output of cbv_wk
 *---------------------------------------------------------------------------*)

fun strong ((th, CLOS{Env,Term=Abs t}), stk) =
      let val (thb,stk') = push_lam_in_stk(th,stk) in
      strong (cbv_wk((thb, mk_clos(NEUTR :: Env, t)), stk'))
      end
  | strong (clos as (_,CLOS _), stk) = raise DEAD_CODE "strong"
  | strong ((th,CST {Skip,Args,...}), stk) =
      let val (argssk, argsrd) = partition_skip Skip Args
          val (th',stk') = foldl (push_skip_stk snd) (th,stk) argssk
          val (th'',stk'') = foldl (push_in_stk snd) (th',stk') argsrd in
      strong_up (th'',stk'')
      end
  | strong ((th, NEUTR), stk) = strong_up (th,stk)

and strong_up (th, Cbv_top) = th
  | strong_up (th, Cbv_rand{Rator=(mka,false,(tha,NEUTR)), Ctx}) =
      strong (cbv_wk((mka tha th,NEUTR), Ctx))
  | strong_up (th, Cbv_rand{Rator=(mka,false,clos), Ctx}) =
      raise DEAD_CODE "strong_up"
  | strong_up (th, Cbv_rator{Rand=(mka,clos), Ctx}) =
      strong (cbv_wk(clos, Cbv_rand{Rator=(mka,true,(th,NEUTR)), Ctx=Ctx}))
  | strong_up (th, Cbv_rand{Rator=(mka,true,(tha,_)), Ctx}) =
      strong_up (mka tha th, Ctx)
  | strong_up (th, Cbv_abs{Bvar=mkl, Ctx}) = strong_up (mkl th, Ctx)
  | strong_up (_, _) = raise DEAD_CODE "strong_up"

(*---------------------------------------------------------------------------
 * [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *---------------------------------------------------------------------------*)

fun CBV_CONV rws = evaluate o strong o cbv_wk o initial_state rws;

(*---------------------------------------------------------------------------
 * WEAK_CBV_CONV is the same as CBV_CONV except that it does not reduce
 * under abstractions, and reduce weakly the arguments of constants.
 * Reduction whenever we reach a state where a strong reduction is needed.
 *---------------------------------------------------------------------------*)

fun WEAK_CBV_CONV rws =
      evaluate
    o (fn ((th,_),stk) => stack_out(th,stk))
    o cbv_wk
    o initial_state rws;

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
 * Adding an arbitrary conv
 *---------------------------------------------------------------------------*)

fun extern_of_conv rws conv tm =
  let val thm = conv tm in
  (thm, mk_clos([],from_term(rws,[],rhs(concl thm))))
  end;

fun add_conv (cst,arity,conv) rws =
  add_extern (cst,arity,extern_of_conv rws conv) rws;

fun set_skip compset c opt =
 let val {Name,Thy,...} = dest_thy_const c
 in clauses.set_skip compset (Name,Thy) opt
 end
 handle HOL_ERR _ => raise ERR "set_skip" "";


(*---------------------------------------------------------------------------
       Support for a global compset.
 ---------------------------------------------------------------------------*)

val bool_redns =
 strictify_thm LET_DEF
 :: strictify_thm literal_case_DEF
 :: List.map lazyfy_thm
      [COND_CLAUSES, COND_ID, NOT_CLAUSES,
       AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES];

fun bool_compset() = let
  val base = from_list bool_redns
  val _ = set_skip base boolSyntax.conditional NONE
          (* change last parameter to SOME 1 to stop CBV_CONV looking at
             conditionals' branches before the guard is fully true or false *)
in
  base
end

val the_compset = bool_compset();

val add_funs = Lib.C add_thms the_compset;
val add_convs = List.app (Lib.C add_conv the_compset);

val del_consts = List.app (scrub_const the_compset);
val del_funs = Lib.C scrub_thms the_compset;

val EVAL_CONV = CBV_CONV the_compset;
fun EVALn_CONV n t = CBVn_CONV n the_compset t
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
    in
        List.app (fn c => add_conv c cs) (translate_convs convs)
      ; add_thms (size_opt @ boolify_opt @ case_thm @ simpls) cs
    end
    val write_datatype_info = add_datatype_info the_compset
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
        CLD_set_skip (t, iopt) => set_skip the_compset t iopt
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
fun temp_set_EVAL_skip t i = set_skip the_compset t i
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
  | Extenders of (compset -> unit) list

local
  fun add_datatype cmp = add_datatype_info cmp o Option.valOf o TypeBase.fetch
in
  fun extend_compset frags cmp =
    List.app
      (fn Convs l => List.app (fn x => add_conv x cmp) l
        | Defs l => add_thms l cmp
        | Tys l => List.app (add_datatype cmp) l
        | Extenders l => List.app (fn f => f cmp) l) frags
end

fun compset_conv cmp l = (extend_compset l cmp; CBV_CONV cmp)

end
