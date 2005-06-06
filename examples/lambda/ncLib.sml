structure ncLib :> ncLib =
struct

open HolKernel Parse boolLib
open BasicProvers SingleStep simpLib

open ncTheory swapTheory NEWLib
val (Type,Term) = parse_from_grammars swapTheory.swap_grammars

fun ERR f msg = raise (HOL_ERR {origin_function = f,
                                origin_structure = "ncLib",
                                message = msg})


exception ProofFailed of (term list * term) list
local
  val string_ty = stringSyntax.string_ty
  val v = mk_var("v", string_ty)
  val u = mk_var("u", string_ty)
  val anc_ty = mk_thy_type{Tyop = "nc", Thy = "nc", Args = [alpha]}
  val t = mk_var("t", anc_ty)
  val sub = mk_thy_const{Name = "SUB", Thy = "nc",
                         Ty = anc_ty --> string_ty --> anc_ty --> anc_ty}
  val VAR_t = mk_thy_const{Name = "VAR", Thy = "nc",
                           Ty = string_ty --> anc_ty}
in
fun vsubst_tac defthm =
    HO_MATCH_MP_TAC nc_INDUCTION2 THEN
    Q.EXISTS_TAC `{u;v}` THEN
    SRW_TAC [][SUB_THM, SUB_VAR, defthm]

fun prove_vsubst_result defthm extra_tac = let
  val cs = strip_conj (concl defthm)
  val f = #1 (strip_comb (lhs (#2 (strip_forall (hd cs)))))
  val goal0 = mk_eq(mk_comb(f, list_mk_comb(sub, [mk_comb(VAR_t, v), u, t])),
                    mk_comb(f, t))
  val goal = mk_forall (t, goal0)
  val extra_tac = case extra_tac of NONE => ALL_TAC | SOME t => t
  val whole_tac = vsubst_tac defthm THEN extra_tac
  val prove_goal = prove(goal, whole_tac)
      handle HOL_ERR _ => raise ProofFailed (#1 (whole_tac ([], goal)))
  val thm_name = #Name (dest_thy_const f) ^ "_vsubst_invariant"
in
  save_thm(thm_name, prove_goal);
  BasicProvers.export_rewrites [thm_name];
  prove_goal
end

end (* local *)


(* ----------------------------------------------------------------------
    prove_recursive_term_function_exists tm

    tm is of the form

       (!s. f (VAR s) = var_rhs s) /\
       (!k. f (CON k) = con_rhs k) /\
       (!t1 t2. f (t1 @@ t2) = app_rhs t1 t2 (f t1) (f t2)) /\
       (!u t. f (LAM u t) = lam_rhs t (f t))

    though not necessarily with the conjuncts in that particular
    order, or with all of them present.  The universal quantifications
    can be omitted for any or all of the conjuncts. This code attempts
    to prove that such a function actually exists.  The RHS of any
    LAMBDA clause comes in for particular attention because this might
    attempt a recursion that is not be justified.  This function
    attempts to use the simplifier and the stateful simpset (srw_ss()) to
    prove that the side-conditions on either
       swapTheory.swap_RECURSION_generic
    or
       swapTheory.swap_RECURSION_simple

   ---------------------------------------------------------------------- *)


val var_con = ``VAR : string -> 'a nc``;
val con_con = ``CON : 'a -> 'a nc``;
val lam_con = ``LAM : string -> 'a nc -> 'a nc``
val app_con = ``$@@ : 'a nc -> 'a nc -> 'a nc``;
val nc_constructors = [var_con, con_con, lam_con, app_con];

val abs_con = ``ABS: (string -> 'a nc) -> 'a nc``
val fv_con = ``FV : 'a nc -> string set``
val new_con = ``NEW : string set -> string``

fun myfind f [] = NONE
  | myfind f (h::t) = case f h of NONE => myfind f t | x => x

fun check_for_errors tm = let
  val conjs = map (#2 o strip_forall) (strip_conj tm)
  val _ = List.all is_eq conjs orelse
          ERR "prove_recursive_term_function_exists"
              "All conjuncts must be equations"
  val f = rator (lhs (hd conjs))
  val _ = List.all (fn t => rator (lhs t) = f) conjs orelse
          ERR "prove_recursive_term_function_exists"
              "Must define same constant in all equations"
  val _ = List.all (fn t => length (#2 (strip_comb (lhs t))) = 1) conjs orelse
          ERR "prove_recursive_term_function_exists"
              "Function being defined must be applied to one argument"
  val _ = (#1 (dest_type (type_of (rand (lhs (hd conjs))))) = "nc"
           handle HOL_ERR _ => false) orelse
          ERR "prove_recursive_term_function_exists"
              "Function to be defined must be applied to nc terms"
  val () =
      case List.find
           (fn t => List.all
                      (fn c => not
                                 (same_const c
                                             (#1 (strip_comb (rand (lhs t))))))
                      nc_constructors) conjs of
        NONE => ()
      | SOME t => ERR "prove_recursive_term_function_exists"
                      ("Unknown constructor "^
                       term_to_string (#1 (strip_comb (rand (lhs t)))))
  val () =
      case myfind
           (fn t => let val (c, args) = strip_comb (rand (lhs t))
                    in
                      case List.find (not o is_var) args of
                        NONE => NONE
                      | SOME v => SOME (v, c)
                    end) conjs of
        NONE => ()
      | SOME (v, c) =>
        ERR "prove_recursive_term_function_exists"
            (#1 (dest_const c)^"^'s argument "^term_to_string v^
             " is not a variable")
in
  (f, conjs)
end

val renaming_goal_form =
  ``!t R. RENAMING R ==> ((hom:'a nc -> 'b) (t ISUB R) = hom t)``

val SIMPLE_LET = prove(``!(t:'a) (v:'b). (let x = v in t) = t``,
                       REWRITE_TAC [LET_THM]);

val string_ty = stringSyntax.string_ty
fun gennc_ty ty = mk_type("nc", [ty])

val var_functor = mk_var("var", string_ty --> beta)
val con_functor = mk_var("con", alpha --> beta)
val app_functor = mk_var("app", beta --> beta -->
                                     gennc_ty alpha --> gennc_ty alpha -->
                                     beta)
val lam_functor = mk_var("lam", beta --> string_ty --> gennc_ty alpha --> beta)

val FV_t = ``nc$FV``
val swap_t = mk_const("swap", ``:string -> string -> 'a nc -> 'a nc``)
val nc_info =
    {nullfv = (``LAM "" (VAR "")``,
                   prove(``FV (LAM "" (VAR "")) = {}``,
                         SRW_TAC [][])),
     fv = (FV_t, FV_THM),
     swap = (swap_t, swap_thm),
     recursion = SIMP_RULE (srw_ss()) []
                           (Q.INST [`X` |-> `{}`]
                                   swapTheory.swap_RECURSION_generic),
     swapping = nc_swapping}

val null_fv = ``K {} : 'a -> string set``
val null_swap = ``\x:string y:string z:'a. z``
val null_info = {nullfv = (mk_arb alpha,
                            prove(``^null_fv ^(mk_arb alpha) = {}``,
                                  SRW_TAC [][])),
                 fv = (null_fv, TRUTH),
                 swap = (null_swap, TRUTH),
                 recursion = swapTheory.swap_RECURSION_simple,
                 swapping = null_swapping}

(*
val string_fv = ``\s:string. {s}``
val string_swap = ``swapstr``
val string_info = {nullfv = (
*)

val database = let
  val empty = Binarymap.mkDict String.compare
in
  Binarymap.insert(empty, "nc", nc_info)
end



fun inst_info dest_ty {nullfv, fv, swap, recursion, swapping} = let
  val inst_val = Type.match_type (type_of (fst nullfv)) dest_ty
  val local_inst = inst inst_val
in
  {nullfv = let val (t, th) = nullfv in (local_inst t, th) end,
   fv = let val (t, th) = fv in (local_inst t, th) end,
   swap = let val(t, th) = swap in (local_inst t, th) end,
   recursion = recursion,
   swapping = swapping}
end

exception InfoProofFailed of term
fun with_info_prove_recn_exists f nc_ty lookup info = let
  val nc_arg_ty = hd (#Args (dest_thy_type nc_ty))
  val {nullfv, fv, swap, recursion, swapping} = info
  val (nullfv_t, nullfv_thm) = nullfv
  val rhs_ty = type_of nullfv_t
  val (fv_t, fv_thm) = fv
  val (rswap_t, rswap_thm) = swap
  val swap_null = SIMP_RULE bool_ss [GSYM rswap_thm]
                            (MATCH_MP swapping_implies_empty_swap
                                      (CONJ swapping nullfv_thm))
  fun mk_simple_abstraction (c, (cargs, r)) = list_mk_abs(cargs, r)
  val varcase =
      case lookup var_con of
        NONE => mk_abs(genvar string_ty, nullfv_t)
      | SOME x => mk_simple_abstraction x
  val concase =
      case lookup con_con of
        NONE => mk_abs(genvar nc_arg_ty, nullfv_t)
      | SOME x => mk_simple_abstraction x
  val appcase =
      case lookup app_con of
        NONE => list_mk_abs([genvar rhs_ty, genvar rhs_ty,
                             genvar nc_ty, genvar nc_ty], nullfv_t)
      | SOME (c, (cargs, r)) => let
          val t1 = hd cargs
          val t2 = hd (tl cargs)
          val t1v = variant [t1,t2,f] (mk_var("t1f", rhs_ty))
          val t2v = variant [t1v,t1,t2,f] (mk_var("t2f", rhs_ty))
          val ft1 = mk_comb(f, t1)
          val ft2 = mk_comb(f, t2)
        in
          list_mk_abs([t1v,t2v,t1,t2],
                      Term.subst [ft1 |-> t1v, ft2 |-> t2v] r)
        end
  val lamcase =
      case lookup lam_con of
        NONE => list_mk_abs([genvar rhs_ty,
                             genvar string_ty,
                             genvar nc_ty],
                            nullfv_t)
      | SOME (c, (cargs, r)) => let
          val uvar = hd cargs
          val bodyvar = hd (tl cargs)
          val body_result_var =
              variant [uvar, bodyvar, f] (mk_var("brv", rhs_ty))
          val fbody = mk_comb(f, bodyvar)
        in
          list_mk_abs([body_result_var, uvar, bodyvar],
                      Term.subst [fbody |-> body_result_var] r)
        end
  val instantiation = [alpha |-> nc_arg_ty, beta |-> rhs_ty]
  fun i t = inst instantiation t
  val recursion_exists0 =
      INST [i con_functor |-> concase,
            i var_functor |-> varcase,
            i app_functor |-> appcase,
            i lam_functor |-> lamcase,
            i ``rFV : 'b -> string set`` |-> fv_t,
            i ``rswap : string -> string -> 'b -> 'b`` |-> rswap_t]
           (INST_TYPE instantiation recursion)
  val recursion_exists =
      CONV_RULE (RAND_CONV
                   (BINDER_CONV
                      (EVERY_CONJ_CONV
                         (STRIP_QUANT_CONV (RAND_CONV LIST_BETA_CONV))) THENC
                      RAND_CONV (ALPHA_CONV f)))
                   recursion_exists0
  val precondition_discharged =
      CONV_RULE
        (LAND_CONV (SIMP_CONV (srw_ss()) [fv_thm, GSYM rswap_thm, swapping,
                                          swap_null, GSYM swap_thm]))
        recursion_exists
in
  MP precondition_discharged TRUTH
     handle HOL_ERR _ =>
            raise InfoProofFailed (#1 (dest_imp
                                         (concl precondition_discharged)))
end;



fun prove_recursive_term_function_exists0 tm = let
  val (f, conjs) = check_for_errors tm

  val (nc_ty, rhs_ty) = dom_rng (type_of f)
  val nc_arg_ty = hd (#2 (dest_type nc_ty))

  fun insert (x as (c, rhs)) alist =
      case alist of
        [] => [(c,rhs)]
      | (h as (c',rhs')) :: t => if same_const c c' then
                                   ERR "prove_recursive_term_function_exists"
                                       ("Two equations for constructor " ^
                                        #1 (dest_const c))
                                 else h :: insert x t
  fun lookup c alist =
      case alist of
        [] => NONE
      | (h as (c',rhs)) :: t => if same_const c c' then SOME h else lookup c t
  fun insert_eqn (eqn, alist) = let
    val (c, cargs) = strip_comb (rand (lhs eqn))
  in
    insert (c, (cargs, rhs eqn)) alist
  end
  (* order of keys is order of clauses in original definition request *)
  val alist = List.foldl insert_eqn [] conjs
  fun find_eqn c = lookup c alist
  val null_info = inst_info rhs_ty null_info
  val callthis = with_info_prove_recn_exists f nc_ty find_eqn
in
  case Lib.total dest_type rhs_ty of
    SOME (tyop, args) => let
    in
      case Binarymap.peek(database, tyop) of
        NONE => callthis null_info
      | SOME i => callthis (inst_info rhs_ty i)
        handle InfoProofFailed tm =>
               (HOL_WARNING
                  "ncLib"
                  "prove_recursive_term_function_exists"
                  ("Couldn't prove function with swap over range - \n\
                   \goal was "^term_to_string tm^"\n\
                   \trying null range assumption");
                callthis null_info)
    end
  | NONE => callthis null_info
end handle InfoProofFailed tm =>
           raise ERR "prove_recursive_term_function_exists"
                     ("Couldn't prove function with swap over range - \n\
                      \goal was "^term_to_string tm)

fun strip_tyannote acc (Absyn.TYPED(_, a, ty)) = strip_tyannote (ty::acc) a
  | strip_tyannote acc x = (List.rev acc, x)

fun head_sym a = let
  val conjs = Absyn.strip_conj a
  val firstbody = #2 (Absyn.strip_forall (hd conjs))
  val (eqlhs, _) = Absyn.dest_app firstbody
  val (_, lhs) = Absyn.dest_app eqlhs
  val (_, fargs)  = strip_tyannote [] lhs
  val (f0, _) = Absyn.strip_app fargs
in
  #2 (strip_tyannote [] f0)
end

fun prove_recursive_term_function_exists tm = let
  val f_thm = prove_recursive_term_function_exists0 tm
  val (f_v, f_body) = dest_exists (concl f_thm)
  val defining_body = CONJUNCT1 (ASSUME f_body)
  val result = EQT_ELIM (SIMP_CONV bool_ss [defining_body] tm)
in
  CHOOSE (f_v, f_thm) (EXISTS (mk_exists(f_v, tm), f_v) result)
end handle InfoProofFailed tm =>
           raise ERR "prove_recursive_term_function_exists"
                     ("Couldn't prove function with swap over range - \n\
                      \goal was "^term_to_string tm)

fun define_recursive_term_function q = let
  val a = Absyn q
  val f = head_sym a
  val fstr = case f of
               Absyn.IDENT(_, s) => s
             | x => ERR "define_recursive_term_function" "invalid head symbol"
  val restore_this = hide fstr
  fun restore() = Parse.update_overload_maps fstr restore_this
  val tm = Parse.absyn_to_term (Parse.term_grammar()) a
           handle e => (restore(); raise e)
  val _ = restore()
  val f_thm0 = prove_recursive_term_function_exists0 tm
  val (f_t, th_body) = dest_exists (concl f_thm0)
  val have_renamings = not (is_const (last (strip_conj th_body)))
  fun defining_conj c = let
    val fvs = List.filter (fn v => #1 (dest_var v) <> fstr) (free_vars c)
  in
    list_mk_forall(fvs, c)
  end
  val defining_term0 = list_mk_conj(map defining_conj (strip_conj tm))
  val defining_term =
      if have_renamings then mk_conj(defining_term0, rand th_body)
      else defining_term0
  val (base_definition, definition_ok) = let
    val definition_ok0 = default_prover(mk_imp(th_body, defining_term),
                                        SIMP_TAC bool_ss [])
  in
    (CHOOSE (f_t, f_thm0)
            (EXISTS(mk_exists(f_t, defining_term), f_t)
                   (UNDISCH definition_ok0)), true)
  end handle HOL_ERR _ =>
             if have_renamings then (f_thm0, false)
             else (CONJUNCT1 (CONV_RULE (HO_REWR_CONV LEFT_EXISTS_AND_THM)
                                        f_thm0), false)
  val f_def =
      new_specification (fstr^"_def", [fstr], base_definition)
  val _ = add_const fstr
  val f_const = prim_mk_const {Name = fstr, Thy = current_theory()}
  val f_thm = if definition_ok then
                save_thm(fstr^"_thm",
                         default_prover(subst [f_t |-> f_const] tm,
                                        SIMP_TAC bool_ss [f_def]))
              else f_def
  val f_invariants =
      if have_renamings then let
          val interesting_bit = CONJUNCT2 f_def
          val th = CONJUNCT1 interesting_bit
              handle HOL_ERR _ => interesting_bit
        in
          SOME (save_thm(fstr^"_swap_invariant", th)) before
          BasicProvers.export_rewrites [fstr^"_swap_invariant"]
        end
      else NONE
in
  (f_thm, f_invariants)
end


val recursive_term_function_existence = prove_recursive_term_function_exists0

end (* struct *)
