structure ncLib :> ncLib =
struct

open HolKernel Parse boolLib
open BasicProvers SingleStep simpLib

open ncTheory
val (Type,Term) = parse_from_grammars ncTheory.nc_grammars

fun ERR f msg = raise (HOL_ERR {origin_function = f,
                                origin_structure = "ncLib",
                                message = msg})

infix |-> THEN
infixr -->
infix 8 by

val FRESH_STRING = prove(
  ``!X Y. FINITE (X:string set) /\ Y SUBSET X ==> ~(NEW X IN Y)``,
  PROVE_TAC [pred_setTheory.SUBSET_DEF, dBTheory.NEW_FRESH_string]);

val FRESH_STRING_eq = prove(
  ``!X x. FINITE (X:string set) /\ x IN X ==> ~(NEW X = x)``,
  PROVE_TAC [pred_setTheory.SUBSET_DEF, dBTheory.NEW_FRESH_string]);

fun NEW_TAC vname t = let
  val var = mk_var(vname, ``:string``)
  val new_t = mk_comb(``NEW:string set -> string``, t)
  val asm = mk_eq(var, new_t)
  fun union_inds (sets, inds) t = let
    val (f, args) = strip_comb t
  in
    if same_const f pred_setSyntax.union_tm then
      union_inds (union_inds (sets, inds) (hd args)) (hd (tl args))
    else if same_const f pred_setSyntax.insert_tm then
      union_inds (sets, hd args::inds) (hd (tl args))
    else if same_const f pred_setSyntax.empty_tm then (sets, inds)
    else (t::sets, inds)
  end
  val (sets, inds) = union_inds ([], []) t
  val munge = UNDISCH o CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
  fun mk_IN (v,s) = let
    val ty = type_of v
  in
    list_mk_comb(inst [alpha |-> ty] pred_setSyntax.in_tm, [v,s])
  end
  fun prove_ind i =
      munge (SIMP_PROVE (srw_ss()) [FRESH_STRING_eq, FINITE_FV,
                                    FINITE_DOM, FINITE_FVS]
                        (mk_imp(asm, mk_neg(mk_eq(var, i)))))
  fun prove_set s =
      munge (prove(mk_imp(asm, mk_neg(mk_IN(var, s))),
                   DISCH_THEN SUBST_ALL_TAC THEN
                   MATCH_MP_TAC FRESH_STRING THEN
                   SIMP_TAC (srw_ss()) [FINITE_FV, FINITE_DOM,
                                        FINITE_FVS,
                                        pred_setTheory.SUBSET_DEF]))
in
  Q.ABBREV_TAC `^asm` THEN
  MAP_EVERY (ASSUME_TAC o prove_ind) inds THEN
  MAP_EVERY (ASSUME_TAC o prove_set) sets THEN
  FIRST_X_ASSUM (K ALL_TAC o assert (is_eq o concl))
end

(* ----------------------------------------------------------------------
    NEW_ELIM_TAC
   ---------------------------------------------------------------------- *)

fun UNBETA_CONV to_elim t = let
  (* find all instances of to_elim in t, and convert t
     to (\v. t[v/to_elim]) to_elim
     v can be a genvar because we expect to get rid of it later. *)
  val gv = genvar (type_of to_elim)
  val newbody = Term.subst [to_elim |-> gv] t
in
  SYM (BETA_CONV (mk_comb(mk_abs(gv,newbody), to_elim)))
end

fun NEW_ELIM_TAC (asl, w) = let
  val newt = find_term (can (match_term ``NEW (X:string set)``)) w
in
  CONV_TAC (UNBETA_CONV newt) THEN MATCH_MP_TAC NEW_ELIM_RULE THEN
  SIMP_TAC (srw_ss()) [FINITE_FV]
end (asl, w)


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
    attempts to prove that the given definition is invariant under any
    renaming, if a recursion occurs in the LAM clause.

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
  fun mk_simple_abstraction (c, (cargs, r)) = let
    val result = list_mk_abs(cargs, r)
    val fvs = FVL [result] empty_tmset
  in
    if HOLset.isEmpty fvs then result
    else ERR "prove_recursive_term_function_exists"
         ("Illegal free variables: " ^
          String.concat
          (HOLset.foldl (fn (v,l) => (#1 (dest_var v)^" ")::l) [] fvs)^
          "on RHS of rule for " ^ #1 (dest_const c))
  end
  val varcase =
      case lookup var_con alist of
        NONE => mk_abs(genvar stringSyntax.string_ty, mk_arb rhs_ty)
      | SOME x => mk_simple_abstraction x
  val concase =
      case lookup con_con alist of
        NONE => mk_abs(genvar nc_arg_ty, mk_arb rhs_ty)
      | SOME x => mk_simple_abstraction x
  val appcase =
      case lookup app_con alist of
        NONE => list_mk_abs([genvar nc_ty, genvar nc_ty,
                             genvar rhs_ty, genvar rhs_ty], mk_arb rhs_ty)
      | SOME (c, (cargs, r)) => let
          val t1 = hd cargs
          val t2 = hd (tl cargs)
          val t1v = variant [t1,t2,f] (mk_var("t1f", rhs_ty))
          val t2v = variant [t1v,t1,t2,f] (mk_var("t2f", rhs_ty))
          val ft1 = mk_comb(f, t1)
          val ft2 = mk_comb(f, t2)
        in
          list_mk_abs([t1,t2,t1v,t2v],
                      Term.subst [ft1 |-> t1v, ft2 |-> t2v] r)
        end
  val lamcase =
      case lookup lam_con alist of
        NONE => list_mk_abs([genvar (stringSyntax.string_ty --> nc_ty),
                             genvar (stringSyntax.string_ty --> rhs_ty)],
                            mk_arb rhs_ty)
      | SOME (c, (cargs, r)) => let
          val string_ty = stringSyntax.string_ty
          val uvar = hd cargs
          val bodyvar = hd (tl cargs)
          (* "term function variable" *)
          val tfv = variant [f] (mk_var("tf", string_ty --> nc_ty))
          (* "result function variable" *)
          val rfv = variant [f,tfv] (mk_var("rf", string_ty --> rhs_ty))
          val newv = variant [f,tfv,rfv] (mk_var("v", string_ty))
          val fbody = mk_comb(f, bodyvar)
          val absv = mk_comb(inst[alpha |-> nc_arg_ty]abs_con, tfv)
          val newbody =
              Term.subst [bodyvar |-> mk_comb(tfv, newv)]
                         (Term.subst [fbody |-> mk_comb(rfv, newv),
                                      uvar |-> newv] r)
          val inst_fv = inst[alpha |-> nc_arg_ty]fv_con
          val attach_let = mk_let(mk_abs(newv, newbody),
                                  mk_comb(new_con, mk_comb(inst_fv, absv)))
        in
          list_mk_abs([tfv, rfv], attach_let)
        end
  val recursion_exists0 =
      SPECL [concase, varcase, appcase, lamcase]
            (INST_TYPE [alpha |-> nc_arg_ty, beta |-> rhs_ty]
                       ncTheory.nc_RECURSION_WEAK)
  val recursion_exists =
      CONV_RULE (BINDER_CONV
                   (EVERY_CONJ_CONV
                      (STRIP_QUANT_CONV (RAND_CONV LIST_BETA_CONV))) THENC
                 RAND_CONV (ALPHA_CONV f))
                recursion_exists0

  val (_, eqns) = dest_exists (concl recursion_exists)
  val homv = mk_var("hom", type_of f)
  val renaming_goal =
      Term.subst [homv |-> f]
                 (Term.inst [alpha |-> nc_arg_ty, beta |-> rhs_ty]
                            renaming_goal_form)
  val eqns_assumed = ASSUME eqns

  val (renaming_proved0, have_renaming) =
      (default_prover(mk_imp(eqns, renaming_goal),
                      STRIP_TAC THEN
                      HO_MATCH_MP_TAC ncTheory.nc_INDUCTION2 THEN
                      SRW_TAC [][ISUB_CON, ISUB_VAR_RENAME, ISUB_APP,
                                 ABS_DEF] THEN
                      Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THEN
                      Q_TAC (NEW_TAC "z") `FVS R UNION DOM R UNION FV t` THEN
                      `LAM y t = LAM z ([VAR z/y] t)` by SRW_TAC [][ALPHA] THEN
                      SRW_TAC [][ISUB_LAM, SUB_ISUB_SINGLETON, ISUB_APPEND,
                                 RENAMING_THM, LET_THM]), true)
      handle HOL_ERR _ => (TRUTH, false)
  val renaming_proved = if have_renaming then UNDISCH renaming_proved0
                        else TRUTH
  val single_sub_proved0 =
      if have_renaming then
        simpLib.SIMP_RULE (srw_ss()) [RENAMING_THM, ISUB_def]
                          (Q.INST [`R` |-> `[(VAR y,x)]`]
                                  (SPEC_ALL renaming_proved))
      else TRUTH
  val single_sub_proved = GEN_ALL single_sub_proved0
  val new_eqns_assumed  =
      CONV_RULE (RAND_CONV
                 (RAND_CONV
                  (RAND_CONV
                   (STRIP_QUANT_CONV
                    (RAND_CONV
                     (SIMP_CONV bool_ss [SIMPLE_LET, single_sub_proved,
                                         ABS_DEF]))))))
                eqns_assumed
  val final_conclusion =
      LIST_CONJ [new_eqns_assumed, renaming_proved,
                 single_sub_proved]
  val final_exists =
      EXISTS(mk_exists(f, concl final_conclusion), f) final_conclusion
in
  CHOOSE(f, recursion_exists) final_exists
end;

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
end

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
      if have_renamings then
        SOME (save_thm(fstr^"_vsubst_invariant",
                       hd (List.rev (CONJUNCTS f_def))),
              save_thm(fstr^"_renaming_invariant",
                       hd (tl (List.rev (CONJUNCTS f_def)))))
      else NONE
  val _ = if have_renamings then let
              val (th1, th2) = valOf f_invariants
            in
              augment_srw_ss [rewrites [th1, th2]];
              adjoin_to_theory
              {sig_ps = NONE,
               struct_ps =
               SOME (fn pp =>
                        PP.add_string pp
                                      ("val _ = BasicProvers.augment_srw_ss "^
                                       "[simpLib.rewrites ["^
                                       fstr^"_vsubst_invariant,"^
                                       fstr^"_renaming_invariant]]\n"))}
            end
          else ()
in
  (f_thm, f_invariants)
end


val recursive_term_function_existence = prove_recursive_term_function_exists0

end (* struct *)
