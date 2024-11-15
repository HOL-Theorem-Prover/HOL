structure binderLib :> binderLib =
struct

open HolKernel Parse boolLib
open BasicProvers simpLib

open nomsetTheory

open NEWLib
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars nomsetTheory.nomset_grammars
end
open Parse

val tmToString =
    term_to_string
        |> with_flag (Parse.current_backend, PPBackEnd.raw_terminal)
        |> trace ("Unicode", 0)


val ERR = mk_HOL_ERR "binderLib"

datatype nominaltype_info =
         NTI of { recursion_thm : thm option,
                  (* recursion theorems are stored in SPEC_ALL form, with
                     preconditions as one big set of conjuncts (rather than
                     iterated implications) *)
                  nullfv : term,
                  pm_constant : term,
                  pm_rewrites : thm list,
                  fv_rewrites : thm list,
                  binders : (term * int * thm) list }

fun nti_null_fv (NTI{nullfv, ...}) = nullfv
fun nti_perm_t (NTI{pm_constant,...}) = pm_constant
fun nti_recursion (NTI{recursion_thm,...}) = recursion_thm




(* ----------------------------------------------------------------------
    prove_recursive_term_function_exists tm

    for the 'a nc type tm would be roughly of the form

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
    prove that the side-conditions on the recursion theorem for the given
    type actually hold.

   ---------------------------------------------------------------------- *)

val type_db =
    ref (Binarymap.mkDict KernelSig.name_compare :
         (KernelSig.kernelname,nominaltype_info) Binarymap.dict)

val string_ty = stringSyntax.string_ty
val stringset_ty = pred_setSyntax.mk_set_type string_ty

fun mk_icomb(f,x) = let
  val (dom,rng) = dom_rng (type_of f)
  val i = match_type dom (type_of x)
in
  mk_comb(Term.inst i f, x)
end

fun findmap_terms f t = let
  fun recurse acc tlist =
      case tlist of
        [] => acc
      | t::ts => let
          val acc' = case f t of
                       NONE => acc
                     | SOME result => result::acc
        in
          case dest_term t of
            COMB(f,x) => recurse acc' (f::x::ts)
          | LAMB(_,b) => recurse acc' (b::ts)
          | _ => recurse acc' ts
        end
in
  recurse [] [t]
end

fun isdbty ty = let
  val {Thy,Tyop,...} = dest_thy_type ty
in
  isSome (Binarymap.peek(!type_db, {Thy=Thy,Name=Tyop}))
end handle HOL_ERR _ => false

fun tylookup ty = let
  val {Thy,Tyop,...} = dest_thy_type ty
in
  Binarymap.peek(!type_db, {Thy=Thy,Name=Tyop})
end handle HOL_ERR _ => NONE

fun get_pm_rewrites ty =
    case tylookup ty of
      NONE => []
    | SOME (NTI i) => #pm_rewrites i

fun findfirst f t = let
  fun recurse tlist =
      case tlist of
        [] => NONE
      | t::ts => let
        in
          case f t of
            NONE => let
            in
              case dest_term t of
                COMB(f,x) => recurse (f::x::ts)
              | LAMB(_,b) => recurse (b::ts)
              | _ => recurse ts
            end
          | x => x
        end
in
  recurse [t]
end

fun find_top_terms P t = let
  fun recurse acc tlist =
      case tlist of
        [] => acc
      | t::ts => let
        in
          if P t then recurse (t::acc) ts
          else
            case dest_term t of
              COMB(f,x) => recurse acc (f::x::ts)
            | LAMB(_,b) => recurse acc (b::ts)
            | _ => recurse acc ts
        end
in
  recurse [] [t]
end

val supp_t = prim_mk_const{Name = "supp", Thy = "nomset"}
fun find_avoids (t, (strs, sets)) = let
  open stringSyntax
  fun isdbty t = let
    val ty = type_of t
    val {Thy,Tyop,...} = dest_thy_type ty
  in
    if is_var t then
      case Binarymap.peek(!type_db, {Thy=Thy,Name=Tyop}) of
        NONE => NONE
      | SOME (NTI data) => SOME (mk_icomb(mk_icomb(supp_t, #pm_constant data),
                                          t))
    else NONE
  end handle HOL_ERR _ => NONE
  fun eqty ty t = type_of t = ty
  val strings = List.filter (fn t => is_var t orelse is_string_literal t)
                            (find_top_terms (eqty string_ty) t)
  val stringsets = List.filter is_var (find_terms (eqty stringset_ty) t)
  val fv_terms = findmap_terms isdbty t
  open HOLset
in
  (addList(strs,strings), addList(addList(sets, fv_terms), stringsets))
end

fun goalnames (asl, w) = let
  val fvs = FVL (w::asl) empty_tmset
  fun foldthis(t,acc) = HOLset.add(acc, #1 (dest_var t))
in
  HOLset.listItems (HOLset.foldl foldthis (HOLset.empty String.compare) fvs)
end

fun FRESH_TAC (g as (asl, w)) = let
  val (strs, sets) = List.foldl find_avoids (empty_tmset, empty_tmset) (w::asl)
  val finite_sets = List.mapPartial (total pred_setSyntax.dest_finite) asl
  fun filterthis t = not (is_var t) orelse tmem t finite_sets
  val sets' = List.filter filterthis (HOLset.listItems sets)
  fun get_binder already_done t =
      case tylookup (type_of t) of
        NONE => NONE
      | SOME (NTI info) => let
          val bs = #binders info
          fun checkthis (_,i,th) = let
            val l = lhs (#2 (strip_forall
                               (#2 (dest_imp (#2 (strip_forall (concl th)))))))
            val argi = List.nth(#2 (strip_comb t), i)
          in
            if can (match_term l) t andalso
               not (HOLset.member(already_done, argi))
            then SOME (t, i, th)
            else NONE
          end handle Subscript => NONE
        in
          get_first checkthis bs
        end
  fun do_one used strs sets' (g as (asl, w)) =
      case get_first (findfirst (get_binder used)) (w::asl) of
        NONE => raise ERR "FRESH_TAC" "No binders present in goal"
      | SOME (t, i, th) => let
          val old = List.nth (#2 (strip_comb t), i)
          val (pre,l,r) = let
            val (_, b) = strip_forall (concl th)
            val (pre, eq) = dest_imp b
            val (l,r) = dest_eq (#2 (strip_forall eq))
          in
            (pre,l,r)
          end
          val base = case total Literal.dest_string_lit old of
                       NONE => #1 (dest_var old)
                     | SOME s => s
          val newname = Lexis.gen_variant Lexis.tmvar_vary (goalnames g) base
          val new_in_thm = List.nth (#2 (strip_comb r), i)
          val new_t = mk_var(newname, type_of new_in_thm)
          val th' = PART_MATCH (lhs o #2 o strip_forall o #2 o dest_imp)
                               th
                               t
          val th' = INST [new_in_thm |-> new_t] th'
          val avoid_t = let
            open pred_setSyntax
          in
            List.foldl mk_union (mk_set (HOLset.listItems strs)) sets'
          end
          fun freshcont freshthm = let
            val th = MP th' freshthm
          in
            SUBST_ALL_TAC th THEN
            ASM_SIMP_TAC (srw_ss()) (basic_swapTheory.swapstr_def ::
                                     get_pm_rewrites (type_of t))
          end

          val tac =
              NEW_TAC newname avoid_t THEN
              SUBGOAL_THEN (#1 (dest_imp (concl th'))) freshcont THENL [
                ASM_SIMP_TAC (srw_ss()) [],
                TRY (do_one (HOLset.add(used,new_t))
                            (HOLset.add(strs,new_t))
                            sets')
              ]
        in
          tac g
        end
in
  do_one empty_tmset strs sets' g
end

fun recthm_for_type ty = let
  val {Tyop,Thy,...} = dest_thy_type ty
  val NTI {recursion_thm,...} = Binarymap.find(!type_db, {Name=Tyop,Thy=Thy})
in
  recursion_thm
end handle HOL_ERR _ => NONE
         | Binarymap.NotFound => NONE

fun find_constructors recthm = let
  val (_, c) = dest_imp (concl recthm)
  val (homvar, body) = dest_exists c
  val eqns = let val (c1, c2) = dest_conj body
             in
               if is_conj c1 then c1
               else body
             end
  fun dest_eqn t = let
    val eqn_proper = #2 (strip_imp (#2 (strip_forall t)))
  in
    (#1 (strip_comb (rand (lhs eqn_proper))), #1 (strip_comb (rhs eqn_proper)))
  end
in
  map dest_eqn (strip_conj eqns)
end

fun check_for_errors tm = let
  val conjs = map (#2 o strip_forall) (strip_conj tm)
  val _ = List.all is_eq conjs orelse
          raise ERR "prove_recursive_term_function_exists"
              "All conjuncts must be equations"
  val f = rator (lhs (hd conjs))
  val _ = List.all (fn t => rator (lhs t) ~~ f) conjs orelse
          raise ERR "prove_recursive_term_function_exists"
              "Must define same constant in all equations"
  val _ = List.all (fn t => length (#2 (strip_comb (lhs t))) = 1) conjs orelse
          raise ERR "prove_recursive_term_function_exists"
              "Function being defined must be applied to one argument"
  val dom_ty = #1 (dom_rng (type_of f))
  val recthm = valOf (recthm_for_type dom_ty)
               handle Option =>
               raise ERR "prove_recursive_term_function_exists"
                 ("No recursion theorem for type " ^ type_to_string dom_ty)
  val constructors = map #1 (find_constructors recthm)
  val () =
      case List.find
           (fn t => List.all
                      (fn c => not
                                 (same_const c
                                             (#1 (strip_comb (rand (lhs t))))))
                      constructors) conjs of
        NONE => ()
      | SOME t => raise ERR "prove_recursive_term_function_exists"
                      ("Unknown constructor "^
                       tmToString (#1 (strip_comb (rand (lhs t)))))
  val () =
      case get_first
           (fn t => let val (c, args) = strip_comb (rand (lhs t))
                    in
                      case List.find (not o is_var) args of
                        NONE => NONE
                      | SOME v => SOME (v, c)
                    end) conjs of
        NONE => ()
      | SOME (v, c) =>
        raise ERR "prove_recursive_term_function_exists"
            (#1 (dest_const c)^"^'s argument "^tmToString v^
             " is not a variable")
in
  (f, conjs)
end

val null_apm = ``nomset$mk_pmact (combin$K combin$I) : 'a nomset$pmact``
val nameless_nti =
    NTI { nullfv = mk_arb alpha,
          pm_constant = null_apm,
          pm_rewrites = [nomsetTheory.discretepm_raw, combinTheory.K_THM,
                         combinTheory.I_THM],
          fv_rewrites = [],
          recursion_thm = NONE,
          binders = []}


val range_database = ref (Binarymap.mkDict String.compare)

fun force_inst {src, to_munge} = let
  val inst = match_type (type_of to_munge) (type_of src)
in
  Term.inst inst to_munge
end

val cpm_ty = let val sty = stringSyntax.string_ty
             in
               listSyntax.mk_list_type (pairSyntax.mk_prod (sty, sty))
             end

fun mk_perm_ty ty = mk_thy_type {Tyop = "pmact", Thy = "nomset", Args = [ty]}

exception InfoProofFailed of term
fun with_info_prove_recn_exists f finisher dom_ty rng_ty lookup info = let
  val NTI {nullfv, pm_rewrites, fv_rewrites, pm_constant, ...} = info
  fun mk_simple_abstraction (c, (cargs, r)) = list_mk_abs(cargs, r)
  val recthm = valOf (recthm_for_type dom_ty)
  val hom_t = #1 (dest_exists (#2 (dest_imp (concl recthm))))
  val base_inst = match_type (type_of hom_t) (type_of f)
  val nullfv = let
    val i = match_type (type_of nullfv) rng_ty
  in
    Term.inst i nullfv
  end
  val constructors = find_constructors recthm
  fun do_a_constructor (c, fnterm) =
      case lookup c of
        SOME (user_c, (args, r_term)) => let
          fun hasdom_ty t = Type.compare(type_of t, dom_ty) = EQUAL
          val rec_args = filter hasdom_ty args
          val f_applied =
              map (fn t => mk_comb(f, t) |-> genvar rng_ty) rec_args
          val new_body = Term.subst f_applied r_term
          val base_abs = list_mk_abs (args, new_body)
          val with_reccalls = list_mk_abs (map #residue f_applied, base_abs)
        in
          force_inst {src = with_reccalls, to_munge = fnterm} |-> with_reccalls
        end
      | NONE => let
          val fnterm' = Term.inst base_inst fnterm
          fun build_abs ty = let
            val (d,r) = dom_rng ty
          in
            mk_abs(genvar (Type.type_subst base_inst d), build_abs r)
          end handle HOL_ERR _ => nullfv
        in
          fnterm' |-> build_abs (type_of fnterm)
        end
  val recursion_exists0 =
      INST (map do_a_constructor constructors) (INST_TYPE base_inst recthm)
  val other_var_inst = let
    val apm = mk_var("apm", mk_perm_ty rng_ty)
    val pm' = force_inst {src = apm, to_munge = pm_constant}
  in
    [apm |-> pm']
  end
  val recursion_exists1 = INST other_var_inst recursion_exists0
  val recursion_exists =
      CONV_RULE (RAND_CONV
                   (BINDER_CONV
                      (EVERY_CONJ_CONV
                         (STRIP_QUANT_CONV (RAND_CONV LIST_BETA_CONV))) THENC
                      RAND_CONV (ALPHA_CONV f)))
                   recursion_exists1
  val rewrites = pm_rewrites @ fv_rewrites
  val precondition_discharged =
      CONV_RULE
        (LAND_CONV (SIMP_CONV (srw_ss()) rewrites THENC
                    SIMP_CONV (srw_ss()) [pred_setTheory.SUBSET_DEF] THENC
                    finisher))
        recursion_exists
in
  MP precondition_discharged TRUTH
     handle HOL_ERR _ =>
            raise InfoProofFailed (#1 (dest_imp
                                         (concl precondition_discharged)))
end;



fun prove_recursive_term_function_exists0 fin tm = let
  val (f, conjs) = check_for_errors tm

  val (dom_ty, rng_ty) = dom_rng (type_of f)

  fun insert (x as (c, rhs)) alist =
      case alist of
        [] => [(c,rhs)]
      | (h as (c',rhs')) :: t => if same_const c c' then
                                   raise ERR "prove_recursive_term_function_exists"
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
  val callthis = with_info_prove_recn_exists f fin dom_ty rng_ty find_eqn
in
  case Lib.total dest_thy_type rng_ty of
    SOME {Tyop, Thy, ...} => let
    in
      case Binarymap.peek(!type_db, {Name=Tyop,Thy=Thy}) of
        NONE => callthis nameless_nti |> REWRITE_RULE [discretepm_thm]
      | SOME i => callthis i
        handle InfoProofFailed tm =>
               (HOL_WARNING
                  "binderLib"
                  "prove_recursive_term_function_exists"
                  ("Couldn't prove function with swap over range - \n\
                   \goal was "^tmToString tm^"\n\
                   \trying null range assumption");
                callthis nameless_nti |> REWRITE_RULE [discretepm_thm])
    end
  | NONE => callthis nameless_nti |> REWRITE_RULE [discretepm_thm]
end handle InfoProofFailed tm =>
           raise ERR "prove_recursive_term_function_exists"
                     ("Couldn't prove function with swap over range - \n\
                      \goal was "^tmToString tm)

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
  val f_thm = prove_recursive_term_function_exists0 ALL_CONV tm
  val (f_v, f_body) = dest_exists (concl f_thm)
  val defining_body = CONJUNCT1 (ASSUME f_body)
  val result = EQT_ELIM (SIMP_CONV bool_ss [defining_body] tm)
in
  CHOOSE (f_v, f_thm) (EXISTS (mk_exists(f_v, tm), f_v) result)
end handle InfoProofFailed tm =>
           raise ERR "prove_recursive_term_function_exists"
                     ("Couldn't prove function with swap over range - \n\
                      \goal was "^tmToString tm)

fun prove_recursive_term_function_exists' fin tm = let
  val f_thm = prove_recursive_term_function_exists0 fin tm
  val (f_v, f_body) = dest_exists (concl f_thm)
  val defining_body = CONJUNCT1 (ASSUME f_body)
  val result = EQT_ELIM (SIMP_CONV bool_ss [defining_body] tm)
in
  CHOOSE (f_v, f_thm) (EXISTS (mk_exists(f_v, tm), f_v) result)
end handle InfoProofFailed tm =>
           raise ERR "prove_recursive_term_function_exists"
                     ("Couldn't prove function with swap over range - \n\
                      \goal was "^tmToString tm)


fun define_wrapper worker q = let
  val a = Absyn q
  val f = head_sym a
  val fstr = case f of
      Absyn.IDENT(_, s) => s
    | x => raise ERR "define_recursive_term_function" "invalid head symbol"
  val restore_this = hide fstr
  fun restore() = Parse.update_overload_maps fstr restore_this
  val tm = Parse.absyn_to_term (Parse.term_grammar()) a
           handle e => (restore(); raise e)
  val _ = restore()
  val f_thm0 = BETA_RULE (worker tm)
  val (f_t0, th_body0) = dest_exists (concl f_thm0)
  val f_t = mk_var(fstr, type_of f_t0)
  val th_body = subst [f_t0 |-> f_t] th_body0
  fun defining_conj c = let
    val fvs = List.filter (fn v => #1 (dest_var v) <> fstr) (free_vars c)
  in
    list_mk_forall(fvs, c)
  end
  val defining_term0 = list_mk_conj(map defining_conj (strip_conj tm))
  val defining_term = mk_conj(defining_term0, rand th_body)
  val base_definition = let
    (* this checks that the user-provided term is a consequence of the
       existential theorem that prove_recursive_term_function_exists0
       returns.  It might go wrong if extra implications appear as
       side-conditions to equations on binder-constructors.  This can't
       happen in this version of the code yet (because we don't handle
       parameters or side sets *)
    val definition_ok0 = default_prover(mk_imp(th_body, defining_term),
                                        SIMP_TAC bool_ss [])
  in
    CHOOSE (f_t, f_thm0)
           (EXISTS(mk_exists(f_t, defining_term), f_t)
                  (UNDISCH definition_ok0))
  end handle HOL_ERR _ => f_thm0
  (* feel that having the equation the other way (non-GSYMed) 'round may be
     better in many theorem-proving circumstances.  But for the moment,
     this way round provides backwards compatibility. *)
  val base_definition =
      CONV_RULE (QUANT_CONV (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])))
                base_definition

  val f_def =
      new_specification (fstr^"_def", [fstr], base_definition)
  val _ = add_const fstr
  val f_const = prim_mk_const {Name = fstr, Thy = current_theory()}
  val f_thm = save_thm(fstr^"_thm",
                       default_prover(subst [f_t |-> f_const] tm,
                                      SIMP_TAC bool_ss [f_def])
                       handle HOL_ERR _ => CONJUNCT1 f_def)
  val f_invariants = let
    val interesting_bit =
        f_def |> CONJUNCT2
              |> PURE_REWRITE_RULE [combinTheory.K_THM, combinTheory.I_THM]
    val (l,r) =
        interesting_bit |> concl |> strip_forall |> #2
                        |> strip_imp |> #2
                        |> dest_eq
    val (lf,_) = strip_comb l
    val (rf, _) = strip_comb r
    val nm = fstr^"_equivariant"
  in
    save_thm(nm, interesting_bit) before export_rewrites [nm]
  end
in
  (f_thm, f_invariants)
end


fun define_recursive_term_function q =
    define_wrapper (prove_recursive_term_function_exists0 ALL_CONV) q

fun define_recursive_term_function' fin q =
    define_wrapper (prove_recursive_term_function_exists0 fin) q


val recursive_term_function_existence =
    prove_recursive_term_function_exists0 ALL_CONV





end (* struct *)
