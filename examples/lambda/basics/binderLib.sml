structure binderLib :> binderLib =
struct

open HolKernel Parse boolLib
open BasicProvers SingleStep simpLib

local open pred_setTheory in end

open NEWLib
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars stringTheory.string_grammars
end
open Parse

fun ERR f msg = raise (HOL_ERR {origin_function = f,
                                origin_structure = "binderLib",
                                message = msg})

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

(* recursion theorems are stored in SPEC_ALL form, with preconditions as one
   big set of conjuncts (rather than iterated implications) *)
val type_db =
    ref (Binarymap.mkDict String.compare : (string,thm) Binarymap.dict)

(*  testing code

type_db :=
     Binarymap.insert(!type_db, "nc",
                      SIMP_RULE (srw_ss()) [] (Q.INST [`X` |-> `{}`]
                                               swap_RECURSION_generic))

type_db :=
   Binarymap.insert(!type_db, "term",
                    SIMP_RULE (srw_ss()) [] (Q.INST [`X` |-> `{}`]
                                             termTheory.swap_RECURSION))
*)

fun recthm_for_type ty = let
  val {Tyop,...} = dest_thy_type ty
in
  SOME (Binarymap.find(!type_db, Tyop))
end handle Binarymap.NotFound => NONE
         | HOL_ERR _ => NONE

fun myfind f [] = NONE
  | myfind f (h::t) = case f h of NONE => myfind f t | x => x

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
          ERR "prove_recursive_term_function_exists"
              "All conjuncts must be equations"
  val f = rator (lhs (hd conjs))
  val _ = List.all (fn t => rator (lhs t) = f) conjs orelse
          ERR "prove_recursive_term_function_exists"
              "Must define same constant in all equations"
  val _ = List.all (fn t => length (#2 (strip_comb (lhs t))) = 1) conjs orelse
          ERR "prove_recursive_term_function_exists"
              "Function being defined must be applied to one argument"
  val dom_ty = #1 (dom_rng (type_of f))
  val recthm = valOf (recthm_for_type dom_ty)
               handle Option => ERR "prove_recursive_term_function_exists"
                                    ("No recursion theorem for type "^
                                     type_to_string dom_ty)
  val constructors = map #1 (find_constructors recthm)
  val () =
      case List.find
           (fn t => List.all
                      (fn c => not
                                 (same_const c
                                             (#1 (strip_comb (rand (lhs t))))))
                      constructors) conjs of
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

val null_fv = ``combin$K pred_set$EMPTY : 'a -> string -> bool``
val null_swap = ``\x:string y:string z:'a. z``
val null_apm = ``combin$K combin$I : (string # string)list -> 'a -> 'a``
val null_info = {nullfv = mk_arb alpha,
                 inst = ["rFV" |-> (fn () => null_fv),
                         "rswap" |-> (fn () => null_swap),
                         "apm" |-> (fn () => null_apm)],
                 rewrites = []}

type range_type_info = {nullfv : term,
                        inst : {redex : string, residue : unit -> term} list,
                        rewrites : thm list}

val range_database = ref (Binarymap.mkDict String.compare)

fun force_inst {src, to_munge} = let
  val inst = match_type (type_of to_munge) (type_of src)
in
  Term.inst inst to_munge
end

exception InfoProofFailed of term
fun with_info_prove_recn_exists f finisher dom_ty rng_ty lookup info = let
  val {nullfv, inst, rewrites} = info
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
    val recvars = free_vars (concl recursion_exists0)
    fun findvar {redex,residue} =
        case List.find (fn t => #1 (dest_var t) = redex) recvars of
          SOME v => let val residue' = residue()
                    in
                      SOME (v |-> force_inst {src = v, to_munge = residue'})
                    end
        | NONE => NONE
  in
    List.mapPartial findvar inst
  end
  val recursion_exists1 = INST other_var_inst recursion_exists0
  val recursion_exists =
      CONV_RULE (RAND_CONV
                   (BINDER_CONV
                      (EVERY_CONJ_CONV
                         (STRIP_QUANT_CONV (RAND_CONV LIST_BETA_CONV))) THENC
                      RAND_CONV (ALPHA_CONV f)))
                   recursion_exists1
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
  val callthis = with_info_prove_recn_exists f fin dom_ty rng_ty find_eqn
in
  case Lib.total dest_type rng_ty of
    SOME (tyop, args) => let
    in
      case Binarymap.peek(!range_database, tyop) of
        NONE => callthis null_info
      | SOME i => callthis i
        handle InfoProofFailed tm =>
               (HOL_WARNING
                  "binderLib"
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
  val f_thm = prove_recursive_term_function_exists0 ALL_CONV tm
  val (f_v, f_body) = dest_exists (concl f_thm)
  val defining_body = CONJUNCT1 (ASSUME f_body)
  val result = EQT_ELIM (SIMP_CONV bool_ss [defining_body] tm)
in
  CHOOSE (f_v, f_thm) (EXISTS (mk_exists(f_v, tm), f_v) result)
end handle InfoProofFailed tm =>
           raise ERR "prove_recursive_term_function_exists"
                     ("Couldn't prove function with swap over range - \n\
                      \goal was "^term_to_string tm)

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
                      \goal was "^term_to_string tm)


fun define_wrapper worker q = let
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
  val f_thm0 = worker tm
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
  end
  val f_def =
      new_specification (fstr^"_def", [fstr], base_definition)
  val _ = add_const fstr
  val f_const = prim_mk_const {Name = fstr, Thy = current_theory()}
  val f_thm = save_thm(fstr^"_thm",
                       default_prover(subst [f_t |-> f_const] tm,
                                      SIMP_TAC bool_ss [f_def]))
  val f_invariants = let
    val interesting_bit = CONJUNCT2 f_def
  in
    save_thm(fstr^"_swap_invariant", interesting_bit) before
    BasicProvers.export_rewrites [fstr^"_swap_invariant"]
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
