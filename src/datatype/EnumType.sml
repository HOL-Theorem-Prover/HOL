(* ---------------------------------------------------------------------*)
(* Enumerated datatypes. An enumerated type with k constructors is      *)
(* represented by the natural numbers < k.                              *)
(* ---------------------------------------------------------------------*)

structure EnumType :> EnumType =
struct

open HolKernel boolLib numLib Parse;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars

infix THEN THENC |->
infixr -->

val NUM = num;
fun mk_int_numeral i = mk_numeral (Arbnum.fromInt i);

fun enum_pred k =
 let val n = mk_var("n",num)
     val topnum = mk_int_numeral k
 in mk_abs(n,mk_less(n,topnum))
 end;

fun type_exists k = let
  val n = mk_var("n",num)
in
  prove (mk_exists(n, mk_comb(enum_pred k, n)),
         EXISTS_TAC zero_tm THEN REDUCE_TAC)
end

fun num_values REP_ABS defs =
 let val len = length defs
     val top_numeral = mk_int_numeral len
     fun rep_of def =
      let val n = rand(rhs(concl def))
          val less_thm = EQT_ELIM (REDUCE_CONV (mk_less(n,top_numeral)))
          val thm = EQ_MP (SPEC n REP_ABS) less_thm
      in SUBS [SYM def] thm
      end
 in
   map rep_of defs
 end;

(* ----------------------------------------------------------------------
    Prove the datatype's cases theorem.  I.e.,
       !a. (a = c1) \/ (a = c2) \/ ... (a = cn)
   ---------------------------------------------------------------------- *)

(* first need a simple lemma: *)
val n_less_cases = prove(
  Term`!m n. n < m = ~(m = 0) /\ (let x = m - 1 in n < x \/ (n = x))`,
  REWRITE_TAC [LET_THM] THEN BETA_TAC THEN CONV_TAC numLib.ARITH_CONV);

fun onestep thm = let
  (* thm of form x < n, where n is a non-zero numeral *)
  val (x,n) = dest_less (concl thm)
  val thm0 = SPECL [n,x] n_less_cases
  val thm1 = EQ_MP thm0 thm
in
  CONV_RULE numLib.REDUCE_CONV thm1
end

fun prove_cases_thm repthm eqns = let
  (* repthm of form !a. ?n. (a = f n) /\ (n < x) *)
  val (avar, spec_rep_t) = dest_forall (concl repthm)
  val (nvar, rep_body_t) = dest_exists spec_rep_t
  val ass_rep_body = ASSUME rep_body_t
  val (aeq_thm, nlt_thm) = CONJ_PAIR ass_rep_body
  (* aeq_thm is of the form |- a = f n *)
  val repfn = rator (rand (concl aeq_thm))
  fun prove_cases nlt_thm eqns = let
    (* nlt_thm is of the form |- n < x     where x is non-zero *)
    (* eqns are of the form   |- d = f m   for various d and decreasing m *)
    (*                                     the first m is x - 1 *)
    fun prove_aeq neq eqn = let
      (* neq is of the form n = x *)
      (* eqn is of the form d = f x *)
      val fn_eq_fx = AP_TERM repfn neq
    in
      TRANS aeq_thm (TRANS fn_eq_fx (SYM eqn))
    end
    val ndisj_thm = onestep nlt_thm
    val ndisj_t = concl ndisj_thm
  in
    if is_disj ndisj_t then let
        (* recursive case *)
        val (new_lt_t, eq_t) = dest_disj ndisj_t
        val eq_thm = prove_aeq (ASSUME eq_t) (hd eqns)
        val eq_t = concl eq_thm
        val lt_thm = prove_cases (ASSUME new_lt_t) (tl eqns)
        val lt_t = concl lt_thm
      in
        DISJ_CASES ndisj_thm (DISJ1 lt_thm eq_t) (DISJ2 lt_t eq_thm)
      end
    else
      (* ndisjthm is |- n = 0   (base case) *)
      prove_aeq ndisj_thm (hd eqns)
  end
in
  REWRITE_RULE [GSYM DISJ_ASSOC]
  (GEN avar (CHOOSE (nvar, SPEC avar repthm) (prove_cases nlt_thm eqns)))
end

(* ----------------------------------------------------------------------
    Prove a datatype's induction theorem
   ---------------------------------------------------------------------- *)

fun prove_induction_thm cases_thm = let
  val (avar, cases_body) = dest_forall (concl cases_thm)
  val body_cases_thm = SPEC avar cases_thm
  val Pvar = mk_var("P", type_of avar --> bool)
  fun basecase eqthm = let
    (* eqthm of form |- a = c *)
    val ass_P = ASSUME (mk_comb(Pvar, rand (concl eqthm)))
  in
    EQ_MP (SYM (AP_TERM Pvar eqthm)) ass_P
  end
  fun recurse thm = let
    val (d1, d2) = dest_disj (concl thm)
  in
    DISJ_CASES thm (basecase (ASSUME d1)) (recurse (ASSUME d2))
  end handle HOL_ERR _ => basecase thm
  val base_thm = GEN avar (recurse body_cases_thm)
  val hyp_thm = ASSUME (list_mk_conj (hyp base_thm))
  fun foldfn (ass,th) = PROVE_HYP ass th
in
  GEN Pvar (DISCH_ALL (foldl foldfn base_thm (CONJUNCTS hyp_thm)))
end

(* ----------------------------------------------------------------------
    Make a size definition for an enumerated type (everywhere zero)
   ---------------------------------------------------------------------- *)

fun mk_size_definition ty = let
  val tyname = #1 (dest_type ty)
  val cname = tyname^"_size"
  val var_t = mk_var(cname, ty --> NUM)
  val avar = mk_var("x", ty)
  val def = new_definition(cname^"_def", mk_eq(mk_comb(var_t, avar), zero_tm))
in
  SOME (rator (lhs (#2 (strip_forall (concl def)))), TypeBase.ORIG def)
end

(* ----------------------------------------------------------------------
    Prove distinctness theorem for an enumerated type
      (only done if there are not too many possibilities as there will
       be n-squared many of these)
   ---------------------------------------------------------------------- *)

fun gen_triangle l = let
  (* generate the upper triangle of the cross product of the list with *)
  (* itself.  Leave out the diagonal *)
  fun gen_row i [] acc = acc
    | gen_row i (h::t) acc = gen_row i t ((i,h)::acc)
  fun doitall [] acc = acc
    | doitall (h::t) acc = doitall t (gen_row h t acc)
in
  List.rev (doitall l [])
end

fun prove_distinctness_thm simpls constrs = let
  val upper_triangle = gen_triangle constrs
  fun prove_inequality (c1, c2) =
      (REWRITE_CONV simpls THENC numLib.REDUCE_CONV) (mk_eq(c1,c2))
in
  LIST_CONJ (map (EQF_ELIM o prove_inequality) upper_triangle)
end

(* ----------------------------------------------------------------------
    Prove initiality theorem for type
   ---------------------------------------------------------------------- *)

fun alphavar n = mk_var("x"^Int.toString n, alpha)

local
  val n = mk_var("n", NUM)

in

fun prove_initiality_thm rep ty constrs simpls = let
  val ncases = length constrs


  fun generate_ntree lo hi =
      (* invariant: lo <= hi *)
      if lo = hi then alphavar lo
      else let
          val midpoint = (lo + hi) div 2
          val ltree = generate_ntree lo midpoint
          val rtree = generate_ntree (midpoint + 1) hi
        in
          mk_cond (mk_leq(n, mk_int_numeral midpoint), ltree, rtree)
        end

  val witness = let
    val x = mk_var("x", ty)
    val body = generate_ntree 0 (ncases - 1)
  in
    mk_abs(x, mk_let(mk_abs(n, body), mk_comb(rep, x)))
  end

  fun prove_clause (n, constr) =
      EQT_ELIM
        ((LAND_CONV BETA_CONV THENC REWRITE_CONV simpls THENC
                    numLib.REDUCE_CONV)
           (mk_eq(mk_comb(witness, constr), alphavar n)))

  fun gen_clauses (_, []) = []
    | gen_clauses (n, (h::t)) = prove_clause (n, h) :: gen_clauses (n + 1, t)

  val clauses_thm = LIST_CONJ (gen_clauses (0, constrs))
  val f = mk_var("f", ty --> alpha)
  val clauses = subst [witness |-> f] (concl clauses_thm)

  val exists_thm = EXISTS(mk_exists(f, clauses), witness) clauses_thm

  fun gen_it n th = if n < 0 then th
                    else gen_it (n - 1) (GEN (alphavar n) th)
in
  gen_it (ncases - 1) exists_thm
end;

end (* local *)





(*---------------------------------------------------------------------------*)
(* The main entrypoints                                                      *)
(*---------------------------------------------------------------------------*)

fun define_enum_type(name,clist,ABS,REP) =
 let val tydef = new_type_definition(name, type_exists (length clist))
     val bij = define_new_type_bijections
                  {ABS=ABS, REP=REP,name=name^"_BIJ", tyax=tydef}
     val ABS_REP  = save_thm(ABS^"_"^REP, CONJUNCT1 bij)
     val REP_ABS  = save_thm(REP^"_"^ABS, BETA_RULE (CONJUNCT2 bij))
     val ABS_11   = save_thm(ABS^"_11",   BETA_RULE (prove_abs_fn_one_one bij))
     val REP_11   = save_thm(REP^"_11",   BETA_RULE (prove_rep_fn_one_one bij))
     val ABS_ONTO = save_thm(ABS^"_ONTO", BETA_RULE (prove_abs_fn_onto bij))
     val REP_ONTO = save_thm(REP^"_ONTO", BETA_RULE (prove_rep_fn_onto bij))
     val TYPE     = type_of(fst(dest_forall(concl REP_11)))
     val ABSconst = mk_const(ABS, NUM --> TYPE)
     val REPconst = mk_const(REP, TYPE --> NUM)
     val nclist   = enumerate 0 clist
     fun def(n,s) = (s,mk_eq(mk_var(s,TYPE),
                             mk_comb(ABSconst,mk_int_numeral n)))
     val defs     = map (new_definition o def) nclist
     val constrs  = map (lhs o concl) defs
     val simpls   = GSYM REP_11::num_values REP_ABS defs
 in
    {TYPE     = TYPE,
     constrs  = constrs,
     defs     = defs,
     ABSconst = ABSconst,
     REPconst = REPconst,
     ABS_REP  = ABS_REP,
     REP_ABS  = REP_ABS,
     ABS_11   = ABS_11,
     REP_11   = REP_11,
     ABS_ONTO = ABS_ONTO,
     REP_ONTO = REP_ONTO,
     simpls   = simpls
    }
 end;

fun enum_type_to_tyinfo (ty, constrs) = let
  val abs = "num2"^ty
  val rep = ty^"2num"
  val (result as {constrs,simpls,TYPE,...}) =
      define_enum_type(ty,constrs,abs,rep)
  val nchotomy = prove_cases_thm (#ABS_ONTO result) (List.rev (#defs result))
  val induction = prove_induction_thm nchotomy
  val size = mk_size_definition TYPE
  val distinct =
      if length constrs > 20 then NONE
      else SOME (prove_distinctness_thm simpls constrs)
  val initiality = prove_initiality_thm (#REPconst result) TYPE constrs simpls
  val case_def = hd (Prim_rec.define_case_constant initiality)
  open TypeBase TypeBase.TypeInfo
  val tyinfo0 =
      mk_tyinfo { ax = ORIG initiality,
                  induction = ORIG induction,
                  case_def = case_def,
                  case_cong = TRUTH,
                  nchotomy = nchotomy,
                  size = size,
                  one_one = NONE,
                  distinct = distinct }
  val simpls = case distinct of
                 NONE => case_def :: simpls
               | SOME thm => [case_def, CONJ thm (GSYM thm)]
in
  put_simpls simpls tyinfo0
end




end (* struct *)

(* Example *)

(* val res as {TYPE,constrs,defs, ABSconst, REPconst,
            ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = define_enum_type
            ("colour", ["red", "green", "blue", "brown", "white"],
             "num2colour", "colour2num");


val res1 as {TYPE,constrs,defs, ABSconst, REPconst,
            ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = Count.apply define_enum_type
       ("thing", ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8",
                  "a9", "a10", "a11", "a12", "a13", "a14", "a15", "a16",
                  "a17", "a18", "a19", "a20", "a21", "a22", "a23", "a24",
                  "a25", "a26", "a27", "a28", "a29", "a30", "a31", "a32",
                  "a33", "a34", "a35", "a36", "a37", "a38", "a39", "a40",
                  "a41", "a42", "a43", "a44", "a45", "a46", "a47", "a48",
                  "a49", "a50", "a51", "a52", "a53", "a54", "a55", "a56",
                  "a57", "a58", "a59", "a60", "a61", "a62", "a63", "a64"],
        "num2thing", "thing2num");


(* Example of something else that could easily be proved: weak
   induction. Problem with this is that abstraction is not being
   supported.

fun prove_rep_bound REPconst TYPE =
 let val a = mk_var("a",TYPE)
     val v = mk_var("v",TYPE)
     val tm0 = mk_comb (REPconst, a)
     val tm1 = mk_comb (REPconst, v)
     val th0 = REFL tm0
     val tm2 = mk_exists(v,mk_eq(tm0,tm1))
     val th1 = EXISTS (tm2,a) th0
     val th2 = PURE_REWRITE_RULE [GSYM REP_ONTO] th1
 in GEN a th2
 end;

val CHAR_INDUCT_THM = Q.store_thm
("WEAK_INDUCT_THM",
 `!P. (!n. n < 256 ==> P (ABS n)) ==> !x. P x`,
REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `c` CHR_ONTO)
  THEN RW_TAC bool_ss []);

*)

*)

