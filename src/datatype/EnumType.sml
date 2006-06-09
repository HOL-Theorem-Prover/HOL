(* ---------------------------------------------------------------------*)
(* Enumerated datatypes. An enumerated type with k constructors is      *)
(* represented by the natural numbers < k.                              *)
(* ---------------------------------------------------------------------*)

structure EnumType :> EnumType =
struct

open HolKernel boolLib Parse numLib;

type tyinfo = TypeBasePure.tyinfo;

val ERR = mk_HOL_ERR "EnumType";
val NUM = num;

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars;

fun enum_pred k =
 let val n = mk_var("n",num)
     val topnum = term_of_int k
 in mk_abs(n,mk_less(n,topnum))
 end;

fun type_exists k =
 let val n = mk_var("n",num)
 in prove (mk_exists(n, mk_comb(enum_pred k, n)),
           EXISTS_TAC zero_tm THEN REDUCE_TAC)
 end

fun num_values REP_ABS defs =
 let val len = length defs
     val top_numeral = term_of_int len
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

fun mk_size_definition ty =
 let val tyname = #1 (dest_type ty)
     val cname = tyname^"_size"
     val var_t = mk_var(cname, ty --> NUM)
     val avar = mk_var("x", ty)
     val def = new_definition(cname^"_def",
                              mk_eq(mk_comb(var_t, avar), zero_tm))
 in
   SOME (rator (lhs (#2 (strip_forall (concl def)))), TypeBasePure.ORIG def)
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

fun prove_distinctness_thm simpls constrs =
 let val upper_triangle = gen_triangle constrs
     fun prove_inequality (c1, c2) =
        (REWRITE_CONV simpls THENC numLib.REDUCE_CONV) (mk_eq(c1,c2))
 in
   if null upper_triangle then NONE else
   SOME (LIST_CONJ (map (EQF_ELIM o prove_inequality) upper_triangle))
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
          mk_cond (mk_leq(n, term_of_int midpoint), ltree, rtree)
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
                             mk_comb(ABSconst,term_of_int n)))
     val defs     = map (new_definition o def) nclist
     val constrs  = map (lhs o concl) defs
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
     REP_ONTO = REP_ONTO
    }
 end;

val (COND_T, COND_F) = CONJ_PAIR (SPEC_ALL COND_CLAUSES)
fun define_case (case_const_name, rep_t, rep_th, constrs) = let
  val sz = length constrs
  val m = mk_var("m", numSyntax.num)
  fun V n = mk_var("v" ^ Int.toString n, alpha)
  open numSyntax
  fun mk_decision_tree lo hi =
      if lo < hi then
        if lo + 1 = hi then
          mk_cond(mk_eq(m, mk_numeral (Arbnum.fromInt lo)),
                  V lo, V hi)
        else let
            val mid = (lo + hi) div 2
          in
            mk_cond(mk_less(m, mk_numeral (Arbnum.fromInt mid)),
                    mk_decision_tree lo (mid - 1),
                    mk_decision_tree mid hi)
          end
      else if lo = hi then V lo
      else raise Fail "can't happen 101"
  val (ty, _) = dom_rng (type_of rep_t)
  val case_t = mk_var(case_const_name,
                      list_mk_fun(List.tabulate(sz, K alpha), ty --> alpha))
  val args = List.tabulate(sz, (fn n => mk_var("v" ^ Int.toString n,
                                               alpha)))
  val e_t = mk_var("x", ty)
  val def_t = mk_eq(mk_comb(list_mk_comb(case_t, args), e_t),
                    mk_comb(mk_abs(m, mk_decision_tree 0 (sz - 1)),
                            mk_comb(rep_t, e_t)))
  val def_th = new_definition(case_const_name, def_t)
  val bare_def_th = SPEC_ALL def_th
  fun mk_consequence e = let
    val th = INST [e_t |-> e] bare_def_th
    val th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV [rep_th]) THENC
                                   BETA_CONV)) th
    fun follow_conds t =
        if is_cond t then
          (RATOR_CONV (RATOR_CONV (RAND_CONV (numLib.REDUCE_CONV))) THENC
           (REWR_CONV COND_T ORELSEC REWR_CONV COND_F) THENC follow_conds) t
        else ALL_CONV t
  in
    GENL args (CONV_RULE (RAND_CONV follow_conds) th)
  end
in
  save_thm(case_const_name ^ "_def",
           LIST_CONJ (map mk_consequence constrs))
end


fun enum_eq_CONV eq_elim_th repth t = let
  (* keying will have already ensured that t is an equality between two
     values in the enumerated type *)
  val (l, r) = dest_eq t
  val _ = is_const l andalso is_const r orelse
          raise ERR "enum_eq_CONV" "Equality not between constants"
in
  REWR_CONV eq_elim_th THENC REWRITE_CONV [repth] THENC
  numLib.REDUCE_CONV
end t

fun update_tyinfo tyname eqth repth tyinfo0 = let
  open TypeBasePure
  val ty = type_of (hd (#1 (strip_forall (concl eqth))))
  val x = mk_var("x", ty) and y = mk_var("y", ty)
  val {convs, rewrs} = simpls_of tyinfo0
  val new_conv = {name = tyname ^ "const_eq_CONV",
                  key = SOME ([], mk_eq(x, y)),
                  trace = 3,
                  conv = K (K (enum_eq_CONV eqth repth))}
in
  put_simpls {convs = new_conv::convs, rewrs = rewrs} tyinfo0
end


fun enum_type_to_tyinfo (ty, constrs) = let
  val abs = "num2"^ty
  val rep = ty^"2num"
  val (result as {constrs,TYPE,...}) = define_enum_type(ty,constrs,abs,rep)
  val abs_thm = save_thm(abs ^ "_thm", LIST_CONJ (map SYM (#defs result)))
  val rep_name = rep ^ "_thm"
  val rep_thm = save_thm(rep_name, 
                   LIST_CONJ (num_values (#REP_ABS result) (#defs result)))
  val eq_elim_name = ty^"_EQ_"^ty
  val eq_elim_th = save_thm(eq_elim_name, GSYM (#REP_11 result))
  val simpls = [rep_thm, eq_elim_th]
  val nchotomy = prove_cases_thm (#ABS_ONTO result) (List.rev (#defs result))
  val induction = prove_induction_thm nchotomy
  val size = mk_size_definition TYPE
  val distinct =
      if length constrs > 15 then NONE
      else prove_distinctness_thm simpls constrs
  val initiality = prove_initiality_thm (#REPconst result) TYPE constrs simpls
  val rep_t = rator (lhs (hd (strip_conj (concl rep_thm))))
  val case_def = define_case (ty ^ "_case", rep_t, rep_thm, constrs)
  val case_cong = Prim_rec.case_cong_thm nchotomy case_def
  open TypeBasePure
  val tyinfo0 =
      mk_datatype_info 
         {ax = ORIG initiality,
          induction = ORIG induction,
          case_def = case_def,
          case_cong = case_cong,
          nchotomy = nchotomy,
          size = size,
          encode = NONE,
          lift = NONE,
          one_one = NONE,
          fields = [],
          accessors = [],
          updates = [],
          distinct = distinct }
in
  case distinct of
    NONE => (update_tyinfo ty eq_elim_th rep_thm tyinfo0,
             "EnumType.update_tyinfo "^mlquote ty^" "^
             eq_elim_name^" "^rep_name^" ")
  | SOME thm => (tyinfo0, "")
end

val _ = Parse.temp_set_grammars ambient_grammars

end (* struct *)

(*---------------------------------------------------------------------------
               Examples
 ---------------------------------------------------------------------------*)

(*

val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO}
  = time define_enum_type
            ("colour", ["red", "green", "blue", "brown", "white"],
             "num2colour", "colour2num");

val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;

val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = define_enum_type
            ("foo", ["B0", "B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8",
                     "B9", "B10", "B11", "B12", "B13", "B14", "B15", "B16",
                     "B17", "B18", "B19", "B20", "B21", "B22", "B23", "B24",
                     "B25", "B26", "B27", "B28", "B29", "B30"],
             "num2foo", "foo2num");

val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;

val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = define_enum_type
            ("bar", ["C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8",
                     "C9", "C10", "C11", "C12", "C13", "C14", "C15", "C16",
                     "C17", "C18", "C19", "C20", "C21", "C22", "C23", "C24",
                     "C25", "C26", "C27", "C28", "C29", "C30", "C31", "C32",
                     "C33", "C34", "C35", "C36", "C37", "C38", "C39", "C40"],
             "num2bar", "bar2num");
val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;


val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = define_enum_type
            ("dar", ["D0", "D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8",
                     "D9", "D10", "D11", "D12", "D13", "D14", "D15", "D16",
                     "D17", "D18", "D19", "D20", "D21", "D22", "D23", "D24",
                     "D25", "D26", "D27", "D28", "D29", "D30", "D31", "D32",
                     "D33", "D34", "D35", "D36", "D37", "D38", "D39", "D40",
                     "D41", "D42", "D43", "D44", "D45", "D46", "D47", "D48",
                     "D49", "D50", "D51","D52","D53","D54","D55"],
             "num2dar", "dar2num");
val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;

val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO}
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
val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;

val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = Count.apply define_enum_type
       ("thing", ["z0", "z1", "z2", "z3", "z4", "z5", "z6", "z7", "z8",
                  "z9", "z10", "z11", "z12", "z13", "z14", "z15", "z16",
                  "z17", "z18", "z19", "z20", "z21", "z22", "z23", "z24",
                  "z25", "z26", "z27", "z28", "z29", "z30", "z31", "z32",
                  "z33", "z34", "z35", "z36", "z37", "z38", "z39", "z40",
                  "z41", "z42", "z43", "z44", "z45", "z46", "z47", "z48",
                  "z49", "z50", "z51", "z52", "z53", "z54", "z55", "z56",
                  "z57", "z58", "z59", "z60", "z61", "z62", "z63", "z64",
                  "z65", "z66", "z67", "z68", "z69", "z70", "z71", "z72",
                  "z73", "z74", "z75"],
        "num2thing", "thing2num");

val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;


val {TYPE,constrs,defs, ABSconst, REPconst,
     ABS_REP, REP_ABS, ABS_11, REP_11, ABS_ONTO, REP_ONTO, simpls}
  = Count.apply define_enum_type
       ("thing", ["Z0", "Z1", "Z2", "Z3", "Z4", "Z5", "Z6", "Z7", "Z8",
                  "Z9", "Z10", "Z11", "Z12", "Z13", "Z14", "Z15", "Z16",
                  "Z17", "Z18", "Z19", "Z20", "Z21", "Z22", "Z23", "Z24",
                  "Z25", "Z26", "Z27", "Z28", "Z29", "Z30", "Z31", "Z32",
                  "Z33", "Z34", "Z35", "Z36", "Z37", "Z38", "Z39", "Z40",
                  "Z41", "Z42", "Z43", "Z44", "Z45", "Z46", "Z47", "Z48",
                  "Z49", "Z50", "Z51", "Z52", "Z53", "Z54", "Z55", "Z56",
                  "Z57", "Z58", "Z59", "Z60", "Z61", "Z62", "Z63", "Z64",
                  "Z65", "Z66", "Z67", "Z68", "Z69", "Z70", "Z71", "Z72",
                  "Z73", "Z74", "Z75", "Z76", "Z77", "Z78", "Z79", "Z80",
                  "Z81", "Z82", "Z83", "Z84", "Z85", "Z86", "Z87", "Z88",
                  "Z89", "Z90", "Z91", "Z92", "Z93", "Z94", "Z95", "Z96",
                  "Z97", "Z98", "Z99"],
        "num2thing", "thing2num");

val initiality =
  Count.apply (prove_initiality_thm REPconst TYPE constrs) simpls;
val case_def = Count.apply define_case initiality;
val nchotomy = Count.apply (prove_cases_thm ABS_ONTO) (rev defs);
val case_cong = Count.apply (case_cong_thm nchotomy) case_def;


fun gen_enum n = let
  fun recurse acc n =
      if n <= 0 then [QUOTE (String.concat ("foo = " :: acc))]
      else recurse (("E"^Int.toString n^ " | ") :: acc) (n - 1)
in
  recurse ["E"^Int.toString n] (n - 1)
end

fun enum_test n = Hol_datatype (gen_enum n)

*)
