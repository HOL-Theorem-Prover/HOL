structure integerScript =
struct

(*==========================================================================*)
(* Theory of integers. (John Harrison)                                      *)
(*                                                                          *)
(* The integers are constructed as equivalence classes of pairs of integers *)
(* using the quotient type procedure.                                       *)
(*                                                                          *)
(* This theory was constructed for use in the HOL-ELLA system, using many of*)
(* the principles, and some of the code, used in the reals library. It is my*)
(* eventual intention to produce a more unified library of number systems.  *)
(*                                                                          *)
(* October/November 1999.                                                   *)
(* Extensions by Michael Norrish to define exponentiation, division and     *)
(* modulus.                                                                 *)
(*                                                                          *)
(*==========================================================================*)


open HolKernel Parse boolLib

val _ = new_theory "integer";

(* interactive mode
  app load ["jrhUtils", "quotient", "liteLib", "QLib",
            "BasicProvers", "boolSimps", "pairSimps",
            "numSimps", "numLib", "metisLib"];
*)
open jrhUtils quotient liteLib
     arithmeticTheory prim_recTheory numTheory
     simpLib numLib boolTheory liteLib metisLib BasicProvers;


val int_ss = boolSimps.bool_ss ++ numSimps.old_ARITH_ss ++ pairSimps.PAIR_ss;

(*---------------------------------------------------------------------------*)
(* Following incantation needed since pairLib is now loaded, and that adds   *)
(* pairTheory.pair_rws to the implicit set of rewrites for REWRITE_TAC.      *)
(* Usually that is good, but for some of the proofs below, that makes things *)
(* worse.                                                                    *)
(*---------------------------------------------------------------------------*)

val _ = Rewrite.set_implicit_rewrites Rewrite.bool_rewrites;

(*--------------------------------------------------------------------------*)
(* Required lemmas about the natural numbers - mostly to drive CANCEL_TAC   *)
(*--------------------------------------------------------------------------*)

val EQ_LADD = store_thm("EQ_LADD",
			Term `!x y z. (x + y = x + z) = (y = z)`,
			ARITH_TAC)


val EQ_ADDL = store_thm("EQ_ADDL",
			Term `!x y. (x = x + y) = (y = 0)`,
			ARITH_TAC)

val LT_LADD = store_thm("LT_LADD",
			Term `!x y z. (x + y) < (x + z) = y < z`,
			ARITH_TAC)

val LT_ADDL = store_thm("LT_ADDL",
			Term `!x y. x < (x + y) = 0 < y`,
			ARITH_TAC)

val LT_ADDR = store_thm("LT_ADDR",
			Term `!x y. ~((x + y) < x)`,
			ARITH_TAC)

val LT_ADD2 =
    store_thm("LT_ADD2",
	      Term`!x1 x2 y1 y2. x1 < y1 /\ x2 < y2 ==> (x1 + x2) < (y1 + y2)`,
		  ARITH_TAC);

(*--------------------------------------------------------------------------*)
(* CANCEL_CONV - Try to cancel, rearranging using AC laws as needed         *)
(*                                                                          *)
(* The first two arguments are the associative and commutative laws, as     *)
(* given to AC_CONV. The remaining list of theorems should be of the form:  *)
(*                                                                          *)
(* |- (a & b ~ a & c) = w (e.g. b ~ c)                                      *)
(* |-    (a & b ~ a)  = x (e.g. F)                                          *)
(* |-     (a ~ a & c) = y (e.g. T)                                          *)
(* |-         (a ~ a) = z (e.g. F)                                          *)
(*                                                                          *)
(* For some operator (written as infix &) and relation (~).                 *)
(*                                                                          *)
(* Theorems may be of the form |- ~ P or |- P, rather than equations, they  *)
(* will be transformed to |- P = F and |- P = T automatically if needed.    *)
(*                                                                          *)
(* Note that terms not cancelled will remain in their original order, but   *)
(* will be flattened to right-associated form.                              *)
(*--------------------------------------------------------------------------*)

fun CANCEL_CONV (assoc,sym,lcancelthms) tm =
  let fun pair_from_list [x, y] = (x, y)
        | pair_from_list _ = raise Match
      val lcthms =
      map ((fn th => (assert (is_eq o concl)) th
	    handle _ => EQF_INTRO th
		handle _ => EQT_INTRO th) o SPEC_ALL) lcancelthms
      val (eqop, binop) = pair_from_list (map
        (rator o rator o lhs o snd o strip_forall o concl) [hd lcthms, sym])
      fun strip_binop tm =
	  if (rator(rator tm) = binop handle _ => false) then
	      (strip_binop (rand(rator tm))) @ (strip_binop(rand tm))
	  else [tm]
      val mk_binop = ((curry mk_comb) o (curry mk_comb binop))
      val list_mk_binop = end_itlist mk_binop

      fun rmel i list = op_set_diff aconv list [i]

      val (_, (l1, r1)) = (assert (equal eqop) ## pair_from_list)
        (strip_comb tm)
      val (l, r) = pair_from_list (map strip_binop [l1, r1])
      val i = op_intersect aconv l r
  in
      if i = [] then raise Fail ""
      else
	  let val itm = list_mk_binop i
	      val (l', r') = pair_from_list
		  (map (end_itlist (C (curry op o)) (map rmel i)) [l, r])
	      val (l2, r2) = pair_from_list
		  (map (fn ts => mk_binop itm (list_mk_binop ts)
		       handle _ => itm) [l',r'])
	      val (le, re) = pair_from_list
		  (map (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq)[(l1,l2),(r1,r2)])
	      val eqv = MK_COMB(AP_TERM eqop le,re)
	  in
	      CONV_RULE(RAND_CONV(end_itlist (curry(op ORELSEC))
				  (map REWR_CONV lcthms))) eqv
	  end
  end handle _ => failwith "CANCEL_CONV";



(*--------------------------------------------------------------------------*)
(* Tactic to do all the obvious simplifications via cancellation etc.       *)
(*--------------------------------------------------------------------------*)

val CANCEL_TAC =
    (C (curry (op THEN)) (REWRITE_TAC []) o
     CONV_TAC o ONCE_DEPTH_CONV o end_itlist (curry (op ORELSEC)))
    (map CANCEL_CONV [(ADD_ASSOC,ADD_SYM,
		       [EQ_LADD, EQ_ADDL, ADD_INV_0_EQ, EQ_SYM_EQ]),
		      (ADD_ASSOC,ADD_SYM,
		       [LT_LADD, LT_ADDL, LT_ADDR, LESS_REFL])]);

(*--------------------------------------------------------------------------*)
(* Define operations on representatives.                                    *)
(*--------------------------------------------------------------------------*)

val _ = print "Defining operations on pairs of naturals\n"

val tint_0 = new_definition("tint_0",
			    Term `tint_0 = (1,1)`);

val tint_1 = new_definition("tint_1",
			    Term `tint_1 = (1 + 1,1)`);

val tint_neg = new_definition("tint_neg",
			      Term `tint_neg (x:num,(y:num)) = (y,x)`);

val tint_add =
    new_infixl_definition
    ("tint_add",
     Term`$tint_add (x1,y1) (x2,y2) = (x1 + x2, y1 + y2)`,
     500);

val tint_mul =
    new_infixl_definition
    ("tint_mul",
     Term `$tint_mul (x1,y1) (x2,y2) = ((x1 * x2) + (y1 * y2),
					(x1 * y2) + (y1 * x2))`,
     600);

val tint_lt = new_definition (
  "tint_lt",
  Term `$tint_lt (x1,y1) (x2,y2) = (x1 + y2) < (x2 + y1)`);
val _ = temp_set_fixity "tint_lt" (Infix(NONASSOC, 450))

(*--------------------------------------------------------------------------*)
(* Define the equivalence relation and prove it *is* one                    *)
(*--------------------------------------------------------------------------*)

val _ = print "Define equivalence relation over pairs of naturals\n"

val tint_eq = new_definition(
  "tint_eq",
  Term `$tint_eq (x1,y1) (x2,y2) = (x1 + y2 = x2 + y1)`);
val _ = temp_set_fixity "tint_eq" (Infix(NONASSOC, 450));

val TINT_EQ_REFL =
    store_thm("TINT_EQ_REFL",
	      Term `!x. x tint_eq x`,
	      GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]);

val TINT_EQ_SYM =
    store_thm("TINT_EQ_SYM",
	      Term `!x y. x tint_eq y = y tint_eq x`,
	      REPEAT GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
	                          THEN ARITH_TAC)

val TINT_EQ_TRANS =
    store_thm("TINT_EQ_TRANS",
	      Term `!x y z. x tint_eq y /\ y tint_eq z ==> x tint_eq z`,
		  REPEAT GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
	                          THEN ARITH_TAC)

val TINT_EQ_EQUIV = store_thm("TINT_EQ_EQUIV",
  Term `!p q. p tint_eq q = ($tint_eq p = $tint_eq q)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV (Term `r:num#num`))) THEN EQ_TAC
  THENL
  [DISCH_THEN(MP_TAC o SPEC (Term `q:num#num`)) THEN REWRITE_TAC[TINT_EQ_REFL],
   DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TINT_EQ_SYM]), ALL_TAC] THEN
   POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
   MATCH_ACCEPT_TAC TINT_EQ_TRANS]);

val TINT_EQ_AP =
    store_thm("TINT_EQ_AP",
	      Term `!p q. (p = q) ==> p tint_eq q`,
		  REPEAT GEN_PAIR_TAC
		  THEN REWRITE_TAC[tint_eq,pairTheory.PAIR_EQ]
		  THEN ARITH_TAC)

(*--------------------------------------------------------------------------*)
(* Prove the properties of representatives                                  *)
(*--------------------------------------------------------------------------*)

val _ = print "Proving various properties of pairs of naturals\n"

val TINT_10 =
    store_thm("TINT_10",
	      Term `~(tint_1 tint_eq tint_0)`,
	      REWRITE_TAC[tint_1, tint_0, tint_eq]
	      THEN ARITH_TAC)

val TINT_ADD_SYM =
    store_thm("TINT_ADD_SYM",
	      Term `!x y. x tint_add y = y tint_add x`,
	      REPEAT GEN_PAIR_TAC
	      THEN REWRITE_TAC[tint_eq,tint_add,pairTheory.PAIR_EQ]
	      THEN ARITH_TAC)

val TINT_MUL_SYM =
    store_thm("TINT_MUL_SYM",
	      Term `!x y. x tint_mul y = y tint_mul x`,
	      REPEAT GEN_PAIR_TAC
	      THEN REWRITE_TAC[tint_eq,tint_mul,pairTheory.PAIR_EQ]
	      THEN SIMP_TAC int_ss [MULT_SYM])

val TINT_ADD_ASSOC =
    store_thm
    ("TINT_ADD_ASSOC",
     Term `!x y z. x tint_add (y tint_add z) = (x tint_add y) tint_add z`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,pairTheory.PAIR_EQ,ADD_ASSOC])

val TINT_MUL_ASSOC =
    store_thm
    ("TINT_MUL_ASSOC",
     Term `!x y z. x tint_mul (y tint_mul z) = (x tint_mul y) tint_mul z`,
     REPEAT GEN_PAIR_TAC
     THEN
     REWRITE_TAC[tint_mul, pairTheory.PAIR_EQ, LEFT_ADD_DISTRIB,
		 RIGHT_ADD_DISTRIB]
     THEN
     SIMP_TAC int_ss [MULT_ASSOC]);

val TINT_LDISTRIB =
    store_thm
    ("TINT_LDISTRIB",
     Term `!x y z. x tint_mul (y tint_add z) =
                   (x tint_mul y) tint_add (x tint_mul z)`,
     REPEAT GEN_PAIR_TAC THEN
     REWRITE_TAC[tint_mul, tint_add,pairTheory.PAIR_EQ, LEFT_ADD_DISTRIB]
     THEN CANCEL_TAC);

val TINT_ADD_LID =
    store_thm
    ("TINT_ADD_LID",
     Term `!x. (tint_0 tint_add x) tint_eq x`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,tint_0,tint_eq]
     THEN ARITH_TAC);

val TINT_MUL_LID =
    store_thm
    ("TINT_MUL_LID",
     Term `!x. (tint_1 tint_mul x) tint_eq x`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_mul,tint_1,tint_eq]
     THEN ARITH_TAC)

val TINT_ADD_LINV =
    store_thm
    ("TINT_ADD_LINV",
     Term `!x. ((tint_neg x) tint_add x) tint_eq tint_0`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,tint_0,tint_eq,tint_neg]
     THEN ARITH_TAC)

val TINT_LT_TOTAL =
    store_thm
    ("TINT_LT_TOTAL",
     Term `!x y. x tint_eq y \/ x tint_lt y \/ y tint_lt x`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_lt,tint_eq]
     THEN ARITH_TAC)

val TINT_LT_REFL =
    store_thm("TINT_LT_REFL",
	      Term `!x. ~(x tint_lt x)`,
	      REPEAT GEN_PAIR_TAC
	      THEN REWRITE_TAC[tint_lt]
	      THEN ARITH_TAC)

fun unfold_dec l =  REPEAT GEN_PAIR_TAC THEN REWRITE_TAC l THEN ARITH_TAC;

val TINT_LT_TRANS =
    store_thm
    ("TINT_LT_TRANS",
     Term `!x y z. x tint_lt y /\ y tint_lt z ==> x tint_lt z`,
     unfold_dec[tint_lt])


val TINT_LT_ADD =
    store_thm
    ("TINT_LT_ADD",
     Term `!x y z. (y tint_lt z) ==> (x tint_add y) tint_lt (x tint_add z)`,
     unfold_dec[tint_lt,tint_add])

val TINT_LT_MUL =
    store_thm
    ("TINT_LT_MUL",
     Term `!x y. tint_0 tint_lt x /\ tint_0 tint_lt y ==>
            tint_0 tint_lt (x tint_mul y)`,
     REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_0, tint_lt, tint_mul] THEN
     CANCEL_TAC THEN DISCH_THEN(CONJUNCTS_THEN
		      (CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1))
     THEN  SIMP_TAC int_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB])

(*--------------------------------------------------------------------------*)
(* Prove that the operations on representatives are well-defined            *)
(*--------------------------------------------------------------------------*)

val TINT_NEG_WELLDEF =
    store_thm
    ("TINT_NEG_WELLDEF",
     Term `!x1 x2. x1 tint_eq x2 ==> (tint_neg x1) tint_eq (tint_neg x2)`,
     unfold_dec[tint_eq,tint_neg])

val TINT_ADD_WELLDEFR =
    store_thm
    ("TINT_ADD_WELLDEFR",
     Term`!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_add y) tint_eq (x2 tint_add y)`,
     unfold_dec[tint_eq,tint_add])

val TINT_ADD_WELLDEF =
    store_thm
    ("TINT_ADD_WELLDEF",
     Term `!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
	 (x1 tint_add y1) tint_eq (x2 tint_add y2)`,
     unfold_dec[tint_eq,tint_add])

val TINT_MUL_WELLDEFR =
    store_thm
    ("TINT_MUL_WELLDEFR",
     Term`!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_mul y) tint_eq (x2 tint_mul y)`,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_mul, tint_eq] THEN
  ONCE_REWRITE_TAC[jrhUtils.AC(ADD_ASSOC,ADD_SYM)
    (Term `(a + b) + (c + d) =
           (a + d) + (b + c)`)] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val TINT_MUL_WELLDEF =
    store_thm
    ("TINT_MUL_WELLDEF",
     Term `!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
	 (x1 tint_mul y1) tint_eq (x2 tint_mul y2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TINT_EQ_TRANS THEN EXISTS_TAC (Term `x1 tint_mul y2`) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TINT_MUL_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TINT_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);

val TINT_LT_WELLDEFR =
    store_thm
    ("TINT_LT_WELLDEFR",
     Term `!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_lt y = x2 tint_lt y)`,
     unfold_dec[tint_eq,tint_lt])

val TINT_LT_WELLDEFL =
    store_thm
    ("TINT_LT_WELLDEFL",
     Term `!x y1 y2. y1 tint_eq y2 ==> (x tint_lt y1 = x tint_lt y2)`,
     unfold_dec[tint_eq,tint_lt])

val TINT_LT_WELLDEF =
    store_thm
    ("TINT_LT_WELLDEF",
     Term `!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
	 (x1 tint_lt y1 = x2 tint_lt y2)`,
     unfold_dec[tint_eq,tint_lt]);

(*--------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism tint_of_num:num->tint.             *)
(*--------------------------------------------------------------------------*)

val tint_of_num =
    new_recursive_definition
      {name = "tint_of_num",
       rec_axiom = prim_recTheory.num_Axiom,
       def = Term `(tint_of_num 0 = tint_0) /\
                   (tint_of_num (SUC n) = (tint_of_num n) tint_add tint_1)`};

(* Could do the following if wished:
val _ = add_numeral_form(#"t", SOME "tint_of_num");
*)

val tint_of_num_PAIR =
    GEN_ALL (SYM (ISPEC(Term `tint_of_num n`) (pairTheory.PAIR)));

val tint_of_num_eq =
    store_thm("tint_of_num_eq",
	      Term `!n. FST (tint_of_num n) = SND (tint_of_num n) + n`,
	      INDUCT_TAC
              THENL
                [ SIMP_TAC int_ss [tint_of_num,tint_0],

                  REWRITE_TAC [tint_of_num]
                  THEN ONCE_REWRITE_TAC [tint_of_num_PAIR]
                  THEN ASM_REWRITE_TAC [tint_1,tint_add]
                  THEN SIMP_TAC int_ss []
                ])

val TINT_INJ =
    store_thm("TINT_INJ",
	      Term `!m n. (tint_of_num m tint_eq tint_of_num n) = (m = n)`,
	      INDUCT_TAC THEN INDUCT_TAC
              THEN REPEAT (POP_ASSUM MP_TAC)
              THEN REWRITE_TAC [tint_of_num]
              THEN ONCE_REWRITE_TAC [tint_of_num_PAIR]
              THEN REWRITE_TAC [tint_0,tint_1,tint_add,tint_eq,tint_of_num_eq]
              THEN SIMP_TAC int_ss [])

val NUM_POSTINT_EX =
    store_thm("NUM_POSTINT_EX",
	      Term `!t. ~(t tint_lt tint_0) ==> ?n. t tint_eq tint_of_num n`,
		  GEN_TAC THEN DISCH_TAC THEN
		  Q.EXISTS_TAC `FST t - SND t`
                   THEN POP_ASSUM MP_TAC
                   THEN ONCE_REWRITE_TAC [GSYM pairTheory.PAIR]
                   THEN REWRITE_TAC [tint_0,tint_lt,tint_eq,tint_of_num_eq]
                   THEN SIMP_TAC int_ss []);

(*--------------------------------------------------------------------------*)
(* Now define the functions over the equivalence classes                    *)
(*--------------------------------------------------------------------------*)

val _ = print "Establish type of integers\n";

local
    fun mk_def (d,t,n,f) = {def_name=d, fixity=f, fname=n, func=t}
in
    val [INT_10, INT_ADD_SYM, INT_MUL_SYM,
	 INT_ADD_ASSOC, INT_MUL_ASSOC, INT_LDISTRIB,
	 INT_ADD_LID, INT_MUL_LID, INT_ADD_LINV,
	 INT_LT_TOTAL, INT_LT_REFL, INT_LT_TRANS,
	 INT_LT_LADD_IMP, INT_LT_MUL,
         int_of_num, INT_INJ, NUM_POSINT_EX] =
	define_equivalence_type
	{name = "int", equiv = TINT_EQ_EQUIV,
	 defs = [mk_def ("int_0", Term `tint_0`,     "int_0", NONE),
		 mk_def ("int_1", Term `tint_1`,     "int_1", NONE),
		 mk_def ("int_neg",Term `tint_neg`,  "int_neg",   NONE),
		 mk_def ("int_add",Term `$tint_add`, "int_add",   NONE),
		 mk_def ("int_mul",Term `$tint_mul`, "int_mul",   NONE),
		 mk_def ("int_lt",Term `$tint_lt`,   "int_lt",    NONE),
                 mk_def ("int_of_num",Term `tint_of_num`,"int_of_num",NONE)],

	 welldefs = [TINT_NEG_WELLDEF, TINT_LT_WELLDEF,
		     TINT_ADD_WELLDEF, TINT_MUL_WELLDEF],
	 old_thms = ([TINT_10] @
		     (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
		      [TINT_ADD_SYM, TINT_MUL_SYM, TINT_ADD_ASSOC,
		       TINT_MUL_ASSOC, TINT_LDISTRIB]) @
		     [TINT_ADD_LID, TINT_MUL_LID, TINT_ADD_LINV,
		      TINT_LT_TOTAL, TINT_LT_REFL, TINT_LT_TRANS,
		      TINT_LT_ADD, TINT_LT_MUL,
                      LIST_CONJ (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
                                     (CONJUNCTS tint_of_num)),
                      TINT_INJ, NUM_POSTINT_EX])}
end;

val _ = Theory.save_thm ("INT_10",INT_10)
val _ = Theory.save_thm ("INT_ADD_SYM",INT_ADD_SYM)
val INT_ADD_COMM = Theory.save_thm("INT_ADD_COMM", INT_ADD_SYM);
val _ = Theory.save_thm ("INT_MUL_SYM",INT_MUL_SYM)
val INT_MUL_COMM = Theory.save_thm("INT_MUL_COMM", INT_MUL_SYM);
val _ = Theory.save_thm ("INT_ADD_ASSOC",INT_ADD_ASSOC)
val _ = Theory.save_thm ("INT_MUL_ASSOC",INT_MUL_ASSOC)
val _ = Theory.save_thm ("INT_LDISTRIB",INT_LDISTRIB)
val _ = Theory.save_thm ("INT_LT_TOTAL",INT_LT_TOTAL)
val _ = Theory.save_thm ("INT_LT_REFL",INT_LT_REFL)
val _ = Theory.save_thm ("INT_LT_TRANS",INT_LT_TRANS)
val _ = Theory.save_thm ("INT_LT_LADD_IMP",INT_LT_LADD_IMP)
val _ = Theory.save_thm ("INT_LT_MUL",INT_LT_MUL)
val _ = Theory.save_thm ("int_of_num",int_of_num)
val _ = Theory.save_thm ("INT_INJ",INT_INJ)
val _ = Theory.save_thm ("NUM_POSINT_EX",NUM_POSINT_EX)
;

val _ = overload_on ("+", Term`int_add`);
val _ = overload_on ("<", Term`int_lt`);
val _ = overload_on ("*", Term`int_mul`);


(* this is a slightly tricky case; we don't have to call overload_on
   on the boolean negation, but we're doing so to put it back at the
   top of the list of possible resolutions. *)

val bool_not = Term`$~`
val _ = overload_on ("~", Term`int_neg`);
val _ = overload_on ("~", bool_not);
val _ = overload_on ("numeric_negate", ``int_neg``);


(*--------------------------------------------------------------------------*)
(* Define subtraction and the other orderings                               *)
(*--------------------------------------------------------------------------*)

val int_sub =
    new_infixl_definition("int_sub",
			 Term `$int_sub x y = x + ~y`,
			 500);
val _ = overload_on ("-",  Term`$int_sub`);

val int_le = new_definition("int_le", Term `int_le x y = ~(y<x:int)`);
val _ = overload_on ("<=", Term`$int_le`);

val int_gt = new_definition("int_gt", Term `int_gt (x:int) y = y < x`);
val _ = overload_on (">",  Term`$int_gt`);

val int_ge = new_definition("int_ge", Term `int_ge x y = y <= x:int`)
val _ = overload_on (">=", Term`$int_ge`);

(*--------------------------------------------------------------------------*)
(* Now use the lifted inclusion homomorphism int_of_num:num->int.           *)
(*--------------------------------------------------------------------------*)

val _ = add_numeral_form(#"i", SOME "int_of_num");

val INT_0 =
    store_thm("INT_0",
	      Term `int_0 = 0i`,
	      REWRITE_TAC[int_of_num]);

val INT_1 =
    store_thm("INT_1",
	      Term `int_1 = 1i`,
	      REWRITE_TAC[ONE, int_of_num, INT_ADD_LID]);

(*--------------------------------------------------------------------------*)
(* Prove lots of boring ring theorems                                       *)
(*--------------------------------------------------------------------------*)

val _ = print "Prove \"lots of boring ring theorems\"\n";

(* already defined, but using the wrong term for 0 *)
val INT_ADD_LID =
    store_thm("INT_ADD_LID",
              Term`!x:int. 0 + x = x`,
              SIMP_TAC int_ss [GSYM INT_0, INT_ADD_LID]);
val _ = export_rewrites ["INT_ADD_LID"]


val INT_ADD_RID =
    store_thm("INT_ADD_RID",
	      Term `!x:int. x + 0 = x`,
	      PROVE_TAC [INT_ADD_COMM,INT_ADD_LID])
val _ = export_rewrites ["INT_ADD_RID"]


(* already defined, but using the wrong term for 0 *)
val INT_ADD_LINV =
    store_thm("INT_ADD_LINV",
              Term`!x. ~x + x = 0`,
              SIMP_TAC int_ss [GSYM INT_0, INT_ADD_LINV]);
val INT_ADD_RINV =
    store_thm("INT_ADD_RINV",
	      Term `!x. x + ~x = 0`,
	      ONCE_REWRITE_TAC [INT_ADD_SYM] THEN
              REWRITE_TAC [INT_ADD_LINV])

(* already defined, but using the wrong term for 1 *)
val INT_MUL_LID =
    store_thm("INT_MUL_LID",
              Term`!x:int. 1 * x = x`,
              SIMP_TAC int_ss [GSYM INT_1, INT_MUL_LID])
val INT_MUL_RID =
    store_thm("INT_MUL_RID",
	      Term `!x:int. x * 1 = x`,
	      PROVE_TAC [INT_MUL_SYM,GSYM INT_1,INT_MUL_LID])
val _ = export_rewrites ["INT_MUL_RID"]

val INT_RDISTRIB =
    store_thm("INT_RDISTRIB",
	      Term `!(x:int) y z. (x + y) * z = (x * z) + (y * z)`,
              ONCE_REWRITE_TAC [INT_MUL_COMM] THEN
              REWRITE_TAC [INT_LDISTRIB])

val INT_EQ_LADD =
    store_thm("INT_EQ_LADD",
	      Term `!(x:int) y z. (x + y = x + z) = (y = z)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o AP_TERM (Term `$+ ~x`)), ALL_TAC] THEN
	      SIMP_TAC int_ss [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID])


val INT_EQ_RADD =
    store_thm("INT_EQ_RADD",
	      Term `!x:int y z. (x + z = y + z) = (x = y)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_EQ_LADD]);

val INT_ADD_LID_UNIQ =
    store_thm("INT_ADD_LID_UNIQ",
	      Term `!x:int y. (x + y = y) = (x = 0)`,
	      REPEAT GEN_TAC THEN
	      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                empty_rewrites [GSYM INT_ADD_LID]
	      THEN SIMP_TAC int_ss [INT_EQ_RADD])

val INT_ADD_RID_UNIQ =
    store_thm("INT_ADD_RID_UNIQ",
	      Term `!x:int y. (x + y = x) = (y = 0)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_ADD_LID_UNIQ])

val INT_LNEG_UNIQ =
    store_thm
    ("INT_LNEG_UNIQ",
     Term `!x y. (x + y = 0) = (x = ~y)`,
     REPEAT GEN_TAC
     THEN SUBST1_TAC (SYM(SPEC (Term `y:int`) INT_ADD_LINV))
     THEN SIMP_TAC int_ss [INT_EQ_RADD]);

val INT_RNEG_UNIQ =
    store_thm("INT_RNEG_UNIQ",
	      Term `!x y. (x + y = 0) = (y = ~x)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_LNEG_UNIQ])

val INT_NEG_ADD =
    store_thm("INT_NEG_ADD",
	      Term `!x y. ~(x + y) = ~x + ~y`,
	      REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
	      REWRITE_TAC[GSYM INT_LNEG_UNIQ] THEN
	      ONCE_REWRITE_TAC
	      [jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
	       (Term `(a + b) + (c + d) = (a + c) + (b + d:int)`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_RID,INT_0]);

val INT_MUL_LZERO =
    store_thm("INT_MUL_LZERO",
	      Term `!x:int. 0 * x = 0`,
	      GEN_TAC THEN SUBST1_TAC
	      (SYM(Q.SPECL [`0 * x`, `0 * x`] INT_ADD_LID_UNIQ))
	      THEN REWRITE_TAC[GSYM INT_RDISTRIB, INT_ADD_RID]);
val _ = export_rewrites ["INT_MUL_LZERO"]

val INT_MUL_RZERO
    = store_thm("INT_MUL_RZERO",
		Term `!x. x * 0i = 0`,
		GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
		SIMP_TAC int_ss [INT_MUL_LZERO]);
val _ = export_rewrites ["INT_MUL_RZERO"]

val INT_NEG_LMUL =
    store_thm("INT_NEG_LMUL",
	      Term `!x y. ~(x * y) = ~x * y`,
	      REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
	      REWRITE_TAC[GSYM INT_LNEG_UNIQ, GSYM INT_RDISTRIB,
              INT_ADD_LINV, INT_MUL_LZERO,INT_0]);

val INT_NEG_RMUL =
    store_thm("INT_NEG_RMUL",
	      Term `!x y. ~(x * y) = x * ~y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
	      SIMP_TAC int_ss [INT_NEG_LMUL]);

val INT_NEGNEG =
    store_thm("INT_NEGNEG",
	      Term `!x:int. ~~x = x`,
	      GEN_TAC THEN CONV_TAC SYM_CONV THEN
	      REWRITE_TAC[GSYM INT_LNEG_UNIQ, INT_ADD_RINV]);

val INT_NEG_MUL2 =
    store_thm("INT_NEG_MUL2",
	      Term `!x y. ~x * ~y = x * y`,
	      REWRITE_TAC[GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG]);

val INT_LT_LADD =
    store_thm("INT_LT_LADD",
	      Term `!x:int y z. x + y < x + z = y < z`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o (SPEC (Term `~x:int`)) o
			  MATCH_MP INT_LT_LADD_IMP)
	       THEN
	       REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID],
	       SIMP_TAC int_ss [INT_LT_LADD_IMP]]);

val INT_LT_RADD =
    store_thm("INT_LT_RADD",
	      Term `!x:int y z. (x + z) < (y + z) = x < y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_LT_LADD]);

val INT_NOT_LT =
    store_thm("INT_NOT_LT",
	      Term `!x:int y. ~(x < y) = y <= x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le]);

val INT_LT_ANTISYM =
    store_thm("INT_LT_ANTISYM",
	      Term `!x:int y. ~(x < y /\ y < x)`,
	      REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_TRANS)
	      THEN REWRITE_TAC[INT_LT_REFL]);

val INT_LT_GT =
    store_thm("INT_LT_GT",
	      Term `!x:int y. x < y ==> ~(y < x)`,
	      REPEAT GEN_TAC THEN
	      DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
	      REWRITE_TAC[INT_LT_ANTISYM]);

val INT_NOT_LE =
    store_thm("INT_NOT_LE",
	      Term `!x y:int. ~(x <= y) = y < x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le]);

val INT_LE_TOTAL =
    store_thm("INT_LE_TOTAL",
	      Term `!x y:int. x <= y \/ y <= x`,
	      REPEAT GEN_TAC THEN
	      REWRITE_TAC[int_le, GSYM DE_MORGAN_THM, INT_LT_ANTISYM]);

val INT_LET_TOTAL =
    store_thm("INT_LET_TOTAL",
	      Term `!x y:int. x <= y \/ y < x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      SIMP_TAC int_ss []);

val INT_LTE_TOTAL =
    store_thm("INT_LTE_TOTAL",
	      Term `!x y:int. x < y \/ y <= x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      SIMP_TAC int_ss [])


val INT_LE_REFL =
    store_thm("INT_LE_REFL",
	      Term `!x:int. x <= x`,
	      GEN_TAC THEN REWRITE_TAC[int_le, INT_LT_REFL]);

val INT_LE_LT =
    store_thm("INT_LE_LT",
	      Term `!x y:int. x <= y = x < y \/ (x = y)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [Term `x:int`, Term `y:int`] INT_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry(op THEN) (MATCH_MP_TAC INT_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC INT_LT_REFL]);

val INT_LT_LE =
    store_thm
    ("INT_LT_LE",
     Term `!x y:int. x < y = x <= y /\ ~(x = y)`,
     let val lemma = TAUT_CONV (Term `~(a /\ ~a)`)
     in
	 REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, RIGHT_AND_OVER_OR, lemma]
	 THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
	 POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
	 DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LT_REFL]
     end);

val INT_LT_IMP_LE =
    store_thm("INT_LT_IMP_LE",
	      Term `!x y:int. x < y ==> x <= y`,
		  REPEAT GEN_TAC THEN DISCH_TAC THEN
		  ASM_REWRITE_TAC[INT_LE_LT]);

val INT_LTE_TRANS =
    store_thm("INT_LTE_TRANS",
	      Term `!x y z:int. x < y /\ y <= z ==> x < z`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, LEFT_AND_OVER_OR] THEN
	      DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
			 (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC))
	                 THEN REWRITE_TAC[]);

val INT_LET_TRANS =
    store_thm("INT_LET_TRANS",
	      Term `!x y z:int. x <= y /\ y < z ==> x < z`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, RIGHT_AND_OVER_OR]
	      THEN
	      DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
			 (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)));

val INT_LE_TRANS =
    store_thm("INT_LE_TRANS",
	      Term `!x y z:int. x <= y /\ y <= z ==> x <= z`,
	      REPEAT GEN_TAC THEN
	      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites
                [INT_LE_LT] THEN
	      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
			 (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
	      THEN REWRITE_TAC[]
	      THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME (Term `y < z:int`))) THEN
	      DISCH_THEN(ACCEPT_TAC o MATCH_MP
			 INT_LT_IMP_LE o MATCH_MP INT_LET_TRANS));

val INT_LE_ANTISYM =
    store_thm("INT_LE_ANTISYM",
	      Term `!x y:int. x <= y /\ y <= x = (x = y)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [REWRITE_TAC[int_le] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
	       (SPECL [Term `x:int`, Term `y:int`] INT_LT_TOTAL) THEN
	       ASM_REWRITE_TAC[],
	       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LE_REFL]]);

val INT_LET_ANTISYM =
    store_thm("INT_LET_ANTISYM",
	      Term `!x y:int. ~(x < y /\ y <= x)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      BOOL_CASES_TAC (Term `x < y:int`) THEN REWRITE_TAC[]);

val INT_LTE_ANTSYM =
    store_thm("INT_LTE_ANTSYM",
	      Term `!x y:int. ~(x <= y /\ y < x)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
	      MATCH_ACCEPT_TAC INT_LET_ANTISYM);

val INT_NEG_LT0 =
    store_thm("INT_NEG_LT0",
	      Term `!x. ~x < 0 = 0 < x`,
	      GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`~x`, `0`,`x`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID]);

val INT_NEG_GT0 =
    store_thm("INT_NEG_GT0",
	      Term `!x. 0 < ~x = x < 0`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LT0, INT_NEGNEG]);

val INT_NEG_LE0 =
    store_thm("INT_NEG_LE0",
	      Term `!x. ~x <= 0 = 0 <= x`,
	      GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      REWRITE_TAC[INT_NEG_GT0]);

val INT_NEG_GE0 =
    store_thm("INT_NEG_GE0",
	      Term `!x. 0 <= ~x = x <= 0`,
	      GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      REWRITE_TAC[INT_NEG_LT0]);

val INT_LT_NEGTOTAL =
    store_thm("INT_LT_NEGTOTAL",
	      Term `!x. (x = 0) \/ 0<x \/ 0 < ~x`,
	      GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
	      (Q.SPECL [`x`, `0`] INT_LT_TOTAL) THEN
	      ASM_REWRITE_TAC
	      [SYM(REWRITE_RULE[INT_NEGNEG] (Q.SPEC `~x` INT_NEG_LT0))]);

val INT_LE_NEGTOTAL =
    store_thm
    ("INT_LE_NEGTOTAL",
     Term `!x. 0 <= x \/ 0 <= ~x`,
     GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
     REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC (Term `x:int`)
					    INT_LT_NEGTOTAL)
     THEN ASM_REWRITE_TAC[]);

val INT_LE_MUL =
    store_thm
    ("INT_LE_MUL",
     Term `!x y:int. 0 <= x /\ 0 <= y ==> 0 <= x*y`,
	 REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
	 MAP_EVERY ASM_CASES_TAC [Term `0i = x`, Term `0i = y`] THEN
	 ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
	 REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO] THEN
	 DISCH_TAC THEN DISJ1_TAC
	 THEN MATCH_MP_TAC (REWRITE_RULE [INT_0] INT_LT_MUL) THEN
	 ASM_REWRITE_TAC[]);

val INT_LE_SQUARE =
    store_thm("INT_LE_SQUARE",
	      Term `!x:int. 0 <= x * x`,
	      GEN_TAC THEN DISJ_CASES_TAC (SPEC (Term `x:int`) INT_LE_NEGTOTAL)
	      THEN
	      POP_ASSUM(MP_TAC o MATCH_MP INT_LE_MUL o W CONJ) THEN
	      REWRITE_TAC[GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL, INT_NEGNEG]);

val INT_LE_01 =
    store_thm("INT_LE_01",
	      Term `0i <= 1`,
	      SUBST1_TAC(SYM(Q.SPEC `1` INT_MUL_LID)) THEN
	      SIMP_TAC int_ss [INT_LE_SQUARE,INT_1]);

val INT_LT_01 =
    store_thm("INT_LT_01",
	      Term `0i < 1i`,
	      SIMP_TAC int_ss [INT_LT_LE, INT_LE_01,
			       GSYM INT_0,GSYM INT_1,INT_10])

val INT_LE_LADD =
    store_thm("INT_LE_LADD",
	      Term `!x:int y z. x + y <= x + z = y <= z`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_LADD);

val INT_LE_RADD =
    store_thm("INT_LE_RADD",
	      Term `!x y z:int. (x + z) <= (y + z) = x <= y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_RADD);

val INT_LT_ADD2 =
    store_thm("INT_LT_ADD2",
	      Term `!w x y z:int. w < x /\ y < z ==> w + y < x + z`,
	      REPEAT GEN_TAC THEN DISCH_TAC THEN
	      MATCH_MP_TAC INT_LT_TRANS THEN EXISTS_TAC (Term `w + z:int`) THEN
	      ASM_REWRITE_TAC[INT_LT_LADD, INT_LT_RADD]);

val INT_LE_ADD2 =
    store_thm("INT_LE_ADD2",
	      Term `!w x y z:int. w <= x /\ y <= z ==> w + y <= x + z`,
	      REPEAT GEN_TAC THEN DISCH_TAC THEN
	      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (Term `w + z:int`) THEN
	      ASM_REWRITE_TAC[INT_LE_LADD, INT_LE_RADD]);

val INT_LE_ADD =
    store_thm("INT_LE_ADD",
	      Term `!x y:int. 0 <= x /\ 0 <= y ==> 0 <= (x + y)`,
	      REPEAT GEN_TAC
	      THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2) THEN
	      REWRITE_TAC[INT_ADD_LID]);

val INT_LT_ADD =
    store_thm("INT_LT_ADD",
	      Term `!x y:int. 0 < x /\ 0 < y ==> 0 < (x + y)`,
	      REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2)
	      THEN
	      REWRITE_TAC[INT_ADD_LID]);

val INT_LT_ADDNEG =
    store_thm("INT_LT_ADDNEG",
	      Term `!x y z. y < x + ~z = y+z < x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `y:int`,
				    Term `x + ~z`,
				    Term `z:int`] INT_LT_RADD)) THEN
	      REWRITE_TAC[GSYM INT_ADD_ASSOC, INT_ADD_LINV,
			  INT_ADD_RID, INT_0]);
(* REWRITE TO *)
val INT_LT_ADDNEG2 =
    store_thm
    ("INT_LT_ADDNEG2",
     Term `!x y z. x + ~y < z = x < z+y`,
     REPEAT GEN_TAC THEN
     SUBST1_TAC
       (SYM(SPECL [Term `x + ~y`, Term `z:int`,Term `y:int`] INT_LT_RADD)) THEN
     REWRITE_TAC[GSYM INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_RID,INT_0]);

val INT_LT_ADD1 =
    store_thm("INT_LT_ADD1",
	      Term `!x y:int. x <= y ==> x < (y + 1)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
	      DISCH_THEN DISJ_CASES_TAC THENL
	      [POP_ASSUM(MP_TAC o MATCH_MP INT_LT_ADD2 o C CONJ INT_LT_01)
	       THEN
	       REWRITE_TAC[INT_ADD_RID],
	       POP_ASSUM SUBST1_TAC THEN
	       GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM INT_ADD_RID] THEN
	       REWRITE_TAC[INT_LT_LADD, INT_LT_01]]);

val INT_SUB_ADD =
    store_thm("INT_SUB_ADD",
	      Term `!x y:int. (x - y) + y = x`,
	      REPEAT GEN_TAC THEN
              REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
		      INT_ADD_LINV, INT_ADD_RID,INT_0])

val INT_SUB_ADD2 =
    store_thm("INT_SUB_ADD2",
	      Term `!x y:int. y + (x - y) = x`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      MATCH_ACCEPT_TAC INT_SUB_ADD);

val INT_SUB_REFL =
    store_thm("INT_SUB_REFL",
	      Term `!x:int. x - x = 0`,
	      GEN_TAC THEN REWRITE_TAC[int_sub, INT_ADD_RINV]);

val INT_SUB_0 =
    store_thm("INT_SUB_0",
	      Term `!x y:int. (x - y = 0) = (x = y)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o C AP_THM (Term `y:int`) o
			  AP_TERM (Term `$+ :int->int->int`)) THEN
	       REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID],
	       DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC INT_SUB_REFL]);

val INT_LE_DOUBLE =
    store_thm("INT_LE_DOUBLE",
	      Term `!x:int. 0 <= x + x = 0 <= x`,
	      GEN_TAC THEN EQ_TAC THENL
	      [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[INT_NOT_LE] THEN
	       DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2 o W CONJ)
	       THEN REWRITE_TAC [INT_ADD_RID],
	       DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2 o W CONJ)] THEN
	      REWRITE_TAC[INT_ADD_RID]);

val INT_LE_NEGL =
    store_thm("INT_LE_NEGL",
	      Term `!x. ~x <= x = 0 <= x`,
	      GEN_TAC THEN SUBST1_TAC (SYM
                (SPECL [Term `x:int`,Term `~x:int`, Term `x:int`]INT_LE_LADD))
	      THEN REWRITE_TAC[INT_ADD_RINV, INT_LE_DOUBLE]);

val INT_LE_NEGR =
    store_thm("INT_LE_NEGR",
	      Term `!x. x <= ~x = x <= 0`,
	      GEN_TAC THEN SUBST1_TAC(SYM(SPEC (Term `x:int`) INT_NEGNEG)) THEN
	      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                empty_rewrites [INT_NEGNEG] THEN
	      REWRITE_TAC[INT_LE_NEGL] THEN REWRITE_TAC[INT_NEG_GE0] THEN
	      REWRITE_TAC[INT_NEGNEG]);

val INT_NEG_EQ0 =
    store_thm("INT_NEG_EQ0",
	      Term `!x. (~x = 0) = (x = 0)`,
GEN_TAC THEN EQ_TAC THENL
[DISCH_THEN(MP_TAC o AP_TERM (Term `$+ x:int->int`))
   THEN REWRITE_TAC[INT_ADD_RINV, INT_ADD_LINV, INT_ADD_RID, INT_0]
   THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC,
 DISCH_THEN(MP_TAC o AP_TERM (Term `$+ (~x)`))
   THEN REWRITE_TAC[INT_ADD_RINV, INT_ADD_LINV, INT_ADD_RID, INT_0]
   THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC])

val INT_NEG_0 =
    store_thm("INT_NEG_0",
	      Term `~0 = 0`,
	      REWRITE_TAC[INT_NEG_EQ0]);

val INT_NEG_SUB =
    store_thm("INT_NEG_SUB",
	      Term `!x y. ~(x - y) = y - x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub,
					      INT_NEG_ADD, INT_NEGNEG] THEN
	      MATCH_ACCEPT_TAC INT_ADD_SYM);

val INT_SUB_LT =
    store_thm("INT_SUB_LT",
	      Term `!x:int y. 0 < x - y = y < x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL [`0`, `x - y`, `y`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID]);

val INT_SUB_LE =
    store_thm("INT_SUB_LE",
	      Term `!x:int y. 0 <= (x - y) = y <= x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL [`0`, `x - y`, `y`] INT_LE_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID]);

val INT_ADD_SUB =
    store_thm("INT_ADD_SUB",
	      Term `!x y:int. (x + y) - x = y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
			  INT_ADD_RINV, INT_ADD_RID, INT_0]);

val INT_SUB_LDISTRIB =
    store_thm("INT_SUB_LDISTRIB",
	      Term `!x y z:int. x * (y - z) = (x * y) - (x * z)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub,
					      INT_LDISTRIB, INT_NEG_RMUL]);

val INT_SUB_RDISTRIB =
    store_thm("INT_SUB_RDISTRIB",
	      Term `!x y z:int. (x - y) * z = (x * z) - (y * z)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
	      MATCH_ACCEPT_TAC INT_SUB_LDISTRIB);

val INT_NEG_EQ =
    store_thm("INT_NEG_EQ",
	      Term `!x y:int. (~x = y) = (x = ~y)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN
	      REWRITE_TAC[INT_NEGNEG]);

val INT_NEG_MINUS1 =
    store_thm("INT_NEG_MINUS1",
	      Term `!x. ~x = ~1 * x`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LMUL] THEN
	      REWRITE_TAC[INT_MUL_LID,GSYM INT_1]);


val INT_LT_IMP_NE =
    store_thm("INT_LT_IMP_NE",
	      Term `!x y:int. x < y ==> ~(x = y)`,
		  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
		  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
		  REWRITE_TAC[INT_LT_REFL]);

val INT_LE_ADDR =
    store_thm("INT_LE_ADDR",
	      Term `!x y:int. x <= x + y = 0 <= y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL [`x`, `0`, `y`] INT_LE_LADD)) THEN
	      REWRITE_TAC[INT_ADD_RID,INT_0]);

val INT_LE_ADDL =
    store_thm("INT_LE_ADDL",
	      Term `!x y:int. y <= x + y = 0 <= x`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      MATCH_ACCEPT_TAC INT_LE_ADDR);

val INT_LT_ADDR =
    store_thm("INT_LT_ADDR",
	      Term `!x y:int. x < x + y = 0 < y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL [`x`, `0`,`y`] INT_LT_LADD)) THEN
	      REWRITE_TAC[INT_ADD_RID,INT_0]);

val INT_LT_ADDL =
    store_thm("INT_LT_ADDL",
	      Term `!x y:int. y < x + y = 0 < x`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      MATCH_ACCEPT_TAC INT_LT_ADDR);

val INT_ENTIRE =
    store_thm("INT_ENTIRE",
	      Term `!x y:int. (x * y = 0) = (x = 0) \/ (y = 0)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
	       STRIP_TAC THEN
	       REPEAT_TCL DISJ_CASES_THEN MP_TAC
	                     (SPEC (Term `x:int`) INT_LT_NEGTOTAL) THEN
	       ASM_REWRITE_TAC[] THEN
	       REPEAT_TCL DISJ_CASES_THEN MP_TAC
			     (SPEC (Term `y:int`) INT_LT_NEGTOTAL) THEN
               ASM_REWRITE_TAC[] THEN
	       REWRITE_TAC[TAUT_CONV (Term `a ==> b ==> c = b /\ a ==> c`)]
	       THEN
	       DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE [INT_0] INT_LT_MUL))
	       THEN
	       REWRITE_TAC[GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL] THEN
	       CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[INT_NEGNEG] THEN
               DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LT_REFL,INT_NEG_GT0],
	       DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
	       REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO]]);

val INT_EQ_LMUL =
    store_thm("INT_EQ_LMUL",
	      Term `!x y z:int. (x * y = x * z) = (x = 0) \/ (y = z)`,
	      REPEAT GEN_TAC THEN
	      GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM INT_SUB_0] THEN
	      REWRITE_TAC[GSYM INT_SUB_LDISTRIB] THEN
	      REWRITE_TAC[INT_ENTIRE, INT_SUB_0]);

val INT_EQ_RMUL =
    store_thm("INT_EQ_RMUL",
	      Term `!x y z:int. (x * z = y * z) = (z = 0) \/ (x = y)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
	      MATCH_ACCEPT_TAC INT_EQ_LMUL);


(*--------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                *)
(*--------------------------------------------------------------------------*)

val _ = print "Prove homomorphisms for the inclusion map\n"

val INT =
    store_thm("INT",
	      Term `!n. &(SUC n) = &n + 1i`,
	      GEN_TAC THEN REWRITE_TAC[int_of_num] THEN
	      REWRITE_TAC[INT_1]);

val INT_POS =
    store_thm("INT_POS",
	      Term `!n. 0i <= &n`,
	      INDUCT_TAC THEN REWRITE_TAC[INT_LE_REFL] THEN
	      MATCH_MP_TAC INT_LE_TRANS THEN
	      EXISTS_TAC (Term `&n:int`) THEN ASM_REWRITE_TAC[INT] THEN
	      REWRITE_TAC[INT_LE_ADDR, INT_LE_01]);

val INT_LE =
    store_thm("INT_LE",
	      Term `!m n. &m:int <= &n = m <= n`,
	      REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
	      [INT, INT_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, INT_LE_REFL] THEN
	      REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
	      [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (Term `&n:int`) THEN
	       ASM_REWRITE_TAC[ZERO_LESS_EQ, INT_LE_ADDR, INT_LE_01],
	       DISCH_THEN(MP_TAC o C CONJ (SPEC (Term `m:num`) INT_POS)) THEN
	       DISCH_THEN(MP_TAC o MATCH_MP INT_LE_TRANS) THEN
	       REWRITE_TAC[INT_NOT_LE, INT_LT_ADDR, INT_LT_01]]);

val INT_LT =
    store_thm("INT_LT",
	      Term `!m n. &m:int < &n = m < n`,
	      REPEAT GEN_TAC
	      THEN MATCH_ACCEPT_TAC ((REWRITE_RULE[] o
                                      AP_TERM (Term `$~:bool->bool`) o
				      REWRITE_RULE[GSYM NOT_LESS,
						   GSYM INT_NOT_LT])
				     (SPEC_ALL INT_LE)));

val INT_INJ =
    store_thm("INT_INJ",
	      Term `!m n. (&m:int = &n) = (m = n)`,
	      let val th = prove(Term `(m:num = n) = m <= n /\ n <= m`,
				 EQ_TAC
				 THENL [DISCH_THEN SUBST1_TAC
					THEN REWRITE_TAC[LESS_EQ_REFL],
					MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM])
	      in
		  REPEAT GEN_TAC
		  THEN REWRITE_TAC[th, GSYM INT_LE_ANTISYM, INT_LE]
	      end)

val INT_ADD =
    store_thm("INT_ADD",
	      Term `!m n. &m + &n = &(m + n)`,
	      INDUCT_TAC THEN REWRITE_TAC[INT, ADD, INT_ADD_LID]
	      THEN
	      RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
	      CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));

val INT_MUL =
    store_thm("INT_MUL",
	      Term `!m n. &m * &n = &(m * n)`,
	      INDUCT_TAC THEN REWRITE_TAC[INT_MUL_LZERO, MULT_CLAUSES, INT,
					  GSYM INT_ADD, INT_RDISTRIB] THEN
	      FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
	      REWRITE_TAC[INT_MUL_LID,GSYM INT_1]);

(*--------------------------------------------------------------------------*)
(* Now more theorems                                                        *)
(*--------------------------------------------------------------------------*)


val INT_LT_NZ =
    store_thm("INT_LT_NZ",
	      Term `!n. ~(&n = 0) = (0 < &n)`,
	      GEN_TAC THEN REWRITE_TAC[INT_LT_LE] THEN
	      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
	      ASM_CASES_TAC (Term `&n = 0`)
	      THEN ASM_REWRITE_TAC[INT_LE_REFL, INT_POS]);

val INT_NZ_IMP_LT =
    store_thm("INT_NZ_IMP_LT",
	      Term `!n. ~(n = 0) ==> 0 < &n`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_INJ, INT_LT_NZ]);

val INT_DOUBLE =
    store_thm("INT_DOUBLE",
	      Term `!x:int. x + x = 2 * x`,
	      GEN_TAC THEN REWRITE_TAC[num_CONV (Term `2n`), INT] THEN
	      REWRITE_TAC[INT_RDISTRIB, INT_MUL_LID,GSYM INT_1]);

val INT_SUB_SUB =
    store_thm("INT_SUB_SUB",
	      Term `!x y. (x - y) - x = ~y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
	      ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
			       (Term `(a + b) + c = (c + a) + b:int`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID]);

val INT_LT_ADD_SUB =
    store_thm("INT_LT_ADD_SUB",
	      Term `!x y z:int. x + y < z = x < z - y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `x:int`, Term `z - y:int`,
				    Term `y:int`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD]);

val INT_LT_SUB_RADD =
    store_thm("INT_LT_SUB_RADD",
	      Term `!x y z:int. x - y < z = x < z + y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL [`x - y`, `z`, `y`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD]);

val INT_LT_SUB_LADD =
    store_thm("INT_LT_SUB_LADD",
	      Term `!x y z:int. x < y - z = x + z < y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL [`x + z`, `y`, `~z`] INT_LT_RADD)) THEN
	      REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
			  INT_ADD_RINV, INT_ADD_RID, INT_0]);

val INT_LE_SUB_LADD =
    store_thm("INT_LE_SUB_LADD",
	      Term `!x y z:int. x <= y - z = x + z <= y`,
      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT, INT_LT_SUB_RADD]);

val INT_LE_SUB_RADD =
    store_thm("INT_LE_SUB_RADD",
	      Term `!x y z:int. x - y <= z = x <= z + y`,
      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT,INT_LT_SUB_LADD]);

val INT_LT_NEG =
    store_thm("INT_LT_NEG",
	      Term `!x y. ~x < ~y = y < x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(Q.SPECL[`~x`, `~y`, `x + y`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID]
	      THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_LID]);

val INT_LE_NEG =
    store_thm("INT_LE_NEG",
	      Term `!x y. ~x <= ~y = y <= x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN
	      REWRITE_TAC[INT_LT_NEG]);

val INT_ADD2_SUB2 =
    store_thm("INT_ADD2_SUB2",
	      Term `!a b c d:int. (a + b) - (c + d) = (a - c) + (b - d)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_ADD] THEN
	      CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));

val INT_SUB_LZERO =
    store_thm("INT_SUB_LZERO",
	      Term `!x. 0 - x = ~x`,
	      GEN_TAC THEN REWRITE_TAC[int_sub, INT_ADD_LID]);

val INT_SUB_RZERO =
    store_thm("INT_SUB_RZERO",
	      Term `!x:int. x - 0 = x`,
      GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_0,INT_ADD_RID, INT_0]);

val INT_LET_ADD2 =
    store_thm("INT_LET_ADD2",
	      Term `!w x y z:int. w <= x /\ y < z ==> w + y < x + z`,
		  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
		  MATCH_MP_TAC INT_LTE_TRANS THEN
		  Q.EXISTS_TAC `w + z` THEN
		  ASM_REWRITE_TAC[INT_LE_RADD, INT_LT_LADD]);

val INT_LTE_ADD2 =
    store_thm("INT_LTE_ADD2",
	      Term `!w x y z:int. w < x /\ y <= z ==> w + y < x + z`,
		  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
		  ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
		  MATCH_ACCEPT_TAC INT_LET_ADD2);

val INT_LET_ADD =
    store_thm("INT_LET_ADD",
	      Term `!x y:int. 0 <= x /\ 0 < y ==> 0 < x + y`,
	  REPEAT GEN_TAC THEN DISCH_TAC THEN
	  SUBST1_TAC(SYM(Q.SPEC `0` INT_ADD_LID)) THEN
          MATCH_MP_TAC INT_LET_ADD2 THEN ASM_REWRITE_TAC[]);

val INT_LTE_ADD =
    store_thm("INT_LTE_ADD",
	      Term `!x y:int. 0 < x /\ 0 <= y ==> 0 < x + y`,
	  REPEAT GEN_TAC THEN DISCH_TAC THEN
	  SUBST1_TAC(SYM(Q.SPEC `0` INT_ADD_LID)) THEN
	  MATCH_MP_TAC INT_LTE_ADD2 THEN ASM_REWRITE_TAC[]);

val INT_LT_MUL2 =
    store_thm
    ("INT_LT_MUL2",
     Term `!x1 x2 y1 y2:int.
              0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2
                 ==>
              x1 * y1 < x2 * y2`,
     REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_SUB_LT] THEN
     REWRITE_TAC[INT_SUB_RZERO] THEN SUBGOAL_THEN
      (Term `!a b c d:int. (a * b) - (c * d)
		                =
                          ((a * b) - (a * d)) + ((a * d) - (c * d))`) MP_TAC
     THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
      ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
		       (Term `(a + b) + (c + d) = (b + c) + (a + d):int`)]
      THEN
      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID],
      DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM INT_SUB_LDISTRIB, GSYM INT_SUB_RDISTRIB] THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN
      MATCH_MP_TAC INT_LTE_ADD THEN CONJ_TAC THENL
      [MATCH_MP_TAC (REWRITE_RULE [INT_0] INT_LT_MUL)
       THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC (Term `x1:int`) THEN
       ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM INT_SUB_LT] THEN
       ASM_REWRITE_TAC[],
       MATCH_MP_TAC (REWRITE_RULE [INT_0] INT_LE_MUL)
       THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC INT_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);

val INT_SUB_LNEG =
    store_thm("INT_SUB_LNEG",
	      Term `!x y. (~x) - y = ~(x + y)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_ADD]);

val INT_SUB_RNEG =
    store_thm("INT_SUB_RNEG",
	      Term `!x y. x - ~y = x + y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEGNEG]);

val INT_SUB_NEG2 =
    store_thm("INT_SUB_NEG2",
	      Term `!x y. (~x) - (~y) = y - x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_SUB_LNEG] THEN
	      REWRITE_TAC[int_sub, INT_NEG_ADD, INT_NEGNEG] THEN
	      MATCH_ACCEPT_TAC INT_ADD_SYM);

val INT_SUB_TRIANGLE =
    store_thm("INT_SUB_TRIANGLE",
	      Term `!a b c:int. (a - b) + (b - c) = a - c`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
	      ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
			       (Term `(a + b) + (c + d)
				      = (b + c) + (a + d):int`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID]);

val INT_EQ_SUB_LADD =
    store_thm("INT_EQ_SUB_LADD",
	      Term `!x y z:int. (x = y - z) = (x + z = y)`,
	      REPEAT GEN_TAC THEN (SUBST1_TAC o SYM o C SPECL INT_EQ_RADD)
	      [Term `x:int`, Term `y - z:int`, Term `z:int`]
	      THEN REWRITE_TAC[INT_SUB_ADD]);

val INT_EQ_SUB_RADD =
    store_thm("INT_EQ_SUB_RADD",
	      Term `!x y z:int. (x - y = z) = (x = z + y)`,
	      REPEAT GEN_TAC THEN CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV))
	      THEN
	      MATCH_ACCEPT_TAC INT_EQ_SUB_LADD);

val INT_SUB =
    store_thm("INT_SUB",
              Term`!n m. m <= n ==> (&n - &m = &(n - m))`,
              SIMP_TAC int_ss [INT_EQ_SUB_RADD, INT_ADD, INT_INJ]);

val INT_SUB_SUB2 =
    store_thm("INT_SUB_SUB2",
	      Term `!x y:int. x - (x - y) = y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEGNEG] THEN
	      AP_TERM_TAC THEN REWRITE_TAC[INT_NEG_SUB, INT_SUB_SUB]);

val INT_ADD_SUB2 =
    store_thm("INT_ADD_SUB2",
	      Term `!x y:int. x - (x + y) = ~y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEG_SUB] THEN
	      AP_TERM_TAC THEN REWRITE_TAC[INT_ADD_SUB]);

val INT_EQ_LMUL2 =
    store_thm("INT_EQ_LMUL2",
	      Term `!x y z:int. ~(x = 0) ==> ((y = z) = (x * y = x * z))`,
		  REPEAT GEN_TAC THEN DISCH_TAC THEN
		  MP_TAC(SPECL [Term `x:int`, Term `y:int`,
				Term `z:int`] INT_EQ_LMUL) THEN
		  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC
		  THEN REFL_TAC);

val INT_EQ_IMP_LE =
    store_thm("INT_EQ_IMP_LE",
	      Term `!x y:int. (x = y) ==> x <= y`,
		  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
		  MATCH_ACCEPT_TAC INT_LE_REFL);

val INT_POS_NZ =
    store_thm("INT_POS_NZ",
	      Term `!x:int. 0 < x ==> ~(x = 0)`,
		  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP INT_LT_IMP_NE)
		  THEN
		  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC);

val INT_EQ_RMUL_IMP =
    store_thm("INT_EQ_RMUL_IMP",
	      Term `!x y z:int. ~(z = 0) /\ (x * z = y * z) ==> (x = y)`,
		  REPEAT GEN_TAC
		  THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
		  ASM_REWRITE_TAC[INT_EQ_RMUL]);

val INT_EQ_LMUL_IMP =
    store_thm("INT_EQ_LMUL_IMP",
	      Term `!x y z:int. ~(x = 0) /\ (x * y = x * z) ==> (y = z)`,
		  ONCE_REWRITE_TAC[INT_MUL_SYM]
		  THEN MATCH_ACCEPT_TAC INT_EQ_RMUL_IMP);

val INT_DIFFSQ =
    store_thm("INT_DIFFSQ",
	      Term `!x y:int. (x + y) * (x - y) = (x * x) - (y * y)`,
	      REPEAT GEN_TAC THEN
	      REWRITE_TAC[INT_LDISTRIB, INT_RDISTRIB, int_sub,
			  GSYM INT_ADD_ASSOC] THEN
	      ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
                     (Term`a + (b + (c + d)) = (b + c) + (a + d):int`)] THEN
	      REWRITE_TAC[INT_ADD_LID_UNIQ, GSYM INT_NEG_RMUL] THEN
	      REWRITE_TAC[INT_LNEG_UNIQ] THEN AP_TERM_TAC THEN
	      MATCH_ACCEPT_TAC INT_MUL_SYM);

val INT_POSSQ =
    store_thm("INT_POASQ",
	      Term `!x:int. 0 < x*x = ~(x = 0)`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LE]
	      THEN AP_TERM_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o C CONJ (SPEC (Term `x:int`) INT_LE_SQUARE))
	       THEN
	       REWRITE_TAC[INT_LE_ANTISYM, INT_ENTIRE],
	       DISCH_THEN SUBST1_TAC
	       THEN REWRITE_TAC[INT_MUL_LZERO, INT_LE_REFL]]);

val INT_SUMSQ =
    store_thm("INT_SUMSQ",
	      Term `!x y:int. ((x * x) + (y * y) = 0) = (x = 0) /\ (y = 0)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
	       DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC INT_POS_NZ THENL
	       [MATCH_MP_TAC INT_LTE_ADD, MATCH_MP_TAC INT_LET_ADD] THEN
	       ASM_REWRITE_TAC[INT_POSSQ, INT_LE_SQUARE],
	       DISCH_TAC THEN ASM_REWRITE_TAC[INT_MUL_LZERO, INT_ADD_RID]]);

val INT_EQ_NEG =
    store_thm("INT_EQ_NEG",
              Term `!x y:int. (~x = ~y) = (x = y)`,
	      REPEAT GEN_TAC THEN
	      REWRITE_TAC[GSYM INT_LE_ANTISYM, INT_LE_NEG] THEN
	      MATCH_ACCEPT_TAC CONJ_SYM);

val int_eq_calculate = prove(
  Term`!n m. ((&n = ~&m) = (n = 0) /\ (m = 0)) /\
             ((~&n = &m) = (n = 0) /\ (m = 0))`,
  Induct THENL [
    SIMP_TAC int_ss [INT_NEG_0, INT_INJ, GSYM INT_NEG_EQ],
    SIMP_TAC int_ss [INT] THEN GEN_TAC THEN CONJ_TAC THENL [
      SIMP_TAC int_ss [GSYM INT_EQ_SUB_LADD, int_sub, GSYM INT_NEG_ADD] THEN
      ASM_SIMP_TAC int_ss [INT_ADD],
      SIMP_TAC int_ss [INT_NEG_ADD, GSYM INT_EQ_SUB_LADD] THEN
      SIMP_TAC int_ss [int_sub] THEN
      ASM_SIMP_TAC int_ss [INT_NEGNEG, INT_ADD]
    ]
  ]);

val INT_LT_CALCULATE = store_thm(
  "INT_LT_CALCULATE",
  Term`!n m.  (&n:int < &m = n < m) /\ (~&n < ~&m = m < n) /\
              (~&n < &m = ~(n = 0) \/ ~(m = 0)) /\ (&n < ~&m = F)`,
  SIMP_TAC int_ss [INT_LT, INT_LT_NEG] THEN
  Induct THENL [
    SIMP_TAC int_ss [INT_NEG_0, INT_LT, INT_NEG_GT0],
    GEN_TAC THEN CONJ_TAC THENL [
      SIMP_TAC int_ss [INT, INT_NEG_ADD, INT_LT_ADDNEG2] THEN
      ASM_SIMP_TAC int_ss [INT_ADD],
      SIMP_TAC int_ss [INT, INT_LT_ADD_SUB, int_sub, GSYM INT_NEG_ADD] THEN
      ASM_SIMP_TAC int_ss [INT_ADD]
    ]
  ]);



(*--------------------------------------------------------------------------*)
(* A nice proof that the positive integers are a copy of the natural        *)
(* numbers (replacing a nasty hack which poked under the quotient).         *)
(*--------------------------------------------------------------------------*)

val _ = print "Proving +ve integers are a copy of natural numbers\n"

val NUM_POSINT =
    store_thm("NUM_POSINT",
	      Term `!i. 0 <= i ==> ?!n. i = &n`,
		  GEN_TAC THEN DISCH_TAC THEN
		  CONV_TAC EXISTS_UNIQUE_CONV THEN
		  CONJ_TAC THEN POP_ASSUM MP_TAC THENL
		   [ REWRITE_TAC[int_le, GSYM INT_0, NUM_POSINT_EX],
                     REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
                     ASM_REWRITE_TAC[INT_INJ]
                   ]);

val NUM_POSINT_EXISTS = store_thm(
  "NUM_POSINT_EXISTS",
  Term`!i. 0 <= i ==> ?n. i = &n`,
  PROVE_TAC [SIMP_RULE bool_ss [EXISTS_UNIQUE_DEF] NUM_POSINT]);

val NUM_NEGINT_EXISTS = store_thm(
  "NUM_NEGINT_EXISTS",
  Term`!i. i <= 0 ==> ?n. i = ~&n`,
  PROVE_TAC [NUM_POSINT_EXISTS, INT_NEG_LE0, INT_NEG_EQ]);

open boolSimps

val INT_NUM_CASES = store_thm(
  "INT_NUM_CASES",
  Term`!p. (?n. (p = &n) /\ ~(n = 0)) \/ (?n. (p = ~&n) /\ ~(n = 0)) \/
           (p = 0)`,
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    Cases_on `p = 0` THENL [
      ASM_SIMP_TAC int_ss [],
      PROVE_TAC [NUM_POSINT_EXISTS]
    ],
    `?n. p = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [INT_EQ_NEG, INT_INJ, INT_NEG_GE0, NOT_LESS_EQUAL,
                          INT_LE]
  ]);

(* ----------------------------------------------------------------------
    Discreteness of <
   ---------------------------------------------------------------------- *)

val int_cases = prove(
  Term`!x:int. (?n. x = &n) \/ (?n. ~(n = 0) /\ (x = ~&n))`,
  PROVE_TAC [INT_NUM_CASES]);

val INT_DISCRETE = store_thm(
  "INT_DISCRETE",
  Term`!x:int y. ~(x < y /\ y < x + 1)`,
  REPEAT GEN_TAC THEN
  `((?n. x = &n) \/ (?n. n <> 0 /\ (x = ~&n))) /\
   ((?m. y = &m) \/ (?m. m <> 0 /\ (y = ~&m)))`
      by PROVE_TAC [int_cases] THEN
  REPEAT VAR_EQ_TAC THENL [
    REWRITE_TAC [INT_ADD, INT_LT, LESS_LESS_SUC, GSYM ADD1],

    REWRITE_TAC [INT_LT_CALCULATE],

    ASM_REWRITE_TAC [INT_LT_CALCULATE] THEN
    `&m < ~&n + 1 <=> ~(~&n + 1) < ~&m` by REWRITE_TAC [INT_LT_NEG] THEN
    POP_ASSUM SUBST1_TAC THEN
    REWRITE_TAC [INT_NEG_ADD, INT_NEGNEG, GSYM int_sub] THEN
    SRW_TAC [numSimps.ARITH_ss][INT_SUB, INT_LT_CALCULATE],

    REWRITE_TAC [INT_LT_CALCULATE] THEN
    `~&m < ~&n + 1 <=> ~(~&n + 1) < &m`
       by PROVE_TAC [INT_LT_NEG, INT_NEGNEG] THEN
    POP_ASSUM SUBST1_TAC THEN
    REWRITE_TAC [INT_NEG_ADD, INT_NEGNEG, GSYM int_sub] THEN
    SRW_TAC [numSimps.ARITH_ss][INT_SUB, INT_LT_CALCULATE]
  ]);

val INT_LE_LT1 = store_thm(
  "INT_LE_LT1",
  ``x <= y  <=>  x < y + 1``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    FULL_SIMP_TAC (srw_ss()) [INT_LE_LT, INT_LT_ADDR, INT_LT] THEN
    MATCH_MP_TAC INT_LT_TRANS THEN Q.EXISTS_TAC `y` THEN
    SRW_TAC [][INT_LT_ADDR, INT_LT],

    SRW_TAC [][int_le] THEN PROVE_TAC [INT_DISCRETE]
  ]);

val INT_LT_LE1 = store_thm(
  "INT_LT_LE1",
  ``x < y  <=>  x + 1 <= y``,
  SRW_TAC [][INT_LE_LT1, INT_LT_RADD]);


(* ------------------------------------------------------------------------ *)
(* More random theorems about "stuff"                                       *)
(* ------------------------------------------------------------------------ *)

val INT_MUL_EQ_1 = store_thm(
  "INT_MUL_EQ_1",
  ``!x y. (x * y = 1) = (x = 1) /\ (y = 1) \/ (x = ~1) /\ (y = ~1)``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `x` STRIP_ASSUME_TAC INT_NUM_CASES THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC (bool_ss ++ numSimps.ARITH_ss) [INT_MUL_LZERO, INT_INJ,
                                             int_eq_calculate] THEN
  Q.SPEC_THEN `y` STRIP_ASSUME_TAC INT_NUM_CASES THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC (bool_ss ++ numSimps.ARITH_ss) [
    INT_MUL_LZERO, INT_INJ, INT_MUL_RZERO, int_eq_calculate,
    GSYM INT_NEG_RMUL, INT_MUL, GSYM INT_NEG_LMUL,
    INT_NEGNEG, INT_EQ_NEG]);

(*--------------------------------------------------------------------------*)
(* Theorems about mapping both ways between :num and :int                   *)
(*--------------------------------------------------------------------------*)

val Num = new_definition("Num", Term `Num (i:int) = @n. i = &n`);

val NUM_OF_INT =
    store_thm("NUM_OF_INT",
	      Term `!n. Num(&n) = n`,
	      GEN_TAC THEN REWRITE_TAC[Num, INT_INJ] THEN
	      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
	      REWRITE_TAC[SELECT_REFL]);
val _ = computeLib.add_persistent_funs [("NUM_OF_INT", NUM_OF_INT)]

val INT_OF_NUM =
    store_thm("INT_OF_NUM",
	      Term `!i. (&(Num i) = i) = 0 <= i`,
	      GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC INT_POS,
	       DISCH_THEN(ASSUME_TAC o EXISTENCE o MATCH_MP NUM_POSINT) THEN
	       REWRITE_TAC[Num] THEN CONV_TAC SYM_CONV THEN
	       MP_TAC(ISPEC (Term `\n. i = &n`) SELECT_AX) THEN
	       BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
	       POP_ASSUM ACCEPT_TAC]);

val LE_NUM_OF_INT = store_thm
  ("LE_NUM_OF_INT",
   ``!n i. & n <= i ==> n <= Num i``,
   METIS_TAC [NUM_OF_INT, INT_OF_NUM, INT_LE_TRANS, INT_POS, INT_LE]);

(*----------------------------------------------------------------------*)
(* Define division                                                      *)
(*----------------------------------------------------------------------*)

val _ = print "Integer division\n"

val int_div_exists0 = prove(
  ``!i j. ?q. ~(j = 0) ==>
               (q = if 0 < j then
                      if 0 <= i then &(Num i DIV Num j)
                      else ~&(Num ~i DIV Num j) +
                           (if Num ~i MOD Num j = 0 then 0 else ~1)
                    else
                      if 0 <= i then ~&(Num i DIV Num ~j) +
                                     (if Num i MOD Num ~j = 0 then 0 else ~1)
                      else &(Num ~i DIV Num ~j))``,
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN DISJ2_TAC THEN
  REWRITE_TAC [EXISTS_REFL]);

val int_div_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_div_exists0

val int_div = new_specification ("int_div", ["int_div"], int_div_exists);

val _ = set_fixity "/" (Infixl 600)
val _ = overload_on("/", Term`int_div`)

val INT_DIV = store_thm(
  "INT_DIV",
  Term`!n m. ~(m = 0) ==> (&n / &m = &(n DIV m))`,
  SIMP_TAC int_ss [int_div, INT_LE, INT_LT, NUM_OF_INT, INT_INJ]);

val INT_DIV_NEG = store_thm(
  "INT_DIV_NEG",
  ``!p q. ~(q = 0) ==> (p / ~q = ~p / q)``,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  FULL_SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ, INT_NEG_0, INT_NEGNEG] THEN
  ASM_SIMP_TAC int_ss [int_div, INT_INJ, INT_NEG_EQ, INT_NEG_0,
                       INT_NEG_GT0, INT_LT, INT_NEG_GE0, INT_NEGNEG,
                       NUM_OF_INT] THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  FULL_SIMP_TAC int_ss [int_div, INT_NEG_EQ0, INT_INJ, INT_NEG_EQ, INT_NEG_0,
                        INT_NEG_GT0, INT_LT, INT_NEG_GE0, INT_NEGNEG,
                        NUM_OF_INT, INT_LE, INT_NEG_LE0, ZERO_DIV,
                        ZERO_MOD, INT_ADD_RID]);




val INT_DIV_1 = store_thm(
  "INT_DIV_1",
  Term`!p:int. p / 1 = p`,
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    (* p positive *)
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC int_ss [DIV_ONE, ONE, INT_DIV],
    (* p negative *)
    `?n. p = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC (int_ss ++ COND_elim_ss) [INT_INJ, INT_EQ_NEG, int_div, ONE,
                DIV_ONE, INT_LT, INT_NEG_GE0, INT_LE,
                INT_NEGNEG, NUM_OF_INT, INT_NEG_0, MOD_ONE,
                INT_ADD_RID, GSYM INT_NEG_EQ]
  ]);

val INT_DIV_0 = store_thm(
  "INT_DIV_0",
  ``!q. ~(q = 0) ==> (0 / q = 0)``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_NEG_EQ0, INT_INJ, INT_DIV_NEG, INT_DIV,
                       INT_NEG_0, ZERO_DIV, GSYM NOT_ZERO_LT_ZERO]);

val INT_DIV_ID = store_thm(
  "INT_DIV_ID",
  Term`!p:int. ~(p = 0) ==> (p / p = 1)`,
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    (* p positive *)
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    ASM_SIMP_TAC int_ss [INT_INJ, INT_DIV, DIVMOD_ID, NOT_ZERO_LT_ZERO],
    (* p negative *)
    `?n. p = ~&n` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    ASM_SIMP_TAC int_ss [INT_NEG_EQ0, INT_NEGNEG, int_div,
                         NUM_OF_INT, INT_NEG_GT0, INT_INJ, INT_LT,
                         DIVMOD_ID, NOT_ZERO_LT_ZERO]
  ]);

(*----------------------------------------------------------------------*)
(* Define the appropriate modulus function for int_div                  *)
(*----------------------------------------------------------------------*)

val _ = print "Integer modulus\n"

val int_mod_exists0 = prove(
  ``!i j. ?r. ~(j = 0) ==> (r = i - i / j * j)``,
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN DISJ2_TAC THEN
  REWRITE_TAC [EXISTS_REFL]);
val int_mod_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_mod_exists0


val int_mod = new_specification ("int_mod",["int_mod"],int_mod_exists);

val _ = set_fixity "%" (Infixl 650)
val _ = overload_on("%", Term`int_mod`);

val little_lemma = prove(
  ``!x y z. ~x < y + ~z = z < y + x``,
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_LADD] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC (LHS_CONV (LAND_CONV  (REWR_CONV INT_ADD_COMM))) THEN
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_RADD]);

val ll2 = prove(
  ``!x y. (x + ~y <= 0) = (x <= y)``,
  REWRITE_TAC [GSYM int_sub, INT_LE_SUB_RADD, INT_ADD_LID]);


val INT_MOD_BOUNDS = store_thm(
  "INT_MOD_BOUNDS",
  ``!p q. ~(q = 0) ==> if q < 0 then q < p % q /\ p % q <= 0
                       else          0 <= p % q /\ p % q < q``,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC int_ss [int_mod] THEN
  REPEAT_TCL STRIP_THM_THEN ASSUME_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THENL [
    ASM_SIMP_TAC int_ss [INT_LT, INT_SUB_LE, INT_LT_SUB_RADD],
    ASM_SIMP_TAC int_ss [INT_NEG_LT0, INT_LT],
    FULL_SIMP_TAC bool_ss []
  ] THEN FULL_SIMP_TAC bool_ss [INT_INJ, INT_NEG_EQ0] THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ADD, INT_DIV, INT_MUL, INT_LE, INT_LT,
                       INT_DIV_NEG, INT_SUB_LZERO, INT_LT_NEG,
                       INT_DIV_0, INT_INJ, ZERO_DIV, GSYM NOT_ZERO_LT_ZERO,
                       INT_NEG_0, INT_MUL_LZERO, INT_LE, INT_NEG_LT0,
                       INT_NEGNEG] THEN
  Q.ABBREV_TAC `p = n'` THEN POP_ASSUM (K ALL_TAC)
  THENL [
    ALL_TAC,
    ASM_SIMP_TAC int_ss [int_div, INT_INJ, INT_LT, INT_NEG_GE0, INT_LE,
                         NUM_OF_INT, INT_NEGNEG] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC int_ss [INT_RDISTRIB, INT_MUL_LZERO, INT_ADD_RID,
                         GSYM INT_NEG_LMUL, INT_LE_NEG, INT_LE, INT_MUL,
                         little_lemma, INT_ADD, INT_LT, GSYM INT_NEG_ADD,
                         GSYM INT_NEG_RMUL, INT_NEGNEG, int_sub],
    ASM_SIMP_TAC int_ss [int_div, INT_INJ, INT_LT, INT_NEG_GE0, INT_LE,
                         NUM_OF_INT, INT_NEGNEG] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC int_ss [INT_RDISTRIB, INT_MUL_LZERO, INT_ADD_RID,
                         GSYM INT_NEG_LMUL, INT_LE_NEG, INT_LE, INT_MUL,
                         little_lemma, INT_ADD, INT_LT, GSYM INT_NEG_ADD,
                         GSYM INT_NEG_RMUL, INT_NEGNEG, int_sub, ll2],
    SIMP_TAC int_ss [GSYM INT_NEG_RMUL, INT_SUB_NEG2, INT_MUL,
                     INT_LE_SUB_RADD, INT_ADD_LID, INT_LE_NEG, INT_LE] THEN
    SIMP_TAC int_ss [int_sub, little_lemma, INT_ADD, INT_LT]
  ] THEN
  `(p = p DIV n * n + p MOD n) /\ p MOD n < n` by
     PROVE_TAC [DIVISION, NOT_ZERO_LT_ZERO] THEN
  Q.ABBREV_TAC `q = p DIV n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = p MOD n` THEN POP_ASSUM (K ALL_TAC) THEN
  ASM_SIMP_TAC int_ss []);

val INT_DIVISION = store_thm(
  "INT_DIVISION",
  Term`!q. ~(q = 0) ==> !p. (p = p / q * q + p % q) /\
                            if q < 0 then q < p % q /\ p % q <= 0
                            else          0 <= p % q /\ p % q < q`,
  REPEAT STRIP_TAC THENL [
    ASM_SIMP_TAC int_ss [int_mod, int_sub] THEN
    PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM, INT_ADD_ASSOC, int_sub],
    PROVE_TAC [INT_MOD_BOUNDS]
  ]);

val INT_MOD = store_thm(
  "INT_MOD",
  Term`!n m. ~(m = 0) ==> (&n % &m = &(n MOD m))`,
  SIMP_TAC int_ss [int_mod, INT_INJ, INT_DIV, INT_MUL, INT_EQ_SUB_RADD,
                   INT_ADD, INT_INJ] THEN
  PROVE_TAC [ADD_COMM, DIVISION, NOT_ZERO_LT_ZERO, MULT_COMM]);

val INT_MOD_NEG = store_thm(
  "INT_MOD_NEG",
  ``!p q. ~(q = 0) ==> (p % ~q = ~(~p % q))``,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  FULL_SIMP_TAC int_ss [INT_INJ, INT_NEGNEG, int_mod, INT_NEG_EQ,
                        INT_NEG_0, INT_DIV_NEG, INT_NEG_ADD,
                        GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, int_sub,
                        INT_NEG_EQ0]);

val INT_MOD0 = store_thm(
  "INT_MOD0",
  Term`!p. ~(p = 0) ==> (0 % p = 0)`,
  GEN_TAC THEN
  Cases_on `0 <= p` THENL [
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC int_ss [INT_MOD, INT_INJ, ZERO_MOD],
    `?n. p = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC int_ss [INT_MOD_NEG, INT_NEG_EQ0, INT_MOD, INT_INJ, ZERO_MOD,
                     INT_NEG_0]
  ]);

val INT_DIV_MUL_ID = store_thm(
  "INT_DIV_MUL_ID",
  Term`!p q. ~(q = 0) /\ (p % q = 0) ==> (p / q * q = p)`,
  REPEAT STRIP_TAC THEN
  `p = p/q * q + p % q` by PROVE_TAC [INT_DIVISION] THEN
  `p = p / q * q` by PROVE_TAC [INT_ADD_RID] THEN
  PROVE_TAC []);

open dividesTheory
val lessmult_lemma = prove(
  ``!x y:num. x * y < y ==> (x = 0)``,
  Induct THEN ASM_SIMP_TAC int_ss [MULT_CLAUSES]);

val negcase = prove(
  ``!q n m.
       m < n /\ ~(q = 0) ==> ((~&q * &n + &m) / &n = ~ &q)``,
  REPEAT STRIP_TAC THEN
  `m < q * n` by
     PROVE_TAC [NOT_LESS_EQUAL, lessmult_lemma, LESS_LESS_EQ_TRANS] THEN
  Q_TAC SUFF_TAC `(&m + ~&q * &n) / &n = ~&q`
        THEN1 SRW_TAC [][INT_ADD_COMM] THEN
  REWRITE_TAC [GSYM int_sub, GSYM INT_NEG_LMUL] THEN
  ONCE_REWRITE_TAC [GSYM INT_NEG_SUB] THEN
  ASM_SIMP_TAC int_ss [INT_SUB, INT_MUL, INT_LE,
                       ARITH_PROVE ``x:num < y ==> x <= y``] THEN
  ASM_SIMP_TAC int_ss [int_div, INT_INJ, INT_LT, INT_NEG_GE0, INT_LE,
                       INT_NEGNEG, NUM_OF_INT, INT_EQ_NEG] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_LT, INT_NEG_GE0, INT_LE,
                       INT_NEGNEG, NUM_OF_INT, INT_EQ_NEG,
                       INT_ADD_RID, GSYM INT_NEG_ADD, INT_ADD]
  THENL [
    Q.MATCH_ABBREV_TAC `tot DIV n = q` THEN
    Q.ABBREV_TAC `q' = tot DIV n` THEN
    Q.ABBREV_TAC `r = tot MOD n` THEN
    `0 < n` by ASM_SIMP_TAC int_ss [] THEN
    `(tot = q' * n + r) /\ r < n` by METIS_TAC [DIVISION] THEN
    `q * n = q' * n + m` by ASM_SIMP_TAC int_ss [Abbr`tot`] THEN
    `(q * n) DIV n = (q' * n + m) DIV n` by SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [ASSUME ``0n < n``, MULT_DIV,
                              ASSUME ``(m:num) < n``, DIV_MULT],
    Q_TAC SUFF_TAC `(q * n - m) DIV n = q - 1` THEN1
       ASM_SIMP_TAC int_ss [] THEN
    MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `n - m` THEN
    `n <= q * n` by PROVE_TAC [lessmult_lemma, NOT_LESS_EQUAL] THEN
    ASM_SIMP_TAC int_ss [RIGHT_SUB_DISTRIB, MULT_CLAUSES,
                         ARITH_PROVE ``x:num < y ==> x <= y``,
                         GSYM LESS_EQ_ADD_SUB, SUB_ADD] THEN
    Q_TAC SUFF_TAC `~(m = 0)` THEN1 ASM_SIMP_TAC int_ss [] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [SUB_0] THEN PROVE_TAC [MOD_EQ_0, MULT_COMM]
  ]);

val INT_DIV_UNIQUE = store_thm(
  "INT_DIV_UNIQUE",
  ``!i j q. (?r. (i = q * j + r) /\
                 if j < 0 then j < r /\ r <= 0 else 0 <= r /\ r < j) ==>
            (i / j = q)``,
  REPEAT GEN_TAC THEN DISCH_THEN (STRIP_THM_THEN  MP_TAC) THEN
  STRUCT_CASES_TAC (Q.SPEC `j` INT_NUM_CASES) THEN
  FULL_SIMP_TAC int_ss [INT_INJ, INT_MUL_RZERO, INT_LT, INT_ADD_LID,
                        INT_NEG_LT0]
  THENL [
    REPEAT STRIP_TAC THEN `?m. r = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC int_ss [INT_LT, INT_LE] THEN
    STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THENL [
      FULL_SIMP_TAC int_ss [INT_MUL, INT_ADD, INT_DIV, INT_INJ] THEN
      PROVE_TAC [ADD_COMM, DIV_UNIQUE, MULT_COMM],
      PROVE_TAC [negcase],
      ASM_SIMP_TAC int_ss [INT_MUL_LZERO, INT_ADD_LID, INT_DIV, INT_INJ,
                           LESS_DIV_EQ_ZERO]
    ],
    REPEAT STRIP_TAC THEN
    `?m. r = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    FULL_SIMP_TAC int_ss [INT_DIV_NEG, INT_INJ, INT_NEG_EQ0,
                          INT_NEG_LE0, INT_LT_NEG, INT_LE, INT_LT] THEN
    STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THENL [
      ASM_SIMP_TAC int_ss [INT_NEG_RMUL, INT_NEGNEG, INT_NEG_ADD, INT_DIV,
                           INT_INJ, INT_ADD, INT_MUL] THEN
      PROVE_TAC [DIV_UNIQUE, ADD_COMM, MULT_COMM],
      ASM_SIMP_TAC bool_ss [INT_NEG_MUL2, negcase, INT_NEG_ADD, INT_NEGNEG,
                            INT_NEG_LMUL],
      ASM_SIMP_TAC int_ss [INT_MUL_LZERO, INT_ADD_LID, INT_DIV, INT_INJ,
                           LESS_DIV_EQ_ZERO, INT_NEGNEG]
    ],
    PROVE_TAC [INT_LET_TRANS, INT_LT_REFL]
  ]);

val INT_MOD_UNIQUE = store_thm(
  "INT_MOD_UNIQUE",
  ``!i j m.
     (?q. (i = q * j + m) /\ if j < 0 then j < m /\ m <= 0
                             else 0 <= m /\ m < j) ==>
     (i % j = m)``,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  `~(j = 0)` by (DISCH_THEN SUBST_ALL_TAC THEN
                 FULL_SIMP_TAC int_ss [INT_LT_REFL] THEN
                 PROVE_TAC [INT_LET_TRANS, INT_LT_REFL]) THEN
  ASM_SIMP_TAC int_ss [int_mod] THEN
  `(q * j + m) / j = q` by PROVE_TAC [INT_DIV_UNIQUE] THEN
  ASM_SIMP_TAC bool_ss [INT_ADD_SUB]);

val INT_MOD_ID = store_thm(
  "INT_MOD_ID",
  ``!i. ~(i = 0) ==> (i % i = 0)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `1` THEN
  SIMP_TAC bool_ss [INT_MUL_LID, INT_ADD_RID, INT_LE_REFL] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]);

val INT_MOD_COMMON_FACTOR = store_thm(
  "INT_MOD_COMMON_FACTOR",
  Term`!p. ~(p = 0) ==> !q. (q * p) % p = 0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  SIMP_TAC int_ss [INT_ADD_RID, INT_LE_REFL] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]);

val INT_DIV_LMUL = store_thm(
  "INT_DIV_LMUL",
  ``!i j. ~(i = 0) ==> ((i * j) / i = j)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN
  ASM_SIMP_TAC int_ss [INT_MUL_COMM, INT_LE_REFL, INT_ADD_RID] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]);

val INT_DIV_RMUL = store_thm(
  "INT_DIV_RMUL",
  ``!i j. ~(i = 0) ==> (j * i / i = j)``,
  PROVE_TAC [INT_DIV_LMUL, INT_MUL_COMM]);

val INT_MOD_EQ0 = store_thm(
  "INT_MOD_EQ0",
  Term`!q. ~(q = 0) ==> !p. (p % q = 0) = (?k. p = k * q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.PAT_ASSUM `~(q = 0)` (ASSUME_TAC o Q.SPEC `p` o
                            MATCH_MP INT_DIVISION) THEN
    PROVE_TAC [INT_ADD_RID],
    MATCH_MP_TAC INT_MOD_UNIQUE THEN
    ASM_SIMP_TAC int_ss [INT_LE_REFL, INT_EQ_RMUL, INT_ADD_RID] THEN
    PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]
  ]);

val INT_MUL_DIV = store_thm(
  "INT_MUL_DIV",
  Term`!p:int q k. ~(q = 0) /\ (p % q = 0) ==>
                   ((k * p) / q = k * (p / q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQUE THEN
  `?m. p = m * q` by PROVE_TAC [INT_MOD_EQ0] THEN
  `p / q = m` by PROVE_TAC [INT_DIV_RMUL] THEN
  POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  Q.EXISTS_TAC `0` THEN
  SIMP_TAC int_ss [INT_MUL_ASSOC, INT_ADD_RID, INT_LE_REFL] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]);

val INT_ADD_DIV = store_thm(
  "INT_ADD_DIV",
  ``!i j k. ~(k = 0) /\ ((i % k = 0) \/ (j % k = 0)) ==>
            ((i + j) / k = i / k + j / k)``,
  REPEAT STRIP_TAC THENL [
    `?m. i = m * k` by PROVE_TAC [INT_MOD_EQ0] THEN
    ASM_SIMP_TAC int_ss [INT_DIV_RMUL] THEN
    MATCH_MP_TAC INT_DIV_UNIQUE THEN
    SIMP_TAC int_ss [INT_RDISTRIB, GSYM INT_ADD_ASSOC, INT_EQ_LADD] THEN
    Q.EXISTS_TAC `j % k` THEN PROVE_TAC [INT_DIVISION],
    `?m. j = m * k` by PROVE_TAC [INT_MOD_EQ0] THEN
    ASM_SIMP_TAC int_ss [INT_DIV_RMUL] THEN
    MATCH_MP_TAC INT_DIV_UNIQUE THEN Q.EXISTS_TAC `i % k` THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_COMM))) THEN
    ASM_SIMP_TAC int_ss [INT_RDISTRIB, INT_ADD_ASSOC, INT_EQ_RADD,
                         INT_DIVISION] THEN
    PROVE_TAC [INT_DIVISION, INT_ADD_COMM]
  ]);

val INT_MOD_ADD0 = prove(
  ``0 <= r /\ r < k ==> ((q * k + r) % k = r)``,
  STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `q` THEN
  METIS_TAC [INT_LET_TRANS, INT_LT_TRANS, INT_LT_REFL])

val INT_MOD_ADD1 = prove(
  ``k < r /\ r <= 0 ==> ((q * k + r) % k = r)``,
  STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `q` THEN
  METIS_TAC [INT_LTE_TRANS])

val INT_MOD_ADD_MULTIPLES = store_thm(
  "INT_MOD_ADD_MULTIPLES",
  ``~(k = 0) ==> ((q * k + r) % k = r % k)``,
  STRIP_TAC THEN
  `0 < k \/ k < 0` by METIS_TAC [INT_LT_TRANS, INT_LT_TOTAL] THENL [
     `(r = r / k * k + r % k) /\ 0 <= r % k /\ r % k < k`
        by METIS_TAC [INT_DIVISION, INT_LT_TRANS, INT_LT_REFL] THEN
     Q.ABBREV_TAC `R = r % k` THEN
     Q.ABBREV_TAC `Q = r / k` THEN
     Q_TAC SUFF_TAC `q * k + r = (q + Q) * k + R` THEN1
       SRW_TAC [][INT_MOD_ADD0] THEN
     SRW_TAC [][INT_RDISTRIB, INT_ADD_ASSOC],

     `(r = r / k * k + r % k) /\ k < r % k /\ r % k <= 0`
        by METIS_TAC [INT_DIVISION] THEN
     Q.ABBREV_TAC `R = r % k` THEN
     Q.ABBREV_TAC `Q = r / k` THEN
     Q_TAC SUFF_TAC `q * k + r = (q + Q) * k + R` THEN1
       SRW_TAC [][INT_MOD_ADD1] THEN
     SRW_TAC [][INT_RDISTRIB, INT_ADD_ASSOC]
  ]);

val INT_MOD_NEG_NUMERATOR = store_thm(
  "INT_MOD_NEG_NUMERATOR",
  ``~(k = 0) ==> (~x % k = (k - x) % k)``,
  METIS_TAC [int_sub, INT_MUL_LID, INT_MOD_ADD_MULTIPLES])

val INT_MOD_PLUS = store_thm(
  "INT_MOD_PLUS",
  ``~(k = 0) ==> ((i % k + j % k) % k = (i + j) % k)``,
  STRIP_TAC THEN
  `(i = i / k * k + i % k) /\ (j = j/k * k + j%k)`
     by METIS_TAC [INT_DIVISION] THEN
  Q.ABBREV_TAC `Qi = i / k` THEN
  Q.ABBREV_TAC `Ri = i % k` THEN
  Q.ABBREV_TAC `Qj = j / k` THEN
  Q.ABBREV_TAC `Rj = j % k` THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN
  SRW_TAC [][] THEN
  `Qi * k + Ri + (Qj * k + Rj) = Qi * k + (Qj * k + (Ri + Rj))`
     by SRW_TAC [][AC INT_ADD_ASSOC INT_ADD_COMM] THEN
  SRW_TAC [][INT_MOD_ADD_MULTIPLES])

(* surprisingly, this is not an easy consequence of INT_MOD_PLUS  and
   INT_MOD_NEG_NUMERATOR
*)
val INT_MOD_SUB = store_thm(
  "INT_MOD_SUB",
  ``~(k = 0) ==> ((i % k - j % k) % k = (i - j) % k)``,
  STRIP_TAC THEN
  `(i = i / k * k + i % k) /\ (j = j / k * k + j % k)`
     by METIS_TAC [INT_DIVISION] THEN
  Q.ABBREV_TAC `Qi = i / k` THEN
  Q.ABBREV_TAC `Ri = i % k` THEN
  Q.ABBREV_TAC `Qj = j / k` THEN
  Q.ABBREV_TAC `Rj = j % k` THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN
  SRW_TAC [][int_sub, INT_NEG_ADD, INT_NEG_LMUL] THEN
  `Qi * k + Ri + (~Qj * k + ~Rj) = Qi * k + (~Qj * k + (Ri + ~Rj))`
     by SRW_TAC [][AC INT_ADD_ASSOC INT_ADD_COMM] THEN
  SRW_TAC [][INT_MOD_ADD_MULTIPLES])

val INT_MOD_MOD = store_thm(
  "INT_MOD_MOD",
  ``~(k = 0) ==> (j % k % k = j % k)``,
  STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN Q.EXISTS_TAC `0` THEN
  SRW_TAC [][] THEN METIS_TAC [INT_DIVISION])
val _ = export_rewrites ["INT_MOD_MOD"]

val INT_DIV_P = store_thm(
  "INT_DIV_P",
  ``!P x c. ~(c = 0) ==>
            (P (x / c) = ?k r. (x = k * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) /\ P k)``,
  METIS_TAC [INT_DIVISION, INT_DIV_UNIQUE]);

val INT_MOD_P = store_thm(
  "INT_MOD_P",
  ``!P x c. ~(c = 0) ==>
            (P (x % c) = ?k r. (x = k * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) /\ P r)``,
  METIS_TAC [INT_DIVISION, INT_MOD_UNIQUE]);

val INT_DIV_FORALL_P = store_thm(
  "INT_DIV_FORALL_P",
  ``!P x c. ~(c = 0) ==>
            (P (x / c) = !k r. (x = k * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) ==>
                               P k)``,
  METIS_TAC [INT_DIV_UNIQUE, INT_DIVISION]);

val INT_MOD_FORALL_P = store_thm(
  "INT_MOD_FORALL_P",
  ``!P x c. ~(c = 0) ==>
            (P (x % c) = !q r. (x = q * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) ==>
                               P r)``,
  METIS_TAC [INT_MOD_UNIQUE, INT_DIVISION]);

val INT_MOD_1 = store_thm(
  "INT_MOD_1",
  ``!i. i % 1 = 0``,
  GEN_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `i` THEN SRW_TAC [][INT_LT, INT_LE]);

val INT_LESS_MOD = store_thm(
  "INT_LESS_MOD",
  ``!i j. 0 <= i /\ i < j ==> (i % j = i)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN SRW_TAC [][] THEN
  PROVE_TAC [INT_LET_TRANS, INT_LT_ANTISYM])

val INT_MOD_MINUS1 = store_thm(
  "INT_MOD_MINUS1",
  ``!n. 0 < n ==> (~1 % n = n - 1)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `~1` THEN SRW_TAC [][] THENL [
    SRW_TAC [][GSYM INT_NEG_MINUS1, INT_NEG_EQ, INT_NEG_ADD, INT_NEGNEG,
               INT_NEG_SUB, INT_SUB_ADD2],
    PROVE_TAC [INT_LT_ANTISYM],
    PROVE_TAC [INT_LT_ANTISYM],
    SRW_TAC [][INT_SUB_LE] THEN
    FULL_SIMP_TAC (srw_ss()) [INT_LT_LE1, INT_ADD],
    SRW_TAC [][INT_LT_SUB_RADD, INT_LT_ADDR, INT_LT]
  ]);


(*----------------------------------------------------------------------*)
(* Define absolute value                                                *)
(*----------------------------------------------------------------------*)

val _ = print "Absolute value\n"

val INT_ABS = new_definition(
  "INT_ABS",
  Term`ABS n = if n < 0 then ~n else n`);

val INT_ABS_POS = store_thm(
  "INT_ABS_POS",
  Term`!p. 0 <= ABS p`,
  GEN_TAC THEN STRIP_ASSUME_TAC (Q.SPEC `p` INT_LT_NEGTOTAL) THEN
  ASM_SIMP_TAC bool_ss [INT_ABS, INT_LE_REFL, INT_LT_REFL, INT_LT_GT,
                        INT_NEG_GT0, INT_NEG_0]
  THENL [
    ASM_SIMP_TAC bool_ss [INT_LE_LT],
    SIMP_TAC bool_ss [GSYM INT_NEG_GT0] THEN
    ASM_SIMP_TAC bool_ss [INT_LE_LT]
  ]);

val INT_ABS_NUM = store_thm(
  "INT_ABS_NUM",
  Term`!n. ABS (&n) = &n`,
  SIMP_TAC bool_ss [INT_ABS, REWRITE_RULE [GSYM INT_NOT_LT] INT_POS]);

val INT_NEG_SAME_EQ = store_thm(
  "INT_NEG_SAME_EQ",
  Term`!p. (p = ~p) = (p = 0)`,
  GEN_TAC THEN EQ_TAC THENL [
    PROVE_TAC [INT_NEG_GT0, INT_LT_TRANS, INT_LT_REFL, INT_LT_NEGTOTAL],
    SIMP_TAC bool_ss [INT_NEG_0]
  ]);

val INT_ABS_NEG = store_thm(
  "INT_ABS_NEG",
  Term`!p. ABS ~p = ABS p`,
  GEN_TAC THEN
  SIMP_TAC (bool_ss ++ boolSimps.COND_elim_ss)
    [INT_ABS, INT_NEG_LT0, INT_NEGNEG, INT_NEG_EQ, INT_NEG_SAME_EQ] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NOT_LT, INT_LE_LT]);

val INT_ABS_ABS = store_thm(
  "INT_ABS_ABS",
  Term`!p. ABS (ABS p) = ABS p`,
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    ASM_SIMP_TAC bool_ss [INT_ABS_NUM],
    FULL_SIMP_TAC bool_ss [INT_NOT_LE, INT_ABS, INT_NEGNEG, INT_NEG_LT0,
                           INT_LT_GT]
  ]);

val INT_ABS_EQ_ID = store_thm(
  "INT_ABS_EQ_ID",
  Term`!p. (ABS p = p) = (0 <= p)`,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_LE, INT_NEG_SAME_EQ,
                   INT_NEG_GE0, INT_INJ]);

val INT_ABS_MUL = store_thm(
  "INT_ABS_MUL",
  Term`!p q. ABS p * ABS q = ABS (p * q)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_MUL,
                   GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEG_MUL2]);

val INT_ABS_EQ0 = store_thm(
  "INT_ABS_EQ0",
  Term`!p. (ABS p = 0) = (p = 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NEG, INT_ABS_NUM, INT_NEG_EQ0]);

val INT_ABS_LT0 = store_thm(
  "INT_ABS_LT0",
  ``!p. ~(ABS p < 0)``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NEG, INT_ABS_NUM, INT_LT, INT_LT_NEG]);

val INT_ABS_LE0 = store_thm(
  "INT_ABS_LE0",
  ``!p. (ABS p <= 0) = (p = 0)``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NEG, INT_ABS_NUM, INT_LE, INT_LE_NEG,
                       INT_INJ, INT_NEG_EQ0]);

val INT_ABS_LT = store_thm(
  "INT_ABS_LT",
  ``!p q. (ABS p < q = p < q /\ ~q < p) /\
          (q < ABS p = q < p \/ p < ~q) /\
          (~ABS p < q = ~q < p \/ p < q) /\
          (q < ~ABS p = p < ~q /\ q < p)``,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_NEG_LT0,
                       INT_NEG_0, INT_NEGNEG, INT_NEG_GT0,
                       INT_LT_CALCULATE]);

val INT_ABS_LE = store_thm(
  "INT_ABS_LE",
  ``!p q. (ABS p <= q = p <= q /\ ~q <= p) /\
          (q <= ABS p = q <= p \/ p <= ~q) /\
          (~ABS p <= q = ~q <= p \/ p <= q) /\
          (q <= ~ABS p = p <= ~q /\ q <= p)``,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_NEG_LT0,
                       INT_NEG_0, INT_NEGNEG, INT_NEG_GT0, int_le,
                       INT_LT_CALCULATE])

val INT_ABS_EQ = store_thm(
  "INT_ABS_EQ",
  ``!p q. ((ABS p = q) = (p = q) /\ (0 < q) \/ (p = ~q) /\ (0 <= q)) /\
          ((q = ABS p) = (p = q) /\ (0 < q) \/ (p = ~q) /\ (0 <= q))``,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) THEN
  REWRITE_TAC [] THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_NEG_0, INT_NEGNEG,
                       int_eq_calculate, INT_EQ_NEG, INT_INJ,
                       INT_LT_CALCULATE, INT_LE_REFL, INT_LE, INT_NOT_LE]);

(* ----------------------------------------------------------------------
    Define integer rem(ainder) and quot(ient) functions.
      These two are analogous to int_mod and int_div respectively, but
      int_quot rounds towards zero, while int_div rounds towards negative
      infinity.  Once int_quot is fixed, the behaviour of int_rem is
      fixed.  The choice of names follows the example of the SML Basis
      Library.
   ---------------------------------------------------------------------- *)

val _ = print "Define integer rem(ainder) and quot(ient) functions\n"

val int_quot_exists0 = prove(
  ``!i j. ?q. ~(j = 0) ==>
              (q = if 0 < j then
                     if 0 <= i then &(Num i DIV Num j)
                     else ~&(Num ~i DIV Num j)
                   else
                     if 0 <= i then ~&(Num i DIV Num ~j)
                     else &(Num ~i DIV Num ~j))``,
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN REWRITE_TAC [EXISTS_REFL]);

val int_quot_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_quot_exists0


val int_quot = new_specification ("int_quot",["int_quot"],int_quot_exists);

val _ = set_fixity "quot" (Infixl 600)
val _ = overload_on("quot", ``int_quot``);

val INT_QUOT = store_thm(
  "INT_QUOT",
  ``!p q. ~(q = 0) ==> (&p quot &q = &(p DIV q))``,
  SIMP_TAC int_ss [int_quot, INT_INJ, INT_LT, INT_LE, NUM_OF_INT]);

val INT_QUOT_0 = store_thm(
  "INT_QUOT_0",
  ``!q. ~(q = 0) ==> (0 quot q = 0)``,
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  SIMP_TAC int_ss [INT_INJ, INT_QUOT, INT_NEG_EQ0, ZERO_DIV,
                   GSYM NOT_ZERO_LT_ZERO, int_quot, INT_NEG_GT0, INT_LE,
                   INT_LT, INT_NEGNEG, NUM_OF_INT]);

val INT_QUOT_1 = store_thm(
  "INT_QUOT_1",
  ``!p. p quot 1 = p``,
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_QUOT, INT_NEG_EQ0, INT_NEG_GE0,
                       ONE, DIV_ONE, int_quot, INT_NEG_GT0, INT_LE,
                       INT_LT, INT_NEGNEG, NUM_OF_INT]);

val INT_QUOT_NEG = store_thm(
  "INT_QUOT_NEG",
  Term`!p q. ~(q = 0) ==> (~p quot q = ~(p quot q)) /\
                          (p quot ~q = ~(p quot q))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_NEGNEG, INT_NEG_0, INT_NEG_EQ0, INT_INJ,
                       INT_NEGNEG, int_quot, INT_LT, INT_LE, NUM_OF_INT,
                       INT_NEG_GE0, INT_NEG_GT0, INT_NEG_LT0, INT_NEG_LE0,
                       ZERO_DIV, GSYM NOT_ZERO_LT_ZERO]);

val INT_ABS_QUOT = store_thm(
  "INT_ABS_QUOT",
  Term`!p q. ~(q = 0) ==> ABS ((p quot q) * q) <= ABS p`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ0, GSYM INT_NEG_LMUL,
                       GSYM INT_NEG_RMUL, INT_NEG_MUL2, INT_MUL, INT_LE,
                       INT_QUOT, INT_QUOT_NEG, INT_ABS_NEG, INT_ABS_NUM] THEN
  PROVE_TAC [DIVISION, LESS_EQ_EXISTS, NOT_ZERO_LT_ZERO, ZERO_DIV,
             MULT_COMM]);

(* can now prove uniqueness of / and % *)
fun case_tac s =
    REPEAT_TCL STRIP_THM_THEN ASSUME_TAC (Q.SPEC [QUOTE s] INT_NUM_CASES) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN Q.ABBREV_TAC [QUOTE s, QUOTE " = n"] THEN
    POP_ASSUM (K ALL_TAC)

val lem1 = prove(
  ``!x y z. (x = y + ~z) = (x + z = y)``,
  REWRITE_TAC [GSYM int_sub, INT_EQ_SUB_LADD]);
val lem2 = prove(
  ``!x y z. (x = ~y + z) = (x + y = z)``,
  PROVE_TAC [INT_ADD_COMM, lem1]);
val lem3 = prove(
  ``!x y z. (~x + y = z) = (y = x + z)``,
  PROVE_TAC [INT_ADD_COMM, lem2]);
val lem3a = prove(
  ``!x y z. (x + ~y = z) = (x = y + z)``,
  PROVE_TAC [INT_ADD_COMM, lem2]);
val lem4 = prove(
  ``!x y:num. x * y < y = (x = 0) /\ ~(y = 0)``,
  Induct THEN ASM_SIMP_TAC int_ss [MULT_CLAUSES]);

val INT_QUOT_UNIQUE = store_thm(
  "INT_QUOT_UNIQUE",
  Term`!p q k.
          (?r. (p = k * q + r) /\
               (if 0 < p then 0 <= r else r <= 0) /\ ABS r < ABS q) ==>
          (p quot q = k)`,
  REPEAT GEN_TAC THEN CONV_TAC LEFT_IMP_EXISTS_CONV THEN GEN_TAC THEN
  case_tac "p" THEN
  ASM_SIMP_TAC int_ss [INT_LT, INT_NEG_GT0] THEN REPEAT STRIP_TAC THENL [
    `?r0. r = &r0` by PROVE_TAC [NUM_POSINT_EXISTS],
    `?r0. r = ~&r0` by PROVE_TAC [NUM_NEGINT_EXISTS],
    `?r0. r = ~&r0` by PROVE_TAC [NUM_NEGINT_EXISTS]
  ] THEN POP_ASSUM SUBST_ALL_TAC THEN Q.ABBREV_TAC `r = r0` THEN
  POP_ASSUM (K ALL_TAC) THEN REPEAT (POP_ASSUM MP_TAC) THEN
  case_tac "q" THEN case_tac "k" THEN
  ASM_SIMP_TAC int_ss
  [INT_LT, GSYM AND_IMP_INTRO, INT_MUL_RZERO, INT_ABS_NUM, INT_ADD_LID,
   INT_ABS_NEG, INT_LE_REFL, INT_LT_REFL, INT_NEGNEG, GSYM INT_NEG_RMUL,
   GSYM INT_NEG_LMUL, INT_MUL, INT_NEG_0, INT_ADD_LID, INT_ABS_LT0,
   INT_ADD, INT_NEG_GT0, INT_LE, INT_QUOT, INT_INJ, INT_LT_CALCULATE,
   INT_EQ_NEG, INT_QUOT_NEG, LESS_DIV_EQ_ZERO, INT_NEG_LE0, lem1,
   lem2, INT_ADD_RINV, INT_ADD_LINV, lem3, int_eq_calculate, lem4] THEN
  REPEAT STRIP_TAC THENL [
    PROVE_TAC [ADD_COMM, DIV_UNIQUE],
    PROVE_TAC [lem4, LESS_EQ_ADD, ADD_COMM, LESS_EQ_LESS_TRANS],
    PROVE_TAC [lem4, LESS_EQ_ADD, ADD_COMM, LESS_EQ_LESS_TRANS],
    PROVE_TAC [ADD_COMM, DIV_UNIQUE],
    PROVE_TAC [lem4, LESS_EQ_ADD, ADD_COMM, LESS_EQ_LESS_TRANS],
    ASM_SIMP_TAC int_ss [GSYM INT_NEG_ADD, INT_ADD, INT_QUOT_NEG, INT_QUOT,
                         INT_INJ, INT_EQ_NEG, INT_NEGNEG] THEN
    PROVE_TAC [ADD_COMM, DIV_UNIQUE],
    ASM_SIMP_TAC int_ss [GSYM INT_NEG_ADD, INT_ADD, INT_QUOT_NEG, INT_QUOT,
                         INT_INJ, INT_EQ_NEG, INT_NEGNEG] THEN
    PROVE_TAC [ADD_COMM, DIV_UNIQUE],
    PROVE_TAC [lem4, LESS_EQ_ADD, ADD_COMM, LESS_EQ_LESS_TRANS]
  ]);

val INT_QUOT_ID = store_thm(
  "INT_QUOT_ID",
  ``!p. ~(p = 0) ==> (p quot p = 1)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_QUOT_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN
  SIMP_TAC int_ss [INT_ADD_RID, INT_MUL_LID, INT_LE_REFL, INT_ABS_NUM] THEN
  PROVE_TAC [INT_ABS_EQ0, INT_ABS_POS, INT_LE_LT]);

(* define rem *)
val int_rem_exists0 = prove(
  ``!i j. ?r. ~(j = 0) ==> (r = i - i quot j * j)``,
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN REWRITE_TAC [EXISTS_REFL]);
val int_rem_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_rem_exists0

val int_rem = new_specification ("int_rem",["int_rem"],int_rem_exists);

val _ = set_fixity "rem" (Infixl 650);
val _ = overload_on("rem", ``int_rem``);

val INT_REM = store_thm(
  "INT_REM",
  ``!p q. ~(q = 0) ==> (&p rem &q = &(p MOD q))``,
  SIMP_TAC int_ss [int_rem, INT_INJ, int_sub, lem1, lem2, lem3, lem3a,
                   INT_QUOT, INT_MUL, INT_ADD] THEN
  PROVE_TAC [DIVISION, NOT_ZERO_LT_ZERO, MULT_COMM]);

val newlemma = prove(
  ``!x y. (~x + y <= 0 = y <= x) /\ (0 <= x + ~y = y <= x)``,
  REPEAT STRIP_TAC THENL [
    CONV_TAC (LHS_CONV (LAND_CONV (REWR_CONV INT_ADD_COMM))),
    ALL_TAC
  ] THEN REWRITE_TAC [GSYM int_sub, INT_LE_SUB_RADD, INT_LE_SUB_LADD,
                      INT_ADD_RID, INT_ADD_LID]);
val nl2 = prove(
  ``!p q. ~(q = 0n) ==> p DIV q * q <= p``,
  PROVE_TAC [DIVISION, LESS_EQ_ADD, NOT_ZERO_LT_ZERO]);
val nl2a = prove(
  ``!p q. ~(q = 0n) ==> p < q + p DIV q * q /\ p DIV q * q < p + q``,
  REPEAT STRIP_TAC THENL [
    `(p = p DIV q * q + p MOD q) /\ p MOD q < q` by
      PROVE_TAC [DIVISION, NOT_ZERO_LT_ZERO] THEN
    FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o
                   ONCE_REWRITE_RULE [ADD_COMM]) THEN
    ASM_REWRITE_TAC [LESS_MONO_ADD_EQ],
    MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `p` THEN
    ASM_SIMP_TAC int_ss [nl2]
  ]);

val nl3 = prove(
  ``!x y z.
      (x + ~y < z = x < y + z) /\ (~x < y + ~z = z < y + x)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_RADD, INT_LT_SUB_LADD] THEN
  CONV_TAC (RAND_CONV (LHS_CONV (LAND_CONV (REWR_CONV INT_ADD_COMM)))) THEN
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_RADD, INT_LT_SUB_LADD] THEN
  PROVE_TAC [INT_ADD_COMM]);
val nl4 = prove(
  ``!x y z.
      (~x + y < z = y < x + z) /\ (~x < ~y + z = y < x + z)``,
  PROVE_TAC [nl3, INT_ADD_COMM]);

val INT_REMQUOT = store_thm(
  "INT_REMQUOT",
  ``!q. ~(q = 0) ==> !p. (p = p quot q * q + p rem q) /\
                         (if 0 < p then 0 <= p rem q else p rem q <= 0) /\
                         ABS (p rem q) < ABS q``,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CONJ_TAC THEN
  ASM_SIMP_TAC int_ss [int_rem, INT_INJ, int_sub, INT_ADD_ASSOC, lem1, lem2,
                       lem3, lem3a]
  THENL [
    MATCH_ACCEPT_TAC INT_ADD_COMM,
    case_tac "p" THEN case_tac "q" THEN FULL_SIMP_TAC int_ss [INT_INJ] THEN
    ASM_SIMP_TAC int_ss [INT_INJ, INT_QUOT, INT_LE, INT_LT, INT_QUOT_NEG,
                         INT_ADD_RID, INT_MUL, INT_NEG_GT0, INT_ADD_LID,
                         INT_ABS_NUM, INT_ABS_NEG, INT_NEGNEG,
                         GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL, ZERO_DIV,
                         GSYM NOT_ZERO_LT_ZERO, INT_NEG_0, newlemma, nl2
                         ] THEN
    ASM_SIMP_TAC int_ss [INT_ABS_LT, nl3, INT_LT, INT_ADD, nl4, nl2a]
  ]);

val INT_REM_UNIQUE = store_thm(
  "INT_REM_UNIQUE",
  Term`!p q r.
          ABS r < ABS q /\ (if 0 < p then 0 <= r else r <= 0) /\
          (?k. p = k * q + r) ==>
          (p rem q = r)`,
  REPEAT STRIP_TAC THEN
  `~(q = 0)` by (DISCH_THEN SUBST_ALL_TAC THEN
                 FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_LT0]) THEN
  ASM_SIMP_TAC int_ss [int_rem, INT_EQ_SUB_RADD] THEN
  `(k * q + r) quot q = k` by PROVE_TAC [INT_QUOT_UNIQUE] THEN
  ASM_SIMP_TAC int_ss [INT_ADD_COMM]);

val INT_REM_NEG = store_thm(
  "INT_REM_NEG",
  Term`!p q. ~(q = 0) ==> (~p rem q = ~(p rem q)) /\ (p rem ~q = p rem q)`,
  REPEAT GEN_TAC THEN
  case_tac "p" THEN case_tac "q" THEN
  ASM_SIMP_TAC int_ss [INT_INJ, int_rem, INT_NEGNEG, lem1, lem2, lem3,
                       int_sub, INT_NEG_EQ0, GSYM INT_NEG_LMUL,
                       GSYM INT_NEG_RMUL, INT_ADD_LID, INT_ADD_RID,
                       INT_NEG_0, INT_NEG_ADD, INT_QUOT_0, INT_QUOT_NEG,
                       INT_MUL_LZERO] THEN
  METIS_TAC [INT_ADD_ASSOC, INT_ADD_COMM, INT_ADD_LINV, INT_ADD_RID,
             INT_ADD_LID, INT_ADD_RINV]);

val INT_REM_ID = store_thm(
  "INT_REM_ID",
  Term`!p. ~(p = 0) ==> (p rem p = 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQUE THEN
  SIMP_TAC int_ss [INT_LE_REFL] THEN CONJ_TAC THENL [
    PROVE_TAC [INT_LE_LT, INT_ABS_POS, INT_ABS_EQ0, INT_ABS_NUM],
    Q.EXISTS_TAC `1` THEN REWRITE_TAC [INT_MUL_LID, INT_ADD_RID, INT_LE_REFL]
  ]);

val INT_REM0 = store_thm(
  "INT_REM0",
  ``!q. ~(q = 0) ==> (0 rem q = 0)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQUE THEN
  ASM_SIMP_TAC int_ss [INT_LE_REFL, INT_ABS_NUM, INT_ADD_RID] THEN
  PROVE_TAC [INT_LE_LT, INT_ABS_POS, INT_MUL_LZERO, INT_ABS_EQ0]);

val INT_REM_COMMON_FACTOR = store_thm(
  "INT_REM_COMMON_FACTOR",
  Term`!p. ~(p = 0) ==> !q. (q * p) rem p = 0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_REM_UNIQUE THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ADD_RID] THEN
  PROVE_TAC [INT_ABS_NUM, INT_LE_LT, INT_ABS_EQ0, INT_ABS_POS]);

val INT_REM_EQ0 = store_thm(
  "INT_REM_EQ0",
  Term`!q. ~(q = 0) ==> !p. (p rem q = 0) = (?k. p = k * q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.PAT_ASSUM `~(q = 0)` (ASSUME_TAC o Q.SPEC `p` o
                            MATCH_MP INT_REMQUOT) THEN
    PROVE_TAC [INT_ADD_RID],
    MATCH_MP_TAC INT_REM_UNIQUE THEN CONJ_TAC THENL [
      PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS],
      PROVE_TAC [INT_ADD_RID, INT_LE_REFL]
    ]
  ]);

val INT_MUL_QUOT = store_thm(
  "INT_MUL_QUOT",
  Term`!p:int q k. ~(q = 0) /\ (p rem q = 0) ==>
                   ((k * p) quot q = k * (p quot q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_QUOT_UNIQUE THEN
  `?m. p = m * q` by PROVE_TAC [INT_REM_EQ0] THEN
  Q.SUBGOAL_THEN `p quot q = m` ASSUME_TAC THENL [
    MATCH_MP_TAC INT_QUOT_UNIQUE THEN
    Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC int_ss [INT_ADD_RID, INT_LE_REFL] THEN
    PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS],
    POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
    Q.EXISTS_TAC `0` THEN
    SIMP_TAC int_ss [INT_MUL_ASSOC, INT_ADD_RID, INT_LE_REFL] THEN
    PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS]
  ]);

val INT_REM_EQ_MOD = store_thm(
  "INT_REM_EQ_MOD",
  ``!i n.
      0 < n ==>
      (i rem n = if i < 0 then (i - 1) % n - n + 1 else i % n)``,
  REPEAT STRIP_TAC THEN
  `n <> 0` by METIS_TAC [INT_LT_REFL] THEN
  MATCH_MP_TAC INT_REM_UNIQUE THEN
  Cases_on `i < 0` THENL [
    ASM_SIMP_TAC (srw_ss()) [] THEN
    Q.ABBREV_TAC `j = (i - 1) % n` THEN
    `0 <= j /\ j < n`
       by PROVE_TAC [INT_LT_ANTISYM, INT_DIVISION] THEN
    `~(0 < i)` by PROVE_TAC [INT_LT_ANTISYM] THEN
    SRW_TAC [][] THENL [
      `0 <= n` by IMP_RES_TAC INT_LT_IMP_LE THEN
      `ABS n = n` by PROVE_TAC [INT_ABS_EQ_ID] THEN
      `~(j - n + 1) = n - (j + 1)`
         by SRW_TAC [][int_sub, INT_NEG_ADD, INT_NEGNEG,
                       AC INT_ADD_ASSOC INT_ADD_COMM] THEN
      `0 <= n - (j + 1)` by PROVE_TAC [INT_SUB_LE, INT_LT_LE1] THEN
      `ABS (j - n + 1) = n - (j + 1)`
         by PROVE_TAC [INT_ABS_EQ_ID, INT_ABS_NEG] THEN
      SRW_TAC [][INT_LT_SUB_RADD, INT_LT_ADDR, GSYM INT_LE_LT1],

      SRW_TAC [][INT_LT_SUB_RADD, GSYM INT_LT_LE1],

      Q.EXISTS_TAC `(i - 1) / n + 1` THEN
      SRW_TAC [][INT_RDISTRIB, Abbr`j`, INT_MUL_LID] THEN
      SRW_TAC [][INT_ADD_ASSOC] THEN
      SRW_TAC [][Once (GSYM INT_EQ_SUB_RADD)] THEN
      `(i - 1) / n * n + (i - 1) % n = i - 1`
         by METIS_TAC [INT_DIVISION, INT_LT_ANTISYM] THEN
      Q_TAC SUFF_TAC `!x y z. x + y + (z - y) = x + z`
         THEN1 SRW_TAC [][] THEN
      SRW_TAC [][INT_SUB_ADD2, GSYM INT_ADD_ASSOC]
    ],

    ASM_SIMP_TAC (srw_ss()) [] THEN
    `0 <= n` by METIS_TAC [INT_LE_LT] THEN
    `0 <= i % n /\ i % n < n` by METIS_TAC [INT_DIVISION, INT_LT_ANTISYM] THEN
    `(ABS (i % n) = i % n) /\ (ABS n = n)` by METIS_TAC [INT_ABS_EQ_ID] THEN
    SRW_TAC [][] THENL [
      `0 < i \/ (i = 0)` by METIS_TAC [INT_NOT_LT, INT_LE_LT] THEN
      SRW_TAC [][INT_MOD0, INT_LE_REFL],

      Q.EXISTS_TAC `i / n` THEN METIS_TAC [INT_DIVISION]
    ]
  ]);


(*----------------------------------------------------------------------*)
(* Define divisibility                                                  *)
(*----------------------------------------------------------------------*)

val _ = print "Facts about integer divisibility\n";
val INT_DIVIDES = new_definition (
  "INT_DIVIDES",
  Term`int_divides p q = ?m:int. m * p = q`);
val _ = set_fixity "int_divides" (Infix(NONASSOC, 450))

val INT_DIVIDES_MOD0 = store_thm(
  "INT_DIVIDES_MOD0",
  Term`!p q. p int_divides q =
             ((q % p = 0) /\ ~(p = 0)) \/ ((p = 0) /\ (q = 0))`,
  REWRITE_TAC [INT_DIVIDES] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  STRIP_TAC THENL [
    Cases_on `p = 0` THENL [
      POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM (SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC [INT_MUL_RZERO],
      FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      PROVE_TAC [INT_MOD_COMMON_FACTOR]
    ],
    PROVE_TAC [INT_MOD_EQ0],
    ASM_REWRITE_TAC [INT_MUL_RZERO]
  ]);

val INT_DIVIDES_0 = store_thm(
  "INT_DIVIDES_0",
  Term`(!x. x int_divides 0) /\ (!x. 0 int_divides x = (x = 0))`,
  PROVE_TAC [INT_DIVIDES, INT_MUL_RZERO, INT_MUL_LZERO]);

val INT_DIVIDES_1 = store_thm(
  "INT_DIVIDES_1",
  Term`!x. 1 int_divides x /\
           (x int_divides 1 = (x = 1) \/ (x = ~1))`,
  REPEAT STRIP_TAC THEN
  PROVE_TAC [INT_DIVIDES, INT_MUL_RID, INT_MUL_EQ_1]);

val INT_DIVIDES_REFL = store_thm(
  "INT_DIVIDES_REFL",
  Term`!x. x int_divides x`,
  PROVE_TAC [INT_DIVIDES, INT_MUL_LID]);

val INT_DIVIDES_TRANS = store_thm(
  "INT_DIVIDES_TRANS",
  Term`!x y z. x int_divides y /\ y int_divides z ==> x int_divides z`,
  PROVE_TAC [INT_DIVIDES, INT_MUL_ASSOC]);

val INT_DIVIDES_MUL = store_thm(
  "INT_DIVIDES_MUL",
  Term`!p q. p int_divides p * q /\ p int_divides q * p`,
  PROVE_TAC [INT_DIVIDES, INT_MUL_COMM]);

val INT_DIVIDES_LMUL = store_thm(
  "INT_DIVIDES_LMUL",
  Term`!p q r. p int_divides q ==> (p int_divides (q * r))`,
  PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM, INT_DIVIDES]);

val INT_DIVIDES_RMUL = store_thm(
  "INT_DIVIDES_RMUL",
  Term`!p q r. p int_divides q ==> (p int_divides (r * q))`,
  PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM, INT_DIVIDES]);

val INT_DIVIDES_MUL_BOTH = store_thm(
  "INT_DIVIDES_MUL_BOTH",
  ``!p q r. ~(p = 0) ==> (p * q int_divides p * r = q int_divides r)``,
  SIMP_TAC bool_ss [INT_DIVIDES] THEN
  REPEAT GEN_TAC THEN
  `!m p q. m * (p * q) = p * (m * q)` by
     PROVE_TAC [INT_MUL_ASSOC, INT_MUL_COMM] THEN
  POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  PROVE_TAC [INT_EQ_LMUL]);

val INT_DIVIDES_LADD = store_thm(
  "INT_DIVIDES_LADD",
  Term`!p q r. p int_divides q ==>
               (p int_divides (q + r) = p int_divides r)`,
  REWRITE_TAC [INT_DIVIDES] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `n` ASSUME_TAC) THENL [
    Q.EXISTS_TAC `n - m` THEN
    ASM_REWRITE_TAC [INT_SUB_RDISTRIB, INT_ADD_SUB],
    Q.EXISTS_TAC `m + n` THEN
    ASM_REWRITE_TAC [INT_RDISTRIB]
  ]);

val INT_DIVIDES_RADD = save_thm(
  "INT_DIVIDES_RADD",
  ONCE_REWRITE_RULE [INT_ADD_COMM] INT_DIVIDES_LADD);

val INT_DIVIDES_NEG = store_thm(
  "INT_DIVIDES_NEG",
  Term`!p q. (p int_divides ~q = p int_divides q) /\
             (~p int_divides q = p int_divides q)`,
  REWRITE_TAC [INT_DIVIDES] THEN ONCE_REWRITE_TAC [INT_NEG_MINUS1] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `n` ASSUME_TAC) THENL [
    Q.EXISTS_TAC `~1 * n` THEN
    ASM_REWRITE_TAC [GSYM INT_MUL_ASSOC, GSYM INT_NEG_MINUS1,
                     INT_NEGNEG],
    PROVE_TAC [INT_MUL_ASSOC],
    PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM],
    PROVE_TAC [INT_NEG_MINUS1, INT_NEG_MUL2]
  ]);

val INT_DIVIDES_LSUB = store_thm(
  "INT_DIVIDES_LSUB",
  Term`!p q r. p int_divides q ==>
               (p int_divides (q - r) = p int_divides r)`,
  REWRITE_TAC [int_sub] THEN
  PROVE_TAC [INT_DIVIDES_NEG, INT_DIVIDES_LADD]);

val INT_DIVIDES_RSUB = store_thm(
  "INT_DIVIDES_RSUB",
  Term`!p q r. p int_divides q ==>
               (p int_divides (r - q) = p int_divides r)`,
  REWRITE_TAC [int_sub] THEN
  PROVE_TAC [INT_DIVIDES_NEG, INT_DIVIDES_RADD]);

(*----------------------------------------------------------------------*)
(* Define exponentiation                                                *)
(*----------------------------------------------------------------------*)

val _ = print "Exponentiation\n"

val int_exp = Prim_rec.new_recursive_definition{
  def = Term`(int_exp (p:int) 0 = 1) /\
             (int_exp p (SUC n) = p * int_exp p n)`,
  name = "int_exp",
  rec_axiom = prim_recTheory.num_Axiom};

val _ = set_fixity "int_exp"  (Infixr 700);
val _ = overload_on ("**", Term`$int_exp`);

val INT_EXP = store_thm(
  "INT_EXP",
  Term`!n m. &n ** m = &(n EXP m)`,
  REPEAT GEN_TAC THEN Induct_on `m` THENL [
    REWRITE_TAC [int_exp, EXP],
    ASM_REWRITE_TAC [int_exp, EXP, INT_MUL]
  ]);

val INT_EXP_EQ0 = store_thm(
  "INT_EXP_EQ0",
  Term`!(p:int) n. (p ** n = 0) = (p = 0) /\ ~(n = 0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Induct_on `n` THENL [
      SIMP_TAC int_ss [int_exp, INT_INJ],
      SIMP_TAC int_ss [int_exp, INT_ENTIRE] THEN PROVE_TAC []
    ],
    `?m. n = SUC m` by PROVE_TAC [num_CASES] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    SIMP_TAC int_ss [int_exp, INT_MUL_LZERO]
  ]);

val INT_MUL_SIGN_CASES = store_thm(
  "INT_MUL_SIGN_CASES",
  Term`!p:int q. ((0 < p * q) = (0 < p /\ 0 < q \/ p < 0 /\ q < 0)) /\
                 ((p * q < 0) = (0 < p /\ q < 0 \/ p < 0 /\ 0 < q))`,
  REPEAT GEN_TAC THEN
  Cases_on `0 <= p` THEN Cases_on `0 <= q` THENL [
    (* both non-negative *)
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `?m. q = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [INT_LE, INT_LT, INT_MUL] THEN
    REWRITE_TAC [GSYM NOT_ZERO_LT_ZERO, MULT_EQ_0, DE_MORGAN_THM],
    (* p positive, q negative *)
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `?m. q = ~&m` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_NEG_GE0, GSYM INT_NEG_RMUL,
                           INT_NEG_GT0, INT_NEG_LT0, INT_MUL, INT_LT,
                           INT_LE, NOT_LESS_EQUAL, NOT_LESS_0] THEN
    ASM_SIMP_TAC int_ss [GSYM NOT_ZERO_LT_ZERO, MULT_EQ_0],
    (* q positive, p negative *)
    `?n. q = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `?m. p = ~&m` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_NEG_GE0, GSYM INT_NEG_LMUL,
                           INT_NEG_GT0, INT_NEG_LT0, INT_MUL, INT_LT,
                           INT_LE, NOT_LESS_EQUAL, NOT_LESS_0] THEN
    ASM_SIMP_TAC int_ss [GSYM NOT_ZERO_LT_ZERO, MULT_EQ_0],
    (* both negative *)
    `?n. p = ~&n` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `?m. q = ~&m` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_NEG_GE0, INT_NEG_MUL2, INT_MUL, INT_LT,
                           INT_LE, NOT_LESS_0, INT_NEG_GT0, INT_NEG_LT0] THEN
    SIMP_TAC int_ss [MULT_EQ_0, GSYM NOT_ZERO_LT_ZERO]
  ]);

val INT_EXP_NEG = store_thm(
  "INT_EXP_NEG",
  Term`!n m.
         (EVEN n ==> (~&m ** n = &(m EXP n))) /\
         (ODD n ==> (~&m ** n = ~&(m EXP n)))`,
  Induct THENL [
    SIMP_TAC int_ss [EVEN, ODD, int_exp, INT_LE, EXP],
    ASM_SIMP_TAC int_ss [EVEN, ODD, GSYM EVEN_ODD, GSYM ODD_EVEN, int_exp,
                         EXP, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_MUL,
                         INT_NEGNEG]
  ]);

val INT_EXP_ADD_EXPONENTS = store_thm(
  "INT_EXP_ADD_EXPONENTS",
  Term`!n m p:int. p ** n * p ** m = p ** (n + m)`,
  Induct THENL [
    SIMP_TAC int_ss [int_exp, INT_MUL_LID],
    SIMP_TAC bool_ss [int_exp, ADD_CLAUSES] THEN
    PROVE_TAC [INT_MUL_ASSOC, INT_EQ_LMUL]
  ]);

val INT_EXP_MULTIPLY_EXPONENTS = store_thm(
  "INT_EXP_MULTIPLY_EXPONENTS",
  Term`!m n p:int. (p ** n) ** m = p ** (n * m)`,
  Induct THENL [
    SIMP_TAC int_ss [MULT_CLAUSES, int_exp],
    ASM_SIMP_TAC bool_ss [int_exp, MULT_CLAUSES, GSYM INT_EXP_ADD_EXPONENTS]
  ]);

val INT_EXP_MOD = store_thm(
  "INT_EXP_MOD",
  Term`!m n p:int. n <= m /\ ~(p = 0) ==> (p ** m % p ** n = 0)`,
  SIMP_TAC int_ss [INT_MOD_EQ0, INT_EXP_EQ0] THEN
  PROVE_TAC [LESS_EQ_EXISTS, INT_EXP_ADD_EXPONENTS, ADD_COMM]);

val INT_EXP_SUBTRACT_EXPONENTS = store_thm(
  "INT_EXP_SUBTRACT_EXPONENTS",
  Term`!m n p:int. n <= m /\ ~(p = 0) ==>
                   ((p ** m) / (p ** n) = p ** (m - n))`,
  Induct THENL [
    REPEAT STRIP_TAC THEN
    `n = 0` by ASM_SIMP_TAC int_ss [] THEN
    RW_TAC int_ss [int_exp, ONE, INT_EXP, DIV_ONE, INT_DIV],
    REPEAT GEN_TAC THEN Cases_on `n = SUC m` THENL
    [ASM_SIMP_TAC int_ss [int_exp, INT_DIV_ID, INT_ENTIRE, INT_EXP_EQ0],
     STRIP_TAC THEN `n <= m` by ASM_SIMP_TAC int_ss []
       THEN ASM_SIMP_TAC int_ss [SUB, int_exp] THEN
       `p ** m % p ** n = 0` by PROVE_TAC [INT_EXP_MOD] THEN
       `p * p ** m / p ** n = p * (p ** m / p ** n)`
         by (MATCH_MP_TAC INT_MUL_DIV THEN ASM_SIMP_TAC int_ss [INT_EXP_EQ0])
       THEN RW_TAC int_ss []]]);

(*----------------------------------------------------------------------*)
(* Define integer minimum and maximum                                   *)
(*----------------------------------------------------------------------*)

val INT_MIN = new_definition(
  "INT_MIN",
  Term`int_min (x:int) y = if x < y then x else y`);

val INT_MAX = new_definition(
  "INT_MAX",
  Term`int_max (x:int) y = if x < y then y else x`);

val INT_MIN_LT = store_thm(
  "INT_MIN_LT",
  Term`!x y z. x < int_min y z ==> x < y /\ x < z`,
  SIMP_TAC bool_ss [INT_MIN] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  PROVE_TAC [INT_LT_TRANS, INT_LT_TOTAL]);

val INT_MAX_LT = store_thm(
  "INT_MAX_LT",
  Term`!x y z. int_max x y < z ==> x < z /\ y < z`,
  SIMP_TAC bool_ss [INT_MAX] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  PROVE_TAC [INT_LT_TRANS, INT_LT_TOTAL]);

val INT_MIN_NUM = store_thm(
  "INT_MIN_NUM",
  ``!m n. int_min (&m) (&n) = &(MIN m n)``,
  SIMP_TAC (bool_ss ++ LIFT_COND_ss) [INT_MIN, MIN_DEF, INT_LT]);

val INT_MAX_NUM = store_thm(
  "INT_MAX_NUM",
  ``!m n. int_max (&m) (&n) = &(MAX m n)``,
  SIMP_TAC (bool_ss ++ LIFT_COND_ss) [INT_MAX, MAX_DEF, INT_LT]);


(* ----------------------------------------------------------------------
    Some monotonicity results
   ---------------------------------------------------------------------- *)

val INT_LT_MONO = store_thm(
  "INT_LT_MONO",
  ``!x y z. 0 < x ==> (x * y < x * z = y < z)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (Conv.BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LT_SUB_LADD, GSYM INT_SUB_LDISTRIB] THEN
  PROVE_TAC [INT_LT_ANTISYM, INT_MUL_SIGN_CASES]);

val INT_LE_MONO = store_thm(
  "INT_LE_MONO",
  ``!x y z. 0 < x ==> (x * y <= x * z = y <= z)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (Conv.BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LE_SUB_LADD, GSYM INT_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC bool_ss [INT_LE_LT, INT_MUL_SIGN_CASES, INT_LT_GT] THEN
  PROVE_TAC [INT_ENTIRE, INT_LT_REFL]);

open pred_setTheory
val INFINITE_INT_UNIV = store_thm(
  "INFINITE_INT_UNIV",
  ``INFINITE univ(:int)``,
  REWRITE_TAC [INFINITE_DEF] THEN STRIP_TAC THEN
  `FINITE (IMAGE Num univ(:int))` by SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `IMAGE Num univ(:int) = univ(:num)`
        THEN1 (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][EXTENSION] THEN Q.EXISTS_TAC `&x` THEN SRW_TAC [][NUM_OF_INT]);
val _ = export_rewrites ["INFINITE_INT_UNIV"]

(*----------------------------------------------------------------------*)
(* Prove rewrites for calculation with integers                         *)
(*----------------------------------------------------------------------*)

val _ = print "Proving rewrites for calculation with integers\n"

val INT_ADD_CALCULATE = store_thm(
  "INT_ADD_CALCULATE",
  Term`!p:int n m.
          (0 + p = p) /\ (p + 0 = p) /\
          (&n + &m:int = &(n + m)) /\
          (&n + ~&m = if m <= n then &(n - m) else ~&(m - n)) /\
          (~&n + &m = if n <= m then &(m - n) else ~&(n - m)) /\
          (~&n + ~&m = ~&(n + m))`,
  SIMP_TAC (int_ss ++ boolSimps.COND_elim_ss) [
    INT_ADD_LID, INT_ADD_RID, INT_ADD, GSYM INT_NEG_ADD, INT_ADD_COMM,
    GSYM int_sub, INT_EQ_SUB_RADD, INT_INJ, INT_SUB
  ]);

val INT_ADD_REDUCE = store_thm(
  "INT_ADD_REDUCE",
  Term`!p:int n m.
          (0 + p = p) /\ (p + 0 = p) /\ (~0 = 0) /\ (~~p = p) /\
          (&(NUMERAL n) + &(NUMERAL m):int =
             &(NUMERAL (numeral$iZ (n + m)))) /\
          (&(NUMERAL n) + ~&(NUMERAL m):int =
             if m <= n then &(NUMERAL (n - m)) else ~&(NUMERAL (m - n))) /\
          (~&(NUMERAL n) + &(NUMERAL m):int =
             if n <= m then &(NUMERAL (m - n)) else ~&(NUMERAL (n - m))) /\
          (~&(NUMERAL n) + ~&(NUMERAL m):int =
             ~&(NUMERAL (numeral$iZ (n + m))))`,
  SIMP_TAC (int_ss ++ boolSimps.COND_elim_ss) [
    INT_ADD_LID, INT_ADD_RID, INT_ADD, GSYM INT_NEG_ADD, INT_ADD_COMM,
    GSYM int_sub, INT_EQ_SUB_RADD, INT_INJ, INT_SUB, numeralTheory.iZ,
    NUMERAL_DEF, INT_NEG_0, INT_NEGNEG
  ]);

val INT_SUB_CALCULATE = save_thm("INT_SUB_CALCULATE", int_sub);

val INT_SUB_REDUCE = store_thm(
  "INT_SUB_REDUCE",
  Term`!m n p:int.
        (p - 0 = p) /\ (0 - p = ~p) /\
        (&(NUMERAL m) - &(NUMERAL n):int = &(NUMERAL m) + ~&(NUMERAL n)) /\
        (~&(NUMERAL m) - &(NUMERAL n):int = ~&(NUMERAL m) + ~&(NUMERAL n)) /\
        (&(NUMERAL m) - ~&(NUMERAL n):int = &(NUMERAL m) + &(NUMERAL n)) /\
        (~&(NUMERAL m) - ~&(NUMERAL n):int = ~&(NUMERAL m) + &(NUMERAL n))`,
  REWRITE_TAC [int_sub, INT_NEG_0, INT_ADD_LID, INT_ADD_RID, INT_NEGNEG]);

val INT_MUL_CALCULATE = save_thm(
  "INT_MUL_CALCULATE",
  LIST_CONJ [INT_MUL, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG]);

val INT_MUL_REDUCE = store_thm(
  "INT_MUL_REDUCE",
  Term`!m n p.
         (p * 0i = 0) /\ (0 * p = 0) /\
         (&(NUMERAL m) * &(NUMERAL n):int = &(NUMERAL (m * n))) /\
         (~&(NUMERAL m) * &(NUMERAL n) = ~&(NUMERAL (m * n))) /\
         (&(NUMERAL m) * ~&(NUMERAL n) = ~&(NUMERAL (m * n))) /\
         (~&(NUMERAL m) * ~&(NUMERAL n) = &(NUMERAL (m * n)))`,
  REWRITE_TAC [INT_MUL, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG,
               NUMERAL_DEF, INT_MUL_LZERO, INT_MUL_RZERO]);

val INT_DIV_CALCULATE = save_thm(
  "INT_DIV_CALCULATE",
  LIST_CONJ [INT_DIV, INT_DIV_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG]);

val NB_NOT_0 = prove(
  ``!n. ~(BIT1 n = 0) /\ ~(BIT2 n = 0)``,
  SIMP_TAC bool_ss [BIT1, BIT2, ADD_CLAUSES, SUC_NOT]);
val INT_DIV_REDUCE = store_thm(
  "INT_DIV_REDUCE",
  Term`!m n.
         (0i / &(NUMERAL (BIT1 n)) = 0i) /\
         (0i / &(NUMERAL (BIT2 n)) = 0i) /\
         (&(NUMERAL m) / &(NUMERAL (BIT1 n)) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
         (&(NUMERAL m) / &(NUMERAL (BIT2 n)) =
            &(NUMERAL m DIV NUMERAL (BIT2 n))) /\
         (~&(NUMERAL m) / &(NUMERAL (BIT1 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT1 n)) +
            if NUMERAL m MOD NUMERAL (BIT1 n) = 0 then 0 else ~1) /\
         (~&(NUMERAL m) / &(NUMERAL (BIT2 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT2 n)) +
            if NUMERAL m MOD NUMERAL (BIT2 n) = 0 then 0 else ~1) /\
         (&(NUMERAL m) / ~&(NUMERAL (BIT1 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT1 n)) +
            if NUMERAL m MOD NUMERAL (BIT1 n) = 0 then 0 else ~1) /\
         (&(NUMERAL m) / ~&(NUMERAL (BIT2 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT2 n)) +
            if NUMERAL m MOD NUMERAL (BIT2 n) = 0 then 0 else ~1) /\
         (~&(NUMERAL m) / ~&(NUMERAL (BIT1 n)) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
         (~&(NUMERAL m) / ~&(NUMERAL (BIT2 n)) =
            &(NUMERAL m DIV NUMERAL (BIT2 n)))`,
  SIMP_TAC int_ss [INT_DIV, INT_DIV_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG,
                   NUMERAL_DEF, NB_NOT_0, ZERO_DIV,
                   GSYM NOT_ZERO_LT_ZERO] THEN
  SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ0, int_div, INT_NEGNEG, INT_NEG_GE0,
                   NUMERAL_DEF, NB_NOT_0, ZERO_DIV,
                   GSYM NOT_ZERO_LT_ZERO, INT_LT, INT_LE, NUM_OF_INT,
                   INT_NEG_EQ0, INT_NEG_0] THEN
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `m = 0` THEN
  ASM_SIMP_TAC int_ss [ZERO_DIV, NB_NOT_0, GSYM NOT_ZERO_LT_ZERO,
                       ZERO_MOD, INT_NEG_0, INT_ADD, INT_INJ]);

val INT_QUOT_CALCULATE = save_thm(
  "INT_QUOT_CALCULATE",
  LIST_CONJ [INT_QUOT, INT_QUOT_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG]);

val INT_QUOT_REDUCE = store_thm(
  "INT_QUOT_REDUCE",
  Term`!m n.
         (0i quot &(NUMERAL (BIT1 n)) = 0i) /\
         (0i quot &(NUMERAL (BIT2 n)) = 0i) /\
         (&(NUMERAL m) quot &(NUMERAL (BIT1 n)) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
         (&(NUMERAL m) quot &(NUMERAL (BIT2 n)) =
            &(NUMERAL m DIV NUMERAL (BIT2 n))) /\
         (~&(NUMERAL m) quot &(NUMERAL (BIT1 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT1 n))) /\
         (~&(NUMERAL m) quot &(NUMERAL (BIT2 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT2 n))) /\
         (&(NUMERAL m) quot ~&(NUMERAL (BIT1 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT1 n))) /\
         (&(NUMERAL m) quot ~&(NUMERAL (BIT2 n)) =
            ~&(NUMERAL m DIV NUMERAL (BIT2 n))) /\
         (~&(NUMERAL m) quot ~&(NUMERAL (BIT1 n)) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
         (~&(NUMERAL m) quot ~&(NUMERAL (BIT2 n)) =
            &(NUMERAL m DIV NUMERAL (BIT2 n)))`,
  SIMP_TAC bool_ss [INT_QUOT, INT_QUOT_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG,
                    NUMERAL_DEF, BIT1, BIT2, ZERO_DIV, ADD_CLAUSES, NOT_SUC,
                    prim_recTheory.LESS_0]);

val INT_MOD_CALCULATE = save_thm(
  "INT_MOD_CALCULATE",
  LIST_CONJ [INT_MOD, INT_MOD_NEG, INT_NEGNEG, INT_INJ, INT_NEG_EQ0]);

val INT_MOD_REDUCE = store_thm(
  "INT_MOD_REDUCE",
  Term`!m n. (0i % &(NUMERAL (BIT1 n)) = 0i) /\
             (0i % &(NUMERAL (BIT2 n)) = 0i) /\
             (&(NUMERAL m) % &(NUMERAL (BIT1 n)) =
                &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
             (&(NUMERAL m) % &(NUMERAL (BIT2 n)) =
                &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
             (x % &(NUMERAL (BIT1 n)) =
                x - x / &(NUMERAL(BIT1 n)) *
                      &(NUMERAL(BIT1 n))) /\
             (x % &(NUMERAL (BIT2 n)) =
                x - x / &(NUMERAL(BIT2 n)) *
                      &(NUMERAL(BIT2 n)))`,
  SIMP_TAC int_ss [INT_MOD_CALCULATE, BIT1, BIT2,
                   NUMERAL_DEF, ALT_ZERO, ZERO_MOD, int_mod]);



val INT_REM_CALCULATE = save_thm(
  "INT_REM_CALCULATE",
  LIST_CONJ [INT_REM, INT_REM_NEG, INT_NEGNEG, INT_INJ, INT_NEG_EQ0]);

val INT_REM_REDUCE = store_thm(
  "INT_REM_REDUCE",
  Term`!m n. (0i rem &(NUMERAL (BIT1 n)) = 0i) /\
             (0i rem &(NUMERAL (BIT2 n)) = 0i) /\
             (&(NUMERAL m) rem &(NUMERAL (BIT1 n)) =
                &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
             (&(NUMERAL m) rem &(NUMERAL (BIT2 n)) =
                &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
             (~&(NUMERAL m) rem &(NUMERAL (BIT1 n)) =
                ~&(NUMERAL m MOD NUMERAL (BIT1 n))) /\
             (~&(NUMERAL m) rem &(NUMERAL (BIT2 n)) =
                ~&(NUMERAL m MOD NUMERAL (BIT2 n))) /\
             (&(NUMERAL m) rem ~&(NUMERAL (BIT1 n)) =
                &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
             (&(NUMERAL m) rem ~&(NUMERAL (BIT2 n)) =
                &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
             (~&(NUMERAL m) rem ~&(NUMERAL (BIT1 n)) =
                ~&(NUMERAL m MOD NUMERAL (BIT1 n))) /\
             (~&(NUMERAL m) rem ~&(NUMERAL (BIT2 n)) =
                ~&(NUMERAL m MOD NUMERAL (BIT2 n)))`,
  SIMP_TAC int_ss [INT_REM_CALCULATE, BIT1, BIT2,
                   NUMERAL_DEF, ALT_ZERO, ZERO_MOD]);

val ODD_NB1 = prove(
  Term`!n. ODD(BIT1 n)`,
  SIMP_TAC bool_ss [BIT1, ODD, ADD_CLAUSES, ODD_ADD]);
val EVEN_NB2 = prove(
  Term`!n. EVEN(BIT2 n)`,
  SIMP_TAC bool_ss [BIT2, ADD_CLAUSES, EVEN, EVEN_ADD]);

val INT_EXP_CALCULATE = store_thm(
  "INT_EXP_CALCULATE",
  Term`!p:int n m.
        (p ** 0 = 1) /\ (&n ** m = &(n EXP m)) /\
        (~&n ** NUMERAL (BIT1 m) =
           ~&(NUMERAL (n EXP NUMERAL (BIT1 m)))) /\
        (~&n ** NUMERAL (BIT2 m) =
            &(NUMERAL (n EXP NUMERAL (BIT2 m))))`,
  SIMP_TAC int_ss [INT_EXP, int_exp] THEN
  SIMP_TAC int_ss [NUMERAL_DEF, ODD_NB1, EVEN_NB2, INT_EXP_NEG]);

val INT_EXP_REDUCE = store_thm(
  "INT_EXP_REDUCE",
  Term`!n m p:int.
          (p ** 0 = 1) /\
          (&(NUMERAL n):int ** (NUMERAL m) = &(NUMERAL (n EXP m))) /\
          (~&(NUMERAL n) ** NUMERAL (BIT1 m) =
             ~&(NUMERAL (n EXP BIT1 m))) /\
          (~&(NUMERAL n) ** NUMERAL (BIT2 m) =
             &(NUMERAL (n EXP BIT2 m)))`,
  SIMP_TAC int_ss [INT_EXP_CALCULATE, NUMERAL_DEF]);

val INT_LT_REDUCE = store_thm(
  "INT_LT_REDUCE",
  Term`!n m. (0i < &(NUMERAL (BIT1 n)) = T) /\
             (0i < &(NUMERAL (BIT2 n)) = T) /\
             (0i < 0i = F) /\
             (0i < ~&(NUMERAL n) = F) /\
             (&(NUMERAL n) < 0i = F) /\
             (~&(NUMERAL (BIT1 n)) < 0i = T) /\
             (~&(NUMERAL (BIT2 n)) < 0i = T) /\
             (&(NUMERAL n) :int < &(NUMERAL m) = n < m) /\
             (~&(NUMERAL (BIT1 n)) < &(NUMERAL m) = T) /\
             (~&(NUMERAL (BIT2 n)) < &(NUMERAL m) = T) /\
             (&(NUMERAL n) < ~&(NUMERAL m) = F) /\
             (~&(NUMERAL n) < ~&(NUMERAL m) = m < n)`,
  SIMP_TAC bool_ss [INT_LT_CALCULATE, NUMERAL_DEF, BIT1,
                    BIT2] THEN
  CONV_TAC ARITH_CONV);

val INT_LE_CALCULATE = save_thm("INT_LE_CALCULATE", INT_LE_LT);

val INT_LE_REDUCE = store_thm(
  "INT_LE_REDUCE",
  Term`!n m. (0i <= 0i = T) /\ (0i <= &(NUMERAL n) = T) /\
             (0i <= ~&(NUMERAL (BIT1 n)) = F) /\
             (0i <= ~&(NUMERAL (BIT2 n)) = F) /\
             (&(NUMERAL(BIT1 n)) <= 0i = F) /\
             (&(NUMERAL(BIT2 n)) <= 0i = F) /\
             (~&(NUMERAL(BIT1 n)) <= 0i = T) /\
             (~&(NUMERAL(BIT2 n)) <= 0i = T) /\
             (&(NUMERAL n):int <= &(NUMERAL m) = n <= m) /\
             (&(NUMERAL n) <= ~&(NUMERAL (BIT1 m)) = F) /\
             (&(NUMERAL n) <= ~&(NUMERAL (BIT2 m)) = F) /\
             (~&(NUMERAL n) <= &(NUMERAL m) = T) /\
             (~&(NUMERAL n) <= ~&(NUMERAL m) = m <= n)`,
  SIMP_TAC bool_ss [NUMERAL_DEF, INT_LE_CALCULATE, INT_LT_CALCULATE,
                    int_eq_calculate, INT_INJ, INT_EQ_NEG, BIT1,
                    BIT2] THEN
  CONV_TAC ARITH_CONV);

val INT_GT_CALCULATE = save_thm("INT_GT_CALCULATE", int_gt);
val INT_GT_REDUCE = save_thm(
  "INT_GT_REDUCE",
  PURE_REWRITE_RULE [GSYM int_gt] INT_LT_REDUCE);
val INT_GE_CALCULATE = save_thm("INT_GE_CALCULATE", int_ge);
val INT_GE_REDUCE = save_thm(
  "INT_GE_REDUCE",
  PURE_REWRITE_RULE [GSYM int_ge] INT_LE_REDUCE);

val INT_EQ_CALCULATE = save_thm(
  "INT_EQ_CALCULATE",
  LIST_CONJ [INT_INJ, INT_EQ_NEG, int_eq_calculate]);
val INT_EQ_REDUCE = store_thm(
  "INT_EQ_REDUCE",
  Term`!n m. ((0i = 0i) = T) /\
             ((0i = &(NUMERAL (BIT1 n))) = F) /\
             ((0i = &(NUMERAL (BIT2 n))) = F) /\
             ((0i = ~&(NUMERAL (BIT1 n))) = F) /\
             ((0i = ~&(NUMERAL (BIT2 n))) = F) /\
             ((&(NUMERAL (BIT1 n)) = 0i) = F) /\
             ((&(NUMERAL (BIT2 n)) = 0i) = F) /\
             ((~&(NUMERAL (BIT1 n)) = 0i) = F) /\
             ((~&(NUMERAL (BIT2 n)) = 0i) = F) /\
             ((&(NUMERAL n) :int = &(NUMERAL m)) = (n = m)) /\
             ((&(NUMERAL (BIT1 n)) = ~&(NUMERAL m)) = F) /\
             ((&(NUMERAL (BIT2 n)) = ~&(NUMERAL m)) = F) /\
             ((~&(NUMERAL (BIT1 n)) = &(NUMERAL m)) = F) /\
             ((~&(NUMERAL (BIT2 n)) = &(NUMERAL m)) = F) /\
             ((~&(NUMERAL n) :int = ~&(NUMERAL m)) = (n = m))`,
  SIMP_TAC bool_ss [INT_EQ_CALCULATE, NUMERAL_DEF, BIT1,
                    BIT2] THEN
  CONV_TAC ARITH_CONV);

val INT_DIVIDES_REDUCE = store_thm(
  "INT_DIVIDES_REDUCE",
  Term`!n m p:int.
          (0 int_divides 0 = T) /\
          (0 int_divides &(NUMERAL (BIT1 n)) = F) /\
          (0 int_divides &(NUMERAL (BIT2 n)) = F) /\
          (p int_divides 0 = T) /\
          (&(NUMERAL (BIT1 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (&(NUMERAL (BIT2 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
          (&(NUMERAL (BIT1 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (&(NUMERAL (BIT2 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
          (~&(NUMERAL (BIT1 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (~&(NUMERAL (BIT2 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
          (~&(NUMERAL (BIT1 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (~&(NUMERAL (BIT2 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0))`,
  SIMP_TAC bool_ss [INT_DIVIDES_NEG] THEN
  SIMP_TAC bool_ss [INT_DIVIDES_MOD0, INT_EQ_CALCULATE,
                    INT_MOD_REDUCE] THEN
  SIMP_TAC bool_ss [NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, SUC_NOT] THEN
  PROVE_TAC [INT_MOD0]);

(*---------------------------------------------------------------------------*)
(* LEAST integer satisfying a predicate (may be undefined).                  *)
(*---------------------------------------------------------------------------*)

val LEAST_INT_DEF = new_definition ("LEAST_INT_DEF",
  ``LEAST_INT P = @i. P i /\ !j. j < i ==> ~P j``)

val _ = set_fixity "LEAST_INT" Binder

(*---------------------------------------------------------------------------*)

val _ = BasicProvers.export_rewrites
        ["INT_ADD_LID_UNIQ", "INT_ADD_LINV",
         "INT_ADD_RID_UNIQ", "INT_ADD_RINV",
         "INT_ADD_SUB", "INT_ADD_SUB2", "INT_DIVIDES_0",
         "INT_DIVIDES_1", "INT_DIVIDES_LADD", "INT_DIVIDES_LMUL",
         "INT_DIVIDES_LSUB", "INT_DIVIDES_MUL", "INT_DIVIDES_NEG",
         "INT_DIVIDES_RADD", "INT_DIVIDES_REFL", "INT_DIVIDES_RMUL",
         "INT_DIVIDES_RSUB", "INT_DIV", "INT_QUOT", "INT_DIV_1",
         "INT_QUOT_1", "INT_DIV_ID", "INT_QUOT_ID", "INT_DIV_NEG",
         "INT_QUOT_NEG", "INT_ENTIRE", "INT_EQ_CALCULATE",
         "INT_EQ_LADD", "INT_EQ_LMUL", "INT_EQ_RADD", "INT_EQ_LMUL",
         "INT_EXP", "INT_EXP_EQ0", "INT_INJ", "INT_LE", "INT_LE_ADD",
         "INT_LE_ADDL", "INT_LE_ADDR", "INT_LE_DOUBLE", "INT_LE_LADD",
         "INT_LE_MUL", "INT_LE_NEG", "INT_LE_NEGL", "INT_LE_NEGR",
         "INT_LE_RADD", "INT_LE_REFL", "INT_LE_SQUARE", "INT_LT_ADD",
         "INT_LT_ADDL", "INT_LT_ADDR", "INT_LT_CALCULATE",
         "INT_LT_IMP_LE", "INT_LT_LADD",
         "INT_LT_RADD", "INT_LT_REFL", "INT_MAX_NUM", "INT_MIN_NUM",
         "INT_MOD", "INT_REM", "INT_MOD0", "INT_REM0",
         "INT_MOD_COMMON_FACTOR", "INT_REM_COMMON_FACTOR",
         "INT_MOD_ID", "INT_REM_ID", "INT_MOD_NEG", "INT_REM_NEG",
         "INT_MUL", "INT_MUL_EQ_1", "INT_MUL_LID", "INT_MUL_LZERO",
         "INT_MUL_RZERO", "INT_NEGNEG", "INT_NEG_0",
         "INT_NEG_EQ0", "INT_NEG_GE0", "INT_NEG_GT0", "INT_NEG_LE0",
         "INT_NEG_LT0", "INT_NEG_MUL2", "INT_NEG_SAME_EQ",
         "INT_NEG_SUB", "INT_SUB_0", "INT_SUB_ADD", "INT_SUB_ADD2",
         "INT_SUB_LZERO", "INT_SUB_NEG2", "INT_SUB_REFL",
         "INT_SUB_RNEG", "INT_SUB_RZERO", "INT_SUB_SUB",
         "INT_SUB_SUB2", "NUM_OF_INT"]

val _ = adjoin_to_theory {sig_ps = NONE,
  struct_ps = SOME (fn ppstrm =>
   app (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
   ["val _ = TypeBase.write [TypeBasePure.mk_nondatatype_info",
    "  (``:int``, {nchotomy = SOME INT_NUM_CASES,",
    "              encode = NONE, size = NONE})];"])}

val _ = export_theory();

end
