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
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;

val _ = new_theory "integer";

(* interactive mode
  app load ["jrhUtils", "EquivType", "liteLib", "QLib",
        "SingleStep", "BasicProvers", "boolSimps", "pairSimps", "arithSimps",
        "numLib", "PairedDefinition"];
*)
open jrhUtils EquivType liteLib arithLib
     arithmeticTheory prim_recTheory numTheory
     simpLib numLib boolTheory liteLib PairedDefinition;

infix ++;

fun new_prim_rec_definition(s,tm) =
  Prim_rec.new_recursive_definition {
    name = s, rec_axiom = prim_recTheory.num_Axiom, def = tm
  };


val int_ss = boolSimps.bool_ss ++ arithSimps.ARITH_ss ++ pairSimps.PAIR_ss;

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
(* Theorems may be of the form |- ~ P or |- P, rather that equations, they  *)
(* will be transformed to |- P = F and |- P = T automatically if needed.    *)
(*                                                                          *)
(* Note that terms not cancelled will remain in their original order, but   *)
(* will be flattened to right-associated form.                              *)
(*--------------------------------------------------------------------------*)

fun CANCEL_CONV (assoc,sym,lcancelthms) tm =
  let val lcthms =
      map ((fn th => (assert (is_eq o concl)) th
	    handle _ => EQF_INTRO th
		handle _ => EQT_INTRO th) o SPEC_ALL) lcancelthms
      val [eqop, binop] =
	  map (rator o rator o lhs o snd o strip_forall o concl)
	  [hd lcthms, sym]
      fun strip_binop tm =
	  if (rator(rator tm) = binop handle _ => false) then
	      (strip_binop (rand(rator tm))) @ (strip_binop(rand tm))
	  else [tm]
      val mk_binop = ((curry mk_comb) o (curry mk_comb binop))
      val list_mk_binop = end_itlist mk_binop

      fun rmel i []     = []
	| rmel i (h::t) = if (i = h) then t else h::(rmel i t)

      val (_,[l1,r1]) = (assert (curry op= eqop) ## I) (strip_comb tm)
      val [l, r] = map strip_binop [l1, r1]
      val i = intersect l r
  in
      if i = [] then raise Fail ""
      else
	  let val itm = list_mk_binop i
	      val [l', r'] =
		  map (end_itlist (C (curry op o)) (map rmel i)) [l, r]
	      val [l2, r2] =
		  map (fn ts => mk_binop itm (list_mk_binop ts)
		       handle _ => itm) [l',r']
	      val [le, re] =
		  map (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq)[(l1,l2),(r1,r2)]
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

val tint_lt =
    new_infixr_definition
    ("tint_lt",
     Term `$tint_lt (x1,y1) (x2,y2) = (x1 + y2) < (x2 + y1)`,
     450);

(*--------------------------------------------------------------------------*)
(* Define the equivalence relation and prove it *is* one                    *)
(*--------------------------------------------------------------------------*)

val _ = print "Define equivalence relation over pairs of naturals\n"

val tint_eq =
    new_infixr_definition
    ("tint_eq",
     Term `$tint_eq (x1,y1) (x2,y2) = (x1 + y2 = x2 + y1)`,
     450);

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
     REPEAT GEN_PAIR_TAC
     THEN
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
  ONCE_REWRITE_TAC[AC(ADD_ASSOC,ADD_SYM)
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
	 INT_LT_LADD_IMP, INT_LT_MUL] =
	define_equivalence_type
	{name = "int", equiv = TINT_EQ_EQUIV,
	 defs = [mk_def ("int_0", Term `tint_0`,     "int_0", Prefix),
		 mk_def ("int_1", Term `tint_1`,     "int_1", Prefix),
		 mk_def ("int_neg",Term `tint_neg`,  "int_neg",   Prefix),
		 mk_def ("int_add",Term `$tint_add`, "int_add",   Infixl 500),
		 mk_def ("int_mul",Term `$tint_mul`, "int_mul",   Infixl 600),
		 mk_def ("int_lt",Term `$tint_lt`,   "int_lt",    Infixr 450)],

	 welldefs = [TINT_NEG_WELLDEF, TINT_LT_WELLDEF,
		     TINT_ADD_WELLDEF, TINT_MUL_WELLDEF],
	 old_thms = ([TINT_10] @
		     (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
		      [TINT_ADD_SYM, TINT_MUL_SYM, TINT_ADD_ASSOC,
		       TINT_MUL_ASSOC, TINT_LDISTRIB]) @
		     [TINT_ADD_LID, TINT_MUL_LID, TINT_ADD_LINV,
		      TINT_LT_TOTAL, TINT_LT_REFL, TINT_LT_TRANS,
		      TINT_LT_ADD, TINT_LT_MUL])}
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
;

val int_tybij = definition "int_tybij";

val _ = overload_on ("+", Term`$int_add`);
val _ = overload_on ("<", Term`$int_lt`);
val _ = overload_on ("*", Term`$int_mul`);


(* this is a slightly tricky case; we don't have to call overload_on
   on the boolean negation, but we're doing so to put it back at the
   top of the list of possible resolutions. *)

val bool_not = Term`$~`
val _ = overload_on ("~", Term`$int_neg`);
val _ = overload_on ("~", bool_not);



(*--------------------------------------------------------------------------*)
(* Define subtraction and the other orderings                               *)
(*--------------------------------------------------------------------------*)

val int_sub =
    new_infixl_definition("int_sub",
			 Term `$int_sub x y = x + ~y`,
			 500);
val _ = overload_on ("-",  Term`$int_sub`);

val int_le =
    new_infixr_definition("int_le",
			 Term `$int_le x y = ~(y<x:int)`,
			 450);
val _ = overload_on ("<=", Term`$int_le`);

val int_gt =
    new_infixr_definition("int_gt",
			 Term `$int_gt (x:int) y = y < x`,
			 450);
val _ = overload_on (">",  Term`$int_gt`);

val int_ge =
    new_infixr_definition("int_ge",
			 Term `$int_ge x y = y <= x:int`,
			 450);
val _ = overload_on (">=", Term`$int_ge`);

(*--------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism int_of_num:num->int.               *)
(*--------------------------------------------------------------------------*)

val int_of_num =
    new_prim_rec_definition
    ("int_of_num",
     Term `(int_of_num 0 = int_0) /\
           (int_of_num (SUC n) = (int_of_num n) + int_1)`);

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
(* Prove lots of boring field theorems                                      *)
(*--------------------------------------------------------------------------*)

val _ = print "Prove \"lots of boring field theorems\"\n";

(* already defined, but using the wrong term for 0 *)
val INT_ADD_LID =
    store_thm("INT_ADD_LID",
              Term`!x:int. 0 + x = x`,
              SIMP_TAC int_ss [GSYM INT_0, INT_ADD_LID]);

val INT_ADD_RID =
    store_thm("INT_ADD_RID",
	      Term `!x:int. x + 0 = x`,
	      SIMP_TAC int_ss [INT_ADD_SYM,INT_ADD_LID])

(* already defined, but using the wrong term for 0 *)
val INT_ADD_LINV =
    store_thm("INT_ADD_LINV",
              Term`!x. ~x + x = 0`,
              SIMP_TAC int_ss [GSYM INT_0, INT_ADD_LINV]);
val INT_ADD_RINV =
    store_thm("INT_ADD_RINV",
	      Term `!x. x + ~x = 0`,
	      SIMP_TAC int_ss [INT_ADD_SYM,INT_0,INT_ADD_LINV])

(* already defined, but using the wrong term for 1 *)
val INT_MUL_LID =
    store_thm("INT_MUL_LID",
              Term`!x:int. 1 * x = x`,
              SIMP_TAC int_ss [GSYM INT_1, INT_MUL_LID])
val INT_MUL_RID =
    store_thm("INT_MUL_RID",
	      Term `!x:int. x * 1 = x`,
	      SIMP_TAC int_ss [INT_MUL_SYM,GSYM INT_1,INT_MUL_LID])

val INT_RDISTRIB =
    store_thm("INT_RDISTRIB",
	      Term `!(x:int) y z. (x + y) * z = (x * z) + (y * z)`,
	      SIMP_TAC int_ss [INT_MUL_SYM,INT_LDISTRIB])

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
	      [AC(INT_ADD_ASSOC,INT_ADD_SYM)
	       (Term `(a + b) + (c + d) = (a + c) + (b + d:int)`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_RID,INT_0]);

val INT_MUL_LZERO =
    store_thm("INT_MUL_LZERO",
	      Term `!x:int. 0 * x = 0`,
	      GEN_TAC THEN SUBST1_TAC
	      (SYM(Q.SPECL [`0 * x`, `0 * x`] INT_ADD_LID_UNIQ))
	      THEN REWRITE_TAC[GSYM INT_RDISTRIB, INT_ADD_RID]);

val INT_MUL_RZERO
    = store_thm("INT_MUL_RZERO",
		Term `!x. x * 0i = 0`,
		GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
		SIMP_TAC int_ss [INT_MUL_LZERO]);

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
	      Term `0 <= 1`,
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
	      Term `!m n. &m:int + &n = &(m + n)`,
	      INDUCT_TAC THEN REWRITE_TAC[INT, ADD, INT_ADD_LID]
	      THEN
	      RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
	      CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));

val INT_MUL =
    store_thm("INT_MUL",
	      Term `!m n. &m:int * &n = &(m * n)`,
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
	      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
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
      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
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
	      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
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
	      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
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
  SingleStep.Induct THENL [
    SIMP_TAC int_ss [INT_NEG_0, INT_INJ, GSYM INT_NEG_EQ],
    SIMP_TAC int_ss [INT] THEN GEN_TAC THEN CONJ_TAC THENL [
      SIMP_TAC int_ss [GSYM INT_EQ_SUB_LADD, int_sub, GSYM INT_NEG_ADD] THEN
      ASM_SIMP_TAC int_ss [INT_ADD],
      SIMP_TAC int_ss [INT_NEG_ADD, GSYM INT_EQ_SUB_LADD, int_sub] THEN
      ASM_SIMP_TAC int_ss [INT_NEGNEG, INT_ADD]
    ]
  ]);

(*--------------------------------------------------------------------------*)
(* Some nasty hacking round to show that the positive integers are a copy   *)
(* of the natural numbers.                                                  *)
(*--------------------------------------------------------------------------*)

val _ = print "Proving +ve integers are a copy of natural numbers\n"

val INT_DECOMPOSE =
    store_thm("INT_DECOMPOSE",
	      Term `!i. ?m n. i = mk_int($tint_eq(m,n))`,
	      GEN_TAC THEN
	      MP_TAC(Q.SPEC `dest_int i` (CONJUNCT2 int_tybij)) THEN
	      REWRITE_TAC[CONJUNCT1 int_tybij] THEN BETA_TAC THEN
	      DISCH_THEN(X_CHOOSE_THEN (Term `x:num#num`) MP_TAC) THEN
	      DISCH_THEN(MP_TAC o AP_TERM (Term `mk_int`)) THEN
	      REWRITE_TAC[CONJUNCT1 int_tybij] THEN
	      DISCH_THEN SUBST1_TAC THEN
	      MAP_EVERY Q.EXISTS_TAC [`FST (x:num#num)`,`SND (x:num#num)`] THEN
	      SIMP_TAC int_ss []);

val DEST_MK_EQCLASS =
    store_thm("DEST_MK_EQCLASS",
	      Term `!v. dest_int (mk_int ($tint_eq v)) = $tint_eq v`,
	      GEN_TAC THEN REWRITE_TAC[GSYM int_tybij] THEN
	      BETA_TAC THEN EXISTS_TAC (Term `v:num#num`) THEN REFL_TAC);

val REP_EQCLASS =
    store_thm("REP_EQCLASS",
	      Term `!v. $@($tint_eq v) tint_eq v`,
	      GEN_TAC THEN ONCE_REWRITE_TAC[TINT_EQ_SYM] THEN
	      MATCH_MP_TAC SELECT_AX THEN
	      EXISTS_TAC (Term (`v:num#num`)) THEN
	      MATCH_ACCEPT_TAC TINT_EQ_REFL);

val NUM_LEMMA =
    store_thm("NUM_LEMMA",
	      Term `!i. 0 <= i ==> ?n. i = mk_int($tint_eq (n,0n))`,
		  GEN_TAC THEN
		  X_CHOOSE_THEN (Term `m:num`)
		           (X_CHOOSE_THEN (Term `n:num`) SUBST1_TAC)
		  (SPEC (Term `i:int`) INT_DECOMPOSE) THEN
		  REWRITE_TAC[GSYM INT_0, definition "int_lt",
                              definition "int_0", int_le, tint_lt] THEN
		  REWRITE_TAC[DEST_MK_EQCLASS] THEN
		  DISCH_TAC THEN Q.EXISTS_TAC `m - n`
		  THEN AP_TERM_TAC THEN
		  REWRITE_TAC[GSYM TINT_EQ_EQUIV, tint_eq] THEN
		  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC SYM_CONV THEN
		  MATCH_MP_TAC SUB_ADD THEN POP_ASSUM MP_TAC THEN
		  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[GSYM NOT_LESS] THEN
		  DISCH_TAC THEN
		  SUBGOAL_THEN (Term `$@($tint_eq(m,n)) tint_eq (m,n) /\
				$@($tint_eq tint_0) tint_eq (1,1)`)
		  (fn th => REWRITE_TAC[MATCH_MP TINT_LT_WELLDEF th])
		  THENL [REWRITE_TAC[REP_EQCLASS, tint_0], ALL_TAC] THEN
		  REWRITE_TAC[tint_lt] THEN
		  GEN_REWRITE_TAC RAND_CONV empty_rewrites [ADD_SYM] THEN
		  ASM_REWRITE_TAC[LESS_MONO_ADD_EQ]);

val NUM_DECOMPOSE =
    store_thm("NUM_DECOMPOSE",
	      Term `!n. &n = mk_int($tint_eq (n,0))`,
	      INDUCT_TAC THEN REWRITE_TAC[int_of_num, definition "int_0",
					  tint_0] THENL
	      [AP_TERM_TAC THEN REWRITE_TAC[GSYM TINT_EQ_EQUIV,
					    tint_eq, ADD_CLAUSES],
	       ASM_REWRITE_TAC[definition "int_1",definition"int_add",tint_1]
	       THEN
	       AP_TERM_TAC THEN REWRITE_TAC[GSYM TINT_EQ_EQUIV,
					    DEST_MK_EQCLASS] THEN
	       REWRITE_TAC[TINT_EQ_EQUIV] THEN
	       SUBGOAL_THEN (Term `$@($tint_eq(n,0)) tint_eq (n,0) /\
			     $@($tint_eq(1 + 1,1)) tint_eq (1 + 1,1)`)
	       (fn th => REWRITE_TAC[REWRITE_RULE[TINT_EQ_EQUIV]
				     (MATCH_MP TINT_ADD_WELLDEF th)])
	       THENL [REWRITE_TAC[REP_EQCLASS, tint_0], ALL_TAC] THEN
	       REWRITE_TAC[tint_add, GSYM TINT_EQ_EQUIV, tint_eq] THEN
	       REWRITE_TAC[num_CONV (Term `1n`), ADD_CLAUSES]]);

val NUM_POSINT =
    store_thm("NUM_POSINT",
	      Term `!i. 0 <= i ==> ?!n. i = &n`,
		  GEN_TAC THEN DISCH_TAC THEN
		  CONV_TAC EXISTS_UNIQUE_CONV THEN
		  CONJ_TAC THENL
		  [ALL_TAC,
		   REPEAT GEN_TAC THEN
		   GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM INT_INJ] THEN
		   DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
		   REFL_TAC] THEN
		  POP_ASSUM
		  (fn th => X_CHOOSE_THEN (Term `n:num`) SUBST1_TAC
		                   (MATCH_MP NUM_LEMMA th)) THEN
		  EXISTS_TAC (Term `n:num`) THEN REWRITE_TAC[NUM_DECOMPOSE]);

open SingleStep BasicProvers

val NUM_POSINT_EXISTS = store_thm(
  "NUM_POSINT_EXISTS",
  Term`!i. 0 <= i ==> ?n. i = &n`,
  PROVE_TAC [SIMP_RULE bool_ss [EXISTS_UNIQUE_DEF] NUM_POSINT]);

val NUM_NEGINT_EXISTS = store_thm(
  "NUM_NEGINT_EXISTS",
  Term`!i. i <= 0 ==> ?n. i = ~&n`,
  PROVE_TAC [NUM_POSINT_EXISTS, INT_NEG_LE0, INT_NEG_EQ]);

open boolSimps
infix 8 by

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

(* ------------------------------------------------------------------------ *)
(* More random theorems about "stuff"                                       *)
(* ------------------------------------------------------------------------ *)

val INT_MUL_EQ_1 = store_thm(
  "INT_MUL_EQ_1",
  ``!x y. (x * y = 1) = (x = 1) /\ (y = 1) \/ (x = ~1) /\ (y = ~1)``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `x` STRIP_ASSUME_TAC INT_NUM_CASES THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC (bool_ss ++ arithSimps.ARITH_ss) [INT_MUL_LZERO, INT_INJ,
                                             int_eq_calculate] THEN
  Q.SPEC_THEN `y` STRIP_ASSUME_TAC INT_NUM_CASES THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC (bool_ss ++ arithSimps.ARITH_ss) [
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


(*----------------------------------------------------------------------*)
(* Define division                                                      *)
(*----------------------------------------------------------------------*)

val _ = print "Integer division\n"

val int_div = new_definition(
  "int_div",
  Term`int_div x y =
         if y = 0i then ARB x
         else
           if 0 <= x then if 0 < y then &(Num(x) DIV Num(y))
                          else ~(& (Num(x) DIV Num(~y)))
           else           if 0 < y then ~& (Num(~x) DIV Num(y))
                          else & (Num(~x) DIV Num(~y))`);

val _ = add_infix("/", 600, HOLgrammars.LEFT);
val _ = overload_on("/", Term`int_div`)

val INT_DIV = store_thm(
  "INT_DIV",
  Term`!n m. ~(m = 0) ==> (&n / &m = &(n DIV m))`,
  SIMP_TAC int_ss [int_div, INT_LE, INT_LT, NUM_OF_INT, INT_INJ]);

val INT_DIV_NEG = store_thm(
  "INT_DIV_NEG",
  Term`!p q. ~(q = 0) ==> ((~p / q = ~(p / q)) /\ (p/~q = ~p/q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Cases_on `0 <= q` THENL [
    `?n. q = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `0 <= p` THENL [
      `?m. p = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_INJ, INT_LE]) THEN
      ASM_SIMP_TAC int_ss [int_div, INT_INJ, INT_LE, INT_LT,
                           INT_NEG_GE0, NUM_OF_INT, INT_NEGNEG, INT_NEG_EQ0,
                           INT_NEG_GT0, INT_NEG_0] THEN
      ASM_SIMP_TAC (int_ss ++ boolSimps.COND_elim_ss) [
        GSYM IMP_DISJ_THM, ZERO_DIV, INT_NEG_EQ0,
        INT_NEG_0, INT_NEG_EQ, INT_NEGNEG],
      `?m. p = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                  INT_LE_LT] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_GE0, INT_NOT_LE, INT_NEG_LT0,
                                    INT_LT, INT_LE, INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [int_div, INT_LT, INT_LE, INT_NEGNEG, INT_INJ,
                           NUM_OF_INT, INT_NEG_GE0, INT_NEG_EQ0,
                           INT_NEG_LE0, INT_NEG_GT0]
   ],
   `?n. q = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
   POP_ASSUM SUBST_ALL_TAC THEN
   Cases_on `0 <= p` THENL [
     `?m. p = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_LE, INT_NEG_EQ0, INT_NEG_GE0,
                                    INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [int_div, INT_NEGNEG, INT_LT, INT_LE, INT_INJ,
                           NUM_OF_INT, INT_NEG_EQ0, INT_NEG_GE0,
                           INT_NEG_GT0, INT_NEG_0, INT_NEG_LT0] THEN
      ASM_SIMP_TAC (int_ss ++ boolSimps.COND_elim_ss)
         [GSYM IMP_DISJ_THM, ZERO_DIV, INT_NEG_0],
      `?m. p = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                  INT_LE_LT] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_EQ0, INT_NEG_GE0, INT_INJ,
                                    INT_LE, NOT_LESS_EQUAL]) THEN
      ASM_SIMP_TAC int_ss [int_div, INT_LT, INT_LE, INT_NEGNEG, INT_INJ,
                           NUM_OF_INT, INT_NEG_GE0, INT_NEG_EQ0,
                           INT_NEG_LE0, INT_NEG_GT0, INT_NEG_LT0]
   ]
 ]);

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
    SIMP_TAC int_ss [INT_INJ, INT_EQ_NEG, INT_DIV_NEG, INT_DIV, ONE,
                     DIV_ONE]
  ]);

val INT_DIV_ID = store_thm(
  "INT_DIV_ID",
  Term`!p:int. ~(p = 0) ==> (p / p = 1)`,
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    (* p positive *)
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    ASM_SIMP_TAC int_ss [INT_INJ, INT_DIV, DIVMOD_ID, NOT_ZERO_LT_ZERO],
    (* p negative *)
    `?n. p = ~&n` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    ASM_SIMP_TAC int_ss [INT_DIV_NEG, INT_NEG_EQ0, INT_NEGNEG] THEN
    SIMP_TAC int_ss [INT_DIV, INT_INJ, DIVMOD_ID, NOT_ZERO_LT_ZERO]
  ]);

(*----------------------------------------------------------------------*)
(* Define the appropriate modulus function for int_div                  *)
(*----------------------------------------------------------------------*)

val _ = print "Integer modulus\n"

val int_mod = new_definition(
  "int_mod",
  Term`int_mod p q = if q = 0i then ARB p
                     else p - p / q * q`);

val _ = add_infix("%", 650, HOLgrammars.LEFT);
val _ = overload_on("%", Term`int_mod`);

val INT_DIVISION = store_thm(
  "INT_DIVISION",
  Term`!p. ~(p = 0) ==> !q. q = q / p * p + q % p`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC int_ss [int_mod, int_sub] THEN
  PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM, INT_ADD_ASSOC, int_sub]);

val INT_MOD = store_thm(
  "INT_MOD",
  Term`!n m. ~(m = 0) ==> (&n % &m = &(n MOD m))`,
  SIMP_TAC int_ss [int_mod, INT_INJ, INT_DIV, INT_MUL, INT_EQ_SUB_RADD,
                   INT_ADD, INT_INJ] THEN
  PROVE_TAC [ADD_COMM, DIVISION, NOT_ZERO_LT_ZERO]);

val INT_MOD_NEG = store_thm(
  "INT_MOD_NEG",
  Term`!p q. ~(q = 0) ==> (~p % q = ~(p % q)) /\ (p % ~q = p % q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Cases_on `0 <= p` THENL [
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `0 <= q` THENL [
      `?m. q = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [int_mod, INT_NEG_EQ0, INT_NEGNEG, INT_DIV, INT_INJ,
                           INT_DIV_NEG, GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                           int_sub, INT_NEG_ADD],
      `?m. q = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                  INT_LE_LT] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_EQ0, INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [int_mod, INT_NEG_EQ0, INT_NEGNEG, INT_DIV, INT_INJ,
                           INT_DIV_NEG, GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                           int_sub, INT_NEG_ADD]
    ],
    `?n. p = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `0 <= q` THENL [
      `?m. q = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [int_mod, INT_NEG_EQ0, INT_NEGNEG, INT_DIV, INT_INJ,
                           INT_DIV_NEG, GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                           int_sub, INT_NEG_ADD],
      `?m. q = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                  INT_LE_LT] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_EQ0, INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [int_mod, INT_NEG_EQ0, INT_NEGNEG, INT_DIV, INT_INJ,
                           INT_DIV_NEG, GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                           int_sub, INT_NEG_ADD]
    ]
  ]);

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
    SIMP_TAC int_ss [INT_MOD_NEG, INT_NEG_EQ0, INT_MOD, INT_INJ, ZERO_MOD]
  ]);

val INT_DIV_MUL_ID = store_thm(
  "INT_DIV_MUL_ID",
  Term`!p q. ~(q = 0) /\ (p % q = 0) ==> (p / q * q = p)`,
  REPEAT STRIP_TAC THEN
  `p = p/q * q + p % q` by PROVE_TAC [INT_DIVISION] THEN
  `p = p / q * q` by PROVE_TAC [INT_ADD_RID] THEN
  PROVE_TAC []);

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

val INT_ABS_DIV = store_thm(
  "INT_ABS_DIV",
  Term`!p q. ~(q = 0) ==> ABS ((p / q) * q) <= ABS p`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ0, GSYM INT_NEG_LMUL,
                       GSYM INT_NEG_RMUL, INT_NEG_MUL2, INT_MUL, INT_LE,
                       INT_DIV, INT_DIV_NEG, INT_ABS_NEG, INT_ABS_NUM] THEN
  PROVE_TAC [DIVISION, LESS_EQ_EXISTS, NOT_ZERO_LT_ZERO, ZERO_DIV]);

(* can now prove uniqueness of / and % *)
(* It's a worry that this proof is so long; there may well be a better one
   making use of INT_NUM_CASES, which I proved after proving this.
   Let sleeping proofs lie, that's my motto *)
val INT_DIV_UNIQUE = store_thm(
  "INT_DIV_UNIQUE",
  Term`!p q k.
          ABS (k * q) <= ABS p /\
          (?r. (p = k * q + r) /\ ABS r < ABS q) ==>
          (p / q = k)`,
  REPEAT STRIP_TAC THEN Q.SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN
    `?n. ABS r = &n` by PROVE_TAC [NUM_POSINT_EXISTS, INT_ABS_POS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_LT],
    ALL_TAC
  ] THEN
  Cases_on `0 <= p` THENL [
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `0 <= q` THENL [
      `?m. q = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [INT_DIV] THEN
      Q.SUBGOAL_THEN `0 <= k` ASSUME_TAC THENL [
        CCONTR_TAC THEN
        `?u. k = ~&u` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS,
                                    INT_LE_LT] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC int_ss [GSYM INT_NEG_LMUL, INT_MUL] THEN
        `r = &n + &(u * m)` by
             PROVE_TAC [INT_ADD_COMM, int_sub, INT_EQ_SUB_RADD] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_ADD, INT_LT, INT_NEG_GE0,
                              INT_LE] THEN
        `?v. u = SUC v` by PROVE_TAC [num_CASES] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC int_ss [MULT_CLAUSES],
        ALL_TAC
      ] THEN
      `?u. k = &u` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      SIMP_TAC int_ss [INT_INJ] THEN
      MATCH_MP_TAC DIV_UNIQUE THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_MUL, INT_ABS_NUM, INT_LE]) THEN
      Q.SUBGOAL_THEN `0 <= r` ASSUME_TAC THENL [
        CCONTR_TAC THEN
        `?v. r = ~&v` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                    INT_LE_LT] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        `n + v = u * m` by PROVE_TAC [INT_INJ, INT_ADD, int_sub,
                                      INT_EQ_SUB_RADD] THEN
        RULE_ASSUM_TAC
          (REWRITE_RULE [INT_NEG_GE0, INT_LE, NOT_LESS_EQUAL]) THEN
        ASM_SIMP_TAC int_ss [],
        ALL_TAC
      ] THEN
      `?v. r = &v` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_LT, INT_ADD, INT_INJ],
      (* q negative *)
      `?m. q = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                  INT_LE_LT] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_GE0, INT_LE, NOT_LESS_EQUAL,
                                    INT_NEG_EQ0, INT_INJ]) THEN
      ASM_SIMP_TAC int_ss [INT_DIV_NEG, INT_INJ] THEN
      Q.SUBGOAL_THEN `k <= 0` ASSUME_TAC THENL [
        SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
        `?u. k = &u` by PROVE_TAC [NUM_POSINT_EXISTS, INT_NOT_LT,
                                   INT_LE_LT] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_LT, NOT_LESS,
                                      GSYM INT_NEG_RMUL, INT_ABS_NUM,
                                      INT_ABS_NEG, INT_MUL, INT_LE]) THEN
        `r = &n + &(u * m)` by PROVE_TAC [INT_ADD_COMM, int_sub,
                                          INT_EQ_SUB_RADD] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC
          (REWRITE_RULE [INT_ADD, INT_ABS_NUM, INT_LT, INT_INJ,
                         NOT_LESS_EQUAL]) THEN
        `?u'. u = SUC u'` by PROVE_TAC [num_CASES, NOT_ZERO_LT_ZERO] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC int_ss [MULT_CLAUSES],
        (* k <= 0 *)
        `?u. k = ~&u` by PROVE_TAC [NUM_NEGINT_EXISTS] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        SIMP_TAC int_ss [INT_NEG_MUL2, INT_MUL, INT_EQ_NEG] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_MUL2, INT_MUL, INT_NEG_LE0,
                                      INT_ABS_NUM, INT_LE, INT_ABS_NEG]) THEN
        Q.SUBGOAL_THEN `0 <= r` (Q.X_CHOOSE_THEN `v` SUBST_ALL_TAC o
                                 MATCH_MP NUM_POSINT_EXISTS)
        THENL [
          SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [INT_NOT_LE]) THEN
          `?v. r = ~&v` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_LE_LT] THEN
          POP_ASSUM SUBST_ALL_TAC THEN
          `n + v = u * m` by PROVE_TAC [INT_INJ, int_sub, INT_EQ_SUB_RADD,
                                        INT_ADD] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_LT0, INT_LT]) THEN
          ASM_SIMP_TAC int_ss [],
          ALL_TAC
        ] THEN
        ASM_SIMP_TAC int_ss [INT_DIV, INT_ADD, INT_INJ] THEN
        MATCH_MP_TAC DIV_UNIQUE THEN
        Q.EXISTS_TAC `v` THEN
        FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_LT]
      ]
    ],
    (* p negative *)
    `?n. p = ~(&n)` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS,
                                  INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `0 <= q` THENL [
      `?m. q = &m` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_GE0, INT_LE, INT_LT, INT_ABS_NUM,
                                    INT_ABS_NEG]) THEN
      Q.SUBGOAL_THEN `k <= 0` STRIP_ASSUME_TAC
      THENL [
        SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
        `?u. k = &u` by PROVE_TAC [NUM_POSINT_EXISTS, INT_NOT_LE,
                                   INT_LE_LT] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_MUL, INT_ABS_NUM, INT_LE, INT_LT,
                                      INT_INJ, NOT_LESS_EQUAL]) THEN
        `r = ~&n - &(u * m)` by PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM] THEN
        POP_ASSUM (fn th =>
          `r = ~(&n + &(u * m))` by PROVE_TAC [th, int_sub, INT_NEG_ADD]) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_ABS_NEG, INT_ADD, INT_ABS_NUM,
                                      INT_LT]) THEN
        `?u'. u = SUC u'` by PROVE_TAC [num_CASES, NOT_LESS_EQUAL,
                                        NOT_ZERO_LT_ZERO] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC int_ss [MULT_CLAUSES],
        ALL_TAC
      ] THEN
      `?u. k = ~&u` by PROVE_TAC [NUM_NEGINT_EXISTS] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_LE0, INT_LE, INT_INJ,
                                    GSYM INT_NEG_LMUL, INT_ABS_NEG,
                                    INT_ABS_NUM, INT_MUL]) THEN
      ASM_SIMP_TAC int_ss [INT_DIV_NEG, INT_INJ, INT_EQ_NEG, INT_DIV] THEN
      MATCH_MP_TAC DIV_UNIQUE THEN
      Q.SUBGOAL_THEN `r <= 0` (Q.X_CHOOSE_THEN `v` SUBST_ALL_TAC o
                               MATCH_MP NUM_NEGINT_EXISTS)
      THENL [
        SPOSE_NOT_THEN ASSUME_TAC THEN
        `?v. r = &v` by PROVE_TAC [INT_NOT_LE, INT_LE_LT,
                                   NUM_POSINT_EXISTS] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        `~&(u * m) = ~&n - &v` by
          PROVE_TAC [INT_ADD_COMM, INT_EQ_SUB_LADD] THEN
        POP_ASSUM (fn th =>
          `&(u * m) = &n + &v` by PROVE_TAC [th, int_sub, INT_NEG_ADD,
                                             INT_EQ_NEG]) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_ADD, INT_INJ, INT_LE,
                                      NOT_LESS_EQUAL]) THEN
        ASM_SIMP_TAC int_ss [],
        ALL_TAC
      ] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_INJ, INT_EQ_NEG, INT_ABS_NEG,
                                    INT_ABS_NUM, INT_LT, GSYM INT_NEG_ADD,
                                    INT_ADD]) THEN
      PROVE_TAC [],
      (* q also negative *)
      `?m. q = ~&m` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_LE_LT,
                                  INT_NOT_LE] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_GE0, INT_NEG_EQ0, INT_ABS_NEG,
                                    INT_ABS_NUM, INT_LE, INT_INJ,
                                    NOT_LESS_EQUAL]) THEN
      ASM_SIMP_TAC int_ss [INT_DIV_NEG, INT_INJ, INT_NEGNEG, INT_DIV] THEN
      Q.SUBGOAL_THEN `0 <= k` (Q.X_CHOOSE_THEN `u` SUBST_ALL_TAC o
                               MATCH_MP NUM_POSINT_EXISTS)
      THENL [
        SPOSE_NOT_THEN ASSUME_TAC THEN
        `?u. k = ~&u` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE,
                                    INT_LE_LT] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_GE0, INT_LE, INT_NEG_MUL2,
                                      NOT_LESS_EQUAL, INT_MUL,
                                      INT_ABS_NUM]) THEN
        `r = ~&n - &(u * m)` by PROVE_TAC [INT_ADD_COMM, INT_EQ_SUB_LADD] THEN
        POP_ASSUM (fn th =>
          `r = ~(&n + &(u * m))` by PROVE_TAC [th, int_sub, INT_NEG_ADD]) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_ADD, INT_ABS_NUM, INT_ABS_NEG,
                                      INT_LT]) THEN
        `?u'. u = SUC u'` by PROVE_TAC [num_CASES, NOT_ZERO_LT_ZERO] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [MULT_CLAUSES]) THEN
        ASM_SIMP_TAC int_ss [],
        ALL_TAC
      ] THEN SIMP_TAC int_ss [INT_INJ] THEN
      MATCH_MP_TAC DIV_UNIQUE THEN
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM INT_NEG_RMUL, INT_ABS_NEG,
                                    INT_ABS_NUM, INT_LE, INT_MUL]) THEN
      Q.SUBGOAL_THEN `r <= 0` (Q.X_CHOOSE_THEN `v` SUBST_ALL_TAC o
                               MATCH_MP NUM_NEGINT_EXISTS)
      THENL [
        SPOSE_NOT_THEN ASSUME_TAC THEN
        `?v. r = &v` by PROVE_TAC [INT_NOT_LE, INT_LE_LT,
                                   NUM_POSINT_EXISTS] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        `&v + &n = &(u * m)` by PROVE_TAC [INT_SUB_NEG2, INT_EQ_SUB_LADD,
                                           INT_ADD_COMM] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INT_ADD, INT_INJ, INT_LE,
                                      NOT_LESS_EQUAL]) THEN
        ASM_SIMP_TAC int_ss [],
        ALL_TAC
      ] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM INT_NEG_ADD, INT_EQ_NEG, INT_ADD,
                                    INT_INJ, INT_ABS_NUM, INT_ABS_NEG,
                                    INT_LT]) THEN
      PROVE_TAC []
    ]
  ]);

val INT_MOD_UNIQUE = store_thm(
  "INT_MOD_UNIQUE",
  Term`!p q r.
          ABS r < ABS q /\ (?k. ABS (k * q) <= ABS p /\ (p = k * q + r)) ==>
          (p % q = r)`,
  REPEAT STRIP_TAC THEN SIMP_TAC int_ss [int_mod] THEN
  Q.SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN
    `?n. ABS r = &n` by PROVE_TAC [NUM_POSINT_EXISTS, INT_ABS_POS] THEN
    FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_LT],
    ALL_TAC
  ] THEN POP_ASSUM (fn th => SIMP_TAC int_ss [th] THEN ASSUME_TAC th) THEN
  `p / q = k` by PROVE_TAC [INT_DIV_UNIQUE] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM]);

val INT_MOD_ID = store_thm(
  "INT_MOD_ID",
  Term`!p. ~(p = 0) ==> (p % p = 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN CONJ_TAC THENL [
    PROVE_TAC [INT_LE_LT, INT_ABS_POS, INT_ABS_EQ0, INT_ABS_NUM],
    Q.EXISTS_TAC `1` THEN REWRITE_TAC [INT_MUL_LID, INT_ADD_RID, INT_LE_REFL]
  ]);

val INT_ABS_MOD_LT = store_thm(
  "INT_ABS_MOD_LT",
  Term`!p q. ~(q = 0) ==> ABS (p % q) < ABS q`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ0, INT_MOD_NEG, INT_ABS_NUM,
                       INT_ABS_NEG, INT_MOD, INT_LT, DIVISION]);

val INT_MOD_COMMON_FACTOR = store_thm(
  "INT_MOD_COMMON_FACTOR",
  Term`!p. ~(p = 0) ==> !q. (q * p) % p = 0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ADD_RID] THEN
  PROVE_TAC [INT_ABS_NUM, INT_LE_LT, INT_ABS_EQ0, INT_ABS_POS]);

val INT_MOD_EQ0 = store_thm(
  "INT_MOD_EQ0",
  Term`!q. ~(q = 0) ==> !p. (p % q = 0) = (?k. p = k * q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.PAT_ASSUM `~(q = 0)` (ASSUME_TAC o Q.SPEC `p` o
                            MATCH_MP INT_DIVISION) THEN
    PROVE_TAC [INT_ADD_RID],
    MATCH_MP_TAC INT_MOD_UNIQUE THEN CONJ_TAC THENL [
      PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS],
      PROVE_TAC [INT_ADD_RID, INT_LE_REFL]
    ]
  ]);

val INT_MUL_DIV = store_thm(
  "INT_MUL_DIV",
  Term`!p:int q k. ~(q = 0) /\ (p % q = 0) ==>
                   ((k * p) / q = k * (p / q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQUE THEN
  `?m. p = m * q` by PROVE_TAC [INT_MOD_EQ0] THEN
  Q.SUBGOAL_THEN `p / q = m` ASSUME_TAC THENL [
    MATCH_MP_TAC INT_DIV_UNIQUE THEN CONJ_TAC THENL [
      PROVE_TAC [INT_LE_REFL],
      Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC int_ss [INT_ADD_RID] THEN
      PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS]
    ],
    POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
    CONJ_TAC THENL [
      PROVE_TAC [INT_MUL_ASSOC, INT_LE_REFL],
      Q.EXISTS_TAC `0` THEN SIMP_TAC int_ss [INT_MUL_ASSOC, INT_ADD_RID] THEN
      PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS]
    ]
  ]);

(*----------------------------------------------------------------------*)
(* Define divisibility                                                  *)
(*----------------------------------------------------------------------*)

val _ = print "Facts about integer divisibility\n";
val INT_DIVIDES = new_definition (
  "INT_DIVIDES",
  Term`int_divides p q = ?m:int. m * p = q`);
val _ = set_fixity ("int_divides", Infixr 450);

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
val _ = set_fixity ("int_exp", Infixr 700);

val _ = add_infix("**", 700, HOLgrammars.RIGHT);
val _ = overload_on ("**", Term`$EXP`);
val _ = overload_on ("**", Term`$int_exp`);

val INT_EXP = store_thm(
  "INT_EXP",
  Term`!n m. &n ** m = &(n ** m)`,
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
  SIMP_TAC (bool_ss ++ COND_elim_ss) [INT_MIN, MIN_DEF, INT_LT]);

val INT_MAX_NUM = store_thm(
  "INT_MAX_NUM",
  ``!m n. int_max (&m) (&n) = &(MAX m n)``,
  SIMP_TAC (bool_ss ++ COND_elim_ss) [INT_MAX, MAX_DEF, INT_LT]);

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
          (&(NUMERAL n) + &(NUMERAL m):int = &(NUMERAL (iZ (n + m)))) /\
          (&(NUMERAL n) + ~&(NUMERAL m):int =
             if m <= n then &(NUMERAL (n - m)) else ~&(NUMERAL (m - n))) /\
          (~&(NUMERAL n) + &(NUMERAL m):int =
             if n <= m then &(NUMERAL (m - n)) else ~&(NUMERAL (n - m))) /\
          (~&(NUMERAL n) + ~&(NUMERAL m):int = ~&(NUMERAL (iZ (n + m))))`,
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

val INT_DIV_REDUCE = store_thm(
  "INT_DIV_REDUCE",
  Term`!m n.
         (0i / &(NUMERAL (NUMERAL_BIT1 n)) = 0i) /\
         (0i / &(NUMERAL (NUMERAL_BIT2 n)) = 0i) /\
         (&(NUMERAL m) / &(NUMERAL (NUMERAL_BIT1 n)) =
            &(NUMERAL m DIV NUMERAL (NUMERAL_BIT1 n))) /\
         (&(NUMERAL m) / &(NUMERAL (NUMERAL_BIT2 n)) =
            &(NUMERAL m DIV NUMERAL (NUMERAL_BIT2 n))) /\
         (~&(NUMERAL m) / &(NUMERAL (NUMERAL_BIT1 n)) =
            ~&(NUMERAL m DIV NUMERAL (NUMERAL_BIT1 n))) /\
         (~&(NUMERAL m) / &(NUMERAL (NUMERAL_BIT2 n)) =
            ~&(NUMERAL m DIV NUMERAL (NUMERAL_BIT2 n))) /\
         (&(NUMERAL m) / ~&(NUMERAL (NUMERAL_BIT1 n)) =
            ~&(NUMERAL m DIV NUMERAL (NUMERAL_BIT1 n))) /\
         (&(NUMERAL m) / ~&(NUMERAL (NUMERAL_BIT2 n)) =
            ~&(NUMERAL m DIV NUMERAL (NUMERAL_BIT2 n))) /\
         (~&(NUMERAL m) / ~&(NUMERAL (NUMERAL_BIT1 n)) =
            &(NUMERAL m DIV NUMERAL (NUMERAL_BIT1 n))) /\
         (~&(NUMERAL m) / ~&(NUMERAL (NUMERAL_BIT2 n)) =
            &(NUMERAL m DIV NUMERAL (NUMERAL_BIT2 n)))`,
  SIMP_TAC int_ss [INT_DIV, INT_DIV_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG,
                   NUMERAL_DEF, NUMERAL_BIT1, NUMERAL_BIT2, ZERO_DIV]);

val INT_MOD_CALCULATE = save_thm(
  "INT_MOD_CALCULATE",
  LIST_CONJ [INT_MOD, INT_MOD_NEG, INT_NEGNEG, INT_INJ, INT_NEG_EQ0]);

val INT_MOD_REDUCE = store_thm(
  "INT_MOD_REDUCE",
  Term`!m n. (0i % &(NUMERAL (NUMERAL_BIT1 n)) = 0i) /\
             (0i % &(NUMERAL (NUMERAL_BIT2 n)) = 0i) /\
             (&(NUMERAL m) % &(NUMERAL (NUMERAL_BIT1 n)) =
                &(NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n))) /\
             (&(NUMERAL m) % &(NUMERAL (NUMERAL_BIT2 n)) =
                &(NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n))) /\
             (~&(NUMERAL m) % &(NUMERAL (NUMERAL_BIT1 n)) =
                ~&(NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n))) /\
             (~&(NUMERAL m) % &(NUMERAL (NUMERAL_BIT2 n)) =
                ~&(NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n))) /\
             (&(NUMERAL m) % ~&(NUMERAL (NUMERAL_BIT1 n)) =
                &(NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n))) /\
             (&(NUMERAL m) % ~&(NUMERAL (NUMERAL_BIT2 n)) =
                &(NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n))) /\
             (~&(NUMERAL m) % ~&(NUMERAL (NUMERAL_BIT1 n)) =
                ~&(NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n))) /\
             (~&(NUMERAL m) % ~&(NUMERAL (NUMERAL_BIT2 n)) =
                ~&(NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n)))`,
  SIMP_TAC int_ss [INT_MOD_CALCULATE, NUMERAL_BIT1, NUMERAL_BIT2,
                   NUMERAL_DEF, ALT_ZERO, ZERO_MOD]);

val ODD_NB1 = prove(
  Term`!n. ODD(NUMERAL_BIT1 n)`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, ODD, ADD_CLAUSES, ODD_ADD]);
val EVEN_NB2 = prove(
  Term`!n. EVEN(NUMERAL_BIT2 n)`,
  SIMP_TAC bool_ss [NUMERAL_BIT2, ADD_CLAUSES, EVEN, EVEN_ADD]);

val INT_EXP_CALCULATE = store_thm(
  "INT_EXP_CALCULATE",
  Term`!p:int n m.
        (p ** 0 = 1) /\ (&n ** m = &(n EXP m)) /\
        (~&n ** NUMERAL (NUMERAL_BIT1 m) =
           ~&(NUMERAL (n EXP NUMERAL (NUMERAL_BIT1 m)))) /\
        (~&n ** NUMERAL (NUMERAL_BIT2 m) =
            &(NUMERAL (n EXP NUMERAL (NUMERAL_BIT2 m))))`,
  SIMP_TAC int_ss [INT_EXP, int_exp] THEN
  SIMP_TAC int_ss [NUMERAL_DEF, ODD_NB1, EVEN_NB2, INT_EXP_NEG]);

val INT_EXP_REDUCE = store_thm(
  "INT_EXP_REDUCE",
  Term`!n m p:int.
          (p ** 0 = 1) /\
          (&(NUMERAL n):int ** m = &(n EXP m)) /\
          (~&(NUMERAL n) ** NUMERAL (NUMERAL_BIT1 m) =
             ~&(NUMERAL (n EXP NUMERAL_BIT1 m))) /\
          (~&(NUMERAL n) ** NUMERAL (NUMERAL_BIT2 m) =
             &(NUMERAL (n EXP NUMERAL_BIT2 m)))`,
  SIMP_TAC int_ss [INT_EXP_CALCULATE, NUMERAL_DEF]);

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

val INT_LT_REDUCE = store_thm(
  "INT_LT_REDUCE",
  Term`!n m. (0i < &(NUMERAL (NUMERAL_BIT1 n)) = T) /\
             (0i < &(NUMERAL (NUMERAL_BIT2 n)) = T) /\
             (0i < 0i = F) /\
             (0i < ~&(NUMERAL n) = F) /\
             (&(NUMERAL n) < 0i = F) /\
             (~&(NUMERAL (NUMERAL_BIT1 n)) < 0i = T) /\
             (~&(NUMERAL (NUMERAL_BIT2 n)) < 0i = T) /\
             (&(NUMERAL n) :int < &(NUMERAL m) = n < m) /\
             (~&(NUMERAL (NUMERAL_BIT1 n)) < &(NUMERAL m) = T) /\
             (~&(NUMERAL (NUMERAL_BIT2 n)) < &(NUMERAL m) = T) /\
             (&(NUMERAL n) < ~&(NUMERAL m) = F) /\
             (~&(NUMERAL n) < ~&(NUMERAL m) = m < n)`,
  SIMP_TAC bool_ss [INT_LT_CALCULATE, NUMERAL_DEF, NUMERAL_BIT1,
                    NUMERAL_BIT2] THEN
  CONV_TAC ARITH_CONV);

val INT_LE_CALCULATE = save_thm("INT_LE_CALCULATE", INT_LE_LT);

val INT_LE_REDUCE = store_thm(
  "INT_LE_REDUCE",
  Term`!n m. (0i <= 0i = T) /\ (0i <= &(NUMERAL n) = T) /\
             (0i <= ~&(NUMERAL (NUMERAL_BIT1 n)) = F) /\
             (0i <= ~&(NUMERAL (NUMERAL_BIT2 n)) = F) /\
             (&(NUMERAL(NUMERAL_BIT1 n)) <= 0i = F) /\
             (&(NUMERAL(NUMERAL_BIT2 n)) <= 0i = F) /\
             (~&(NUMERAL(NUMERAL_BIT1 n)) <= 0i = T) /\
             (~&(NUMERAL(NUMERAL_BIT2 n)) <= 0i = T) /\
             (&(NUMERAL n):int <= &(NUMERAL m) = n <= m) /\
             (&(NUMERAL n) <= ~&(NUMERAL (NUMERAL_BIT1 m)) = F) /\
             (&(NUMERAL n) <= ~&(NUMERAL (NUMERAL_BIT2 m)) = F) /\
             (~&(NUMERAL n) <= &(NUMERAL m) = T) /\
             (~&(NUMERAL n) <= ~&(NUMERAL m) = m <= n)`,
  SIMP_TAC bool_ss [NUMERAL_DEF, INT_LE_CALCULATE, INT_LT_CALCULATE,
                    int_eq_calculate, INT_INJ, INT_EQ_NEG, NUMERAL_BIT1,
                    NUMERAL_BIT2] THEN
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
             ((0i = &(NUMERAL (NUMERAL_BIT1 n))) = F) /\
             ((0i = &(NUMERAL (NUMERAL_BIT2 n))) = F) /\
             ((0i = ~&(NUMERAL (NUMERAL_BIT1 n))) = F) /\
             ((0i = ~&(NUMERAL (NUMERAL_BIT2 n))) = F) /\
             ((&(NUMERAL (NUMERAL_BIT1 n)) = 0i) = F) /\
             ((&(NUMERAL (NUMERAL_BIT2 n)) = 0i) = F) /\
             ((~&(NUMERAL (NUMERAL_BIT1 n)) = 0i) = F) /\
             ((~&(NUMERAL (NUMERAL_BIT2 n)) = 0i) = F) /\
             ((&(NUMERAL n) :int = &(NUMERAL m)) = (n = m)) /\
             ((&(NUMERAL (NUMERAL_BIT1 n)) = ~&(NUMERAL m)) = F) /\
             ((&(NUMERAL (NUMERAL_BIT2 n)) = ~&(NUMERAL m)) = F) /\
             ((~&(NUMERAL (NUMERAL_BIT1 n)) = &(NUMERAL m)) = F) /\
             ((~&(NUMERAL (NUMERAL_BIT2 n)) = &(NUMERAL m)) = F) /\
             ((~&(NUMERAL n) :int = ~&(NUMERAL m)) = (n = m))`,
  SIMP_TAC bool_ss [INT_EQ_CALCULATE, NUMERAL_DEF, NUMERAL_BIT1,
                    NUMERAL_BIT2] THEN
  CONV_TAC ARITH_CONV);

val INT_DIVIDES_REDUCE = store_thm(
  "INT_DIVIDES_REDUCE",
  Term`!n m p:int.
          (0 int_divides 0 = T) /\
          (0 int_divides &(NUMERAL (NUMERAL_BIT1 n)) = F) /\
          (0 int_divides &(NUMERAL (NUMERAL_BIT2 n)) = F) /\
          (p int_divides 0 = T) /\
          (&(NUMERAL (NUMERAL_BIT1 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n) = 0)) /\
          (&(NUMERAL (NUMERAL_BIT2 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n) = 0)) /\
          (&(NUMERAL (NUMERAL_BIT1 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n) = 0)) /\
          (&(NUMERAL (NUMERAL_BIT2 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n) = 0)) /\
          (~&(NUMERAL (NUMERAL_BIT1 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n) = 0)) /\
          (~&(NUMERAL (NUMERAL_BIT2 n)) int_divides &(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n) = 0)) /\
          (~&(NUMERAL (NUMERAL_BIT1 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT1 n) = 0)) /\
          (~&(NUMERAL (NUMERAL_BIT2 n)) int_divides ~&(NUMERAL m) =
           (NUMERAL m MOD NUMERAL (NUMERAL_BIT2 n) = 0))`,
  SIMP_TAC bool_ss [INT_DIVIDES_MOD0, INT_EQ_CALCULATE,
                    INT_MOD_REDUCE] THEN
  SIMP_TAC int_ss [NUMERAL_DEF, NUMERAL_BIT1, NUMERAL_BIT2] THEN
  PROVE_TAC [INT_MOD0]);



(* val _ = Globals.show_numeral_types := true *)

(* more theorems *)
val int_cases = prove(
  Term`!x:int. (?n. x = &n) \/ (?n. ~(n = 0) /\ (x = ~&n))`,
  PROVE_TAC [INT_NUM_CASES]);

val INT_DISCRETE = store_thm(
  "INT_DISCRETE",
  Term`!x:int y. ~(x < y /\ y < x + 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `x` int_cases) THEN
  STRUCT_CASES_TAC (Q.SPEC `y` int_cases) THENL [
    REWRITE_TAC [INT_ADD, INT_LT, LESS_LESS_SUC, GSYM ADD1],
    REWRITE_TAC [INT_LT_CALCULATE],
    ASM_REWRITE_TAC [INT_LT_CALCULATE, INT_ADD_CALCULATE] THEN
    `?m. n = SUC m` by PROVE_TAC [num_CASES] THEN POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC [ONE, LESS_MONO_EQ, SUB_MONO_EQ, LESS_EQ_MONO, SUB_0] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC [INT_LT_CALCULATE, prim_recTheory.NOT_LESS_0],
    REWRITE_TAC [INT_LT_CALCULATE, INT_ADD_CALCULATE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_LT_CALCULATE] THEN
    ASM_SIMP_TAC int_ss []
  ]);

val _ = export_theory();

end
