(*==========================================================================*)
(* Theory of integers. (John Harrison)                                      *)
(*                                                                          *)
(* The integers are constructed as equivalence classes of pairs of integers *)
(* using the quotient type procedure.                                       *)
(*                                                                          *)
(* This theory was constructed for use in the HOL-ELLA system, using many of*)
(* the principles, and some of the code, used in the reals library. It is my*)
(* eventual intention to produce a more unified library of number systems.  *)
(*==========================================================================*)


open HolKernel Parse basicHol90Lib;

val _ = new_theory "integer";

open useful EquivType hol88Lib arithLib Psyntax
     arithmeticTheory prim_recTheory numTheory
     simpLib Num_conv Num_induct boolTheory liteLib;

infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infix ++;

val int_ss = boolSimps.bool_ss ++ arithSimps.ARITH_ss ++ pairSimps.PAIR_ss;
val DECIDE_TAC = CONV_TAC ARITH_CONV;

(*--------------------------------------------------------------------------*)
(* Required lemmas about the natural numbers - mostly to drive CANCEL_TAC   *)
(*--------------------------------------------------------------------------*)

val EQ_LADD = prove_thm("EQ_LADD",
			Term `!x y z. (x + y = x + z) = (y = z)`,
			DECIDE_TAC)


val EQ_ADDL = prove_thm("EQ_ADDL",
			Term `!x y. (x = x + y) = (y = 0)`,
			DECIDE_TAC)

val LT_LADD = prove_thm("LT_LADD",
			Term `!x y z. (x + y) < (x + z) = y < z`,
			DECIDE_TAC)

val LT_ADDL = prove_thm("LT_ADDL",
			Term `!x y. x < (x + y) = 0 < y`,
			DECIDE_TAC)

val LT_ADDR = prove_thm("LT_ADDR",
			Term `!x y. ~((x + y) < x)`,
			DECIDE_TAC)

val LT_ADD2 =
    prove_thm("LT_ADD2",
	      Term`!x1 x2 y1 y2. x1 < y1 /\ x2 < y2 ==> (x1 + x2) < (y1 + y2)`,
		  DECIDE_TAC)

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

fun failwith s = raise HOL_ERR{message=s,origin_structure="INT",
			       origin_function=""}

fun CANCEL_CONV (assoc,sym,lcancelthms) tm =
  let

      val lcthms =
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

val tint_eq =
    new_infixr_definition
    ("tint_eq",
     Term `$tint_eq (x1,y1) (x2,y2) = x1 + y2 = x2 + y1`,
     450);

val TINT_EQ_REFL =
    prove_thm("TINT_EQ_REFL",
	      Term `!x. x tint_eq x`,
	      GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]);

val TINT_EQ_SYM =
    prove_thm("TINT_EQ_SYM",
	      Term `!x y. x tint_eq y = y tint_eq x`,
	      REPEAT GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
	                          THEN DECIDE_TAC)

val TINT_EQ_TRANS =
    prove_thm("TINT_EQ_TRANS",
	      Term `!x y z. x tint_eq y /\ y tint_eq z ==> x tint_eq z`,
		  REPEAT GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
	                          THEN DECIDE_TAC)


val TINT_EQ_EQUIV = prove_thm("TINT_EQ_EQUIV",
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
    prove_thm("TINT_EQ_AP",
	      Term `!p q. (p = q) ==> p tint_eq q`,
		  REPEAT GEN_PAIR_TAC
		  THEN REWRITE_TAC[tint_eq,pairTheory.PAIR_EQ]
		  THEN DECIDE_TAC)

(*--------------------------------------------------------------------------*)
(* Prove the properties of representatives                                  *)
(*--------------------------------------------------------------------------*)

val TINT_10 =
    prove_thm("TINT_10",
	      Term `~(tint_1 tint_eq tint_0)`,
	      REWRITE_TAC[tint_1, tint_0, tint_eq]
	      THEN DECIDE_TAC)

val TINT_ADD_SYM =
    prove_thm("TINT_ADD_SYM",
	      Term `!x y. x tint_add y = y tint_add x`,
	      REPEAT GEN_PAIR_TAC
	      THEN REWRITE_TAC[tint_eq,tint_add,pairTheory.PAIR_EQ]
	      THEN DECIDE_TAC)

val TINT_MUL_SYM =
    prove_thm("TINT_MUL_SYM",
	      Term `!x y. x tint_mul y = y tint_mul x`,
	      REPEAT GEN_PAIR_TAC
	      THEN REWRITE_TAC[tint_eq,tint_mul,pairTheory.PAIR_EQ]
	      THEN SIMP_TAC int_ss [MULT_SYM])

val TINT_ADD_ASSOC =
    prove_thm
    ("TINT_ADD_ASSOC",
     Term `!x y z. x tint_add (y tint_add z) = (x tint_add y) tint_add z`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,pairTheory.PAIR_EQ,ADD_ASSOC])

val TINT_MUL_ASSOC =
    prove_thm
    ("TINT_MUL_ASSOC",
     Term `!x y z. x tint_mul (y tint_mul z) = (x tint_mul y) tint_mul z`,
     REPEAT GEN_PAIR_TAC
     THEN
     REWRITE_TAC[tint_mul, pairTheory.PAIR_EQ, LEFT_ADD_DISTRIB,
		 RIGHT_ADD_DISTRIB]
     THEN
     SIMP_TAC int_ss [MULT_ASSOC]);

val TINT_LDISTRIB =
    prove_thm
    ("TINT_LDISTRIB",
     Term `!x y z. x tint_mul (y tint_add z) =
     (x tint_mul y) tint_add (x tint_mul z)`,
     REPEAT GEN_PAIR_TAC
     THEN
     REWRITE_TAC[tint_mul, tint_add,pairTheory.PAIR_EQ, LEFT_ADD_DISTRIB]
     THEN CANCEL_TAC);

val TINT_ADD_LID =
    prove_thm
    ("TINT_ADD_LID",
     Term `!x. (tint_0 tint_add x) tint_eq x`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,tint_0,tint_eq]
     THEN DECIDE_TAC);

val TINT_MUL_LID =
    prove_thm
    ("TINT_MUL_LID",
     Term `!x. (tint_1 tint_mul x) tint_eq x`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_mul,tint_1,tint_eq]
     THEN DECIDE_TAC)


val TINT_ADD_LINV =
    prove_thm
    ("TINT_ADD_LINV",
     Term `!x. ((tint_neg x) tint_add x) tint_eq tint_0`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,tint_0,tint_eq,tint_neg]
     THEN DECIDE_TAC)

val TINT_LT_TOTAL =
    prove_thm
    ("TINT_LT_TOTAL",
     Term `!x y. x tint_eq y \/ x tint_lt y \/ y tint_lt x`,
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_lt,tint_eq]
     THEN DECIDE_TAC)

val TINT_LT_REFL =
    prove_thm("TINT_LT_REFL",
	      Term `!x. ~(x tint_lt x)`,
	      REPEAT GEN_PAIR_TAC
	      THEN REWRITE_TAC[tint_lt]
	      THEN DECIDE_TAC)

fun unfold_dec l =  REPEAT GEN_PAIR_TAC THEN REWRITE_TAC l THEN DECIDE_TAC;

val TINT_LT_TRANS =
    prove_thm
    ("TINT_LT_TRANS",
     Term `!x y z. x tint_lt y /\ y tint_lt z ==> x tint_lt z`,
     unfold_dec[tint_lt])


val TINT_LT_ADD =
    prove_thm
    ("TINT_LT_ADD",
     Term `!x y z. (y tint_lt z) ==> (x tint_add y) tint_lt (x tint_add z)`,
     unfold_dec[tint_lt,tint_add])

val TINT_LT_MUL =
    prove_thm
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
    prove_thm
    ("TINT_NEG_WELLDEF",
     Term `!x1 x2. x1 tint_eq x2 ==> (tint_neg x1) tint_eq (tint_neg x2)`,
     unfold_dec[tint_eq,tint_neg])

val TINT_ADD_WELLDEFR =
    prove_thm
    ("TINT_ADD_WELLDEFR",
     Term`!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_add y) tint_eq (x2 tint_add y)`,
     unfold_dec[tint_eq,tint_add])

val TINT_ADD_WELLDEF =
    prove_thm
    ("TINT_ADD_WELLDEF",
     Term `!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
	 (x1 tint_add y1) tint_eq (x2 tint_add y2)`,
     unfold_dec[tint_eq,tint_add])

val TINT_MUL_WELLDEFR =
    prove_thm
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
    prove_thm
    ("TINT_MUL_WELLDEF",
     Term `!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
	 (x1 tint_mul y1) tint_eq (x2 tint_mul y2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TINT_EQ_TRANS THEN EXISTS_TAC (Term `x1 tint_mul y2`) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TINT_MUL_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TINT_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);

val TINT_LT_WELLDEFR =
    prove_thm
    ("TINT_LT_WELLDEFR",
     Term `!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_lt y = x2 tint_lt y)`,
     unfold_dec[tint_eq,tint_lt])

val TINT_LT_WELLDEFL =
    prove_thm
    ("TINT_LT_WELLDEFL",
     Term `!x y1 y2. y1 tint_eq y2 ==> (x tint_lt y1 = x tint_lt y2)`,
     unfold_dec[tint_eq,tint_lt])

val TINT_LT_WELLDEF =
    prove_thm
    ("TINT_LT_WELLDEF",
     Term `!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
	 (x1 tint_lt y1 = x2 tint_lt y2)`,
     unfold_dec[tint_eq,tint_lt])

(*--------------------------------------------------------------------------*)
(* Now define the functions over the equivalence classes                    *)
(*--------------------------------------------------------------------------*)


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
		 mk_def ("int_neg",Term `tint_neg`,  "--",    Prefix),
		 mk_def ("int_add",Term `$tint_add`, "+_",    Infixl 500),
		 mk_def ("int_mul",Term `$tint_mul`, "*_",    Infixl 600),
		 mk_def ("int_lt",Term `$tint_lt`,   "<_",    Infixr 450)],

	 welldefs = [TINT_NEG_WELLDEF, TINT_LT_WELLDEF,
		     TINT_ADD_WELLDEF, TINT_MUL_WELLDEF],
	 old_thms = ([TINT_10] @
		     (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
		      [TINT_ADD_SYM, TINT_MUL_SYM, TINT_ADD_ASSOC,
		       TINT_MUL_ASSOC, TINT_LDISTRIB]) @
		     [TINT_ADD_LID, TINT_MUL_LID, TINT_ADD_LINV,
		      TINT_LT_TOTAL, TINT_LT_REFL, TINT_LT_TRANS,
		      TINT_LT_ADD, TINT_LT_MUL])}
end

(* Is this right ???
   WAS: val int_tybij = definition "-" "int_tybij";*)
val int_tybij = definition "int_tybij";

val natplus = Term`$+`;
val _ = allow_for_overloading_on ("+", Type`:'a -> 'a -> 'a`);
val _ = overload_on("+", natplus);
val _ = overload_on ("+", Term`$+_`);

val natless = Term`$<`;
val _ = allow_for_overloading_on ("<", Type`:'a -> 'a -> bool`);
val _ = overload_on ("<", natless);
val _ = overload_on ("<", Term`$<_`);

val bool_not = Term`$~`
val _ = allow_for_overloading_on ("~", Type`:'a -> 'a`);
val _ = overload_on ("~", Term`$--`);
val _ = overload_on ("~", bool_not);

val natmult = Term`$*`;
val _ = allow_for_overloading_on ("*", Type`:'a -> 'a -> 'a`);
val _ = overload_on ("*", Term`$*_`);
val _ = overload_on ("*", natmult);


(*--------------------------------------------------------------------------*)
(* Define subtraction and the other orderings                               *)
(*--------------------------------------------------------------------------*)

val int_sub =
    new_infixl_definition("int_sub",
			 Term `$-_ x y = x + (-- y)`,
			 500);

val natsub = Term`$-`;
val _ = allow_for_overloading_on ("-", Type`:'a -> 'a -> 'a`);
val _ = overload_on("-", natsub);
val _ = overload_on("-", Term`$-_`);

val int_le =
    new_infixr_definition("int_le",
			 Term `$<=_ x y = ~(y <_ x)`,
			 450);

val natlte = Term`$<=`;
val _ = allow_for_overloading_on ("<=", Type`:'a -> 'a -> bool`);
val _ = overload_on ("<=", natlte);
val _ = overload_on ("<=", Term`$<=_`);

val int_gt =
    new_infixr_definition("int_gt",
			 Term `$>_ (x:int) y = y < x`,
			 450);
val natgt = Term`$>`;
val _ = allow_for_overloading_on (">", Type`:'a -> 'a -> bool`);
val _ = overload_on (">", natgt);
val _ = overload_on (">", Term`$>_`);

val int_ge =
    new_infixr_definition("int_ge",
			 Term `$>=_ x y = y <=_ x`,
			 450);

(*--------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism int_of_num:num->int.               *)
(*--------------------------------------------------------------------------*)

val int_of_num =
    new_prim_rec_definition
    ("int_of_num",
     Term `(& 0 = int_0) /\
           (& (SUC n) = (& n) + int_1)`);

val _ = add_numeral_form(#"i", SOME "&");

(*
val num_incl = new_definition ("&", Term `& = int_of_num`)
val _ = Rewrite.add_implicit_rewrites[num_incl]
*)

val INT_0 =
    prove_thm("INT_0",
	      Term `int_0 = 0`,
	      REWRITE_TAC[int_of_num]);

val INT_1 =
    prove_thm("INT_1",
	      Term `int_1 = 1`,
	      REWRITE_TAC[num_CONV (Term `1n`), int_of_num, INT_ADD_LID]);

(*--------------------------------------------------------------------------*)
(* Set up a nice interface map. Use & for the inclusion homomorphism, adjust*)
(* theorems retrospectively to use &n as Term `notation` for int constants. *)
(*--------------------------------------------------------------------------*)

(* Have been included above for now
new_special_symbol "--";

set_interface_map
[               "--","int_neg",
 "num_add","+",  "+_","int_add",
 "num_mul","*",  "*_","int_mul",
 "num_sub","-",  "-_","int_sub",
 "num_lt","<" ,  "<_","int_lt",
 "num_le","<=", "<=_","int_le",
 "num_gt",">" ,  ">_","int_gt",
 "num_ge",">=", ">=_","int_ge",
                 "&","int_of_num"];
*)

(*fun reeducate (s,t) = save_thm(s,REWRITE_RULE[INT_0, INT_1] t);

val thlist =
 ["INT_10",INT_10,
  "INT_ADD_SYM",INT_ADD_SYM,
  "INT_MUL_SYM",INT_MUL_SYM,
  "INT_ADD_ASSOC",INT_ADD_ASSOC,
  "INT_MUL_ASSOC",INT_MUL_ASSOC,
  "INT_ADD_LID",INT_ADD_LID,
  "INT_MUL_LID",INT_MUL_LID,
  "INT_ADD_LINV",INT_ADD_LINV,
  "INT_LDISTRIB",INT_LDISTRIB,
  "INT_LT_TOTAL",INT_LT_TOTAL,
  "INT_LT_REFL",INT_LT_REFL,
  "INT_LT_TRANS",INT_LT_TRANS,
  "INT_LT_LADD_IMP",INT_LT_LADD_IMP,
  "INT_LT_MUL",INT_LT_MUL] in

do (map reeducate thlist, map (load_theorem "-" o fst) thlist);
*)
(*--------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                      *)
(*--------------------------------------------------------------------------*)

val INT_ADD_RID =
    prove_thm("INT_ADD_RID",
	      Term `!x. x + 0 = x`,
	      SIMP_TAC int_ss [INT_ADD_SYM,GSYM INT_0,INT_ADD_LID])

val INT_ADD_RINV =
    prove_thm("INT_ADD_RINV",
	      Term `!x. x + (--x) = 0`,
	      SIMP_TAC int_ss [INT_ADD_SYM,INT_0,INT_ADD_LINV])

val INT_MUL_RID =
    prove_thm("INT_MUL_RID",
	      Term `!x. x * 1 = x`,
	      SIMP_TAC int_ss [INT_MUL_SYM,GSYM INT_1,INT_MUL_LID])

val INT_RDISTRIB =
    prove_thm("INT_RDISTRIB",
	      Term `!(x:int) y z. (x + y) * z = (x * z) + (y * z)`,
	      SIMP_TAC int_ss [INT_MUL_SYM,INT_LDISTRIB])

val INT_EQ_LADD =
    prove_thm("INT_EQ_LADD",
	      Term `!(x:int) y z. (x + y = x + z) = (y = z)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o AP_TERM (Term `$+_ (-- x)`)), ALL_TAC] THEN
	      SIMP_TAC int_ss [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID])


val INT_EQ_RADD =
    prove_thm("INT_EQ_RADD",
	      Term `!x y z. (x +_ z = y +_ z) = (x = y)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_EQ_LADD]);

val INT_ADD_LID_UNIQ =
    prove_thm("INT_ADD_LID_UNIQ",
	      Term `!x y. (x + y = y) = (x = 0)`,
	      REPEAT GEN_TAC THEN
	      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [GSYM INT_ADD_LID]
	      THEN SIMP_TAC int_ss [INT_0,INT_EQ_RADD])

val INT_ADD_RID_UNIQ =
    prove_thm("INT_ADD_RID_UNIQ",
	      Term `!x y. (x + y = x) = (y = 0)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_ADD_LID_UNIQ])

val INT_LNEG_UNIQ =
    prove_thm
    ("INT_LNEG_UNIQ",
     Term `!x y. (x + y = 0) = (x = ~y)`,
     REPEAT GEN_TAC THEN REWRITE_TAC [GSYM INT_0]
     THEN SUBST1_TAC (SYM(SPEC (Term `y:int`) INT_ADD_LINV))
     THEN SIMP_TAC int_ss [INT_EQ_RADD]);

val INT_RNEG_UNIQ =
    prove_thm("INT_RNEG_UNIQ",
	      Term `!x y. (x + y = 0) = (y = ~x)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_LNEG_UNIQ])

val INT_NEG_ADD =
    prove_thm("INT_NEG_ADD",
	      Term `!x y. ~(x + y) = ~x + ~y`,
	      REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
	      REWRITE_TAC[GSYM INT_LNEG_UNIQ] THEN
	      ONCE_REWRITE_TAC
	      [AC(INT_ADD_ASSOC,INT_ADD_SYM)
	       (Term `(a +_ b) +_ (c +_ d) = (a +_ c) +_ (b +_ d)`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_RID,INT_0]);

val INT_MUL_LZERO =
    prove_thm("INT_MUL_LZERO",
	      Term `!x. 0 * x = 0`,
	      GEN_TAC THEN SUBST1_TAC
	      (SYM(SPECL [Term `0 * x`, Term `0 * x`] INT_ADD_LID_UNIQ))
	      THEN REWRITE_TAC[GSYM INT_RDISTRIB, INT_ADD_RID]);

val INT_MUL_RZERO
    = prove_thm("INT_MUL_RZERO",
		Term `!x. x * 0 = 0`,
		GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
		SIMP_TAC int_ss [INT_MUL_LZERO]);

val INT_NEG_LMUL =
    prove_thm("INT_NEG_LMUL",
	      Term `!x y. --(x * y) = (--x) * y`,
	      REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
	      REWRITE_TAC[GSYM INT_LNEG_UNIQ, GSYM INT_RDISTRIB,
              INT_ADD_LINV, INT_MUL_LZERO,INT_0]);

val INT_NEG_RMUL =
    prove_thm("INT_NEG_RMUL",
	      Term `!x y. --(x * y) = x * (--y)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
	      SIMP_TAC int_ss [INT_NEG_LMUL]);

val INT_NEGNEG =
    prove_thm("INT_NEGNEG",
	      Term `!x. --(--x) = x`,
	      GEN_TAC THEN CONV_TAC SYM_CONV THEN
	      REWRITE_TAC[GSYM INT_LNEG_UNIQ, INT_ADD_RINV]);

val INT_NEG_MUL2 =
    prove_thm("INT_NEG_MUL2",
	      Term `!x y. (--x) * (--y) = x * y`,
	      REWRITE_TAC[GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG]);

val INT_LT_LADD =
    prove_thm("INT_LT_LADD",
	      Term `!x:int y z. (x + y) < (x + z) = y < z`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o (SPEC (Term `--x`)) o
			  MATCH_MP INT_LT_LADD_IMP)
	       THEN
	       REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID],
	       SIMP_TAC int_ss [INT_LT_LADD_IMP]]);

val INT_LT_RADD =
    prove_thm("INT_LT_RADD",
	      Term `!x:int y z. (x + z) < (y + z) = x < y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      SIMP_TAC int_ss [INT_LT_LADD]);

val INT_NOT_LT =
    prove_thm("INT_NOT_LT",
	      Term `!x:int y. ~(x < y) = y <= x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le]);

val INT_LT_ANTISYM =
    prove_thm("INT_LT_ANTISYM",
	      Term `!x:int y. ~(x < y /\ y < x)`,
	      REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_TRANS)
	      THEN REWRITE_TAC[INT_LT_REFL]);

val INT_LT_GT =
    prove_thm("INT_LT_GT",
	      Term `!x:int y. x < y ==> ~(y < x)`,
	      REPEAT GEN_TAC THEN
	      DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
	      REWRITE_TAC[INT_LT_ANTISYM]);

val INT_NOT_LE =
    prove_thm("INT_NOT_LE",
	      Term `!x y. ~(x <=_ y) = y <_ x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le]);

val INT_LE_TOTAL =
    prove_thm("INT_LE_TOTAL",
	      Term `!x y. x <=_ y \/ y <=_ x`,
	      REPEAT GEN_TAC THEN
	      REWRITE_TAC[int_le, GSYM DE_MORGAN_THM, INT_LT_ANTISYM]);

val INT_LET_TOTAL =
    prove_thm("INT_LET_TOTAL",
	      Term `!x y. x <=_ y \/ y <_ x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      SIMP_TAC int_ss []);

val INT_LTE_TOTAL =
    prove_thm("INT_LTE_TOTAL",
	      Term `!x y. x <_ y \/ y <=_ x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      SIMP_TAC int_ss [])


val INT_LE_REFL =
    prove_thm("INT_LE_REFL",
	      Term `!x. x <=_ x`,
	      GEN_TAC THEN REWRITE_TAC[int_le, INT_LT_REFL]);

val INT_LE_LT =
    prove_thm("INT_LE_LT",
	      Term `!x y. x <=_ y = x <_ y \/ (x = y)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [Term `x:int`, Term `y:int`] INT_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry(op THEN) (MATCH_MP_TAC INT_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC INT_LT_REFL]);

val INT_LT_LE =
    prove_thm
    ("INT_LT_LE",
     Term `!x y. x <_ y = x <=_ y /\ ~(x = y)`,
     let val lemma = TAUT_CONV (Term `~(a /\ ~a)`)
     in
	 REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, RIGHT_AND_OVER_OR, lemma]
	 THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
	 POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
	 DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LT_REFL]
     end);

val INT_LT_IMP_LE =
    prove_thm("INT_LT_IMP_LE",
	      Term `!x y. x <_ y ==> x <=_ y`,
		  REPEAT GEN_TAC THEN DISCH_TAC THEN
		  ASM_REWRITE_TAC[INT_LE_LT]);

val INT_LTE_TRANS =
    prove_thm("INT_LTE_TRANS",
	      Term `!x y z. x <_ y /\ y <=_ z ==> x <_ z`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, LEFT_AND_OVER_OR] THEN
	      DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
			 (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC))
	                 THEN REWRITE_TAC[]);

val INT_LET_TRANS =
    prove_thm("INT_LET_TRANS",
	      Term `!x y z. x <=_ y /\ y <_ z ==> x <_ z`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, RIGHT_AND_OVER_OR]
	      THEN
	      DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
			 (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)));

val INT_LE_TRANS =
    prove_thm("INT_LE_TRANS",
	      Term `!x y z. x <=_ y /\ y <=_ z ==> x <=_ z`,
	      REPEAT GEN_TAC THEN
	      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [INT_LE_LT] THEN
	      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
			 (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
	      THEN REWRITE_TAC[]
	      THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME (Term `y <_ z`))) THEN
	      DISCH_THEN(ACCEPT_TAC o MATCH_MP
			 INT_LT_IMP_LE o MATCH_MP INT_LET_TRANS));

val INT_LE_ANTISYM =
    prove_thm("INT_LE_ANTISYM",
	      Term `!x y. x <=_ y /\ y <=_ x = (x = y)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [REWRITE_TAC[int_le] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
	       (SPECL [Term `x:int`, Term `y:int`] INT_LT_TOTAL) THEN
	       ASM_REWRITE_TAC[],
	       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LE_REFL]]);

val INT_LET_ANTISYM =
    prove_thm("INT_LET_ANTISYM",
	      Term `!x y. ~(x <_ y /\ y <=_ x)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      BOOL_CASES_TAC (Term `x <_ y`) THEN REWRITE_TAC[]);

val INT_LTE_ANTSYM =
    prove_thm("INT_LTE_ANTSYM",
	      Term `!x y. ~(x <=_ y /\ y <_ x)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
	      MATCH_ACCEPT_TAC INT_LET_ANTISYM);

val INT_NEG_LT0 =
    prove_thm("INT_NEG_LT0",
	      Term `!x. (--x) <_ 0 = 0 <_ x`,
	      GEN_TAC THEN SUBST1_TAC(SYM(SPECL [Term `--x`,
						 Term `0`,
						 Term`x:int`] INT_LT_RADD))
	      THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID, GSYM INT_0]);

val INT_NEG_GT0 =
    prove_thm("INT_NEG_GT0",
	      Term `!x. 0 <_ (--x) = x <_ 0`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LT0, INT_NEGNEG]);

val INT_NEG_LE0 =
    prove_thm("INT_NEG_LE0",
	      Term `!x. (--x) <=_ 0 = 0 <=_ x`,
	      GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      REWRITE_TAC[INT_NEG_GT0]);

val INT_NEG_GE0 =
    prove_thm("INT_NEG_GE0",
	      Term `!x. 0 <=_ (--x) = x <=_ 0`,
	      GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      REWRITE_TAC[INT_NEG_LT0]);

val INT_LT_NEGTOTAL =
    prove_thm("INT_LT_NEGTOTAL",
	      Term `!x. (x = 0) \/ (0 <_ x) \/ (0 <_ --x)`,
	      GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
	      (SPECL [Term `x:int`, Term `0`] INT_LT_TOTAL) THEN
	      ASM_REWRITE_TAC
	      [SYM(REWRITE_RULE[INT_NEGNEG] (SPEC (Term `--x`) INT_NEG_LT0))]);

val INT_LE_NEGTOTAL =
    prove_thm
    ("INT_LE_NEGTOTAL",
     Term `!x. 0 <=_ x \/ 0 <=_ --x`,
     GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
     REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC (Term `x:int`)
					    INT_LT_NEGTOTAL)
     THEN ASM_REWRITE_TAC[]);

val INT_LE_MUL =
    prove_thm
    ("INT_LE_MUL",
     Term `!x y. 0 <=_ x /\ 0 <=_ y ==> 0 <=_ (x *_ y)`,
	 REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
	 MAP_EVERY ASM_CASES_TAC [Term `0 = x`, Term `0 = y`] THEN
	 ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
	 REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO] THEN
	 DISCH_TAC THEN DISJ1_TAC
	 THEN MATCH_MP_TAC (REWRITE_RULE [INT_0] INT_LT_MUL) THEN
	 ASM_REWRITE_TAC[]);

val INT_LE_SQUARE =
    prove_thm("INT_LE_SQUARE",
	      Term `!x. 0 <=_ x *_ x`,
	      GEN_TAC THEN DISJ_CASES_TAC (SPEC (Term `x:int`) INT_LE_NEGTOTAL)
	      THEN
	      POP_ASSUM(MP_TAC o MATCH_MP INT_LE_MUL o W CONJ) THEN
	      REWRITE_TAC[GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL, INT_NEGNEG]);

val INT_LE_01 =
    prove_thm("INT_LE_01",
	      Term `0 <=_ 1`,
	      SUBST1_TAC(SYM(SPEC (Term `1`) INT_MUL_LID)) THEN
	      SIMP_TAC int_ss [INT_LE_SQUARE,INT_1]);

val INT_LT_01 =
    prove_thm("INT_LT_01",
	      Term `0 <_ 1`,
	      SIMP_TAC int_ss [INT_LT_LE, INT_LE_01,
			       GSYM INT_0,GSYM INT_1,INT_10])

val INT_LE_LADD =
    prove_thm("INT_LE_LADD",
	      Term `!x y z. (x +_ y) <=_ (x +_ z) = y <=_ z`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_LADD);

val INT_LE_RADD =
    prove_thm("INT_LE_RADD",
	      Term `!x y z. (x +_ z) <=_ (y +_ z) = x <=_ y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
	      AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_RADD);

val INT_LT_ADD2 =
    prove_thm("INT_LT_ADD2",
	      Term `!w x y z. w <_ x /\ y <_ z ==> (w +_ y) <_ (x +_ z)`,
	      REPEAT GEN_TAC THEN DISCH_TAC THEN
	      MATCH_MP_TAC INT_LT_TRANS THEN EXISTS_TAC (Term `w +_ z`) THEN
	      ASM_REWRITE_TAC[INT_LT_LADD, INT_LT_RADD]);

val INT_LE_ADD2 =
    prove_thm("INT_LE_ADD2",
	      Term `!w x y z. w <=_ x /\ y <=_ z ==> (w +_ y) <=_ (x +_ z)`,
	      REPEAT GEN_TAC THEN DISCH_TAC THEN
	      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (Term `w +_ z`) THEN
	      ASM_REWRITE_TAC[INT_LE_LADD, INT_LE_RADD]);

val INT_LE_ADD =
    prove_thm("INT_LE_ADD",
	      Term `!x y. 0 <=_ x /\ 0 <=_ y ==> 0 <=_ (x +_ y)`,
	      REPEAT GEN_TAC
	      THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2) THEN
	      REWRITE_TAC[INT_ADD_LID,GSYM INT_0]);

val INT_LT_ADD =
    prove_thm("INT_LT_ADD",
	      Term `!x y. 0 <_ x /\ 0 <_ y ==> 0 <_ (x +_ y)`,
	      REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2)
	      THEN
	      REWRITE_TAC[INT_ADD_LID,GSYM INT_0]);



val INT_LT_ADDNEG =
    prove_thm("INT_LT_ADDNEG",
	      Term `!x y z. y <_ (x +_ (--z)) = (y +_ z) <_ x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `y:int`,
				    Term `x +_ (--z)`,
				    Term `z:int`] INT_LT_RADD)) THEN
	      REWRITE_TAC[GSYM INT_ADD_ASSOC, INT_ADD_LINV,
			  INT_ADD_RID, INT_0]);
(* REWRITE TO *)
val INT_LT_ADDNEG2 =
    prove_thm
    ("INT_LT_ADDNEG2",
     Term `!x y z. (x +_ (--y)) <_ z = x <_ (z +_ y)`,
     REPEAT GEN_TAC THEN
     SUBST1_TAC(SYM(SPECL [Term `x +_ (-- y)`, Term `z:int`,
			   Term `y:int`] INT_LT_RADD)) THEN
     REWRITE_TAC[GSYM INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_RID,INT_0]);

val INT_LT_ADD1 =
    prove_thm("INT_LT_ADD1",
	      Term `!x y. x <=_ y ==> x <_ (y +_ 1)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
	      DISCH_THEN DISJ_CASES_TAC THENL
	      [POP_ASSUM(MP_TAC o MATCH_MP INT_LT_ADD2 o C CONJ INT_LT_01)
	       THEN
	       REWRITE_TAC[INT_ADD_RID],
	       POP_ASSUM SUBST1_TAC THEN
	       GEN_REWRITE_TAC LAND_CONV [] [GSYM INT_ADD_RID] THEN
	       REWRITE_TAC[INT_LT_LADD, INT_LT_01]]);

val INT_SUB_ADD =
    prove_thm("INT_SUB_ADD",
	      Term `!x y. (x -_ y) +_ y = x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
					      INT_ADD_LINV, INT_ADD_RID,INT_0])

val INT_SUB_ADD2 =
    prove_thm("INT_SUB_ADD2",
	      Term `!x y. y +_ (x -_ y) = x`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      MATCH_ACCEPT_TAC INT_SUB_ADD);

val INT_SUB_REFL =
    prove_thm("INT_SUB_REFL",
	      Term `!x. x -_ x = 0`,
	      GEN_TAC THEN REWRITE_TAC[int_sub, INT_ADD_RINV]);

val INT_SUB_0 =
    prove_thm("INT_SUB_0",
	      Term `!x y. (x -_ y = 0) = (x = y)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o C AP_THM (Term `y:int`) o
			  AP_TERM (Term `$+_`)) THEN
	       REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID,GSYM INT_0],
	       DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC INT_SUB_REFL]);

val INT_LE_DOUBLE =
    prove_thm("INT_LE_DOUBLE",
	      Term `!x. 0 <=_ x +_ x = 0 <=_ x`,
	      GEN_TAC THEN EQ_TAC THENL
	      [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[INT_NOT_LE] THEN
	       DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2 o W CONJ)
	       THEN REWRITE_TAC [INT_ADD_RID],
	       DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2 o W CONJ)] THEN
	      REWRITE_TAC[INT_ADD_RID]);

val INT_LE_NEGL =
    prove_thm("INT_LE_NEGL",
	      Term `!x. (--x <=_ x) = (0 <=_ x)`,
	      GEN_TAC
	      THEN SUBST1_TAC (SYM(SPECL [Term `x:int`,
					  Term `--x`, Term `x:int`]
				   INT_LE_LADD))
	      THEN REWRITE_TAC[INT_ADD_RINV, INT_LE_DOUBLE]);

val INT_LE_NEGR =
    prove_thm("INT_LE_NEGR",
	      Term `!x. (x <=_ --x) = (x <=_ 0)`,
	      GEN_TAC THEN SUBST1_TAC(SYM(SPEC (Term `x:int`) INT_NEGNEG)) THEN
	      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [INT_NEGNEG] THEN
	      REWRITE_TAC[INT_LE_NEGL] THEN REWRITE_TAC[INT_NEG_GE0] THEN
	      REWRITE_TAC[INT_NEGNEG]);

val INT_NEG_EQ0 =
    prove_thm("INT_NEG_EQ0",
	      Term `!x. (--x = 0) = (x = 0)`,
GEN_TAC THEN EQ_TAC THENL
[DISCH_THEN(MP_TAC o AP_TERM (Term `$+_ x`))
   THEN REWRITE_TAC[INT_ADD_RINV, INT_ADD_LINV, INT_ADD_RID, INT_0]
   THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC,
 DISCH_THEN(MP_TAC o AP_TERM (Term `$+_ (--x)`))
   THEN REWRITE_TAC[INT_ADD_RINV, INT_ADD_LINV, INT_ADD_RID, INT_0]
   THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC])

val INT_NEG_0 =
    prove_thm("INT_NEG_0",
	      Term `--(0) = 0`,
	      REWRITE_TAC[INT_NEG_EQ0]);

val INT_NEG_SUB =
    prove_thm("INT_NEG_SUB",
	      Term `!x y. --(x -_ y) = y -_ x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub,
					      INT_NEG_ADD, INT_NEGNEG] THEN
	      MATCH_ACCEPT_TAC INT_ADD_SYM);

val INT_SUB_LT =
    prove_thm("INT_SUB_LT",
	      Term `!x y. 0 <_ x -_ y = y <_ x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `0`, Term `x -_ y`,
				    Term `y:int`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID,GSYM INT_0]);

val INT_SUB_LE =
    prove_thm("INT_SUB_LE",
	      Term `!x y. 0 <=_ (x -_ y) = y <=_ x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `0`, Term `x -_ y`,
				    Term `y:int`] INT_LE_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID, GSYM INT_0]);

val INT_ADD_SUB =
    prove_thm("INT_ADD_SUB",
	      Term `!x y. (x +_ y) -_ x = y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
			  INT_ADD_RINV, INT_ADD_RID, INT_0]);

val INT_SUB_LDISTRIB =
    prove_thm("INT_SUB_LDISTRIB",
	      Term `!x y z. x *_ (y -_ z) = (x *_ y) -_ (x *_ z)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub,
					      INT_LDISTRIB, INT_NEG_RMUL]);

val INT_SUB_RDISTRIB =
    prove_thm("INT_SUB_RDISTRIB",
	      Term `!x y z. (x -_ y) *_ z = (x *_ z) -_ (y *_ z)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
	      MATCH_ACCEPT_TAC INT_SUB_LDISTRIB);

val INT_NEG_EQ =
    prove_thm("INT_NEG_EQ",
	      Term `!x y. (--x = y) = (x = --y)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN
	      REWRITE_TAC[INT_NEGNEG]);

val INT_NEG_MINUS1 =
    prove_thm("INT_NEG_MINUS1",
	      Term `!x. --x = (--(1)) *_ x`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LMUL] THEN
	      REWRITE_TAC[INT_MUL_LID,GSYM INT_1]);

val INT_LT_IMP_NE =
    prove_thm("INT_LT_IMP_NE",
	      Term `!x y. x <_ y ==> ~(x = y)`,
		  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
		  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
		  REWRITE_TAC[INT_LT_REFL]);

val INT_LE_ADDR =
    prove_thm("INT_LE_ADDR",
	      Term `!x y. x <=_ x +_ y = 0 <=_ y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `x:int`, Term `0`,
				    Term `y:int`] INT_LE_LADD)) THEN
	      REWRITE_TAC[INT_ADD_RID,INT_0]);

val INT_LE_ADDL =
    prove_thm("INT_LE_ADDL",
	      Term `!x y. y <=_ x +_ y = 0 <=_ x`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      MATCH_ACCEPT_TAC INT_LE_ADDR);

val INT_LT_ADDR =
    prove_thm("INT_LT_ADDR",
	      Term `!x y. x <_ x +_ y = 0 <_ y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `x:int`, Term `0`,
				    Term `y:int`] INT_LT_LADD)) THEN
	      REWRITE_TAC[INT_ADD_RID,INT_0]);

val INT_LT_ADDL =
    prove_thm("INT_LT_ADDL",
	      Term `!x y. y <_ x +_ y = 0 <_ x`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      MATCH_ACCEPT_TAC INT_LT_ADDR);

val INT_ENTIRE =
    prove_thm("INT_ENTIRE",
	      Term `!x y. (x *_ y = 0) = (x = 0) \/ (y = 0)`,
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
	       CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
	       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_NEG_0, INT_LT_REFL],
	       DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
	       REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO]]);

val INT_EQ_LMUL =
    prove_thm("INT_EQ_LMUL",
	      Term `!x y z. (x *_ y = x *_ z) = (x = 0) \/ (y = z)`,
	      REPEAT GEN_TAC THEN
	      GEN_REWRITE_TAC LAND_CONV [] [GSYM INT_SUB_0] THEN
	      REWRITE_TAC[GSYM INT_SUB_LDISTRIB] THEN
	      REWRITE_TAC[INT_ENTIRE, INT_SUB_0]);

val INT_EQ_RMUL =
    prove_thm("INT_EQ_RMUL",
	      Term `!x y z. (x *_ z = y *_ z) = (z = 0) \/ (x = y)`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
	      MATCH_ACCEPT_TAC INT_EQ_LMUL);

(*--------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                *)
(*--------------------------------------------------------------------------*)

val INT =
    prove_thm("INT",
	      Term `!n. &(SUC n) = &n +_ 1`,
	      GEN_TAC THEN REWRITE_TAC[int_of_num] THEN
	      REWRITE_TAC[INT_1]);

val INT_POS =
    prove_thm("INT_POS",
	      Term `!n. 0 <=_ &n`,
	      INDUCT_TAC THEN REWRITE_TAC[INT_LE_REFL] THEN
	      MATCH_MP_TAC INT_LE_TRANS THEN
	      EXISTS_TAC (Term `&n`) THEN ASM_REWRITE_TAC[INT] THEN
	      REWRITE_TAC[INT_LE_ADDR, INT_LE_01]);

val INT_LE =
    prove_thm("INT_LE",
	      Term `!m n. &m <=_ &n = m <= n`,
	      REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
	      [INT, INT_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, INT_LE_REFL] THEN
	      REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
	      [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (Term `&n`) THEN
	       ASM_REWRITE_TAC[ZERO_LESS_EQ, INT_LE_ADDR, INT_LE_01],
	       DISCH_THEN(MP_TAC o C CONJ (SPEC (Term `m:num`) INT_POS)) THEN
	       DISCH_THEN(MP_TAC o MATCH_MP INT_LE_TRANS) THEN
	       REWRITE_TAC[INT_NOT_LE, INT_LT_ADDR, INT_LT_01]]);

val INT_LT =
    prove_thm("INT_LT",
	      Term `!m n. &m <_ &n = m < n`,
	      REPEAT GEN_TAC
	      THEN MATCH_ACCEPT_TAC ((REWRITE_RULE[] o AP_TERM (Term `$~`) o
				      REWRITE_RULE[GSYM NOT_LESS,
						   GSYM INT_NOT_LT])
				     (SPEC_ALL INT_LE)));

val INT_INJ =
    prove_thm("INT_INJ",
	      Term `!m n. (&m = &n) = (m = n)`,
	      let val th = PROVE(Term `(m:num = n) = m <= n /\ n <= m`,
				 EQ_TAC
				 THENL [DISCH_THEN SUBST1_TAC
					THEN REWRITE_TAC[LESS_EQ_REFL],
					MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM])
	      in
		  REPEAT GEN_TAC
		  THEN REWRITE_TAC[th, GSYM INT_LE_ANTISYM, INT_LE]
	      end)

val INT_ADD =
    prove_thm("INT_ADD",
	      Term `!m n. &m +_ &n = &(m + n)`,
	      INDUCT_TAC THEN REWRITE_TAC[INT, ADD, INT_ADD_LID,GSYM INT_0]
	      THEN
	      RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
	      CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));

val INT_MUL =
    prove_thm("INT_MUL",
	      Term `!m n. &m *_ &n = &(m * n)`,
	      INDUCT_TAC THEN REWRITE_TAC[INT_MUL_LZERO, MULT_CLAUSES, INT,
					  GSYM INT_ADD, INT_RDISTRIB] THEN
	      FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
	      REWRITE_TAC[INT_MUL_LID,GSYM INT_1]);

(*--------------------------------------------------------------------------*)
(* Now more theorems                                                        *)
(*--------------------------------------------------------------------------*)

val INT_LT_NZ =
    prove_thm("INT_LT_NZ",
	      Term `!n. ~(&n = 0) = (0 <_ &n)`,
	      GEN_TAC THEN REWRITE_TAC[INT_LT_LE] THEN
	      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
	      ASM_CASES_TAC (Term `&n = 0`)
	      THEN ASM_REWRITE_TAC[INT_LE_REFL, INT_POS]);

val INT_NZ_IMP_LT =
    prove_thm("INT_NZ_IMP_LT",
	      Term `!n. ~(n = 0n) ==> 0 <_ &n`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_INJ, INT_LT_NZ]);

val INT_DOUBLE =
    prove_thm("INT_DOUBLE",
	      Term `!x. x +_ x = 2 *_ x`,
	      GEN_TAC THEN REWRITE_TAC[num_CONV (Term `2n`), INT] THEN
	      REWRITE_TAC[INT_RDISTRIB, INT_MUL_LID,GSYM INT_1]);

val INT_SUB_SUB =
    prove_thm("INT_SUB_SUB",
	      Term `!x y. (x - y) - x = ~y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
	      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
			       (Term `(a +_ b) +_ c = (c +_ a) +_ b`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID,GSYM INT_0]);

val INT_LT_ADD_SUB =
    prove_thm("INT_LT_ADD_SUB",
	      Term `!x y z. (x +_ y) <_ z = x <_ (z -_ y)`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `x:int`, Term `z -_ y`,
				    Term `y:int`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD]);

val INT_LT_SUB_RADD =
    prove_thm("INT_LT_SUB_RADD",
	      Term `!x y z. (x -_ y) <_ z = x <_ z +_ y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `x -_ y`, Term `z:int`,
				    Term `y:int`] INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_SUB_ADD]);

val INT_LT_SUB_LADD =
    prove_thm("INT_LT_SUB_LADD",
	      Term `!x y z. x <_ (y -_ z) = (x +_ z) <_ y`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL [Term `x +_ z`, Term `y:int`,
				    Term `--z`] INT_LT_RADD)) THEN
	      REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
			  INT_ADD_RINV, INT_ADD_RID, INT_0]);

val INT_LE_SUB_LADD =
    prove_thm("INT_LE_SUB_LADD",
	      Term `!x y z. x <=_ (y -_ z) = (x +_ z) <=_ y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT,
					      INT_LT_SUB_RADD]);

val INT_LE_SUB_RADD =
    prove_thm("INT_LE_SUB_RADD",
	      Term `!x y z. (x -_ y) <=_ z = x <=_ z +_ y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT,
					      INT_LT_SUB_LADD]);

val INT_LT_NEG =
    prove_thm("INT_LT_NEG",
	      Term `!x y. --x <_ --y = y <_ x`,
	      REPEAT GEN_TAC THEN
	      SUBST1_TAC(SYM(SPECL[Term `--x`, Term `--y`, Term `x +_ y`]
			     INT_LT_RADD)) THEN
	      REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID, GSYM INT_0]
	      THEN
	      ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
	      REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_RINV,
			  INT_ADD_LID, GSYM INT_0]);

val INT_LE_NEG =
    prove_thm("INT_LE_NEG",
	      Term `!x y. --x <=_ --y = y <=_ x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN
	      REWRITE_TAC[INT_LT_NEG]);

val INT_ADD2_SUB2 =
    prove_thm("INT_ADD2_SUB2",
	      Term `!a b c d. (a +_ b) -_ (c +_ d) = (a -_ c) +_ (b -_ d)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_ADD] THEN
	      CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));

val INT_SUB_LZERO =
    prove_thm("INT_SUB_LZERO",
	      Term `!x. 0 -_ x = --x`,
	      GEN_TAC THEN REWRITE_TAC[int_sub, INT_ADD_LID, GSYM INT_0]);

val INT_SUB_RZERO =
    prove_thm("INT_SUB_RZERO",
	      Term `!x. x -_ 0 = x`,
	      GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_0,
				       INT_ADD_RID, INT_0]);

val INT_LET_ADD2 =
    prove_thm("INT_LET_ADD2",
	      Term `!w x y z. w <=_ x /\ y <_ z ==> (w +_ y) <_ (x +_ z)`,
		  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
		  MATCH_MP_TAC INT_LTE_TRANS THEN
		  EXISTS_TAC (Term `w +_ z`) THEN
		  ASM_REWRITE_TAC[INT_LE_RADD, INT_LT_LADD]);

val INT_LTE_ADD2 =
    prove_thm("INT_LTE_ADD2",
	      Term `!w x y z. w <_ x /\ y <=_ z ==> (w +_ y) <_ (x +_ z)`,
		  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
		  ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
		  MATCH_ACCEPT_TAC INT_LET_ADD2);

val INT_LET_ADD =
    prove_thm("INT_LET_ADD",
	      Term `!x y. 0 <=_ x /\ 0 <_ y ==> 0 <_ (x +_ y)`,
		  REPEAT GEN_TAC THEN DISCH_TAC THEN
		  SUBST1_TAC(SYM(SPEC (Term `0`) (REWRITE_RULE [INT_0]
						   INT_ADD_LID)))
		  THEN
		  MATCH_MP_TAC INT_LET_ADD2 THEN
		  ASM_REWRITE_TAC[]);

val INT_LTE_ADD =
    prove_thm("INT_LTE_ADD",
	      Term `!x y. 0 <_ x /\ 0 <=_ y ==> 0 <_ (x +_ y)`,
		  REPEAT GEN_TAC THEN DISCH_TAC THEN
		  SUBST1_TAC(SYM(SPEC (Term `0`) (REWRITE_RULE [INT_0]
						   INT_ADD_LID))) THEN
		  MATCH_MP_TAC INT_LTE_ADD2 THEN
		  ASM_REWRITE_TAC[]);

val INT_LT_MUL2 =
    prove_thm
    ("INT_LT_MUL2",
     Term `!x1 x2 y1 y2. 0 <=_ x1 /\ 0 <=_ y1 /\ x1 <_ x2 /\ y1 <_ y2 ==>
         (x1 *_ y1) <_ (x2 *_ y2)`,
     REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_SUB_LT] THEN
     REWRITE_TAC[INT_SUB_RZERO] THEN
     SUBGOAL_THEN (Term `!a b c d.
		   (a *_ b) -_ (c *_ d)
		   = ((a *_ b) -_ (a *_ d)) +_ ((a *_ d) -_ (c *_ d))`)
     MP_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
		       (Term `(a +_ b) +_ (c +_ d) = (b +_ c) +_ (a +_ d)`)]
      THEN
      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID, GSYM INT_0],
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
    prove_thm("INT_SUB_LNEG",
	      Term `!x y. (--x) -_ y = --(x +_ y)`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_ADD]);

val INT_SUB_RNEG =
    prove_thm("INT_SUB_RNEG",
	      Term `!x y. x -_ (--y) = x +_ y`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEGNEG]);

val INT_SUB_NEG2 =
    prove_thm("INT_SUB_NEG2",
	      Term `!x y. (--x) -_ (--y) = y -_ x`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[INT_SUB_LNEG] THEN
	      REWRITE_TAC[int_sub, INT_NEG_ADD, INT_NEGNEG] THEN
	      MATCH_ACCEPT_TAC INT_ADD_SYM);

val INT_SUB_TRIANGLE =
    prove_thm("INT_SUB_TRIANGLE",
	      Term `!a b c. (a -_ b) +_ (b -_ c) = a -_ c`,
	      REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
	      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
			       (Term `(a +_ b) +_ (c +_ d)
				      = (b +_ c) +_ (a +_ d)`)] THEN
	      REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID, GSYM INT_0]);

val INT_EQ_SUB_LADD =
    prove_thm("INT_EQ_SUB_LADD",
	      Term `!x y z. (x = y -_ z) = (x +_ z = y)`,
	      REPEAT GEN_TAC THEN (SUBST1_TAC o SYM o C SPECL INT_EQ_RADD)
	      [Term `x:int`, Term `y -_ z`, Term `z:int`]
	      THEN REWRITE_TAC[INT_SUB_ADD]);

val INT_EQ_SUB_RADD =
    prove_thm("INT_EQ_SUB_RADD",
	      Term `!x y z. (x -_ y = z) = (x = z +_ y)`,
	      REPEAT GEN_TAC THEN CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV))
	      THEN
	      MATCH_ACCEPT_TAC INT_EQ_SUB_LADD);

val INT_SUB_SUB2 =
    prove_thm("INT_SUB_SUB2",
	      Term `!x y. x -_ (x -_ y) = y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEGNEG] THEN
	      AP_TERM_TAC THEN REWRITE_TAC[INT_NEG_SUB, INT_SUB_SUB]);

val INT_ADD_SUB2 =
    prove_thm("INT_ADD_SUB2",
	      Term `!x y. x -_ (x +_ y) = --y`,
	      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEG_SUB] THEN
	      AP_TERM_TAC THEN REWRITE_TAC[INT_ADD_SUB]);

val INT_EQ_LMUL2 =
    prove_thm("INT_EQ_LMUL2",
	      Term `!x y z. ~(x = 0) ==> ((y = z) = (x *_ y = x *_ z))`,
		  REPEAT GEN_TAC THEN DISCH_TAC THEN
		  MP_TAC(SPECL [Term `x:int`, Term `y:int`,
				Term `z:int`] INT_EQ_LMUL) THEN
		  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC
		  THEN REFL_TAC);

val INT_EQ_IMP_LE =
    prove_thm("INT_EQ_IMP_LE",
	      Term `!x y. (x = y) ==> x <=_ y`,
		  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
		  MATCH_ACCEPT_TAC INT_LE_REFL);

val INT_POS_NZ =
    prove_thm("INT_POS_NZ",
	      Term `!x. 0 <_ x ==> ~(x = 0)`,
		  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP INT_LT_IMP_NE)
		  THEN
		  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC);

val INT_EQ_RMUL_IMP =
    prove_thm("INT_EQ_RMUL_IMP",
	      Term `!x y z. ~(z = 0) /\ (x *_ z = y *_ z) ==> (x = y)`,
		  REPEAT GEN_TAC
		  THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
		  ASM_REWRITE_TAC[INT_EQ_RMUL]);

val INT_EQ_LMUL_IMP =
    prove_thm("INT_EQ_LMUL_IMP",
	      Term `!x y z. ~(x = 0) /\ (x *_ y = x *_ z) ==> (y = z)`,
		  ONCE_REWRITE_TAC[INT_MUL_SYM]
		  THEN MATCH_ACCEPT_TAC INT_EQ_RMUL_IMP);

val INT_DIFFSQ =
    prove_thm("INT_DIFFSQ",
	      Term `!x y. (x +_ y) *_ (x -_ y) = (x *_ x) -_ (y *_ y)`,
	      REPEAT GEN_TAC THEN
	      REWRITE_TAC[INT_LDISTRIB, INT_RDISTRIB, int_sub,
			  GSYM INT_ADD_ASSOC] THEN
	      ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
			       (Term`a +_ (b +_ (c +_ d)) =
                                     (b +_ c) +_ (a +_ d)`)]
	      THEN
	      REWRITE_TAC[INT_ADD_LID_UNIQ, GSYM INT_NEG_RMUL] THEN
	      REWRITE_TAC[INT_LNEG_UNIQ] THEN AP_TERM_TAC THEN
	      MATCH_ACCEPT_TAC INT_MUL_SYM);

val INT_POSSQ =
    prove_thm("INT_POASQ",
	      Term `!x. 0 <_ (x *_ x) = ~(x = 0)`,
	      GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LE]
	      THEN AP_TERM_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(MP_TAC o C CONJ (SPEC (Term `x:int`) INT_LE_SQUARE))
	       THEN
	       REWRITE_TAC[INT_LE_ANTISYM, INT_ENTIRE],
	       DISCH_THEN SUBST1_TAC
	       THEN REWRITE_TAC[INT_MUL_LZERO, INT_LE_REFL]]);

val INT_SUMSQ =
    prove_thm("INT_SUMSQ",
	      Term `!x y. ((x *_ x) +_ (y *_ y) = 0) = (x = 0) /\ (y = 0)`,
	      REPEAT GEN_TAC THEN EQ_TAC THENL
	      [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
	       DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC INT_POS_NZ THENL
	       [MATCH_MP_TAC INT_LTE_ADD, MATCH_MP_TAC INT_LET_ADD] THEN
	       ASM_REWRITE_TAC[INT_POSSQ, INT_LE_SQUARE],
	       DISCH_TAC
	       THEN ASM_REWRITE_TAC[INT_MUL_LZERO, INT_ADD_RID]]);

val INT_EQ_NEG =
    prove_thm("INT_EQ_NEG",
	      Term `!x y. (--x = --y) = (x = y)`,
	      REPEAT GEN_TAC THEN
	      REWRITE_TAC[GSYM INT_LE_ANTISYM, INT_LE_NEG] THEN
	      MATCH_ACCEPT_TAC CONJ_SYM);

(*--------------------------------------------------------------------------*)
(* Some nasty hacking round to show that the positive integers are a copy   *)
(* of the natural numbers.                                                  *)
(*--------------------------------------------------------------------------*)

val INT_DECOMPOSE =
    prove_thm("INT_DECOMPOSE",
	      Term `!i. ?m n. i = mk_int($tint_eq(m,n))`,
	      GEN_TAC THEN
	      MP_TAC(SPEC (Term `dest_int i`) (CONJUNCT2 int_tybij)) THEN
	      REWRITE_TAC[CONJUNCT1 int_tybij] THEN BETA_TAC THEN
	      DISCH_THEN(X_CHOOSE_THEN (Term `x:num#num`) MP_TAC) THEN
	      DISCH_THEN(MP_TAC o AP_TERM (Term `mk_int`)) THEN
	      REWRITE_TAC[CONJUNCT1 int_tybij] THEN
	      DISCH_THEN SUBST1_TAC THEN
	      MAP_EVERY EXISTS_TAC [Term `FST(x:num#num)`,
				    Term `SND(x:num#num)`] THEN
	      SIMP_TAC int_ss []);

val DEST_MK_EQCLASS =
    prove_thm("DEST_MK_EQCLASS",
	      Term `!v. dest_int (mk_int ($tint_eq v)) = $tint_eq v`,
	      GEN_TAC THEN REWRITE_TAC[GSYM int_tybij] THEN
	      BETA_TAC THEN EXISTS_TAC (Term `v:num#num`) THEN REFL_TAC);

val REP_EQCLASS =
    prove_thm("REP_EQCLASS",
	      Term `!v. $@($tint_eq v) tint_eq v`,
	      GEN_TAC THEN ONCE_REWRITE_TAC[TINT_EQ_SYM] THEN
	      MATCH_MP_TAC SELECT_AX THEN
	      EXISTS_TAC (Term (`v:num#num`)) THEN
	      MATCH_ACCEPT_TAC TINT_EQ_REFL);

val NUM_LEMMA =
    prove_thm("NUM_LEMMA",
	      Term `!i. 0 <=_ i ==> ?n. i = mk_int($tint_eq (n,0n))`,
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
				$@($tint_eq tint_0) tint_eq (1n,1n)`)
		  (fn th => REWRITE_TAC[MATCH_MP TINT_LT_WELLDEF th])
		  THENL [REWRITE_TAC[REP_EQCLASS, tint_0], ALL_TAC] THEN
		  REWRITE_TAC[tint_lt] THEN
		  GEN_REWRITE_TAC RAND_CONV [] [ADD_SYM] THEN
		  ASM_REWRITE_TAC[LESS_MONO_ADD_EQ]);

val NUM_DECOMPOSE =
    prove_thm("NUM_DECOMPOSE",
	      Term `!n. &n = mk_int($tint_eq (n,0n))`,
	      INDUCT_TAC THEN REWRITE_TAC[int_of_num, definition "int_0",
					  tint_0] THENL
	      [AP_TERM_TAC THEN REWRITE_TAC[GSYM TINT_EQ_EQUIV,
					    tint_eq, ADD_CLAUSES],
	       ASM_REWRITE_TAC[definition "int_1",definition"int_add",tint_1]
	       THEN
	       AP_TERM_TAC THEN REWRITE_TAC[GSYM TINT_EQ_EQUIV,
					    DEST_MK_EQCLASS] THEN
	       REWRITE_TAC[TINT_EQ_EQUIV] THEN
	       SUBGOAL_THEN (Term `$@($tint_eq(n,0n)) tint_eq (n,0n) /\
			     $@($tint_eq(1n + 1n,1n)) tint_eq (1n + 1n,1n)`)
	       (fn th => REWRITE_TAC[REWRITE_RULE[TINT_EQ_EQUIV]
				     (MATCH_MP TINT_ADD_WELLDEF th)])
	       THENL [REWRITE_TAC[REP_EQCLASS, tint_0], ALL_TAC] THEN
	       REWRITE_TAC[tint_add, GSYM TINT_EQ_EQUIV, tint_eq] THEN
	       REWRITE_TAC[num_CONV (Term `1n`), ADD_CLAUSES]]);

val NUM_POSINT =
    prove_thm("NUM_POSINT",
	      Term `!i. 0 <=_ i ==> ?!n. i = &n`,
		  GEN_TAC THEN DISCH_TAC THEN
		  CONV_TAC EXISTS_UNIQUE_CONV THEN
		  CONJ_TAC THENL
		  [ALL_TAC,
		   REPEAT GEN_TAC THEN
		   GEN_REWRITE_TAC RAND_CONV [] [GSYM INT_INJ] THEN
		   DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
		   REFL_TAC] THEN
		  POP_ASSUM
		  (fn th => X_CHOOSE_THEN (Term `n:num`) SUBST1_TAC
		                   (MATCH_MP NUM_LEMMA th)) THEN
		  EXISTS_TAC (Term `n:num`) THEN REWRITE_TAC[NUM_DECOMPOSE]);

(*--------------------------------------------------------------------------*)
(* Theorems about mapping both ways between :num and :int                   *)
(*--------------------------------------------------------------------------*)

val Num = new_definition("Num",
  Term `Num i = @n. i = &n`);

val NUM_OF_INT =
    prove_thm("NUM_OF_INT",
	      Term `!n. Num(&n) = n`,
	      GEN_TAC THEN REWRITE_TAC[Num, INT_INJ] THEN
	      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
	      REWRITE_TAC[SELECT_REFL]);

val INT_OF_NUM =
    prove_thm("INT_OF_NUM",
	      Term `!i. (&(Num i) = i) = 0 <=_ i`,
	      GEN_TAC THEN EQ_TAC THENL
	      [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC INT_POS,
	       DISCH_THEN(ASSUME_TAC o EXISTENCE o MATCH_MP NUM_POSINT) THEN
	       REWRITE_TAC[Num] THEN CONV_TAC SYM_CONV THEN
	       MP_TAC(ISPEC (Term `\n. i = &n`) SELECT_AX) THEN
	       BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
	       POP_ASSUM ACCEPT_TAC]);

val _ = export_theory();
