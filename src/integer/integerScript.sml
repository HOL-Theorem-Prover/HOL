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
Theory integer
Ancestors
  arithmetic pred_set prim_rec num divides normalizer
Libs
  jrhUtils quotient liteLib simpLib numLib liteLib metisLib
  BasicProvers hurdUtils boolSimps



val _ = temp_delsimps ["NORMEQ_CONV"]

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

Theorem EQ_LADD:
                        !x y z. (x + y = x + z) = (y = z)
Proof
                        ARITH_TAC
QED


Theorem EQ_ADDL:
                        !x y. (x = x + y) = (y = 0)
Proof
                        ARITH_TAC
QED

Theorem LT_LADD:
                        !x y z. (x + y) < (x + z) <=> y < z
Proof
                        ARITH_TAC
QED

Theorem LT_ADDL:
                        !x y. x < (x + y) <=> 0 < y
Proof
                        ARITH_TAC
QED

Theorem LT_ADDR:
                        !x y. ~((x + y) < x)
Proof
                        ARITH_TAC
QED

Theorem LT_ADD2:
              !x1 x2 y1 y2. x1 < y1 /\ x2 < y2 ==> (x1 + x2) < (y1 + y2)
Proof
                  ARITH_TAC
QED

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
          if (rator(rator tm) ~~ binop handle _ => false) then
              (strip_binop (rand(rator tm))) @ (strip_binop(rand tm))
          else [tm]
      val mk_binop = ((curry mk_comb) o (curry mk_comb binop))
      val list_mk_binop = end_itlist mk_binop

      fun rmel i list = op_set_diff aconv list [i]

      val (_, (l1, r1)) =
          (assert (aconv eqop) ## pair_from_list) (strip_comb tm)
      val (l, r) = pair_from_list (map strip_binop [l1, r1])
      val i = op_intersect aconv l r
  in
      if null i then raise Fail ""
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

Definition tint_0[nocompute]:
                            tint_0 = (1,1)
End

Definition tint_1[nocompute]:
                            tint_1 = (1 + 1,1)
End

Definition tint_neg[nocompute]:
                              tint_neg (x:num,(y:num)) = (y,x)
End

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

Definition tint_lt[nocompute]:
  $tint_lt (x1,y1) (x2,y2) <=> (x1 + y2) < (x2 + y1)
End
val _ = temp_set_fixity "tint_lt" (Infix(NONASSOC, 450))

(*--------------------------------------------------------------------------*)
(* Define the equivalence relation and prove it *is* one                    *)
(*--------------------------------------------------------------------------*)

val _ = print "Define equivalence relation over pairs of naturals\n"

Definition tint_eq[nocompute]:
  $tint_eq (x1,y1) (x2,y2) = (x1 + y2 = x2 + y1)
End
val _ = temp_set_fixity "tint_eq" (Infix(NONASSOC, 450));

Theorem TINT_EQ_REFL:
              !x. x tint_eq x
Proof
              GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
QED

Theorem TINT_EQ_SYM:
              !x y. x tint_eq y <=> y tint_eq x
Proof
              REPEAT GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
                                  THEN ARITH_TAC
QED

Theorem TINT_EQ_TRANS:
              !x y z. x tint_eq y /\ y tint_eq z ==> x tint_eq z
Proof
                  REPEAT GEN_PAIR_TAC THEN REWRITE_TAC[tint_eq]
                                  THEN ARITH_TAC
QED

Theorem TINT_EQ_EQUIV:
  !p q. p tint_eq q <=> ($tint_eq p = $tint_eq q)
Proof
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV (Term `r:num#num`))) THEN EQ_TAC
  THENL
  [DISCH_THEN(MP_TAC o SPEC (Term `q:num#num`)) THEN REWRITE_TAC[TINT_EQ_REFL],
   DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TINT_EQ_SYM]), ALL_TAC] THEN
   POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
   MATCH_ACCEPT_TAC TINT_EQ_TRANS]
QED

Theorem TINT_EQ_AP:
              !p q. (p = q) ==> p tint_eq q
Proof
                  REPEAT GEN_PAIR_TAC
                  THEN REWRITE_TAC[tint_eq,pairTheory.PAIR_EQ]
                  THEN ARITH_TAC
QED

(*--------------------------------------------------------------------------*)
(* Prove the properties of representatives                                  *)
(*--------------------------------------------------------------------------*)

val _ = print "Proving various properties of pairs of naturals\n"

Theorem TINT_10:
              ~(tint_1 tint_eq tint_0)
Proof
              REWRITE_TAC[tint_1, tint_0, tint_eq]
              THEN ARITH_TAC
QED

Theorem TINT_ADD_SYM:
              !y x. x tint_add y = y tint_add x
Proof
              REPEAT GEN_PAIR_TAC
              THEN REWRITE_TAC[tint_eq,tint_add,pairTheory.PAIR_EQ]
              THEN ARITH_TAC
QED

Theorem TINT_MUL_SYM:
              !y x. x tint_mul y = y tint_mul x
Proof
              REPEAT GEN_PAIR_TAC
              THEN REWRITE_TAC[tint_eq,tint_mul,pairTheory.PAIR_EQ]
              THEN SIMP_TAC int_ss [MULT_SYM]
QED

Theorem TINT_ADD_ASSOC:
     !z y x. x tint_add (y tint_add z) = (x tint_add y) tint_add z
Proof
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,pairTheory.PAIR_EQ,ADD_ASSOC]
QED

Theorem TINT_MUL_ASSOC:
     !z y x. x tint_mul (y tint_mul z) = (x tint_mul y) tint_mul z
Proof
     REPEAT GEN_PAIR_TAC
     THEN
     REWRITE_TAC[tint_mul, pairTheory.PAIR_EQ, LEFT_ADD_DISTRIB,
                 RIGHT_ADD_DISTRIB]
     THEN
     SIMP_TAC int_ss [MULT_ASSOC]
QED

Theorem TINT_LDISTRIB:
     !z y x. x tint_mul (y tint_add z) =
                   (x tint_mul y) tint_add (x tint_mul z)
Proof
     REPEAT GEN_PAIR_TAC THEN
     REWRITE_TAC[tint_mul, tint_add,pairTheory.PAIR_EQ, LEFT_ADD_DISTRIB]
     THEN CANCEL_TAC
QED

Theorem TINT_ADD_LID:
     !x. (tint_0 tint_add x) tint_eq x
Proof
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,tint_0,tint_eq]
     THEN ARITH_TAC
QED

Theorem TINT_MUL_LID:
     !x. (tint_1 tint_mul x) tint_eq x
Proof
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_mul,tint_1,tint_eq]
     THEN ARITH_TAC
QED

Theorem TINT_ADD_LINV:
     !x. ((tint_neg x) tint_add x) tint_eq tint_0
Proof
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_add,tint_0,tint_eq,tint_neg]
     THEN ARITH_TAC
QED

Theorem TINT_LT_TOTAL:
     !x y. x tint_eq y \/ x tint_lt y \/ y tint_lt x
Proof
     REPEAT GEN_PAIR_TAC
     THEN REWRITE_TAC[tint_lt,tint_eq]
     THEN ARITH_TAC
QED

Theorem TINT_LT_REFL:
              !x. ~(x tint_lt x)
Proof
              REPEAT GEN_PAIR_TAC
              THEN REWRITE_TAC[tint_lt]
              THEN ARITH_TAC
QED

fun unfold_dec l = REPEAT GEN_PAIR_TAC THEN REWRITE_TAC l THEN ARITH_TAC;

Theorem TINT_LT_TRANS:
     !x y z. x tint_lt y /\ y tint_lt z ==> x tint_lt z
Proof
     unfold_dec[tint_lt]
QED


Theorem TINT_LT_ADD:
     !x y z. (y tint_lt z) ==> (x tint_add y) tint_lt (x tint_add z)
Proof
     unfold_dec[tint_lt,tint_add]
QED

Theorem TINT_LT_MUL:
     !x y. tint_0 tint_lt x /\ tint_0 tint_lt y ==>
            tint_0 tint_lt (x tint_mul y)
Proof
     REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_0, tint_lt, tint_mul] THEN
     CANCEL_TAC THEN DISCH_THEN(CONJUNCTS_THEN
                      (CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1))
     THEN  SIMP_TAC int_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
QED

(*--------------------------------------------------------------------------*)
(* Prove that the operations on representatives are well-defined            *)
(*--------------------------------------------------------------------------*)

Theorem TINT_NEG_WELLDEF:
     !x1 x2. x1 tint_eq x2 ==> (tint_neg x1) tint_eq (tint_neg x2)
Proof
     unfold_dec[tint_eq,tint_neg]
QED

Theorem TINT_ADD_WELLDEFR:
     !x1 x2 y. x1 tint_eq x2 ==> (x1 tint_add y) tint_eq (x2 tint_add y)
Proof
     unfold_dec[tint_eq,tint_add]
QED

Theorem TINT_ADD_WELLDEF:
     !x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
         (x1 tint_add y1) tint_eq (x2 tint_add y2)
Proof
     unfold_dec[tint_eq,tint_add]
QED

Theorem TINT_MUL_WELLDEFR:
     !x1 x2 y. x1 tint_eq x2 ==> (x1 tint_mul y) tint_eq (x2 tint_mul y)
Proof
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_mul, tint_eq] THEN
  ONCE_REWRITE_TAC[jrhUtils.AC(ADD_ASSOC,ADD_SYM)
    (Term `(a + b) + (c + d) =
           (a + d) + (b + c)`)] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC
QED

Theorem TINT_MUL_WELLDEF:
     !x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
         (x1 tint_mul y1) tint_eq (x2 tint_mul y2)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TINT_EQ_TRANS THEN EXISTS_TAC (Term `x1 tint_mul y2`) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TINT_MUL_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TINT_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]
QED

Theorem TINT_LT_WELLDEFR:
     !x1 x2 y. x1 tint_eq x2 ==> (x1 tint_lt y <=> x2 tint_lt y)
Proof
     unfold_dec[tint_eq,tint_lt]
QED

Theorem TINT_LT_WELLDEFL:
     !x y1 y2. y1 tint_eq y2 ==> (x tint_lt y1 <=> x tint_lt y2)
Proof
     unfold_dec[tint_eq,tint_lt]
QED

Theorem TINT_LT_WELLDEF:
     !x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
         (x1 tint_lt y1 <=> x2 tint_lt y2)
Proof
     unfold_dec[tint_eq,tint_lt]
QED

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

Theorem tint_of_num_eq:
              !n. FST (tint_of_num n) = SND (tint_of_num n) + n
Proof
              INDUCT_TAC
              THENL
                [ SIMP_TAC int_ss [tint_of_num,tint_0],

                  REWRITE_TAC [tint_of_num]
                  THEN ONCE_REWRITE_TAC [tint_of_num_PAIR]
                  THEN ASM_REWRITE_TAC [tint_1,tint_add]
                  THEN SIMP_TAC int_ss []
                ]
QED

Theorem TINT_INJ:
              !m n. (tint_of_num m tint_eq tint_of_num n) = (m = n)
Proof
              INDUCT_TAC THEN INDUCT_TAC
              THEN REPEAT (POP_ASSUM MP_TAC)
              THEN REWRITE_TAC [tint_of_num]
              THEN ONCE_REWRITE_TAC [tint_of_num_PAIR]
              THEN REWRITE_TAC [tint_0,tint_1,tint_add,tint_eq,tint_of_num_eq]
              THEN SIMP_TAC int_ss []
QED

Theorem NUM_POSTINT_EX:
              !t. ~(t tint_lt tint_0) ==> ?n. t tint_eq tint_of_num n
Proof
                  GEN_TAC THEN DISCH_TAC THEN
                  Q.EXISTS_TAC `FST t - SND t`
                   THEN POP_ASSUM MP_TAC
                   THEN ONCE_REWRITE_TAC [GSYM pairTheory.PAIR]
                   THEN REWRITE_TAC [tint_0,tint_lt,tint_eq,tint_of_num_eq]
                   THEN SIMP_TAC int_ss []
QED

(*--------------------------------------------------------------------------*)
(* Now define the functions over the equivalence classes                    *)
(*--------------------------------------------------------------------------*)

val _ = print "Establish type of integers\n";

local
    fun mk_def (d,t,n) = {def_name=d, fixity=NONE, fname=n, func=t}
in
    val [INT_10, INT_ADD_SYM, INT_MUL_SYM,
         INT_ADD_ASSOC, INT_MUL_ASSOC, INT_LDISTRIB,
         INT_ADD_LID, INT_MUL_LID, INT_ADD_LINV,
         INT_LT_TOTAL, INT_LT_REFL, INT_LT_TRANS,
         INT_LT_LADD_IMP, INT_LT_MUL,
         int_of_num, INT_INJ, NUM_POSINT_EX] =
        define_equivalence_type
        {name = "int", equiv = TINT_EQ_EQUIV,
         defs = [mk_def ("int_0"      , “tint_0”,      "int_0"),
                 mk_def ("int_1"      , “tint_1”,      "int_1"),
                 mk_def ("int_neg"    , “tint_neg”,    "int_neg"),
                 mk_def ("int_add"    , “$tint_add”,   "int_add"),
                 mk_def ("int_mul"    , “$tint_mul”,   "int_mul"),
                 mk_def ("int_lt"     , “$tint_lt”,    "int_lt"),
                 mk_def ("int_of_num" , “tint_of_num”, "int_of_num")],

         welldefs = [TINT_NEG_WELLDEF, TINT_LT_WELLDEF,
                     TINT_ADD_WELLDEF, TINT_MUL_WELLDEF],
         old_thms = ([TINT_10, TINT_ADD_SYM, TINT_MUL_SYM, TINT_ADD_ASSOC,
                      TINT_MUL_ASSOC, TINT_LDISTRIB,
                      TINT_ADD_LID, TINT_MUL_LID, TINT_ADD_LINV,
                      TINT_LT_TOTAL, TINT_LT_REFL, TINT_LT_TRANS,
                      TINT_LT_ADD, TINT_LT_MUL, tint_of_num,
                      TINT_INJ, NUM_POSTINT_EX])}
end;

Theorem INT_10 = INT_10
Theorem INT_ADD_SYM = INT_ADD_SYM
Theorem INT_ADD_COMM = INT_ADD_SYM;
Theorem INT_MUL_SYM = INT_MUL_SYM
Theorem INT_MUL_COMM = INT_MUL_SYM;
Theorem INT_ADD_ASSOC = INT_ADD_ASSOC
Theorem INT_MUL_ASSOC = INT_MUL_ASSOC
Theorem INT_LDISTRIB = INT_LDISTRIB
Theorem INT_LT_TOTAL = INT_LT_TOTAL
Theorem INT_LT_REFL = INT_LT_REFL
Theorem INT_LT_TRANS = INT_LT_TRANS
Theorem INT_LT_LADD_IMP = INT_LT_LADD_IMP
Theorem INT_LT_MUL = INT_LT_MUL
Theorem NUM_POSINT_EX = NUM_POSINT_EX
;

val _ = overload_on ("+", Term`int_add`);
val _ = overload_on ("<", Term`int_lt`);
val _ = overload_on ("*", Term`int_mul`);


(* this is a slightly tricky case; we don't have to call overload_on
   on the boolean negation, but we're doing so to put it back at the
   top of the list of possible resolutions.

   Also need to overload from the Unicode negation in order to make that
   preferred over the tilde.

*)

val bool_not = “$~ : bool -> bool”
Overload "~" = “int_neg”
Overload "~" = bool_not
Overload numeric_negate = “int_neg”
Overload "¬" = bool_not

(*--------------------------------------------------------------------------*)
(* Define subtraction and the other orderings                               *)
(*--------------------------------------------------------------------------*)

val int_sub =
    new_infixl_definition("int_sub",
                         Term `$int_sub x y = x + ~y`,
                         500);
val _ = overload_on ("-",  Term`$int_sub`);

Definition int_le[nocompute]: int_le x y = ~(y<x:int)
End
val _ = overload_on ("<=", Term`$int_le`);

Definition int_gt[nocompute]: int_gt (x:int) y <=> y < x
End
val _ = overload_on (">",  Term`$int_gt`);

Definition int_ge[nocompute]: int_ge x y <=> y <= x:int
End
val _ = overload_on (">=", Term`$int_ge`);

Theorem INT_GT = int_gt (* HOL-Light compatible name *)
Theorem INT_GE = int_ge (* HOL-Light compatible name *)

(*--------------------------------------------------------------------------*)
(* Now use the lifted inclusion homomorphism int_of_num:num->int.           *)
(*--------------------------------------------------------------------------*)

val _ = add_numeral_form(#"i", SOME "int_of_num");

Theorem INT_0:
              int_0 = 0i
Proof
              REWRITE_TAC[int_of_num]
QED

Theorem INT_1:
              int_1 = 1i
Proof
              REWRITE_TAC[ONE, int_of_num, INT_ADD_LID]
QED

(*--------------------------------------------------------------------------*)
(* Prove lots of boring ring theorems                                       *)
(*--------------------------------------------------------------------------*)

val _ = print "Prove \"lots of boring ring theorems\"\n";

(* already defined, but using the wrong term for 0 *)
Theorem INT_ADD_LID:
              !x:int. 0 + x = x
Proof
              SIMP_TAC int_ss [GSYM INT_0, INT_ADD_LID]
QED
val _ = export_rewrites ["INT_ADD_LID"]


Theorem INT_ADD_RID:
              !x:int. x + 0 = x
Proof
              PROVE_TAC [INT_ADD_COMM,INT_ADD_LID]
QED
val _ = export_rewrites ["INT_ADD_RID"]


(* already defined, but using the wrong term for 0 *)
Theorem INT_ADD_LINV[simp]: !x. ~x + x = 0
Proof SIMP_TAC int_ss [GSYM INT_0, INT_ADD_LINV]
QED
Theorem INT_ADD_RINV[simp]:
  !x. x + ~x = 0
Proof
  ONCE_REWRITE_TAC [INT_ADD_SYM] THEN REWRITE_TAC [INT_ADD_LINV]
QED

(* already defined, but using the wrong term for 1 *)
Theorem INT_MUL_LID[simp]: !x:int. 1 * x = x
Proof
  SIMP_TAC int_ss [GSYM INT_1, INT_MUL_LID]
QED

Theorem INT_MUL_RID[simp]: !x:int. x * 1 = x
Proof PROVE_TAC [INT_MUL_SYM,GSYM INT_1,INT_MUL_LID]
QED

Theorem INT_RDISTRIB:
              !(x:int) y z. (x + y) * z = (x * z) + (y * z)
Proof
              ONCE_REWRITE_TAC [INT_MUL_COMM] THEN
              REWRITE_TAC [INT_LDISTRIB]
QED

Theorem INT_EQ_LADD:
              !(x:int) y z. (x + y = x + z) = (y = z)
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [DISCH_THEN(MP_TAC o AP_TERM (Term `$+ ~x`)), ALL_TAC] THEN
              SIMP_TAC int_ss [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID]
QED


Theorem INT_EQ_RADD:
              !x:int y z. (x + z = y + z) = (x = y)
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              SIMP_TAC int_ss [INT_EQ_LADD]
QED

Theorem INT_ADD_LID_UNIQ:
              !x:int y. (x + y = y) = (x = 0)
Proof
              REPEAT GEN_TAC THEN
              GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                empty_rewrites [GSYM INT_ADD_LID]
              THEN SIMP_TAC int_ss [INT_EQ_RADD]
QED

Theorem INT_ADD_RID_UNIQ:
              !x:int y. (x + y = x) = (y = 0)
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              SIMP_TAC int_ss [INT_ADD_LID_UNIQ]
QED

Theorem INT_LNEG_UNIQ:
     !x y. (x + y = 0) = (x = ~y)
Proof
     REPEAT GEN_TAC
     THEN SUBST1_TAC (SYM(SPEC (Term `y:int`) INT_ADD_LINV))
     THEN SIMP_TAC int_ss [INT_EQ_RADD]
QED

Theorem INT_RNEG_UNIQ:
              !x y. (x + y = 0) = (y = ~x)
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              SIMP_TAC int_ss [INT_LNEG_UNIQ]
QED

Theorem INT_NEG_ADD:
              !x y. ~(x + y) = ~x + ~y
Proof
              REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
              REWRITE_TAC[GSYM INT_LNEG_UNIQ] THEN
              ONCE_REWRITE_TAC
              [jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
               (Term `(a + b) + (c + d) = (a + c) + (b + d:int)`)] THEN
              REWRITE_TAC[INT_ADD_LINV, INT_ADD_RID,INT_0]
QED

Theorem INT_MUL_LZERO:
              !x:int. 0 * x = 0
Proof
              GEN_TAC THEN SUBST1_TAC
              (SYM(Q.SPECL [`0 * x`, `0 * x`] INT_ADD_LID_UNIQ))
              THEN REWRITE_TAC[GSYM INT_RDISTRIB, INT_ADD_RID]
QED
val _ = export_rewrites ["INT_MUL_LZERO"]

Theorem INT_MUL_RZERO:
                !x. x * 0i = 0
Proof
                GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
                SIMP_TAC int_ss [INT_MUL_LZERO]
QED
val _ = export_rewrites ["INT_MUL_RZERO"]

Theorem INT_NEG_LMUL:
              !x y. ~(x * y) = ~x * y
Proof
              REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
              REWRITE_TAC[GSYM INT_LNEG_UNIQ, GSYM INT_RDISTRIB,
              INT_ADD_LINV, INT_MUL_LZERO,INT_0]
QED

(* |- !x y. -x * y = -(x * y) *)
Theorem INT_MUL_LNEG = GSYM INT_NEG_LMUL (* HOL-Light compatible *)

Theorem INT_NEG_RMUL:
              !x y. ~(x * y) = x * ~y
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
              SIMP_TAC int_ss [INT_NEG_LMUL]
QED

(* |- !x y. x * -y = -(x * y) *)
Theorem INT_MUL_RNEG = GSYM INT_NEG_RMUL (* HOL-Light compatible *)

Theorem INT_NEGNEG[simp]:
  !x:int. ~~x = x
Proof
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM INT_LNEG_UNIQ, INT_ADD_RINV]
QED

Theorem INT_NEG_NEG = INT_NEGNEG (* HOL-Light compatible name *)

Theorem INT_NEG_MUL2:
              !x y. ~x * ~y = x * y
Proof
              REWRITE_TAC[GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG]
QED

Theorem INT_LT_LADD:
              !x:int y z. x + y < x + z <=> y < z
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [DISCH_THEN(MP_TAC o (SPEC (Term `~x:int`)) o
                          MATCH_MP INT_LT_LADD_IMP)
               THEN
               REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID],
               SIMP_TAC int_ss [INT_LT_LADD_IMP]]
QED

Theorem INT_LT_RADD:
    !x:int y z. (x + z) < (y + z) <=> x < y
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              SIMP_TAC int_ss [INT_LT_LADD]
QED

Theorem INT_NOT_LT:
    !x:int y. ~(x < y) <=> y <= x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le]
QED

(* NOTE: This is INT_LT of HOL-Light *)
Theorem INT_LT2 :
    !x (y :int). x < y <=> ~(y <= x)
Proof
    REWRITE_TAC [GSYM INT_NOT_LT]
QED

Theorem INT_LT_ANTISYM:
              !x:int y. ~(x < y /\ y < x)
Proof
              REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_TRANS)
              THEN REWRITE_TAC[INT_LT_REFL]
QED

Theorem INT_LT_GT:
              !x:int y. x < y ==> ~(y < x)
Proof
              REPEAT GEN_TAC THEN
              DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
              REWRITE_TAC[INT_LT_ANTISYM]
QED

Theorem INT_NOT_LE:
    !x y:int. ~(x <= y) <=> y < x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le]
QED

Theorem INT_LE_TOTAL:
              !x y:int. x <= y \/ y <= x
Proof
              REPEAT GEN_TAC THEN
              REWRITE_TAC[int_le, GSYM DE_MORGAN_THM, INT_LT_ANTISYM]
QED

Theorem INT_LET_TOTAL:
              !x y:int. x <= y \/ y < x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
              SIMP_TAC int_ss []
QED

Theorem INT_LTE_TOTAL:
              !x y:int. x < y \/ y <= x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
              SIMP_TAC int_ss []
QED


Theorem INT_LE_REFL[simp]: !x:int. x <= x
Proof GEN_TAC THEN REWRITE_TAC[int_le, INT_LT_REFL]
QED

Theorem INT_LE_LT:
    !x y:int. x <= y <=> x < y \/ (x = y)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [Term `x:int`, Term `y:int`] INT_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry(op THEN) (MATCH_MP_TAC INT_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC INT_LT_REFL]
QED

Theorem INT_LT_LE:
    !x y:int. x < y <=> x <= y /\ ~(x = y)
Proof
     let val lemma = TAUT_CONV (Term `~(a /\ ~a)`)
     in
         REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, RIGHT_AND_OVER_OR, lemma]
         THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
         POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
         DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LT_REFL]
     end
QED

Theorem INT_LT_IMP_LE:
              !x y:int. x < y ==> x <= y
Proof
                  REPEAT GEN_TAC THEN DISCH_TAC THEN
                  ASM_REWRITE_TAC[INT_LE_LT]
QED

Theorem INT_LTE_TRANS:
              !x y z:int. x < y /\ y <= z ==> x < z
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, LEFT_AND_OVER_OR] THEN
              DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
                         (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC))
                         THEN REWRITE_TAC[]
QED

Theorem INT_LET_TRANS:
              !x y z:int. x <= y /\ y < z ==> x < z
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT, RIGHT_AND_OVER_OR]
              THEN
              DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
                         (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC))
QED

Theorem INT_LE_TRANS:
              !x y z:int. x <= y /\ y <= z ==> x <= z
Proof
              REPEAT GEN_TAC THEN
              GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites
                [INT_LE_LT] THEN
              DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
                         (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
              THEN REWRITE_TAC[]
              THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME (Term `y < z:int`))) THEN
              DISCH_THEN(ACCEPT_TAC o MATCH_MP
                         INT_LT_IMP_LE o MATCH_MP INT_LET_TRANS)
QED

Theorem INT_LE_ANTISYM:
    !x y:int. x <= y /\ y <= x <=> (x = y)
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [REWRITE_TAC[int_le] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
               (SPECL [Term `x:int`, Term `y:int`] INT_LT_TOTAL) THEN
               ASM_REWRITE_TAC[],
               DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LE_REFL]]
QED

Theorem INT_LET_ANTISYM:
              !x y:int. ~(x < y /\ y <= x)
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
              BOOL_CASES_TAC (Term `x < y:int`) THEN REWRITE_TAC[]
QED

Theorem INT_LTE_ANTSYM:
              !x y:int. ~(x <= y /\ y < x)
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
              MATCH_ACCEPT_TAC INT_LET_ANTISYM
QED

Theorem INT_NEG_LT0:
    !x. ~x < 0 <=> 0 < x
Proof
              GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`~x`, `0`,`x`] INT_LT_RADD)) THEN
              REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID]
QED

Theorem INT_NEG_GT0:
    !x. 0 < ~x <=> x < 0
Proof         GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LT0, INT_NEGNEG]
QED

Theorem INT_NEG_LE0:
    !x. ~x <= 0 <=> 0 <= x
Proof         GEN_TAC THEN REWRITE_TAC[int_le] THEN
              REWRITE_TAC[INT_NEG_GT0]
QED

Theorem INT_NEG_GE0:
    !x. 0 <= ~x <=> x <= 0
Proof
              GEN_TAC THEN REWRITE_TAC[int_le] THEN
              REWRITE_TAC[INT_NEG_LT0]
QED

Theorem INT_LT_NEGTOTAL:
    !x. (x = 0) \/ 0<x \/ 0 < ~x
Proof
              GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
              (Q.SPECL [`x`, `0`] INT_LT_TOTAL) THEN
              ASM_REWRITE_TAC
              [SYM(REWRITE_RULE[INT_NEGNEG] (Q.SPEC `~x` INT_NEG_LT0))]
QED

Theorem INT_LE_NEGTOTAL:
     !x. 0 <= x \/ 0 <= ~x
Proof
     GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
     REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC (Term `x:int`)
                                            INT_LT_NEGTOTAL)
     THEN ASM_REWRITE_TAC[]
QED

Theorem INT_LE_MUL:
     !x y:int. 0 <= x /\ 0 <= y ==> 0 <= x*y
Proof
         REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
         MAP_EVERY ASM_CASES_TAC [Term `0i = x`, Term `0i = y`] THEN
         ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
         REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO] THEN
         DISCH_TAC THEN DISJ1_TAC
         THEN MATCH_MP_TAC (REWRITE_RULE [INT_0] INT_LT_MUL) THEN
         ASM_REWRITE_TAC[]
QED

Theorem INT_LE_SQUARE:
              !x:int. 0 <= x * x
Proof
              GEN_TAC THEN DISJ_CASES_TAC (SPEC (Term `x:int`) INT_LE_NEGTOTAL)
              THEN
              POP_ASSUM(MP_TAC o MATCH_MP INT_LE_MUL o W CONJ) THEN
              REWRITE_TAC[GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL, INT_NEGNEG]
QED

Theorem INT_LE_01:
              0i <= 1
Proof
              SUBST1_TAC(SYM(Q.SPEC `1` INT_MUL_LID)) THEN
              SIMP_TAC int_ss [INT_LE_SQUARE,INT_1]
QED

Theorem INT_LT_01:
              0i < 1i
Proof
              SIMP_TAC int_ss [INT_LT_LE, INT_LE_01,
                               GSYM INT_0,GSYM INT_1,INT_10]
QED

Theorem INT_LE_LADD:
    !x:int y z. x + y <= x + z <=> y <= z
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
              AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_LADD
QED

Theorem INT_LE_RADD:
    !x y z:int. (x + z) <= (y + z) <=> x <= y
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
              AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_RADD
QED

Theorem INT_LT_ADD2:
              !w x y z:int. w < x /\ y < z ==> w + y < x + z
Proof
              REPEAT GEN_TAC THEN DISCH_TAC THEN
              MATCH_MP_TAC INT_LT_TRANS THEN EXISTS_TAC (Term `w + z:int`) THEN
              ASM_REWRITE_TAC[INT_LT_LADD, INT_LT_RADD]
QED

Theorem INT_LE_ADD2:
              !w x y z:int. w <= x /\ y <= z ==> w + y <= x + z
Proof
              REPEAT GEN_TAC THEN DISCH_TAC THEN
              MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (Term `w + z:int`) THEN
              ASM_REWRITE_TAC[INT_LE_LADD, INT_LE_RADD]
QED

Theorem INT_LE_ADD:
              !x y:int. 0 <= x /\ 0 <= y ==> 0 <= (x + y)
Proof
              REPEAT GEN_TAC
              THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2) THEN
              REWRITE_TAC[INT_ADD_LID]
QED

Theorem INT_LT_ADD:
              !x y:int. 0 < x /\ 0 < y ==> 0 < (x + y)
Proof
              REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2)
              THEN
              REWRITE_TAC[INT_ADD_LID]
QED

Theorem INT_LT_ADDNEG:
    !x y z. y < x + ~z <=> y+z < x
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(SPECL [Term `y:int`,
                                    Term `x + ~z`,
                                    Term `z:int`] INT_LT_RADD)) THEN
              REWRITE_TAC[GSYM INT_ADD_ASSOC, INT_ADD_LINV,
                          INT_ADD_RID, INT_0]
QED

(* REWRITE TO *)
Theorem INT_LT_ADDNEG2:
    !x y z. x + ~y < z <=> x < z+y
Proof
     REPEAT GEN_TAC THEN
     SUBST1_TAC
       (SYM(SPECL [Term `x + ~y`, Term `z:int`,Term `y:int`] INT_LT_RADD)) THEN
     REWRITE_TAC[GSYM INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_RID,INT_0]
QED

Theorem INT_LT_ADD1:
              !x y:int. x <= y ==> x < (y + 1)
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
              DISCH_THEN DISJ_CASES_TAC THENL
              [POP_ASSUM(MP_TAC o MATCH_MP INT_LT_ADD2 o C CONJ INT_LT_01)
               THEN
               REWRITE_TAC[INT_ADD_RID],
               POP_ASSUM SUBST1_TAC THEN
               GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM INT_ADD_RID] THEN
               REWRITE_TAC[INT_LT_LADD, INT_LT_01]]
QED

Theorem INT_SUB_ADD:
              !x y:int. (x - y) + y = x
Proof
              REPEAT GEN_TAC THEN
              REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
                      INT_ADD_LINV, INT_ADD_RID,INT_0]
QED

Theorem INT_SUB_ADD2:
              !x y:int. y + (x - y) = x
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              MATCH_ACCEPT_TAC INT_SUB_ADD
QED

Theorem INT_SUB_REFL:
              !x:int. x - x = 0
Proof
              GEN_TAC THEN REWRITE_TAC[int_sub, INT_ADD_RINV]
QED

Theorem INT_SUB_0:
              !x y:int. (x - y = 0) = (x = y)
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [DISCH_THEN(MP_TAC o C AP_THM (Term `y:int`) o
                          AP_TERM (Term `$+ :int->int->int`)) THEN
               REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID],
               DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC INT_SUB_REFL]
QED

Theorem INT_LE_DOUBLE:
    !x:int. 0 <= x + x <=> 0 <= x
Proof
              GEN_TAC THEN EQ_TAC THENL
              [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[INT_NOT_LE] THEN
               DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2 o W CONJ)
               THEN REWRITE_TAC [INT_ADD_RID],
               DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2 o W CONJ)] THEN
              REWRITE_TAC[INT_ADD_RID]
QED

Theorem INT_LE_NEGL:
    !x. ~x <= x <=> 0 <= x
Proof
              GEN_TAC THEN SUBST1_TAC (SYM
                (SPECL [Term `x:int`,Term `~x:int`, Term `x:int`]INT_LE_LADD))
              THEN REWRITE_TAC[INT_ADD_RINV, INT_LE_DOUBLE]
QED

Theorem INT_LE_NEGR:
    !x. x <= ~x <=> x <= 0
Proof
              GEN_TAC THEN SUBST1_TAC(SYM(SPEC (Term `x:int`) INT_NEGNEG)) THEN
              GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                empty_rewrites [INT_NEGNEG] THEN
              REWRITE_TAC[INT_LE_NEGL] THEN REWRITE_TAC[INT_NEG_GE0] THEN
              REWRITE_TAC[INT_NEGNEG]
QED

Theorem INT_NEG_EQ0:
              !x. (~x = 0) = (x = 0)
Proof
GEN_TAC THEN EQ_TAC THENL
[DISCH_THEN(MP_TAC o AP_TERM (Term `$+ x:int->int`))
   THEN REWRITE_TAC[INT_ADD_RINV, INT_ADD_LINV, INT_ADD_RID, INT_0]
   THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC,
 DISCH_THEN(MP_TAC o AP_TERM (Term `$+ (~x)`))
   THEN REWRITE_TAC[INT_ADD_RINV, INT_ADD_LINV, INT_ADD_RID, INT_0]
   THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]
QED

Theorem INT_NEG_0[simp]:  ~0 = 0
Proof REWRITE_TAC[INT_NEG_EQ0]
QED

Theorem INT_NEG_SUB:
              !x y. ~(x - y) = y - x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub,
                                              INT_NEG_ADD, INT_NEGNEG] THEN
              MATCH_ACCEPT_TAC INT_ADD_SYM
QED

Theorem INT_SUB_LT:
    !x:int y. 0 < x - y <=> y < x
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`0`, `x - y`, `y`] INT_LT_RADD)) THEN
              REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID]
QED

Theorem INT_SUB_LE:
    !x:int y. 0 <= (x - y) <=> y <= x
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`0`, `x - y`, `y`] INT_LE_RADD)) THEN
              REWRITE_TAC[INT_SUB_ADD, INT_ADD_LID]
QED

Theorem INT_ADD_SUB:
              !x y:int. (x + y) - x = y
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
                          INT_ADD_RINV, INT_ADD_RID, INT_0]
QED

Theorem INT_SUB_LDISTRIB:
              !x y z:int. x * (y - z) = (x * y) - (x * z)
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub,
                                              INT_LDISTRIB, INT_NEG_RMUL]
QED

Theorem INT_SUB_RDISTRIB:
              !x y z:int. (x - y) * z = (x * z) - (y * z)
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
              MATCH_ACCEPT_TAC INT_SUB_LDISTRIB
QED

Theorem INT_NEG_EQ:
              !x y:int. (~x = y) = (x = ~y)
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN
              REWRITE_TAC[INT_NEGNEG]
QED

Theorem INT_NEG_MINUS1:
              !x. ~x = ~1 * x
Proof
              GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LMUL] THEN
              REWRITE_TAC[INT_MUL_LID,GSYM INT_1]
QED


Theorem INT_LT_IMP_NE:
              !x y:int. x < y ==> ~(x = y)
Proof
                  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
                  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
                  REWRITE_TAC[INT_LT_REFL]
QED

Theorem INT_NOT_EQ :
    !x y. ~(x = y) <=> x < y \/ y < x
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >- PROVE_TAC [INT_LT_TOTAL]
 >> PROVE_TAC [INT_LT_IMP_NE]
QED

Theorem INT_LE_ADDR:
    !x y:int. x <= x + y <=> 0 <= y
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`x`, `0`, `y`] INT_LE_LADD)) THEN
              REWRITE_TAC[INT_ADD_RID,INT_0]
QED

Theorem INT_LE_ADDL:
    !x y:int. y <= x + y <=> 0 <= x
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              MATCH_ACCEPT_TAC INT_LE_ADDR
QED

Theorem INT_LT_ADDR:
    !x y:int. x < x + y <=> 0 < y
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`x`, `0`,`y`] INT_LT_LADD)) THEN
              REWRITE_TAC[INT_ADD_RID,INT_0]
QED

Theorem INT_LT_ADDL:
    !x y:int. y < x + y <=> 0 < x
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              MATCH_ACCEPT_TAC INT_LT_ADDR
QED

Theorem INT_ENTIRE:
    !x y:int. (x * y = 0) <=> (x = 0) \/ (y = 0)
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
               STRIP_TAC THEN
               REPEAT_TCL DISJ_CASES_THEN MP_TAC
                             (SPEC (Term `x:int`) INT_LT_NEGTOTAL) THEN
               ASM_REWRITE_TAC[] THEN
               REPEAT_TCL DISJ_CASES_THEN MP_TAC
                             (SPEC (Term `y:int`) INT_LT_NEGTOTAL) THEN
               ASM_REWRITE_TAC[] THEN
               REWRITE_TAC[TAUT_CONV (Term `a ==> b ==> c <=> b /\ a ==> c`)]
               THEN
               DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE [INT_0] INT_LT_MUL))
               THEN
               REWRITE_TAC[GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL] THEN
               CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[INT_NEGNEG] THEN
               DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LT_REFL,INT_NEG_GT0],
               DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
               REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO]]
QED

Theorem INT_EQ_LMUL:
    !x y z:int. (x * y = x * z) <=> (x = 0) \/ (y = z)
Proof
              REPEAT GEN_TAC THEN
              GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM INT_SUB_0] THEN
              REWRITE_TAC[GSYM INT_SUB_LDISTRIB] THEN
              REWRITE_TAC[INT_ENTIRE, INT_SUB_0]
QED

Theorem INT_EQ_RMUL:
    !x y z:int. (x * z = y * z) <=> (z = 0) \/ (x = y)
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
              MATCH_ACCEPT_TAC INT_EQ_LMUL
QED


(*--------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                *)
(*--------------------------------------------------------------------------*)

val _ = print "Prove homomorphisms for the inclusion map\n"

Theorem INT:
              !n. &(SUC n) = &n + 1i
Proof
              GEN_TAC THEN REWRITE_TAC[int_of_num] THEN
              REWRITE_TAC[INT_1]
QED

Theorem INT_POS:
              !n. 0i <= &n
Proof
              INDUCT_TAC THEN REWRITE_TAC[INT_LE_REFL] THEN
              MATCH_MP_TAC INT_LE_TRANS THEN
              EXISTS_TAC (Term `&n:int`) THEN ASM_REWRITE_TAC[INT] THEN
              REWRITE_TAC[INT_LE_ADDR, INT_LE_01]
QED

Theorem INT_LE:
    !m n. &m:int <= &n <=> m <= n
Proof
              REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
              [INT, INT_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, INT_LE_REFL] THEN
              REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
              [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (Term `&n:int`) THEN
               ASM_REWRITE_TAC[ZERO_LESS_EQ, INT_LE_ADDR, INT_LE_01],
               DISCH_THEN(MP_TAC o C CONJ (SPEC (Term `m:num`) INT_POS)) THEN
               DISCH_THEN(MP_TAC o MATCH_MP INT_LE_TRANS) THEN
               REWRITE_TAC[INT_NOT_LE, INT_LT_ADDR, INT_LT_01]]
QED

Theorem INT_LT[simp]:
  !m n. &m:int < &n <=> m < n
Proof
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC ((REWRITE_RULE[] o
                     AP_TERM (Term `$~:bool->bool`) o
                     REWRITE_RULE[GSYM NOT_LESS, GSYM INT_NOT_LT])
                    (SPEC_ALL INT_LE))
QED

Theorem INT_OF_NUM_LE = INT_LE (* HOL-Light compatible name *)
Theorem INT_OF_NUM_LT = INT_LT (* HOL-Light compatible name *)

Theorem INT_INJ[simp]: !m n. (&m:int = &n) = (m = n)
Proof
  let val th = prove(“(m:num = n) <=> m <= n /\ n <= m”,
                     EQ_TAC
                     THENL [DISCH_THEN SUBST1_TAC
                            THEN REWRITE_TAC[LESS_EQ_REFL],
                            MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM])
  in
    REPEAT GEN_TAC THEN REWRITE_TAC[th, GSYM INT_LE_ANTISYM, INT_LE]
  end
QED

(* |- !m n. &m = &n <=> m = n *)
Theorem INT_OF_NUM_EQ = INT_INJ (* HOL-Light compatible name *)

Theorem INT_ADD:
              !m n. &m + &n = &(m + n)
Proof
              INDUCT_TAC THEN REWRITE_TAC[INT, ADD, INT_ADD_LID]
              THEN
              RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
              CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM))
QED

Theorem INT_MUL:
              !m n. &m * &n = &(m * n)
Proof
              INDUCT_TAC THEN REWRITE_TAC[INT_MUL_LZERO, MULT_CLAUSES, INT,
                                          GSYM INT_ADD, INT_RDISTRIB] THEN
              FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
              REWRITE_TAC[INT_MUL_LID,GSYM INT_1]
QED

Theorem INT_OF_NUM_ADD = INT_ADD (* HOL-Light compatible name *)
Theorem INT_OF_NUM_MUL = INT_MUL (* HOL-Light compatible name *)

(*--------------------------------------------------------------------------*)
(* Now more theorems                                                        *)
(*--------------------------------------------------------------------------*)


Theorem INT_LT_NZ:
              !n. ~(&n = 0) = (0 < &n)
Proof
              GEN_TAC THEN REWRITE_TAC[INT_LT_LE] THEN
              CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
              ASM_CASES_TAC (Term `&n = 0`)
              THEN ASM_REWRITE_TAC[INT_LE_REFL, INT_POS]
QED

Theorem INT_NZ_IMP_LT:
              !n. ~(n = 0) ==> 0 < &n
Proof
              GEN_TAC THEN REWRITE_TAC[GSYM INT_INJ, INT_LT_NZ]
QED

Theorem INT_DOUBLE:
              !x:int. x + x = 2 * x
Proof
              GEN_TAC THEN REWRITE_TAC[num_CONV (Term `2n`), INT] THEN
              REWRITE_TAC[INT_RDISTRIB, INT_MUL_LID,GSYM INT_1]
QED

Theorem INT_SUB_SUB:
              !x y. (x - y) - x = ~y
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
              ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
                               (Term `(a + b) + c = (c + a) + b:int`)] THEN
              REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID]
QED

Theorem INT_LT_ADD_SUB:
    !x y z:int. x + y < z <=> x < z - y
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(SPECL [Term `x:int`, Term `z - y:int`,
                                    Term `y:int`] INT_LT_RADD)) THEN
              REWRITE_TAC[INT_SUB_ADD]
QED

Theorem INT_LT_SUB_RADD:
              !x y z:int. x - y < z <=> x < z + y
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`x - y`, `z`, `y`] INT_LT_RADD)) THEN
              REWRITE_TAC[INT_SUB_ADD]
QED

Theorem INT_LT_SUB_LADD:
              !x y z:int. x < y - z <=> x + z < y
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL [`x + z`, `y`, `~z`] INT_LT_RADD)) THEN
              REWRITE_TAC[int_sub, GSYM INT_ADD_ASSOC,
                          INT_ADD_RINV, INT_ADD_RID, INT_0]
QED

Theorem INT_LE_SUB_LADD:
              !x y z:int. x <= y - z <=> x + z <= y
Proof
      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT, INT_LT_SUB_RADD]
QED

Theorem INT_LE_SUB_RADD:
              !x y z:int. x - y <= z <=> x <= z + y
Proof
      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT,INT_LT_SUB_LADD]
QED

Theorem INT_LT_NEG:
              !x y. ~x < ~y <=> y < x
Proof
              REPEAT GEN_TAC THEN
              SUBST1_TAC(SYM(Q.SPECL[`~x`, `~y`, `x + y`] INT_LT_RADD)) THEN
              REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID]
              THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
              REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_LID]
QED

Theorem INT_LE_NEG:
              !x y. ~x <= ~y <=> y <= x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN
              REWRITE_TAC[INT_LT_NEG]
QED

Theorem INT_ADD2_SUB2:
              !a b c d:int. (a + b) - (c + d) = (a - c) + (b - d)
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_ADD] THEN
              CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM))
QED

Theorem INT_SUB_LZERO[simp]: !x. 0 - x = ~x
Proof GEN_TAC THEN REWRITE_TAC[int_sub, INT_ADD_LID]
QED

Theorem INT_SUB_RZERO[simp]: !x:int. x - 0 = x
Proof GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_0,INT_ADD_RID, INT_0]
QED

Theorem INT_LET_ADD2:
              !w x y z:int. w <= x /\ y < z ==> w + y < x + z
Proof
                  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
                  MATCH_MP_TAC INT_LTE_TRANS THEN
                  Q.EXISTS_TAC `w + z` THEN
                  ASM_REWRITE_TAC[INT_LE_RADD, INT_LT_LADD]
QED

Theorem INT_LTE_ADD2:
              !w x y z:int. w < x /\ y <= z ==> w + y < x + z
Proof
                  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
                  ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
                  MATCH_ACCEPT_TAC INT_LET_ADD2
QED

Theorem INT_LET_ADD:
              !x y:int. 0 <= x /\ 0 < y ==> 0 < x + y
Proof
          REPEAT GEN_TAC THEN DISCH_TAC THEN
          SUBST1_TAC(SYM(Q.SPEC `0` INT_ADD_LID)) THEN
          MATCH_MP_TAC INT_LET_ADD2 THEN ASM_REWRITE_TAC[]
QED

Theorem INT_LTE_ADD:
              !x y:int. 0 < x /\ 0 <= y ==> 0 < x + y
Proof
          REPEAT GEN_TAC THEN DISCH_TAC THEN
          SUBST1_TAC(SYM(Q.SPEC `0` INT_ADD_LID)) THEN
          MATCH_MP_TAC INT_LTE_ADD2 THEN ASM_REWRITE_TAC[]
QED

Theorem INT_LT_MUL2:
     !x1 x2 y1 y2:int.
              0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2
                 ==>
              x1 * y1 < x2 * y2
Proof
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
       MATCH_MP_TAC INT_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]
QED

Theorem INT_SUB_LNEG:
              !x y. (~x) - y = ~(x + y)
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEG_ADD]
QED

Theorem INT_SUB_RNEG:
              !x y. x - ~y = x + y
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub, INT_NEGNEG]
QED

Theorem INT_LE_LNEG :
    !x y. -x <= y <=> &0 <= x + y
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [Q.SPECL [‘y’, ‘-x’] (GSYM INT_SUB_LE)]
 >> REWRITE_TAC [INT_SUB_RNEG, Once INT_ADD_SYM]
QED

Theorem INT_LE_RNEG :
    !x y. x <= -y <=> x + y <= &0
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [Q.SPECL [‘-y’, ‘x’] (GSYM INT_SUB_LE)]
 >> REWRITE_TAC [INT_SUB_LNEG, INT_NEG_GE0, Once INT_ADD_SYM]
QED

Theorem INT_SUB_NEG2:
              !x y. (~x) - (~y) = y - x
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[INT_SUB_LNEG] THEN
              REWRITE_TAC[int_sub, INT_NEG_ADD, INT_NEGNEG] THEN
              MATCH_ACCEPT_TAC INT_ADD_SYM
QED

Theorem INT_SUB_TRIANGLE:
              !a b c:int. (a - b) + (b - c) = a - c
Proof
              REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
              ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
                               (Term `(a + b) + (c + d)
                                      = (b + c) + (a + d):int`)] THEN
              REWRITE_TAC[INT_ADD_LINV, INT_ADD_LID]
QED

Theorem INT_EQ_SUB_LADD:
              !x y z:int. (x = y - z) = (x + z = y)
Proof
              REPEAT GEN_TAC THEN (SUBST1_TAC o SYM o C SPECL INT_EQ_RADD)
              [Term `x:int`, Term `y - z:int`, Term `z:int`]
              THEN REWRITE_TAC[INT_SUB_ADD]
QED

Theorem INT_EQ_SUB_RADD:
              !x y z:int. (x - y = z) = (x = z + y)
Proof
              REPEAT GEN_TAC THEN CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV))
              THEN
              MATCH_ACCEPT_TAC INT_EQ_SUB_LADD
QED

Theorem INT_SUB:
              !n m. m <= n ==> (&n - &m = &(n - m))
Proof
              SIMP_TAC int_ss [INT_EQ_SUB_RADD, INT_ADD, INT_INJ]
QED

Theorem INT_SUB_SUB2:
              !x y:int. x - (x - y) = y
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEGNEG] THEN
              AP_TERM_TAC THEN REWRITE_TAC[INT_NEG_SUB, INT_SUB_SUB]
QED

Theorem INT_ADD_SUB2:
              !x y:int. x - (x + y) = ~y
Proof
              REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEG_SUB] THEN
              AP_TERM_TAC THEN REWRITE_TAC[INT_ADD_SUB]
QED

Theorem INT_EQ_LMUL2:
              !x y z:int. ~(x = 0) ==> ((y = z) = (x * y = x * z))
Proof
                  REPEAT GEN_TAC THEN DISCH_TAC THEN
                  MP_TAC(SPECL [Term `x:int`, Term `y:int`,
                                Term `z:int`] INT_EQ_LMUL) THEN
                  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC
                  THEN REFL_TAC
QED

Theorem INT_EQ_IMP_LE:
              !x y:int. (x = y) ==> x <= y
Proof
                  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
                  MATCH_ACCEPT_TAC INT_LE_REFL
QED

Theorem INT_POS_NZ:
              !x:int. 0 < x ==> ~(x = 0)
Proof
                  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP INT_LT_IMP_NE)
                  THEN
                  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC
QED

Theorem INT_EQ_RMUL_IMP:
              !x y z:int. ~(z = 0) /\ (x * z = y * z) ==> (x = y)
Proof
                  REPEAT GEN_TAC
                  THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                  ASM_REWRITE_TAC[INT_EQ_RMUL]
QED

Theorem INT_EQ_LMUL_IMP:
              !x y z:int. ~(x = 0) /\ (x * y = x * z) ==> (y = z)
Proof
                  ONCE_REWRITE_TAC[INT_MUL_SYM]
                  THEN MATCH_ACCEPT_TAC INT_EQ_RMUL_IMP
QED

Theorem INT_DIFFSQ:
              !x y:int. (x + y) * (x - y) = (x * x) - (y * y)
Proof
              REPEAT GEN_TAC THEN
              REWRITE_TAC[INT_LDISTRIB, INT_RDISTRIB, int_sub,
                          GSYM INT_ADD_ASSOC] THEN
              ONCE_REWRITE_TAC[jrhUtils.AC(INT_ADD_ASSOC,INT_ADD_SYM)
                     (Term`a + (b + (c + d)) = (b + c) + (a + d):int`)] THEN
              REWRITE_TAC[INT_ADD_LID_UNIQ, GSYM INT_NEG_RMUL] THEN
              REWRITE_TAC[INT_LNEG_UNIQ] THEN AP_TERM_TAC THEN
              MATCH_ACCEPT_TAC INT_MUL_SYM
QED

Theorem INT_POSSQ:
    !x:int. 0 < x*x <=> ~(x = 0)
Proof
              GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LE]
              THEN AP_TERM_TAC THEN EQ_TAC THENL
              [DISCH_THEN(MP_TAC o C CONJ (SPEC (Term `x:int`) INT_LE_SQUARE))
               THEN
               REWRITE_TAC[INT_LE_ANTISYM, INT_ENTIRE],
               DISCH_THEN SUBST1_TAC
               THEN REWRITE_TAC[INT_MUL_LZERO, INT_LE_REFL]]
QED

Theorem INT_SUMSQ:
    !x y:int. ((x * x) + (y * y) = 0) <=> (x = 0) /\ (y = 0)
Proof
              REPEAT GEN_TAC THEN EQ_TAC THENL
              [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
               DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC INT_POS_NZ THENL
               [MATCH_MP_TAC INT_LTE_ADD, MATCH_MP_TAC INT_LET_ADD] THEN
               ASM_REWRITE_TAC[INT_POSSQ, INT_LE_SQUARE],
               DISCH_TAC THEN ASM_REWRITE_TAC[INT_MUL_LZERO, INT_ADD_RID]]
QED

Theorem INT_EQ_NEG[simp]: !x y:int. (~x = ~y) = (x = y)
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM, INT_LE_NEG] THEN
  MATCH_ACCEPT_TAC CONJ_SYM
QED

Theorem int_eq_calculate[simp]:
  !n m. ((&n = ~&m) <=> (n = 0) /\ (m = 0)) /\
        ((~&n = &m) <=> (n = 0) /\ (m = 0))
Proof
  Induct THENL [
    SIMP_TAC int_ss [INT_NEG_0, INT_INJ, GSYM INT_NEG_EQ],
    SIMP_TAC int_ss [INT] THEN GEN_TAC THEN CONJ_TAC THENL [
      SIMP_TAC int_ss [GSYM INT_EQ_SUB_LADD, int_sub, GSYM INT_NEG_ADD] THEN
      ASM_SIMP_TAC int_ss [INT_ADD],
      SIMP_TAC int_ss [INT_NEG_ADD, GSYM INT_EQ_SUB_LADD] THEN
      SIMP_TAC int_ss [int_sub] THEN
      ASM_SIMP_TAC int_ss [INT_NEGNEG, INT_ADD]
    ]
  ]
QED

Theorem INT_LT_CALCULATE:
  !n m.  (&n:int < &m <=> n < m) /\ (~&n < ~&m <=> m < n) /\
         (~&n < &m <=> ~(n = 0) \/ ~(m = 0)) /\ (&n < ~&m <=> F)
Proof
  SIMP_TAC int_ss [INT_LT, INT_LT_NEG] THEN
  Induct THENL [
    SIMP_TAC int_ss [INT_NEG_0, INT_LT, INT_NEG_GT0],
    GEN_TAC THEN CONJ_TAC THENL [
      SIMP_TAC int_ss [INT, INT_NEG_ADD, INT_LT_ADDNEG2] THEN
      ASM_SIMP_TAC int_ss [INT_ADD],
      SIMP_TAC int_ss [INT, INT_LT_ADD_SUB, int_sub, GSYM INT_NEG_ADD] THEN
      ASM_SIMP_TAC int_ss [INT_ADD]
    ]
  ]
QED



(*--------------------------------------------------------------------------*)
(* A nice proof that the positive integers are a copy of the natural        *)
(* numbers (replacing a nasty hack which poked under the quotient).         *)
(*--------------------------------------------------------------------------*)

val _ = print "Proving +ve integers are a copy of natural numbers\n"

Theorem NUM_POSINT:
              !i. 0 <= i ==> ?!n. i = &n
Proof
                  GEN_TAC THEN DISCH_TAC THEN
                  CONV_TAC EXISTS_UNIQUE_CONV THEN
                  CONJ_TAC THEN POP_ASSUM MP_TAC THENL
                   [ REWRITE_TAC[int_le, GSYM INT_0, NUM_POSINT_EX],
                     REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
                     ASM_REWRITE_TAC[INT_INJ]
                   ]
QED

Theorem NUM_POSINT_EXISTS:
  !i. 0 <= i ==> ?n. i = &n
Proof
  PROVE_TAC [SIMP_RULE bool_ss [EXISTS_UNIQUE_DEF] NUM_POSINT]
QED

Theorem NUM_NEGINT_EXISTS:
  !i. i <= 0 ==> ?n. i = ~&n
Proof
  PROVE_TAC [NUM_POSINT_EXISTS, INT_NEG_LE0, INT_NEG_EQ]
QED

Theorem INT_NUM_CASES:
  !p. (?n. (p = &n) /\ ~(n = 0)) \/ (?n. (p = ~&n) /\ ~(n = 0)) \/
           (p = 0)
Proof
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    Cases_on `p = 0` THENL [
      ASM_SIMP_TAC int_ss [],
      PROVE_TAC [NUM_POSINT_EXISTS]
    ],
    `?n. p = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [INT_EQ_NEG, INT_INJ, INT_NEG_GE0, NOT_LESS_EQUAL,
                          INT_LE]
  ]
QED
val _ = TypeBase.export [
      TypeBasePure.mk_nondatatype_info (
        “:int”,
        {nchotomy = SOME INT_NUM_CASES,
         induction = NONE, encode = NONE, size = NONE}
      )
    ];


(* ----------------------------------------------------------------------
    Discreteness of <
   ---------------------------------------------------------------------- *)

Theorem int_cases :
    !x:int. (?n. x = &n) \/ (?n. ~(n = 0) /\ (x = ~&n))
Proof
  PROVE_TAC [INT_NUM_CASES]
QED

Theorem INT_DISCRETE:
  !x:int y. ~(x < y /\ y < x + 1)
Proof
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
  ]
QED

Theorem INT_LE_LT1:
    x <= y  <=>  x < y + 1
Proof
  SRW_TAC [][EQ_IMP_THM] THENL [
    FULL_SIMP_TAC (srw_ss()) [INT_LE_LT, INT_LT_ADDR, INT_LT] THEN
    MATCH_MP_TAC INT_LT_TRANS THEN Q.EXISTS_TAC `y` THEN
    SRW_TAC [][INT_LT_ADDR, INT_LT],

    SRW_TAC [][int_le] THEN PROVE_TAC [INT_DISCRETE]
  ]
QED

Theorem INT_LT_LE1:
    x < y  <=>  x + 1 <= y
Proof
  SRW_TAC [][INT_LE_LT1, INT_LT_RADD]
QED

(* |- !x y. x < y <=> x + 1 <= y *)
Theorem INT_LT_DISCRETE = Q.GENL [‘x’, ‘y’] INT_LT_LE1

(* ------------------------------------------------------------------------ *)
(* More random theorems about "stuff"                                       *)
(* ------------------------------------------------------------------------ *)

Theorem INT_MUL_EQ_1:
  !x y. (x * y = 1) <=> (x = 1) /\ (y = 1) \/ (x = ~1) /\ (y = ~1)
Proof
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
    INT_NEGNEG, INT_EQ_NEG]
QED

(*--------------------------------------------------------------------------*)
(* Theorems about mapping both ways between :num and :int                   *)
(*--------------------------------------------------------------------------*)

Definition Num[nocompute]:
  Num (i:int) = @n. if 0 <= i then i = &n else i = - &n
End

Overload num_of_int[inferior] = “Num” (* from HOL Light *)

(* NOTE: In HOL-Light, num_of_int is unspecified for negative integers:
   |- !x. num_of_int x = (@n. &n = x) (int.ml, line 2056)
 *)
Theorem num_of_int = Num

Theorem NUM_OF_INT[simp,compute]:
  !n. Num(&n) = n
Proof
  GEN_TAC THEN REWRITE_TAC[Num, INT_INJ, INT_POS] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  REWRITE_TAC[SELECT_REFL]
QED

Theorem NUM_OF_NEG_INT[simp,compute]:
  !n. Num(-&n) = n
Proof
  GEN_TAC THEN
  REWRITE_TAC[Num, INT_INJ, INT_POS, INT_EQ_NEG] THEN
  Cases_on ‘0 <= -&n’ THEN ASM_REWRITE_TAC [] THEN
  CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) THEN
  REWRITE_TAC [SELECT_REFL] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [INT_NEG_GE0,INT_LE,LE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [INT_NEG_0,INT_INJ] THEN
  REWRITE_TAC [SELECT_REFL]
QED

Theorem INT_OF_NUM[simp]:
  !i. (&(Num i) = i) <=> 0 <= i
Proof
  GEN_TAC THEN EQ_TAC THEN1
   (DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC INT_POS) THEN
  DISCH_THEN(ASSUME_TAC o EXISTENCE o MATCH_MP NUM_POSINT) THEN
  REWRITE_TAC[Num] THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC [INT_POS,INT_INJ] THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) THEN
  REWRITE_TAC [SELECT_REFL]
QED

Theorem NUM_EQ0[simp]:
  Num i = 0 <=> i = 0
Proof
  Cases_on ‘i’ >> simp[]
QED

Theorem Num_EQ:
  Num a = Num b <=> a=b \/ a=-b
Proof
  Cases_on ‘a’ >> Cases_on ‘b’ >> simp[]
QED

Theorem Num_neg:
  Num (-a) = Num a
Proof
  Cases_on `a` >> gvs[]
QED

Theorem LE_NUM_OF_INT:
     !n i. & n <= i ==> n <= Num i
Proof
   METIS_TAC [NUM_OF_INT, INT_OF_NUM, INT_LE_TRANS, INT_POS, INT_LE]
QED

Theorem NUM_LT:
   0 <= x /\ 0 <= y ==> (Num x < Num y <=> x < y)
Proof
  map_every (fn q => Q.SPEC_THEN q strip_assume_tac INT_NUM_CASES) [‘x’, ‘y’] >>
  simp[INT_LE, INT_LT, INT_NEG_GE0]
QED

(*----------------------------------------------------------------------*)
(* Define division                                                      *)
(*----------------------------------------------------------------------*)

val _ = print "Integer division\n"

Theorem int_div_exists0[local]:
    !i j. ?q. ~(j = 0) ==>
               (q = if 0 < j then
                      if 0 <= i then &(Num i DIV Num j)
                      else ~&(Num ~i DIV Num j) +
                           (if Num ~i MOD Num j = 0 then 0 else ~1)
                    else
                      if 0 <= i then ~&(Num i DIV Num ~j) +
                                     (if Num i MOD Num ~j = 0 then 0 else ~1)
                      else &(Num ~i DIV Num ~j))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN DISJ2_TAC THEN
  REWRITE_TAC [EXISTS_REFL]
QED

val int_div_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_div_exists0

val int_div = new_specification ("int_div", ["int_div"], int_div_exists);

val _ = set_fixity "/" (Infixl 600)
val _ = overload_on("/", Term`int_div`)

Theorem INT_DIV:
  !n m. ~(m = 0) ==> (&n / &m = &(n DIV m))
Proof
  SIMP_TAC int_ss [int_div, INT_LE, INT_LT, NUM_OF_INT, INT_INJ]
QED

Theorem INT_DIV_NEG:
    !p q. ~(q = 0) ==> (p / ~q = ~p / q)
Proof
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
                        ZERO_MOD, INT_ADD_RID]
QED

Theorem INT_DIV_1:
  !p:int. p / 1 = p
Proof
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
  ]
QED

Theorem INT_DIV_0:
    !q. ~(q = 0) ==> (0 / q = 0)
Proof
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_NEG_EQ0, INT_INJ, INT_DIV_NEG, INT_DIV,
                       INT_NEG_0, ZERO_DIV, GSYM NOT_ZERO_LT_ZERO]
QED

Theorem INT_DIV_ID:
  !p:int. ~(p = 0) ==> (p / p = 1)
Proof
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    (* p positive *)
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    ASM_SIMP_TAC int_ss [INT_INJ, INT_DIV, DIVMOD_ID, NOT_ZERO_LT_ZERO],
    (* p negative *)
    `?n. p = ~&n` by PROVE_TAC [INT_NOT_LE, NUM_NEGINT_EXISTS, INT_LE_LT] THEN
    ASM_SIMP_TAC int_ss [INT_NEG_EQ0, INT_NEGNEG, int_div,
                         NUM_OF_INT, INT_NEG_GT0, INT_INJ, INT_LT,
                         DIVMOD_ID, NOT_ZERO_LT_ZERO]
  ]
QED

(*----------------------------------------------------------------------*)
(* Define the appropriate modulus function for int_div                  *)
(*----------------------------------------------------------------------*)

val _ = print "Integer modulus\n"

Theorem int_mod_exists0[local]:
    !i j. ?r. ~(j = 0) ==> (r = i - i / j * j)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN DISJ2_TAC THEN
  REWRITE_TAC [EXISTS_REFL]
QED
val int_mod_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_mod_exists0


val int_mod = new_specification ("int_mod",["int_mod"],int_mod_exists);

val _ = set_fixity "%" (Infixl 650)
Overload "%" = “int_mod”

Theorem little_lemma[local]:
    !x y z. ~x < y + ~z <=> z < y + x
Proof
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_LADD] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC (LHS_CONV (LAND_CONV  (REWR_CONV INT_ADD_COMM))) THEN
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_RADD]
QED

Theorem ll2[local]:
    !x y. (x + ~y <= 0) = (x <= y)
Proof
  REWRITE_TAC [GSYM int_sub, INT_LE_SUB_RADD, INT_ADD_LID]
QED


Theorem INT_MOD_BOUNDS:
    !p q. ~(q = 0) ==> if q < 0 then q < p % q /\ p % q <= 0
                       else          0 <= p % q /\ p % q < q
Proof
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
  ASM_SIMP_TAC int_ss []
QED

Theorem INT_DIVISION:
  !q. ~(q = 0) ==> !p. (p = p / q * q + p % q) /\
                            if q < 0 then q < p % q /\ p % q <= 0
                            else          0 <= p % q /\ p % q < q
Proof
  REPEAT STRIP_TAC THENL [
    ASM_SIMP_TAC int_ss [int_mod, int_sub] THEN
    PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM, INT_ADD_ASSOC, int_sub],
    PROVE_TAC [INT_MOD_BOUNDS]
  ]
QED

Theorem INT_MOD:
  !n m. ~(m = 0) ==> (&n % &m = &(n MOD m))
Proof
  SIMP_TAC int_ss [int_mod, INT_INJ, INT_DIV, INT_MUL, INT_EQ_SUB_RADD,
                   INT_ADD, INT_INJ] THEN
  PROVE_TAC [ADD_COMM, DIVISION, NOT_ZERO_LT_ZERO, MULT_COMM]
QED

Theorem INT_MOD_NEG:
    !p q. ~(q = 0) ==> (p % ~q = ~(~p % q))
Proof
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  FULL_SIMP_TAC int_ss [INT_INJ, INT_NEGNEG, int_mod, INT_NEG_EQ,
                        INT_NEG_0, INT_DIV_NEG, INT_NEG_ADD,
                        GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, int_sub,
                        INT_NEG_EQ0]
QED

Theorem INT_MOD0:
  !p. ~(p = 0) ==> (0 % p = 0)
Proof
  GEN_TAC THEN
  Cases_on `0 <= p` THENL [
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC int_ss [INT_MOD, INT_INJ, ZERO_MOD],
    `?n. p = ~&n` by PROVE_TAC [NUM_NEGINT_EXISTS, INT_NOT_LE, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC int_ss [INT_MOD_NEG, INT_NEG_EQ0, INT_MOD, INT_INJ, ZERO_MOD,
                     INT_NEG_0]
  ]
QED

Theorem INT_DIV_MUL_ID:
  !p q. ~(q = 0) /\ (p % q = 0) ==> (p / q * q = p)
Proof
  REPEAT STRIP_TAC THEN
  `p = p/q * q + p % q` by PROVE_TAC [INT_DIVISION] THEN
  `p = p / q * q` by PROVE_TAC [INT_ADD_RID] THEN
  PROVE_TAC []
QED

Theorem lessmult_lemma[local]:
    !x y:num. x * y < y ==> (x = 0)
Proof
  Induct THEN ASM_SIMP_TAC int_ss [MULT_CLAUSES]
QED

Theorem negcase[local]:
    !q n m.
       m < n /\ ~(q = 0) ==> ((~&q * &n + &m) / &n = ~ &q)
Proof
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
    rpt VAR_EQ_TAC THEN
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
  ]
QED

Theorem INT_DIV_UNIQUE:
    !i j q. (?r. (i = q * j + r) /\
                 if j < 0 then j < r /\ r <= 0 else 0 <= r /\ r < j) ==>
            (i / j = q)
Proof
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
  ]
QED

Theorem INT_MOD_UNIQUE:
    !i j m.
     (?q. (i = q * j + m) /\ if j < 0 then j < m /\ m <= 0
                             else 0 <= m /\ m < j) ==>
     (i % j = m)
Proof
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  `~(j = 0)` by (DISCH_THEN SUBST_ALL_TAC THEN
                 FULL_SIMP_TAC int_ss [INT_LT_REFL] THEN
                 PROVE_TAC [INT_LET_TRANS, INT_LT_REFL]) THEN
  ASM_SIMP_TAC int_ss [int_mod] THEN
  `(q * j + m) / j = q` by PROVE_TAC [INT_DIV_UNIQUE] THEN
  ASM_SIMP_TAC bool_ss [INT_ADD_SUB]
QED

Theorem INT_MOD_ID:
    !i. ~(i = 0) ==> (i % i = 0)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `1` THEN
  SIMP_TAC bool_ss [INT_MUL_LID, INT_ADD_RID, INT_LE_REFL] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]
QED

Theorem INT_MOD_COMMON_FACTOR:
  !p. ~(p = 0) ==> !q. (q * p) % p = 0
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  SIMP_TAC int_ss [INT_ADD_RID, INT_LE_REFL] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]
QED

Theorem INT_DIV_LMUL:
    !i j. ~(i = 0) ==> ((i * j) / i = j)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN
  ASM_SIMP_TAC int_ss [INT_MUL_COMM, INT_LE_REFL, INT_ADD_RID] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]
QED

Theorem INT_DIV_RMUL:
    !i j. ~(i = 0) ==> (j * i / i = j)
Proof
  PROVE_TAC [INT_DIV_LMUL, INT_MUL_COMM]
QED

Theorem INT_MOD_EQ0:
  !q. ~(q = 0) ==> !p. (p % q = 0) = (?k. p = k * q)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.PAT_ASSUM `~(q = 0)` (ASSUME_TAC o Q.SPEC `p` o
                            MATCH_MP INT_DIVISION) THEN
    PROVE_TAC [INT_ADD_RID],
    MATCH_MP_TAC INT_MOD_UNIQUE THEN
    ASM_SIMP_TAC int_ss [INT_LE_REFL, INT_EQ_RMUL, INT_ADD_RID] THEN
    PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]
  ]
QED

Theorem INT_MUL_DIV:
  !p:int q k. ~(q = 0) /\ (p % q = 0) ==>
                   ((k * p) / q = k * (p / q))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQUE THEN
  `?m. p = m * q` by PROVE_TAC [INT_MOD_EQ0] THEN
  `p / q = m` by PROVE_TAC [INT_DIV_RMUL] THEN
  POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  Q.EXISTS_TAC `0` THEN
  SIMP_TAC int_ss [INT_MUL_ASSOC, INT_ADD_RID, INT_LE_REFL] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]
QED

Theorem INT_ADD_DIV:
    !i j k. ~(k = 0) /\ ((i % k = 0) \/ (j % k = 0)) ==>
            ((i + j) / k = i / k + j / k)
Proof
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
  ]
QED

Theorem INT_MOD_ADD0[local]:
    0 <= r /\ r < k ==> ((q * k + r) % k = r)
Proof
  STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `q` THEN
  METIS_TAC [INT_LET_TRANS, INT_LT_TRANS, INT_LT_REFL]
QED

Theorem INT_MOD_ADD1[local]:
    k < r /\ r <= 0 ==> ((q * k + r) % k = r)
Proof
  STRIP_TAC THEN
  MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `q` THEN
  METIS_TAC [INT_LTE_TRANS]
QED

Theorem INT_MOD_ADD_MULTIPLES:
    ~(k = 0) ==> ((q * k + r) % k = r % k)
Proof
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
  ]
QED

Theorem INT_MOD_NEG_NUMERATOR:
    ~(k = 0) ==> (~x % k = (k - x) % k)
Proof
  METIS_TAC [int_sub, INT_MUL_LID, INT_MOD_ADD_MULTIPLES]
QED

Theorem INT_MOD_PLUS:
    ~(k = 0) ==> ((i % k + j % k) % k = (i + j) % k)
Proof
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
  SRW_TAC [][INT_MOD_ADD_MULTIPLES]
QED

(* surprisingly, this is not an easy consequence of INT_MOD_PLUS  and
   INT_MOD_NEG_NUMERATOR
*)
Theorem INT_MOD_SUB:
    ~(k = 0) ==> ((i % k - j % k) % k = (i - j) % k)
Proof
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
  SRW_TAC [][INT_MOD_ADD_MULTIPLES]
QED

Theorem INT_MOD_MOD:
    ~(k = 0) ==> (j % k % k = j % k)
Proof
  STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN Q.EXISTS_TAC `0` THEN
  SRW_TAC [][] THEN METIS_TAC [INT_DIVISION]
QED
val _ = export_rewrites ["INT_MOD_MOD"]

Theorem INT_DIV_P:
    !P x c. ~(c = 0) ==>
            (P (x / c) = ?k r. (x = k * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) /\ P k)
Proof
  METIS_TAC [INT_DIVISION, INT_DIV_UNIQUE]
QED

Theorem INT_MOD_P:
    !P x c. ~(c = 0) ==>
            (P (x % c) = ?k r. (x = k * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) /\ P r)
Proof
  METIS_TAC [INT_DIVISION, INT_MOD_UNIQUE]
QED

Theorem INT_DIV_FORALL_P:
    !P x c. ~(c = 0) ==>
            (P (x / c) = !k r. (x = k * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) ==>
                               P k)
Proof
  METIS_TAC [INT_DIV_UNIQUE, INT_DIVISION]
QED

Theorem INT_MOD_FORALL_P:
    !P x c. ~(c = 0) ==>
            (P (x % c) = !q r. (x = q * c + r) /\
                               (c < 0 /\ c < r /\ r <= 0 \/
                                ~(c < 0) /\ 0 <= r /\ r < c) ==>
                               P r)
Proof
  METIS_TAC [INT_MOD_UNIQUE, INT_DIVISION]
QED

Theorem INT_MOD_1:
    !i. i % 1 = 0
Proof
  GEN_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `i` THEN SRW_TAC [][INT_LT, INT_LE]
QED

Theorem INT_LESS_MOD:
    !i j. 0 <= i /\ i < j ==> (i % j = i)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN SRW_TAC [][] THEN
  PROVE_TAC [INT_LET_TRANS, INT_LT_ANTISYM]
QED

Theorem INT_MOD_MINUS1:
    !n. 0 < n ==> (~1 % n = n - 1)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  Q.EXISTS_TAC `~1` THEN SRW_TAC [][] THENL [
    SRW_TAC [][GSYM INT_NEG_MINUS1, INT_NEG_EQ, INT_NEG_ADD, INT_NEGNEG,
               INT_NEG_SUB, INT_SUB_ADD2],
    PROVE_TAC [INT_LT_ANTISYM],
    PROVE_TAC [INT_LT_ANTISYM],
    SRW_TAC [][INT_SUB_LE] THEN
    FULL_SIMP_TAC (srw_ss()) [INT_LT_LE1, INT_ADD],
    SRW_TAC [][INT_LT_SUB_RADD, INT_LT_ADDR, INT_LT]
  ]
QED


(*----------------------------------------------------------------------*)
(* Define absolute value                                                *)
(*----------------------------------------------------------------------*)

val _ = print "Absolute value\n"

Definition INT_ABS[nocompute]:
  ABS n = if n < 0 then ~n else n
End

Theorem INT_ABS_POS[simp]:
  !p. 0 <= ABS p
Proof
  GEN_TAC THEN STRIP_ASSUME_TAC (Q.SPEC `p` INT_LT_NEGTOTAL) THEN
  ASM_SIMP_TAC bool_ss [INT_ABS, INT_LE_REFL, INT_LT_REFL, INT_LT_GT,
                        INT_NEG_GT0, INT_NEG_0]
  THENL [
    ASM_SIMP_TAC bool_ss [INT_LE_LT],
    SIMP_TAC bool_ss [GSYM INT_NEG_GT0] THEN
    ASM_SIMP_TAC bool_ss [INT_LE_LT]
  ]
QED

Theorem INT_ABS_NUM[simp]:
  !n. ABS (&n) = &n
Proof
  SIMP_TAC bool_ss [INT_ABS, REWRITE_RULE [GSYM INT_NOT_LT] INT_POS]
QED

Theorem INT_NEG_SAME_EQ:
  !p. (p = ~p) = (p = 0)
Proof
  GEN_TAC THEN EQ_TAC THENL [
    PROVE_TAC [INT_NEG_GT0, INT_LT_TRANS, INT_LT_REFL, INT_LT_NEGTOTAL],
    SIMP_TAC bool_ss [INT_NEG_0]
  ]
QED

Theorem INT_ABS_NEG[simp]:
  !p. ABS ~p = ABS p
Proof
  GEN_TAC THEN
  SIMP_TAC (bool_ss ++ boolSimps.COND_elim_ss)
    [INT_ABS, INT_NEG_LT0, INT_NEGNEG, INT_NEG_EQ, INT_NEG_SAME_EQ] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NOT_LT, INT_LE_LT]
QED

Theorem INT_ABS_ABS[simp]:
  !p. ABS (ABS p) = ABS p
Proof
  GEN_TAC THEN Cases_on `0 <= p` THENL [
    `?n. p = &n` by PROVE_TAC [NUM_POSINT_EXISTS] THEN
    ASM_SIMP_TAC bool_ss [INT_ABS_NUM],
    FULL_SIMP_TAC bool_ss [INT_NOT_LE, INT_ABS, INT_NEGNEG, INT_NEG_LT0,
                           INT_LT_GT]
  ]
QED

Theorem INT_ABS_EQ_ID[simp]:
  !p. (ABS p = p) = (0 <= p)
Proof
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_LE, INT_NEG_SAME_EQ,
                   INT_NEG_GE0, INT_INJ]
QED

Theorem INT_ABS_MUL:
  !p q. ABS p * ABS q = ABS (p * q)
Proof
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_MUL,
                   GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEG_MUL2]
QED

Theorem INT_ABS_EQ0[simp]:
  !p. (ABS p = 0) = (p = 0)
Proof
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NEG, INT_ABS_NUM, INT_NEG_EQ0]
QED

Theorem INT_ABS_LT0:
    !p. ~(ABS p < 0)
Proof
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NEG, INT_ABS_NUM, INT_LT, INT_LT_NEG]
QED

Theorem INT_ABS_0LT[simp]:
   0 < ABS p <=> p <> 0
Proof
  ‘0 < ABS p <=> 0 <= ABS p /\ ABS p <> 0’ by metis_tac[INT_LE_LT, INT_LT_REFL] >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem INT_ABS_LE0[simp]:
    !p. (ABS p <= 0) = (p = 0)
Proof
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NEG, INT_ABS_NUM, INT_LE, INT_LE_NEG,
                       INT_INJ, INT_NEG_EQ0]
QED

Theorem Num_EQ_ABS:
  !i. & (Num i) = ABS i
Proof
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `i` INT_NUM_CASES) THEN
  REWRITE_TAC [INT_ABS_NUM,INT_ABS_NEG,NUM_OF_INT,NUM_OF_NEG_INT]
QED

Theorem INT_ABS_LT:
  !p q. (ABS p < q <=> p < q /\ ~q < p) /\
        (q < ABS p <=> q < p \/ p < ~q) /\
        (~ABS p < q <=> ~q < p \/ p < q) /\
        (q < ~ABS p <=> p < ~q /\ q < p)
Proof
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_NEG_LT0,
                       INT_NEG_0, INT_NEGNEG, INT_NEG_GT0,
                       INT_LT_CALCULATE]
QED

Theorem INT_ABS_LE:
  !p q. (ABS p <= q <=> p <= q /\ ~q <= p) /\
        (q <= ABS p <=> q <= p \/ p <= ~q) /\
        (~ABS p <= q <=> ~q <= p \/ p <= q) /\
        (q <= ~ABS p <=> p <= ~q /\ q <= p)
Proof
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_NEG_LT0,
                       INT_NEG_0, INT_NEGNEG, INT_NEG_GT0, int_le,
                       INT_LT_CALCULATE]
QED

Theorem INT_ABS_EQ:
  !p q. ((ABS p = q) <=> (p = q) /\ (0 < q) \/ (p = ~q) /\ (0 <= q)) /\
        ((q = ABS p) <=> (p = q) /\ (0 < q) \/ (p = ~q) /\ (0 <= q))
Proof
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) THEN
  REWRITE_TAC [] THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_NEG, INT_NEG_0, INT_NEGNEG,
                       int_eq_calculate, INT_EQ_NEG, INT_INJ,
                       INT_LT_CALCULATE, INT_LE_REFL, INT_LE, INT_NOT_LE]
QED

Theorem INT_ABS_EQ_ABS:
   (ABS x = ABS y) <=> (x = y) \/ (x = -y)
Proof
  rw[INT_ABS, EQ_IMP_THM] >>
  fs[INT_NEG_LT0, INT_NOT_LT, INT_EQ_NEG, INT_NEGNEG, INT_NEG_GE0] >>
  metis_tac[INT_LET_TRANS, INT_LT_TRANS, INT_LT_REFL, INT_LE_ANTISYM, INT_NEG_0]
QED




(* ----------------------------------------------------------------------
    Define integer rem(ainder) and quot(ient) functions.
      These two are analogous to int_mod and int_div respectively, but
      int_quot rounds towards zero, while int_div rounds towards negative
      infinity.  Once int_quot is fixed, the behaviour of int_rem is
      fixed.  The choice of names follows the example of the SML Basis
      Library.
   ---------------------------------------------------------------------- *)

val _ = print "Define integer rem(ainder) and quot(ient) functions\n"

Theorem int_quot_exists0[local]:
    !i j. ?q. ~(j = 0) ==>
              (q = if 0 < j then
                     if 0 <= i then &(Num i DIV Num j)
                     else ~&(Num ~i DIV Num j)
                   else
                     if 0 <= i then ~&(Num i DIV Num ~j)
                     else &(Num ~i DIV Num ~j))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN REWRITE_TAC [EXISTS_REFL]
QED

val int_quot_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_quot_exists0


val int_quot = new_specification ("int_quot",["int_quot"],int_quot_exists);

val _ = set_fixity "quot" (Infixl 600)
val _ = overload_on("quot", ``int_quot``);

Theorem INT_QUOT:
    !p q. ~(q = 0) ==> (&p quot &q = &(p DIV q))
Proof
  SIMP_TAC int_ss [int_quot, INT_INJ, INT_LT, INT_LE, NUM_OF_INT]
QED

Theorem INT_QUOT_0:
    !q. ~(q = 0) ==> (0 quot q = 0)
Proof
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  SIMP_TAC int_ss [INT_INJ, INT_QUOT, INT_NEG_EQ0, ZERO_DIV,
                   GSYM NOT_ZERO_LT_ZERO, int_quot, INT_NEG_GT0, INT_LE,
                   INT_LT, INT_NEGNEG, NUM_OF_INT]
QED

Theorem INT_QUOT_1:
    !p. p quot 1 = p
Proof
  GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_QUOT, INT_NEG_EQ0, INT_NEG_GE0,
                       ONE, DIV_ONE, int_quot, INT_NEG_GT0, INT_LE,
                       INT_LT, INT_NEGNEG, NUM_OF_INT]
QED

Theorem INT_QUOT_NEG:
  !p q. ~(q = 0) ==> (~p quot q = ~(p quot q)) /\
                          (p quot ~q = ~(p quot q))
Proof
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_NEGNEG, INT_NEG_0, INT_NEG_EQ0, INT_INJ,
                       INT_NEGNEG, int_quot, INT_LT, INT_LE, NUM_OF_INT,
                       INT_NEG_GE0, INT_NEG_GT0, INT_NEG_LT0, INT_NEG_LE0,
                       ZERO_DIV, GSYM NOT_ZERO_LT_ZERO]
QED

Theorem INT_ABS_QUOT:
  !p q. ~(q = 0) ==> ABS ((p quot q) * q) <= ABS p
Proof
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
  STRUCT_CASES_TAC (Q.SPEC `q` INT_NUM_CASES) THEN
  ASM_SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ0, GSYM INT_NEG_LMUL,
                       GSYM INT_NEG_RMUL, INT_NEG_MUL2, INT_MUL, INT_LE,
                       INT_QUOT, INT_QUOT_NEG, INT_ABS_NEG, INT_ABS_NUM] THEN
  PROVE_TAC [DIVISION, LESS_EQ_EXISTS, NOT_ZERO_LT_ZERO, ZERO_DIV,
             MULT_COMM]
QED

(* can now prove uniqueness of / and % *)
fun case_tac s =
    REPEAT_TCL STRIP_THM_THEN ASSUME_TAC (Q.SPEC [QUOTE s] INT_NUM_CASES) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN Q.ABBREV_TAC [QUOTE s, QUOTE " = n"] THEN
    POP_ASSUM (K ALL_TAC)

Theorem lem1[local]:
    !x y z. (x = y + ~z) = (x + z = y)
Proof
  REWRITE_TAC [GSYM int_sub, INT_EQ_SUB_LADD]
QED
Theorem lem2[local]:
    !x y z. (x = ~y + z) = (x + y = z)
Proof
  PROVE_TAC [INT_ADD_COMM, lem1]
QED
Theorem lem3[local]:
    !x y z. (~x + y = z) = (y = x + z)
Proof
  PROVE_TAC [INT_ADD_COMM, lem2]
QED
Theorem lem3a[local]:
    !x y z. (x + ~y = z) = (x = y + z)
Proof
  PROVE_TAC [INT_ADD_COMM, lem2]
QED
Theorem lem4[local]:
    !x y:num. x * y < y <=> (x = 0) /\ ~(y = 0)
Proof
  Induct THEN ASM_SIMP_TAC int_ss [MULT_CLAUSES]
QED

Theorem INT_QUOT_UNIQUE:
  !p q k.
          (?r. (p = k * q + r) /\
               (if 0 < p then 0 <= r else r <= 0) /\ ABS r < ABS q) ==>
          (p quot q = k)
Proof
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
  ]
QED

Theorem INT_QUOT_ID:
    !p. ~(p = 0) ==> (p quot p = 1)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_QUOT_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN
  SIMP_TAC int_ss [INT_ADD_RID, INT_MUL_LID, INT_LE_REFL, INT_ABS_NUM] THEN
  PROVE_TAC [INT_ABS_EQ0, INT_ABS_POS, INT_LE_LT]
QED

(* define rem *)
Theorem int_rem_exists0[local]:
    !i j. ?r. ~(j = 0) ==> (r = i - i quot j * j)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  CONV_TAC EXISTS_OR_CONV THEN REWRITE_TAC [EXISTS_REFL]
QED
val int_rem_exists =
    CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) int_rem_exists0

val int_rem = new_specification ("int_rem",["int_rem"],int_rem_exists);

val _ = set_fixity "rem" (Infixl 650);
val _ = overload_on("rem", ``int_rem``);

Theorem INT_REM:
    !p q. ~(q = 0) ==> (&p rem &q = &(p MOD q))
Proof
  SIMP_TAC int_ss [int_rem, INT_INJ, int_sub, lem1, lem2, lem3, lem3a,
                   INT_QUOT, INT_MUL, INT_ADD] THEN
  PROVE_TAC [DIVISION, NOT_ZERO_LT_ZERO, MULT_COMM]
QED

Theorem newlemma[local]:
    !x y. (~x + y <= 0 <=> y <= x) /\ (0 <= x + ~y <=> y <= x)
Proof
  REPEAT STRIP_TAC THENL [
    CONV_TAC (LHS_CONV (LAND_CONV (REWR_CONV INT_ADD_COMM))),
    ALL_TAC
  ] THEN REWRITE_TAC [GSYM int_sub, INT_LE_SUB_RADD, INT_LE_SUB_LADD,
                      INT_ADD_RID, INT_ADD_LID]
QED
Theorem nl2[local]:
    !p q. ~(q = 0n) ==> p DIV q * q <= p
Proof
  PROVE_TAC [DIVISION, LESS_EQ_ADD, NOT_ZERO_LT_ZERO]
QED
Theorem nl2a[local]:
    !p q. ~(q = 0n) ==> p < q + p DIV q * q /\ p DIV q * q < p + q
Proof
  REPEAT STRIP_TAC THENL [
    `(p = p DIV q * q + p MOD q) /\ p MOD q < q` by
      PROVE_TAC [DIVISION, NOT_ZERO_LT_ZERO] THEN
    FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o
                   ONCE_REWRITE_RULE [ADD_COMM]) THEN
    ASM_REWRITE_TAC [LESS_MONO_ADD_EQ],
    MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `p` THEN
    ASM_SIMP_TAC int_ss [nl2]
  ]
QED

Theorem nl3[local]:
    !x y z.
      (x + ~y < z <=> x < y + z) /\ (~x < y + ~z <=> z < y + x)
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_RADD, INT_LT_SUB_LADD] THEN
  CONV_TAC (RAND_CONV (LHS_CONV (LAND_CONV (REWR_CONV INT_ADD_COMM)))) THEN
  REWRITE_TAC [GSYM int_sub, INT_LT_SUB_RADD, INT_LT_SUB_LADD] THEN
  PROVE_TAC [INT_ADD_COMM]
QED
Theorem nl4[local]:
    !x y z.
      (~x + y < z <=> y < x + z) /\ (~x < ~y + z <=> y < x + z)
Proof
  PROVE_TAC [nl3, INT_ADD_COMM]
QED

Theorem INT_REMQUOT:
    !q. ~(q = 0) ==> !p. (p = p quot q * q + p rem q) /\
                         (if 0 < p then 0 <= p rem q else p rem q <= 0) /\
                         ABS (p rem q) < ABS q
Proof
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
  ]
QED

Theorem INT_REM_UNIQUE:
  !p q r.
          ABS r < ABS q /\ (if 0 < p then 0 <= r else r <= 0) /\
          (?k. p = k * q + r) ==>
          (p rem q = r)
Proof
  REPEAT STRIP_TAC THEN
  `~(q = 0)` by (DISCH_THEN SUBST_ALL_TAC THEN
                 FULL_SIMP_TAC int_ss [INT_ABS_NUM, INT_ABS_LT0]) THEN
  ASM_SIMP_TAC int_ss [int_rem, INT_EQ_SUB_RADD] THEN
  `(k * q + r) quot q = k` by PROVE_TAC [INT_QUOT_UNIQUE] THEN
  ASM_SIMP_TAC int_ss [INT_ADD_COMM]
QED

Theorem INT_REM_NEG:
  !p q. ~(q = 0) ==> (~p rem q = ~(p rem q)) /\ (p rem ~q = p rem q)
Proof
  REPEAT GEN_TAC THEN
  case_tac "p" THEN case_tac "q" THEN
  ASM_SIMP_TAC int_ss [INT_INJ, int_rem, INT_NEGNEG, lem1, lem2, lem3,
                       int_sub, INT_NEG_EQ0, GSYM INT_NEG_LMUL,
                       GSYM INT_NEG_RMUL, INT_ADD_LID, INT_ADD_RID,
                       INT_NEG_0, INT_NEG_ADD, INT_QUOT_0, INT_QUOT_NEG,
                       INT_MUL_LZERO] THEN
  METIS_TAC [INT_ADD_ASSOC, INT_ADD_COMM, INT_ADD_LINV, INT_ADD_RID,
             INT_ADD_LID, INT_ADD_RINV]
QED

Theorem INT_REM_ID:
  !p. ~(p = 0) ==> (p rem p = 0)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQUE THEN
  SIMP_TAC int_ss [INT_LE_REFL] THEN CONJ_TAC THENL [
    PROVE_TAC [INT_LE_LT, INT_ABS_POS, INT_ABS_EQ0, INT_ABS_NUM],
    Q.EXISTS_TAC `1` THEN REWRITE_TAC [INT_MUL_LID, INT_ADD_RID, INT_LE_REFL]
  ]
QED

Theorem INT_REM0:
    !q. ~(q = 0) ==> (0 rem q = 0)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQUE THEN
  ASM_SIMP_TAC int_ss [INT_LE_REFL, INT_ABS_NUM, INT_ADD_RID] THEN
  PROVE_TAC [INT_LE_LT, INT_ABS_POS, INT_MUL_LZERO, INT_ABS_EQ0]
QED

Theorem INT_REM_COMMON_FACTOR:
  !p. ~(p = 0) ==> !q. (q * p) rem p = 0
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_REM_UNIQUE THEN
  SIMP_TAC int_ss [INT_ABS_NUM, INT_ADD_RID] THEN
  PROVE_TAC [INT_ABS_NUM, INT_LE_LT, INT_ABS_EQ0, INT_ABS_POS]
QED

Theorem INT_REM_EQ0:
  !q. ~(q = 0) ==> !p. (p rem q = 0) = (?k. p = k * q)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.PAT_ASSUM `~(q = 0)` (ASSUME_TAC o Q.SPEC `p` o
                            MATCH_MP INT_REMQUOT) THEN
    PROVE_TAC [INT_ADD_RID],
    MATCH_MP_TAC INT_REM_UNIQUE THEN CONJ_TAC THENL [
      PROVE_TAC [INT_ABS_NUM, INT_ABS_EQ0, INT_LE_LT, INT_ABS_POS],
      PROVE_TAC [INT_ADD_RID, INT_LE_REFL]
    ]
  ]
QED

Theorem INT_MUL_QUOT:
  !p:int q k. ~(q = 0) /\ (p rem q = 0) ==>
                   ((k * p) quot q = k * (p quot q))
Proof
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
  ]
QED

Theorem INT_REM_EQ_MOD:
    !i n.
      0 < n ==>
      (i rem n = if i < 0 then (i - 1) % n - n + 1 else i % n)
Proof
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
  ]
QED


(*----------------------------------------------------------------------*)
(* Define divisibility                                                  *)
(*----------------------------------------------------------------------*)

val _ = print "Facts about integer divisibility\n";
Definition INT_DIVIDES[nocompute]:
  int_divides p q = ?m:int. m * p = q
End
val _ = set_fixity "int_divides" (Infix(NONASSOC, 450))

(* HOL-Light compatible definition of ‘int_divides’ (divides) *)
Theorem int_divides :
    !b a. a int_divides b <=> (?x. b = a * x)
Proof
    RW_TAC std_ss [INT_DIVIDES, Once INT_MUL_SYM]
 >> EQ_TAC >> STRIP_TAC
 >| [ Q.EXISTS_TAC ‘m’ >> ASM_REWRITE_TAC [],
      Q.EXISTS_TAC ‘x’ >> ASM_REWRITE_TAC [] ]
QED

Theorem INT_DIVIDES_MOD0:
  !p q. p int_divides q <=>
             ((q % p = 0) /\ ~(p = 0)) \/ ((p = 0) /\ (q = 0))
Proof
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
  ]
QED

Theorem INT_DIVIDES_0:
  (!x. x int_divides 0) /\ (!x. 0 int_divides x <=> (x = 0))
Proof
  PROVE_TAC [INT_DIVIDES, INT_MUL_RZERO, INT_MUL_LZERO]
QED

Theorem INT_DIVIDES_1:
  !x. 1 int_divides x /\ (x int_divides 1 <=> (x = 1) \/ (x = ~1))
Proof
  REPEAT STRIP_TAC THEN
  PROVE_TAC [INT_DIVIDES, INT_MUL_RID, INT_MUL_EQ_1]
QED

Theorem INT_DIVIDES_REFL:
  !x. x int_divides x
Proof
  PROVE_TAC [INT_DIVIDES, INT_MUL_LID]
QED

Theorem INT_DIVIDES_TRANS:
  !x y z. x int_divides y /\ y int_divides z ==> x int_divides z
Proof
  PROVE_TAC [INT_DIVIDES, INT_MUL_ASSOC]
QED

Theorem INT_DIVIDES_MUL:
  !p q. p int_divides p * q /\ p int_divides q * p
Proof
  PROVE_TAC [INT_DIVIDES, INT_MUL_COMM]
QED

Theorem INT_DIVIDES_LMUL:
  !p q r. p int_divides q ==> (p int_divides (q * r))
Proof
  PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM, INT_DIVIDES]
QED

Theorem INT_DIVIDES_RMUL:
  !p q r. p int_divides q ==> (p int_divides (r * q))
Proof
  PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM, INT_DIVIDES]
QED

Theorem INT_DIVIDES_MUL_BOTH:
    !p q r. ~(p = 0) ==> (p * q int_divides p * r <=> q int_divides r)
Proof
  SIMP_TAC bool_ss [INT_DIVIDES] THEN
  REPEAT GEN_TAC THEN
  `!m p q. m * (p * q) = p * (m * q)` by
     PROVE_TAC [INT_MUL_ASSOC, INT_MUL_COMM] THEN
  POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  PROVE_TAC [INT_EQ_LMUL]
QED

Theorem INT_DIVIDES_LADD:
  !p q r. p int_divides q ==>
               (p int_divides (q + r) <=> p int_divides r)
Proof
  REWRITE_TAC [INT_DIVIDES] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `n` ASSUME_TAC) THENL [
    Q.EXISTS_TAC `n - m` THEN
    ASM_REWRITE_TAC [INT_SUB_RDISTRIB, INT_ADD_SUB],
    Q.EXISTS_TAC `m + n` THEN
    ASM_REWRITE_TAC [INT_RDISTRIB]
  ]
QED

Theorem INT_DIVIDES_RADD =
  ONCE_REWRITE_RULE [INT_ADD_COMM] INT_DIVIDES_LADD;

Theorem INT_DIVIDES_NEG:
  !p q. (p int_divides ~q <=> p int_divides q) /\
             (~p int_divides q <=> p int_divides q)
Proof
  REWRITE_TAC [INT_DIVIDES] THEN ONCE_REWRITE_TAC [INT_NEG_MINUS1] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `n` ASSUME_TAC) THENL [
    Q.EXISTS_TAC `~1 * n` THEN
    ASM_REWRITE_TAC [GSYM INT_MUL_ASSOC, GSYM INT_NEG_MINUS1,
                     INT_NEGNEG],
    PROVE_TAC [INT_MUL_ASSOC],
    PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM],
    PROVE_TAC [INT_NEG_MINUS1, INT_NEG_MUL2]
  ]
QED

Theorem INT_DIVIDES_LSUB:
  !p q r. p int_divides q ==>
               (p int_divides (q - r) <=> p int_divides r)
Proof
  REWRITE_TAC [int_sub] THEN
  PROVE_TAC [INT_DIVIDES_NEG, INT_DIVIDES_LADD]
QED

Theorem INT_DIVIDES_RSUB:
  !p q r. p int_divides q ==>
               (p int_divides (r - q) <=> p int_divides r)
Proof
  REWRITE_TAC [int_sub] THEN
  PROVE_TAC [INT_DIVIDES_NEG, INT_DIVIDES_RADD]
QED

(* temporarily make divides an infix *)
val _ = temp_set_fixity "divides" (Infixl 480);

(* NOTE: This theorem is the definition of ‘divides’ of natural numbers in
   HOL-Light. This name is HOL-Light compatible.
 *)
Theorem num_divides :
    a divides b <=> &a int_divides &b
Proof
    rw [INT_DIVIDES, divides_def]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘&q’ \\
     rw [INT_OF_NUM_MUL])
 (* INT_POS *)
 >> MP_TAC (Q.SPEC ‘m’ INT_NUM_CASES)
 >> rw [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      Q.EXISTS_TAC ‘n’ >> fs [INT_OF_NUM_MUL],
      (* goal 2 (of 3): impossible *)
      fs [INT_MUL_LNEG, INT_OF_NUM_MUL],
      (* goal 3 (of 3) *)
      fs [] >> POP_ASSUM (fn th => rw [GSYM th]) \\
      Q.EXISTS_TAC ‘0’ >> rw [] ]
QED

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

Theorem INT_POW :
    (x :int) ** 0 = &1 /\ (!n. x ** SUC n = x * x ** n)
Proof
    rw [int_exp]
QED

Theorem INT_EXP:
  !n m. &n ** m = &(n EXP m)
Proof
  REPEAT GEN_TAC THEN Induct_on `m` THENL [
    REWRITE_TAC [int_exp, EXP],
    ASM_REWRITE_TAC [int_exp, EXP, INT_MUL]
  ]
QED

Theorem INT_OF_NUM_POW = INT_EXP (* HOL-Light compatible name *)

Theorem INT_EXP_EQ0:
  !(p:int) n. (p ** n = 0) <=> (p = 0) /\ ~(n = 0)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Induct_on `n` THENL [
      SIMP_TAC int_ss [int_exp, INT_INJ],
      SIMP_TAC int_ss [int_exp, INT_ENTIRE] THEN PROVE_TAC []
    ],
    `?m. n = SUC m` by PROVE_TAC [num_CASES] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    SIMP_TAC int_ss [int_exp, INT_MUL_LZERO]
  ]
QED

Theorem INT_MUL_SIGN_CASES:
  !p:int q. ((0 < p * q) = (0 < p /\ 0 < q \/ p < 0 /\ q < 0)) /\
                 ((p * q < 0) = (0 < p /\ q < 0 \/ p < 0 /\ 0 < q))
Proof
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
  ]
QED

Theorem INT_EXP_NEG:
  !n m.
         (EVEN n ==> (~&m ** n = &(m EXP n))) /\
         (ODD n ==> (~&m ** n = ~&(m EXP n)))
Proof
  Induct THENL [
    SIMP_TAC int_ss [EVEN, ODD, int_exp, INT_LE, EXP],
    ASM_SIMP_TAC int_ss [EVEN, ODD, GSYM EVEN_ODD, GSYM ODD_EVEN, int_exp,
                         EXP, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_MUL,
                         INT_NEGNEG]
  ]
QED

Theorem INT_POW_NEG :
    !(x :int) n. -x ** n = (if EVEN n then x ** n else -(x ** n))
Proof
    qx_genl_tac [‘p’, ‘m’]
 >> MP_TAC (Q.SPEC ‘p’ INT_NUM_CASES)
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [GSYM ODD_EVEN]
 >| [ (* goal 1 (of 6) *)
      RW_TAC std_ss[INT_EXP_NEG, INT_EXP],
      (* goal 2 (of 6) *)
      RW_TAC std_ss[INT_NEG_NEG, INT_EXP_NEG, INT_EXP],
      (* goal 3 (of 6) *)
      RW_TAC std_ss[INT_NEG_0],
      (* goal 4 (of 6) *)
      RW_TAC std_ss [INT_EXP_NEG, INT_EXP],
      (* goal 5 (of 6) *)
      RW_TAC std_ss [INT_NEG_NEG, INT_EXP_NEG, INT_EXP],
      (* goal 6 (of 6) *)
      RW_TAC std_ss [INT_NEG_0, INT_EXP] \\
      rw [ZERO_EXP] \\
      CCONTR_TAC >> fs [] ]
QED

Theorem INT_EXP_ADD_EXPONENTS:
  !n m p:int. p ** n * p ** m = p ** (n + m)
Proof
  Induct THENL [
    SIMP_TAC int_ss [int_exp, INT_MUL_LID],
    SIMP_TAC bool_ss [int_exp, ADD_CLAUSES] THEN
    PROVE_TAC [INT_MUL_ASSOC, INT_EQ_LMUL]
  ]
QED

Theorem INT_EXP_MULTIPLY_EXPONENTS:
  !m n p:int. (p ** n) ** m = p ** (n * m)
Proof
  Induct THENL [
    SIMP_TAC int_ss [MULT_CLAUSES, int_exp],
    ASM_SIMP_TAC bool_ss [int_exp, MULT_CLAUSES, GSYM INT_EXP_ADD_EXPONENTS]
  ]
QED

Theorem INT_EXP_MOD:
  !m n p:int. n <= m /\ ~(p = 0) ==> (p ** m % p ** n = 0)
Proof
  SIMP_TAC int_ss [INT_MOD_EQ0, INT_EXP_EQ0] THEN
  PROVE_TAC [LESS_EQ_EXISTS, INT_EXP_ADD_EXPONENTS, ADD_COMM]
QED

Theorem INT_EXP_SUBTRACT_EXPONENTS:
  !m n p:int. n <= m /\ ~(p = 0) ==>
                   ((p ** m) / (p ** n) = p ** (m - n))
Proof
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
       THEN RW_TAC int_ss []]]
QED

(*----------------------------------------------------------------------*)
(* Define integer minimum and maximum                                   *)
(*----------------------------------------------------------------------*)

Definition INT_MIN[nocompute]:
  int_min (x:int) y = if x < y then x else y
End

Definition INT_MAX[nocompute]:
  int_max (x:int) y = if x < y then y else x
End

Theorem INT_MIN_LT:
  !x y z. x < int_min y z ==> x < y /\ x < z
Proof
  SIMP_TAC bool_ss [INT_MIN] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  PROVE_TAC [INT_LT_TRANS, INT_LT_TOTAL]
QED

Theorem INT_MAX_LT:
  !x y z. int_max x y < z ==> x < z /\ y < z
Proof
  SIMP_TAC bool_ss [INT_MAX] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  PROVE_TAC [INT_LT_TRANS, INT_LT_TOTAL]
QED

Theorem INT_MIN_NUM:
    !m n. int_min (&m) (&n) = &(MIN m n)
Proof
  SIMP_TAC (bool_ss ++ LIFT_COND_ss) [INT_MIN, MIN_DEF, INT_LT]
QED

Theorem INT_MAX_NUM:
    !m n. int_max (&m) (&n) = &(MAX m n)
Proof
  SIMP_TAC (bool_ss ++ LIFT_COND_ss) [INT_MAX, MAX_DEF, INT_LT]
QED


(* ----------------------------------------------------------------------
    Some monotonicity results
   ---------------------------------------------------------------------- *)

Theorem INT_LT_MONO:
    !x y z. 0 < x ==> (x * y < x * z <=> y < z)
Proof
  REPEAT STRIP_TAC THEN
  CONV_TAC (Conv.BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LT_SUB_LADD, GSYM INT_SUB_LDISTRIB] THEN
  PROVE_TAC [INT_LT_ANTISYM, INT_MUL_SIGN_CASES]
QED

Theorem INT_LE_MONO:
    !x y z. 0 < x ==> (x * y <= x * z <=> y <= z)
Proof
  REPEAT STRIP_TAC THEN
  CONV_TAC (Conv.BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LE_SUB_LADD, GSYM INT_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC bool_ss [INT_LE_LT, INT_MUL_SIGN_CASES, INT_LT_GT] THEN
  PROVE_TAC [INT_ENTIRE, INT_LT_REFL]
QED

Theorem INFINITE_INT_UNIV:
    INFINITE univ(:int)
Proof
  REWRITE_TAC [] THEN STRIP_TAC THEN
  `FINITE (IMAGE Num univ(:int))` by SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `IMAGE Num univ(:int) = univ(:num)`
        THEN1 (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][EXTENSION] THEN Q.EXISTS_TAC `&x` THEN SRW_TAC [][NUM_OF_INT]
QED
val _ = export_rewrites ["INFINITE_INT_UNIV"]

Theorem INT_ABS_SUB:
  ABS (i - j) = ABS (j - i)
Proof
  Cases_on ‘i’ >> Cases_on‘j’ >> simp[INT_ABS, INT_LT_SUB_RADD, INT_LT] >>
  rw[] >> gs[INT_NEG_SUB, INT_SUB, INT_LT, INT_LT_CALCULATE] >>
  rename [‘~(m < n)’, ‘~(n < m)’] >> ‘m = n’ by DECIDE_TAC >> gvs[]
QED

Theorem INT_ABS_TRIANGLE:
  ABS (i + j) <= ABS i + ABS j
Proof
  Cases_on ‘i’ >> Cases_on ‘j’ >> simp[INT_ADD, GSYM INT_NEG_ADD] >~
  [‘ABS (&m + -&n)’]
  >- (Cases_on ‘n <= m’ >> simp[GSYM int_sub, INT_SUB, INT_LE] >>
      simp[Once INT_ABS_SUB, INT_SUB, INT_LE]) >~
  [‘ABS (-&m + &n)’]
  >- (ONCE_REWRITE_TAC[INT_ADD_COMM] >>
      Cases_on ‘m <= n’ >> simp[GSYM int_sub, INT_SUB, INT_LE] >>
      simp[Once INT_ABS_SUB, INT_SUB, INT_LE])
QED

Theorem INT_SUB_ABS_TRIANGLE:
  ABS i - ABS j <= ABS (i - j)
Proof
  Cases_on ‘i’ >> Cases_on ‘j’ >> simp[] >>~-
  ([‘-&m <= &m’], irule INT_LE_TRANS >> qexists ‘0’ >>
                  simp[INT_NEG_LE0, INT_LE]) >>
  simp[INT_SUB, INT_SUB_RNEG, INT_ADD] >>
  rename [‘&m - &n <= _’] >>
  Cases_on ‘m <= n’ >> simp[INT_SUB, INT_SUB_RNEG, INT_LE] >>~-
  ([‘&m:int - &n’, ‘m <= n’],
   irule INT_LE_TRANS >> qexists ‘0’ >> simp[INT_LE_SUB_RADD, INT_LE]) >~
  [‘-&m - &n:int’] >- simp[INT_SUB_LNEG, INT_ADD, INT_LE] >~
  [‘-&m + &n’]
  >- (‘-&m + &n = &n - &m’ by simp[int_sub, AC INT_ADD_COMM INT_ADD_ASSOC] >>
      simp[Once INT_ABS_SUB, INT_SUB])
QED

(*----------------------------------------------------------------------*)
(* Prove rewrites for calculation with integers                         *)
(*----------------------------------------------------------------------*)

val _ = print "Proving rewrites for calculation with integers\n"

Theorem INT_ADD_CALCULATE:
  !p:int n m.
          (0 + p = p) /\ (p + 0 = p) /\
          (&n + &m:int = &(n + m)) /\
          (&n + ~&m = if m <= n then &(n - m) else ~&(m - n)) /\
          (~&n + &m = if n <= m then &(m - n) else ~&(n - m)) /\
          (~&n + ~&m = ~&(n + m))
Proof
  SIMP_TAC (int_ss ++ boolSimps.COND_elim_ss) [
    INT_ADD_LID, INT_ADD_RID, INT_ADD, GSYM INT_NEG_ADD, INT_ADD_COMM,
    GSYM int_sub, INT_EQ_SUB_RADD, INT_INJ, INT_SUB
  ]
QED

Theorem INT_ADD_REDUCE:
  !p:int n m.
          (0 + p = p) /\ (p + 0 = p) /\ (~0 = 0) /\ (~~p = p) /\
          (&(NUMERAL n) + &(NUMERAL m):int =
             &(NUMERAL (numeral$iZ (n + m)))) /\
          (&(NUMERAL n) + ~&(NUMERAL m):int =
             if m <= n then &(NUMERAL (n - m)) else ~&(NUMERAL (m - n))) /\
          (~&(NUMERAL n) + &(NUMERAL m):int =
             if n <= m then &(NUMERAL (m - n)) else ~&(NUMERAL (n - m))) /\
          (~&(NUMERAL n) + ~&(NUMERAL m):int =
             ~&(NUMERAL (numeral$iZ (n + m))))
Proof
  SIMP_TAC (int_ss ++ boolSimps.COND_elim_ss) [
    INT_ADD_LID, INT_ADD_RID, INT_ADD, GSYM INT_NEG_ADD, INT_ADD_COMM,
    GSYM int_sub, INT_EQ_SUB_RADD, INT_INJ, INT_SUB, numeralTheory.iZ,
    NUMERAL_DEF, INT_NEG_0, INT_NEGNEG
  ]
QED

Theorem INT_SUB_CALCULATE = int_sub;

Theorem INT_SUB_REDUCE:
  !m n p:int.
        (p - 0 = p) /\ (0 - p = ~p) /\
        (&(NUMERAL m) - &(NUMERAL n):int = &(NUMERAL m) + ~&(NUMERAL n)) /\
        (~&(NUMERAL m) - &(NUMERAL n):int = ~&(NUMERAL m) + ~&(NUMERAL n)) /\
        (&(NUMERAL m) - ~&(NUMERAL n):int = &(NUMERAL m) + &(NUMERAL n)) /\
        (~&(NUMERAL m) - ~&(NUMERAL n):int = ~&(NUMERAL m) + &(NUMERAL n))
Proof
  REWRITE_TAC [int_sub, INT_NEG_0, INT_ADD_LID, INT_ADD_RID, INT_NEGNEG]
QED

Theorem INT_MUL_CALCULATE =
  LIST_CONJ [INT_MUL, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG];

Theorem INT_MUL_REDUCE:
  !m n p.
         (p * 0i = 0) /\ (0 * p = 0) /\
         (&(NUMERAL m) * &(NUMERAL n):int = &(NUMERAL (m * n))) /\
         (~&(NUMERAL m) * &(NUMERAL n) = ~&(NUMERAL (m * n))) /\
         (&(NUMERAL m) * ~&(NUMERAL n) = ~&(NUMERAL (m * n))) /\
         (~&(NUMERAL m) * ~&(NUMERAL n) = &(NUMERAL (m * n)))
Proof
  REWRITE_TAC [INT_MUL, GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL, INT_NEGNEG,
               NUMERAL_DEF, INT_MUL_LZERO, INT_MUL_RZERO]
QED

Theorem INT_DIV_CALCULATE =
  LIST_CONJ [INT_DIV, INT_DIV_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG];

Theorem NB_NOT_0[local]:
    !n. ~(BIT1 n = 0) /\ ~(BIT2 n = 0)
Proof
  SIMP_TAC bool_ss [BIT1, BIT2, ADD_CLAUSES, SUC_NOT]
QED
Theorem INT_DIV_REDUCE:
  !m n.
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
            &(NUMERAL m DIV NUMERAL (BIT2 n)))
Proof
  SIMP_TAC int_ss [INT_DIV, INT_DIV_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG,
                   NUMERAL_DEF, NB_NOT_0, ZERO_DIV,
                   GSYM NOT_ZERO_LT_ZERO] THEN
  SIMP_TAC int_ss [INT_INJ, INT_NEG_EQ0, int_div, INT_NEGNEG, INT_NEG_GE0,
                   NUMERAL_DEF, NB_NOT_0, ZERO_DIV,
                   GSYM NOT_ZERO_LT_ZERO, INT_LT, INT_LE, NUM_OF_INT,
                   INT_NEG_EQ0, INT_NEG_0] THEN
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `m = 0` THEN
  ASM_SIMP_TAC int_ss [ZERO_DIV, NB_NOT_0, GSYM NOT_ZERO_LT_ZERO,
                       ZERO_MOD, INT_NEG_0, INT_ADD, INT_INJ]
QED

Theorem INT_QUOT_CALCULATE =
  LIST_CONJ [INT_QUOT, INT_QUOT_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG];

Theorem INT_QUOT_REDUCE:
  !m n.
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
            &(NUMERAL m DIV NUMERAL (BIT2 n)))
Proof
  SIMP_TAC bool_ss [INT_QUOT, INT_QUOT_NEG, INT_INJ, INT_NEG_EQ0, INT_NEGNEG,
                    NUMERAL_DEF, BIT1, BIT2, ZERO_DIV, ADD_CLAUSES, NOT_SUC,
                    prim_recTheory.LESS_0]
QED

Theorem INT_MOD_CALCULATE =
  LIST_CONJ [INT_MOD, INT_MOD_NEG, INT_NEGNEG, INT_INJ, INT_NEG_EQ0];

Theorem INT_MOD_REDUCE:
   !m n.
     (0i % &(NUMERAL (BIT1 n)) = 0i) /\
     (0i % &(NUMERAL (BIT2 n)) = 0i) /\
     (0i % -&(NUMERAL (BIT1 n)) = 0i) /\
     (0i % -&(NUMERAL (BIT2 n)) = 0i) /\
     (&(NUMERAL m) % &(NUMERAL (BIT1 n)) = &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
     (&(NUMERAL m) % &(NUMERAL (BIT2 n)) = &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
     (&(NUMERAL m) % -&(NUMERAL (BIT1 n)) =
        -(-&(NUMERAL m) % &(NUMERAL (BIT1 n)))) /\
     (&(NUMERAL m) % -&(NUMERAL (BIT2 n)) =
        -(-&(NUMERAL m) % &(NUMERAL (BIT2 n)))) /\
     (x % &(NUMERAL (BIT1 n)) =
        x - x / &(NUMERAL(BIT1 n)) * &(NUMERAL(BIT1 n))) /\
     (x % &(NUMERAL (BIT2 n)) =
        x - x / &(NUMERAL(BIT2 n)) * &(NUMERAL(BIT2 n))) /\
     (x % -&(NUMERAL (BIT1 n)) =
        (-x / &(NUMERAL(BIT1 n)) * &(NUMERAL(BIT1 n)) + x)) /\
     (x % -&(NUMERAL (BIT2 n)) =
        (-x / &(NUMERAL(BIT2 n)) * &(NUMERAL(BIT2 n)) + x))
Proof
  SIMP_TAC int_ss
    [INT_MOD_CALCULATE, BIT1, BIT2, NUMERAL_DEF, ALT_ZERO, ZERO_MOD, int_mod,
     INT_NEG_0, INT_DIV_0, INT_MUL_LZERO, INT_SUB_RZERO, INT_NEG_SUB,
     INT_SUB_RNEG]
QED


Theorem INT_REM_CALCULATE =
  LIST_CONJ [INT_REM, INT_REM_NEG, INT_NEGNEG, INT_INJ, INT_NEG_EQ0];

Theorem INT_REM_REDUCE:
  !m n. (0i rem &(NUMERAL (BIT1 n)) = 0i) /\
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
                ~&(NUMERAL m MOD NUMERAL (BIT2 n)))
Proof
  SIMP_TAC int_ss [INT_REM_CALCULATE, BIT1, BIT2,
                   NUMERAL_DEF, ALT_ZERO, ZERO_MOD]
QED

Theorem ODD_NB1[local]:
   !n. ODD(BIT1 n)
Proof
  SIMP_TAC bool_ss [BIT1, ODD, ADD_CLAUSES, ODD_ADD]
QED
Theorem EVEN_NB2[local]:
   !n. EVEN(BIT2 n)
Proof
  SIMP_TAC bool_ss [BIT2, ADD_CLAUSES, EVEN, EVEN_ADD]
QED

Theorem INT_EXP_CALCULATE:
  !p:int n m.
        (p ** 0 = 1) /\ (&n ** m = &(n EXP m)) /\
        (~&n ** NUMERAL (BIT1 m) =
           ~&(NUMERAL (n EXP NUMERAL (BIT1 m)))) /\
        (~&n ** NUMERAL (BIT2 m) =
            &(NUMERAL (n EXP NUMERAL (BIT2 m))))
Proof
  SIMP_TAC int_ss [INT_EXP, int_exp] THEN
  SIMP_TAC int_ss [NUMERAL_DEF, ODD_NB1, EVEN_NB2, INT_EXP_NEG]
QED

Theorem INT_EXP_REDUCE:
  !n m p:int.
          (p ** 0 = 1) /\
          (&(NUMERAL n):int ** (NUMERAL m) = &(NUMERAL (n EXP m))) /\
          (~&(NUMERAL n) ** NUMERAL (BIT1 m) =
             ~&(NUMERAL (n EXP BIT1 m))) /\
          (~&(NUMERAL n) ** NUMERAL (BIT2 m) =
             &(NUMERAL (n EXP BIT2 m)))
Proof
  SIMP_TAC int_ss [INT_EXP_CALCULATE, NUMERAL_DEF]
QED

Theorem INT_LT_REDUCE:
  !n m. (0i < &(NUMERAL (BIT1 n)) <=> T) /\
             (0i < &(NUMERAL (BIT2 n)) <=> T) /\
             (0i < 0i <=> F) /\
             (0i < ~&(NUMERAL n) <=> F) /\
             (&(NUMERAL n) < 0i <=> F) /\
             (~&(NUMERAL (BIT1 n)) < 0i <=> T) /\
             (~&(NUMERAL (BIT2 n)) < 0i <=> T) /\
             (&(NUMERAL n) :int < &(NUMERAL m) <=> n < m) /\
             (~&(NUMERAL (BIT1 n)) < &(NUMERAL m) <=> T) /\
             (~&(NUMERAL (BIT2 n)) < &(NUMERAL m) <=> T) /\
             (&(NUMERAL n) < ~&(NUMERAL m) <=> F) /\
             (~&(NUMERAL n) < ~&(NUMERAL m) <=> m < n)
Proof
  SIMP_TAC bool_ss [INT_LT_CALCULATE, NUMERAL_DEF, BIT1,
                    BIT2] THEN
  CONV_TAC ARITH_CONV
QED

Theorem INT_LE_CALCULATE = INT_LE_LT;

Theorem INT_LE_REDUCE:
  !n m. (0i <= 0i <=> T) /\ (0i <= &(NUMERAL n) <=> T) /\
             (0i <= ~&(NUMERAL (BIT1 n)) <=> F) /\
             (0i <= ~&(NUMERAL (BIT2 n)) <=> F) /\
             (&(NUMERAL(BIT1 n)) <= 0i <=> F) /\
             (&(NUMERAL(BIT2 n)) <= 0i <=> F) /\
             (~&(NUMERAL(BIT1 n)) <= 0i <=> T) /\
             (~&(NUMERAL(BIT2 n)) <= 0i <=> T) /\
             (&(NUMERAL n):int <= &(NUMERAL m) <=> n <= m) /\
             (&(NUMERAL n) <= ~&(NUMERAL (BIT1 m)) <=> F) /\
             (&(NUMERAL n) <= ~&(NUMERAL (BIT2 m)) <=> F) /\
             (~&(NUMERAL n) <= &(NUMERAL m) <=> T) /\
             (~&(NUMERAL n) <= ~&(NUMERAL m) <=> m <= n)
Proof
  SIMP_TAC bool_ss [NUMERAL_DEF, INT_LE_CALCULATE, INT_LT_CALCULATE,
                    int_eq_calculate, INT_INJ, INT_EQ_NEG, BIT1,
                    BIT2] THEN
  CONV_TAC ARITH_CONV
QED

Theorem INT_GT_CALCULATE = int_gt;
Theorem INT_GT_REDUCE =
  PURE_REWRITE_RULE [GSYM int_gt] INT_LT_REDUCE;
Theorem INT_GE_CALCULATE = int_ge;
Theorem INT_GE_REDUCE =
  PURE_REWRITE_RULE [GSYM int_ge] INT_LE_REDUCE;

Theorem INT_EQ_CALCULATE =
  LIST_CONJ [INT_INJ, INT_EQ_NEG, int_eq_calculate];
Theorem INT_EQ_REDUCE:
  !n m. ((0i = 0i) <=> T) /\
             ((0i = &(NUMERAL (BIT1 n))) <=> F) /\
             ((0i = &(NUMERAL (BIT2 n))) <=> F) /\
             ((0i = ~&(NUMERAL (BIT1 n))) <=> F) /\
             ((0i = ~&(NUMERAL (BIT2 n))) <=> F) /\
             ((&(NUMERAL (BIT1 n)) = 0i) <=> F) /\
             ((&(NUMERAL (BIT2 n)) = 0i) <=> F) /\
             ((~&(NUMERAL (BIT1 n)) = 0i) <=> F) /\
             ((~&(NUMERAL (BIT2 n)) = 0i) <=> F) /\
             ((&(NUMERAL n) :int = &(NUMERAL m)) <=> (n = m)) /\
             ((&(NUMERAL (BIT1 n)) = ~&(NUMERAL m)) <=> F) /\
             ((&(NUMERAL (BIT2 n)) = ~&(NUMERAL m)) <=> F) /\
             ((~&(NUMERAL (BIT1 n)) = &(NUMERAL m)) <=> F) /\
             ((~&(NUMERAL (BIT2 n)) = &(NUMERAL m)) <=> F) /\
             ((~&(NUMERAL n) :int = ~&(NUMERAL m)) <=> (n = m))
Proof
  SIMP_TAC bool_ss [INT_EQ_CALCULATE, NUMERAL_DEF, BIT1,
                    BIT2] THEN
  CONV_TAC ARITH_CONV
QED

Theorem INT_DIVIDES_REDUCE:
  !n m p:int.
          (0 int_divides 0 <=> T) /\
          (0 int_divides &(NUMERAL (BIT1 n)) <=> F) /\
          (0 int_divides &(NUMERAL (BIT2 n)) <=> F) /\
          (p int_divides 0 <=> T) /\
          (&(NUMERAL (BIT1 n)) int_divides &(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (&(NUMERAL (BIT2 n)) int_divides &(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
          (&(NUMERAL (BIT1 n)) int_divides ~&(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (&(NUMERAL (BIT2 n)) int_divides ~&(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
          (~&(NUMERAL (BIT1 n)) int_divides &(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (~&(NUMERAL (BIT2 n)) int_divides &(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
          (~&(NUMERAL (BIT1 n)) int_divides ~&(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
          (~&(NUMERAL (BIT2 n)) int_divides ~&(NUMERAL m) <=>
           (NUMERAL m MOD NUMERAL (BIT2 n) = 0))
Proof
  SIMP_TAC bool_ss [INT_DIVIDES_NEG] THEN
  SIMP_TAC bool_ss [INT_DIVIDES_MOD0, INT_EQ_CALCULATE,
                    INT_MOD_REDUCE] THEN
  SIMP_TAC bool_ss [NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, SUC_NOT] THEN
  PROVE_TAC [INT_MOD0]
QED

(* equations to put any expression build on + * ~ & int_0 int_1
   under the (unique) following forms:  &n  or ~&n

   NOTE: was in integerRingScript.sml
 *)
Theorem int_calculate :
            ( &n +  &m = &(n+m))
         /\ (~&n +  &m = if n<=m then &(m-n) else ~&(n-m))
         /\ ( &n + ~&m = if m<=n then &(n-m) else ~&(m-n))
         /\ (~&n + ~&m = ~&(n+m))

         /\ ( &n *  &m =  &(n*m))
         /\ (~&n *  &m = ~&(n*m))
         /\ ( &n * ~&m = ~&(n*m))
         /\ (~&n * ~&m =  &(n*m))

         /\ (( &n =  &m) <=> (n=m))
         /\ (( &n = ~&m) <=> (n=0)/\(m=0))
         /\ ((~&n =  &m) <=> (n=0)/\(m=0))
         /\ ((~&n = ~&m) <=> (n=m))

         /\ (~~x = x : int)
         /\ (~0 = 0 : int)
Proof
    REWRITE_TAC [INT_ADD_CALCULATE,INT_MUL_CALCULATE,INT_EQ_CALCULATE]
QED

(*---------------------------------------------------------------------------*)
(* Lemmas for intLib.                                                        *)
(*---------------------------------------------------------------------------*)

Triviality INT_POLY_CONV_sth:
  (!x y z. x + (y + z) = (x + y) + z :int) /\
  (!x y. x + y = y + x :int) /\
  (!x. &0 + x = x :int) /\
  (!x y z. x * (y * z) = (x * y) * z :int) /\
  (!x y. x * y = y * x :int) /\
  (!x. &1 * x = x :int) /\
  (!(x :int). &0 * x = &0) /\
  (!x y z. x * (y + z) = x * y + x * z :int) /\
  (!(x :int). x ** 0 = &1) /\
  (!(x :int) n. x ** (SUC n) = x * (x ** n))
Proof
  REWRITE_TAC [INT_POW, INT_ADD_ASSOC, INT_MUL_ASSOC, INT_ADD_LID,
    INT_MUL_LZERO, INT_MUL_LID, INT_LDISTRIB] THEN
  REWRITE_TAC [Once INT_ADD_SYM, Once INT_MUL_SYM]
QED

Theorem INT_POLY_CONV_sth = MATCH_MP SEMIRING_PTHS INT_POLY_CONV_sth;

Theorem INT_POLY_CONV_rth:
  (!x. -x = -(&1) * x :int) /\
  (!x y. x - y = x + -(&1) * y :int)
Proof
  REWRITE_TAC [INT_MUL_LNEG, INT_MUL_LID, int_sub]
QED

Theorem INT_INTEGRAL:
  (!(x :int). &0 * x = &0) /\
  (!x y (z :int). (x + y = x + z) <=> (y = z)) /\
  (!w x y (z :int). (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))
Proof
  REWRITE_TAC[INT_MUL_LZERO, INT_EQ_LADD] THEN
  ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
  REWRITE_TAC[GSYM INT_ENTIRE] THEN
  rpt GEN_TAC \\
  Suff ‘w * y + x * z - (w * z + x * y) = (w - x) * (y - z :int)’
  >- (Rewr' >> REWRITE_TAC []) \\
  REWRITE_TAC [INT_ADD2_SUB2] \\
  REWRITE_TAC [GSYM INT_SUB_LDISTRIB] \\
  ‘x * (z - y) = -x * (y - z :int)’
    by (REWRITE_TAC [INT_MUL_LNEG, INT_SUB_LDISTRIB, INT_NEG_SUB]) \\
  POP_ORW \\
  REWRITE_TAC [GSYM INT_RDISTRIB, GSYM int_sub]
QED

(*---------------------------------------------------------------------------*)
(* LEAST integer satisfying a predicate (may be undefined).                  *)
(*---------------------------------------------------------------------------*)

Definition LEAST_INT_DEF[nocompute]:
  LEAST_INT P = @i. P i /\ !j. j < i ==> ~P j
End

val _ = set_fixity "LEAST_INT" Binder

(* NOTE: Ported from HOL-Light *)
Theorem FORALL_INT_CASES :
    !(P :int -> bool). (!x. P x) <=> (!n. P (&n)) /\ (!n. P (-&n))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw []
 >> MP_TAC (Q.SPEC ‘x’ INT_NUM_CASES) >> rw [] (* 3 subgoals *)
 >> rw []
QED

(*---------------------------------------------------------------------------*)
(* Euclidean div and mod                                                     *)
(*---------------------------------------------------------------------------*)

Definition EDIV_DEF[nocompute]:
  ediv i j = if 0 < j then i / j else -(i / -j)
End

Definition EMOD_DEF[nocompute]:
  emod i j = i % ABS j
End

(*---------------------------------------------------------------------------*)
(* Theorems used for converting div/mod operations into ediv and emod        *)
(*---------------------------------------------------------------------------*)

Theorem INT_DIV_EDIV:
  !i j. j <> 0 ==> i / j = if 0 < j then ediv i j else -ediv (-i) j
Proof
  simp[EDIV_DEF, INT_DIV_NEG, INT_NEGNEG]
QED

Theorem INT_MOD_EMOD:
  !i j. j <> 0 ==> i % j = if 0 < j then emod i j else -emod (-i) j
Proof
  METIS_TAC[INT_MOD_NEG, INT_NEGNEG, INT_NOT_LT, INT_LT_LE, EMOD_DEF, INT_ABS]
QED

Theorem INT_QUOT_EDIV:
  !i j. j <> 0 ==> i quot j = if 0 <= i then ediv i j else ediv (-i) (-j)
Proof
  simp[EDIV_DEF, int_quot, int_div, INT_DIV_NEG, INT_NEGNEG] THEN
  METIS_TAC[INT_NEG_0, NUM_OF_INT, INT_ADD_LID, INT_LT_LE, INT_NOT_LE,
    INT_LE_NEG, ZERO_DIV, ZERO_MOD, NUM_LT]
QED

Theorem INT_REM_EMOD:
  !i j. j <> 0 ==> i rem j = if 0 <= i then emod i j else -emod (-i) j
Proof
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  simp[EMOD_DEF, int_rem, int_mod, int_quot, int_div, INT_ABS_EQ0] THEN
  simp[INT_ABS] THEN
  Cases_on `j < 0` THEN
  simp[INT_NEGNEG] THEN
  METIS_TAC[INT_MUL_CALCULATE, INT_LE_NEG, INT_LT_LE, INT_NOT_LE, INT_SUB_NEG2,
    INT_NEG_SUB, INT_NEG_EQ0]
QED

(*---------------------------------------------------------------------------*)
(* Theorems used for converting num operators into int operators             *)
(*---------------------------------------------------------------------------*)

Theorem NUM_INT_ADD:
  !m n. m + n = Num (&m + &n)
Proof
  REWRITE_TAC [INT_ADD, NUM_OF_INT]
QED

Theorem NUM_INT_SUB:
  !m n. m - n = if &m <= &n then 0n else Num (&m - &n)
Proof
  METIS_TAC[INT_LE, INT_SUB, NUM_OF_INT, NOT_LESS_EQUAL, LESS_IMP_LESS_OR_EQ,
    SUB_EQ_0, INT_LE]
QED

Theorem NUM_INT_MUL:
  !m n. m * n = Num (&m * &n)
Proof
  REWRITE_TAC [INT_MUL, NUM_OF_INT]
QED

Theorem NUM_INT_EDIV:
  !n m. n DIV m = if m = 0 then 0 else Num (ediv (&n) (&m))
Proof
  METIS_TAC[EDIV_DEF, INT_POS, INT_LT_LE, INT_DIV, NUM_OF_INT, DIV_def]
QED

Theorem NUM_INT_EMOD:
  !n m. n MOD m = if m = 0 then n else Num (emod (&n) (&m))
Proof
  METIS_TAC[EMOD_DEF, INT_ABS_NUM, INT_MOD, NUM_OF_INT, MOD_def]
QED

(*---------------------------------------------------------------------------*)

val _ = BasicProvers.export_rewrites
        ["INT_ADD_LID_UNIQ",
         "INT_ADD_RID_UNIQ",
         "INT_ADD_SUB", "INT_ADD_SUB2", "INT_DIVIDES_0",
         "INT_DIVIDES_1", "INT_DIVIDES_LADD", "INT_DIVIDES_LMUL",
         "INT_DIVIDES_LSUB", "INT_DIVIDES_MUL", "INT_DIVIDES_NEG",
         "INT_DIVIDES_RADD", "INT_DIVIDES_REFL", "INT_DIVIDES_RMUL",
         "INT_DIVIDES_RSUB", "INT_DIV", "INT_QUOT", "INT_DIV_1",
         "INT_QUOT_1", "INT_DIV_ID", "INT_QUOT_ID", "INT_DIV_NEG",
         "INT_QUOT_NEG", "INT_ENTIRE",
         "INT_EQ_LADD", "INT_EQ_LMUL", "INT_EQ_RADD", "INT_EQ_LMUL",
         "INT_EXP", "INT_EXP_EQ0", "INT_LE", "INT_LE_ADD",
         "INT_LE_ADDL", "INT_LE_ADDR", "INT_LE_DOUBLE", "INT_LE_LADD",
         "INT_LE_MUL", "INT_LE_NEG", "INT_LE_NEGL", "INT_LE_NEGR",
         "INT_LE_RADD", "INT_LE_SQUARE", "INT_LT_ADD",
         "INT_LT_ADDL", "INT_LT_ADDR", "INT_LT_CALCULATE",
         "INT_LT_IMP_LE", "INT_LT_LADD",
         "INT_LT_RADD", "INT_LT_REFL", "INT_MAX_NUM", "INT_MIN_NUM",
         "INT_MOD", "INT_REM", "INT_MOD0", "INT_REM0",
         "INT_MOD_COMMON_FACTOR", "INT_REM_COMMON_FACTOR",
         "INT_MOD_ID", "INT_REM_ID", "INT_MOD_NEG", "INT_REM_NEG",
         "INT_MUL", "INT_MUL_EQ_1", "INT_MUL_LZERO",
         "INT_MUL_RZERO",
         "INT_NEG_EQ0", "INT_NEG_GE0", "INT_NEG_GT0", "INT_NEG_LE0",
         "INT_NEG_LT0", "INT_NEG_MUL2", "INT_NEG_SAME_EQ",
         "INT_NEG_SUB", "INT_SUB_0", "INT_SUB_ADD", "INT_SUB_ADD2",
         "INT_SUB_NEG2", "INT_SUB_REFL",
         "INT_SUB_RNEG", "INT_SUB_SUB",
         "INT_SUB_SUB2", "NUM_OF_INT"]

