(*===========================================================================*)
(* Construct reals from positive reals                                       *)
(*===========================================================================*)

structure realaxScript =
struct

(*
app load ["hol88Lib",
          "numLib",
          "reduceLib",
          "pairTheory",
          "arithmeticTheory",
          "quotient",
          "jrhUtils",
          "hratTheory",
          "hrealTheory"];
*)

open HolKernel Parse boolLib hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory prim_recTheory
     jrhUtils hratTheory hrealTheory;

infix THEN THENL ORELSE ORELSEC ##;

val _ = new_theory "realax";

(*---------------------------------------------------------------------------*)
(* Required lemmas about the halfreals - mostly to drive CANCEL_TAC          *)
(*---------------------------------------------------------------------------*)

val HREAL_RDISTRIB = prove_thm("HREAL_RDISTRIB",
  (--`!x y z. (x hreal_add y) hreal_mul z =
              (x hreal_mul z) hreal_add (y hreal_mul z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HREAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HREAL_LDISTRIB);

val HREAL_EQ_ADDR = prove_thm("HREAL_EQ_ADDR",
  (--`!x y. ~(x hreal_add y = x)`--),
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC HREAL_NOZERO);

val HREAL_EQ_ADDL = prove_thm("HREAL_EQ_ADDL",
  (--`!x y. ~(x = x hreal_add y)`--),
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC HREAL_EQ_ADDR);

val HREAL_EQ_LADD = prove_thm("HREAL_EQ_LADD",
  (--`!x y z. (x hreal_add y = x hreal_add z) = (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL [(--`y:hreal`--), (--`z:hreal`--)] HREAL_ADD_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC, ALL_TAC, ALL_TAC] THEN
    POP_ASSUM(X_CHOOSE_THEN (--`d:hreal`--) SUBST1_TAC) THEN
    REWRITE_TAC[HREAL_ADD_ASSOC, HREAL_EQ_ADDR, HREAL_EQ_ADDL],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val HREAL_LT_REFL = prove_thm("HREAL_LT_REFL",
  (--`!x. ~(x hreal_lt x)`--),
  GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  REWRITE_TAC[HREAL_EQ_ADDL]);

val HREAL_LT_ADDL = prove_thm("HREAL_LT_ADDL",
  (--`!x y. x hreal_lt (x hreal_add y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  EXISTS_TAC (--`y:hreal`--) THEN REFL_TAC);

val HREAL_LT_NE = prove_thm("HREAL_LT_NE",
  (--`!x y. x hreal_lt y  ==> ~(x = y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  MATCH_ACCEPT_TAC HREAL_EQ_ADDL);

val HREAL_LT_ADDR = prove_thm("HREAL_LT_ADDR",
  (--`!x y. ~((x hreal_add y) hreal_lt x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC, HREAL_EQ_ADDL]);

val HREAL_LT_GT = prove_thm("HREAL_LT_GT",
  (--`!x y. x hreal_lt y  ==> ~(y hreal_lt x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC, HREAL_EQ_ADDL]);

val HREAL_LT_ADD2 = prove_thm("HREAL_LT_ADD2",
  (--`!x1 x2 y1 y2. x1 hreal_lt y1 /\ x2 hreal_lt y2 ==>
     (x1 hreal_add x2) hreal_lt (y1 hreal_add y2)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN (--`d1:hreal`--) SUBST1_TAC)
    (X_CHOOSE_THEN (--`d2:hreal`--) SUBST1_TAC)) THEN
  EXISTS_TAC (--`d1 hreal_add d2`--) THEN
  CONV_TAC(AC_CONV(HREAL_ADD_ASSOC,HREAL_ADD_SYM)));

val HREAL_LT_LADD = prove_thm("HREAL_LT_LADD",
  (--`!x y z. (x hreal_add y) hreal_lt (x hreal_add z) = y hreal_lt z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:hreal`--) (curry op THEN (EXISTS_TAC (--`d:hreal`--)) o MP_TAC))
  THEN REWRITE_TAC[GSYM HREAL_ADD_ASSOC, HREAL_EQ_LADD]);

(*---------------------------------------------------------------------------*)
(* CANCEL_CONV - Try to cancel, rearranging using AC laws as needed          *)
(*                                                                           *)
(* The first two arguments are the associative and commutative laws, as      *)
(* given to AC_CONV. The remaining list of theorems should be of the form:   *)
(*                                                                           *)
(* |- (a & b ~ a & c) = w (e.g. b ~ c)                                       *)
(* |-    (a & b ~ a)  = x (e.g. F)                                           *)
(* |-     (a ~ a & c) = y (e.g. T)                                           *)
(* |-         (a ~ a) = z (e.g. F)                                           *)
(*                                                                           *)
(* For some operator (written as infix &) and relation (~).                  *)
(*                                                                           *)
(* Theorems may be of the form |- ~ P or |- P, rather that equations; they   *)
(* will be transformed to |- P = F and |- P = T automatically if needed.     *)
(*                                                                           *)
(* Note that terms not cancelled will remain in their original order, but    *)
(* will be flattened to right-associated form.                               *)
(*---------------------------------------------------------------------------*)

fun intro th =
  if is_eq(concl th) then th else
  if is_neg(concl th) then EQF_INTRO th
  else EQT_INTRO th;

val lhs_rator2 = rator o rator o lhs o snd o strip_forall o concl;

fun rmel i list =
    case list of
      [] => []
    | h::t => if aconv h i then t else h :: rmel i t

fun ERR s = HOL_ERR{origin_structure = "realaxScript",
                     origin_function = "CANCEL_CONV", message = s};

fun CANCEL_CONV(assoc,sym,lcancelthms) tm =
  let val lcthms = map (intro o SPEC_ALL) lcancelthms
      val eqop = lhs_rator2 (Lib.trye hd lcthms)
      val binop = lhs_rator2 sym
      fun strip_binop tm =
        if (rator(rator tm) = binop handle HOL_ERR _ => false)
        then strip_binop (rand(rator tm)) @ strip_binop(rand tm)
        else [tm]
      val mk_binop = curry mk_comb o curry mk_comb binop
      val list_mk_binop = end_itlist mk_binop
      val (c,alist) = strip_comb tm
      val _ = assert (curry op = eqop) c
  in
    case alist of
      [l1,r1] => let
        val l = strip_binop l1
        and r = strip_binop r1
        val i = op_intersect aconv l r
      in
        if (i = []) then raise ERR "unchanged"
        else let
            val itm = list_mk_binop i
            val l' = end_itlist (C (curry op o)) (map rmel i) l
            and r' = end_itlist (C (curry op o)) (map rmel i) r
            fun mk ts = mk_binop itm (list_mk_binop ts)
                handle HOL_ERR _ => itm
            val l2 = mk l'
            val r2 = mk r'
            val le = (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq) (l1,l2)
            val re = (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq) (r1,r2)
            val eqv = MK_COMB(AP_TERM eqop le,re)
          in
            CONV_RULE(RAND_CONV
                        (end_itlist (curry op ORELSEC) (map REWR_CONV lcthms)))
                     eqv
          end
      end
    | _ => raise ERR ""
  end

(*---------------------------------------------------------------------------*)
(* Tactic to do all the obvious simplifications via cancellation etc.        *)
(*---------------------------------------------------------------------------*)
fun mk_rewrites th =
   let val th = Drule.SPEC_ALL th
       val t = Thm.concl th
   in
   if is_eq t
   then [th]
   else if is_conj t
        then (op @ o (mk_rewrites##mk_rewrites) o Drule.CONJ_PAIR) th
        else if is_neg t
             then [Drule.EQF_INTRO th]
             else [Drule.EQT_INTRO th]
   end;

val CANCEL_TAC = (C (curry op THEN)
 (PURE_REWRITE_TAC
    (itlist (append o mk_rewrites)
            [REFL_CLAUSE, EQ_CLAUSES, NOT_CLAUSES,
               AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES,
               COND_CLAUSES, FORALL_SIMP, EXISTS_SIMP,
               ABS_SIMP] []))
 o CONV_TAC o ONCE_DEPTH_CONV o end_itlist (curry op ORELSEC))
 (map CANCEL_CONV
      [(HREAL_ADD_ASSOC,HREAL_ADD_SYM,
        [HREAL_EQ_LADD, HREAL_EQ_ADDL, HREAL_EQ_ADDR, EQ_SYM]),
       (HREAL_ADD_ASSOC,HREAL_ADD_SYM,
        [HREAL_LT_LADD, HREAL_LT_ADDL, HREAL_LT_ADDR, HREAL_LT_REFL])]);

(*---------------------------------------------------------------------------*)
(* Define operations on representatives.                                     *)
(*---------------------------------------------------------------------------*)

val treal_0 = new_definition("treal_0",
  (--`treal_0 = (hreal_1,hreal_1)`--));

val treal_1 = new_definition("treal_1",
  (--`treal_1 = (hreal_1 hreal_add hreal_1,hreal_1)`--));

val treal_neg = new_definition("treal_neg",
  (--`treal_neg (x:hreal,(y:hreal)) = (y,x)`--));

val treal_add = new_infixl_definition("treal_add",
  (--`$treal_add (x1,y1) (x2,y2) = (x1 hreal_add x2, y1 hreal_add y2)`--),500);

val treal_mul = new_infixl_definition("treal_mul",
  (--`treal_mul (x1,y1) (x2,y2) =
      ((x1 hreal_mul x2) hreal_add (y1 hreal_mul y2),
       (x1 hreal_mul y2) hreal_add (y1 hreal_mul x2))`--), 600);

val treal_lt = new_definition("treal_lt",
--`treal_lt (x1,y1) (x2,y2) = (x1 hreal_add y2) hreal_lt (x2 hreal_add y1)`--);
val _ = temp_set_fixity "treal_lt" (Infix(NONASSOC, 450))

val treal_inv = new_definition("treal_inv",
  (--`treal_inv (x,y) =
      if (x = y) then treal_0
      else if y hreal_lt x then
        ((hreal_inv (x hreal_sub y)) hreal_add hreal_1,hreal_1)
      else (hreal_1,(hreal_inv(y hreal_sub x)) hreal_add hreal_1)`--));

(*---------------------------------------------------------------------------*)
(* Define the equivalence relation and prove it *is* one                     *)
(*---------------------------------------------------------------------------*)

val treal_eq = new_definition("treal_eq",
  (--`treal_eq (x1,y1) (x2,y2) = (x1 hreal_add y2 = x2 hreal_add y1)`--));
val _ = temp_set_fixity "treal_eq" (Infix(NONASSOC, 450))

val TREAL_EQ_REFL = prove_thm("TREAL_EQ_REFL",
  (--`!x. x treal_eq x`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN REFL_TAC);

val TREAL_EQ_SYM = prove_thm("TREAL_EQ_SYM",
  (--`!x y. x treal_eq y = y treal_eq x`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC);

val TREAL_EQ_TRANS = prove_thm("TREAL_EQ_TRANS",
  (--`!x y z. x treal_eq y /\ y treal_eq z ==> x treal_eq z`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN
  DISCH_THEN(MP_TAC o MK_COMB o (AP_TERM (--`$hreal_add`--) ## I) o CONJ_PAIR)
  THEN CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN CANCEL_TAC);

val TREAL_EQ_EQUIV = prove_thm("TREAL_EQ_EQUIV",
  (--`!p q. p treal_eq q = ($treal_eq p = $treal_eq q)`--),
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV (--`r:hreal#hreal`--))) THEN
  EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC (--`q:hreal#hreal`--)) THEN
      REWRITE_TAC[TREAL_EQ_REFL],
      DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
       [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TREAL_EQ_SYM]), ALL_TAC] THEN
      POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
      MATCH_ACCEPT_TAC TREAL_EQ_TRANS]);

val TREAL_EQ_AP = prove_thm("TREAL_EQ_AP",
  (--`!p q. (p = q) ==> p treal_eq q`--),
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC TREAL_EQ_REFL);

(*---------------------------------------------------------------------------*)
(* Prove the properties of representatives                                   *)
(*---------------------------------------------------------------------------*)

val TREAL_10 = prove_thm("TREAL_10",
  (--`~(treal_1 treal_eq treal_0)`--),
  REWRITE_TAC[treal_1, treal_0, treal_eq, HREAL_NOZERO]);

val TREAL_ADD_SYM = prove_thm("TREAL_ADD_SYM",
  (--`!x y. x treal_add y = y treal_add x`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                  [HREAL_ADD_SYM] THEN
  REFL_TAC);

val TREAL_MUL_SYM = prove_thm("TREAL_MUL_SYM",
  (--`!x y. x treal_mul y = y treal_mul x`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                  [HREAL_MUL_SYM] THEN
  REWRITE_TAC[PAIR_EQ] THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);

val TREAL_ADD_ASSOC = prove_thm("TREAL_ADD_ASSOC",
  (--`!x y z. x treal_add (y treal_add z) = (x treal_add y) treal_add z`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC]);

val TREAL_MUL_ASSOC = prove_thm("TREAL_MUL_ASSOC",
  (--`!x y z. x treal_mul (y treal_mul z) = (x treal_mul y) treal_mul z`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul] THEN
  REWRITE_TAC[HREAL_LDISTRIB, HREAL_RDISTRIB, PAIR_EQ, GSYM HREAL_MUL_ASSOC]
  THEN CONJ_TAC THEN CANCEL_TAC);

val TREAL_LDISTRIB = prove_thm("TREAL_LDISTRIB",
  (--`!x y z. x treal_mul (y treal_add z) =
       (x treal_mul y) treal_add (x treal_mul z)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul, treal_add] THEN
  REWRITE_TAC[HREAL_LDISTRIB, PAIR_EQ] THEN
  CONJ_TAC THEN CANCEL_TAC);

val TREAL_ADD_LID = prove_thm("TREAL_ADD_LID",
  (--`!x. (treal_0 treal_add x) treal_eq x`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_add, treal_eq] THEN
  CANCEL_TAC);

val TREAL_MUL_LID = prove_thm("TREAL_MUL_LID",
  (--`!x. (treal_1 treal_mul x) treal_eq x`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_1, treal_mul, treal_eq] THEN
  REWRITE_TAC[HREAL_MUL_LID, HREAL_LDISTRIB, HREAL_RDISTRIB] THEN
  CANCEL_TAC THEN CANCEL_TAC);

val TREAL_ADD_LINV = prove_thm("TREAL_ADD_LINV",
  (--`!x. ((treal_neg x) treal_add x) treal_eq treal_0`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_neg, treal_add, treal_eq, treal_0]
  THEN CANCEL_TAC);

val TREAL_INV_0 = prove_thm("TREAL_INV_0",
 Term`treal_inv (treal_0) treal_eq (treal_0)`,
  REWRITE_TAC[treal_inv, treal_eq, treal_0]);

val TREAL_MUL_LINV = prove_thm("TREAL_MUL_LINV",
  (--`!x. ~(x treal_eq treal_0) ==>
              (((treal_inv x) treal_mul x) treal_eq treal_1)`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_eq, treal_inv] THEN
  CANCEL_TAC THEN DISCH_TAC THEN DISJ_CASES_THEN2
    (fn th => MP_TAC th THEN ASM_REWRITE_TAC[]) (DISJ_CASES_THEN ASSUME_TAC)
    (SPECL [(--`FST (x:hreal#hreal)`--), (--`SND (x:hreal#hreal)`--)] HREAL_LT_TOTAL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HREAL_LT_GT) THEN
  PURE_ASM_REWRITE_TAC[COND_CLAUSES, treal_mul, treal_eq, treal_1] THEN
  REWRITE_TAC[HREAL_MUL_LID, HREAL_LDISTRIB, HREAL_RDISTRIB] THEN
  CANCEL_TAC THEN W(SUBST1_TAC o SYM o C SPEC HREAL_MUL_LINV o
    find_term(fn tm => rator(rator tm) = (--`$hreal_sub`--) handle _ => false) o snd) THEN
  REWRITE_TAC[GSYM HREAL_LDISTRIB] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HREAL_SUB_ADD) THEN REFL_TAC);

val TREAL_LT_TOTAL = prove_thm("TREAL_LT_TOTAL",
  (--`!x y. x treal_eq y \/ x treal_lt y \/ y treal_lt x`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_eq] THEN
  MATCH_ACCEPT_TAC HREAL_LT_TOTAL);

val TREAL_LT_REFL = prove_thm("TREAL_LT_REFL",
  (--`!x. ~(x treal_lt x)`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt] THEN
  MATCH_ACCEPT_TAC HREAL_LT_REFL);

val TREAL_LT_TRANS = prove_thm("TREAL_LT_TRANS",
  (--`!x y z. x treal_lt y /\ y treal_lt z ==> x treal_lt z`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HREAL_LT_ADD2) THEN CANCEL_TAC THEN
  DISCH_TAC THEN GEN_REWR_TAC RAND_CONV  [HREAL_ADD_SYM]
  THEN POP_ASSUM ACCEPT_TAC);

val TREAL_LT_ADD = prove_thm("TREAL_LT_ADD",
  (--`!x y z. (y treal_lt z) ==> (x treal_add y) treal_lt (x treal_add z)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_add] THEN
  CANCEL_TAC);

val TREAL_LT_MUL = prove_thm("TREAL_LT_MUL",
  (--`!x y. treal_0 treal_lt x /\ treal_0 treal_lt y ==>
           treal_0 treal_lt (x treal_mul y)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_lt, treal_mul] THEN
  CANCEL_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[HREAL_LT])) THEN
  REWRITE_TAC[HREAL_LDISTRIB, HREAL_RDISTRIB] THEN CANCEL_TAC THEN CANCEL_TAC);

(*---------------------------------------------------------------------------*)
(* Rather than grub round proving the supremum property for representatives, *)
(* we prove the appropriate order-isomorphism {x::R|0 < r} <-> R^+           *)
(*---------------------------------------------------------------------------*)

val treal_of_hreal = new_definition("treal_of_hreal",
  (--`treal_of_hreal x = (x hreal_add hreal_1,hreal_1)`--));

val hreal_of_treal = new_definition("hreal_of_treal",
  (--`hreal_of_treal (x,y) = @d. x = y hreal_add d`--));

val TREAL_BIJ = prove_thm("TREAL_BIJ",
  (--`(!h. (hreal_of_treal(treal_of_hreal h)) = h) /\
   (!r. treal_0 treal_lt r = (treal_of_hreal(hreal_of_treal r)) treal_eq r)`--),
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[treal_of_hreal, hreal_of_treal] THEN
    CANCEL_TAC THEN CONV_TAC SYM_CONV THEN
    CONV_TAC(funpow 2 RAND_CONV ETA_CONV) THEN
    MATCH_MP_TAC SELECT_AX THEN EXISTS_TAC (--`h:hreal`--) THEN REFL_TAC,
    GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_lt, treal_eq,
      treal_of_hreal, hreal_of_treal] THEN CANCEL_TAC THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP HREAL_SUB_ADD) THEN
      DISCH_THEN(CONV_TAC o RAND_CONV o REWR_CONV o SYM o SELECT_RULE o
      EXISTS((--`?d. d hreal_add (SND r) = FST r`--), (--`(FST r) hreal_sub (SND r)`--)))
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                      [HREAL_ADD_SYM] THEN
      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN REFL_TAC,
      DISCH_THEN(SUBST1_TAC o SYM) THEN CANCEL_TAC]]);

val TREAL_ISO = prove_thm("TREAL_ISO",
  (--`!h i. h hreal_lt i ==> (treal_of_hreal h) treal_lt (treal_of_hreal i)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[treal_of_hreal, treal_lt] THEN CANCEL_TAC THEN
  CANCEL_TAC);

val TREAL_BIJ_WELLDEF = prove_thm("TREAL_BIJ_WELLDEF",
  (--`!h i. h treal_eq i ==> (hreal_of_treal h = hreal_of_treal i)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq, hreal_of_treal] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC(X_FUN_EQ_CONV (--`d:hreal`--)) THEN
  GEN_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM (--`SND(i:hreal#hreal)`--) o AP_TERM (--`$hreal_add`--))
    THEN POP_ASSUM SUBST1_TAC,
    DISCH_THEN(MP_TAC o C AP_THM (--`SND(h:hreal#hreal)`--) o AP_TERM (--`$hreal_add`--))
    THEN POP_ASSUM(SUBST1_TAC o SYM)] THEN
  CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);

(*---------------------------------------------------------------------------*)
(* Prove that the operations on representatives are well-defined             *)
(*---------------------------------------------------------------------------*)

val TREAL_NEG_WELLDEF = prove_thm("TREAL_NEG_WELLDEF",
  (--`!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_neg, treal_eq] THEN
  DISCH_THEN(curry op THEN (ONCE_REWRITE_TAC[HREAL_ADD_SYM]) o SUBST1_TAC) THEN
  REFL_TAC);

val TREAL_ADD_WELLDEFR = prove_thm("TREAL_ADD_WELLDEFR",
  (--`!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add, treal_eq] THEN
  CANCEL_TAC);

val TREAL_ADD_WELLDEF = prove_thm("TREAL_ADD_WELLDEF",
  (--`!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_add y1) treal_eq (x2 treal_add y2)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC (--`x1 treal_add y2`--) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_ADD_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TREAL_ADD_WELLDEFR THEN ASM_REWRITE_TAC[]);

val TREAL_MUL_WELLDEFR = prove_thm("TREAL_MUL_WELLDEFR",
  (--`!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul, treal_eq] THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    (--`(a hreal_add b) hreal_add (c hreal_add d) =
     (a hreal_add d) hreal_add (b hreal_add c)`--)] THEN
  REWRITE_TAC[GSYM HREAL_RDISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val TREAL_MUL_WELLDEF = prove_thm("TREAL_MUL_WELLDEF",
  (--`!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC (--`x1 treal_mul y2`--) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_MUL_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TREAL_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);

val TREAL_LT_WELLDEFR = prove_thm("TREAL_LT_WELLDEFR",
  (--`!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_lt y = x2 treal_lt y)`--),
  let fun mkc v tm = SYM(SPECL (v::snd(strip_comb tm)) HREAL_LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc (--`SND (x1:hreal#hreal)`--))) THEN
  CONV_TAC(LAND_CONV(mkc (--`SND (x2:hreal#hreal)`--))) THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    (--`a hreal_add (b hreal_add c) = (b hreal_add a) hreal_add c`--)] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC end);

val TREAL_LT_WELLDEFL = prove_thm("TREAL_LT_WELLDEFL",
  (--`!x y1 y2. y1 treal_eq y2 ==> (x treal_lt y1 = x treal_lt y2)`--),
  let fun mkc v tm = SYM(SPECL (v::snd(strip_comb tm)) HREAL_LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc (--`FST (y1:hreal#hreal)`--))) THEN
  CONV_TAC(LAND_CONV(mkc (--`FST (y2:hreal#hreal)`--))) THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    (--`a hreal_add (b hreal_add c) = (a hreal_add c) hreal_add b`--)] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC THEN AP_TERM_TAC THEN CANCEL_TAC end);

val TREAL_LT_WELLDEF = prove_thm("TREAL_LT_WELLDEF",
  (--`!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_lt y1 = x2 treal_lt y2)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC (--`x1 treal_lt y2`--) THEN CONJ_TAC THENL
   [MATCH_MP_TAC TREAL_LT_WELLDEFL, MATCH_MP_TAC TREAL_LT_WELLDEFR] THEN
  ASM_REWRITE_TAC[]);

val TREAL_INV_WELLDEF = prove_thm("TREAL_INV_WELLDEF",
  (--`!x1 x2. x1 treal_eq x2 ==> (treal_inv x1) treal_eq (treal_inv x2)`--),
  let val lemma1 = PROVE
   ((--`(a hreal_add b' = b hreal_add a') ==>
        (a' hreal_lt a = b' hreal_lt b)`--),
    DISCH_TAC THEN EQ_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[HREAL_LT]) THEN
    POP_ASSUM MP_TAC THEN CANCEL_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN CANCEL_TAC)
  val lemma2 = PROVE
   ((--`(a hreal_add b' = b hreal_add a') ==>
        ((a = a') = (b = b'))`--),
    DISCH_TAC THEN EQ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC
    THEN CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_inv, treal_eq] THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP lemma1) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP lemma2) THEN COND_CASES_TAC THEN
  REWRITE_TAC[TREAL_EQ_REFL] THEN COND_CASES_TAC THEN REWRITE_TAC[treal_eq]
  THEN CANCEL_TAC THEN CANCEL_TAC THEN AP_TERM_TAC THEN
  W(FREEZE_THEN(CONV_TAC o REWR_CONV) o GSYM o C SPEC HREAL_EQ_LADD o
    mk_comb o (curry mk_comb (--`$hreal_add`--) ## I) o (rand ## rand) o dest_eq o snd)
  THEN ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [HREAL_ADD_SYM] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC] THENL
   [RULE_ASSUM_TAC GSYM,
    MP_TAC(SPECL[(--`FST(x2:hreal#hreal)`--), (--`SND(x2:hreal#hreal)`--)]
    HREAL_LT_TOTAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[HREAL_ADD_SYM])] THEN
  FIRST_ASSUM(fn th => FIRST_ASSUM(MP_TAC o EQ_MP (MATCH_MP lemma1 th))) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert(curry op =(--`$hreal_lt`--) o rator o rator) o concl)
  THEN REPEAT(DISCH_THEN(SUBST1_TAC o MATCH_MP HREAL_SUB_ADD)) THEN
  FIRST_ASSUM SUBST1_TAC THEN REFL_TAC end);

(*---------------------------------------------------------------------------*)
(* Now define the functions over the equivalence classes                     *)
(*---------------------------------------------------------------------------*)

val [REAL_10, REAL_ADD_SYM, REAL_MUL_SYM, REAL_ADD_ASSOC,
     REAL_MUL_ASSOC, REAL_LDISTRIB, REAL_ADD_LID, REAL_MUL_LID,
     REAL_ADD_LINV, REAL_MUL_LINV, REAL_LT_TOTAL, REAL_LT_REFL,
     REAL_LT_TRANS, REAL_LT_IADD, REAL_LT_MUL, REAL_BIJ, REAL_ISO,REAL_INV_0] =
 let fun mk_def (d,t,n,f) = {def_name=d, fixity=f, fname=n, func=t}
 in
  quotient.define_equivalence_type
   {name = "real",
    equiv = TREAL_EQ_EQUIV,
    defs = [mk_def("real_0",   Term`treal_0`,   "real_0", Prefix),
            mk_def("real_1",   Term`treal_1`,   "real_1", Prefix),
            mk_def("real_neg", Term`treal_neg`, "real_neg", Prefix),
            mk_def("real_inv", Term`treal_inv`, "inv", Prefix),
            mk_def("real_add", Term`$treal_add`, "real_add", Infixl 500),
            mk_def("real_mul",  Term`$treal_mul`, "real_mul", Infixl 600),
            mk_def("real_lt",  Term`$treal_lt`,  "real_lt",  Prefix),
            mk_def("real_of_hreal",Term`$treal_of_hreal`, "real_of_hreal",Prefix),
            mk_def("hreal_of_real", Term`$hreal_of_treal`,"hreal_of_real",Prefix)],
    welldefs = [TREAL_NEG_WELLDEF, TREAL_INV_WELLDEF, TREAL_LT_WELLDEF,
                TREAL_ADD_WELLDEF, TREAL_MUL_WELLDEF, TREAL_BIJ_WELLDEF],
    old_thms = ([TREAL_10]
                @ (map (GEN_ALL o MATCH_MP TREAL_EQ_AP o SPEC_ALL)
                       [TREAL_ADD_SYM, TREAL_MUL_SYM, TREAL_ADD_ASSOC,
                        TREAL_MUL_ASSOC, TREAL_LDISTRIB])
                @ [TREAL_ADD_LID, TREAL_MUL_LID, TREAL_ADD_LINV,
                   TREAL_MUL_LINV, TREAL_LT_TOTAL, TREAL_LT_REFL,
                   TREAL_LT_TRANS, TREAL_LT_ADD, TREAL_LT_MUL, TREAL_BIJ,
                   TREAL_ISO,TREAL_INV_0])}
 end;

(*---------------------------------------------------------------------------
       Overload arithmetic operations.
 ---------------------------------------------------------------------------*)

val natplus  = Term`$+`;
val natless  = Term`$<`;
val bool_not = Term`$~`
val natmult  = Term`$*`;

val _ = overload_on ("~", bool_not);

val _ = overload_on ("+", natplus);
val _ = overload_on ("*", natmult);
val _ = overload_on ("<", natless);

val _ = overload_on ("~", Term`$real_neg`);
val _ = overload_on ("numeric_negate", Term`$real_neg`);
val _ = overload_on ("+", Term`$real_add`);
val _ = overload_on ("*", Term`$real_mul`);
val _ = overload_on ("<", Term`real_lt`);


(*---------------------------------------------------------------------------*)
(* Transfer of supremum property for all-positive sets - bit painful         *)
(*---------------------------------------------------------------------------*)

val REAL_ISO_EQ = prove_thm("REAL_ISO_EQ",
  (--`!h i. h hreal_lt i = real_of_hreal h < real_of_hreal i`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC REAL_ISO,
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [(--`h:hreal`--), (--`i:hreal`--)] HREAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_ISO th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
    REWRITE_TAC[REAL_LT_REFL]]);

val REAL_POS = prove_thm("REAL_POS",
  (--`!X. real_0 < real_of_hreal X`--),
  GEN_TAC THEN REWRITE_TAC[REAL_BIJ]);

val SUP_ALLPOS_LEMMA1 = prove_thm("SUP_ALLPOS_LEMMA1",
  (--`!P y. (!x. P x ==> real_0 < x) ==>
            ((?x. P x /\ y < x) =
            (?X. P(real_of_hreal X) /\ y < (real_of_hreal X)))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) (fn th => MP_TAC th THEN POP_ASSUM
     (SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ] o C MATCH_MP (CONJUNCT1 th))))
    THEN DISCH_TAC THEN EXISTS_TAC (--`hreal_of_real x`--) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(X_CHOOSE_THEN (--`X:hreal`--) ASSUME_TAC) THEN
    EXISTS_TAC (--`real_of_hreal X`--) THEN ASM_REWRITE_TAC[]]);

val SUP_ALLPOS_LEMMA2 = prove_thm("SUP_ALLPOS_LEMMA2",
  (--`!P X. P(real_of_hreal X) :bool = (\h. P(real_of_hreal h)) X`--),
  REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);

val SUP_ALLPOS_LEMMA3 = prove_thm("SUP_ALLPOS_LEMMA3",
  (--`!P. (!x. P x ==> real_0 < x) /\
          (?x. P x) /\
          (?z. !x. P x ==> x < z)
           ==> (?X. (\h. P(real_of_hreal h)) X) /\
               (?Y. !X. (\h. P(real_of_hreal h)) X ==> X hreal_lt Y)`--),
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [EXISTS_TAC (--`hreal_of_real x`--) THEN BETA_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o REWRITE_RULE[REAL_BIJ] o
                C MATCH_MP (ASSUME (--`(P:real->bool) x`--))) THEN
    FIRST_ASSUM ACCEPT_TAC,
    EXISTS_TAC (--`hreal_of_real z`--) THEN BETA_TAC THEN GEN_TAC THEN
    UNDISCH_TAC (--`(P:real->bool) x`--) THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(fn th => EVERY_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[REAL_ISO_EQ] THEN
    MP_TAC(SPECL[(--`real_0`--), (--`real_of_hreal X`--), (--`z:real`--)] REAL_LT_TRANS) THEN
    ASM_REWRITE_TAC[REAL_BIJ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

val SUP_ALLPOS_LEMMA4 = prove_thm("SUP_ALLPOS_LEMMA4",
  (--`!y. ~(real_0 < y) ==> !x. y < (real_of_hreal x)`--),
  GEN_TAC THEN DISCH_THEN(curry op THEN GEN_TAC o MP_TAC) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [(--`y:real`--), (--`real_0`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM(MP_TAC o C CONJ (SPEC (--`x:hreal`--) REAL_POS)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_TRANS));

val REAL_SUP_ALLPOS = prove_thm("REAL_SUP_ALLPOS",
  (--`!P. (!x. P x ==> real_0 < x) /\ (?x. P x) /\ (?z. !x. P x ==> x < z)
    ==> (?s. !y. (?x. P x /\ y < x) = y < s)`--),
  let val lemma = TAUT_CONV (--`a /\ b ==> (a = b)`--) in
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC (--`real_of_hreal(hreal_sup(\h. P(real_of_hreal h)))`--) THEN
  GEN_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUP_ALLPOS_LEMMA1(CONJUNCT1 th)]) THEN
  ASM_CASES_TAC (--`real_0 < y`--) THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ]) THEN
    REWRITE_TAC[GSYM REAL_ISO_EQ] THEN
    GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
                    [SUP_ALLPOS_LEMMA2] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HREAL_SUP o MATCH_MP SUP_ALLPOS_LEMMA3)
    THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP SUP_ALLPOS_LEMMA3) THEN
      BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`X:hreal`--) o CONJUNCT1) THEN
      EXISTS_TAC (--`X:hreal`--) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SUP_ALLPOS_LEMMA4)] end);

(*---------------------------------------------------------------------------*)
(* Now save all the unsaved theorems                                         *)
(*---------------------------------------------------------------------------*)

val _ = map save_thm
 [("REAL_10",REAL_10),               ("REAL_ADD_SYM",REAL_ADD_SYM),
  ("REAL_MUL_SYM",REAL_MUL_SYM),     ("REAL_ADD_ASSOC",REAL_ADD_ASSOC),
  ("REAL_MUL_ASSOC",REAL_MUL_ASSOC), ("REAL_LDISTRIB",REAL_LDISTRIB),
  ("REAL_ADD_LID",REAL_ADD_LID),     ("REAL_MUL_LID",REAL_MUL_LID),
  ("REAL_ADD_LINV",REAL_ADD_LINV),   ("REAL_MUL_LINV",REAL_MUL_LINV),
  ("REAL_LT_TOTAL",REAL_LT_TOTAL),   ("REAL_LT_REFL",REAL_LT_REFL),
  ("REAL_LT_TRANS",REAL_LT_TRANS),   ("REAL_LT_IADD",REAL_LT_IADD),
  ("REAL_LT_MUL",REAL_LT_MUL),       ("REAL_INV_0",REAL_INV_0)];

val _ = export_theory();

end;
