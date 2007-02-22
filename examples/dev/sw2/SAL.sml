
(*---------------------------------------------------------------------------*)
(* Labels                                                                    *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `
    LABEL = L of num`;

val inc_def = Define `
    inc (L i) = L (i + 1)`;

(*---------------------------------------------------------------------------*)
(* Structured Assembly Language                                              *)
(* Syntax                                                                    *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `
    INST = ASG of num => num`;

val _ = Hol_datatype `
     COMPOSITE =
        BLK of LABEL => INST list => LABEL
     |  IFGOTO of LABEL => bool => LABEL # LABEL
     |  UNION of COMPOSITE => COMPOSITE`;

val _ = overload_on ("&",Term`UNION`);
val _ = set_fixity "&" (Infixl 650);

(*---------------------------------------------------------------------------*)
(* Structured Assembly Language                                              *)
(* Natural Operational Semantics                                             *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `
     VALUE = 
           NOP
        |  OP of num => num`;

(* Natural semantics represented by reduction rules *)

val (fix_rule, fix_ind, fix_case) =
    Hol_reln `
    ((fix (\f. f = e f)) v = e v)`;

val (ns_rule, ns_ind, ns_case) =
    Hol_reln `
    (R (l1, BLK l1 [ASG v w] (inc l1), (inc l1)) (OP w v)) /\
    (R (l1, BLK l1 instL l2, l2) (OP (f x) w) ==>
       R (l1, BLK l1 ((ASG x v) :: instL) l2, l2) (OP (let x = v in (f x)) w)) /\
    (R (l1, S1, l2) NOP /\ R (l2, S2, l3) value ==>
       R (l1, UNION S1 S2, l3) value) /\
    (R (l1, S1, l2) (OP e_1 v) /\ R (l2, S2, l3) (OP (f v) w) ==>
       R (l1, UNION S1 S2, l3) (OP (f e_1) w)) /\

    (R (l1, S1, l2) v1 /\ R (l3, S2, l4) v2 /\ ~(l2 = l3) ==>
       R (l1, UNION S1 S2, l2) v1) /\
    (cond /\ R (l2, S2, l4) value ==>
       R (l1, UNION (IFGOTO l1 cond (l2,l3)) S2, l4) value) /\
    (~cond /\ R (l2, S2, l4) value ==>
       R (l1, UNION (IFGOTO l1 cond (l2,l3)) S2, l3) NOP)
  `;

val inst_rule = CONJUNCT1 reduce_rule;
val block_rule = CONJUNCT1 (CONJUNCT2 reduce_rule);
val nop_rule = (CONJUNCT1 o CONJUNCT2 o CONJUNCT2) reduce_rule;
val seq_rule = (CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) reduce_rule;
val omit_rule = (CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) reduce_rule;
val ift_rule = (CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) reduce_rule;
val iff_rule = (CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) reduce_rule;

(*---------------------------------------------------------------------------*)
(* Translate if-then-else structures into structured assembly                *)
(*---------------------------------------------------------------------------*)

val REDUCE_CONDITIONAL = store_thm (
  "REDUCE_CONDITIONAL",
  ``R (l2, S1, l4) (OP e1 v) /\ R (l3, S2, l4) (OP e2 v) /\ ~(l2 = l3) /\ ~(l3 = l4) ==>
    R (l1, ((IFGOTO l1 cond (l2,l3)) & S1 & S2), l4) (OP (if cond then e1 else e2) v)``,
   Cases_on `cond` THEN
   RW_TAC std_ss [] THENL [
     IMP_RES_TAC (SIMP_RULE std_ss [] ift_rule) THEN
       METIS_TAC [omit_rule],
     IMP_RES_TAC (SIMP_RULE std_ss [] iff_rule) THEN
       METIS_TAC [nop_rule]
   ]
  );

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

(* 
val f_def = Define `f x = 
         if x = 0 then x else x + f (x - 1)`;

val f = ``\f x. if x = 0 then x else x + f (x - 1)``;
val f' = ``(\f x. if x = 0 then x else x + f (x - 1)) f x``;
*)

val example_1 = prove (
   ``(R (l1, BLK l1 [ASG y (a + b); ASG x (a * y)] (inc l1), (inc l1)) 
       (OP (let y = a + b in (\y. a * y) y) x))``,
   MATCH_MP_TAC (SPEC_ALL block_rule) THEN
   RW_TAC std_ss [inst_rule]
 );
