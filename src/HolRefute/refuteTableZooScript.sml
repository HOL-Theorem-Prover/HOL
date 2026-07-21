Theory refuteTableZoo
Ancestors
  refute ltree itreeTau fixedPoint
Libs
  TotalDefn Refute_Core quotient

Datatype:
  zoo_tree = ZooLeaf num | ZooNode zoo_tree zoo_tree
End

Datatype:
  zoo_record = <| zoo_num : num; zoo_bit : bool |>
End

Datatype:
  zoo_poly_record = <| zoo_poly : 'a; zoo_poly_bit : bool |>
End

Datatype:
  zoo_poly_tail_record =
    <| zoo_tail_bit : bool; zoo_tail_poly : 'a |>
End

Definition zoo_bool_rel_def:
  zoo_bool_rel (x : bool) y = (x = y)
End

Theorem zoo_bool_equiv:
  !x y. zoo_bool_rel x y = (zoo_bool_rel x = zoo_bool_rel y)
Proof
  simp [zoo_bool_rel_def, EQ_IMP_THM, FUN_EQ_THM] >>
  metis_tac []
QED

val zoo_bool_quot_def =
  define_quotient_type "zoo_bool_quot" "zoo_bool_quot_abs"
    "zoo_bool_quot_rep" zoo_bool_equiv;

Theorem zoo_three_exists[local]:
  ?n : num. (\n. n < 3) n
Proof
  qexists_tac `0` >> simp []
QED

val zoo_three_tydef =
  new_type_definition ("zoo_three", zoo_three_exists);

val zoo_three_absrep = define_new_type_bijections
  {name = "zoo_three_absrep", ABS = "zoo_three_abs",
   REP = "zoo_three_rep", tyax = zoo_three_tydef};

Definition zoo_three_rep_wrapper_def:
  zoo_three_rep_wrapper b (x : zoo_three) =
    if b then zoo_three_rep x else zoo_three_rep x
End

Theorem zoo_univ_exists[local]:
  ?n : num. (\n. T) n
Proof
  qexists_tac `0` >> simp []
QED

val zoo_univ_tydef =
  new_type_definition ("zoo_univ", zoo_univ_exists);

val zoo_univ_absrep = define_new_type_bijections
  {name = "zoo_univ_absrep", ABS = "zoo_univ_abs",
   REP = "zoo_univ_rep", tyax = zoo_univ_tydef};

Datatype:
  zoo_even_tree = ZooEvenLeaf num | ZooEvenNode zoo_odd_tree ;
  zoo_odd_tree = ZooOddNode zoo_even_tree
End

val zoo_total_def = TotalDefn.qDefine "zoo_total_def" `
  zoo_total (n : num) =
    if n = 0 then 0 else SUC (zoo_total (n - 1))
`
  (SOME (WF_REL_TAC `measure I` >> simp []));

val zoo_height_def =
  Prim_rec.new_recursive_definition
    {name = "zoo_height_def",
     rec_axiom = DB.fetch "-" "zoo_tree_Axiom",
     def = ``(zoo_height (ZooLeaf n) = n) /\
             (zoo_height (ZooNode left right) =
                SUC (zoo_height left + zoo_height right))``};

Theorem zoo_spec_exists[local]:
  ?n : num. EVEN n
Proof
  qexists_tac `0` >> simp []
QED

val zoo_spec_property =
  new_specification
    ("zoo_spec_property", ["zoo_spec"], zoo_spec_exists);

val zoo_raw_spec_property =
  new_specification
    ("zoo_raw_spec_property[notuserdef]", ["zoo_raw_spec"],
     zoo_spec_exists);

val zoo_mutual_def = TotalDefn.Define `
  (zoo_even 0 = T) /\
  (zoo_even (SUC n) = zoo_odd n) /\
  (zoo_odd 0 = F) /\
  (zoo_odd (SUC n) = zoo_even n)
`;

Definition zoo_override_def:
  zoo_override n = n
End

Theorem zoo_override_old[refute_unfold]:
  zoo_override n = n + 0
Proof
  simp [zoo_override_def]
QED

Theorem zoo_override_latest[refute_unfold]:
  zoo_override n = n
Proof
  simp [zoo_override_def]
QED

Inductive zoo_wf_lfp:
  zoo_wf_lfp 0 /\
  (!n. zoo_wf_lfp n ==> zoo_wf_lfp (SUC n))
End

Inductive zoo_nonwf_lfp:
  !n : num. zoo_nonwf_lfp n ==> zoo_nonwf_lfp n
End

CoInductive zoo_wf_gfp:
  zoo_wf_gfp 0 /\
  (!n. zoo_wf_gfp n ==> zoo_wf_gfp (SUC n))
End

CoInductive zoo_guarded_gfp:
  !b. b /\ zoo_guarded_gfp b ==> zoo_guarded_gfp b
End

CoInductive zoo_mutual_gfp:
  (!b. b /\ zoo_mutual_other_gfp b ==> zoo_mutual_gfp b) /\
  (!b. b /\ zoo_mutual_gfp b ==> zoo_mutual_other_gfp b)
End

(* These deliberately misleading bindings ensure that group discovery ties
   a cases/rules stem to the coinduction theorem stored in the registry. *)
Theorem zoo_mutual_other_gfp_cases:
  !b. zoo_mutual_other_gfp b <=> zoo_mutual_other_gfp b
Proof
  simp []
QED

Theorem zoo_mutual_other_gfp_rules:
  !b. zoo_mutual_other_gfp b ==> zoo_mutual_other_gfp b
Proof
  simp []
QED

Definition zoo_hand_gfp_def:
  zoo_hand_gfp = fixedPoint$gfp (\p : bool -> bool. p)
End

Inductive zoo_unroll_lfp:
  zoo_unroll_lfp 0 /\
  (!n. zoo_unroll_lfp n ==> zoo_unroll_lfp (SUC n)) /\
  (!n. zoo_unroll_lfp n ==> zoo_unroll_lfp n)
End

Inductive zoo_nonlinear_lfp:
  zoo_nonlinear_lfp (0 : num) /\
  (!(m : num) n. zoo_nonlinear_lfp m /\ zoo_nonlinear_lfp n ==>
                  zoo_nonlinear_lfp (m + n))
End

Inductive zoo_param_lfp:
  (!k : num. zoo_param_lfp k 0) /\
  (!k n. zoo_param_lfp k n ==>
         zoo_param_lfp k (SUC n))
End

Inductive zoo_poly_lfp:
  (!(x : 'a). zoo_poly_lfp x 0) /\
  (!x n. zoo_poly_lfp x n ==>
         zoo_poly_lfp x (SUC n))
End

Inductive zoo_mutual_lfp:
  zoo_mutual_lfp 0 /\
  (!n. zoo_mutual_other_lfp n ==>
       zoo_mutual_lfp (SUC n)) /\
  (!n. zoo_mutual_lfp n ==>
       zoo_mutual_other_lfp (SUC n))
End

(* The final, extensionally redundant rule makes the group's recursive
   relation non-well-founded without changing its even/odd least fixpoint. *)
Inductive zoo_mutual_nonwf_lfp:
  zoo_mutual_nonwf_lfp 0 /\
  (!n. zoo_mutual_nonwf_other_lfp n ==>
       zoo_mutual_nonwf_lfp (SUC n)) /\
  (!n. zoo_mutual_nonwf_lfp n ==>
       zoo_mutual_nonwf_other_lfp (SUC n)) /\
  (!n. zoo_mutual_nonwf_lfp n ==>
       zoo_mutual_nonwf_lfp n)
End

(* Two instances in one model-finder context must retain distinct iterator
   markers even though their generated unroll constants share a name. *)
Inductive zoo_mutual_poly_nonwf_lfp:
  (!(x : 'a). zoo_mutual_poly_nonwf_lfp x 0) /\
  (!x n. zoo_mutual_poly_nonwf_other_lfp x n ==>
         zoo_mutual_poly_nonwf_lfp x (SUC n)) /\
  (!x n. zoo_mutual_poly_nonwf_lfp x n ==>
         zoo_mutual_poly_nonwf_other_lfp x (SUC n)) /\
  (!x n. zoo_mutual_poly_nonwf_lfp x n ==>
         zoo_mutual_poly_nonwf_lfp x n)
End

(* The rule variable deliberately collides with the joint wf relation's
   preferred name and type.  It must not capture the generated relation. *)
Inductive zoo_mutual_capture_lfp:
  (!(R : (num + num) -> (num + num) -> bool) n.
       R (INL n) (INL n) /\ zoo_mutual_capture_lfp n ==>
       zoo_mutual_capture_lfp n) /\
  zoo_mutual_capture_other_lfp 0
End

(* Static support for the ported Nitpick_Examples acceptance corpus. *)
Inductive zoo_induct_p1:
  zoo_induct_p1 (0 : num) /\
  (!n : num. zoo_induct_p1 n ==>
       zoo_induct_p1 (n + 2))
End

CoInductive zoo_induct_q1:
  zoo_induct_q1 (0 : num) /\
  (!n : num. zoo_induct_q1 n ==>
       zoo_induct_q1 (n + 2))
End

Inductive zoo_induct_p2:
  !n : num. zoo_induct_p2 n ==> zoo_induct_p2 n
End

CoInductive zoo_induct_q2:
  !n : num. zoo_induct_q2 n ==> zoo_induct_q2 n
End

Inductive zoo_induct_p3:
  zoo_induct_p3 0 /\
  (!n. zoo_induct_p3 n ==> zoo_induct_p4 (SUC n)) /\
  (!n. zoo_induct_p4 n ==> zoo_induct_p3 (SUC n))
End

CoInductive zoo_induct_q3:
  zoo_induct_q3 0 /\
  (!n. zoo_induct_q3 n ==> zoo_induct_q4 (SUC n)) /\
  (!n. zoo_induct_q4 n ==> zoo_induct_q3 (SUC n))
End

Definition zoo_special_f1_def:
  zoo_special_f1 (a : num) b c d e = a + b + c + d + e
End

(* HOL4's partial-definition completion is a choice specification, which
   prevents certification even at applications covered by the source
   equations.  These deterministic completions preserve those equations;
   the flat f3 body also avoids higher-order case combinators in the
   dont_specialize runs. *)
Definition zoo_special_f2_def:
  zoo_special_f2 (a : num) (b : num) (c : num) (d : num) (e : num) =
    if e = 0 then a else a + b + c + d + PRE e
End

Definition zoo_special_f3_def:
  zoo_special_f3 (a : num) (b : num) (c : num) (d : num) (e : num) =
    if c <> 0 then a
    else if a = 0 then
      if e = 0 then b + d else a
    else if e = 0 then a
    else PRE a + b + d + PRE e
End

Definition zoo_special_f4_def:
  zoo_special_f4 (y : num) z = if y = z then (1 : num) else 0
End

val zoo_special_f5_def = TotalDefn.Define `
  zoo_special_f5 (f : num -> num) (SUC a) = f a
`;

val zoo_pattern_f1_def = TotalDefn.Define `
  zoo_pattern_f1 x () = x
`;

val zoo_pattern_f2_def = TotalDefn.Define `
  (zoo_pattern_f2 x y T = x) /\
  (zoo_pattern_f2 x y F = y)
`;

val zoo_pattern_f3_def = TotalDefn.Define `
  zoo_pattern_f3 (x, y) = y
`;

val zoo_pattern_f4_def = TotalDefn.Define `
  (zoo_pattern_f4 x 0 = x) /\
  (zoo_pattern_f4 x (SUC n) = n)
`;

val zoo_pattern_f5_def = TotalDefn.Define `
  (zoo_pattern_f5 x NONE = x) /\
  (zoo_pattern_f5 x (SOME y) = y)
`;

val zoo_pattern_f6_def = TotalDefn.Define `
  (zoo_pattern_f6 x [] = x) /\
  (zoo_pattern_f6 x (y :: ys) = y)
`;

val zoo_pattern_f7_def = TotalDefn.Define `
  (zoo_pattern_f7 x (y :: SOME (a, b) :: zs) = b) /\
  (zoo_pattern_f7 x (y :: NONE :: zs) = x) /\
  (zoo_pattern_f7 x [y] = x) /\
  (zoo_pattern_f7 x [] = x)
`;
