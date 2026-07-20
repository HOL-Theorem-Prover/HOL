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
