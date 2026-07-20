Theory refuteTableZoo
Ancestors
  refute ltree itreeTau
Libs
  TotalDefn Refute_Core

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
