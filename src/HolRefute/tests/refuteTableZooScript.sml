Theory refuteTableZoo
Ancestors
  refute ltree itreeTau fixedPoint
Libs
  TotalDefn Refute_ModelFinder_Names Refute_Core quotient Omega

Datatype:
  zoo_tree = ZooLeaf num | ZooNode zoo_tree zoo_tree
End

(* An ordinary, genuinely acyclic datatype for [register_codatatype]'s
   shape-validation control: [combin$I]'s declared result type is the
   bare type variable ['a], which unifies with any [result_ty] under
   [Type.match_type], so substituting it for [ZooSucc] in the
   constructor list has the same arity and the same instantiated result
   type ([zoo_nat0 -> zoo_nat0]) as the constructor it replaces and would
   pass every other clause of [validate_codatatype_shape]. *)
Datatype:
  zoo_nat0 = ZooZero | ZooSucc zoo_nat0
End

(* Witness for the cross-type control: [combin$I] instantiated at
   [zoo_nat0 -> zoo_nat0] is trivially cyclic ([x = I x] for any [x]),
   so if the instance-typed impostor were ever accepted as a [zoo_nat0]
   constructor, this witness would certify it. *)
Theorem zoo_nat0_instance_impostor_witness:
  ?x : zoo_nat0. x = (combin$I : zoo_nat0 -> zoo_nat0) x
Proof
  qexists_tac `ZooZero` >> simp [combinTheory.I_THM]
QED

(* A database impostor: [zoo_id] is a genuine constant declared at
   [zoo_nat0 -> zoo_nat0] - unlike [combin$I], its declared result type
   is already [zoo_nat0]-headed - but it is not one of [zoo_nat0]'s
   database constructors, and its witness is just as trivially cyclic. *)
Definition zoo_id_def:
  zoo_id (x : zoo_nat0) = x
End

Theorem zoo_id_witness:
  ?x : zoo_nat0. x = zoo_id x
Proof
  qexists_tac `ZooZero` >> simp [zoo_id_def]
QED

(* Stable replay fixtures.  Their equations deliberately expose constructor
   behavior only after a kernel case split or induction; a symbolic
   scrutinee does not collapse by ordinary evaluation. *)
Definition replay_list_case_def[simp]:
  (replay_list_case ([] : num list) = T) /\
  (replay_list_case (h :: t) = T)
End

Definition replay_tree_case_def[simp]:
  (replay_tree_case (ZooLeaf n) = T) /\
  (replay_tree_case (ZooNode left right) = T)
End

Definition replay_list_true_def[simp]:
  (replay_list_true ([] : num list) = T) /\
  (replay_list_true (h :: t) = replay_list_true t)
End

Definition replay_tree_true_def[simp]:
  (replay_tree_true (ZooLeaf n) = T) /\
  (replay_tree_true (ZooNode left right) =
     (replay_tree_true left /\ replay_tree_true right))
End

Definition replay_list_tail_def[simp]:
  (replay_list_tail p ([] : num list) = T) /\
  (replay_list_tail p (h :: t) = p t)
End

Definition replay_list_bad_def[simp]:
  (replay_list_bad ([] : num list) = T) /\
  (replay_list_bad (h :: t) = F)
End

(* Executable source-side copies used to certify that the model finder's
   native relation inv/O ersatz operations preserve HOL4 argument order. *)
Definition zoo_relation_inv_def:
  zoo_relation_inv r y x = r x y
End

Definition zoo_bool_relcomp_def:
  zoo_bool_relcomp r s x z =
    ((s x F /\ r F z) \/ (s x T /\ r T z))
End

Datatype:
  zoo_record = <| zoo_num : num; zoo_bit : bool |>
End

Definition replay_record_case_def[simp]:
  replay_record_case (zoo_record n bit) = T
End

Datatype:
  zoo_poly_record = <| zoo_poly : 'a; zoo_poly_bit : bool |>
End

Datatype:
  zoo_poly_tail_record =
    <| zoo_tail_bit : bool; zoo_tail_poly : 'a |>
End

Datatype:
  zoo_integer_tree =
      ZooIntegerNull
    | ZooIntegerNode num zoo_integer_tree zoo_integer_tree
End

Definition zoo_integer_labels_def:
  (zoo_integer_labels ZooIntegerNull = {}) /\
  (zoo_integer_labels (ZooIntegerNode x left right) =
     {x} UNION zoo_integer_labels left UNION zoo_integer_labels right)
End

Datatype:
  zoo_nibble =
      ZooNibble0 | ZooNibble1 | ZooNibble2 | ZooNibble3
    | ZooNibble4 | ZooNibble5 | ZooNibble6 | ZooNibble7
    | ZooNibble8 | ZooNibble9 | ZooNibbleA | ZooNibbleB
    | ZooNibbleC | ZooNibbleD | ZooNibbleE | ZooNibbleF
End

Definition zoo_nibble_rot_def:
  zoo_nibble_rot n =
    case n of
        ZooNibble0 => ZooNibble1
      | ZooNibble1 => ZooNibble2
      | ZooNibble2 => ZooNibble3
      | ZooNibble3 => ZooNibble4
      | ZooNibble4 => ZooNibble5
      | ZooNibble5 => ZooNibble6
      | ZooNibble6 => ZooNibble7
      | ZooNibble7 => ZooNibble8
      | ZooNibble8 => ZooNibble9
      | ZooNibble9 => ZooNibbleA
      | ZooNibbleA => ZooNibbleB
      | ZooNibbleB => ZooNibbleC
      | ZooNibbleC => ZooNibbleD
      | ZooNibbleD => ZooNibbleE
      | ZooNibbleE => ZooNibbleF
      | ZooNibbleF => ZooNibble0
End

Datatype:
  zoo_pd = ZooPd ('a # 'b)
End

Definition zoo_pd_fs_def:
  zoo_pd_fs (ZooPd (a, b)) = a
End

Definition zoo_pd_sn_def:
  zoo_pd_sn (ZooPd (a, b)) = b
End

Datatype:
  zoo_fn = ZooFn ('a -> 'b)
End

Definition zoo_fn_app_def:
  zoo_fn_app (ZooFn f) x = f x
End

Datatype:
  zoo_point2d = <| zoo_xc2 : int; zoo_yc2 : int |>
End

Datatype:
  zoo_point3d =
    <| zoo_xc3 : int; zoo_yc3 : int; zoo_zc3 : int |>
End

Datatype:
  zoo_point4d =
    <| zoo_xc4 : int; zoo_yc4 : int; zoo_zc4 : int;
       zoo_wc4 : int |>
End

Theorem zoo_point2d_fn_updates_compute[compute] =
  DB.fetch "-" "zoo_point2d_fn_updates"

Theorem zoo_point3d_fn_updates_compute[compute] =
  DB.fetch "-" "zoo_point3d_fn_updates"

Theorem zoo_point4d_fn_updates_compute[compute] =
  DB.fetch "-" "zoo_point4d_fn_updates"

Theorem zoo_record_int_eq_compute[compute] =
  integerTheory.INT_EQ_REDUCE

Theorem zoo_nat_div_zero_compute[compute] =
  arithmeticTheory.DIV_0

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

(* Registers [zoo_bool_quot] in the "quotient" ThmSetData set, so
   Refute_Gen's structural [is_quotient_type] fallback (a TypeBase-info
   type with a registered QUOTIENT theorem) has a genuine, ground,
   TypeBase-less target to fire on -- unlike rat/real, whose own
   registered generators shadow that check first. *)
Theorem zoo_bool_quot_quotient_reg[quotient] = zoo_bool_quot_def

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

(* A bound above [binary_int_threshold], so that the smart binarize choice
   would fire on this typedef were it not vetoed. *)
Theorem zoo_four_exists[local]:
  ?n : num. (\n. n < 4) n
Proof
  qexists_tac `0` >> simp []
QED

val zoo_four_tydef =
  new_type_definition ("zoo_four", zoo_four_exists);

val zoo_four_absrep = define_new_type_bijections
  {name = "zoo_four_absrep", ABS = "zoo_four_abs",
   REP = "zoo_four_rep", tyax = zoo_four_tydef};

(* A kernel typedef with abs/rep constants but no bijection theorem of any
   kind - whole or split - anywhere in this theory: neither form is
   harvestable.  A selftest can add a fresh bijection theorem temporarily,
   against the same [_TY_DEF] witness, to exercise negative-cache
   freshness. *)
Theorem zoo_unharvested_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val zoo_unharvested_tydef =
  new_type_definition ("zoo_unharvested", zoo_unharvested_exists);

val zoo_unharvested_absrep = define_new_type_bijections
  {name = "zoo_unharvested_absrep", ABS = "zoo_unharvested_abs",
   REP = "zoo_unharvested_rep", tyax = zoo_unharvested_tydef};

val _ = Theory.delete_binding "zoo_unharvested_absrep";

Definition zoo_unharvested_wrapper_def:
  zoo_unharvested_wrapper b n =
    if b then zoo_unharvested_abs n else zoo_unharvested_abs n
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

Theorem zoo_one_or_two_exists[local]:
  ?x : 'a. (\x. x = ARB F \/ x = ARB T) x
Proof
  qexists_tac `ARB F` >> simp []
QED

val zoo_one_or_two_tydef =
  new_type_definition ("zoo_one_or_two", zoo_one_or_two_exists);

val zoo_one_or_two_absrep = define_new_type_bijections
  {name = "zoo_one_or_two_absrep", ABS = "zoo_one_or_two_abs",
   REP = "zoo_one_or_two_rep", tyax = zoo_one_or_two_tydef};

(* On the selected finite instances, the source subset
   {n | n < CARD UNIV(:'a)} is isomorphic to 'a.  This representation
   preserves exactly the equality/cardinality behavior under test without
   exposing a cardinality-dependent membership axiom to native tyvar
   scopes. *)
Theorem zoo_bounded_exists[local]:
  ?x : 'a. (\x. T) x
Proof
  qexists_tac `ARB` >> simp []
QED

val zoo_bounded_tydef =
  new_type_definition ("zoo_bounded", zoo_bounded_exists);

val zoo_bounded_absrep = define_new_type_bijections
  {name = "zoo_bounded_absrep", ABS = "zoo_bounded_abs",
   REP = "zoo_bounded_rep", tyax = zoo_bounded_tydef};

Theorem zoo_check_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val zoo_check_tydef =
  new_type_definition ("zoo_check", zoo_check_exists);

val zoo_check_absrep = define_new_type_bijections
  {name = "zoo_check_absrep", ABS = "zoo_check_abs",
   REP = "zoo_check_rep", tyax = zoo_check_tydef};

(* A hand-rolled codatatype for [register_codatatype]'s witness path: a
   typedef over the always-true predicate on [:num -> 'a] gives an infinite
   stream, with [zoo_scons] its sole constructor and [zoo_stream_CASE] a
   scrutinee-first case constant.  [zoo_tree] above cannot stand in for this:
   it is a genuine (acyclic) TypeBase datatype. *)
Theorem zoo_stream_exists[local]:
  ?f : num -> 'a. (\f. T) f
Proof
  qexists_tac `\n. ARB` >> simp []
QED

val zoo_stream_tydef =
  new_type_definition ("zoo_stream", zoo_stream_exists);

val zoo_stream_absrep = define_new_type_bijections
  {name = "zoo_stream_absrep", ABS = "zoo_stream_abs",
   REP = "zoo_stream_rep", tyax = zoo_stream_tydef};

Theorem zoo_stream_repabs[local]:
  !r. zoo_stream_rep (zoo_stream_abs r) = r
Proof
  simp [GSYM zoo_stream_absrep]
QED

Theorem zoo_stream_rep_11[local]:
  !x y. (zoo_stream_rep x = zoo_stream_rep y) <=> (x = y)
Proof
  metis_tac [CONJUNCT1 zoo_stream_absrep]
QED

Definition zoo_scons_def:
  zoo_scons (a : 'a) (s : 'a zoo_stream) : 'a zoo_stream =
    zoo_stream_abs (\n. if n = 0 then a else zoo_stream_rep s (n - 1))
End

Definition zoo_shd_def:
  zoo_shd (s : 'a zoo_stream) : 'a = zoo_stream_rep s 0
End

Definition zoo_stl_def:
  zoo_stl (s : 'a zoo_stream) : 'a zoo_stream =
    zoo_stream_abs (\n. zoo_stream_rep s (n + 1))
End

Definition zoo_stream_CASE_def:
  zoo_stream_CASE (s : 'a zoo_stream)
                  (f : 'a -> 'a zoo_stream -> 'b) : 'b =
    f (zoo_shd s) (zoo_stl s)
End

(* The stream eta law: every stream is its own head/tail reassembly. *)
Theorem zoo_stream_eta:
  !s. s = zoo_scons (zoo_shd s) (zoo_stl s)
Proof
  simp [GSYM zoo_stream_rep_11, zoo_scons_def, zoo_shd_def,
        zoo_stl_def, zoo_stream_repabs, FUN_EQ_THM] >>
  rw []
QED

(* The registration witness: the constant stream of [a] is cyclic under
   [zoo_scons], which is exactly what justifies dropping acyclicity. *)
Theorem zoo_stream_witness:
  ?s. s = zoo_scons a s
Proof
  qexists_tac `zoo_stream_abs (\n. a)` >>
  simp [GSYM zoo_stream_rep_11, zoo_scons_def, zoo_stream_repabs]
QED

(* Positive control for the constructor-spine walk (clause 3 of
   [validate_codatatype_witness]): [s] is nested two [zoo_scons]
   applications deep, not a top-level argument of the outer one, so a
   check confined to the outer application's own arguments rejects this
   genuine depth-2 cyclic witness.  The walk accepts it because
   [zoo_scons]'s own argument is again a [zoo_scons] application. *)
Theorem zoo_stream_nested_witness:
  ?s. s = zoo_scons a (zoo_scons a s)
Proof
  qexists_tac `zoo_stream_abs (\n. a)` >>
  simp [GSYM zoo_stream_rep_11, zoo_scons_def, zoo_stream_repabs]
QED

(* Negative control for [register_codatatype]'s witness check: [a] is
   free inside the argument [combin$K a l], but [combin$K] is not a
   registered constructor, so the constructor-spine walk never descends
   into it and [l] itself is never an argument on that spine.  This is
   not a cyclic value - [l = [a]] proves it, an ordinary finite list. *)
Theorem zoo_list_free_occurrence_witness:
  ?l : 'a list. l = CONS (combin$K a l) []
Proof
  qexists_tac `[a]` >> simp [combinTheory.K_THM]
QED

(* Negative control: [combin$I] is a constant, but not one of
   [zoo_stream]'s registered constructors. *)
Theorem zoo_stream_non_constructor_witness:
  ?s : num zoo_stream. s = combin$I s
Proof
  qexists_tac `ARB` >> simp [combinTheory.I_THM]
QED

(* Positive control: the instance-typed witness the shape check accepts -
   [num zoo_stream], not [zoo_stream]'s generic instance. *)
Theorem zoo_stream_instance_witness:
  ?s : num zoo_stream. s = zoo_scons 0 s
Proof
  qexists_tac `zoo_stream_abs (\n. 0)` >>
  simp [GSYM zoo_stream_rep_11, zoo_scons_def, zoo_stream_repabs]
QED

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

(* A computational view for the QC-vs-MF differential corpus.  Hol_reln
   constants are not executable merely from their cases theorem; this
   proved equation lets QC evaluate the inductive predicate without
   changing the predicate seen by MF. *)
Theorem zoo_wf_lfp_compute:
  !n. zoo_wf_lfp n <=> T
Proof
  Induct >> metis_tac [zoo_wf_lfp_rules]
QED

Inductive zoo_nonwf_lfp:
  !n : num. zoo_nonwf_lfp n ==> zoo_nonwf_lfp n
End

(* Smart-generator mode-inference zoo.  These deliberately cover a linear
   relation, a mutual SCC, an unconstrained conclusion variable, and a
   higher-order relation parameter. *)
Inductive zoo_sg_linear:
  zoo_sg_linear 0 /\
  (!n. zoo_sg_linear n ==> zoo_sg_linear (SUC n))
End

Theorem zoo_sg_linear_compute:
  !n. zoo_sg_linear n <=> T
Proof
  Induct >> metis_tac [zoo_sg_linear_rules]
QED

Inductive zoo_sg_duplicate:
  (!n : num. zoo_sg_duplicate n (n,n))
End

Theorem zoo_sg_duplicate_compute:
  !n p. zoo_sg_duplicate n p <=> (p = (n,n))
Proof
  metis_tac [zoo_sg_duplicate_cases, zoo_sg_duplicate_rules]
QED

(* Same duplicate-pattern clause as [zoo_sg_duplicate], but over a type
   with a total generator ([:bool] is fully enumerated by
   [Refute_Gen.enumerate]), so a [:num] free variable's unboundedness is
   not a confound when probing the negative complement's exhaustive
   coverage -- see [negation_complement_expectnone_goal] in
   selftest.sml. *)
Inductive zoo_sg_bool_duplicate:
  (!x : bool. zoo_sg_bool_duplicate x (x,x))
End

Theorem zoo_sg_bool_duplicate_compute:
  !x p. zoo_sg_bool_duplicate x p <=> (p = (x,x))
Proof
  metis_tac [zoo_sg_bool_duplicate_cases, zoo_sg_bool_duplicate_rules]
QED

(* Same duplicate-pattern clause again, but its Sidecond, [HD [] = x],
   can never be evaluated ([HD] is partial and its argument is always
   [[]]): the complement's runtime guard is always stuck, never true or
   false.  See [negation_complement_stuck_goal] in selftest.sml. *)
Inductive zoo_sg_bool_stuck:
  (!x : bool. HD ([] : bool list) = x ==> zoo_sg_bool_stuck x (x,x))
End

(* Stream-order pins for substrate-neutral enumerator synthesis.  The first
   relation has genuinely duplicate derivations; the second exposes multiple
   outputs in source order. *)
Inductive zoo_sg_derivations:
  zoo_sg_derivations (0 : num) /\
  zoo_sg_derivations (0 : num) /\
  zoo_sg_derivations (1 : num)
End

Theorem zoo_sg_derivations_compute:
  !n. zoo_sg_derivations n <=> (n = 0) \/ (n = 1)
Proof
  metis_tac [zoo_sg_derivations_cases, zoo_sg_derivations_rules]
QED

Inductive zoo_sg_multi_output:
  zoo_sg_multi_output (0 : num) F /\
  zoo_sg_multi_output (0 : num) T /\
  zoo_sg_multi_output (1 : num) F
End

Theorem zoo_sg_multi_output_compute:
  !n b. zoo_sg_multi_output n b <=>
    (n = 0 /\ (b = F \/ b = T)) \/ (n = 1 /\ b = F)
Proof
  metis_tac [zoo_sg_multi_output_cases, zoo_sg_multi_output_rules]
QED

Inductive zoo_sg_mutual:
  zoo_sg_even 0 /\
  (!n. zoo_sg_linear n /\ zoo_sg_odd n /\
       zoo_sg_linear (SUC n) ==> zoo_sg_even (SUC n)) /\
  (!n. zoo_sg_even n ==> zoo_sg_odd (SUC n))
End

Inductive zoo_sg_fresh:
  !x : num. !y : num. x = 0 ==> zoo_sg_fresh x y
End

(* Its all-input mode still needs a clause-local generator.  This makes its
   goal score tie the ordinary Guard score and pins SmartGen's tie-break. *)
Inductive zoo_sg_tied:
  !x : num. !y : num. y = y ==> zoo_sg_tied x
End

Inductive zoo_sg_native_mutual:
  zoo_sg_native_left 0 /\
  (!n. zoo_sg_native_right n ==> zoo_sg_native_left (SUC n)) /\
  (!n. zoo_sg_native_left n ==> zoo_sg_native_right (SUC n))
End

Inductive zoo_sg_higher_order:
  !P x. P x ==> zoo_sg_higher_order P x
End

(* Recursive higher-order relation: the second clause's premise
   [zoo_sg_listall P xs] is a [Prem] carrying the predicate argument, so
   it reaches [derive_atomic]'s [Fun] branch via [derive_call] -- unlike
   [zoo_sg_higher_order]'s variable-headed premise, which is a
   [Sidecond]. *)
Inductive zoo_sg_listall:
  (!P. zoo_sg_listall P []) /\
  (!P x xs. P x /\ zoo_sg_listall P xs ==>
            zoo_sg_listall P (x::xs))
End

(* Unlike [zoo_sg_linear_compute], this is never added to a compset:
   [compute_qc_gate] does flag [zoo_sg_listall] as non-executable, and
   the full-pipeline pin passes anyway because [strategy_run_body]'s
   [can_preflight] holds for the specialised plan and its
   [compile_smart_selected] call does not fail, not because of
   anything registered here.  This theorem's actual role is as the
   source, via [ISPEC], of the provably-true [EVERY]-form twin used by
   the specialisation pin. *)
Theorem zoo_sg_listall_compute:
  !P xs. zoo_sg_listall P xs <=> EVERY P xs
Proof
  Induct_on `xs` >> rw [Once zoo_sg_listall_cases]
QED

(* A mixed group: [zoo_sg_mix_fo] is first-order, [zoo_sg_mix_ho] takes a
   non-predicate function parameter and so gets no modes at all.  Joint
   inference must degrade [zoo_sg_mix_ho] alone, not the whole group. *)
Inductive zoo_sg_mix:
  zoo_sg_mix_fo (0 : num) /\
  (!n. zoo_sg_mix_fo n ==> zoo_sg_mix_fo (SUC n)) /\
  (!f n. zoo_sg_mix_fo n /\ (f n = n) ==> zoo_sg_mix_ho (f : num -> num) n)
End

(* Replaces a selftest-local [TotalDefn.Define]: a fixture with fixture
   provenance, driven through the same [Hol_reln]/SCC route as the
   others. *)
Inductive zoo_sg_fun_param:
  !f x. (f x = x) ==> zoo_sg_fun_param (f : num -> num) x
End

(* [argument_modes] handles products before function types, so this
   argument's mode really is [Pair (Fun (Input, Bool), _)] -- a predicate
   nested in a pair.  The head argument [fp] must be a bare variable, not
   a literal pair: a literal pair is destructured by [split_argument]'s
   own [dest_pair] before [split_atomic] ever sees the composite mode. *)
Inductive zoo_sg_pair_pred:
  !fp : (num -> bool) # num. FST fp (SND fp) ==> zoo_sg_pair_pred fp
End

Inductive zoo_sg_string:
  zoo_sg_string [] /\
  (!c s. zoo_sg_string s ==> zoo_sg_string (c::s))
End

Theorem zoo_sg_string_compute:
  !s : char list. zoo_sg_string s <=> T
Proof
  Induct >> metis_tac [zoo_sg_string_rules]
QED

Inductive zoo_sg_string_mixed:
  zoo_sg_string_mixed [] [] /\
  (!c left right. zoo_sg_string_mixed left right ==>
     zoo_sg_string_mixed (c::left) (c::right))
End

(* word8 sits exactly at the finite-enumeration cap.  Its recursive rule
   distinguishes complete finite CpsGenerate semantics from size-bounding. *)
Inductive zoo_sg_word8_list:
  zoo_sg_word8_list ([] : word8 list) /\
  (!w ws. zoo_sg_word8_list ws ==>
     zoo_sg_word8_list (w::ws))
End

(* Source names here deliberately collide with fixed emitter helpers after
   ordinary SML sanitization. *)
Inductive zoo_sg_hygiene:
  !size complete smart_in_0 : num.
    size = complete ==> zoo_sg_hygiene size complete smart_in_0
End

(* The clauses have the same partitioned intro shape modulo alpha-renaming,
   but their source premise interleavings differ. *)
Inductive zoo_sg_ordered:
  (!x y. x = x /\ zoo_sg_ordered x y /\ y = y ==>
         zoo_sg_ordered x y) /\
  (!a b. a = a /\ b = b /\ zoo_sg_ordered a b ==>
         zoo_sg_ordered a b)
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

(* Static support for the Core/Refute/Manual/Hotel acceptance groups. *)

Datatype:
  zoo_ref_t3 = ZooRefE ('a -> 'b)
End

Definition zoo_ref_rec_t3_def:
  zoo_ref_rec_t3 e (ZooRefE f) = e f
End

Datatype:
  zoo_ref_bintree =
      ZooRefLeaf 'a
    | ZooRefNode zoo_ref_bintree zoo_ref_bintree
End

val zoo_ref_rec_bintree_def = TotalDefn.Define `
  (zoo_ref_rec_bintree l n (ZooRefLeaf x) = l x) /\
  (zoo_ref_rec_bintree l n (ZooRefNode x y) =
     n x y (zoo_ref_rec_bintree l n x)
       (zoo_ref_rec_bintree l n y))
`;

Datatype:
  zoo_ref_aexp =
      ZooRefNumber 'a
    | ZooRefITE zoo_ref_bexp zoo_ref_aexp zoo_ref_aexp ;
  zoo_ref_bexp = ZooRefEqual zoo_ref_aexp zoo_ref_aexp
End

val zoo_ref_rec_exp_def = TotalDefn.Define `
  (zoo_ref_rec_aexp number ite equal (ZooRefNumber x) = number x) /\
  (zoo_ref_rec_aexp number ite equal (ZooRefITE x y z) =
     ite x y z (zoo_ref_rec_bexp number ite equal x)
       (zoo_ref_rec_aexp number ite equal y)
       (zoo_ref_rec_aexp number ite equal z)) /\
  (zoo_ref_rec_bexp number ite equal (ZooRefEqual x y) =
     equal x y (zoo_ref_rec_aexp number ite equal x)
       (zoo_ref_rec_aexp number ite equal y))
`;

Datatype:
  zoo_ref_x = ZooRefXA | ZooRefXB zoo_ref_x | ZooRefXC zoo_ref_y ;
  zoo_ref_y = ZooRefYD zoo_ref_x | ZooRefYE zoo_ref_y | ZooRefYF
End

val zoo_ref_rec_xy_def = TotalDefn.Define `
  (zoo_ref_rec_x a b c d e f ZooRefXA = a) /\
  (zoo_ref_rec_x a b c d e f (ZooRefXB x) =
     b x (zoo_ref_rec_x a b c d e f x)) /\
  (zoo_ref_rec_x a b c d e f (ZooRefXC y) =
     c y (zoo_ref_rec_y a b c d e f y)) /\
  (zoo_ref_rec_y a b c d e f (ZooRefYD x) =
     d x (zoo_ref_rec_x a b c d e f x)) /\
  (zoo_ref_rec_y a b c d e f (ZooRefYE y) =
     e y (zoo_ref_rec_y a b c d e f y)) /\
  (zoo_ref_rec_y a b c d e f ZooRefYF = f)
`;

(* HOL4's datatype package cannot form recursive occurrences below the
   function type constructor.  These fixtures preserve the embedding shape
   at the constructor boundary while using Boolean function codomains. *)
Datatype:
  zoo_ref_xopt = ZooRefCX (zoo_ref_xopt option) | ZooRefDX bool
End

Datatype:
  zoo_ref_yopt = ZooRefCY (('a -> bool) option)
End

Datatype:
  zoo_ref_trie = ZooRefTR (zoo_ref_trie list)
End

Datatype:
  zoo_ref_inftree = ZooRefInfLeaf | ZooRefInfNode (num -> bool)
End

Datatype:
  zoo_ref_lambda =
      ZooRefVar 'a
    | ZooRefApp zoo_ref_lambda zoo_ref_lambda
    | ZooRefLam ('a -> bool)
End

Datatype:
  zoo_ref_t = ZooRefTC ('a -> bool) | ZooRefTD ('b list)
End

Datatype:
  zoo_ref_u = ZooRefUE ('a -> bool)
End

Datatype:
  zoo_ref_point = <| zoo_ref_xpos : 'a; zoo_ref_ypos : 'b |>
End

Datatype:
  zoo_ref_extpoint =
    <| zoo_ref_ext_xpos : 'a; zoo_ref_ext_ypos : 'b;
       zoo_ref_extension : 'c |>
End

Inductive zoo_ref_undefined_set:
  !(x : 'a). x = ARB ==> zoo_ref_undefined_set x
End

Inductive zoo_ref_even_card:
  zoo_ref_even_card ({} : 'a set) /\
  (!S x y. zoo_ref_even_card S /\ x NOTIN S /\ y NOTIN S /\ x <> y ==>
     zoo_ref_even_card (S UNION {x; y}))
End

Inductive zoo_ref_even:
  zoo_ref_even 0 /\
  (!n. zoo_ref_even n ==> zoo_ref_odd (SUC n)) /\
  (!n. zoo_ref_odd n ==> zoo_ref_even (SUC n))
End

Inductive zoo_ref_a_even:
  (!(f : 'a -> 'a) x. x = ARB ==> zoo_ref_a_even f x) /\
  (!f x. zoo_ref_a_even f x ==> zoo_ref_a_odd f (f x)) /\
  (!f x. zoo_ref_a_odd f x ==> zoo_ref_a_even f (f x))
End

Definition zoo_manual_my_int_rel_def:
  zoo_manual_my_int_rel (x : num # num) y <=>
    FST x + SND y = FST y + SND x
End

Theorem zoo_manual_my_int_equiv:
  !x y. zoo_manual_my_int_rel x y =
        (zoo_manual_my_int_rel x = zoo_manual_my_int_rel y)
Proof
  Cases >> Cases >>
  simp [zoo_manual_my_int_rel_def, FUN_EQ_THM,
        pairTheory.FORALL_PROD] >>
  Omega.OMEGA_TAC
QED

val zoo_manual_my_int_quot_def =
  define_quotient_type "zoo_manual_my_int" "zoo_manual_my_int_abs"
    "zoo_manual_my_int_rep" zoo_manual_my_int_equiv;

Definition zoo_manual_add_def:
  zoo_manual_add x y =
    zoo_manual_my_int_abs
      (FST (zoo_manual_my_int_rep x) + FST (zoo_manual_my_int_rep y),
       SND (zoo_manual_my_int_rep x) + SND (zoo_manual_my_int_rep y))
End

Inductive zoo_manual_even:
  zoo_manual_even 0 /\
  (!n. zoo_manual_even n ==> zoo_manual_even (SUC (SUC n)))
End

Inductive zoo_manual_even_alt:
  zoo_manual_even_alt (0 : num) /\ zoo_manual_even_alt 2 /\
  (!m n. zoo_manual_even_alt m /\ zoo_manual_even_alt n ==>
         zoo_manual_even_alt (m + n))
End

CoInductive zoo_manual_nats:
  !n : num. zoo_manual_nats n ==> zoo_manual_nats n
End

Inductive zoo_manual_odd:
  zoo_manual_odd 1 /\
  (!m n. zoo_manual_odd m /\ zoo_manual_even n ==>
         zoo_manual_odd (m + n))
End

Definition zoo_manual_iterates_def:
  zoo_manual_iterates f a =
    llist$LUNFOLD (\x. SOME (f x, x)) a
End

Datatype:
  zoo_manual_tm =
      ZooManualVar num
    | ZooManualLam zoo_manual_tm
    | ZooManualApp zoo_manual_tm zoo_manual_tm
End

val zoo_manual_lift_def = TotalDefn.Define `
  (zoo_manual_lift (ZooManualVar j) k =
     ZooManualVar (if j < k then j else j + 1)) /\
  (zoo_manual_lift (ZooManualLam t) k =
     ZooManualLam (zoo_manual_lift t (k + 1))) /\
  (zoo_manual_lift (ZooManualApp t u) k =
     ZooManualApp (zoo_manual_lift t k) (zoo_manual_lift u k))
`;

val zoo_manual_loose_def = TotalDefn.Define `
  (zoo_manual_loose (ZooManualVar j) k = (j >= k)) /\
  (zoo_manual_loose (ZooManualLam t) k =
     zoo_manual_loose t (SUC k)) /\
  (zoo_manual_loose (ZooManualApp t u) k =
     (zoo_manual_loose t k \/ zoo_manual_loose u k))
`;

val zoo_manual_subst1_def = TotalDefn.Define `
  (zoo_manual_subst1 sigma (ZooManualVar j) = sigma j) /\
  (zoo_manual_subst1 sigma (ZooManualLam t) =
     ZooManualLam
       (zoo_manual_subst1
         (\n. case n of
                  0 => ZooManualVar 0
                | SUC m => zoo_manual_lift (sigma m) 1) t)) /\
  (zoo_manual_subst1 sigma (ZooManualApp t u) =
     ZooManualApp (zoo_manual_subst1 sigma t)
       (zoo_manual_subst1 sigma u))
`;

val zoo_manual_subst2_def = TotalDefn.Define `
  (zoo_manual_subst2 sigma (ZooManualVar j) = sigma j) /\
  (zoo_manual_subst2 sigma (ZooManualLam t) =
     ZooManualLam
       (zoo_manual_subst2
         (\n. case n of
                  0 => ZooManualVar 0
                | SUC m => zoo_manual_lift (sigma m) 0) t)) /\
  (zoo_manual_subst2 sigma (ZooManualApp t u) =
     ZooManualApp (zoo_manual_subst2 sigma t)
       (zoo_manual_subst2 sigma u))
`;

Datatype:
  zoo_manual_aa_tree =
      ZooManualAALeaf
    | ZooManualAAN num num zoo_manual_aa_tree zoo_manual_aa_tree
End

val zoo_manual_data_def = TotalDefn.Define `
  (zoo_manual_data ZooManualAALeaf = ARB) /\
  (zoo_manual_data (ZooManualAAN x k t u) = x)
`;

val zoo_manual_dataset_def = TotalDefn.Define `
  (zoo_manual_dataset ZooManualAALeaf = {}) /\
  (zoo_manual_dataset (ZooManualAAN x k t u) =
     {x} UNION zoo_manual_dataset t UNION zoo_manual_dataset u)
`;

val zoo_manual_level_def = TotalDefn.Define `
  (zoo_manual_level ZooManualAALeaf = 0) /\
  (zoo_manual_level (ZooManualAAN x k t u) = k)
`;

val zoo_manual_left_def = TotalDefn.Define `
  (zoo_manual_left ZooManualAALeaf = ZooManualAALeaf) /\
  (zoo_manual_left (ZooManualAAN x k t u) = t)
`;

val zoo_manual_right_def = TotalDefn.Define `
  (zoo_manual_right ZooManualAALeaf = ZooManualAALeaf) /\
  (zoo_manual_right (ZooManualAAN x k t u) = u)
`;

val zoo_manual_wf_def = TotalDefn.Define `
  (zoo_manual_wf ZooManualAALeaf = T) /\
  (zoo_manual_wf (ZooManualAAN x k t u) =
     if t = ZooManualAALeaf then
       k = 1 /\
       (u = ZooManualAALeaf \/
        (zoo_manual_level u = 1 /\
         zoo_manual_left u = ZooManualAALeaf /\
         zoo_manual_right u = ZooManualAALeaf))
     else
       zoo_manual_wf t /\ zoo_manual_wf u /\
       u <> ZooManualAALeaf /\ zoo_manual_level t < k /\
       zoo_manual_level u <= k /\ zoo_manual_level (zoo_manual_right u) < k)
`;

val zoo_manual_skew_def = TotalDefn.Define `
  (zoo_manual_skew ZooManualAALeaf = ZooManualAALeaf) /\
  (zoo_manual_skew (ZooManualAAN x k t u) =
     if t <> ZooManualAALeaf /\ k = zoo_manual_level t then
       ZooManualAAN (zoo_manual_data t) k (zoo_manual_left t)
         (ZooManualAAN x k (zoo_manual_right t) u)
     else ZooManualAAN x k t u)
`;

val zoo_manual_split_def = TotalDefn.Define `
  (zoo_manual_split ZooManualAALeaf = ZooManualAALeaf) /\
  (zoo_manual_split (ZooManualAAN x k t u) =
     if u <> ZooManualAALeaf /\
        k = zoo_manual_level (zoo_manual_right u) then
       ZooManualAAN (zoo_manual_data u) (SUC k)
         (ZooManualAAN x k t (zoo_manual_left u)) (zoo_manual_right u)
     else ZooManualAAN x k t u)
`;

val zoo_manual_insort1_def = TotalDefn.Define `
  (zoo_manual_insort1 ZooManualAALeaf x =
     ZooManualAAN x 1 ZooManualAALeaf ZooManualAALeaf) /\
  (zoo_manual_insort1 (ZooManualAAN y k t u) x =
     ZooManualAAN y k
       (if x < y then zoo_manual_insort1 t x else t)
       (if x > y then zoo_manual_insort1 u x else u))
`;

val zoo_manual_insort2_def = TotalDefn.Define `
  (zoo_manual_insort2 ZooManualAALeaf x =
     ZooManualAAN x 1 ZooManualAALeaf ZooManualAALeaf) /\
  (zoo_manual_insort2 (ZooManualAAN y k t u) x =
     zoo_manual_split (zoo_manual_skew
       (ZooManualAAN y k
         (if x < y then zoo_manual_insort2 t x else t)
         (if x > y then zoo_manual_insort2 u x else u))))
`;

val _ = new_type ("zoo_hotel_guest", 0);
val _ = new_type ("zoo_hotel_key", 0);
val _ = new_type ("zoo_hotel_room", 0);

Datatype:
  zoo_hotel_state =
    <| zoo_hotel_owns : zoo_hotel_room -> zoo_hotel_guest option;
       zoo_hotel_currk : zoo_hotel_room -> zoo_hotel_key;
       zoo_hotel_issued : zoo_hotel_key set;
       zoo_hotel_cards : zoo_hotel_guest ->
         (zoo_hotel_key # zoo_hotel_key) set;
       zoo_hotel_roomk : zoo_hotel_room -> zoo_hotel_key;
       zoo_hotel_isin : zoo_hotel_room -> zoo_hotel_guest set;
       zoo_hotel_safe : zoo_hotel_room -> bool |>
End

Inductive zoo_hotel_reach:
  (!initk. ONE_ONE initk ==>
     zoo_hotel_reach
       <| zoo_hotel_owns := K NONE;
          zoo_hotel_currk := initk;
          zoo_hotel_issued := IMAGE initk UNIV;
          zoo_hotel_cards := K {};
          zoo_hotel_roomk := initk;
          zoo_hotel_isin := K {};
          zoo_hotel_safe := K T |>) /\
  (!s k r g. zoo_hotel_reach s /\ k NOTIN zoo_hotel_issued s ==>
     zoo_hotel_reach
       (s with
        <| zoo_hotel_currk := (r =+ k) (zoo_hotel_currk s);
           zoo_hotel_issued := zoo_hotel_issued s UNION {k};
           zoo_hotel_cards :=
             (g =+ (zoo_hotel_cards s g UNION
                    {(zoo_hotel_currk s r, k)})) (zoo_hotel_cards s);
           zoo_hotel_owns := (r =+ SOME g) (zoo_hotel_owns s);
           zoo_hotel_safe := (r =+ F) (zoo_hotel_safe s) |>)) /\
  (!s k k' g r.
     zoo_hotel_reach s /\ (k, k') IN zoo_hotel_cards s g /\
     zoo_hotel_roomk s r IN {k; k'} ==>
     zoo_hotel_reach
       (s with
        <| zoo_hotel_isin :=
             (r =+ (zoo_hotel_isin s r UNION {g})) (zoo_hotel_isin s);
           zoo_hotel_roomk := (r =+ k') (zoo_hotel_roomk s);
           zoo_hotel_safe :=
             (r =+ ((zoo_hotel_owns s r = SOME g /\
                      zoo_hotel_isin s r = {}) \/ zoo_hotel_safe s r))
               (zoo_hotel_safe s) |>)) /\
  (!s g r. zoo_hotel_reach s /\ g IN zoo_hotel_isin s r ==>
     zoo_hotel_reach
       (s with zoo_hotel_isin :=
          (r =+ (zoo_hotel_isin s r DELETE g)) (zoo_hotel_isin s)))
End

(* A one-step projection of the planted enter-room bug keeps this format
   regression independent of the protocol-unrolling depth.  The complete
   reach relation remains above as static theory content. *)
Inductive zoo_hotel_pinned:
  (!s r g. zoo_hotel_safe s r /\ g IN zoo_hotel_isin s r /\
           zoo_hotel_owns s r <> SOME g ==>
           zoo_hotel_pinned s r g)
End

(* Point-free relative to its own type, though not relative to its
   pattern: the equation binds two formals, but [strip_fun] on
   [(num -> num) -> num -> (num -> num)] peels the trailing arrow too,
   giving three domains -- one more than the equation's own arity -- so
   a graph-clause synthesiser driven by the type alone must refuse this
   rather than assume the equation is already at maximal application. *)
Definition zoo_graph_select_def:
  zoo_graph_select (g : num -> num) (x : num) = g
End

(* A step equation that calls a different function of the same arity,
   rather than recursing on the function being defined: [flatten_rhs]
   must refuse this by falling through to its final [else NONE], never
   mistaking the call for a self-recursive one and building a clause
   set against the wrong relation. *)
Definition zoo_graph_other_def:
  zoo_graph_other (t : num list) (l : num list) = l
End

Definition zoo_graph_calls_other_def:
  (zoo_graph_calls_other ([] : num list) (l : num list) = l) /\
  (zoo_graph_calls_other (h :: t) l = zoo_graph_other t l)
End

(* A product-typed formal that stays a bare variable: no pattern ever
   destructures [p], so a candidate mode that splits it into a separate
   input half and output half cannot be applied to the actual term --
   [split_arguments] can only recurse into a literal pair constructor.
   Witnesses [check_graph_clause]'s blanket handler on a live raiser. *)
Definition zoo_graph_pair_formal_def:
  zoo_graph_pair_formal (p : num # num) (n : num) = n
End
