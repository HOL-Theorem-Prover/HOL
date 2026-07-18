open testutils
open refuteTheory
open refute_cvTheory
open refuteTableZooTheory
open sortingTheory
open realTheory
open Refute_Core
open Refute_Gen
open Refute_Cert
open Refute_Eval
open Refute_EvalCompute
open Refute_EvalSML
open Refute_EvalCv
open Refute_Extract
open Refute_QC
open cv_transLib

(* cv_std loads ratTheory, whose parser preference would otherwise make
   unannotated selftest numerals rationals. *)
val _ = numLib.prefer_num ()

val erc = ref 0
val _ = diemode := Remember erc

val _ = tprint "Refute skeleton smoke check"
val _ = require_msg (check_result (fn () => true)) (fn () => "")
                    (fn () => ()) ()

val _ = tprint "Refute support theory"

fun constructor_count ty =
  length (TypeBasePure.constructors_of (valOf (TypeBase.fetch ty)))

fun check_type (ty, count) =
  require_msg (check_result (fn () => constructor_count ty = count))
              (fn () => "unexpected TypeBase constructor count")
              (fn () => ()) ()

val _ = check_type (``:refute$rf1``, 1)
val _ = check_type (``:refute$rf2``, 2)
val _ = check_type (``:refute$rf3``, 3)
val _ = check_type (``:refute$rf4``, 4)
val _ = check_type (``:refute$rf5``, 5)
val _ = check_type (``:refute$rf6``, 6)

fun same_conclusion left right =
  Term.aconv (Thm.concl left) (Thm.concl right)

fun check_theorem_set settype expected =
  let
    val actual = ThmSetData.added_thms
      (ThmSetData.theory_data {settype = settype, thy = "refute"})
    fun contains theorem = List.exists (same_conclusion theorem) actual
  in
    require_msg (check_result (fn () =>
      length actual = length expected andalso List.all contains expected))
      (fn () => "unexpected contents in " ^ settype)
      (fn () => ()) ()
  end

val _ = check_theorem_set "refute_simp" [list_size_simp]
val _ = check_theorem_set "refute_psimp" [Eps_psimp]
val _ = check_theorem_set "refute_unfold"
  [one_case_unfold, num_case_unfold]

val same_string_set : string list -> string list -> bool = Lib.set_eq

fun cv_ancestry_is_separate () =
  same_string_set (Theory.parents "refute")
    ["real", "sorting", "words"] andalso
  same_string_set (Theory.parents "refute_cv") ["refute", "cv_std"] andalso
  not (Lib.mem "cv_std" (Theory.ancestry "refute"))

val _ = require_msg (check_result cv_ancestry_is_separate) (fn () =>
  "refute parents: " ^ String.concatWith ", " (Theory.parents "refute") ^
  "; refute_cv parents: " ^
  String.concatWith ", " (Theory.parents "refute_cv"))
  (fn () => ()) ()

val _ = tprint "Refute model-finder names"

structure MFN = Refute_ModelFinder_Names

fun var_name variable = #1 (Term.dest_var variable)

fun mf_name_round_trips () =
  let
    val ty = ``:num``
    val selector = MFN.mk_selector 2 "list$CONS" ty
    val discriminator = MFN.mk_discriminator "list$CONS" ty
    val skolem = MFN.mk_skolem 1 7 "witness" ty
    val nested = MFN.sel_prefix_for 0 ^ var_name skolem
  in
    var_name selector = "refute$sel2$list$CONS" andalso
    MFN.is_sel (var_name selector) andalso
    MFN.sel_no_from_name (var_name selector) = 2 andalso
    MFN.original_name (var_name selector) = "list$CONS" andalso
    var_name discriminator = "refute$is$list$CONS" andalso
    MFN.is_sel (var_name discriminator) andalso
    MFN.sel_no_from_name (var_name discriminator) = ~1 andalso
    MFN.original_name (var_name discriminator) = "list$CONS" andalso
    var_name skolem = "refute$sk1@7$witness" andalso
    MFN.is_skolem_name (var_name skolem) andalso
    MFN.is_skolem_name nested andalso
    MFN.original_name (var_name skolem) = "witness" andalso
    var_name (MFN.mk_numeral 3 ty) = "refute$num$3" andalso
    var_name (MFN.mk_eval 4 ty) = "refute$eval4" andalso
    var_name (MFN.unknown_marker ty) = "?" andalso
    var_name (MFN.unrepresented_marker ty) = "…" andalso
    var_name (MFN.unrepresented_marker_ascii ty) = "..." andalso
    var_name (MFN.irrelevant_marker ty) = "_" andalso
    Parse.term_to_string (MFN.irrelevant_marker ty) = "_" andalso
    var_name (MFN.fake_atom 1 ty) = "a1"
  end

val _ = require_msg (check_result mf_name_round_trips) (fn () =>
  "model-finder fabricated names did not round-trip")
  (fn () => ()) ()

fun mf_variant_renames_goal_first () =
  let
    val ty = ``:num``
    val question = Term.mk_var ("?", ty)
    val atom = Term.mk_var ("a1", ty)
    val goal = boolSyntax.mk_eq (question, atom)
    val fabricated = [MFN.unknown_marker ty, MFN.fake_atom 1 ty]
    val (renamed, renaming) =
      MFN.rename_colliding_goal_vars fabricated goal
    val selector = MFN.mk_selector 0 "list$CONS" ty
    val (renamed_selector, selector_renaming) =
      MFN.rename_colliding_goal_vars [selector]
        (boolSyntax.mk_eq (selector, selector))
  in
    map var_name (Term.free_vars_lr renamed) = ["?'", "a1'"] andalso
    map (fn (old, fresh) => (var_name old, var_name fresh)) renaming =
      [("?", "?'"), ("a1", "a1'")] andalso
    map var_name fabricated = ["?", "a1"] andalso
    map var_name (Term.free_vars_lr renamed_selector) =
      ["user$refute$sel0$list$CONS"] andalso
    map (fn (old, fresh) => (var_name old, var_name fresh))
      selector_renaming =
      [("refute$sel0$list$CONS", "user$refute$sel0$list$CONS")]
  end

val _ = require_msg (check_result mf_variant_renames_goal_first) (fn () =>
  "model-finder collision handling did not rename the user goal first")
  (fn () => ()) ()

fun mf_reserved_name_guards () =
  let
    val clean = Term.mk_var ("x", ``:num``)
    val reserved = MFN.mk_selector 0 "C" ``:num``
    val entry_rejected =
      ((MFN.assert_user_goal (boolSyntax.mk_eq (reserved, reserved)); false)
       handle HOL_ERR _ => true)
    val bound_entry_rejected =
      ((MFN.assert_user_goal
          (boolSyntax.mk_forall
            (reserved, boolSyntax.mk_eq (reserved, reserved))); false)
       handle HOL_ERR _ => true)
    val escape_rejected =
      ((MFN.assert_no_reserved_in_theorem "selftest"
          (Thm.REFL reserved); false)
       handle HOL_ERR _ => true)
    val clean_accepted =
      ((MFN.assert_user_goal (boolSyntax.mk_eq (clean, clean));
        MFN.assert_no_reserved_in_theorem "selftest" (Thm.REFL clean);
        true)
       handle HOL_ERR _ => false)
  in
    entry_rejected andalso bound_entry_rejected andalso
    escape_rejected andalso clean_accepted
  end

val _ = require_msg (check_result mf_reserved_name_guards) (fn () =>
  "model-finder reserved-name entry/no-escape guards failed")
  (fn () => ()) ()

val _ = tprint "Refute model-finder HOL tables"

structure MFH = Refute_ModelFinder_HOL

val mf_hol_context : MFH.mf_context =
  MFH.make_context Refute_Core.default_mf_config []

fun mf_has_def constant =
  let val (_, fallback) = #def_tables mf_hol_context
  in not (null (MFH.def_props_for_const fallback constant)) end

fun mf_has_simp constant =
  not (null (MFH.def_props_for_const (!(#simp_table mf_hol_context))
    constant))

fun mf_has_psimp constant =
  not (null (MFH.def_props_for_const (#psimp_table mf_hol_context)
    constant))

fun term_has_const key term =
  List.exists (fn constant => MFH.const_key constant = key)
    (HolKernel.find_terms Term.is_const term)

fun mf_table_zoo () =
  let
    val total = ``zoo_total : num -> num``
    val primitive = ``zoo_height : zoo_tree -> num``
    val specification = ``zoo_spec : num``
    val raw_specification = ``zoo_raw_spec : num``
    val even = ``zoo_even : num -> bool``
    val odd = ``zoo_odd : num -> bool``
    val tree_case = TypeBase.case_const_of ``:zoo_tree``
    val record_case = TypeBase.case_const_of ``:zoo_record``
    val fields = TypeBase.fields_of ``:zoo_record``
    val {accessor, fupd, ...} = #2 (hd fields)
    val total_axioms = MFH.equational_fun_axioms mf_hol_context total
    val total_definition = MFH.def_of_const mf_hol_context total
    val wfrec = {Thy = "relation", Name = "WFREC"}
    val choice_only =
      MFH.is_choice_spec_fun mf_hol_context specification andalso
      MFH.is_choice_spec_fun mf_hol_context raw_specification andalso
      MFH.is_choice_spec_fun mf_hol_context
        ``pred_set$CHOICE : num set -> num`` andalso
      not (MFH.is_choice_spec_fun mf_hol_context
        ``pred_set$EMPTY : num set``) andalso
      not (mf_has_def specification) andalso
      not (mf_has_def raw_specification)
    val clean_total =
      not (null total_axioms) andalso
      not (List.exists (term_has_const wfrec) total_axioms) andalso
      (case total_definition of
           SOME definition => not (term_has_const wfrec definition)
         | NONE => false)
  in
    List.all mf_has_def
      [total, primitive, tree_case, record_case, accessor, fupd,
       even, odd] andalso
    List.all mf_has_simp [total, primitive, even, odd] andalso
    choice_only andalso clean_total andalso
    MFH.is_record_get accessor andalso MFH.is_record_update fupd andalso
    mf_has_psimp ``$@ : (num -> bool) -> num`` andalso
    mf_has_simp ``list_size : ('a -> num) -> 'a list -> num`` andalso
    (case MFH.def_of_const_ext mf_hol_context
       ``one_CASE : unit -> 'a -> 'a`` of
         SOME (true, _) => true
       | _ => false)
  end

val _ = require_msg (check_result mf_table_zoo) (fn () =>
  "model-finder def/simp/psimp/choice-spec table zoo failed")
  (fn () => ()) ()

fun mf_definition_last_wins () =
  let
    val constant = ``zoo_total : num -> num``
    val old = boolSyntax.mk_eq (constant, ``\n : num. 0``)
    val latest = boolSyntax.mk_eq (constant, ``\n : num. 1``)
    val condition = ``p : bool``
    val conditional = boolSyntax.mk_imp (condition, latest)
    val table = MFH.def_table_for [old, latest]
    val conditional_table = MFH.def_table_for [conditional]
    val (unfold, _) = #def_tables mf_hol_context
    val override = ``zoo_override : num -> num``
    val actual_override_latest =
      case MFH.get_def_of_const unfold override of
          SOME definition => Term.aconv definition ``\n : num. n``
        | NONE => false
  in
    (case MFH.get_def_of_const table constant of
         SOME definition => Term.aconv definition ``\n : num. 1``
       | NONE => false) andalso
    not (Option.isSome
      (MFH.get_def_of_const conditional_table constant)) andalso
    actual_override_latest andalso
    (case MFH.def_of_const_ext mf_hol_context override of
         SOME (true, _) => true
       | _ => false) andalso
    (case MFH.def_of_const_ext mf_hol_context
       ``$?! : (num -> bool) -> bool`` of
         SOME (true, _) => true
       | _ => false)
  end

val _ = require_msg (check_result mf_definition_last_wins) (fn () =>
  "model-finder definition precedence was not last-wins")
  (fn () => ()) ()

fun mf_equational_completeness () =
  MFH.is_equational_fun_surely_complete mf_hol_context
    ``zoo_total : num -> num`` andalso
  not (MFH.is_equational_fun_surely_complete mf_hol_context
    ``$@ : (num -> bool) -> num``)

val _ = require_msg (check_result mf_equational_completeness) (fn () =>
  "model-finder conditional equations were classified as complete")
  (fn () => ()) ()

fun mf_nondef_helpers () =
  let
    val prop = ``zoo_total n = zoo_height (ZooLeaf n)``
    val table = MFH.const_nondef_table [prop]
  in
    (case MFH.table_lookup table ``zoo_total : num -> num`` of
         [actual] => Term.aconv actual prop
       | _ => false) andalso
    (case MFH.table_lookup table ``zoo_height : zoo_tree -> num`` of
         [actual] => Term.aconv actual prop
       | _ => false) andalso
    MFH.is_poly_term ``[] : 'a list`` andalso
    not (MFH.is_poly_term ``[] : num list``)
  end

val _ = require_msg (check_result mf_nondef_helpers) (fn () =>
  "model-finder nondef indexing or polymorphism test failed")
  (fn () => ()) ()

fun mf_constructor_recognizers () =
  let
    val constructors = MFH.data_type_constrs mf_hol_context ``:num list``
    val expected = [``NIL : num list``,
                    ``CONS : num -> num list -> num list``]
  in
    ListPair.allEq (fn (left, right) => Term.aconv left right)
      (constructors, expected) andalso
    List.all MFH.is_constr constructors andalso
    MFH.is_data_type ``:num list`` andalso
    MFH.is_data_type ``:zoo_record`` andalso
    not (MFH.is_data_type ``:num``) andalso
    MFH.is_integer_type ``:num`` andalso MFH.is_integer_type ``:int`` andalso
    MFH.is_descr ``$@ : (num -> bool) -> num`` andalso
    MFH.is_descr ``safe_The : (num -> bool) -> num`` andalso
    MFH.is_exists_unique ``$?! : (num -> bool) -> bool``
  end

val _ = require_msg (check_result mf_constructor_recognizers) (fn () =>
  "model-finder TypeBase recognizers/constructor enumeration failed")
  (fn () => ()) ()

val _ = tprint "Refute model-finder HOL synthesis"

fun mf_selector_discriminator_roundtrips () =
  let
    val list_constructors =
      MFH.data_type_constrs mf_hol_context ``:num list``
    val nil_constructor = List.nth (list_constructors, 0)
    val cons = List.nth (list_constructors, 1)
    val list_value = ``[3; 4] : num list``
    val list_variable = ``xs : num list``
    val list_args = [
      MFH.select_nth_constr_arg mf_hol_context cons list_variable 0
        ``:num``,
      MFH.select_nth_constr_arg mf_hol_context cons list_variable 1
        ``:num list``]
    val tree_constructors =
      MFH.data_type_constrs mf_hol_context ``:zoo_tree``
    val leaf = List.nth (tree_constructors, 0)
    val node = List.nth (tree_constructors, 1)
    val tree_variable = ``tr : zoo_tree``
    val tree_args = List.tabulate (2, fn index =>
      MFH.select_nth_constr_arg mf_hol_context node tree_variable index
        ``:zoo_tree``)
    val record_constructor = hd
      (MFH.data_type_constrs mf_hol_context ``:zoo_record``)
    val record_variable = ``r : zoo_record``
    val expanded_record = MFH.constr_expand mf_hol_context
      ``:zoo_record`` record_variable
    val (expanded_record_head, expanded_record_args) =
      HolKernel.strip_comb expanded_record
    val mutual_constructor = List.nth
      (MFH.data_type_constrs mf_hol_context ``:zoo_even_tree``, 1)
    val mutual_value = ``ZooEvenNode (ZooOddNode (ZooEvenLeaf 2))``
    val mutual_variable = ``even : zoo_even_tree``
    val mutual_arg = MFH.select_nth_constr_arg mf_hol_context
      mutual_constructor mutual_variable 0 ``:zoo_odd_tree``
    val pair_constructor = hd
      (MFH.constructors_for mf_hol_context ``:num # bool``)
    val pair_variable = ``p : num # bool``
    val pair_tys = MFH.constructor_arg_types pair_constructor
    val pair_args = List.tabulate (2, fn index =>
      MFH.select_nth_constr_arg mf_hol_context pair_constructor
        pair_variable index (List.nth (pair_tys, index)))
    val generated_discriminator =
      MFH.discriminate_value mf_hol_context cons list_variable
    val (generated_discriminator_head, _) =
      HolKernel.strip_comb generated_discriminator
    val generated_discriminator_ok =
      case Lib.total Term.dest_var generated_discriminator_head of
          SOME (name, _) =>
            String.isPrefix MFN.discr_prefix name andalso
            MFN.original_name name = MFH.constructor_name cons
        | NONE => false
    val wrong_constructor_selection =
      MFH.select_nth_constr_arg mf_hol_context cons
        nil_constructor 0 ``:num``
  in
    Term.aconv
      (MFH.discriminate_value mf_hol_context cons list_value)
      boolSyntax.T andalso
    Term.aconv
      (MFH.discriminate_value mf_hol_context nil_constructor list_value)
      boolSyntax.F andalso
    Term.aconv
      (MFH.select_nth_constr_arg mf_hol_context cons list_value 0
        ``:num``) ``3`` andalso
    Term.aconv
      (MFH.construct_value mf_hol_context cons list_args) list_variable andalso
    Term.aconv
      (MFH.select_nth_constr_arg mf_hol_context leaf ``ZooLeaf 8`` 0
        ``:num``) ``8`` andalso
    Term.aconv (MFH.construct_value mf_hol_context node tree_args)
      tree_variable andalso
    Term.same_const record_constructor expanded_record_head andalso
    length expanded_record_args = 2 andalso
    Term.aconv
      (MFH.discriminate_value mf_hol_context mutual_constructor
        mutual_value) boolSyntax.T andalso
    Term.aconv (MFH.construct_value mf_hol_context mutual_constructor
      [mutual_arg]) mutual_variable andalso
    Term.aconv
      (MFH.construct_value mf_hol_context pair_constructor pair_args)
      pair_variable andalso
    generated_discriminator_ok andalso
    Term.type_of generated_discriminator = Type.bool andalso
    Term.aconv wrong_constructor_selection (MFH.unknown_value ``:num``) andalso
    length (MFH.constructor_arg_types record_constructor) = 2
  end

val _ = require_msg
  (check_result mf_selector_discriminator_roundtrips) (fn () =>
    "model-finder selector/discriminator synthesis did not round-trip")
  (fn () => ()) ()

fun mf_record_optimizations () =
  let
    val constructor = hd
      (MFH.data_type_constrs mf_hol_context ``:zoo_record``)
    val record = Term.list_mk_comb
      (constructor, [``4 : num``, boolSyntax.T])
    val expected = Term.list_mk_comb
      (constructor, [``4 + 1 : num``, boolSyntax.T])
    val {accessor, fupd, ...} = #2
      (hd (TypeBase.fields_of ``:zoo_record``))
    val get = MFH.optimized_record_get mf_hol_context accessor record
    val update_function = ``\n : num. n + 1``
    val update = MFH.optimized_record_update mf_hol_context fupd
      update_function record
    val unfolded_get = MFH.unfold_defs_in_term mf_hol_context
      (Term.mk_comb (accessor, record))
    val unfolded_update = MFH.unfold_defs_in_term mf_hol_context
      (Term.list_mk_comb (fupd, [update_function, record]))
    val polymorphic_update =
      ``zoo_poly_fupd (\n : num. n = 0)
          <|zoo_poly := 1; zoo_poly_bit := T|>``
    val (polymorphic_fupd, polymorphic_arguments) =
      HolKernel.strip_comb polymorphic_update
    val polymorphic_constructor = hd
      (MFH.data_type_constrs mf_hol_context
        ``:num zoo_poly_record``)
    val polymorphic_record = Term.list_mk_comb
      (polymorphic_constructor, [``1 : num``, boolSyntax.T])
    val changed_type = MFH.optimized_record_update mf_hol_context
      polymorphic_fupd (hd polymorphic_arguments) polymorphic_record
    val output_constructor = hd
      (MFH.data_type_constrs mf_hol_context
        ``:bool zoo_poly_record``)
    val expected_changed = Term.list_mk_comb
      (output_constructor, [``1 = 0``, boolSyntax.T])
    val tail_update =
      ``zoo_tail_poly_fupd (\n : num. n = 0)
          <|zoo_tail_bit := T; zoo_tail_poly := 1|>``
    val (tail_fupd, tail_update_arguments) =
      HolKernel.strip_comb tail_update
    val tail_input_constructor = hd
      (MFH.data_type_constrs mf_hol_context
        ``:num zoo_poly_tail_record``)
    val tail_input = Term.list_mk_comb
      (tail_input_constructor, [boolSyntax.T, ``1 : num``])
    val tail_changed = MFH.optimized_record_update mf_hol_context
      tail_fupd (hd tail_update_arguments) tail_input
    val tail_output_constructor = hd
      (MFH.data_type_constrs mf_hol_context
        ``:bool zoo_poly_tail_record``)
    val expected_tail_changed = Term.list_mk_comb
      (tail_output_constructor, [boolSyntax.T, ``1 = 0``])
  in
    Term.aconv get ``4`` andalso
    Term.aconv update expected andalso
    Term.aconv unfolded_get ``4`` andalso
    Term.aconv unfolded_update expected andalso
    Term.aconv changed_type expected_changed andalso
    Term.aconv tail_changed expected_tail_changed
  end

val _ = require_msg (check_result mf_record_optimizations) (fn () =>
  "model-finder record get/update optimization failed")
  (fn () => ()) ()

fun contains_constant key term =
  List.exists (fn constant => MFH.same_key (MFH.const_key constant) key)
    (HolKernel.find_terms Term.is_const term)

fun mf_case_order_conformance () =
  let
    val nested =
      ``list_CASE [SOME 2] 0
          (\h t. option_CASE h 1 (\n : num. n))``
    val partial = ``list_CASE (xs : num list)``
    val capture_candidate =
      ``rf3_CASE (r : refute$rf3) (x0 : num)``
    val unfolded_nested = MFH.unfold_defs_in_term mf_hol_context nested
    val unfolded_partial = MFH.unfold_defs_in_term mf_hol_context partial
    val unfolded_capture = MFH.unfold_defs_in_term mf_hol_context
      capture_candidate
    val closed_partial = MFH.unfold_defs_in_term mf_hol_context
      ``(list_CASE [3 : num]) :
          num -> (num -> num list -> num) -> num``
    val applied_partial = MFH.s_betapplys
      (closed_partial,
       [``0 : num``, ``\h : num. \t : num list. h``])
    val (partial_head, partial_arguments) =
      HolKernel.strip_comb applied_partial
    val normalized_partial =
      MFH.s_betapplys (partial_head, partial_arguments)
    val list_case_key = {Thy = "list", Name = "list_CASE"}
    val option_case_key = {Thy = "option", Name = "option_CASE"}
  in
    Term.aconv unfolded_nested ``2`` andalso
    Term.type_of unfolded_partial = Term.type_of partial andalso
    Term.free_in ``x0 : num`` unfolded_capture andalso
    Term.free_in ``r : refute$rf3`` unfolded_capture andalso
    Term.aconv normalized_partial ``3 : num`` andalso
    not (contains_constant list_case_key unfolded_partial) andalso
    not (contains_constant list_case_key unfolded_nested) andalso
    not (contains_constant option_case_key unfolded_nested)
  end

val _ = require_msg (check_result mf_case_order_conformance) (fn () =>
  "model-finder case unfolding violated scrutinee-first HOL4 order")
  (fn () => ()) ()

fun mf_builtins_numerals_sets_and_ersatz () =
  let
    val numeral = ``37 : num``
    val integer = ``~12 : int``
    val bare_zero = numSyntax.alt_zero_tm
    val bare_one = numSyntax.mk_bit1 bare_zero
    val bare_integer = intSyntax.mk_negated
      (intSyntax.mk_injected bare_one)
    val literal = ``literal_case (\n : num. n + 1) 4``
    val set_builder = ``GSPEC (\n : num. (n + 1, n < 3))``
    val open_set_builder =
      ``GSPEC (\n : num. (x : num, n = 0))``
    val card = ``CARD ({T; F} : bool set)``
    val unfolded_set = MFH.unfold_defs_in_term mf_hol_context set_builder
    val unfolded_open_set = MFH.unfold_defs_in_term mf_hol_context
      open_set_builder
    val unfolded_card = MFH.unfold_defs_in_term mf_hol_context card
    val card_axioms = MFH.equational_fun_axioms mf_hol_context
      ``card' : 'a set -> num``
    val boolean_conditional = ``if b then T else F``
    val unfolded_conditional = MFH.unfold_defs_in_term mf_hol_context
      boolean_conditional
    val numeral_keys =
      [{Thy = "arithmetic", Name = "NUMERAL"},
       {Thy = "arithmetic", Name = "BIT1"},
       {Thy = "arithmetic", Name = "BIT2"},
       {Thy = "arithmetic", Name = "ZERO"}]
    fun built_in key = MFH.is_never_unfold_const
      (Term.prim_mk_const key)
    fun typed_built_in (({Thy, Name}, ty), _) =
      MFH.is_never_unfold_const
        (Term.mk_thy_const {Thy = Thy, Name = Name, Ty = ty})
  in
    MFH.is_built_in_const boolSyntax.IN_tm andalso
    length MFH.built_in_consts = 26 andalso
    length MFH.built_in_typed_consts = 17 andalso
    List.all (built_in o #1) MFH.built_in_consts andalso
    List.all typed_built_in MFH.built_in_typed_consts andalso
    List.all built_in numeral_keys andalso
    not (MFH.is_built_in_const
      (Term.prim_mk_const {Thy = "relation", Name = "TC"})) andalso
    (case MFH.numeral_value numeral of
         SOME value => Arbint.compare (value, Arbint.fromInt 37) = EQUAL
       | NONE => false) andalso
    (case MFH.numeral_value integer of
         SOME value => Arbint.compare (value, Arbint.fromInt ~12) = EQUAL
       | NONE => false) andalso
    (case MFH.numeral_value bare_zero of
         SOME value => Arbint.compare (value, Arbint.zero) = EQUAL
       | NONE => false) andalso
    (case MFH.numeral_value bare_one of
         SOME value => Arbint.compare (value, Arbint.one) = EQUAL
       | NONE => false) andalso
    (case MFH.numeral_value bare_integer of
         SOME value => Arbint.compare (value, Arbint.fromInt ~1) = EQUAL
       | NONE => false) andalso
    not (List.exists
      (contains_constant {Thy = "pred_set", Name = "CARD"}) card_axioms) andalso
    not (Option.isSome (MFH.def_of_const mf_hol_context
      ``$~ : bool -> bool``)) andalso
    not (MFH.is_built_in_const
      ``COND : bool -> bool -> bool -> bool``) andalso
    MFH.is_never_unfold_const
      ``COND : bool -> bool -> bool -> bool`` andalso
    Term.aconv unfolded_conditional boolean_conditional andalso
    Term.aconv (MFH.unfold_defs_in_term mf_hol_context literal)
      ``4 + 1`` andalso
    Term.type_of unfolded_set = ``:num set`` andalso
    Term.free_in ``x : num`` unfolded_open_set andalso
    not (contains_constant {Thy = "pred_set", Name = "GSPEC"}
      unfolded_set) andalso
    contains_constant {Thy = "refute", Name = "card'"} unfolded_card andalso
    not (contains_constant {Thy = "pred_set", Name = "CARD"}
      unfolded_card)
  end

val _ = require_msg
  (check_result mf_builtins_numerals_sets_and_ersatz) (fn () =>
    "model-finder built-in/numeral/set/ersatz mapping failed")
  (fn () => ()) ()

val _ = tprint "Refute model-finder preprocessing goldens"

structure MFP = Refute_ModelFinder_Preproc

fun fresh_mf_context () =
  MFH.make_context Refute_Core.default_mf_config []

fun mf_preproc_destroy_goldens () =
  let
    val context = fresh_mf_context ()
    val list_discriminator = MFN.mk_discriminator "list$CONS"
      ``:num list -> bool``
    val list_head = MFN.mk_selector 0 "list$CONS"
      ``:num list -> num``
    val list_tail = MFN.mk_selector 1 "list$CONS"
      ``:num list -> num list``
    val expected_list =
      ``(^list_discriminator) (xs : num list) /\
        h = (^list_head) xs /\ t = (^list_tail) xs``
    val actual_list = MFP.destroy_pulled_out_constrs context false true
      ``(xs : num list) = h :: t``
    val node_name = "refuteTableZoo$ZooNode"
    val tree_discriminator = MFN.mk_discriminator node_name
      ``:zoo_tree -> bool``
    val tree_left = MFN.mk_selector 0 node_name
      ``:zoo_tree -> zoo_tree``
    val tree_right = MFN.mk_selector 1 node_name
      ``:zoo_tree -> zoo_tree``
    val expected_tree =
      ``(^tree_discriminator) (tree : zoo_tree) /\
        left = (^tree_left) tree /\
        right = (^tree_right) tree``
    val actual_tree = MFP.destroy_pulled_out_constrs context false true
      ``(tree : zoo_tree) = ZooNode left right``
    val actual_suc = MFP.destroy_pulled_out_constrs context false true
      ``(n : num) = SUC m``
    val expected_suc = ``~((0 : num) = n) /\ m = n - 1``
    val (pipeline_lists, pipeline_list_defs, _, _) =
      MFP.preprocess_formulas (fresh_mf_context ()) []
        ``(xs : num list) = h :: t``
    val (pipeline_trees, pipeline_tree_defs, _, _) =
      MFP.preprocess_formulas (fresh_mf_context ()) []
        ``(tree : zoo_tree) = ZooNode left right``
    val weak_pattern = MFP.destroy_pulled_out_constrs context false false
      ``!h t h' t'. (h :: t : num list) = h' :: t'``
    val expected_weak_pattern =
      ``!h t h' t'. (h' : num) = h /\ (t' : num list) = t``
    val weak_nonpattern =
      ``REVERSE (xs : num list) = h :: t``
    val protected_axiom = ``(xs : num list) = h :: t``
    val large_argument = List.foldl (fn (_, result) =>
      numSyntax.mk_plus (result, ``1 : num``)) ``n : num``
      (List.tabulate (5, fn index => index))
    val generated_function = MFN.mk_reserved_var "refute$vfun"
      ``:num -> num list``
    val large_left = Term.mk_comb (generated_function, large_argument)
    val shared = Term.mk_var ("l", ``:num list``)
    val shared_constraints =
      boolSyntax.list_mk_conj
        [Term.mk_comb (list_discriminator, shared),
         boolSyntax.mk_eq (``h : num``, Term.mk_comb (list_head, shared)),
         boolSyntax.mk_eq
           (``t : num list``, Term.mk_comb (list_tail, shared))]
    val expected_shared = boolSyntax.mk_let
      (Term.mk_abs (shared, shared_constraints), large_left)
    val actual_shared = MFP.destroy_pulled_out_constrs context false true
      (boolSyntax.mk_eq (large_left, ``h :: t : num list``))
    val user_free_constructor = ``q (h :: t : num list)``
    val user_free_result =
      MFP.pull_out_universal_constrs context false user_free_constructor
    val first_generated_function = MFN.mk_reserved_var "refute$vfunA"
      ``:num -> bool``
    val second_generated_function = MFN.mk_reserved_var "refute$vfunB"
      ``:num -> bool``
    val first_option = optionSyntax.mk_some first_generated_function
    val second_option = optionSyntax.mk_some second_generated_function
    val binary_predicate =
      ``binary_q : ((num -> bool) option) ->
                   ((num -> bool) option) -> bool``
    val first_value = MFN.mk_reserved_var "refute$v2"
      (Term.type_of first_option)
    val second_value = MFN.mk_reserved_var "refute$v1"
      (Term.type_of second_option)
    val multiple_input = Term.list_mk_comb
      (binary_predicate, [first_option, second_option])
    val multiple_expected = boolSyntax.list_mk_imp
      ([boolSyntax.mk_eq (first_value, first_option),
        boolSyntax.mk_eq (second_value, second_option)],
       Term.list_mk_comb
         (binary_predicate, [first_value, second_value]))
    val multiple_result =
      MFP.pull_out_universal_constrs context false multiple_input
    val predicate = ``q : ((num -> bool) option) -> bool``
    val function = ``p : num -> bool``
    val option = optionSyntax.mk_some function
    val option_value = MFN.mk_reserved_var "refute$v1"
      (Term.type_of option)
    val definition_option = optionSyntax.mk_some first_generated_function
    val definition_implication = boolSyntax.mk_imp
      (Term.mk_comb (predicate, definition_option),
       ``conclusion : bool``)
    val definition_expected = boolSyntax.list_mk_imp
      ([boolSyntax.mk_eq (option_value, definition_option)],
       boolSyntax.mk_imp
         (Term.mk_comb (predicate, option_value), ``conclusion : bool``))
    val definition_result = MFP.pull_out_universal_constrs context true
      definition_implication
    val existential_input = boolSyntax.mk_exists (function,
      Term.mk_comb (predicate, option))
    val existential_expected = boolSyntax.list_mk_exists
      ([function, option_value], boolSyntax.mk_conj
        (boolSyntax.mk_eq (option_value, option),
         Term.mk_comb (predicate, option_value)))
    val existential_result =
      MFP.pull_out_existential_constrs context existential_input
    val first_function = ``f : num -> bool``
    val second_function = ``g : num -> bool``
    val nested_option =
      ``SOME (\n. (f : num -> bool) n /\ (g : num -> bool) n)``
    val nested_predicate =
      ``nested_q : ((num -> bool) option) -> bool``
    val nested_value = MFN.mk_reserved_var "refute$v1"
      (Term.type_of nested_option)
    val nested_input = boolSyntax.list_mk_exists
      ([first_function, second_function],
       Term.mk_comb (nested_predicate, nested_option))
    val nested_expected = boolSyntax.list_mk_exists
      ([first_function, second_function, nested_value],
       boolSyntax.mk_conj
         (boolSyntax.mk_eq (nested_value, nested_option),
          Term.mk_comb (nested_predicate, nested_value)))
    val nested_result =
      MFP.pull_out_existential_constrs context nested_input
    val relaxed_definition =
      MFP.pull_out_universal_constrs context true user_free_constructor
    val second_existential_predicate =
      ``two_q : ((num -> bool) option) ->
                 ((num -> bool) option) -> bool``
    val first_existential_value = MFN.mk_reserved_var "refute$v2"
      (Term.type_of first_option)
    val second_existential_value = MFN.mk_reserved_var "refute$v1"
      (Term.type_of second_option)
    val two_existential_input = boolSyntax.list_mk_exists
      ([first_generated_function, second_generated_function],
       Term.list_mk_comb
         (second_existential_predicate, [first_option, second_option]))
    val two_existential_expected = boolSyntax.list_mk_exists
      ([first_generated_function, second_generated_function,
        second_existential_value, first_existential_value],
       boolSyntax.list_mk_conj
         [boolSyntax.mk_eq (second_existential_value, second_option),
          boolSyntax.mk_eq (first_existential_value, first_option),
          Term.list_mk_comb
            (second_existential_predicate,
             [first_existential_value, second_existential_value])])
    val two_existential_result =
      MFP.pull_out_existential_constrs context two_existential_input
    val beta_variable = ``beta_variable : num``
    val beta_argument = ``beta_argument : num``
    val beta_redex = Term.mk_comb
      (Term.mk_abs (beta_variable,
         boolSyntax.mk_eq (beta_variable, beta_variable)),
       beta_argument)
    val beta_result =
      MFP.destroy_pulled_out_constrs context false true beta_redex
    val existential_beta_result =
      MFP.pull_out_existential_constrs context beta_redex
    val reserved_bound = MFN.mk_reserved_var "refute$v1"
      ``:num list``
    val ordinary_bound = ``bound_list : num list``
    fun bound_axiom variable = boolSyntax.mk_exists
      (variable, boolSyntax.mk_imp
        (boolSyntax.mk_eq (``[1] : num list``, variable), boolSyntax.F))
    val reserved_bound_result = MFP.destroy_pulled_out_constrs
      context true true (bound_axiom reserved_bound)
    val ordinary_bound_result = MFP.destroy_pulled_out_constrs
      context true true (bound_axiom ordinary_bound)
    val free_value = MFN.mk_reserved_var "refute$vfree"
      ``:num list``
    val colliding_bound = MFN.mk_reserved_var "refute$vfree"
      ``:num list``
    val fresh_bound = ``fresh_bound : num list``
    val bound_predicate = ``bound_predicate : num list -> bool``
    fun sibling_axiom variable = boolSyntax.mk_imp
      (boolSyntax.mk_eq (free_value, ``[1] : num list``),
       boolSyntax.mk_exists
         (variable, Term.mk_comb (bound_predicate, variable)))
    val colliding_result = MFP.destroy_pulled_out_constrs context true true
      (sibling_axiom colliding_bound)
    val fresh_result = MFP.destroy_pulled_out_constrs context true true
      (sibling_axiom fresh_bound)
  in
    Term.aconv actual_list expected_list andalso
    Term.aconv actual_tree expected_tree andalso
    Term.aconv actual_suc expected_suc andalso
    ListPair.allEq (fn (actual, expected) =>
      Term.aconv actual expected) (pipeline_lists, [expected_list]) andalso
    null pipeline_list_defs andalso
    ListPair.allEq (fn (actual, expected) =>
      Term.aconv actual expected) (pipeline_trees, [expected_tree]) andalso
    null pipeline_tree_defs andalso
    Term.aconv weak_pattern expected_weak_pattern andalso
    Term.aconv actual_shared expected_shared andalso
    Term.aconv user_free_result user_free_constructor andalso
    Term.aconv multiple_result multiple_expected andalso
    Term.aconv definition_result definition_expected andalso
    Term.aconv existential_result existential_expected andalso
    Term.aconv nested_result nested_expected andalso
    Term.aconv relaxed_definition user_free_constructor andalso
    Term.aconv two_existential_result two_existential_expected andalso
    Term.aconv beta_result beta_redex andalso
    Term.aconv existential_beta_result beta_redex andalso
    Term.aconv reserved_bound_result ordinary_bound_result andalso
    Term.aconv colliding_result fresh_result andalso
    Term.aconv
      (MFP.destroy_pulled_out_constrs context true true protected_axiom)
      protected_axiom andalso
    Term.aconv
      (MFP.destroy_pulled_out_constrs context false false
        weak_nonpattern)
      weak_nonpattern
  end

val _ = require_msg (check_result mf_preproc_destroy_goldens) (fn () =>
  "model-finder constructor-destruction golden changed")
  (fn () => ()) ()

fun mf_preproc_skolem_golden () =
  let
    val context = fresh_mf_context ()
    val input =
      ``!a b c : num. ?x : num. !d : num. ?y : num.
          x = a + b + c /\ y = d``
    val skolem = MFN.mk_skolem 3 1 "x"
      ``:num -> num -> num -> num``
    val expected =
      ``!a b c : num.
          let x = (^skolem) a b c
          in !d : num. ?y : num.
               x = a + b + c /\ y = d``
    val actual = MFP.skolemize_term_and_more context 3 input
    val metadata = !(#skolems context)
    val pipeline_context = fresh_mf_context ()
    val (pipeline_terms, pipeline_defs, pipeline_all_mono,
         pipeline_no_poly) =
      MFP.preprocess_formulas pipeline_context [] input
    val expected_pipeline =
      ``!c b a : num.
          let x = (^skolem) a b c
          in x = a + b + c``
    val axiom_context = fresh_mf_context ()
    val axiom = ``?w : num. w = 2``
    val unskolemized =
      MFP.skolemize_term_and_more axiom_context ~1 axiom
    val higher_order_context = fresh_mf_context ()
    val higher_order =
      ``!p : (num -> bool) # num. ?w : num. w = SND p``
    val higher_order_result =
      MFP.skolemize_term_and_more higher_order_context 3 higher_order
    val smart_context = fresh_mf_context ()
    val smart_result = MFP.skolemize_term_and_more smart_context 3
      ``(?w : num. T) /\ p``
    val negative_context = fresh_mf_context ()
    val negative_skolem = MFN.mk_skolem 0 1 "x" ``:num``
    val negative_result = MFP.skolemize_term_and_more negative_context 3
      ``~(!x : num. p x)``
    val neutral_context = fresh_mf_context ()
    val neutral_input = ``q (?x : num. p x)``
    val neutral_result =
      MFP.skolemize_term_and_more neutral_context 3 neutral_input
    val collected_context = fresh_mf_context ()
    val (collected, _, _, _) = MFP.axioms_for_term collected_context
      [axiom] boolSyntax.T
  in
    Term.aconv actual expected andalso
    metadata = [("refute$sk3@1$x", ["c", "b", "a"])] andalso
    ListPair.allEq (fn (result, golden) => Term.aconv result golden)
      (pipeline_terms, [expected_pipeline]) andalso
    null pipeline_defs andalso pipeline_all_mono andalso
    pipeline_no_poly andalso
    !(#skolems pipeline_context) =
      [("refute$sk3@1$x", ["c", "b", "a"])] andalso
    Term.aconv unskolemized axiom andalso
    null (!(#skolems axiom_context)) andalso
    Term.aconv higher_order_result higher_order andalso
    null (!(#skolems higher_order_context)) andalso
    Term.aconv smart_result ``p : bool`` andalso
    Term.aconv negative_result
      (boolSyntax.mk_neg (Term.mk_comb (``p : num -> bool``,
        negative_skolem))) andalso
    !(#skolems negative_context) = [("refute$sk0@1$x", [])] andalso
    Term.aconv neutral_result neutral_input andalso
    null (!(#skolems neutral_context)) andalso
    List.exists (Term.aconv axiom) collected andalso
    null (!(#skolems collected_context))
  end

val _ = require_msg (check_result mf_preproc_skolem_golden) (fn () =>
  "model-finder depth-three skolem golden changed")
  (fn () => ()) ()

fun mf_preproc_unfold_goldens () =
  let
    val context = fresh_mf_context ()
    val list_nil_discriminator = MFN.mk_discriminator "list$NIL"
      ``:num list -> bool``
    val list_head = MFN.mk_selector 0 "list$CONS"
      ``:num list -> num``
    val case_input =
      ``list_CASE (xs : num list) 7 (\h t. h + 1)``
    val expected_case =
      ``if (^list_nil_discriminator) (xs : num list) then 7
        else (^list_head) xs + 1``
    val actual_case = MFH.unfold_defs_in_term context case_input
    val case_goal = boolSyntax.mk_eq (case_input, ``9 : num``)
    val expected_case_goal = boolSyntax.mk_eq (expected_case, ``9 : num``)
    val (pipeline_cases, pipeline_case_defs, _, _) =
      MFP.preprocess_formulas (fresh_mf_context ()) [] case_goal
    val set_input =
      ``(2 : num) IN GSPEC (\n : num. (n + 1, n < 3))``
    val set_value = ``set_value : num``
    val expected_set = Term.mk_comb
      (Term.mk_abs (set_value,
         ``?x : num. (^set_value, T) = (x + 1, x < 3)``),
       ``2 : num``)
    val actual_set = set_input
      |> MFH.unfold_defs_in_term context
      |> MFP.destroy_set_Collect
    val (pipeline_sets, pipeline_set_defs, _, _) =
      MFP.preprocess_formulas (fresh_mf_context ()) [] set_input
    val expected_pipeline_set =
      ``?x : num. x + 1 = 2 /\ (x < 3 <=> T)``
    val direct_set = MFP.destroy_set_Collect
      ``(2 : num) IN (\n : num. n < 3)``
    val direct_set_variable = ``n : num``
    val expected_direct_set = Term.mk_comb
      (Term.mk_abs (direct_set_variable, ``n < 3``), ``2 : num``)
    val pair_first = MFP.simplify_constrs_and_sels context
      ``FST ((a : num), b : bool)``
    val pair_second = MFP.simplify_constrs_and_sels context
      ``SND ((a : num), b : bool)``
    val eta_variable = ``eta_n : num``
    val eta_function = ``eta_f : num -> num``
    val eta_argument = Term.mk_abs
      (eta_variable, Term.mk_comb (eta_function, eta_variable))
    val eta_option = optionSyntax.mk_some eta_argument
    val eta_result = MFP.simplify_constrs_and_sels context eta_option
    val list_tail = MFN.mk_selector 1 "list$CONS"
      ``:num list -> num list``
    val reconstructed_list = listSyntax.mk_cons
      (Term.mk_comb (list_head, ``xs : num list``),
       Term.mk_comb (list_tail, ``xs : num list``))
    val reconstructed_result =
      MFP.simplify_constrs_and_sels context reconstructed_list
    val reflexive_result = MFP.simplify_constrs_and_sels context
      ``(same : num) = same``
    val true_conditional_result = MFP.simplify_constrs_and_sels context
      ``if T then (left : num) else right``
    val false_conditional_result = MFP.simplify_constrs_and_sels context
      ``if F then (left : num) else right``
    val let_argument = ``let_x : num``
    val let_bound = ``let_x : num``
    val let_parameter = ``let_y : num``
    val let_function = boolSyntax.mk_let
      (Term.mk_abs (let_bound,
         Term.mk_abs (let_parameter,
           numSyntax.mk_plus (let_bound, let_parameter))),
       ``1 : num``)
    val let_result = MFH.s_betapply (let_function, let_argument)
  in
    Term.aconv actual_case expected_case andalso
    ListPair.allEq (fn (actual, expected) =>
      Term.aconv actual expected)
      (pipeline_cases, [expected_case_goal]) andalso
    null pipeline_case_defs andalso
    Term.aconv actual_set expected_set andalso
    ListPair.allEq (fn (actual, expected) =>
      Term.aconv actual expected)
      (pipeline_sets, [expected_pipeline_set]) andalso
    null pipeline_set_defs andalso
    Term.aconv direct_set expected_direct_set andalso
    Term.aconv pair_first ``a : num`` andalso
    Term.aconv pair_second ``b : bool`` andalso
    Term.aconv eta_result eta_option andalso
    Term.aconv reconstructed_result ``xs : num list`` andalso
    Term.aconv reflexive_result boolSyntax.T andalso
    Term.aconv true_conditional_result ``left : num`` andalso
    Term.aconv false_conditional_result ``right : num`` andalso
    Term.aconv let_result
      ``let let_z = 1 : num in let_z + let_x``
  end

val _ = require_msg (check_result mf_preproc_unfold_goldens) (fn () =>
  "model-finder case/set-comprehension golden changed")
  (fn () => ()) ()

fun mf_preproc_pipeline_shape () =
  let
    val context = fresh_mf_context ()
    val goal = ``?x : num. x = 3``
    val (nondefinitions, _, _, _) =
      MFP.preprocess_formulas context [] goal
    val skolems = !(#skolems context)
    val preprocessed = hd nondefinitions
    val free_names = map var_name (Term.free_vars_lr preprocessed)
    val expected_skolem = MFN.mk_skolem 0 1 "x" ``:num``
    val open_goal = ``(user_x : num) = 3``
    val value = MFN.mk_reserved_var "refute$vtest" ``:num``
    val open_value_goal = boolSyntax.mk_eq (value, ``3 : num``)
    val closed_value_goal =
      boolSyntax.mk_forall (value, open_value_goal)
    val equality_chain =
      boolSyntax.list_mk_imp
        ([boolSyntax.mk_eq (value, ``3 : num``),
          boolSyntax.mk_eq
            (MFN.mk_reserved_var "refute$vother" ``:num``, ``4``)],
         boolSyntax.mk_eq (value,
           MFN.mk_reserved_var "refute$vother" ``:num``))
    val definition = ``(defined_x : num) = 3``
    val (_, selected_definitions, _, _) =
      MFP.axioms_for_term (fresh_mf_context ()) [definition]
        ``(defined_x : num) = 4``
    val shadow_definition = ``(shadow_x : num) = 3``
    val shadow_goal =
      ``(!shadow_x : num. p shadow_x) /\ q (shadow_x : num)``
    val (_, shadow_definitions, _, _) =
      MFP.axioms_for_term (fresh_mf_context ()) [shadow_definition]
        shadow_goal
    val (_, bound_definitions, _, _) =
      MFP.axioms_for_term (fresh_mf_context ()) [shadow_definition]
        ``!shadow_x : num. p shadow_x``
    val interleaved_pattern =
      ``!condition. condition ==> !h : num. !t : num list.
          (pattern_f : num list -> num) (h :: t) = h``
    val interleaved_nonpattern =
      ``!condition. condition ==> !xs : num list.
          (pattern_f : num list -> num list) (REVERSE xs) = xs``
  in
    length nondefinitions >= 1 andalso
    skolems = [("refute$sk0@1$x", [])] andalso
    free_names = ["refute$sk0@1$x"] andalso
    Term.aconv preprocessed
      (boolSyntax.mk_eq (expected_skolem, ``3 : num``)) andalso
    Term.aconv (MFP.close_form open_goal) open_goal andalso
    Term.aconv (MFP.close_form open_value_goal) closed_value_goal andalso
    Term.aconv (MFP.destroy_universal_equalities equality_chain)
      ``(3 : num) = 4`` andalso
    List.exists (Term.aconv definition) selected_definitions andalso
    List.exists (Term.aconv shadow_definition) shadow_definitions andalso
    null bound_definitions andalso
    MFP.is_constructor_pattern_formula interleaved_pattern andalso
    not (MFP.is_constructor_pattern_formula interleaved_nonpattern)
  end

val _ = require_msg (check_result mf_preproc_pipeline_shape) (fn () =>
  "model-finder preprocessing pipeline shape changed")
  (fn () => ()) ()

fun mf_preproc_axiom_closure () =
  let
    val table_axiom_closed =
      case MFH.equational_fun_axioms (fresh_mf_context ())
             ``zoo_override : num -> num`` of
          [axiom] =>
            let val (variables, _) = boolSyntax.strip_forall axiom
            in
              length variables = 1 andalso
              null (Term.free_vars_lr axiom)
            end
        | _ => false
    val extensional_axiom = MFH.equationalize_term "closure golden"
      ``!f g : num -> num. f = g``
  in
    table_axiom_closed andalso
    case extensional_axiom of
        SOME axiom =>
          length (#1 (boolSyntax.strip_forall axiom)) = 3 andalso
          null (Term.free_vars_lr axiom) andalso
          Term.aconv axiom
            ``!f g : num -> num. !x : num. f x = g x``
      | NONE => false
  end

val _ = require_msg (check_result mf_preproc_axiom_closure) (fn () =>
  "model-finder theorem-table axiom was not universally closed")
  (fn () => ()) ()

fun mf_preproc_axiom_collection_golden () =
  let
    val total_context = fresh_mf_context ()
    val total_goal = ``zoo_total 2 = 4``
    val total_axioms =
      [``!n. zoo_total n =
          if n = 0 then 0 else SUC (zoo_total (n - 1))``]
    val (total_nondefs, total_defs, total_all_mono, total_no_poly) =
      MFP.axioms_for_term total_context [] total_goal
    val choice_context = fresh_mf_context ()
    val choice_goal = ``zoo_spec = 0``
    val choice_spec = ``EVEN zoo_spec``
    val choice_def_axioms =
      [``!n. EVEN (SUC n) <=> ~(EVEN n)``,
       ``EVEN 0 <=> T``]
    val (choice_nondefs, choice_defs, choice_all_mono, choice_no_poly) =
      MFP.axioms_for_term choice_context [] choice_goal
  in
    ListPair.allEq (fn (actual, expected) => Term.aconv actual expected)
      (total_nondefs, [total_goal]) andalso
    ListPair.allEq (fn (actual, expected) => Term.aconv actual expected)
      (total_defs, total_axioms) andalso
    total_all_mono andalso total_no_poly andalso
    ListPair.allEq (fn (actual, expected) => Term.aconv actual expected)
      (choice_nondefs, [choice_goal, choice_spec]) andalso
    ListPair.allEq (fn (actual, expected) => Term.aconv actual expected)
      (choice_defs, choice_def_axioms) andalso
    choice_all_mono andalso choice_no_poly
  end

val _ = require_msg
  (check_result mf_preproc_axiom_collection_golden) (fn () =>
    "model-finder axiom collection golden changed")
  (fn () => ()) ()

fun mf_preproc_existential_equality_golden () =
  let
    val beta_variable = ``beta_variable : num``
    val beta_argument = ``beta_argument : num``
    val existential = ``existential : num``
    val beta_redex = Term.mk_comb
      (Term.mk_abs (beta_variable,
         boolSyntax.mk_exists (existential,
           boolSyntax.mk_eq (existential, beta_variable))),
       beta_argument)
    val expected_redex = Term.mk_comb
      (Term.mk_abs (beta_variable, boolSyntax.T), beta_argument)
  in
    Term.aconv
      (MFP.destroy_existential_equalities
        ``?x : num. x = y /\ p x``)
      ``(p (y : num) : bool)`` andalso
    Term.aconv
      (MFP.destroy_existential_equalities
        ``?x : num. p x /\ x = y /\ q x``)
      ``p (y : num) /\ q y`` andalso
    Term.aconv
      (MFP.destroy_existential_equalities
        ``?x : num. p x /\ q x``)
      ``?x : num. q x /\ p x`` andalso
    Term.aconv
      (MFP.destroy_existential_equalities beta_redex)
      expected_redex
  end

val _ = require_msg
  (check_result mf_preproc_existential_equality_golden) (fn () =>
    "model-finder existential-equality golden changed")
  (fn () => ()) ()

fun mf_preproc_quantifier_golden () =
  let
    val distributed = Term.aconv
      (MFP.distribute_quantifiers ``!x : num. p x /\ q``)
      ``(!x : num. p x) /\ q``
    val negated = Term.aconv
      (MFP.distribute_quantifiers ``?x : num. ~(p x)``)
      ``~(!x : num. p x)``
    val value = MFN.mk_reserved_var "refute$vneg" ``:num``
    val negative_equality = boolSyntax.mk_neg
      (boolSyntax.mk_eq (value, ``3 : num``))
    val negative_preserved = Term.aconv
      (MFP.destroy_universal_equalities negative_equality)
      negative_equality
    val x = ``x : num``
    val x' = ``x' : num``
    val predicate = ``p : num -> bool``
    val inner = boolSyntax.mk_forall
      (x, Term.mk_comb (predicate, x))
    val shadowed = boolSyntax.mk_forall (x, inner)
    val distinct = boolSyntax.mk_forall (x', inner)
    val pushed_shadowed = MFP.push_quantifiers_inward shadowed
    val pushed_distinct = MFP.push_quantifiers_inward distinct
    val nested_input =
      ``!x : num. (?y : num. r y /\ q) \/ s x``
    val nested_expected =
      ``(!x : num. s x) \/ (?y : num. r y /\ q)``
    val nested_result = MFP.push_quantifiers_inward nested_input
    val high_cost_input =
      ``!f g h : (num -> num) -> num.
          f (\x. x) + g (\x. x) = h (\x. x)``
    val high_cost_result = MFP.push_quantifiers_inward high_cost_input
    val heterogeneous_input =
      ``!x : bool. !y : num. p x \/ q y \/ r x y``
    val heterogeneous_expected =
      ``!y : num. (!x : bool. r x y \/ p x) \/ q y``
    val heterogeneous_result =
      MFP.push_quantifiers_inward heterogeneous_input
    val atomic_quantifier = ``!x : num. T``
  in
    distributed andalso negated andalso negative_preserved andalso
    Term.aconv pushed_shadowed inner andalso
    Term.aconv pushed_distinct inner andalso
    Term.aconv nested_result nested_expected andalso
    Term.type_of high_cost_result = Type.bool andalso
    null (Term.free_vars_lr high_cost_result) andalso
    Term.aconv heterogeneous_result heterogeneous_expected andalso
    Term.aconv (MFP.push_quantifiers_inward atomic_quantifier)
      atomic_quantifier
  end

val _ = require_msg (check_result mf_preproc_quantifier_golden) (fn () =>
  "model-finder quantifier-distribution golden changed")
  (fn () => ()) ()

fun mf_cardinality_arithmetic () =
  let
    val missing_card_raises =
      ((MFH.bounded_card_of_type 100 ~1 [] ``:zoo_tree``; false)
       handle HOL_ERR _ => true)
    val product_overflow_is_normalized =
      ((MFH.card_of_type [] ``:word32 # word32``; false)
       handle Refute_ModelFinder_Util.TOO_LARGE _ => true)
    val unknown_word = ``:'a word``
  in
    MFH.card_of_type [] ``:bool`` = 2 andalso
    MFH.card_of_type [] ``:bool -> bool`` = 4 andalso
    MFH.card_of_type [] ``:word8`` = 256 andalso
    MFH.card_of_type [] ``:8`` = 8 andalso
    MFH.card_of_type [(unknown_word, 7)] unknown_word = 7 andalso
    MFH.bounded_card_of_type 3 4 [] ``:'a`` = 3 andalso
    MFH.bounded_card_of_type 3 4 [] ``:'a -> bool itself`` = 3 andalso
    MFH.bounded_card_of_type 100 4 [] ``:word32 # word32`` = 100 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 100 4 []
      ``:refute$rf3`` = 3 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 100 4 []
      ``:bool -> refute$rf3`` = 9 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 100 4 []
      ``:refute$rf3[2]`` = 9 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 100 4 []
      ``:zoo_tree`` = 0 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 100 4 []
      ``:zoo_even_tree`` = 0 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 100 4
      [(unknown_word, 7)] unknown_word = 7 andalso
    MFH.bounded_exact_card_of_type mf_hol_context [] 1 2 []
      ``:num -> bool`` = 0 andalso
    MFH.is_finite_type mf_hol_context ``:word8`` andalso
    MFH.is_finite_type mf_hol_context ``:refute$rf3`` andalso
    not (MFH.is_finite_type mf_hol_context ``:zoo_tree``) andalso
    not (MFH.is_finite_type mf_hol_context ``:num -> bool``) andalso
    missing_card_raises andalso product_overflow_is_normalized
  end

val _ = require_msg (check_result mf_cardinality_arithmetic) (fn () =>
  "model-finder exact/bounded cardinality arithmetic failed")
  (fn () => ()) ()

val _ = tprint "Refute model-finder scope"

structure MFS = Refute_ModelFinder_Scope

fun mf_scope_card_repair () =
  let
    val unit_repair = MFS.repair_card_assigns mf_hol_context
      ([(``:unit``, 3)], [])
    val enum_repair = MFS.repair_card_assigns mf_hol_context
      ([(``:refute$rf3``, 5)], [])
    val cons = List.nth
      (MFH.data_type_constrs mf_hol_context ``:num list``, 1)
  in
    unit_repair = SOME [(``:unit``, 1)] andalso
    enum_repair = SOME [(``:refute$rf3``, 3)] andalso
    MFS.domain_card 3 [] cons = 3
  end

val _ = require_msg (check_result mf_scope_card_repair) (fn () =>
  "model-finder datatype cardinality repair failed")
  (fn () => ()) ()

fun mf_scope_mono_partition () =
  let
    val alpha = ``:'a``
    val enum = ``:refute$rf3``
    val number = ``:num``
    val defaults = [(NONE, NONE)]
    val (mono, nonmono) =
      MFS.mono_partition defaults [alpha, enum, number]
    val overrides =
      [(SOME alpha, SOME true), (SOME enum, SOME false),
       (NONE, NONE)]
    val (overridden_mono, overridden_nonmono) =
      MFS.mono_partition overrides [alpha, enum, number]
    val (calculus_mono, _) = MFS.mono_partition_with
      (fn _ => true) defaults [alpha]
    val (_, pattern_nonmono) = MFS.mono_partition
      [(SOME ``:'a list``, SOME false), (NONE, NONE)]
      [``:num list``]
    val (_, pattern_scopes) = MFS.all_scopes mf_hol_context
      [(SOME ``:'a list``, [3]), (NONE, [1])]
      [(NONE, [~1])] [``:num list``, number] [] []
    val pattern_scope = hd pattern_scopes
  in
    mono = [enum, number] andalso nonmono = [alpha] andalso
    overridden_mono = [alpha, number] andalso
    overridden_nonmono = [enum] andalso
    pattern_nonmono = [``:num list``] andalso
    MFH.assignment_lookup (#card_assigns pattern_scope)
      ``:num list`` = SOME 3 andalso calculus_mono = [alpha]
  end

val _ = require_msg (check_result mf_scope_mono_partition) (fn () =>
  "model-finder fundamental monotonicity partition failed")
  (fn () => ()) ()

fun nondecreasing [] = true
  | nondecreasing [_] = true
  | nondecreasing (first :: second :: rest) =
      first <= second andalso nondecreasing (second :: rest)

fun mf_scope_enumeration_order () =
  let
    val ordered = MFS.all_combinations_ordered_smartly
      [(3, 0), (3, 0)]
    val (skipped, scopes) = MFS.all_scopes mf_hol_context
      [(NONE, [1, 2, 3])] [(NONE, [~1])]
      [``:refute$rf6``] [``:'a``] []
    val truncation_cards = MFS.default_cards @ [11]
    val (truncated, retained) = MFS.all_scopes mf_hol_context
      [(NONE, truncation_cards)] [(NONE, [~1])]
      [``:refute$rf6``] [``:'a``, ``:'b``, ``:'c``] []
    fun cards (scope : MFS.scope) =
      (valOf (MFH.assignment_lookup (#card_assigns scope)
         ``:refute$rf6``),
       valOf (MFH.assignment_lookup (#card_assigns scope) ``:'a``))
  in
    MFS.default_cards = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] andalso
    List.take (ordered, 3) = [[0, 0], [1, 1], [2, 2]] andalso
    nondecreasing (map MFS.combination_cost ordered) andalso
    skipped = 0 andalso length scopes = 9 andalso
    map cards (List.take (scopes, 3)) = [(1, 1), (2, 2), (3, 3)] andalso
    truncated = 9641 andalso length retained = MFS.max_scopes
  end

val _ = require_msg (check_result mf_scope_enumeration_order) (fn () =>
  "model-finder scope count or cost ordering changed")
  (fn () => ()) ()

fun mf_scope_offsets_and_facto_pairs () =
  let
    val (_, scopes) = MFS.all_scopes mf_hol_context
      [(NONE, [2])] [(NONE, [~1])]
      [``:refute$rf2``, ``:num``] [``:'a``, ``:unit``] []
    val scope = hd scopes
    val data_types = #data_types scope
    fun degenerate_pair (spec : MFS.data_type_spec) =
      #1 (#complete spec) = #2 (#complete spec) andalso
      #1 (#concrete spec) = #2 (#concrete spec)
  in
    MFS.offset_of_type (#ofs scope) ``:refute$rf2`` = 0 andalso
    MFS.offset_of_type (#ofs scope) ``:'a`` = 2 andalso
    MFS.offset_of_type (#ofs scope) ``:num`` = 4 andalso
    MFS.offset_of_type (#ofs scope) ``:bool`` = 4 andalso
    MFS.spec_of_type scope ``:unit`` = (1, 4) andalso
    List.all degenerate_pair data_types
  end

val _ = require_msg (check_result mf_scope_offsets_and_facto_pairs) (fn () =>
  "model-finder scope offsets or facto pairs failed")
  (fn () => ()) ()

val _ = tprint "Refute model-finder utility"

local
  open Refute_ModelFinder_Util
in
  structure MFU = Refute_ModelFinder_Util
end

fun mf_reasonable_power_edges () =
  MFU.reasonable_power 2 10 = 1024 andalso
  MFU.reasonable_power (~2) 5 = ~32 andalso
  MFU.reasonable_power 0 0 = 1 andalso
  MFU.reasonable_power 0 (~3) = 0 andalso
  MFU.reasonable_power 1 20000 = 1 andalso
  ((MFU.reasonable_power 2 (~1); false) handle MFU.ARG _ => true) andalso
  ((MFU.reasonable_power 2 16385; false)
   handle MFU.TOO_LARGE _ => true) andalso
  ((MFU.reasonable_power 2 100; false)
   handle MFU.TOO_LARGE _ => true) andalso
  ((MFU.reasonable_power 2 (valOf Int.minInt); false)
   handle MFU.ARG _ => true) andalso
  ((MFU.reasonable_power (valOf Int.minInt) 2; false)
   handle MFU.TOO_LARGE _ => true) andalso
  MFU.exact_log 2 1024 = 10 andalso
  MFU.exact_root 3 27 = 3

val _ = require_msg (check_result mf_reasonable_power_edges) (fn () =>
  "model-finder power arithmetic mishandled an edge case")
  (fn () => ()) ()

fun mf_combinatorics_fixed_inputs () =
  MFU.offset_list [2, 3, 4] = [0, 2, 5] andalso
  MFU.index_seq (~2) 4 = [~2, ~3, ~4, ~5] andalso
  MFU.filter_indices [0, 2, 4] [1, 2, 3, 4, 5] = [1, 3, 5] andalso
  MFU.filter_out_indices [0, 2, 4] [1, 2, 3, 4, 5] = [2, 4] andalso
  MFU.fold1 (fn left => fn right => left - right) [10, 3, 2] = 5 andalso
  MFU.replicate_list 2 [1, 2] = [1, 2, 1, 2] andalso
  MFU.all_distinct_unordered_pairs_of [1, 2, 3] =
    [(1, 2), (1, 3), (2, 3)] andalso
  MFU.nth_combination [(2, 10), (3, 20)] 4 = [11, 21] andalso
  MFU.all_combinations [(2, 10), (3, 20)] =
    [[10, 20], [10, 21], [10, 22],
     [11, 20], [11, 21], [11, 22]] andalso
  MFU.all_combinations [] = [[]] andalso
  MFU.all_permutations [1, 2, 3] =
    [[1, 2, 3], [1, 3, 2], [2, 1, 3],
     [2, 3, 1], [3, 1, 2], [3, 2, 1]] andalso
  MFU.all_permutations [] = [[]] andalso
  MFU.chunk_list 2 [1, 2, 3, 4, 5] = [[1, 2], [3, 4], [5]] andalso
  MFU.chunk_list_unevenly [2, 1] [1, 2, 3, 4, 5] =
    [[1, 2], [3], [4], [5]]

val _ = require_msg (check_result mf_combinatorics_fixed_inputs) (fn () =>
  "model-finder combinatorics changed on fixed inputs")
  (fn () => ()) ()

fun mf_lookup_precedence () =
  let
    val entries =
      [(SOME 12, "relaxed"), (SOME 2, "exact"), (NONE, "default")]
    fun congruent (left, right) = left mod 10 = right mod 10
  in
    MFU.double_lookup congruent entries 2 = SOME "relaxed" andalso
    MFU.triple_lookup congruent entries 2 = SOME "exact" andalso
    MFU.triple_lookup congruent entries 22 = SOME "relaxed" andalso
    MFU.triple_lookup congruent entries 7 = SOME "default"
  end

val _ = require_msg (check_result mf_lookup_precedence) (fn () =>
  "model-finder lookup precedence is incorrect")
  (fn () => ()) ()

val _ = tprint "Refute model-finder representations"

structure MFR = Refute_ModelFinder_Rep

fun mf_rep_arithmetic () =
  MFR.card_of_rep (MFR.Formula MFU.Neut) = 2 andalso
  MFR.arity_of_rep (MFR.Formula MFU.Neut) = 0 andalso
  MFR.card_of_rep (MFR.Struct [MFR.Atom (2, 0), MFR.Atom (3, 2)]) = 6
  andalso
  MFR.arity_of_rep (MFR.Struct [MFR.Atom (2, 0), MFR.Atom (3, 2)]) = 2
  andalso
  MFR.card_of_rep (MFR.Vect (3, MFR.Atom (2, 0))) = 8 andalso
  MFR.arity_of_rep (MFR.Vect (3, MFR.Atom (2, 0))) = 3 andalso
  MFR.card_of_rep
    (MFR.Func (MFR.Atom (2, 0), MFR.Atom (3, 2))) = 9 andalso
  MFR.arity_of_rep
    (MFR.Func (MFR.Atom (2, 0), MFR.Atom (3, 2))) = 2 andalso
  MFR.min_univ_card_of_rep
    (MFR.Opt (MFR.Struct [MFR.Atom (2, 0), MFR.Atom (3, 2)])) = 6
  andalso
  MFR.card_of_domain_from_rep 2 (MFR.Atom (16, 0)) = 4 andalso
  MFR.atom_schema_of_rep
    (MFR.Vect (2, MFR.Struct [MFR.Atom (2, 0), MFR.Atom (3, 4)])) =
    [(2, 0), (3, 4), (2, 0), (3, 4)] andalso
  MFR.all_combinations_for_rep
    (MFR.Struct [MFR.Atom (2, 1), MFR.Atom (2, 4)]) =
    [[1, 4], [1, 5], [2, 4], [2, 5]]

val _ = require_msg (check_result mf_rep_arithmetic) (fn () =>
  "model-finder rep cardinality, arity, or schema arithmetic failed")
  (fn () => ()) ()

fun mf_rep_ordering () =
  MFR.min_rep (MFR.Opt (MFR.Atom (2, 0)))
      (MFR.Formula MFU.Neut) = MFR.Opt (MFR.Atom (2, 0)) andalso
  MFR.min_rep (MFR.Formula MFU.Neut)
      (MFR.Formula MFU.Pos) = MFR.Formula MFU.Pos andalso
  MFR.min_rep (MFR.Atom (2, 0))
      (MFR.Struct [MFR.Atom (2, 0)]) = MFR.Atom (2, 0) andalso
  MFR.min_rep (MFR.Vect (3, MFR.Atom (2, 0)))
      (MFR.Vect (2, MFR.Atom (3, 0))) =
    MFR.Vect (2, MFR.Atom (3, 0)) andalso
  MFR.min_reps
      [MFR.Atom (2, 0), MFR.Vect (3, MFR.Atom (2, 0))]
      [MFR.Atom (2, 0), MFR.Vect (2, MFR.Atom (3, 0))] =
    [MFR.Atom (2, 0), MFR.Vect (2, MFR.Atom (3, 0))] andalso
  ((MFR.min_rep (MFR.Formula MFU.Pos) (MFR.Formula MFU.Neg); false)
   handle MFU.ARG _ => true)

val _ = require_msg (check_result mf_rep_ordering) (fn () =>
  "model-finder rep ordering or unification failed")
  (fn () => ()) ()

fun mf_rep_fixed_scope () =
  let
    val (_, scopes) = MFS.all_scopes mf_hol_context
      [(NONE, [2])] [(NONE, [~1])]
      [``:refute$rf2``, ``:num``] [] []
    val scope = hd scopes
    val enum_offset = MFS.offset_of_type (#ofs scope) ``:refute$rf2``
    val main_offset = MFS.offset_of_type (#ofs scope) ``:bool``
    val enum = MFR.Atom (2, enum_offset)
    val number = MFR.Atom (2, main_offset)
    val vector = MFR.best_one_rep_for_type scope
      ``:refute$rf2 -> num``
    val curried_relation = MFR.best_non_opt_set_rep_for_type scope
      ``:refute$rf2 -> refute$rf2 -> bool``
    val binary_relation =
      MFR.Func
        (MFR.Struct [enum, enum], MFR.Formula MFU.Neut)
    val curried_binary_relation =
      MFR.Func (enum, MFR.Func (enum, MFR.Formula MFU.Neut))
    val optional_curried_binary_relation =
      MFR.Func
        (enum, MFR.Func (enum, MFR.Opt (MFR.Atom (2, main_offset))))
    val pair_ty = ``:refute$rf2 # refute$rf2``
    val pair_offset = MFS.offset_of_type (#ofs scope) pair_ty
    val pair_endpoint = MFR.Struct [enum, enum]
    val pair_atom = MFR.Atom (4, pair_offset)
    val pair_curried_relation =
      MFR.Func
        (pair_endpoint,
         MFR.Func (pair_endpoint, MFR.Formula MFU.Neut))
    val atomized_pair_curried_relation =
      MFR.Func
        (pair_atom, MFR.Func (pair_atom, MFR.Formula MFU.Neut))
  in
    MFR.best_one_rep_for_type scope ``:refute$rf2 # num`` =
      MFR.Struct [enum, number] andalso
    vector = MFR.Vect (2, number) andalso
    MFR.card_of_rep vector = 4 andalso MFR.arity_of_rep vector = 2 andalso
    MFR.best_non_opt_set_rep_for_type scope
      ``:refute$rf2 -> bool`` =
      MFR.Func (enum, MFR.Formula MFU.Neut) andalso
    MFR.best_opt_set_rep_for_type scope ``:refute$rf2 -> num`` =
      MFR.Func (enum, MFR.Opt number) andalso
    MFR.best_set_rep_for_type scope ``:refute$rf2`` = enum andalso
    MFR.best_set_rep_for_type scope ``:num`` = MFR.Opt number andalso
    MFR.rep_to_binary_rel_rep (#ofs scope)
      ``:refute$rf2 -> refute$rf2 -> bool`` curried_relation =
      curried_binary_relation andalso
    MFR.rep_to_binary_rel_rep (#ofs scope)
      ``:(refute$rf2 # refute$rf2) -> bool`` binary_relation =
      binary_relation andalso
    MFR.rep_to_binary_rel_rep (#ofs scope)
      ``:refute$rf2 -> refute$rf2 -> bool`` binary_relation =
      curried_binary_relation andalso
    MFR.rep_to_binary_rel_rep (#ofs scope)
      ``:refute$rf2 -> refute$rf2 -> bool``
      (MFR.Atom (16, main_offset)) = curried_binary_relation andalso
    MFR.rep_to_binary_rel_rep (#ofs scope)
      ``:refute$rf2 -> refute$rf2 -> bool``
      (MFR.Opt (MFR.Atom (16, main_offset))) =
      curried_binary_relation andalso
    MFR.opt_rep (#ofs scope) ``:refute$rf2 -> refute$rf2 -> bool``
      curried_binary_relation = optional_curried_binary_relation andalso
    MFR.type_schema_of_rep ``:refute$rf2 -> refute$rf2 -> bool``
      curried_binary_relation = [``:refute$rf2``, ``:refute$rf2``] andalso
    MFR.type_schema_of_rep ``:refute$rf2 -> refute$rf2 -> bool``
      optional_curried_binary_relation =
      [``:refute$rf2``, ``:refute$rf2``, ``:bool``] andalso
    MFR.rep_to_binary_rel_rep (#ofs scope)
      ``:(refute$rf2 # refute$rf2) ->
         (refute$rf2 # refute$rf2) -> bool``
      pair_curried_relation = atomized_pair_curried_relation andalso
    MFR.type_schema_of_rep
      ``:(refute$rf2 # refute$rf2) ->
         (refute$rf2 # refute$rf2) -> bool``
      atomized_pair_curried_relation = [pair_ty, pair_ty] andalso
    MFR.type_schema_of_rep ``:refute$rf2 -> num`` vector =
      [``:num``, ``:num``]
  end

val _ = require_msg (check_result mf_rep_fixed_scope) (fn () =>
  "model-finder best reps changed on a fixed scope")
  (fn () => ()) ()

val _ = tprint "Refute model-finder peephole"

structure MFPP = Refute_ModelFinder_Peephole

fun mf_atom_codecs () =
  let
    fun int_round_trip card offset =
      List.all (fn atom =>
        MFPP.atom_for_int (card, offset)
          (MFPP.int_for_atom (card, offset) atom) = atom)
        (MFU.index_seq offset card)
    fun value_round_trip card offset =
      List.all (fn value =>
        MFPP.int_for_atom (card, offset)
          (MFPP.atom_for_int (card, offset) value) = value)
        (List.tabulate
          (card, fn index => MFPP.min_int_for_card card + index))
    fun successor_round_trip tabulate =
      MFPP.atom_seq_for_suc_rel
        (MFPP.suc_rel_for_atom_seq ((7, 49), tabulate)) =
      ((7, 49), tabulate)
  in
    MFPP.atom_for_bool 11 false = Refute_Forl.Atom 11 andalso
    MFPP.atom_for_bool 11 true = Refute_Forl.Atom 12 andalso
    MFPP.formula_for_bool false = Refute_Forl.False andalso
    MFPP.formula_for_bool true = Refute_Forl.True andalso
    MFPP.atom_for_nat (4, 10) (~1) = ~1 andalso
    MFPP.atom_for_nat (4, 10) 0 = 10 andalso
    MFPP.atom_for_nat (4, 10) 3 = 13 andalso
    MFPP.atom_for_nat (4, 10) 4 = ~1 andalso
    MFPP.atom_for_int (5, 20) (~3) = ~1 andalso
    MFPP.atom_for_int (5, 20) 3 = ~1 andalso
    int_round_trip 5 20 andalso value_round_trip 5 20 andalso
    int_round_trip 6 30 andalso value_round_trip 6 30 andalso
    successor_round_trip false andalso successor_round_trip true andalso
    ((MFPP.suc_rel_for_atom_seq ((7, 50), true); false)
     handle MFU.TOO_LARGE _ => true)
  end

val _ = require_msg (check_result mf_atom_codecs) (fn () =>
  "model-finder atom codec round-trip failed")
  (fn () => ()) ()

fun mf_peephole_formula_identities () =
  let
    open Refute_Forl
    val kk = MFPP.kodkod_constrs true 4 5 20
    val f = No Univ
    val declaration = DeclOne ((1, 0), AtomSeq (2, 0))
    val empty_declaration = DeclOne ((1, 1), None)
  in
    #kk_and kk True f = f andalso #kk_and kk False f = False andalso
    #kk_or kk False f = f andalso #kk_or kk f f = f andalso
    #kk_not kk (Not f) = f andalso #kk_not kk (Some Univ) = No Univ
    andalso
    #kk_iff kk f f = True andalso #kk_implies kk f f = True andalso
    #kk_formula_if kk True f False = f andalso
    #kk_formula_if kk f True False = f andalso
    #kk_all kk [declaration]
      (All ([empty_declaration], f)) = True andalso
    #kk_exist kk [empty_declaration] f = False
  end

val _ = require_msg (check_result mf_peephole_formula_identities)
  (fn () => "model-finder formula peepholes failed")
  (fn () => ()) ()

fun mf_peephole_relational_identities () =
  let
    open Refute_Forl
    val kk = MFPP.kodkod_constrs true 4 5 20
    val pair = Product (Atom 1, Atom 2)
    val projected = Project (pair, [Num 1, Num 0])
  in
    #kk_difference kk (Atom 1) (Atom 1) = None andalso
    #kk_intersect kk (Atom 1) (Atom 2) = None andalso
    #kk_product kk None (Atom 2) = Product (None, None) andalso
    #kk_closure kk None = None andalso
    #kk_reflexive_closure kk None = Iden andalso
    #kk_project kk pair [Num 0, Num 1] = pair andalso
    #kk_project kk projected [Num 1] = Project (pair, [Num 0]) andalso
    #kk_not3 kk (Atom 20) = Atom 21 andalso
    #kk_not3 kk (#kk_not3 kk (Rel (1, 7))) = Rel (1, 7) andalso
    #kk_comprehension kk [DeclOne ((1, 0), AtomSeq (2, 3))] True =
      AtomSeq (2, 3)
  end

val _ = require_msg (check_result mf_peephole_relational_identities)
  (fn () => "model-finder relational peepholes failed")
  (fn () => ()) ()

fun mf_peephole_arithmetic () =
  let
    open Refute_Forl
    val kk = MFPP.kodkod_constrs true 4 5 20
    fun apply relation left right =
      #kk_join kk right (Join (left, Rel relation))
  in
    #kk_join kk (Atom 22) (Rel MFPP.suc_rel) = Atom 23 andalso
    #kk_join kk (Atom 23) (Rel MFPP.suc_rel) = None andalso
    apply MFPP.nat_add_rel (Atom 21) (Atom 22) = Atom 23 andalso
    apply MFPP.nat_add_rel (Atom 22) (Atom 22) = None andalso
    apply MFPP.nat_subtract_rel (Atom 23) (Atom 21) = Atom 22 andalso
    apply MFPP.nat_subtract_rel (Atom 21) (Atom 23) = Atom 20 andalso
    apply MFPP.nat_multiply_rel (Atom 21) (Atom 23) = Atom 23 andalso
    apply MFPP.nat_multiply_rel (Atom 22) (Atom 22) = None andalso
    #kk_nat_less kk (Atom 21) (Atom 22) = Atom 21 andalso
    #kk_nat_less kk (Atom 22) (Atom 21) = Atom 20 andalso
    #kk_int_less kk (Atom 23) (Atom 22) = Atom 21
  end

val _ = require_msg (check_result mf_peephole_arithmetic) (fn () =>
  "model-finder arithmetic peepholes failed")
  (fn () => ()) ()

fun mf_peephole_disabled () =
  let
    open Refute_Forl
    val kk = MFPP.kodkod_constrs false 4 5 20
  in
    #kk_and kk True False = And (True, False) andalso
    #kk_not kk True = Not True andalso
    #kk_project_seq kk (Atom 1) 0 1 = Project (Atom 1, [Num 0]) andalso
    #kk_not3 kk (Atom 20) = Join (Atom 20, Rel MFPP.not3_rel)
  end

val _ = require_msg (check_result mf_peephole_disabled) (fn () =>
  "disabled model-finder peepholes did not preserve raw constructors")
  (fn () => ()) ()

val _ = tprint "Refute FORL serializer goldens"

local
  open Refute_Forl

  val golden_header = "HOL4 Refute FORL golden\nfixed timestamp"

  val layout_problem : problem =
    {comment = "layout problem\nsecond line",
     settings =
       [("solver", "\"DefaultSAT4J\""),
        ("symmetry_breaking", "20")],
     univ_card = 6,
     tuple_assigns =
       [AssignTuple ((1, ~1), Tuple [0]),
        AssignTuple ((2, 1), TupleIndex (2, 3)),
        AssignTupleSet ((3, ~2),
          TupleUnion
            (TupleSet [Tuple [0, 1, 2], TupleReg (3, 0)],
             TupleProject
               (TupleIntersect
                  (TupleProduct (TupleAtomSeq (2, 0), TupleAtomSeq (2, 2)),
                   TupleDifference
                     (TupleSetReg (3, 0), TupleSet [TupleIndex (3, 1)])),
                1)))],
     bounds =
       [([((1, 0), "unary * relation\ncontinued"),
          ((2, ~1), ""), ((3, 2), "ternary")],
         [TupleRange (Tuple [0], Tuple [3]),
          TupleArea (Tuple [0, 1], Tuple [2, 3])]),
        ([((4, ~2), "arity four")],
         [TupleUnion
            (TupleSet [],
             TupleProduct (TupleAtomSeq (2, 0), TupleAtomSeq (2, 2)))])],
     int_bounds =
       [(SOME (~7), [TupleSet [Tuple [4]]]),
        (NONE, [TupleRange (Tuple [0], Tuple [0]), TupleAtomSeq (3, 1)])],
     expr_assigns =
       [AssignRelReg ((2, ~1), Join (Rel (2, ~1), Rel (2, 1))),
        AssignIntReg (~1, Num (~12))],
     formula =
       And
         (Some (Rel (1, 0)),
          And
            (Subset (Product (Rel (1, 0), Rel (1, 0)), Rel (2, ~1)),
             IntEq (IntReg (~1), Num (~12))))}

  val relation_cases =
    [RelLet
       ([AssignFormulaReg (20, True),
         AssignRelReg ((1, 20), Atom 0),
         AssignIntReg (20, Num 0)], Rel (1, 20)),
     RelIf (FormulaReg 20, Atom 0, Atom 1),
     Union (Rel (1, 0), Difference (Rel (1, 1), Rel (1, 2))),
     Difference (Union (Rel (1, 0), Rel (1, 1)), Rel (1, 2)),
     Override (Rel (2, 0), Rel (2, 1)),
     Intersect (Rel (1, 0), Rel (1, 1)),
     Product (Rel (1, 0), Rel (1, 1)),
     IfNo (Rel (1, 0), Rel (1, 1)),
     Project (Rel (3, 0), [Num 0, Add (Num 1, Num 1)]),
     Join (Rel (2, 0), Join (Rel (2, 1), Rel (2, 2))),
     Closure (Union (Rel (2, 0), Rel (2, 1))),
     ReflexiveClosure
       (RelLet ([AssignRelReg ((2, 7), Rel (2, 0))], RelReg (2, 7))),
     Transpose
       (IfNo (Project (Rel (3, 0), [Num 0, Num 1]),
              Join (Rel (2, 0), Rel (2, 1)))),
     Comprehension
       ([DeclOne ((1, 8), Univ), DeclSet ((1, 9), Univ)],
        Subset (Var (1, 8), Var (1, 9))),
     Bits (Num (~3)), Int (Num 4), Iden, Ints, None, Univ,
     Atom (~1), AtomSeq (2, 3), Rel (1, ~1), Var (2, ~2),
     RelReg (3, ~3)]

  val integer_cases =
    [Sum ([DeclOne ((1, 0), Univ)], Cardinality (Var (1, 0))),
     IntLet ([AssignIntReg (0, Num 1)], Add (IntReg 0, Num 2)),
     IntIf (FormulaReg 0, Num 1, Num 2),
     SHL (Num 1, SHL (Num 2, Num 3)),
     SHA (Num 8, Num 1), SHR (Num 8, Num 1),
     Add (Num 1, Add (Num 2, Num 3)),
     Sub (Num 1, Sub (Num 2, Num 3)),
     Mult (Num 2, Mult (Num 3, Num 4)),
     Div (Num 8, Div (Num 4, Num 2)),
     Mod (Num 8, Mod (Num 4, Num 3)),
     Cardinality (Union (Rel (1, 0), Rel (1, 1))),
     SetSum (Rel (1, 0)),
     BitOr (Num 1, BitOr (Num 2, Num 3)),
     BitXor (BitXor (Num 1, Num 2), Num 3),
     BitAnd (Num 1, BitAnd (Num 2, Num 3)),
     BitNot (Add (Num 1, Num 2)),
     Neg (Add (Num 1, Num 2)), Absolute (Sub (Num 1, Num 2)),
     Signum (Num (~9)), Num (~42), IntReg (~1)]

  val formula_cases =
    [All
       ([DeclNo ((1, 0), None), DeclLone ((1, 1), Univ)],
        Exist
          ([DeclOne ((1, 2), Univ), DeclSome ((1, 3), Univ),
            DeclSet ((1, 4), Univ)], Some (Var (1, 2)))),
     FormulaLet ([AssignFormulaReg (0, True)], FormulaReg 0),
     FormulaIf (FormulaReg 0, True, False),
     Or (True, Iff (False, True)), Iff (True, False),
     Implies (Implies (True, False), Implies (True, False)),
     And (True, False),
     Not (Or (True, False)), Acyclic (2, 0),
     Function ((2, 0), Rel (1, 0), Rel (1, 1)),
     Functional ((2, 1), Rel (1, 0), Rel (1, 1)),
     TotalOrdering ((2, 2), Rel (1, 0), Atom 0, Atom 1),
     Subset (Rel (1, 0), Univ), RelEq (Rel (1, 0), Rel (1, 1)),
     IntEq (Num 1, Num 1), LT (Num 1, Num 2), LE (Num 2, Num 2),
     No None, Lone (Atom 0), One (Atom 0), Some Univ,
     False, True, FormulaReg (~1)]

  fun indexed_assigns make values =
    #2 (List.foldl (fn (value, (index, result)) =>
      (index + 1, make (index, value) :: result)) (0, []) values)
    |> rev

  val expression_problem : problem =
    {comment = "all expression forms",
     settings = [("bit_width", "5")],
     univ_card = 5,
     tuple_assigns = [],
     bounds = [],
     int_bounds = [],
     expr_assigns =
       indexed_assigns (fn (index, relation) =>
         AssignRelReg ((1, index), relation)) relation_cases @
       indexed_assigns AssignIntReg integer_cases @
       indexed_assigns AssignFormulaReg formula_cases,
     formula =
       All
         ([DeclOne ((1, 30), Univ)],
          Exist
            ([DeclSet ((1, 31), Univ)],
             And
               (Subset (Var (1, 30), Var (1, 31)),
                Implies (Some (Var (1, 31)), FormulaReg 0))))}

  fun simple_problem comment formula : problem =
    {comment = comment, settings = [], univ_card = 2,
     tuple_assigns = [], bounds = [], int_bounds = [], expr_assigns = [],
     formula = formula}

  val multi_problems =
    [simple_problem "first" True,
     simple_problem "second" (And (Some Univ, Not False))]

  fun read_all path =
    let
      val stream = TextIO.openIn path
      val text = TextIO.inputAll stream
        handle error => (TextIO.closeIn stream; raise error)
      val _ = TextIO.closeIn stream
    in
      text
    end

  fun remove path = OS.FileSys.remove path handle _ => ()

  fun serialize problems =
    let
      val path = OS.FileSys.tmpName ()
      val stream = TextIO.openOut path
      val _ = write_problem stream golden_header problems
        handle error => (TextIO.closeOut stream; remove path; raise error)
      val _ = TextIO.closeOut stream
      val text = read_all path handle error => (remove path; raise error)
      val _ = remove path
    in
      text
    end

  fun golden_matches (name, problems) =
    serialize problems = read_all (OS.Path.concat ("tests", name))

  fun serializer_goldens () =
    String.isPrefix "generated by HOL4 Refute\n" (production_header ()) andalso
    List.all golden_matches
      [("forl-layout.kki", [layout_problem]),
       ("forl-expressions.kki", [expression_problem]),
       ("forl-multi.kki", multi_problems)]
in
  val _ = require_msg (check_result serializer_goldens) (fn () =>
    "FORL output differed byte-for-byte from a checked-in .kki golden")
    (fn () => ()) ()
end

val _ = tprint "Refute FORL Kodkodi transcript parser"

local
  open Refute_Forl

  fun read_all path =
    let
      val stream = TextIO.openIn (OS.Path.concat ("tests", path))
      val text = TextIO.inputAll stream
        handle error => (TextIO.closeIn stream; raise error)
      val _ = TextIO.closeIn stream
    in
      text
    end

  val first_sat_instance : raw_bound list =
    [((1, 0), [[0]]),
     ((2, 1), [[0, 1], [1, 0]]),
     ((3, ~3), [[0, 1, 2]]),
     ((1, 4), [])]

  val second_sat_instance : raw_bound list =
    [((1, 0), [[1]]),
     ((2, 1), []),
     ((3, ~3), [[2, 1, 0]]),
     ((1, 4), [[0]])]

  fun sat_transcript_parses () =
    let val (solutions, unsat) =
      parse_output (read_all "kodkodi-sat.stdout")
    in
      solutions =
        [(0, first_sat_instance), (0, second_sat_instance)] andalso
      length solutions = 2 andalso null unsat
    end

  fun unsat_transcript_parses () =
    parse_output (read_all "kodkodi-unsat.stdout") = ([], [0])

  fun mixed_batch_parses () =
    parse_output (read_all "kodkodi-batch.stdout") =
      ([(0, [((1, 0), [[1]])]), (2, [])], [1])

  fun timeout_and_error_transcripts_parse () =
    parse_output (read_all "kodkodi-timeout.stdout") = ([], []) andalso
    first_error (read_all "kodkodi-timeout.stderr") =
      "Ran out of time" andalso
    parse_output (read_all "kodkodi-error.stdout") = ([], []) andalso
    first_error (read_all "kodkodi-error.stderr") =
      "No solver was specified" andalso
    first_error "\nEXIT\n" = "" andalso
    first_error " \nError: ignored.\n" = " "

  fun malformed_instance_is_rejected () =
    let
      fun rejected text =
        (ignore (extract_instance text); false) handle SYNTAX _ => true
    in
      rejected "relations:{s0=[[A0],]}" andalso
      rejected "relations:{s0=[[A0]]} trailing output"
    end
in
  val _ = require_msg (check_result sat_transcript_parses) (fn () =>
    "Kodkodi solve-all SAT instances were parsed incorrectly")
    (fn () => ()) ()
  val _ = require_msg (check_result unsat_transcript_parses) (fn () =>
    "Kodkodi UNSAT was parsed as SAT") (fn () => ()) ()
  val _ = require_msg (check_result mixed_batch_parses) (fn () =>
    "Kodkodi mixed batch outcomes were parsed incorrectly")
    (fn () => ()) ()
  val _ = require_msg
    (check_result timeout_and_error_transcripts_parse) (fn () =>
    "Kodkodi timeout or stderr error filtering was incorrect")
    (fn () => ()) ()
  val _ = require_msg (check_result malformed_instance_is_rejected) (fn () =>
    "an ill-formed Kodkodi instance was accepted") (fn () => ()) ()
end

val _ = tprint "Refute live Kodkodi bridge"

local
  open Refute_Forl

  fun quoted text = "\"" ^ text ^ "\""

  fun solver_settings timeout name =
    let val (_, arguments) = Refute_ForlSat.sat_solver_spec timeout name
    in
      [("solver", String.concatWith ", " (List.map quoted arguments))]
    end

  fun deadline seconds = Time.now () + Time.fromSeconds seconds

  fun unary_bound index count =
    ([((1, index), "")],
     [TupleSet [], TupleAtomSeq (count, 0)])

  val bridge_configured = is_configured ()

  fun problem comment settings count bounds formula : problem =
    {comment = comment, settings = settings, univ_card = count,
     tuple_assigns = [], bounds = bounds, int_bounds = [],
     expr_assigns = [], formula = formula}

  val mini_settings =
    if Lib.mem "MiniSat_JNI"
         (Refute_ForlSat.configured_sat_solvers false)
    then solver_settings (Time.fromSeconds 30) "MiniSat_JNI" @
      [("symmetry_breaking", "0")]
    else []

  val sat_problem =
    problem "MiniSat JNI SAT" mini_settings 1
      [unary_bound 0 1, unary_bound 1 1]
      (And
        (Or (Some (Rel (1, 0)), Some (Rel (1, 1))),
         Not (And (Some (Rel (1, 0)), Some (Rel (1, 1))))))

  val unsat_problem =
    let
      val x = Some (Rel (1, 0))
      val y = Some (Rel (1, 1))
    in
      problem "MiniSat JNI nontrivial UNSAT" mini_settings 1
        [unary_bound 0 1, unary_bound 1 1]
        (And
          (Or (x, y),
           And
             (Or (Not x, y),
              And (Or (x, Not y), Or (Not x, Not y)))))
    end

  val incremental_problem =
    problem "MiniSat JNI three solutions" mini_settings 2
      [unary_bound 0 2] (Lone (Rel (1, 0)))

  val false_problem = problem "false" mini_settings 1 [] False
  val true_problem = problem "true" mini_settings 1 [] True

  fun with_delay comment delay ({settings, univ_card, tuple_assigns,
      bounds, int_bounds, expr_assigns, formula, ...} : problem) : problem =
    {comment = comment, settings = settings @ [("delay", delay)],
     univ_card = univ_card, tuple_assigns = tuple_assigns,
     bounds = bounds, int_bounds = int_bounds, expr_assigns = expr_assigns,
     formula = formula}

  fun solver_surface_is_correct () =
    let val solvers = Refute_ForlSat.configured_sat_solvers false
    in
      Lib.mem "MiniSat_JNI" solvers andalso
      not (Lib.mem "Lingeling_JNI" solvers) andalso
      not (Lib.mem "CryptoMiniSat_JNI" solvers) andalso
      Refute_ForlSat.smart_sat_solver_name false = "SAT4J"
    end

  fun native_preflight () =
    let
      val sat = solve_any_problem true false (deadline 30) 1 1
        [sat_problem]
      val unsat = solve_any_problem true false (deadline 30) 1 1
        [unsat_problem]
    in
      (case sat of
           Normal ([(0, _)], [], "") => true
         | _ => false) andalso
      (case unsat of
           Normal ([], [0], "") => true
         | _ => false)
    end

  fun incremental_preflight () =
    case solve_any_problem true false (deadline 30) 1 3
        [incremental_problem] of
        Normal (solutions, unsat, "") =>
          length solutions = 3 andalso
          List.all (fn (index, _) => index = 0) solutions andalso
          null unsat
      | _ => false

  fun batching_short_circuits_and_cache () =
    let
      val first =
        [false_problem, with_delay "first" "1" sat_problem,
         false_problem]
      val equivalent =
        [false_problem, with_delay "cached" "999" sat_problem,
         false_problem]
      val solved = solve_any_problem false false (deadline 30) 1 1 first
      val cached = solve_any_problem false false
        (Time.now () - Time.fromSeconds 1) 1 1 equivalent
      val true_short_circuit = solve_any_problem true false (deadline 30)
        1 1 [false_problem, true_problem, sat_problem]
      fun expected (Normal ([(1, _)], [0, 2], "")) = true
        | expected _ = false
    in
      expected solved andalso expected cached andalso
      expected true_short_circuit
    end

  datatype test_rep =
    TestFormula
  | TestAtom of int
  | TestStruct of test_rep list
  | TestVect of int * test_rep
  | TestFunc of test_rep * test_rep

  fun rep_shape TestFormula = [2]
    | rep_shape (TestAtom cardinality) = [cardinality]
    | rep_shape (TestStruct reps) = List.concat (List.map rep_shape reps)
    | rep_shape (TestVect (count, rep)) =
        List.concat (List.tabulate (count, fn _ => rep_shape rep))
    | rep_shape (TestFunc (domain, range)) =
        List.concat
          (List.tabulate
            (List.foldl op* 1 (rep_shape domain), fn _ => rep_shape range))

  val a1 = TestAtom 1
  val a2 = TestAtom 2
  val a3 = TestAtom 3
  val a4 = TestAtom 4
  val a6 = TestAtom 6
  val a16 = TestAtom 16

  (* The first two upstream conversions simplify to False before launch.
     The remaining 22 are represented directly as finite Kodkod
     bijections between the Formula/Atom/Struct/Vect/Func layouts. *)
  val conversion_tests =
    [("rep_conversion_formula_formula", NONE),
     ("rep_conversion_atom_atom", NONE),
     ("rep_conversion_struct_struct_1",
      SOME (TestStruct [a4, a6], TestStruct [a4, a6])),
     ("rep_conversion_struct_struct_2",
      SOME (TestStruct [a4, a6], TestStruct [a4, TestStruct [a2, a3]])),
     ("rep_conversion_struct_struct_3",
      SOME (TestStruct [a4, TestStruct [a2, a3]], TestStruct [a4, a6])),
     ("rep_conversion_vect_vect_1",
      SOME (TestVect (2, TestStruct [a2, a2]), TestVect (2, a4))),
     ("rep_conversion_vect_vect_2",
      SOME (TestVect (2, a4), TestVect (2, TestStruct [a2, a2]))),
     ("rep_conversion_vect_vect_3",
      SOME (TestVect (2, TestVect (2, a2)), TestVect (2, a4))),
     ("rep_conversion_vect_vect_4",
      SOME (TestVect (2, a4), TestVect (2, TestVect (2, a2)))),
     ("rep_conversion_func_func_1",
      SOME (TestFunc (a2, a6), TestFunc (a2, TestStruct [a2, a3]))),
     ("rep_conversion_func_func_2",
      SOME (TestFunc (a2, TestStruct [a2, a3]), TestFunc (a2, a6))),
     ("rep_conversion_atom_formula_atom", SOME (a2, TestFormula)),
     ("rep_conversion_atom_struct_atom1",
      SOME (a6, TestStruct [a3, a2])),
     ("rep_conversion_atom_struct_atom_2",
      SOME (TestAtom 24, TestStruct [TestStruct [a3, a4], a2])),
     ("rep_conversion_atom_vect_func_atom_1",
      SOME (TestFunc (a4, a2), TestVect (4, a2))),
     ("rep_conversion_atom_vect_func_atom_2",
      SOME (TestFunc (a4, a2), TestVect (4, a2))),
     ("rep_conversion_atom_vect_func_atom_3",
      SOME (TestFunc (a4, TestFormula), TestVect (4, a2))),
     ("rep_conversion_atom_func_vect_atom_1",
      SOME (TestVect (4, a2), TestFunc (a4, a2))),
     ("rep_conversion_atom_func_vect_atom_2",
      SOME (TestVect (4, a2), TestFunc (a4, a2))),
     ("rep_conversion_atom_func_vect_atom_3",
      SOME (TestVect (4, a2), TestFunc (a4, TestFormula))),
     ("rep_conversion_atom_func_vect_atom_5",
      SOME (TestVect (1, a16), TestFunc (a1, a16))),
     ("rep_conversion_atom_vect_atom",
      SOME (TestAtom 36, TestVect (2, TestStruct [a2, a3]))),
     ("rep_conversion_atom_func_atom",
      SOME (TestAtom 36, TestFunc (a2, TestStruct [a2, a3]))),
     ("rep_conversion_struct_atom1_1",
      SOME (a1, TestStruct [a1, a1]))]

  fun tuple_set_product [] = raise Fail "empty representation shape"
    | tuple_set_product [cardinality] = TupleAtomSeq (cardinality, 0)
    | tuple_set_product (cardinality :: cardinalities) =
        TupleProduct
          (TupleAtomSeq (cardinality, 0),
           tuple_set_product cardinalities)

  fun digits radices number =
    let
      fun calculate [] _ values = values
        | calculate (radix :: rest) value values =
            calculate rest (value div radix) ((value mod radix) :: values)
    in
      calculate (rev radices) number []
    end

  fun variable_tuple start shape =
    let
      val (relation, _) = List.foldl (fn (_, (prior, index)) =>
        (case prior of
             NONE => (SOME (Var (1, index)), index - 1)
           | SOME value =>
               (SOME (Product (value, Var (1, index))), index - 1)))
        (NONE, start) shape
    in
      valOf relation
    end

  fun declarations start shape =
    List.map (fn (offset, cardinality) =>
      DeclOne ((1, start - offset), AtomSeq (cardinality, 0)))
      (ListPair.zip (Portable.upto 0 (length shape - 1), shape))

  fun mapping_tuples shape =
    let val cardinality = List.foldl op* 1 shape
    in
      List.tabulate (cardinality, fn index =>
        Tuple (digits shape index @ [index]))
    end

  val sat4j_settings =
    solver_settings (Time.fromSeconds 60)
      (Refute_ForlSat.smart_sat_solver_name false)

  fun conversion_problem (name, NONE) =
        problem name sat4j_settings 2 [] False
    | conversion_problem (name, SOME (old_rep, new_rep)) =
        let
          val old_shape = rep_shape old_rep
          val new_shape = rep_shape new_rep
          val cardinality = List.foldl op* 1 old_shape
          val _ =
            if cardinality = List.foldl op* 1 new_shape then ()
            else raise Fail (name ^ ": representation cardinality mismatch")
          val old_arity = length old_shape
          val new_arity = length new_shape
          val source = Rel (old_arity, 0)
          val old_mapping = Rel (old_arity + 1, 1)
          val new_mapping = Rel (new_arity + 1, 2)
          val old_result_start = ~1
          val old_source_start = old_result_start - old_arity
          val new_start = old_source_start - old_arity
          val index = new_start - new_arity
          val old_result = variable_tuple old_result_start old_shape
          val old_source = variable_tuple old_source_start old_shape
          val new_value = variable_tuple new_start new_shape
          val index_value = Var (1, index)
          val body =
            And
              (RelEq (old_source, source),
               And
                 (Subset (Product (old_source, index_value), old_mapping),
                  And
                    (Subset (Product (new_value, index_value), new_mapping),
                     Subset
                       (Product (old_result, index_value), old_mapping))))
          val round_trip =
            Comprehension
              (declarations old_result_start old_shape,
               Exist
                 (declarations old_source_start old_shape @
                  declarations new_start new_shape @
                  [DeclOne ((1, index), AtomSeq (cardinality, 0))],
                  body))
          val bounds =
            [([((old_arity, 0), "source representation")],
              [TupleSet [], tuple_set_product old_shape]),
             ([((old_arity + 1, 1), "old representation index")],
              [TupleSet (mapping_tuples old_shape)]),
             ([((new_arity + 1, 2), "new representation index")],
              [TupleSet (mapping_tuples new_shape)])]
        in
          problem name sat4j_settings cardinality bounds
            (And (One source, Not (RelEq (round_trip, source))))
        end

  val conversion_problems = List.map conversion_problem conversion_tests

  fun conversion_round_trips () =
    case solve_any_problem true false (deadline 60) 1 1
        conversion_problems of
        Normal ([], unsat, "") =>
          unsat = Portable.upto 0 (length conversion_tests - 1)
      | _ => false

  val _ =
    if bridge_configured then ()
    else print "(Kodkodi not configured, live bridge tests skipped.)\n"
in
  val _ =
    if bridge_configured then
      require_msg (check_result solver_surface_is_correct) (fn () =>
        "Kodkodi SAT solver availability did not match native artifacts")
        (fn () => ()) ()
    else ()
  val _ =
    if bridge_configured then
      require_msg (check_result native_preflight) (fn () =>
        "MiniSat JNI failed the SAT/nontrivial-UNSAT preflight")
        (fn () => ()) ()
    else ()
  val _ =
    if bridge_configured then
      require_msg (check_result incremental_preflight) (fn () =>
        "MiniSat JNI failed three-solution incremental solving")
        (fn () => ()) ()
    else ()
  val _ =
    if bridge_configured then
      require_msg (check_result batching_short_circuits_and_cache) (fn () =>
        "Kodkodi batching, short-circuiting, reindexing, or cache failed")
        (fn () => ()) ()
    else ()
  val _ =
    if bridge_configured then
      require_msg (check_result conversion_round_trips) (fn () =>
        "Kodkodi accepted a negated representation-conversion identity")
        (fn () => ()) ()
    else ()
end

val _ = tprint "Refute unified PRNG"

val pinned_rand_stream = [423, 509, 648, 382, 795]

fun sml_rand_stream count bound seed =
  let
    fun loop 0 _ values = rev values
      | loop remaining state values =
          let
            val (value, next) = rand_below (IntInf.fromInt bound) state
          in
            loop (remaining - 1) next (IntInf.toInt value :: values)
          end
  in
    loop count seed []
  end

fun evaluated_rand_stream conversion count bound seed =
  let
    val bound_tm = numSyntax.term_of_int bound
    fun loop 0 _ values = rev values
      | loop remaining state values =
          let
            val application = Term.list_mk_comb
              (``rand_below``, [bound_tm, state])
            val (value, next) =
              pairSyntax.dest_pair (rhs_of (conversion application))
            val value_int = Arbnum.toInt (numSyntax.dest_numeral value)
          in
            loop (remaining - 1) next (value_int :: values)
          end
  in
    loop count (numSyntax.term_of_int seed) []
  end

fun hol_rand_stream count bound seed =
  evaluated_rand_stream computeLib.EVAL_CONV count bound seed

fun cv_pinned_rand_stream () =
  let
    val term =
      ``let (x1, s1) = rand_below 1000 1;
             (x2, s2) = rand_below 1000 s1;
             (x3, s3) = rand_below 1000 s2;
             (x4, s4) = rand_below 1000 s3;
             (x5, s5) = rand_below 1000 s4
        in [x1; x2; x3; x4; x5]``
    val (values, _) = listSyntax.dest_list (rhs_of (cv_eval term))
  in
    List.map (Arbnum.toInt o numSyntax.dest_numeral) values
  end

fun prng_pin_works () =
  sml_rand_stream 5 1000 1 = pinned_rand_stream andalso
  hol_rand_stream 5 1000 1 = pinned_rand_stream andalso
  cv_pinned_rand_stream () = pinned_rand_stream

val _ = require_msg (check_result prng_pin_works) (fn () =>
  "HOL, SML, and cv PRNG streams did not match the pinned MMIX stream")
  (fn () => ()) ()

val _ = tprint "Refute cv build-time generators"

fun cv_rhs tm = rhs_of (cv_eval tm)

val same_terms = boolSyntax.tml_eq

fun compute_exhaustive ty size =
  case enumerate ty of
      SOME values => values
    | NONE =>
        let
          val values = ref []
          val _ = exhaustive_values (spec_of ty) size (fn value =>
            (values := value :: !values; Continue))
        in
          rev (!values)
        end

fun cv_exhaustive_agrees ty size application =
  let
    val (actual, _) = listSyntax.dest_list (cv_rhs application)
  in
    same_terms (compute_exhaustive ty size) actual
  end

fun num_term_of_intinf value =
  numSyntax.mk_numeral (Arbnum.fromLargeInt value)

fun cv_random_agrees ty size seed application =
  let
    val (expected_value, expected_state) = random_term ty size seed
    val (actual_value, actual_state) =
      pairSyntax.dest_pair (cv_rhs application)
  in
    Term.aconv expected_value actual_value andalso
    Term.aconv (num_term_of_intinf expected_state) actual_state
  end

fun cv_word64_draw_uses_two_halves () =
  let
    val (hi, state1) = rand_below 4294967296 1
    val (lo, state2) = rand_below 4294967296 state1
    val joined = hi * 4294967296 + lo
    val expected = wordsSyntax.mk_wordi
      (Arbnum.fromString (IntInf.toString joined), 64)
    val (actual, actual_state) =
      pairSyntax.dest_pair (cv_rhs ``refute_cv_rnd_word64 3 1``)
  in
    Term.aconv expected actual andalso
    Term.aconv (num_term_of_intinf state2) actual_state
  end

fun cv_generators_agree () =
  cv_exhaustive_agrees ``:bool`` 0 ``refute_cv_exh_bool 0`` andalso
  cv_exhaustive_agrees ``:word16`` 3 ``refute_cv_exh_word16 3`` andalso
  cv_exhaustive_agrees ``:num # num`` 2
    ``refute_cv_exh_num_pair 2`` andalso
  cv_exhaustive_agrees ``:num list`` 3
    ``refute_cv_exh_num_list 3`` andalso
  cv_random_agrees ``:refute$rf3`` 3 1 ``refute_cv_rnd_rf3 3 1`` andalso
  cv_random_agrees ``:word32`` 3 1 ``refute_cv_rnd_word32 3 1`` andalso
  cv_word64_draw_uses_two_halves () andalso
  cv_random_agrees ``:num # num`` 3 1
    ``refute_cv_rnd_num_pair 3 1`` andalso
  cv_random_agrees ``:num list`` 3 1
    ``refute_cv_rnd_num_list 3 1`` andalso
  cv_random_agrees ``:string`` 2 1 ``refute_cv_rnd_string 2 1``

val _ = require_msg (check_result cv_generators_agree) (fn () =>
  "a build-time cv generator disagreed with the compute substrate")
  (fn () => ()) ()

val _ = tprint "Refute core configuration"

fun same_term_option NONE NONE = true
  | same_term_option (SOME left) (SOME right) = Term.aconv left right
  | same_term_option _ _ = false

fun same_term_assignments left right =
  Lib.list_eq
    (fn (left_term, left_values) => fn (right_term, right_values) =>
      same_term_option left_term right_term andalso
      left_values = right_values)
    left right

fun same_bool_term_assignments left right =
  Lib.list_eq
    (fn (left_term, left_value) => fn (right_term, right_value) =>
      same_term_option left_term right_term andalso
      left_value = right_value)
    left right

fun same_terms left right = Lib.list_eq Term.aconv left right

fun same_optional_terms NONE NONE = true
  | same_optional_terms (SOME left) (SOME right) = same_terms left right
  | same_optional_terms _ _ = false

fun same_mf (left : mf_config) (right : mf_config) =
  #card left = #card right andalso
  same_term_assignments (#max left) (#max right) andalso
  #mono left = #mono right andalso
  same_bool_term_assignments (#wf left) (#wf right) andalso
  #sat_solver left = #sat_solver right andalso
  #batch_size left = #batch_size right andalso
  #falsify left = #falsify right andalso
  #user_axioms left = #user_axioms right andalso
  #destroy_constrs left = #destroy_constrs right andalso
  #total_consts left = #total_consts right andalso
  #peephole_optim left = #peephole_optim right andalso
  #datatype_sym_break left = #datatype_sym_break right andalso
  #kodkod_sym_break left = #kodkod_sym_break right andalso
  #max_potential left = #max_potential right andalso
  #max_genuine left = #max_genuine right andalso
  #atoms left = #atoms right andalso
  same_term_assignments (#format left) (#format right) andalso
  #show_types left = #show_types right andalso
  #show_skolems left = #show_skolems right andalso
  #show_consts left = #show_consts right andalso
  #debug left = #debug right andalso
  #overlord left = #overlord right andalso
  #max_threads left = #max_threads right andalso
  Real.== (#tac_timeout left, #tac_timeout right) andalso
  #specialize left = #specialize right andalso
  #box left = #box right andalso
  #binary_ints left = #binary_ints right andalso
  #bits left = #bits right andalso
  #star_linear_preds left = #star_linear_preds right andalso
  same_term_assignments (#iter left) (#iter right) andalso
  #bisim_depth left = #bisim_depth right andalso
  #finitize left = #finitize right andalso
  same_terms (#whack left) (#whack right) andalso
  same_optional_terms (#need left) (#need right)

fun size_update_is_local () =
  let
    val updated = upd_size 5 default_config
    val original = #qc default_config
    val after = #qc updated
  in
    #size after = 5 andalso
    #iterations after = #iterations original andalso
    #depth after = #depth original andalso
    #finite_types after = #finite_types original andalso
    #finite_type_size after = #finite_type_size original andalso
    #default_type after = #default_type original andalso
    #substrate after = #substrate original andalso
    #allow_function_inversion after =
      #allow_function_inversion original andalso
    #use_subtype after = #use_subtype original andalso
    #seed after = #seed original andalso
    #smart_quantifier after = #smart_quantifier original andalso
    #optimise_equality after = #optimise_equality original andalso
    Real.== (#timeout updated, #timeout default_config) andalso
    #backends updated = #backends default_config andalso
    #sequential updated = #sequential default_config andalso
    #genuine_only updated = #genuine_only default_config andalso
    #abort_potential updated = #abort_potential default_config andalso
    #no_assms updated = #no_assms default_config andalso
    null (#evals updated) andalso
    #expect updated = #expect default_config andalso
    #max_counterexamples updated = #max_counterexamples default_config andalso
    #tag updated = #tag default_config andalso
    same_mf (#mf updated) (#mf default_config)
  end

val _ = require_msg (check_result size_update_is_local) (fn () =>
  "upd_size changed a field other than qc.size") (fn () => ()) ()

fun mf_update_is_local () =
  let
    val base = upd_show_types true
      (upd_size 6 (upd_timeout 7.0 default_config))
    val updated = upd_sat_solver "selftest-solver" base
    val restored = upd_sat_solver (#sat_solver (#mf base)) updated
  in
    #sat_solver (#mf updated) = "selftest-solver" andalso
    same_mf (#mf restored) (#mf base) andalso
    Real.== (#timeout updated, #timeout base) andalso
    #backends updated = #backends base andalso
    #sequential updated = #sequential base andalso
    #genuine_only updated = #genuine_only base andalso
    #abort_potential updated = #abort_potential base andalso
    #no_assms updated = #no_assms base andalso
    same_terms (#evals updated) (#evals base) andalso
    #expect updated = #expect base andalso
    #max_counterexamples updated = #max_counterexamples base andalso
    #tag updated = #tag base andalso
    #qc updated = #qc base
  end

val _ = require_msg (check_result mf_update_is_local) (fn () =>
  "upd_sat_solver changed a field other than mf.sat_solver")
  (fn () => ()) ()

fun m4_guard_is_pinned (field, testfn) = shouldfail {
  checkexn = check_HOL_ERRexn
    (fn (_, _, message) =>
      message = field ^ ": not implemented until M4"),
  printarg = K (field ^ " M4 guard"),
  printresult = K "<config>",
  testfn = testfn
} ()

val _ = List.app m4_guard_is_pinned
  [("specialize", fn () =>
      Refute.upd_specialize true Refute.default_config),
   ("max_potential", fn () =>
      Refute.upd_max_potential 2 Refute.default_config),
   ("max_genuine", fn () =>
      Refute.upd_max_genuine 2 Refute.default_config)]

val _ = tprint "Refute core backend registry"

fun dummy_backend name weight : backend =
  { name = name,
    weight = weight,
    configured = fn () => true,
    requires = ExecutableGoal,
    run = fn _ => fn _ => Unknown [] }

val registry_alpha = dummy_backend "refute-core-alpha" (~97)
val registry_beta = dummy_backend "refute-core-beta" (~98)
val registry_alpha_replacement = dummy_backend "refute-core-alpha" (~96)

val public_any_goal_backend : Refute.backend =
  { name = "refute-public-any-goal",
    weight = ~95,
    configured = fn () => false,
    requires = Refute.AnyGoal,
    run = fn _ => fn _ => Unknown [] }

val _ = register_backend registry_alpha
val _ = register_backend registry_beta
val _ = register_backend registry_alpha_replacement

fun core_backend_names () =
  map #name (List.filter (fn backend =>
    #name backend = "refute-core-alpha" orelse
    #name backend = "refute-core-beta") (registered_backends ()))

val _ = require_msg
  (check_result (fn names => names =
    ["refute-core-beta", "refute-core-alpha"]))
  (fn names => "unexpected registry order: " ^ String.concatWith ", " names)
  core_backend_names ()

val _ = tprint "Refute core silent report"

val report_cex : counterexample =
  { backend = "selftest",
    substrate = "compute",
    certainty = Genuine,
    bindings = [(``x : num``, ``0``)],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [("size", 3), ("card", 2), ("tests", 412), ("msec", 400)] }

fun silent_report () =
  let
    val prior = Feedback.current_trace "Refute"
    val _ = Feedback.set_trace "Refute" 0
    val _ = report_outcome default_config (Counterexample [report_cex])
    val _ = Feedback.set_trace "Refute" prior
  in
    true
  end

val _ = require_msg (check_result silent_report) (fn () =>
  "reporting failed at trace level zero") (fn () => ()) ()

fun counterexample_report_has_one_header () =
  String.isPrefix
    ("Refute found a counterexample (backend: selftest, substrate: " ^
     "compute, size 3, 0.4s):")
    (format_outcome default_config (Counterexample [report_cex]))

val _ = require_msg
  (check_result counterexample_report_has_one_header) (fn () =>
  "counterexample reporting did not use the substrate line format")
  (fn () => ()) ()

val _ = tprint "Refute genuine-decisive backend racing"

fun stub_cex backend certainty : counterexample =
  { backend = backend,
    substrate = "stub",
    certainty = certainty,
    bindings = [],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [] }

val race_mutex = Mutex.mutex ()
val race_ready = ConditionVar.conditionVar ()
val race_potential_started = ref false
val race_potential_enabled = ref false
val race_genuine_enabled = ref false

fun reset_race () =
  Multithreading.synchronized "Refute race reset" race_mutex
    (fn () => race_potential_started := false)

fun mark_race_potential_started () =
  Multithreading.synchronized "Refute race potential" race_mutex
    (fn () =>
      (race_potential_started := true;
       ConditionVar.broadcast race_ready))

fun wait_for_race_potential () =
  Multithreading.synchronized "Refute race genuine" race_mutex
    (fn () =>
      let
        fun wait () =
          if !race_potential_started then ()
          else (ConditionVar.wait (race_ready, race_mutex); wait ())
      in
        wait ()
      end)

val race_potential_backend : backend =
  { name = "refute-race-mf-potential",
    weight = 50,
    configured = fn () => !race_potential_enabled,
    requires = AnyGoal,
    run = fn _ => fn _ =>
      (mark_race_potential_started ();
       Counterexample
         [stub_cex "refute-race-mf-potential"
            (Refute_Core.Potential ["stub"])]) }

val race_genuine_backend : backend =
  { name = "refute-race-qc-genuine",
    weight = 20,
    configured = fn () => !race_genuine_enabled,
    requires = ExecutableGoal,
    run = fn _ => fn _ =>
      (wait_for_race_potential ();
       OS.Process.sleep (Time.fromReal 0.05);
       Counterexample
         [stub_cex "refute-race-qc-genuine" Genuine]) }

val merge_low_enabled = ref false
val merge_high_enabled = ref false

fun potential_backend name weight enabled : backend =
  { name = name,
    weight = weight,
    configured = fn () => !enabled,
    requires = AnyGoal,
    run = fn _ => fn _ =>
      Counterexample
        [stub_cex name (Refute_Core.Potential ["stub"])] }

val merge_low_backend =
  potential_backend "refute-merge-potential-low" 10 merge_low_enabled
val merge_high_backend =
  potential_backend "refute-merge-potential-high" 60 merge_high_enabled

val _ = register_backend race_potential_backend
val _ = register_backend race_genuine_backend
val _ = register_backend merge_low_backend
val _ = register_backend merge_high_backend

fun potential_does_not_interrupt_genuine () =
  let
    val _ = reset_race ()
    val _ = race_potential_enabled := true
    val _ = race_genuine_enabled := true
    val config =
      upd_expect ExpectGenuine
        (upd_timeout 2.0
          (upd_sequential false
            (upd_backends
              (SOME ["refute-race-mf-potential",
                     "refute-race-qc-genuine"])
              default_config)))
    val captured = Exn.capture (fn () => refute config ``T``) ()
    val _ = race_potential_enabled := false
    val _ = race_genuine_enabled := false
  in
    case Exn.release captured of
        Counterexample ({backend, certainty = Genuine, ...} :: _) =>
          backend = "refute-race-qc-genuine"
      | _ => false
  end

val _ = require_msg
  (check_result potential_does_not_interrupt_genuine) (fn () =>
  "an MF-like Potential interrupted a QC Genuine result")
  (fn () => ()) ()

fun potential_merge_uses_backend_weight () =
  let
    val _ = merge_low_enabled := true
    val _ = merge_high_enabled := true
    val config =
      upd_expect ExpectPotential
        (upd_sequential true
          (upd_backends
            (SOME ["refute-merge-potential-low",
                   "refute-merge-potential-high"])
            default_config))
    val captured = Exn.capture (fn () => refute config ``T``) ()
    val _ = merge_low_enabled := false
    val _ = merge_high_enabled := false
  in
    case Exn.release captured of
        Counterexample
          ({backend, certainty = Refute_Core.Potential _, ...} :: _) =>
          backend = "refute-merge-potential-low"
      | _ => false
  end

val _ = require_msg
  (check_result potential_merge_uses_backend_weight) (fn () =>
  "Potential-only outcomes were not merged by backend weight")
  (fn () => ()) ()

val _ = tprint "Refute refined expectations"

fun expectation_accepts expectation outcome =
  ((check_expect (upd_expect expectation default_config) outcome; true)
   handle _ => false)

fun refined_expectations_hold () =
  let
    val potential = stub_cex "potential" (Refute_Core.Potential [])
    val quasi = stub_cex "quasi" (QuasiGenuine [])
    val genuine = stub_cex "genuine" Genuine
    val mixed = Counterexample [potential, quasi]
  in
    expectation_accepts ExpectCex mixed andalso
    expectation_accepts ExpectQuasiGenuine mixed andalso
    not (expectation_accepts ExpectPotential mixed) andalso
    expectation_accepts ExpectPotential (Counterexample [potential]) andalso
    expectation_accepts ExpectGenuine
      (Counterexample [potential, genuine]) andalso
    expectation_accepts ExpectNone NoCounterexample andalso
    expectation_accepts ExpectUnknown (Unknown ["stub"])
  end

val _ = require_msg (check_result refined_expectations_hold) (fn () =>
  "refined expectations did not use the best reported certainty")
  (fn () => ()) ()

val _ = tprint "Refute generator derivation"

fun check_gen name predicate ty =
  require_msg (check_result (fn () => predicate (spec_of ty)))
    (fn () => "unexpected generator specification for " ^ name)
    (fn () => ()) ()

fun is_num_kind kind (GenNum actual) = kind = actual
  | is_num_kind _ _ = false

fun datatype_info (GenDatatype info) = SOME info
  | datatype_info _ = NONE

fun has_no_generator ty =
  ((ignore (spec_of ty); false)
   handle NoGenerator (_, reason) => String.size reason > 0)

val _ = check_gen "num" (is_num_kind Num) ``:num``
val _ = check_gen "char" (is_num_kind Char) ``:char``
val _ = check_gen "word" (fn GenNum (Word 8) => true | _ => false)
  ``:bool[8]``
val _ = check_gen "function" (fn GenFun _ => true | _ => false)
  ``:num -> bool``
val _ = check_gen "rf3" (fn GenEnum values => length values = 3 | _ => false)
  ``:refute$rf3``

fun list_shape () =
  case datatype_info (spec_of ``:'a list``) of
    SOME {constrs, recursive, min_size, family} =>
      length constrs = 2 andalso recursive = [[], [false, true]] andalso
      min_size = [[], [0, 1]] andalso length family = 1
  | NONE => false

fun option_shape () =
  case datatype_info (spec_of ``:'a option``) of
    SOME {constrs, recursive, min_size, family} =>
      length constrs = 2 andalso recursive = [[], [false]] andalso
      min_size = [[], [0]] andalso length family = 1
  | NONE => false

val _ = require_msg (check_result list_shape) (fn () =>
  "list generator has an unexpected recursive shape") (fn () => ()) ()
val _ = require_msg (check_result option_shape) (fn () =>
  "option generator has an unexpected recursive shape") (fn () => ()) ()

val _ = Datatype.Datatype `rg_rose = RGLeaf | RGNode ((rg_rose) list)`
val _ = Datatype.Datatype
  `rg_tree = RGTip num | RGBin rg_tree rg_tree`
val _ = Datatype.Datatype `rg_left = RGLeft | RGToRight rg_right;
                           rg_right = RGRight rg_left`
val _ = Datatype.Datatype `rg_record = <| rg_field : num |>`
val _ = Datatype.Datatype
  `rg_stream_record = <| rg_stream_field : num; rg_stream_flag : bool |>`
val _ = Datatype.Datatype `rg_enum = RGRed | RGGreen | RGBlue`
val _ = Datatype.Datatype
  `rg_custom_matrix = RGCustomA | RGCustomB`

val rx_sum_def = TotalDefn.Define
  `rx_sum ([] : num list) = 0 /\
   rx_sum (x :: xs) = x + rx_sum xs`

val rx_sum_plus_one_def = TotalDefn.Define
  `rx_sum_plus_one xs = SUC (rx_sum xs)`

val rx_rose_def = TotalDefn.Define
  `rx_rose RGLeaf = 0 /\
   rx_rose (RGNode []) = 1 /\
   rx_rose (RGNode (child :: children)) = SUC (rx_rose child)`

val rx_pair_case_def = TotalDefn.Define
  `rx_pair_case pair =
     let (xs : num list, n) = pair
     in case xs of [] => n | h :: t => h + n`

val rx_record_def = TotalDefn.Define
  `rx_record r =
     let updated = r with rg_field := r.rg_field + 1
     in updated.rg_field`

val rx_partial_def = TotalDefn.Define
  `rx_partial RGLeaf = 10`

val rx_even_odd_def = TotalDefn.Define
  `rx_even 0 = T /\
   rx_even (SUC n) = rx_odd n /\
   rx_odd 0 = F /\
   rx_odd (SUC n) = rx_even n`

val _ = Theory.new_constant ("rx_unmapped", ``:num -> num``)

structure RefuteExtractSelftest = struct
  val result : bool option ref = ref NONE
end

val extract_compile_counter = ref 0

fun compile_extracted_with term finish =
  let
    val {source, entry} = Refute_Extract.extract_term term
    val serial = !extract_compile_counter
    val _ = extract_compile_counter := serial + 1
    val structure_name = "RefuteExtractGolden_" ^ Int.toString serial
    val program =
      "structure " ^ structure_name ^ " = struct\n" ^ source ^ "end\n" ^
      "val _ = RefuteExtractSelftest.result := SOME (" ^
      finish (structure_name ^ "." ^ entry) ^ ")\n"
    val stream = TextIO.openString program
    fun input () = TextIO.input1 stream
    fun compile () =
      if TextIO.endOfStream stream then ()
      else
        (PolyML.compiler
           (input, [PolyML.Compiler.CPOutStream (fn _ => ())]) ();
         compile ())
    val _ = RefuteExtractSelftest.result := NONE
    val _ = compile ()
    val _ = TextIO.closeIn stream
  in
    valOf (!RefuteExtractSelftest.result)
  end

fun compile_extracted term = compile_extracted_with term (fn entry => entry)

fun evaluated_bool term =
  let
    fun result_of conversion =
      #2 (boolSyntax.dest_eq (Thm.concl (conversion term)))
    val evaluated = result_of computeLib.EVAL_CONV
    val result =
      if Term.aconv evaluated boolSyntax.T orelse
         Term.aconv evaluated boolSyntax.F then evaluated
      else result_of intLib.REDUCE_CONV
  in
    Term.aconv result boolSyntax.T
  end

fun extraction_agrees term = compile_extracted term = evaluated_bool term

val _ = tprint "Refute extraction type and constant layers"

val extraction_goldens =
  [``APPEND [1; 2] [3; 4] = [1; 2; 3; 4]``,
   ``REVERSE [1; 2; 3] = [3; 2; 1]``,
   ``MAP (\n : num. n + 1) [0; 2; 5] = [1; 3; 6]``,
   ``rx_sum [1; 2; 3; 4] = 10``,
   ``rx_sum_plus_one [1; 2; 3; 4] = 11``,
   ``rx_rose (RGNode [RGNode [RGLeaf]; RGLeaf]) = 2``,
   ``rx_pair_case ([4; 9], 3) = 7``,
   ``rx_pair_case ([], 3) = 3``,
   ``rx_record <|rg_field := 8|> = 9``,
   ``rx_even 10 /\ rx_odd 7``,
   ``~rx_even 9 /\ ~rx_odd 8``,
   ``(2 : num) - 5 = 0``,
   ``17 DIV 5 = 3 /\ 17 MOD 5 = 2``,
   ``((17 : int) / 5 = 3)``,
   ``((17 : int) % 5 = 2)``,
   ``((~5 : int) / 2 = ~3)``,
   ``((~5 : int) % 2 = 1)``,
   ``((~5 : int) - 2 = ~7)``,
   ``Num (~5) = 5``,
   ``((n2w 250 : bool[8]) + n2w 10) = n2w 4``,
   ``word_xor (n2w 3 : bool[8]) (n2w 5) = n2w 6``,
   ``ORD #"A" = 65``,
   ``IMPLODE (EXPLODE "ab") = "ab"``,
   ``STRCAT "ab" "c" = "abc"``,
   ``HD "ab" = #"a"``,
   ``TL "ab" = "b"``,
   ``(I (\n : num. n + 1)) 2 = 3``,
   ``(\b : bool. b) = (\b. b)``]

fun all_extraction_goldens () =
  let
    fun check [] = true
      | check (term :: terms) =
          if extraction_agrees term then check terms
          else raise Fail ("extraction mismatch: " ^ Parse.term_to_string term)
  in
    check extraction_goldens
  end

val _ = require_msg (check_result all_extraction_goldens) (fn () =>
  "an extracted golden function disagreed with EVAL") (fn () => ()) ()

fun mutual_definition_group_is_emitted () =
  let val {source, ...} = Refute_Extract.extract_term ``rx_even 4``
  in String.isSubstring "and f_rx_odd_" source end

val _ = require_msg (check_result mutual_definition_group_is_emitted)
  (fn () => "a mutual definition was not emitted with fun/and")
  (fn () => ()) ()

fun extracted_div_zero_is_stuck () =
  compile_extracted_with ``1 DIV 0 = 0`` (fn entry =>
    "(" ^ entry ^ "; false) handle Refute_EvalSML.Stuck _ => true")

val _ = require_msg (check_result extracted_div_zero_is_stuck) (fn () =>
  "extracted DIV 0 did not raise Refute_EvalSML.Stuck")
  (fn () => ()) ()

fun extracted_missing_clause_is_match () =
  compile_extracted_with ``rx_partial (RGNode []) = 0`` (fn entry =>
    "(" ^ entry ^ "; false) handle Match => true")

val _ = require_msg (check_result extracted_missing_clause_is_match) (fn () =>
  "an extracted inexhaustive function did not raise Match")
  (fn () => ()) ()

fun unmapped_is_not_extractable () =
  ((ignore (Refute_Extract.extract_term ``rx_unmapped 0 = 0``); false)
   handle Refute_Extract.NotExtractable reasons =>
     List.exists (String.isSubstring "rx_unmapped") reasons)

val _ = require_msg (check_result unmapped_is_not_extractable) (fn () =>
  "an unmapped constant lacked a useful NotExtractable reason")
  (fn () => ()) ()

fun infinite_function_equality_is_rejected () =
  ((ignore (Refute_Extract.extract_term
      ``(f : num -> bool) = (g : num -> bool)``); false)
   handle Refute_Extract.NotExtractable reasons =>
     List.exists (String.isSubstring "non-enumerable") reasons)

val _ = require_msg
  (check_result infinite_function_equality_is_rejected) (fn () =>
  "function equality over num was extractable") (fn () => ()) ()

fun compile_extracted_tests strategy plans =
  let
    val {source, entry} =
      Refute_Extract.extract_tests default_config strategy plans
  in
    case Refute_EvalSML.compile_install source entry of
        Refute_EvalSML.Installed dispatch => dispatch
      | Refute_EvalSML.CompileError messages =>
          raise Fail (String.concat messages)
  end

fun generated_result strategy plan size draws seed =
  compile_extracted_tests strategy [plan] 1 false size draws seed

fun generated_env ({hit = SOME (environment, genuine), table, ...} :
    generated_answer) =
      SOME (List.map (fn (index, rebuild) =>
        (table_term table index, rebuild ())) environment, genuine)
  | generated_env _ = NONE

fun compute_plan_result strategy plan size draws seed =
  let
    val compiled =
      case Refute_EvalCompute.compile default_config strategy [plan] of
        Compiled test => test
      | Inapplicable reasons =>
          raise Fail (String.concatWith "; " reasons)
  in
    #run compiled
      {genuine_only = false, card = 1, size = size, draws = draws,
       ignored = []}
  end

fun generated_compute_agree strategy plan size draws seed =
  case (generated_env (generated_result strategy plan size draws seed),
        compute_plan_result strategy plan size draws seed) of
      (SOME (generated, generated_genuine),
       CexFound {env = computed, genuine = computed_genuine}) =>
        generated_genuine = computed_genuine andalso
        same_env generated computed
    | (NONE, Exhausted _) => true
    | _ => false

fun extraction_plan_checks () =
  let
    val list_plan = compile_plan default_config
      ``REVERSE (xs : num list) = xs``
    val tree_plan = compile_plan default_config
      ``(tree : rg_tree) = RGTip 0``
    val word_plan = compile_plan default_config
      ``(word : bool[8]) = 0w``
    val function_plan = compile_plan default_config
      ``(function : refute$rf2 -> refute$rf2) rf2_2 = rf2_1``
    fun both plan size =
      generated_compute_agree Exhaustive plan size 0 1 andalso
      List.all (fn seed => generated_compute_agree
        (Random {seed = IntInf.fromInt seed}) plan size 30
        (IntInf.fromInt seed)) [1, 2, 3]
  in
    both list_plan 3 andalso both tree_plan 3 andalso both word_plan 3 andalso
    both function_plan 3
  end

fun generated_stream seed count =
  let
    val first = Term.mk_var ("stream_first", ``:num``)
    val second = Term.mk_var ("stream_second", ``:num``)
    val plan = Gen (first, Gen (second, Test boolSyntax.F))
    val dispatch = compile_extracted_tests (Random {seed = seed}) [plan]
    fun loop 0 _ candidates = rev candidates
      | loop remaining state candidates =
          let
            val answer = dispatch 1 false 999 1 state
            val (environment, _) = valOf (#hit answer)
            val values = rev (List.map (fn (_, rebuild) => rebuild ())
              environment)
          in
            loop (remaining - 1) (#state answer) (values :: candidates)
          end
  in
    loop count seed []
  end

fun generated_type_stream ty size seed count =
  let
    val variable = Term.mk_var ("stream_value", ty)
    val plan = Gen (variable, Test boolSyntax.F)
    val dispatch = compile_extracted_tests (Random {seed = seed}) [plan]
    fun loop 0 _ candidates = rev candidates
      | loop remaining state candidates =
          let
            val answer = dispatch 1 false size 1 state
            val (environment, _) = valOf (#hit answer)
            val value = #2 (hd environment) ()
          in
            loop (remaining - 1) (#state answer) ([value] :: candidates)
          end
  in
    loop count seed []
  end

fun generated_stream_checks () =
  let
    val first = Term.mk_var ("stream_first", ``:num``)
    val second = Term.mk_var ("stream_second", ``:num``)
    val plan = Gen (first, Gen (second, Test boolSyntax.F))
    fun number_check seed =
      let val expected = dump_random_candidates
            {plan = plan, seed = seed, size = 999, count = 8}
      in
        ListPair.allEq (fn (left, right) => same_terms left right)
          (generated_stream seed 8, expected)
      end
    fun type_check ty size seed =
      let
        val variable = Term.mk_var ("stream_value", ty)
        val one_plan = Gen (variable, Test boolSyntax.F)
        val expected = dump_random_candidates
          {plan = one_plan, seed = seed, size = size, count = 6}
      in
        ListPair.allEq (fn (left, right) => same_terms left right)
          (generated_type_stream ty size seed 6, expected)
      end
    fun seed_checks seed =
      number_check seed andalso
      type_check ``:num list`` 4 seed andalso
      type_check ``:rg_tree`` 4 seed andalso
      type_check ``:bool[8]`` 4 seed
  in
    List.all (seed_checks o IntInf.fromInt) [1, 2, 3]
  end

fun partial_plan_checks () =
  let
    val variable = Term.mk_var ("bound", ``:num``)
    val stuck_num = ``THE (NONE : num option)``
    val stuck_bool = ``THE (NONE : bool option)``
    val bind = Bind
      (variable, stuck_num, SOME (Test boolSyntax.F), Test boolSyntax.T)
    val guard = Guard (stuck_bool, Test boolSyntax.F)
    val nested_guard =
      Guard (boolSyntax.T, Guard (stuck_bool, Test boolSyntax.F))
    val guard_after_stuck =
      Guard (stuck_bool, Guard (boolSyntax.T, Test boolSyntax.F))
    val test = Test stuck_bool
    val some_num = #1 (boolSyntax.strip_comb ``SOME (x : num)``)
    val split = Split (``THE (NONE : num option)``,
      [(some_num, [variable], Test boolSyntax.F)])
    val generated = Term.mk_var ("generated", ``:num``)
    val bound = Term.mk_var ("bound_value", ``:num``)
    val successful_bind = Gen
      (generated, Bind (bound, ``generated + 1``, NONE,
        Test ``bound_value = 0``))
    val option = Term.mk_var ("option", ``:num option``)
    val selected = Term.mk_var ("selected", ``:num``)
    val successful_split = Gen
      (option, Split (option,
        [(some_num, [selected], Test boolSyntax.F)]))
    val list = Term.mk_var ("split_list", ``:num list``)
    val list_head = Term.mk_var ("list_head", ``:num``)
    val list_tail = Term.mk_var ("list_tail", ``:num list``)
    val cons_num = #1
      (boolSyntax.strip_comb ``(1 : num) :: (rest : num list)``)
    val successful_list_split = Gen
      (list, Split (list,
        [(cons_num, [list_head, list_tail], Test boolSyntax.F)]))
    fun exhaustive plan =
      generated_compute_agree Exhaustive plan 2 0 1
    fun random plan =
      generated_compute_agree (Random {seed = 1}) plan 2 1 1
    fun check plan = exhaustive plan andalso random plan
    fun potential answer =
      case generated_env answer of
          SOME ([], false) => true
        | _ => false
    val split_answer = generated_result Exhaustive split 2 0 1
  in
    potential (generated_result Exhaustive bind 2 0 1) andalso
    potential (generated_result (Random {seed = 1}) bind 2 1 1) andalso
    check guard andalso check nested_guard andalso
    check guard_after_stuck andalso check test andalso exhaustive split andalso
    #match_failures split_answer = 1 andalso
    exhaustive successful_bind andalso exhaustive successful_split andalso
    exhaustive successful_list_split
  end

fun generated_completeness_checks () =
  let
    val boolean = Term.mk_var ("complete_bool", ``:bool``)
    val list = Term.mk_var ("incomplete_list", ``:num list``)
    val finite = generated_result Exhaustive
      (Gen (boolean, Test boolSyntax.T)) 2 0 1
    val bounded = generated_result Exhaustive
      (Gen (list, Test boolSyntax.T)) 2 0 1
  in
    #complete finite andalso not (#complete bounded)
  end

fun wide_word_extraction_checks () =
  let
    val wide = Term.mk_var ("wide", ``:word64``)
    val plan = Gen (wide, Test boolSyntax.T)
    val exhaustive_ok =
      let val {source, ...} = extract_tests default_config Exhaustive [plan]
      in String.isSubstring "IntInf.pow (2, 64)" source end
    val random_rejected =
      ((ignore (extract_tests default_config (Random {seed = 1}) [plan]);
        false)
       handle NotExtractable reasons =>
         List.exists (String.isSubstring "32-bit bound") reasons)
  in
    exhaustive_ok andalso random_rejected
  end

fun guard_scaling_checks () =
  let
    val flag = Term.mk_var ("guard_flag", ``:bool``)
    fun nest 0 = Test boolSyntax.F
      | nest n = Guard (flag, nest (n - 1))
    val plan = Gen (flag, nest 12)
    fun occurrences text source =
      let
        val text_size = String.size text
        val limit = String.size source - text_size
        fun loop index count =
          if index > limit then count
          else if String.substring (source, index, text_size) = text then
            loop (index + text_size) (count + 1)
          else
            loop (index + 1) count
      in
        if text_size = 0 then 0 else loop 0 0
      end
    fun linear strategy =
      let
        val {source, ...} = extract_tests default_config strategy [plan]
      in
        occurrences "tests := !tests + 1" source <= 2
      end
  in
    linear Exhaustive andalso linear (Random {seed = 1})
  end

fun generated_hygiene_and_retention_checks () =
  let
    val size = Term.mk_var ("size", ``:num``)
    val state = Term.mk_var ("state", ``:num``)
    val collision_plan = Gen
      (size, Gen (state, Test boolSyntax.F))
    val string = Term.mk_var ("string", ``:string``)
    val head = Term.mk_var ("head", ``:char``)
    val tail = Term.mk_var ("tail", ``:string``)
    val cons = #1 (boolSyntax.strip_comb ``#"a" :: (s : string)``)
    val string_plan = Gen
      (string, Split (string, [(cons, [head, tail], Test boolSyntax.F)]))
    val first_dispatch = compile_extracted_tests Exhaustive [collision_plan]
    val other = Term.mk_var ("other", ``:bool[8]``)
    val _ = compile_extracted_tests Exhaustive
      [Gen (other, Test boolSyntax.F)]
    val retained = first_dispatch 1 false 2 0 1
  in
    generated_compute_agree Exhaustive collision_plan 2 0 1 andalso
    generated_compute_agree Exhaustive string_plan 3 0 1 andalso
    (case generated_env retained of
       SOME (environment, true) => length environment = 2
     | _ => false)
  end

fun reconstruction_is_lazy () =
  let
    val variable = Term.mk_var ("lazy_x", ``:num list``)
    val miss = Gen (variable, Test boolSyntax.T)
    val hit = Gen (variable, Test boolSyntax.F)
    val _ = reset_reconstruction_forces ()
    val _ = generated_result Exhaustive miss 3 0 1
    val miss_forces = !reconstruction_forces
    val _ = reset_reconstruction_forces ()
    val answer = generated_result Exhaustive hit 3 0 1
    val before_force = !reconstruction_forces
    val environment = #1 (valOf (#hit answer))
    val _ = List.app (fn (_, rebuild) => ignore (rebuild ())) environment
  in
    miss_forces = 0 andalso before_force = 0 andalso
    !reconstruction_forces > 0
  end

val _ = tprint "Refute extraction generators and plans"
val _ = require_msg (check_result extraction_plan_checks) (fn () =>
  "an extracted plan outcome disagreed with compute") (fn () => ()) ()
val _ = require_msg (check_result generated_stream_checks) (fn () =>
  "an extracted random stream disagreed with compute") (fn () => ()) ()
val _ = require_msg (check_result partial_plan_checks) (fn () =>
  "an extracted plan handled partiality differently from compute")
  (fn () => ()) ()
val _ = require_msg (check_result generated_completeness_checks) (fn () =>
  "an extracted enumerator reported the wrong completeness")
  (fn () => ()) ()
val _ = require_msg (check_result wide_word_extraction_checks) (fn () =>
  "wide-word extraction overflowed or ignored the random bound")
  (fn () => ()) ()
val _ = require_msg (check_result guard_scaling_checks) (fn () =>
  "guarded plan extraction duplicated continuations")
  (fn () => ()) ()
val _ = require_msg
  (check_result generated_hygiene_and_retention_checks) (fn () =>
  "generated names, string splitting, or retained term tables failed")
  (fn () => ()) ()
val _ = require_msg (check_result reconstruction_is_lazy) (fn () =>
  "an extracted reconstruction thunk was forced before a hit")
  (fn () => ()) ()

val _ = require_msg (check_result (fn () =>
  let val {ml_type, source, ...} =
        Refute_Extract.compile_type ``:bool[8]``
  in ml_type = "IntInf.int" andalso
     String.isSubstring "refute_norm" source end)) (fn () =>
  "word type extraction did not use IntInf and modular helpers")
  (fn () => ()) ()

val _ = require_msg (check_result (fn () =>
  let val {source, ...} = Refute_Extract.compile_types
        [``:rg_left``, ``:rg_right``]
  in String.isSubstring "datatype" source andalso
     String.isSubstring "and refute_ty_" source andalso
     String.isSubstring "eq_refute_" source end)) (fn () =>
  "mutual datatype or structural equality declarations were not emitted")
  (fn () => ()) ()

val _ = require_msg (check_result (fn () =>
  case cached_spec ``:refute$rf3`` of NONE => true | SOME _ => false))
  (fn () => "generator cache was not invalidated") (fn () => ()) ()

fun rose_shape () =
  case datatype_info (spec_of ``:rg_rose``) of
    SOME {recursive, min_size, family, ...} =>
      recursive = [[], [true]] andalso min_size = [[], [1]] andalso
      length family = 1
  | NONE => false

fun mutual_shape () =
  case datatype_info (spec_of ``:rg_right``) of
    SOME {recursive, min_size, family, ...} =>
      recursive = [[true]] andalso min_size = [[1]] andalso
      length family = 2
  | NONE => false

val _ = require_msg (check_result rose_shape) (fn () =>
  "rose generator has an unexpected recursive shape") (fn () => ()) ()
val _ = require_msg (check_result mutual_shape) (fn () =>
  "mutual generator has an unexpected recursive shape") (fn () => ()) ()
val _ = check_gen "record" (fn GenDatatype _ => true | _ => false)
  ``:rg_record``
val _ = check_gen "enum" (fn GenEnum values => length values = 3 | _ => false)
  ``:rg_enum``
val _ = require_msg (check_result (fn () =>
  recursive_under_function [``:rg_rose``] ``:rg_rose -> bool``))
  (fn () => "recursive function occurrence was not detected")
  (fn () => ()) ()
val real_ty = Type.mk_thy_type {Thy = "real", Tyop = "real", Args = []}
  handle Feedback.HOL_ERR _ => ``:ind``
val _ = require_msg (check_result (fn () => has_no_generator real_ty))
  (fn () => "real unexpectedly has a generator") (fn () => ()) ()
val _ = require_msg (check_result (fn () => has_no_generator ``:ind``))
  (fn () => "unknown type unexpectedly has a generator") (fn () => ()) ()

val _ = tprint "Refute enumeration and registries"

fun check_cardinality ty expected =
  require_msg (check_result (fn () => cardinality ty = expected))
    (fn () => "unexpected cardinality") (fn () => ()) ()

val _ = check_cardinality ``:bool`` (SOME 2)
val _ = check_cardinality ``:refute$rf3`` (SOME 3)
val _ = check_cardinality ``:bool[8]`` (SOME 256)
val _ = check_cardinality ``:refute$rf2 # bool`` (SOME 4)
val _ = check_cardinality ``:bool -> bool`` (SOME 4)
val _ = check_cardinality ``:bool[8] -> bool`` NONE
val _ = check_cardinality ``:num`` NONE

fun is_enumerated ty count =
  case enumerate ty of
    SOME values => length values = count
  | NONE => false

val _ = require_msg (check_result (fn () => is_enumerated ``:bool`` 2))
  (fn () => "bool was not completely enumerated") (fn () => ()) ()
val _ = require_msg (check_result (fn () =>
  is_enumerated ``:refute$rf3`` 3))
  (fn () => "rf3 was not completely enumerated") (fn () => ()) ()
val _ = require_msg (check_result (fn () =>
  is_enumerated ``:refute$rf2 # bool`` 4))
  (fn () => "product was not completely enumerated") (fn () => ()) ()

fun eval_rhs tm =
  let
    val theorem = computeLib.CBV_CONV (!computeLib.the_compset) tm
  in
    #2 (boolSyntax.dest_eq (Thm.concl theorem))
  end

fun function_graphs_work () =
  case (enumerate ``:bool -> refute$rf2``, enumerate ``:refute$rf2``) of
    (SOME graphs, SOME values) =>
      length graphs = 4 andalso
      List.all (fn graph =>
        List.all (fn input =>
          List.exists (fn value =>
            Term.aconv (eval_rhs (Term.mk_comb (graph, input))) value)
            values) [boolSyntax.T, boolSyntax.F]) graphs
  | _ => false

val _ = require_msg (check_result function_graphs_work) (fn () =>
  "function graphs did not EVAL on both boolean inputs") (fn () => ()) ()

val empty_custom : custom_gen = {enumerate = NONE, random = NONE}
fun custom_zero_random _ state =
  let val (_, next) = rand_below 1 state
  in (``0``, next) end

val finite_custom : custom_gen =
  {enumerate = SOME (fn _ => [``0``]),
   random = SOME custom_zero_random}

fun rejects_empty_custom () =
  ((register_generator ``:ind`` empty_custom; false)
   handle Fail _ => true)

val _ = require_msg (check_result rejects_empty_custom) (fn () =>
  "an empty custom generator was accepted") (fn () => ()) ()
val _ = register_generator ``:ind`` finite_custom
val matrix_custom : custom_gen =
  {enumerate = SOME (fn _ => [``RGCustomA``, ``RGCustomB``]),
   random = SOME (fn _ => fn state =>
     let val (choice, next) = rand_below 2 state
     in
       (if choice = 0 then ``RGCustomA`` else ``RGCustomB``, next)
     end)}
val _ = register_generator ``:rg_custom_matrix`` matrix_custom
val _ = require_msg (check_result (fn () =>
  case spec_of ``:ind`` of GenCustom _ => true | _ => false))
  (fn () => "custom generator was not registered") (fn () => ()) ()

fun custom_random_threads_state () =
  let
    val (_, final) = random_value (GenCustom finite_custom)
      {budget = 1, size = 1} 7
  in
    final = rand_next 7
  end

val _ = require_msg (check_result custom_random_threads_state) (fn () =>
  "a custom random generator did not return its successor state")
  (fn () => ()) ()

val abstract_ty = ``:rg_record``
val abstract_predicate = ``\x : rg_record. T``
val abstract_constructor =
  hd (TypeBasePure.constructors_of (valOf (TypeBase.fetch abstract_ty)))
val _ = abstract_generator
  {ty = abstract_ty,
   constructors = [abstract_constructor],
   pred = SOME abstract_predicate}

fun abstract_generator_works () =
  (case spec_of abstract_ty of
     GenDatatype {constrs, family, ...} =>
       length constrs = 1 andalso family = [abstract_ty]
   | _ => false) andalso
  (case predicate_of abstract_ty of
     SOME predicate => Term.aconv predicate abstract_predicate
   | NONE => false)

val _ = require_msg (check_result abstract_generator_works) (fn () =>
  "abstract generator or predicate registry was not populated")
  (fn () => ()) ()

fun custom_generators_are_not_extracted () =
  let
    fun rejected ty =
      let val variable = Term.mk_var ("custom_value", ty)
      in
        ((ignore (extract_tests default_config Exhaustive
            [Gen (variable, Test boolSyntax.T)]); false)
         handle NotExtractable reasons =>
           List.exists (String.isPrefix
             ("custom generator registered for " ^
              Hol_pp.type_to_string ty)) reasons)
      end
  in
    rejected ``:rg_record`` andalso rejected ``:ind list``
  end

val _ = require_msg (check_result custom_generators_are_not_extracted)
  (fn () => "a custom generator escaped native closure validation")
  (fn () => ()) ()

val _ = tprint "Refute preprocessing and executability"

fun preprocessing_problem goal : problem =
  { goal = goal, assumptions = [], evals = [] }

fun preprocessed_instances instances = SOME instances

fun has_conjunction tm =
  case Lib.total boolSyntax.dest_conj tm of
      SOME _ => true
    | NONE =>
        if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            has_conjunction left orelse has_conjunction right
          end
        else
          false

fun two_way_disjunction tm =
  case Lib.total boolSyntax.dest_disj tm of
      SOME _ => true
    | NONE => false

fun bool_forall_expands () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``p /\ (!x : bool. x)``)) of
      SOME [instance] => has_conjunction (#goal instance)
    | _ => false

val _ = require_msg (check_result bool_forall_expands) (fn () =>
  "a boolean universal did not expand to a two-way conjunction")
  (fn () => ()) ()

fun explicit_forall_is_stripped () =
  case preprocessed_instances
    (preprocess (upd_finite_types false default_config)
      (preprocessing_problem
        ``!x : 'a. (f : 'a -> 'a) x = (g x : 'a)``)) of
      SOME [instance] =>
        not (boolSyntax.is_forall (#goal instance)) andalso
        length (#evals instance) = 2
    | _ => false

val _ = require_msg (check_result explicit_forall_is_stripped) (fn () =>
  "an explicit outer universal was not stripped before preprocessing")
  (fn () => ()) ()

fun rf2_exists_expands () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``?x : refute$rf2. x = rf2_1``)) of
      SOME [instance] => two_way_disjunction (#goal instance)
    | _ => false

val _ = require_msg (check_result rf2_exists_expands) (fn () =>
  "an rf2 existential did not expand to a two-way disjunction")
  (fn () => ()) ()

fun num_binder_is_not_executable () =
  not (null (instance_gate_reasons
    (preprocess default_config
      (preprocessing_problem ``q (!n : num. n = 0)``))))

val _ = require_msg (check_result num_binder_is_not_executable) (fn () =>
  "a universal over num was accepted as executable")
  (fn () => ()) ()

fun negated_exists_normalizes () =
  let
    val normalized = normalize ``~(?x : bool. x)``
    val (variables, body) = strip_outer_forall normalized
  in
    length variables = 1 andalso not (boolSyntax.is_forall body)
  end

val _ = require_msg (check_result negated_exists_normalizes) (fn () =>
  "a negated existential did not normalize and strip as a universal")
  (fn () => ()) ()

fun all_same_type ty variables =
  List.all (fn variable => Type.compare (Term.type_of variable, ty) = EQUAL)
    variables

val polymorphic_goal = ``p (x : 'a) /\ q (y : 'b)``

fun value_variable_types tm =
  List.map Term.type_of (List.filter (fn variable =>
    case Lib.total Type.dom_rng (Term.type_of variable) of
        NONE => true
      | SOME _ => false) (Term.free_vars_lr tm))

fun finite_type_instances () =
  case preprocessed_instances
    (preprocess (upd_finite_type_size 3 default_config)
      (preprocessing_problem polymorphic_goal)) of
      SOME instances =>
        length instances = 3 andalso
        List.all (fn instance =>
          all_same_type (rf_type (#card instance))
            (List.map (fn ty => Term.mk_var ("x", ty))
              (value_variable_types (#goal instance)))) instances
    | NONE => false

val _ = require_msg (check_result finite_type_instances) (fn () =>
  "finite-type monomorphization did not produce rf1 through rf3")
  (fn () => ()) ()

fun default_type_instance () =
  case preprocessed_instances
    (preprocess (upd_finite_types false default_config)
      (preprocessing_problem polymorphic_goal)) of
      SOME [instance] =>
        #card instance = 1 andalso
        all_same_type numSyntax.num
          (List.map (fn ty => Term.mk_var ("x", ty))
            (value_variable_types (#goal instance)))
    | _ => false

val _ = require_msg (check_result default_type_instance) (fn () =>
  "default-type monomorphization did not use num")
  (fn () => ()) ()

fun equation_adds_evals () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``(f : bool -> bool) x = (g x : bool)``)) of
      SOME [instance] => length (#evals instance) = 2
    | _ => false

val _ = require_msg (check_result equation_adds_evals) (fn () =>
  "an equational conclusion did not add both evaluation terms")
  (fn () => ()) ()

val _ = Theory.new_constant ("refute_task07_unmapped", ``:bool``)

fun unmapped_constant_is_not_executable () =
  case preprocess default_config
    (preprocessing_problem ``refute_task07_unmapped``) of
      [{qc_gate = SOME [reason], ...}] =>
        String.isSubstring "refute_task07_unmapped" reason
    | _ => false

val _ = require_msg
  (check_result unmapped_constant_is_not_executable) (fn () =>
  "a constant without a compute-set entry was accepted")
  (fn () => ()) ()

val nonexecutable_goal = ``q (!n : num. n = 0)``

fun qc_gate_reason_is_merged () =
  case refute_problem
    (upd_backends (SOME ["exhaustive"]) default_config)
    (preprocessing_problem nonexecutable_goal) of
      Unknown reasons =>
        reasons = ["not executable: unexpanded binder"]
    | _ => false

val _ = require_msg (check_result qc_gate_reason_is_merged) (fn () =>
  "an executability-gate reason was not preserved for QC")
  (fn () => ()) ()

val any_goal_stub_enabled = ref false
val any_goal_stub_received = ref false

val any_goal_stub : backend =
  { name = "refute-any-goal-stub",
    weight = ~99,
    configured = fn () => !any_goal_stub_enabled,
    requires = AnyGoal,
    run = fn _ => fn instances =>
      (any_goal_stub_received :=
         (not (null instances) andalso
          List.all (Option.isSome o #qc_gate) instances);
       Unknown ["received non-executable instance"]) }

val _ = register_backend any_goal_stub

fun any_goal_backend_receives_nonexecutable_instance () =
  let
    val _ = any_goal_stub_received := false
    val _ = any_goal_stub_enabled := true
    val captured = Exn.capture (fn () => refute_problem
      (upd_backends (SOME ["refute-any-goal-stub"]) default_config)
      (preprocessing_problem nonexecutable_goal)) ()
    val _ = any_goal_stub_enabled := false
  in
    case Exn.release captured of
        Unknown [reason] =>
          !any_goal_stub_received andalso
          reason = "refute-any-goal-stub: received non-executable instance"
      | _ => false
  end

val _ = require_msg
  (check_result any_goal_backend_receives_nonexecutable_instance) (fn () =>
  "an AnyGoal backend did not receive a non-executable instance")
  (fn () => ()) ()

fun qc_gate_reason_merges_with_any_goal_unknown () =
  let
    val _ = any_goal_stub_enabled := true
    val captured = Exn.capture (fn () => refute_problem
      (upd_backends
        (SOME ["exhaustive", "refute-any-goal-stub"])
        default_config)
      (preprocessing_problem nonexecutable_goal)) ()
    val _ = any_goal_stub_enabled := false
  in
    case Exn.release captured of
        Unknown reasons =>
          reasons =
            ["not executable: unexpanded binder",
             "refute-any-goal-stub: received non-executable instance"]
      | _ => false
  end

val _ = require_msg
  (check_result qc_gate_reason_merges_with_any_goal_unknown) (fn () =>
  "a QC gate reason was not merged with an AnyGoal Unknown")
  (fn () => ()) ()

val _ = tprint "Refute QC plan compiler"

fun plan_is_bind_with_fallback plan =
  case plan of
      Gen (_, Gen (_, Bind (_, _, SOME (Gen (_, Gen (_, Test _))),
        Gen (_, Test _)))) => true
    | _ => false

fun plan_is_single_split plan =
  case plan of
      Gen (_, Split (_, [(_, variables, _)])) => length variables = 1
    | _ => false

fun plan_is_generic_guard plan =
  case plan of
      Gen (_, Gen (_, Guard (_, Gen (_, Test _)))) => true
    | _ => false

fun plan_is_fmap_lookup plan =
  case plan of
      Gen (_, Gen (_, Split (_, [(_, variables, _)]))) =>
        length variables = 1
    | _ => false

fun plan_is_distinct_zip plan =
  case plan of
      Gen (_, Gen (_, Guard (_, Test _))) => true
    | _ => false

fun plan_is_naive goal plan =
  case plan of
      Gen (_, Test tested) => Term.aconv tested goal
    | _ => false

fun plan_has_abstract_guard plan =
  case plan of
      Gen (_, Guard (_, Test _)) => true
    | _ => false

val bind_goal = ``(x : num) = f (y : num) ==> r (x : num)``
val split_goal = ``(z : num option) = SOME (x : num) ==> T``
val guard_goal = ``(p : num -> bool) x ==> q (x : num)``
val fmap_lookup_goal =
  ``(m1 : num -> num option) k = SOME (v : num) ==> p m1 k v``
val distinct_zip_goal =
  ``ALL_DISTINCT (ZIP (xs : num list, ys : num list)) ==> T``
val naive_goal = ``(x : num) = 0 ==> F``
val abstract_guard_goal = ``(r : rg_record) = r``

fun check_plan predicate message goal =
  require_msg (check_result predicate) (fn plan =>
    message ^ "\n" ^ pp_plan plan)
    (fn () => compile_plan default_config goal) ()

val _ = check_plan plan_is_bind_with_fallback
  "free-variable equality did not compile to Bind with fallback" bind_goal

val _ = check_plan plan_is_single_split
  "constructor equality did not compile to a single Split branch" split_goal

val _ = check_plan plan_is_generic_guard
  "generic premise did not compile to Guard" guard_goal

val _ = check_plan plan_is_fmap_lookup
  "fmap-lookup premise did not compile to the expected Split" fmap_lookup_goal

val _ = check_plan plan_is_distinct_zip
  "distinct/zip premise did not compile to Guard" distinct_zip_goal

val _ = require_msg (check_result (plan_is_naive naive_goal)) (fn _ =>
  "smart_quantifier := false did not retain the whole goal")
  (fn () => compile_plan (upd_smart_quantifier false default_config)
    naive_goal) ()

val _ = check_plan plan_has_abstract_guard
  "abstract-generator predicate was not inserted as Guard" abstract_guard_goal

val _ = tprint "Refute QC exhaustive backend"

fun fast_substrates_precede_compute () =
  case get_substrates () of
      native :: cv :: compute :: _ =>
        #name native = "native" andalso #priority native = 10 andalso
        #name cv = "cv" andalso #priority cv = 20 andalso
        #name compute = "compute" andalso #priority compute = 30
    | _ => false

val _ = require_msg
  (check_result fast_substrates_precede_compute) (fn () =>
  "the native, cv, and compute substrates had the wrong registry order")
  (fn () => ()) ()

fun dummy_compile _ _ _ = Inapplicable ["dummy substrate"]

val seam_alpha : substrate =
  {name = "refute-seam-alpha", priority = 50, compile = dummy_compile}
val seam_beta : substrate =
  {name = "refute-seam-beta", priority = 40, compile = dummy_compile}
val seam_alpha_replacement : substrate =
  {name = "refute-seam-alpha", priority = 35, compile = dummy_compile}

val _ = register_substrate seam_alpha
val _ = register_substrate seam_beta
val _ = register_substrate seam_alpha_replacement

fun seam_registry_order () =
  map #name (List.filter (fn substrate =>
    #name substrate = "refute-seam-alpha" orelse
    #name substrate = "refute-seam-beta") (get_substrates ())) =
  ["refute-seam-alpha", "refute-seam-beta"]

val _ = require_msg (check_result seam_registry_order) (fn () =>
  "substrate registry replacement or priority ordering failed")
  (fn () => ()) ()

val public_seam : Refute.substrate =
  {name = "refute-public-seam", priority = 45, compile = dummy_compile}
val _ = Refute.register_substrate public_seam

val _ = require_msg (check_result (fn () =>
  List.exists (fn substrate => #name substrate = "refute-public-seam")
    (get_substrates ()))) (fn () =>
  "the public register_substrate re-export did not register a substrate")
  (fn () => ()) ()

fun qc_problem goal : problem = {goal = goal, assumptions = [], evals = []}

fun qc_instances config goal = preprocess config (qc_problem goal)

fun exhaustive config goal =
  let
    val instances = qc_instances config goal
    val reasons = instance_gate_reasons instances
  in
    if null reasons then strategy_run Exhaustive config instances
    else Unknown reasons
  end

fun has_binding predicate (Counterexample (cex :: _)) =
      List.exists predicate (#bindings cex)
  | has_binding _ _ = false

fun reverse_counterexample () =
  let
    val config = upd_size 3 (upd_max_counterexamples 1 default_config)
    val result = exhaustive config ``REVERSE (xs : num list) = xs``
  in
    (case result of
         Counterexample (cex :: _) => #substrate cex = "native"
       | _ => false) andalso
    has_binding (fn (_, value) =>
      case Lib.total listSyntax.dest_list value of
          SOME (values, _) => length values >= 2 andalso
            not (Term.aconv (hd values) (List.nth (values, 1)))
        | NONE => false) result
  end

val _ = require_msg (check_result reverse_counterexample) (fn () =>
  "the exhaustive backend did not find a non-palindromic list")
  (fn () => ()) ()

fun complete_bool_goal () =
  case exhaustive default_config ``T`` of
      NoCounterexample => true
    | _ => false

val _ = require_msg (check_result complete_bool_goal) (fn () =>
  "a decidable closed boolean goal was not exhausted completely")
  (fn () => ()) ()

fun stuck_split_counts_failure () =
  let
    val config = default_config
    val goal =
      ``(if THE (NONE : bool option) then SOME 0 else NONE) =
        SOME (x : num) ==> F``
    val result = exhaustive config goal
    val instances = qc_instances config goal
    val plans = List.map (fn i => compile_plan config (#goal i)) instances
    val compiled =
      case Refute_EvalCompute.compile config Exhaustive plans of
          Compiled test => test
        | Inapplicable reasons => raise Fail (String.concatWith "; " reasons)
    val _ = List.app (fn (card, size) =>
      ignore (#run compiled
        {genuine_only = false, card = card, size = size, draws = 0,
         ignored = []}))
      (schedule instances (#size (#qc config)))
  in
    (case result of Unknown _ => true | _ => false) andalso
    (case lookup_stat "match_failures" (!(#last_stats compiled)) of
        SOME failures => failures > 0
      | NONE => false)
  end

val _ = require_msg (check_result stuck_split_counts_failure) (fn () =>
  "a stuck Split scrutinee did not increment match_failures")
  (fn () => ()) ()

fun no_generator_is_compile_inapplicable () =
  let
    val variable = Term.mk_var ("r", ``:real``)
  in
    case Refute_EvalCompute.compile default_config Exhaustive
      [Gen (variable, Test boolSyntax.T)] of
        Inapplicable reasons =>
          List.exists (fn reason =>
            String.isSubstring "no generator for :real" reason andalso
            String.isSubstring "quotient type" reason) reasons
      | Compiled _ => false
  end

val _ = require_msg
  (check_result no_generator_is_compile_inapplicable) (fn () =>
  "NoGenerator was not converted to compile-time Inapplicable")
  (fn () => ()) ()

fun explicit_cv_is_available strategy =
  let
    val config = upd_substrate Cv default_config
    val instances = qc_instances config ``T``
  in
    case strategy_run strategy config instances of
        NoCounterexample => true
      | _ => false
  end

val _ = require_msg (check_result (fn () =>
  explicit_cv_is_available Exhaustive andalso
  explicit_cv_is_available (Random {seed = 1}))) (fn () =>
  "the explicit cv substrate was unavailable for a backend")
  (fn () => ()) ()

fun run_with_strategy strategy config goal =
  strategy_run strategy config (qc_instances config goal)

fun selected_substrate expected result =
  case result of
      Counterexample (cex :: _) => #substrate cex = expected
    | _ => false

val auto_ho_custom : custom_gen =
  {enumerate = SOME (fn _ =>
     [``\x : rg_enum. T``, ``\x : rg_enum. F``]),
   random = SOME (fn _ => fn state =>
     let val (choice, next) = rand_below 2 state
     in
       (if choice = 0 then ``\x : rg_enum. T``
        else ``\x : rg_enum. F``, next)
     end)}
val _ = register_generator ``:rg_enum -> bool`` auto_ho_custom

val auto_native_goal = ``REVERSE (xs : num list) = xs``
val auto_custom_goal = ``(r : rg_record) = s``
val auto_cv_goal = ``(w : word64) = 0w``
val auto_ho_goal = ``(f : rg_enum -> bool) RGRed``

fun auto_selection_works () =
  let
    val config = upd_size 3 (upd_iterations 30 default_config)
    fun runs expected goal strategy =
      selected_substrate expected
        (run_with_strategy strategy config goal)
  in
    runs "native" auto_native_goal Exhaustive andalso
    runs "native" auto_native_goal (Random {seed = 1}) andalso
    runs "compute" auto_custom_goal Exhaustive andalso
    runs "compute" auto_custom_goal (Random {seed = 1}) andalso
    runs "cv" auto_cv_goal (Random {seed = 1}) andalso
    runs "compute" auto_ho_goal Exhaustive andalso
    runs "compute" auto_ho_goal (Random {seed = 1})
  end

val _ = require_msg (check_result auto_selection_works) (fn () =>
  "Auto did not select native, cv, and compute by applicability")
  (fn () => ()) ()

fun reason_contains fragment (Unknown reasons) =
      List.exists (String.isSubstring fragment) reasons
  | reason_contains _ _ = false

fun explicit_inapplicable_is_unknown () =
  let
    fun rejected choice fragment strategy =
      let val config = upd_substrate choice default_config
      in
        reason_contains fragment
          (run_with_strategy strategy config auto_custom_goal)
      end
    fun both choice fragment =
      rejected choice fragment Exhaustive andalso
      rejected choice fragment (Random {seed = 1})
  in
    both NativeSML "custom generator registered" andalso
    both Cv "abstract generator registered"
  end

val _ = require_msg
  (check_result explicit_inapplicable_is_unknown) (fn () =>
  "an explicit inapplicable substrate fell back or lost its reason")
  (fn () => ()) ()

fun capture_refute_messages level action =
  let
    val chunks = ref ([] : string list)
    fun output text = chunks := text :: !chunks
    val result = Lib.with_flag (Feedback.MESG_outstream, output)
      (Feedback.with_traces [("Refute", level)] action) ()
  in
    (result, String.concat (rev (!chunks)))
  end

fun trace_level_two_reports_qc_gate () =
  let
    val config = upd_backends (SOME ["exhaustive"]) default_config
    val (_, output) = capture_refute_messages 2 (fn () =>
      ignore (refute_problem config
        (preprocessing_problem nonexecutable_goal)))
  in
    String.isSubstring
      "QC backends excluded: not executable: unexpanded binder" output
  end

val _ = require_msg
  (check_result trace_level_two_reports_qc_gate) (fn () =>
  "trace level 2 omitted the executability-gate reason")
  (fn () => ()) ()

fun trace_level_two_reports_selection () =
  let
    val config = upd_size 2 default_config
    val (_, output) = capture_refute_messages 2 (fn () =>
      ignore (run_with_strategy Exhaustive config auto_custom_goal))
  in
    String.isSubstring
      "native is inapplicable: custom generator registered" output andalso
    String.isSubstring
      "cv is inapplicable: cv: :rg_record - abstract generator" output andalso
    String.isSubstring "selected compute" output andalso
    String.isSubstring "Refute schedule entry" output
  end

val _ = require_msg
  (check_result trace_level_two_reports_selection) (fn () =>
  "trace level 2 omitted substrate skip reasons or entry timing")
  (fn () => ()) ()

fun trace_level_three_dumps_generated_programs () =
  let
    val native_config = upd_size 2 default_config
    val (_, native_output) = capture_refute_messages 3 (fn () =>
      ignore (run_with_strategy Exhaustive native_config
        auto_native_goal))
    val cv_config = upd_substrate Cv (upd_size 1 default_config)
    val (_, cv_output) = capture_refute_messages 3 (fn () =>
      ignore (run_with_strategy Exhaustive cv_config ``(b : bool)``))
  in
    String.isSubstring "Refute plan (card" native_output andalso
    String.isSubstring "Refute generated SML" native_output andalso
    String.isSubstring "Refute synthesized HOL loop" cv_output
  end

val _ = require_msg
  (check_result trace_level_three_dumps_generated_programs) (fn () =>
  "trace level 3 omitted a generated plan or program dump")
  (fn () => ()) ()

fun trace_level_four_is_compute_only () =
  let
    val compute_config = upd_substrate Compute (upd_size 1 default_config)
    val (_, output) = capture_refute_messages 4 (fn () =>
      ignore (run_with_strategy Exhaustive compute_config ``(b : bool)``))
  in
    String.isSubstring "Refute compute candidate:" output
  end

val _ = require_msg (check_result trace_level_four_is_compute_only) (fn () =>
  "trace level 4 omitted compute candidates") (fn () => ()) ()

fun gave_up_reason_is_plumbed () =
  let
    val original = valOf (List.find (fn substrate =>
      #name substrate = "compute") (get_substrates ()))
    val last_stats = ref []
    val test : compiled_test =
      {run = fn _ => GaveUp "selftest gave up", close = fn () => (),
       max_chunk = NONE, last_stats = last_stats}
    val replacement : substrate =
      {name = "compute", priority = 30,
       compile = fn _ => fn _ => fn _ => Compiled test}
    val config = upd_substrate Compute default_config
    val instances = qc_instances config ``T``
    val _ = register_substrate replacement
    val result = strategy_run Exhaustive config instances
      handle e => (register_substrate original; raise e)
    val _ = register_substrate original
  in
    case result of
        Unknown reasons => List.exists (fn reason =>
          reason = "selftest gave up") reasons
      | _ => false
  end

val _ = require_msg (check_result gave_up_reason_is_plumbed) (fn () =>
  "a substrate GaveUp reason was not merged into Unknown")
  (fn () => ()) ()

fun smart_pruning_works () =
  let
    val base = upd_size 3 default_config
    val smart = exhaustive (upd_smart_quantifier true base)
      ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``
    val naive = exhaustive (upd_smart_quantifier false base)
      ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``
  in
    (case smart of Counterexample _ => true | _ => false) andalso
    (case naive of Unknown _ => true | _ => false)
  end

val _ = require_msg (check_result smart_pruning_works) (fn () =>
  "smart premise pruning did not improve the bounded exhaustive search")
  (fn () => ()) ()

fun update_witness () =
  let
    val result = exhaustive (upd_size 2 default_config)
      ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
        f rf2_2 = rf2_2 ==> F``
  in
    has_binding (fn (_, value) =>
      not (null (#1 (combinSyntax.strip_update value)))) result
  end

val _ = require_msg (check_result update_witness) (fn () =>
  "a function-variable counterexample was not an UPDATE-chain witness")
  (fn () => ()) ()

val _ = tprint "Refute QC random backend"

fun random config goal =
  let
    val instances = qc_instances config goal
    val reasons = instance_gate_reasons instances
  in
    if null reasons then
      strategy_run (Random {seed = strategy_seed config}) config instances
    else Unknown reasons
  end

val same_bindings = same_env

fun same_random_outcome (Counterexample (left :: _))
      (Counterexample (right :: _)) =
      #backend left = #backend right andalso
      #substrate left = #substrate right andalso
      #certainty left = #certainty right andalso
      same_bindings (#bindings left) (#bindings right) andalso
      List.filter (fn (name, _) => name <> "msec") (#stats left) =
      List.filter (fn (name, _) => name <> "msec") (#stats right)
  | same_random_outcome NoCounterexample NoCounterexample = true
  | same_random_outcome (Unknown left) (Unknown right) = left = right
  | same_random_outcome _ _ = false

val random_config = upd_iterations 50
  (upd_size 4 (upd_seed (SOME 1) default_config))

fun random_is_registered () =
  case lookup_backend "random" of
      SOME backend => #weight backend = 30
    | NONE => false

fun random_reverse_counterexample () =
  case random random_config ``REVERSE (xs : num list) = xs`` of
      Counterexample (cex :: _) =>
        #substrate cex = "native" andalso
        Option.isSome (lookup_stat "msec" (#stats cex))
    | _ => false

fun random_arithmetic_counterexample () =
  case random random_config ``(x : num) - y + y = x`` of
      Counterexample _ => true
    | _ => false

fun random_seed_is_reproducible () =
  let
    val goal = ``REVERSE (xs : num list) = xs``
    val prior_seed = !session_seed
    val left = random random_config goal
    val right = random random_config goal
  in
    same_random_outcome left right andalso !session_seed = prior_seed
  end

fun random_collects_requested_counterexamples () =
  let
    val config = upd_substrate Compute
      (upd_iterations 10
        (upd_size 1
          (upd_seed (SOME 1)
            (upd_max_counterexamples 3 default_config))))
  in
    case random config ``(x : num) = x + 1`` of
        Counterexample counterexamples => length counterexamples = 3
      | _ => false
  end

fun negative_seed_agrees_across_substrates () =
  let
    val config = upd_iterations 3
      (upd_size 10
        (upd_seed (SOME ~1) default_config))
    val goal = ``(x : num) = x + 1``
    fun binding choice =
      case random (upd_substrate choice config) goal of
          Counterexample (cex :: _) =>
            (case #bindings cex of
                 [(_, value)] => SOME value
               | _ => NONE)
        | _ => NONE
  in
    strategy_seed config = normalize_seed ~1 andalso
    (case (binding Compute, binding Cv, binding NativeSML) of
         (SOME compute, SOME cv, SOME native) =>
           Term.aconv compute cv andalso Term.aconv compute native
       | _ => false)
  end

fun session_random_completes () =
  let
    val config = upd_iterations 2 (upd_size 2 default_config)
    val prior_seed = !session_seed
    val result = random config ``(x : num) = 0``
  in
    !session_seed = rand_next prior_seed andalso
    (case result of
         Counterexample _ => true
       | NoCounterexample => true
       | Unknown _ => true)
  end

fun list_draws_respect_floors () =
  let
    fun draw 0 _ = true
      | draw remaining state =
          let val (_, next) = random_term ``:num list`` 0 state
          in draw (remaining - 1) next end
  in
    draw 100 1
  end

fun compute_stream_dump_is_pinned () =
  let
    val first = Term.mk_var ("m", ``:num``)
    val second = Term.mk_var ("n", ``:num``)
    val candidates = dump_random_candidates
      {plan = Gen (first, Gen (second, Test boolSyntax.T)),
       seed = 1, size = 999, count = 2}
    fun values terms = List.map
      (Arbnum.toInt o numSyntax.dest_numeral) terms
  in
    List.map values candidates = [[423, 509], [648, 382]]
  end

val _ = require_msg (check_result random_reverse_counterexample) (fn () =>
  "the random backend did not refute REVERSE xs = xs") (fn () => ()) ()

val _ = require_msg (check_result random_is_registered) (fn () =>
  "the random backend was not registered with weight 30") (fn () => ()) ()

val _ = require_msg (check_result random_arithmetic_counterexample) (fn () =>
  "the random backend did not refute x - y + y = x") (fn () => ()) ()

val _ = require_msg (check_result random_seed_is_reproducible) (fn () =>
  "the random backend was not reproducible for an explicit seed")
  (fn () => ()) ()

val _ = require_msg
  (check_result random_collects_requested_counterexamples) (fn () =>
  "the random backend stopped before max_counterexamples")
  (fn () => ()) ()

val _ = require_msg
  (check_result negative_seed_agrees_across_substrates) (fn () =>
  "a negative seed produced different substrate streams")
  (fn () => ()) ()

val _ = require_msg (check_result session_random_completes) (fn () =>
  "the session random generator did not complete a run") (fn () => ()) ()

val _ = require_msg (check_result list_draws_respect_floors) (fn () =>
  "small-budget recursive list draws raised an exception") (fn () => ()) ()

val _ = require_msg (check_result compute_stream_dump_is_pinned) (fn () =>
  "the compute candidate-dump hook did not preserve the pinned stream")
  (fn () => ()) ()

(* The public corpus precedes the potential-path tests below.  Those tests
   replace the ordinary list generator with tiny adversarial generators. *)
val selftest_level =
  case OS.Process.getEnv "HOLSELFTESTLEVEL" of
      NONE => 1
    | SOME text =>
        (case Int.fromString text of
            NONE => 1
          | SOME level => level)

fun same_snapshot (left : Refute_EvalCv.snapshot)
    (right : Refute_EvalCv.snapshot) =
  #theory left = #theory right andalso
  same_string_set (#types left) (#types right) andalso
  same_string_set (#constants left) (#constants right) andalso
  same_string_set (#bindings left) (#bindings right)

fun make_bracket_artifacts suffix =
  let
    val prefix = fresh_prefix () ^ suffix
    val _ = Theory.new_type (prefix ^ "_type", 0)
    val _ = Theory.new_constant (prefix ^ "_const", ``:num``)
    val _ = Theory.save_thm (prefix ^ "_binding", boolTheory.TRUTH)
  in
    ()
  end

fun clean_bracket_success () =
  let
    val baseline = snapshot ()
    val _ = with_clean_theory (fn () => make_bracket_artifacts "success")
  in
    same_snapshot baseline (snapshot ())
  end

fun clean_bracket_exception () =
  let
    val baseline = snapshot ()
    val raised =
      ((with_clean_theory (fn () =>
          (make_bracket_artifacts "exception";
           raise Fail "forced cv bracket failure")); false)
       handle Fail "forced cv bracket failure" => true)
  in
    raised andalso same_snapshot baseline (snapshot ())
  end

fun clean_bracket_interrupt () =
  let
    val baseline = snapshot ()
    val raised =
      ((with_clean_theory (fn () =>
          (make_bracket_artifacts "interrupt"; raise Interrupt)); false)
       handle Interrupt => true)
  in
    raised andalso same_snapshot baseline (snapshot ())
  end

fun translation_error_is_clean () =
  let
    val baseline = snapshot ()
    val attempt = with_generators [``:bool``] (fn _ =>
      (make_bracket_artifacts "hol_error";
       raise (Feedback.mk_HOL_ERR
         "RefuteCvSelftest" "translate" "forced translation error")))
  in
    (case attempt of
         CvInapplicable [reason] =>
           String.isPrefix "cv: RefuteCvSelftest.translate" reason
       | _ => false) andalso
    same_snapshot baseline (snapshot ())
  end

val _ = tprint "Refute cv clean-theory bracket"
val _ = require_msg (check_result (fn () =>
  clean_bracket_success () andalso clean_bracket_exception () andalso
  clean_bracket_interrupt () andalso translation_error_is_clean ()))
  (fn () =>
    "cv bracket left a theory artifact on a return or exception")
  (fn () => ()) ()

fun generated_tree_agrees () =
  let
    val baseline = snapshot ()
    val attempt = with_generators [``:rg_tree``] (fn generators =>
      case generators of
          [{exhaustive, random, ...}] =>
            let
              fun exhaustive_agrees size =
                let
                  val application = Term.mk_comb
                    (exhaustive, numSyntax.term_of_int size)
                  val (actual, _) = listSyntax.dest_list
                    (cv_rhs application)
                in
                  same_terms (compute_exhaustive ``:rg_tree`` size) actual
                end
              fun random_agrees size seed =
                let
                  val application = Term.list_mk_comb
                    (random,
                     [numSyntax.term_of_int size,
                      numSyntax.term_of_int seed])
                  val (actual_value, actual_state) =
                    pairSyntax.dest_pair (cv_rhs application)
                  val (expected_value, expected_state) =
                    random_term ``:rg_tree`` size (IntInf.fromInt seed)
                in
                  Term.aconv actual_value expected_value andalso
                  Term.aconv actual_state
                    (num_term_of_intinf expected_state)
                end
            in
              List.all exhaustive_agrees [0, 1, 2] andalso
              List.all (fn seed => random_agrees 3 seed) [1, 2, 3]
            end
        | _ => false)
  in
    (case attempt of CvSuccess result => result
     | CvInapplicable _ => false) andalso
    same_snapshot baseline (snapshot ())
  end

fun generated_finite_agrees ty =
  let
    val baseline = snapshot ()
    val attempt = with_generators [ty] (fn generators =>
      case generators of
          [{exhaustive, random, ...}] =>
            let
              fun exhaustive_agrees size =
                let
                  val application = Term.mk_comb
                    (exhaustive, numSyntax.term_of_int size)
                  val (actual, _) = listSyntax.dest_list
                    (cv_rhs application)
                in
                  same_terms (compute_exhaustive ty size) actual
                end
              fun random_agrees seed =
                let
                  val application = Term.list_mk_comb
                    (random,
                     [numSyntax.term_of_int 3,
                      numSyntax.term_of_int seed])
                  val (actual_value, actual_state) =
                    pairSyntax.dest_pair (cv_rhs application)
                  val (expected_value, expected_state) =
                    random_term ty 3 (IntInf.fromInt seed)
                in
                  Term.aconv actual_value expected_value andalso
                  Term.aconv actual_state
                    (num_term_of_intinf expected_state)
                end
            in
              List.all exhaustive_agrees [0, 2] andalso
              List.all random_agrees [1, 2, 3]
            end
        | _ => false)
  in
    (case attempt of CvSuccess result => result
     | CvInapplicable _ => false) andalso
    same_snapshot baseline (snapshot ())
  end

fun generated_tree_repeats_and_caches () =
  let
    val baseline = snapshot ()
    val stats0 = synthesis_stats ()
    val first = generated_tree_agrees ()
    val stats1 = synthesis_stats ()
    val second = generated_tree_agrees ()
    val stats2 = synthesis_stats ()
  in
    first andalso second andalso
    #misses stats1 = #misses stats0 + 1 andalso
    #misses stats2 = #misses stats1 andalso
    #hits stats2 = #hits stats1 + 1 andalso
    same_snapshot baseline (snapshot ())
  end

fun out_of_fragment_is_clean () =
  let
    val baseline = snapshot ()
    fun rejected ty =
      case with_generators [ty]
          (fn _ => raise Fail "out-of-fragment continuation ran") of
          CvInapplicable reasons =>
            not (null reasons) andalso
            List.all (String.isPrefix "cv: ") reasons
        | CvSuccess _ => false
  in
    rejected ``:real`` andalso rejected ``:num -> bool`` andalso
    same_snapshot baseline (snapshot ())
  end

val _ =
  if selftest_level >= 2 then
    (tprint "Refute cv per-goal generator synthesis";
     require_msg (check_result generated_tree_repeats_and_caches) (fn () =>
       "cv generator synthesis disagreed, leaked, or missed its cache")
       (fn () => ()) ();
     require_msg (check_result (fn () =>
       generated_finite_agrees ``:rg_enum`` andalso
       generated_finite_agrees ``:bool option``)) (fn () =>
         "cv finite generator synthesis disagreed or leaked an artifact")
       (fn () => ()) ();
     require_msg (check_result out_of_fragment_is_clean) (fn () =>
       "cv accepted an out-of-fragment type or leaked an artifact")
       (fn () => ()) ())
  else ()

fun first_cex_bindings (Counterexample (cex :: _)) =
      SOME (#bindings cex)
  | first_cex_bindings _ = NONE

fun cv_result strategy choice goal =
  let
    val config = upd_substrate choice
      (upd_iterations 100 (upd_size 3 default_config))
  in
    let
      val instances = qc_instances config goal
      val reasons = instance_gate_reasons instances
    in
      if null reasons then strategy_run strategy config instances
      else Unknown reasons
    end
  end

fun cv_agrees strategy goal =
  let
    val baseline = snapshot ()
    val compute = cv_result strategy Compute goal
    val cv = cv_result strategy Cv goal
  in
    (case (first_cex_bindings compute, first_cex_bindings cv) of
         (SOME left, SOME right) => same_bindings left right
       | (NONE, NONE) =>
           (case (compute, cv) of
                (NoCounterexample, NoCounterexample) => true
              | (Unknown _, Unknown _) => true
              | _ => false)
       | _ => false) andalso same_snapshot baseline (snapshot ())
  end

fun explicit_cv_smoke () =
  let
    val goal = ``REVERSE (xs : num list) = xs``
  in
    cv_agrees Exhaustive goal andalso
    cv_agrees (Random {seed = 1}) goal
  end

val _ = tprint "Refute cv substrate smoke"
val _ = require_msg (check_result explicit_cv_smoke) (fn () =>
  "the cv substrate disagreed with compute or leaked theory state")
  (fn () => ()) ()

fun native_agrees strategy goal =
  let
    val compute = cv_result strategy Compute goal
    val native = cv_result strategy NativeSML goal
  in
    case (compute, native) of
        (Counterexample (left :: _), Counterexample (right :: _)) =>
          #backend left = #backend right andalso
          #substrate left = "compute" andalso
          #substrate right = "native" andalso
          Option.isSome (#cert left) andalso
          Option.isSome (#cert right) andalso
          same_bindings (#bindings left) (#bindings right)
      | (NoCounterexample, NoCounterexample) => true
      | _ => false
  end

fun native_smoke () =
  let
    val goals =
      [``REVERSE (xs : num list) = xs``,
       ``(x : num) - y + y = x``,
       ``(x : refute$rf3) = rf3_1``]
    fun strategies goal =
      native_agrees Exhaustive goal andalso
      List.all (fn seed => native_agrees (Random {seed = seed}) goal)
        [1, 2, 3]
  in
    List.all strategies goals
  end

fun native_custom_is_inapplicable () =
  let
    val variable = Term.mk_var ("native_custom", ``:rg_record``)
    val plan = Gen (variable, Test boolSyntax.T)
    fun rejected strategy =
      case Refute_EvalSML.compile default_config strategy [plan] of
          Inapplicable reasons =>
            List.exists (String.isPrefix
              "custom generator registered for :rg_record") reasons
        | Compiled test => (#close test (); false)
  in
    rejected Exhaustive andalso rejected (Random {seed = 1})
  end

fun native_compile_error_is_reason () =
  let
    val original = !extract_tests_hook
    val table_count_before = term_table_count ()
    fun broken _ _ _ =
      let val table = register_term_tables [] []
      in
        Extracted
          {source = "val refute_broken =", entry = "()", table = table}
      end
    val _ = extract_tests_hook := broken
    val captured = Exn.capture (fn () =>
      Refute_EvalSML.compile default_config Exhaustive []) ()
    val _ = extract_tests_hook := original
  in
    case captured of
        Exn.Res (Inapplicable [reason]) =>
          String.isPrefix "native: internal: " reason andalso
          size reason > size "native: internal: " andalso
          term_table_count () = table_count_before
      | _ => false
  end

fun native_ignored_filter_resumes () =
  let
    val variable = Term.mk_var ("native_ignored", ``:bool``)
    val plan = Gen (variable, Test boolSyntax.F)
    fun exhaustive () =
      case Refute_EvalSML.compile default_config Exhaustive [plan] of
          Inapplicable _ => false
        | Compiled test =>
            let
              val first = #run test
                {genuine_only = true, card = 1, size = 2, draws = 0,
                 ignored = []}
              val second =
                case first of
                    CexFound candidate => #run test
                      {genuine_only = true, card = 1, size = 2, draws = 0,
                       ignored = [candidate]}
                  | _ => Exhausted {complete = false}
              val _ = #close test ()
            in
              case (first, second) of
                  (CexFound {env = [(_, left)], ...},
                   CexFound {env = [(_, right)], ...}) =>
                    not (Term.aconv left right)
                | _ => false
            end
    val number = Term.mk_var ("native_random_ignored", ``:num``)
    val random_plan = Gen (number, Test boolSyntax.F)
    fun random () =
      case Refute_EvalSML.compile default_config (Random {seed = 1})
          [random_plan] of
          Inapplicable _ => false
        | Compiled test =>
            let
              val first = #run test
                {genuine_only = true, card = 1, size = 0, draws = 1,
                 ignored = []}
              val second =
                case first of
                    CexFound candidate => #run test
                      {genuine_only = true, card = 1, size = 0, draws = 5,
                       ignored = [candidate]}
                  | _ => CexFound {env = [], genuine = false}
              val _ = #close test ()
            in
              case second of Exhausted _ => true | _ => false
            end
  in
    exhaustive () andalso random ()
  end

val _ = tprint "Refute native substrate smoke"
val _ = require_msg (check_result (fn () =>
  native_smoke () andalso native_custom_is_inapplicable () andalso
  native_compile_error_is_reason () andalso
  native_ignored_filter_resumes ())) (fn () =>
  "the native harness disagreed, accepted a custom generator, or crashed")
  (fn () => ()) ()

fun native_timeout_is_healthy () =
  let
    val variable = Term.mk_var ("native_huge", ``:num list``)
    val huge = Gen (variable, Test boolSyntax.T)
    val short = upd_timeout 0.05 default_config
    val started = Time.now ()
    val timed =
      case Refute_EvalSML.compile short Exhaustive [huge] of
          Inapplicable _ => false
        | Compiled test =>
            let
              val result = #run test
                {genuine_only = true, card = 1, size = 100, draws = 0,
                 ignored = []}
              val _ = #close test ()
            in
              case result of GaveUp "deadline" => true | _ => false
            end
    val elapsed = Time.toReal (Time.- (Time.now (), started))
    val healthy =
      case Refute_EvalSML.compile default_config Exhaustive
          [Test boolSyntax.F] of
          Inapplicable _ => false
        | Compiled test =>
            let
              val result = #run test
                {genuine_only = true, card = 1, size = 1, draws = 0,
                 ignored = []}
              val _ = #close test ()
            in
              case result of CexFound _ => true | _ => false
            end
  in
    timed andalso elapsed < 2.0 andalso healthy
  end

fun native_benchmark () =
  let
    val plan = compile_plan default_config
      ``REVERSE (REVERSE (xs : num list)) = xs``
  in
    case Refute_EvalSML.compile default_config Exhaustive [plan] of
        Inapplicable _ => false
      | Compiled test =>
          let
            val started = Time.now ()
            val result = #run test
              {genuine_only = true, card = 1, size = 9, draws = 0,
               ignored = []}
            val elapsed = Time.toReal (Time.- (Time.now (), started))
            val tests =
              case lookup_stat "tests" (!(#last_stats test)) of
                  SOME count => count
                | NONE => 0
            val rate = if elapsed <= 0.0 then 0.0
              else Real.fromInt tests / elapsed
            val _ = TextIO.print
              ("Refute native benchmark: " ^
               Int.toString (Real.round rate) ^ " tests/sec\n")
            val _ = #close test ()
          in
            tests > 0 andalso
            (case result of Exhausted _ => true | _ => false)
          end
  end

val _ =
  if selftest_level >= 2 then
    (tprint "Refute native timeout smoke";
     require_msg (check_result native_timeout_is_healthy) (fn () =>
       "a native deadline failed or left the session unhealthy")
       (fn () => ()) ();
     tprint "Refute native substrate benchmark";
     require_msg (check_result native_benchmark) (fn () =>
       "the native list/nat benchmark did not exhaust its search")
       (fn () => ()) ())
  else ()

fun cv_matrix_agrees () =
  let
    val goals =
      [("list", ``REVERSE (xs : num list) = xs``),
       ("table", ``(x : refute$rf3) = rf3_1``),
       ("synthesised", ``(t : rg_tree) = RGTip n ==> F``)]
    fun check (_, goal) strategy = cv_agrees strategy goal
    fun strategies goal =
      check goal Exhaustive andalso
      List.all (fn seed => check goal (Random {seed = seed}))
        [1, 2, 3]
  in
    List.all strategies goals
  end

fun cv_stream_resumes () =
  let
    val variable = Term.mk_var ("x", ``:num``)
    val plan = Gen
      (variable, Test (boolSyntax.mk_neg
        (boolSyntax.mk_eq (variable, ``2803 : num``))))
    fun run compile =
      case compile default_config (Random {seed = 1}) [plan] of
          Inapplicable reasons =>
            raise Fail (String.concatWith "; " reasons)
        | Compiled test =>
            let
              val first = #run test
                {genuine_only = true, card = 1, size = 5000,
                 draws = 1024, ignored = []}
              val middle = #run test
                {genuine_only = true, card = 1, size = 5000,
                 draws = 75, ignored = []}
              val last = #run test
                {genuine_only = true, card = 1, size = 5000,
                 draws = 1, ignored = []}
              val _ = #close test ()
            in
              (first, middle, last)
            end
    val baseline = snapshot ()
    val (compute_first, compute_middle, compute_last) =
      run Refute_EvalCompute.compile
    val (cv_first, cv_middle, cv_last) = run Refute_EvalCv.compile
    fun is_empty (Exhausted _) = true | is_empty _ = false
    fun value (CexFound {env = [(_, tm)], ...}) = SOME tm
      | value _ = NONE
  in
    is_empty compute_first andalso is_empty cv_first andalso
    is_empty compute_middle andalso is_empty cv_middle andalso
    (case (value compute_last, value cv_last) of
         (SOME left, SOME right) =>
           Term.aconv left ``2803 : num`` andalso Term.aconv left right
       | _ => false) andalso same_snapshot baseline (snapshot ())
  end

fun cv_partial_is_clean () =
  let
    val baseline = snapshot ()
    val variable = Term.mk_var ("xs", ``:num list``)
    val plan = Gen
      (variable, Test ``HD (xs : num list) = HD xs``)
    val rejected =
      case Refute_EvalCv.compile default_config Exhaustive [plan] of
          Inapplicable reasons =>
            List.exists (fn reason =>
              String.isSubstring "cv: precondition for HD" reason) reasons
        | Compiled test => (#close test (); false)
  in
    rejected andalso same_snapshot baseline (snapshot ())
  end

fun cv_revert_under_translation_failure () =
  let
    val baseline = snapshot ()
    val definitions_landed = ref false
    val attempt = with_generators [``:rg_tree``] (fn _ =>
      let
        val _ = definitions_landed :=
          not (same_snapshot baseline (snapshot ()))
        val xs = Term.mk_var
          (fresh_prefix () ^ "bad_xs", ``:num list``)
        val bad = Term.mk_var
          (fresh_prefix () ^ "bad",
           Type.mk_type
             ("fun", [listSyntax.mk_list_type numSyntax.num,
                       numSyntax.num]))
        val equation = boolSyntax.mk_eq
          (Term.mk_comb (bad, xs), listSyntax.mk_hd xs)
        val definition = TotalDefn.Define
          [HOLPP.ANTIQUOTE equation]
        val _ = cv_transLib.cv_auto_trans definition
      in
        false
      end)
    val helper_rejected =
      case attempt of
          CvInapplicable reasons => not (null reasons)
        | CvSuccess _ => false
    val variable = Term.mk_var ("cv_bad_tree", ``:rg_tree``)
    val plan = Gen
      (variable, Test ``rx_unmapped 0 = 0``)
    val production_clean =
      case Refute_EvalCv.compile default_config Exhaustive [plan] of
          Inapplicable reasons => not (null reasons)
        | Compiled test =>
            let
              val result = #run test
                {genuine_only = true, card = 1, size = 2, draws = 0,
                 ignored = []}
              val production_landed =
                not (same_snapshot baseline (snapshot ()))
              val _ = #close test ()
            in
              production_landed andalso
              (case result of
                   GaveUp reason => String.isPrefix "cv: " reason
                 | _ => false)
            end
  in
    !definitions_landed andalso helper_rejected andalso
    production_clean andalso same_snapshot baseline (snapshot ())
  end

fun cv_timeout_is_healthy () =
  let
    val baseline = snapshot ()
    val original = valOf (List.find (fn substrate =>
      #name substrate = "cv") (get_substrates ()))
    val config = upd_timeout 0.2
      (upd_iterations 1
        (upd_size 1
          (upd_sequential true
            (upd_backends (SOME ["random"])
              (upd_substrate Cv default_config)))))
    val compiled =
      case Refute_EvalCv.compile config (Random {seed = 1})
          [Test boolSyntax.T] of
          Inapplicable reasons =>
            raise Fail (String.concatWith "; " reasons)
        | Compiled test => test
    val warm = #run compiled
      {genuine_only = true, card = 1, size = 1, draws = 0,
       ignored = []}
    val _ =
      case warm of
          Exhausted _ => ()
        | _ => raise Fail "cv timeout runner did not warm up"
    fun huge_run (input : run_input) = #run compiled
      {genuine_only = #genuine_only input, card = #card input,
       size = #size input, draws = 1000000000000,
       ignored = #ignored input}
    val replacement_test : compiled_test =
      {run = huge_run, close = #close compiled,
       max_chunk = #max_chunk compiled,
       last_stats = #last_stats compiled}
    val replacement : substrate =
      {name = "cv", priority = #priority original,
       compile = fn _ => fn _ => fn _ => Compiled replacement_test}
    val _ = register_substrate replacement
    val started = Time.now ()
    val result = Refute.refute config ``T``
      handle error =>
        (register_substrate original; #close compiled (); raise error)
    val elapsed = Time.toReal (Time.- (Time.now (), started))
    val _ = register_substrate original
    val _ = #close compiled ()
    val timed_out =
      case result of
          Refute.Unknown reasons =>
            List.exists (String.isSubstring "timed out") reasons
        | _ => false
    val clean_after_timeout = same_snapshot baseline (snapshot ())
    val healthy_config = upd_timeout 5.0
      (upd_size 2
        (upd_sequential true
          (upd_backends (SOME ["exhaustive"])
            (upd_substrate Cv default_config))))
    val healthy =
      case Refute.refute healthy_config ``(b : bool)`` of
          Refute.Counterexample ({cert = SOME _, ...} :: _) => true
        | _ => false
  in
    timed_out andalso elapsed < 1.0 andalso clean_after_timeout andalso
    healthy andalso same_snapshot baseline (snapshot ())
  end

fun cv_dual_run_is_clean sequential goal sound =
  let
    val baseline = snapshot ()
    val original = valOf (List.find (fn substrate =>
      #name substrate = "cv") (get_substrates ()))
    val results = ref ([] : (strategy * run_result) list)
    val closes = ref 0
    val result_mutex = Mutex.mutex ()
    fun record entry = Multithreading.synchronized
      "Refute cv racing result" result_mutex
      (fn () => results := entry :: !results)
    fun wrap strategy test : compiled_test =
      {run = fn input =>
         let
           val result = #run test input
           val _ = record (strategy, result)
         in
           result
         end,
       close = fn () =>
         (Multithreading.synchronized "Refute cv racing close"
            result_mutex (fn () => closes := !closes + 1);
          #close test ()),
       max_chunk = #max_chunk test,
       last_stats = #last_stats test}
    val replacement : substrate =
      {name = "cv", priority = #priority original,
       compile = fn config => fn strategy => fn plans =>
         case #compile original config strategy plans of
             Inapplicable reasons => Inapplicable reasons
           | Compiled test => Compiled (wrap strategy test)}
    val config = upd_timeout 10.0
      (upd_iterations 20
        (upd_size 2
          (upd_sequential sequential
            (upd_backends (SOME ["exhaustive", "random"])
              (upd_substrate Cv default_config)))))
    val _ = register_substrate replacement
    val outcome = Refute.refute config goal
      handle error => (register_substrate original; raise error)
    val _ = register_substrate original
    fun exhaustive_result (Exhaustive, Exhausted _) = true
      | exhaustive_result _ = false
    fun random_result (Random _, Exhausted _) = true
      | random_result _ = false
    val both_exhausted =
      List.exists exhaustive_result (!results) andalso
      List.exists random_result (!results) andalso !closes = 2
    val accepted =
      if sound then
        (case outcome of Refute.NoCounterexample => both_exhausted
         | _ => false)
      else
        (case outcome of
             Refute.Counterexample ({cert = SOME _, ...} :: _) => true
           | _ => false)
  in
    accepted andalso same_snapshot baseline (snapshot ())
  end

fun cv_racing_is_clean () =
  cv_dual_run_is_clean false ``(b : bool)`` false andalso
  cv_dual_run_is_clean false ``T`` true andalso
  cv_dual_run_is_clean true ``T`` true

val _ =
  if selftest_level >= 2 then
    (tprint "Refute cv substrate conformance";
     require_msg (check_result cv_matrix_agrees) (fn () =>
       "cv disagreed with compute on the corpus slice")
       (fn () => ()) ();
     require_msg (check_result cv_stream_resumes) (fn () =>
       "the cv random stream did not resume across chunks")
       (fn () => ()) ();
     require_msg (check_result cv_partial_is_clean) (fn () =>
       "cv accepted a partial property or leaked theory state")
       (fn () => ()) ();
     require_msg (check_result cv_revert_under_translation_failure) (fn () =>
       "cv translation failure was not inapplicable and residue-free")
       (fn () => ()) ();
     require_msg (check_result cv_timeout_is_healthy) (fn () =>
       "a cv chunk timeout missed its deadline, leaked, or broke cv")
       (fn () => ()) ();
     require_msg (check_result cv_racing_is_clean) (fn () =>
       "a parallel or sequential dual-cv run failed or leaked")
       (fn () => ()) ())
  else ()

val corpus_config =
  upd_timeout 5.0
    (upd_seed (SOME 1)
      (upd_sequential true
        (upd_backends (SOME ["exhaustive"]) default_config)))

fun public_expect NoExpectation = Refute.NoExpectation
  | public_expect ExpectNone = Refute.ExpectNone
  | public_expect ExpectUnknown = Refute.ExpectUnknown
  | public_expect ExpectCex = Refute.ExpectCex
  | public_expect ExpectGenuine = Refute.ExpectGenuine
  | public_expect ExpectQuasiGenuine = Refute.ExpectQuasiGenuine
  | public_expect ExpectPotential = Refute.ExpectPotential

fun tc {name, cfg, tm, expect} =
  let
    val _ = tprint name
    val config = Refute.upd_expect (public_expect expect) cfg
    val _ = Refute.refute config tm
  in
    OK ()
  end
  handle e => die (Feedback.exn_to_string e)

fun is_unknown_with needle (Refute.Unknown reasons) =
      List.exists (String.isSubstring needle) reasons
  | is_unknown_with _ _ = false

fun check_corpus name predicate =
  let val _ = tprint name
  in if predicate () then OK () else die "corpus check failed" end
  handle e => die (Feedback.exn_to_string e)

fun same_corpus_outcome (Refute.Counterexample _, Refute.Counterexample _) =
      true
  | same_corpus_outcome (Refute.NoCounterexample, Refute.NoCounterexample) =
      true
  | same_corpus_outcome (Refute.Unknown left, Refute.Unknown right) =
      left = right
  | same_corpus_outcome _ = false

fun corpus_smoke () =
  (tc {name = "Refute corpus: classic reverse",
       cfg = corpus_config,
       tm = ``REVERSE (xs : num list) = xs``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: arithmetic",
       cfg = corpus_config,
       tm = ``(x : num) - y + y = x``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: sound reverse",
       cfg = corpus_config,
       tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
       expect = ExpectNone})

fun corpus_classics () =
  (tc {name = "Refute corpus: reverse append mutation",
       cfg = corpus_config,
       tm = ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: ALL_DISTINCT append mutation",
       cfg = corpus_config,
       tm = ``ALL_DISTINCT (xs : num list ++ ys) <=>
             ALL_DISTINCT xs /\ ALL_DISTINCT ys``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: nub append mutation",
       cfg = corpus_config,
       tm = ``nub (xs : num list ++ ys) = nub xs ++ nub ys``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: integer order mutation",
       cfg = corpus_config,
       tm = ``~((x : int) = x)``,
       expect = ExpectGenuine})

fun corpus_smart_quantifiers () =
  let
    val ordered_insert =
      ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``
    val lookup =
      ``(m1 : num -> num option) k = SOME (v : num) ==>
        m1 k = NONE``
    val let_case =
      ``let z = (xs : num option) in
          case z of NONE => F | SOME x => x = x``
  in
    tc {name = "Refute corpus: sorted insert mutation",
        cfg = corpus_config, tm = ordered_insert, expect = ExpectGenuine};
    tc {name = "Refute corpus: fmap lookup premise",
        cfg = corpus_config, tm = lookup, expect = ExpectGenuine};
    check_corpus "Refute corpus: let/case plan" (fn () =>
      case compile_plan corpus_config let_case of
          Gen (_, Test _) => true
        | _ => false)
  end

fun corpus_default_quickcheck () =
  let
    val config =
      upd_backends (SOME ["exhaustive", "random"]) (!the_config)
    fun check name tm =
      tc {name = "Refute default quickcheck: " ^ name,
          cfg = config, tm = tm, expect = ExpectGenuine}
  in
    check "classic reverse" ``REVERSE (xs : num list) = xs``;
    check "reverse append mutation"
      ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``;
    check "ALL_DISTINCT append mutation"
      ``ALL_DISTINCT (xs : num list ++ ys) <=>
        ALL_DISTINCT xs /\ ALL_DISTINCT ys``;
    check "nub append mutation"
      ``nub (xs : num list ++ ys) = nub xs ++ nub ys``;
    check "integer order mutation" ``~((x : int) = x)``;
    check "sorted insert mutation"
      ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``;
    check "fmap lookup premise"
      ``(m1 : num -> num option) k = SOME (v : num) ==>
        m1 k = NONE``
  end

fun corpus_potential () =
  let
    val hd_goal =
      ``HD (xs : num list) = if xs = [] then HD ys else HD xs``
    val hd_map = ``~(HD (MAP (f : num -> num) xs) = f (HD xs))``
    val short_lists : custom_gen =
      { enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
        random = NONE }
    val _ = register_generator ``:num list`` short_lists
    val abort_config = upd_abort_potential true corpus_config
    val genuine_config = upd_genuine_only true corpus_config
    fun potential result =
      case result of
          Refute_Core.Counterexample
            ({certainty = Refute_Core.Potential _, cert = NONE, ...} :: _) =>
              true
        | _ => false
  in
    check_corpus "Refute corpus: HD potential only" (fn () =>
      potential (exhaustive abort_config hd_goal));
    check_corpus "Refute corpus: abort potential" (fn () =>
      potential (exhaustive abort_config hd_goal));
    check_corpus "Refute corpus: genuine only" (fn () =>
      case exhaustive genuine_config hd_goal of
          Refute_Core.Counterexample _ => false
        | _ => true);
    tc {name = "Refute corpus: HD/MAP certification upgrade",
        cfg = corpus_config, tm = hd_map, expect = ExpectGenuine}
  end

fun corpus_polymorphism () =
  (tc {name = "Refute corpus: polymorphic lists",
       cfg = corpus_config,
       tm = ``(xs : 'a list) = ys``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: polymorphic card schedule",
       cfg = corpus_config,
       tm = ``(x : 'a) = y``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: num fallback",
       cfg = upd_finite_types false corpus_config,
       tm = ``(x : 'a) = y``,
       expect = ExpectGenuine})

fun corpus_functions () =
  let
    val map_goal =
      ``MAP (f : num -> num) xs = MAP (g : num -> num) xs ==> f = g``
    val goal =
      ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
        f rf2_2 = rf2_2 ==> F``
  in
    check_corpus "Refute corpus: MAP function plan" (fn () =>
      let val _ = compile_plan corpus_config map_goal in true end);
    tc {name = "Refute corpus: function UPDATE counterexample",
        cfg = corpus_config, tm = goal, expect = ExpectGenuine};
    check_corpus "Refute corpus: function UPDATE witness" (fn () =>
      case Refute.refute corpus_config goal of
          Refute.Counterexample ({bindings, ...} :: _) =>
            List.exists (fn (_, value) =>
              not (null (#1 (combinSyntax.strip_update value)))) bindings
        | _ => false)
  end

fun corpus_quantifiers () =
  let
    val finite =
      ``(p : bool) /\ (!x : bool. x) /\
        (?y : refute$rf2. y = y)``
    val infinite = ``(!n : num. n <= n)``
  in
    check_corpus "Refute corpus: finite quantifier expansion" (fn () =>
      case preprocess corpus_config (preprocessing_problem finite) of
          [instance] => has_conjunction (#goal instance)
        | _ => false);
    tc {name = "Refute corpus: finite check counterexample",
        cfg = corpus_config, tm = ``(b : bool)``, expect = ExpectGenuine};
    tc {name = "Refute corpus: num quantifier unknown",
        cfg = corpus_config, tm = infinite, expect = ExpectUnknown}
  end

fun corpus_hol4_specific () =
  let
    val record_goal = ``(r : rg_record) = s``
    val word_goal =
      ``w2n ((a : bool[8]) + b) = w2n a + w2n b``
    val quotient_goal = ``(x : real) = y``
  in
    tc {name = "Refute corpus: record type",
        cfg = corpus_config, tm = record_goal, expect = ExpectGenuine};
    tc {name = "Refute corpus: word addition",
        cfg = corpus_config, tm = word_goal, expect = ExpectGenuine};
    tc {name = "Refute corpus: quotient unknown",
        cfg = corpus_config, tm = quotient_goal, expect = ExpectUnknown};
    check_corpus "Refute corpus: quotient explanation" (fn () =>
      is_unknown_with "quotient" (Refute.refute corpus_config quotient_goal))
  end

(* Numeral/string/char literals in a goal must not be mistaken for
   non-executable constants (their internal NUMERAL/BIT1/STRING/CHR
   tags reduce natively under EVAL), so goals mentioning them stay
   testable and their counterexamples are found and certified. *)
fun corpus_literals () =
  (tc {name = "Refute corpus: numeral literal counterexample",
       cfg = corpus_config, tm = ``!n : num. n <> 2``, expect = ExpectGenuine};
   tc {name = "Refute corpus: character literal counterexample",
       cfg = corpus_config, tm = ``!c : char. c <> #"a"``,
       expect = ExpectGenuine};
   tc {name = "Refute corpus: string literal counterexample",
       cfg = corpus_config, tm = ``!s : string. s <> "x"``,
       expect = ExpectGenuine})

fun corpus_soundness () =
  (tc {name = "Refute corpus: sound reverse involution",
       cfg = corpus_config,
       tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound addition commutes",
       cfg = corpus_config,
       tm = ``T``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound bool check_all",
       cfg = corpus_config,
       tm = ``(b : bool) \/ ~b``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound rf check_all",
       cfg = corpus_config,
       tm = ``(x : refute$rf2) = rf2_1 \/ x = rf2_2``,
       expect = ExpectNone})

fun corpus_registries () =
  let
    val _ = Datatype.Datatype `rg_sorted = RGSorted (num list)`
    val sorted_ty = ``:rg_sorted``
    val sorted_constructor = ``RGSorted``
    val sorted_predicate =
      ``\s : rg_sorted. case s of RGSorted xs => SORTED $<= xs``
    val _ = abstract_generator
      {ty = sorted_ty,
       constructors = [sorted_constructor],
       pred = SOME sorted_predicate}
    val _ = Datatype.Datatype `rg_custom = RGC0 | RGC1`
    val custom_ty = ``:rg_custom``
    val custom : custom_gen =
      {enumerate = SOME (fn _ => [``RGC0``, ``RGC1``]), random = NONE}
    val _ = register_generator custom_ty custom
  in
    check_corpus "Refute corpus: sorted abstract generator" (fn () =>
      case (spec_of sorted_ty, predicate_of sorted_ty) of
          (GenDatatype _, SOME predicate) =>
            Term.aconv predicate sorted_predicate
        | _ => false);
    check_corpus "Refute corpus: registered custom generator" (fn () =>
      case spec_of custom_ty of GenCustom _ => true | _ => false);
    tc {name = "Refute corpus: custom generator counterexample",
        cfg = corpus_config,
        tm = ``(x : rg_custom) = RGC0``,
        expect = ExpectGenuine}
  end

fun corpus_parlist () =
  let
    val parallel_config =
      upd_backends (SOME ["exhaustive", "random"])
        (upd_sequential false corpus_config)
    val sequential_config =
      upd_backends (SOME ["exhaustive", "random"]) corpus_config
    val cex_goal = ``(x : num) - y + y = x``
    val sound_goal = ``(!b : bool. b \/ ~b)``
    fun same goal =
      same_corpus_outcome
        (Refute.refute sequential_config goal,
         Refute.refute parallel_config goal)
  in
    check_corpus "Refute corpus: ParList get_first" (fn () =>
      ParList.get_first (fn n => if n = 2 then SOME n else NONE) [1, 2, 3]
        = SOME 2);
    check_corpus "Refute corpus: ParList get_some" (fn () =>
      case ParList.get_some (fn n =>
        if n = 2 orelse n = 3 then SOME n else NONE) [1, 2, 3] of
          SOME 2 => true
        | SOME 3 => true
        | _ => false);
    check_corpus "Refute corpus: parallel counterexample outcome" (fn () =>
      same cex_goal);
    check_corpus "Refute corpus: parallel sound outcome" (fn () =>
      same sound_goal)
  end

type conformance_case =
  {name : string, cfg : config, tm : term,
   inapplicable : (substrate_choice * string) list}

val conformance_substrates =
  [(Compute, "compute"), (Cv, "cv"), (NativeSML, "native")]

fun conformance_reason choice expected =
  Option.map #2 (List.find (fn (old_choice, _) => old_choice = choice)
    expected)

fun public_substrate Compute = Refute.Compute
  | public_substrate Cv = Refute.Cv
  | public_substrate NativeSML = Refute.NativeSML
  | public_substrate Auto = Refute.Auto

fun conformance_bindings (Refute.Counterexample (cex :: _)) =
      SOME (#bindings cex)
  | conformance_bindings _ = NONE

fun same_conformance_outcome (left, right) =
  case (left, right) of
      (Refute.Counterexample _, Refute.Counterexample _) =>
        (case (conformance_bindings left, conformance_bindings right) of
             (SOME left_bindings, SOME right_bindings) =>
               same_bindings left_bindings right_bindings
           | _ => false)
    | (Refute.NoCounterexample, Refute.NoCounterexample) => true
    | (Refute.Unknown left_reasons, Refute.Unknown right_reasons) =>
        left_reasons = right_reasons
    | _ => false

fun certificate_tag_clean theorem =
  Tag.isEmpty (Thm.tag theorem) orelse Tag.isDisk (Thm.tag theorem)

fun certified_conformance_cex
      (Refute.Counterexample ({certainty = Refute.Genuine,
                               cert = SOME theorem, ...} :: _)) =
        certificate_tag_clean theorem
  | certified_conformance_cex _ = false

fun conformance_outcome_name (Refute.Counterexample _) = "Counterexample"
  | conformance_outcome_name Refute.NoCounterexample = "NoCounterexample"
  | conformance_outcome_name (Refute.Unknown reasons) =
      "Unknown (" ^ String.concatWith "; " reasons ^ ")"

fun expectation_holds expectation outcome =
  case expectation of
      ExpectCex =>
        (case outcome of Refute.Counterexample (_ :: _) => true | _ => false)
    | ExpectGenuine => certified_conformance_cex outcome
    | ExpectQuasiGenuine =>
        (case outcome of
             Refute.Counterexample
               ({certainty = Refute.QuasiGenuine _, ...} :: _) => true
           | _ => false)
    | ExpectPotential =>
        (case outcome of
             Refute.Counterexample
               ({certainty = Refute.Potential _, ...} :: _) => true
           | _ => false)
    | ExpectNone =>
        (case outcome of Refute.Counterexample _ => false | _ => true)
    | ExpectUnknown =>
        (case outcome of Refute.Unknown _ => true | _ => false)
    | NoExpectation => true

fun quiet_refute config tm =
  Feedback.with_traces [("Refute", 0)]
    (fn () => Refute.refute config tm) ()

fun conform ({name, cfg, tm, inapplicable} : conformance_case) =
  let
    val expectation = #expect cfg
    val base = Refute.upd_expect Refute.NoExpectation
      (Refute.upd_sequential true cfg)
    val strategies =
      [("exhaustive", NONE), ("random", SOME 1),
       ("random", SOME 2), ("random", SOME 3)]

    fun run strategy seed choice =
      let
        val selected = Refute.upd_substrate (public_substrate choice) base
        val configured =
          case seed of
              NONE => Refute.upd_backends (SOME ["exhaustive"]) selected
            | SOME value => Refute.upd_seed (SOME value)
                (Refute.upd_backends (SOME ["random"]) selected)
      in
        quiet_refute configured tm
      end

    fun reason_matches backend prefix (Refute.Unknown reasons) =
          List.exists (String.isPrefix
            (backend ^ ": " ^ prefix)) reasons
      | reason_matches _ _ _ = false

    fun check_strategy (strategy, seed) =
      let
        val results = List.map (fn (choice, substrate) =>
          (choice, substrate, run strategy seed choice))
          conformance_substrates
        val baseline = #3 (hd results)
        val _ =
          if expectation_holds expectation baseline then ()
          else raise Fail (name ^ ": compute violated the expectation on " ^
            strategy ^ ": " ^ conformance_outcome_name baseline)

        fun check (choice, substrate, outcome) =
          case conformance_reason choice inapplicable of
              SOME prefix =>
                if reason_matches strategy prefix outcome then ()
                else raise Fail (name ^ ": " ^ substrate ^
                  " did not report expected inapplicability on " ^ strategy ^
                  ": " ^ conformance_outcome_name outcome)
            | NONE =>
                if not (same_conformance_outcome (baseline, outcome)) then
                  raise Fail (name ^ ": " ^ substrate ^
                    " disagreed with compute on " ^ strategy)
                else if expectation_holds expectation outcome then ()
                else raise Fail (name ^ ": " ^ substrate ^
                  " produced an uncertified or unsound result on " ^ strategy)
      in
        List.app check results
      end
  in
    List.app check_strategy strategies
  end

fun conformance_config expectation =
  upd_expect expectation
    (upd_timeout 10.0
      (upd_iterations 100
        (upd_size 4
          (upd_max_counterexamples 1 default_config))))

val conform_cex_config = conformance_config ExpectGenuine
val conform_none_config = conformance_config ExpectNone
val conform_unknown_config = conformance_config ExpectUnknown

val conformance_smoke_cases : conformance_case list =
  [{name = "boolean counterexample", cfg = conform_cex_config,
    tm = ``(b : bool)``, inapplicable = []},
   {name = "boolean soundness", cfg = conform_none_config,
    tm = ``(b : bool) \/ ~b``, inapplicable = []}]

val conformance_full_cases : conformance_case list =
  [{name = "reverse", cfg = conform_cex_config,
    tm = ``REVERSE (xs : num list) = xs``, inapplicable = []},
   {name = "natural subtraction", cfg = conform_cex_config,
    tm = ``(x : num) - y + y = x``, inapplicable = []},
   {name = "reverse append", cfg = conform_cex_config,
    tm = ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``,
    inapplicable = []},
   {name = "ALL_DISTINCT append", cfg = conform_cex_config,
    tm = ``ALL_DISTINCT (xs : num list ++ ys) <=>
           ALL_DISTINCT xs /\ ALL_DISTINCT ys``,
    inapplicable = []},
   {name = "nub append", cfg = conform_cex_config,
    tm = ``nub (xs : num list ++ ys) = nub xs ++ nub ys``,
    inapplicable =
      [(NativeSML, "non-constructor pattern: GSPEC f")]},
   {name = "integer equality", cfg = conform_cex_config,
    tm = ``~((x : int) = x)``, inapplicable = []},
   {name = "sorted insert", cfg = conform_cex_config,
    tm = ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``,
    inapplicable = []},
   {name = "finite-map lookup", cfg = conform_cex_config,
    tm = ``(m : num -> num option) k = SOME (v : num) ==>
           m k = NONE``,
    inapplicable =
      [(Cv, "cv: :num -> num option - function type in data position"),
       (NativeSML,
        "function equality has non-enumerable domain :num")]},
   {name = "polymorphic lists", cfg = conform_cex_config,
    tm = ``(xs : 'a list) = ys``, inapplicable = []},
   {name = "polymorphic card schedule", cfg = conform_cex_config,
    tm = ``(x : 'a) = y``, inapplicable = []},
   {name = "polymorphic num fallback",
    cfg = upd_finite_types false conform_cex_config,
    tm = ``(x : 'a) = y``, inapplicable = []},
   {name = "function UPDATE", cfg = conform_cex_config,
    tm = ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
           f rf2_2 = rf2_2 ==> F``,
    inapplicable =
      [(Cv, "cv: :rf2 -> rf2 - function type in data position")]},
   {name = "finite boolean", cfg = conform_cex_config,
    tm = ``(b : bool)``, inapplicable = []},
   {name = "word addition", cfg = conform_cex_config,
    tm = ``w2n ((a : word8) + b) = w2n a + w2n b``,
    inapplicable = []},
   {name = "numeral literal", cfg = conform_cex_config,
    tm = ``!n : num. n <> 2``, inapplicable = []},
   {name = "character literal", cfg = conform_cex_config,
    tm = ``!c : char. c <> #"a"``, inapplicable = []},
   {name = "string literal", cfg = conform_cex_config,
    tm = ``!s : string. s <> "x"``, inapplicable = []},
   {name = "MAP specialization", cfg = conform_cex_config,
    tm = ``MAP SUC (xs : num list) = xs``, inapplicable = []},
   {name = "FILTER specialization", cfg = conform_cex_config,
    tm = ``FILTER ($= 0) (xs : num list) = xs``, inapplicable = []},
   {name = "higher-order MAP", cfg = conform_cex_config,
    tm = ``MAP (f : refute$rf2 -> bool) [rf2_1; rf2_2] = [T; T]``,
    inapplicable =
      [(Cv, "cv: :rf2 -> bool - function type in data position")]},
   {name = "higher-order FILTER", cfg = conform_cex_config,
    tm = ``FILTER (p : refute$rf2 -> bool) [rf2_1; rf2_2] = []``,
    inapplicable =
      [(Cv, "cv: :rf2 -> bool - function type in data position")]},
   {name = "word-heavy", cfg = conform_cex_config,
    tm = ``word_xor (a : word8) b = a``, inapplicable = []},
   {name = "record", cfg = conform_cex_config,
    tm = ``(r : rg_stream_record) = s``, inapplicable = []},
   {name = "deep rose", cfg = conform_cex_config,
    tm = ``rx_rose (t : rg_rose) = 0``,
    inapplicable =
      [(Cv, "cv: :rg_rose - nested recursive datatype generator")]},
   {name = "partial HD", cfg = conform_cex_config,
    tm = ``HD (xs : num list) = 0``,
    inapplicable = [(Cv, "cv: precondition for HD")]},
   {name = "abstract generator", cfg = conform_cex_config,
    tm = ``(r : rg_record) = s``,
    inapplicable =
      [(Cv, "cv: :rg_record - abstract generator registered"),
       (NativeSML, "custom generator registered for :rg_record")]},
   {name = "custom generator", cfg = conform_cex_config,
    tm = ``(x : rg_custom_matrix) = RGCustomA``,
    inapplicable =
      [(Cv, "cv: :rg_custom_matrix - custom generator registered"),
       (NativeSML,
        "custom generator registered for :rg_custom_matrix")]},
   {name = "infinite quantifier", cfg = conform_unknown_config,
    tm = ``(!n : num. n <= n)``, inapplicable = []},
   {name = "quotient", cfg = conform_unknown_config,
    tm = ``(x : real) = y``,
    inapplicable =
      [(Compute, "no generator for :real"),
       (Cv, "cv: :real - quotient type"),
       (NativeSML, "no generator for :real")]},
   {name = "closed soundness", cfg = conform_none_config,
    tm = ``T``, inapplicable = []},
   {name = "reverse soundness", cfg = conform_none_config,
    tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
    inapplicable = []},
   {name = "boolean soundness", cfg = conform_none_config,
    tm = ``(b : bool) \/ ~b``, inapplicable = []},
   {name = "finite-enum soundness", cfg = conform_none_config,
    tm = ``(x : refute$rf2) = rf2_1 \/ x = rf2_2``,
    inapplicable = []}]

fun run_conformance cases = List.app conform cases

fun same_candidate_stream left right =
  length left = length right andalso
  ListPair.allEq (fn (left_candidate, right_candidate) =>
    same_terms left_candidate right_candidate) (left, right)

fun stream_conformance () =
  let
    val types =
      [("num", ``:num``), ("int", ``:int``), ("char", ``:char``),
       ("word8", ``:word8``), ("num list", ``:num list``),
       ("record", ``:rg_stream_record``), ("rose", ``:rg_rose``),
       ("function", ``:refute$rf2 -> bool``)]

    fun check seed (name, ty) =
      let
        val variable = Term.mk_var ("stream_" ^ name, ty)
        val plan = Gen (variable, Test boolSyntax.T)
        val arguments =
          {plan = plan, seed = IntInf.fromInt seed, size = 2, count = 5}
        val compute = Refute_EvalCompute.dump_random_candidates arguments
        val native = Refute_EvalSML.dump_native_random_candidates arguments
        val cv = Refute_EvalCv.dump_cv_random_candidates arguments
      in
        if same_candidate_stream compute native andalso
           same_candidate_stream compute cv
        then ()
        else raise Fail ("candidate stream disagreement for " ^ name ^
          " at seed " ^ Int.toString seed)
      end
  in
    List.app (fn seed => List.app (check seed) types) [1, 2, 3]
  end

val _ =
  if selftest_level < 2 then
    (tprint "Refute substrate conformance smoke";
     require_msg
       (check_result (fn () =>
         (run_conformance conformance_smoke_cases; true)))
       (fn () => "the substrate smoke matrix disagreed")
       (fn () => ()) ())
  else ()

val _ =
  if selftest_level >= 2 then
    (tprint "Refute full substrate conformance matrix";
     require_msg (check_result (fn () =>
       (run_conformance conformance_full_cases; true))) (fn () =>
         "the full substrate conformance matrix disagreed")
       (fn () => ()) ();
     tprint "Refute substrate candidate-stream conformance";
     require_msg (check_result (fn () =>
       (stream_conformance (); true))) (fn () =>
       "candidate streams differed across substrates")
       (fn () => ()) ())
  else ()

val _ =
  if selftest_level >= 2 then
    (corpus_smoke ();
     corpus_classics ();
     corpus_smart_quantifiers ();
     corpus_default_quickcheck ();
     corpus_polymorphism ();
     corpus_functions ();
     corpus_quantifiers ();
     corpus_hol4_specific ();
     corpus_literals ();
     corpus_soundness ();
     corpus_registries ();
     corpus_parlist ())
  else
    corpus_smoke ()

val _ = tprint "Refute certification and potential retry"

fun certified_reverse () =
  case exhaustive (upd_size 3 default_config)
    ``REVERSE (xs : num list) = xs`` of
      Counterexample ({certainty = Genuine, cert = SOME theorem, ...} :: _) =>
        Term.aconv (Thm.concl theorem)
          ``~(!xs : num list. REVERSE xs = xs)`` andalso
        certificate_tag_clean theorem
    | _ => false

val _ = require_msg (check_result certified_reverse) (fn () =>
  "REVERSE xs = xs was not certified with a tag-clean theorem")
  (fn () => ()) ()

fun make_cex genuine : counterexample =
  { backend = "selftest",
    substrate = "compute",
    certainty = Refute_Core.Potential [],
    bindings = [],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [("tests", 1)] }

fun upgrade_from_stuck_path () =
  case Refute_Cert.certify
    { original = ``F``,
      evals = [],
      env = [],
      cex = make_cex false } of
      Certified {certainty = Genuine, cert = SOME theorem, ...} =>
        Term.aconv (Thm.concl theorem) ``~F``
    | _ => false

val _ = require_msg (check_result upgrade_from_stuck_path) (fn () =>
  "certification did not upgrade a tainted candidate to Genuine")
  (fn () => ()) ()

fun false_positive_is_discarded () =
  case Refute_Cert.certify
    { original = ``T``,
      evals = [],
      env = [],
      cex = make_cex true } of
      Discarded => true
    | _ => false

val _ = require_msg (check_result false_positive_is_discarded) (fn () =>
  "certification did not discard an EVAL-true candidate") (fn () => ()) ()

val stuck_list_gen : custom_gen =
  { enumerate = SOME (fn _ => [``[] : num list``]), random = NONE }

val _ = register_generator ``:num list`` stuck_list_gen

val stuck_goal = ``HD (xs : num list) = 0``

fun potential_only config = exhaustive config stuck_goal

fun default_retries_potential () =
  case potential_only (upd_size 1 default_config) of
      Counterexample _ => false
    | Unknown _ => true
    | NoCounterexample => true

fun abort_returns_potential () =
  case potential_only (upd_abort_potential true
    (upd_size 1 default_config)) of
      Counterexample
        ({certainty = Refute_Core.Potential _, cert = NONE, ...} :: _) => true
    | _ => false

fun genuine_only_hides_potential () =
  case potential_only (upd_genuine_only true
    (upd_size 1 default_config)) of
      Counterexample _ => false
    | Unknown _ => true
    | NoCounterexample => true

val _ = require_msg (check_result default_retries_potential) (fn () =>
  "the default flow returned a potential instead of retrying genuinely")
  (fn () => ()) ()

val _ = require_msg (check_result abort_returns_potential) (fn () =>
  "abort_potential did not return the potential counterexample")
  (fn () => ()) ()

val _ = require_msg (check_result genuine_only_hides_potential) (fn () =>
  "genuine_only surfaced a potential counterexample") (fn () => ()) ()

val hd_map_lists : custom_gen =
  { enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
    random = NONE }

val _ = register_generator ``:num list`` hd_map_lists

fun hd_map_stuck_path_upgrades () =
  case exhaustive (upd_size 1 default_config)
    ``~(HD (MAP (f : num -> num) xs) = f (HD xs))`` of
      Counterexample ({certainty = Genuine, cert = SOME _, ...} :: _) => true
    | _ => false

val _ = require_msg (check_result hd_map_stuck_path_upgrades) (fn () =>
  "the HD/MAP stuck path was not upgraded to a genuine counterexample")
  (fn () => ()) ()

val _ = tprint "Refute public facade"

fun facade_reverse () =
  case Refute.quickcheck ``(x : num) - y + y = x`` of
      Refute.Counterexample _ => true
    | _ => false

fun facade_expectation () =
  ((ignore (Refute.refute
      (Refute.upd_expect Refute.ExpectNone
        (Refute.upd_backends (SOME ["exhaustive"]) default_config))
      ``(x : num) - y + y = x``); false)
   handle _ => true)

fun facade_parallel () =
  case Refute.refute
    (Refute.upd_sequential false
      (Refute.upd_backends (SOME ["exhaustive"]) default_config))
    ``(x : num) - y + y = x`` of
      Refute.Counterexample _ => true
    | _ => false

fun facade_tactic_fails () =
  ((ignore (Refute.REFUTE_TAC
      ([], ``(x : num) - y + y = x``)); false)
   handle _ => true)

fun facade_tactic_allows_unknown () =
  ((ignore (Refute.REFUTE_TAC ([], ``(x : ind) = x``)); true)
   handle _ => false)

fun facade_assumptions () =
  case (Refute.refute_goal
    (Refute.upd_backends (SOME ["exhaustive"]) default_config)
    ([``b : bool``], ``b : bool``),
    Refute.refute_goal
      (Refute.upd_no_assms true
        (Refute.upd_backends (SOME ["exhaustive"]) default_config))
      ([``b : bool``], ``b : bool``)) of
      (Refute.NoCounterexample, Refute.Counterexample _) => true
    | _ => false

val _ = require_msg (check_result facade_reverse) (fn () =>
  "the public quickcheck facade did not find a counterexample")
  (fn () => ()) ()
val _ = require_msg (check_result facade_expectation) (fn () =>
  "the public expect check did not raise on a mismatch") (fn () => ()) ()
val _ = require_msg (check_result facade_parallel) (fn () =>
  "the public parallel facade did not find a counterexample")
  (fn () => ()) ()
val _ = require_msg (check_result facade_tactic_fails) (fn () =>
  "REFUTE_TAC did not fail on a refutable goal") (fn () => ()) ()
val _ = require_msg (check_result facade_tactic_allows_unknown) (fn () =>
  "REFUTE_TAC blocked on an inconclusive goal") (fn () => ()) ()
val _ = require_msg (check_result facade_assumptions) (fn () =>
  "refute_goal did not handle assumptions or no_assms") (fn () => ()) ()

val _ = if selftest_level >= 2 then corpus_potential () else ()

val _ = exit_count0 erc
