signature Refute_ModelFinder_HOL = sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

  type kname = KernelSig.kernelname

  type const_table = term list KNametab.table

  type special_fun = (term * int list * term list) * term

  type wf_cache = (term * (bool * bool)) list

  type iterator_info =
    {pred : term, preds : term list, arg_tys : hol_type list,
     arg_tyss : hol_type list list, gfp : bool, token : string}

  type iterator_table = (hol_type * iterator_info) list ref

  type skolem_dependency = Refute_Skolem.dependency

  type skolem_info = Refute_Skolem.info

  datatype fixpoint_kind = Lfp | Gfp | NoFp

  type fixpoint_group =
    {kind : fixpoint_kind,
     stem : string,
     members : kname list,
     rules : term list,
     cases : term list}

  type fixpoint_cache = (kname * fixpoint_group option) list

  type type_operator = {Thy : string, Tyop : string}

  type ersatz = {original : kname, replacement : kname}

  type codatatype_registration =
    {tyop : type_operator, case_const : term, constructors : term list,
     witness : thm option}

  type quotient_registration =
    {qty : hol_type, rty : hol_type, abs : term, rep : term,
     equiv_thm : thm}

  type typedef_info =
    {ty : hol_type, rty : hol_type, abs : term, rep : term,
     pred : term, inverse_axioms : term list, univ : bool}

  type frac_info = {tyop : type_operator, ersatz : ersatz list}

  type mf_context =
    {max_bisim_depth : int,
     boxes : (hol_type option * bool option) list,
     wfs : (term option * bool option) list,
     user_axioms : bool option,
     debug : bool,
     whacks : term list,
     binary_ints : bool option,
     destroy_constrs : bool,
     specialize : bool,
     star_linear_preds : bool,
     total_consts : bool option,
     needs : term list option,
     tac_timeout : Time.time,
     evals : term list,
     case_names : (kname * (int * int)) list,
     def_tables : const_table * const_table,
     nondef_table : const_table,
     nondefs : term list,
     simp_table : const_table ref,
     psimp_table : const_table,
     choice_spec_table : const_table,
     intro_table : const_table ref,
     case_table : const_table ref,
     fixpoint_cache : fixpoint_cache ref,
     iterator_table : iterator_table,
     ersatz_table : ersatz list,
     whack_weakening : bool ref,
     choice_guard_inserted : bool ref,
     choice_empty_cache : (term * bool) list ref,
     choice_predicate_attempts : int ref,
     prefix_origins : (string * hol_type) list ref,
     skolems : skolem_info list ref,
     special_funs : special_fun list ref,
     wf_cache : wf_cache ref,
     constr_cache : (hol_type * term list) list ref}

  val const_key : term -> {Name : string, Thy : string}
  val same_key : KernelSig.kernelname -> KernelSig.kernelname -> bool
  val add_simps : 'a list KNametab.table ref -> term -> 'a list -> unit
  val term_under_def : term -> term
  val num_type : hol_type
  val int_type : hol_type
  val unsigned_bit_type : hol_type
  val signed_bit_type : hol_type
  val bisim_iterator_type : hol_type
  val unsigned_bitword_type : hol_type
  val signed_bitword_type : hol_type
  val is_bit_type : hol_type -> bool
  val is_bitword_type : hol_type -> bool
  val binarize_nat_and_int_in_type : hol_type -> hol_type
  val retype_constant : string -> term -> hol_type -> term
  val restore_retyped_constant : term -> term
  val numeric_type_card : hol_type -> int option
  val word_dimension : hol_type -> int option
  val word_width : hol_type -> int
  val is_word_type : hol_type -> bool
  val is_word_literal : term -> bool
  val word_op_dimension : hol_type -> int option
  val char_card : int
  val is_char_type : hol_type -> bool
  val is_exact_carrier_type : hol_type -> bool
  val is_char_literal : term -> bool
  val is_char_op_type : hol_type -> bool
  val order_consts : (KernelSig.kernelname * hol_type * bool) list
  val order_const_names : string list
  val word_built_in_consts : (KernelSig.kernelname * int) list
  val char_built_in_consts : (KernelSig.kernelname * int) list
  val arity_of_built_in_const : term -> int option
  val is_built_in_const : term -> bool
  val raw_fixpoint_kind : term -> fixpoint_kind
  val nondef_props_for_const : term list KNametab.table -> term -> term list
  val def_of_const : mf_context -> term -> term option
  val fixpoint_kind_of_rhs : term -> fixpoint_kind
  val all_nondefs_of : unit -> term list
  val is_poly_term : term -> bool
  val choice_spec_props_for_const : mf_context -> term -> term list
  val is_choice_spec_fun : mf_context -> term -> bool
  val fixpoint_kind_of_const : mf_context -> term -> fixpoint_kind
  val is_fixpoint_bound_const : term -> bool
  val is_raw_inductive_pred : mf_context -> term -> bool
  val instantiated_fixpoint_group :
    mf_context -> term ->
    {cases : term list,
     kind : fixpoint_kind,
     members : term list,
     rules : term list,
     stem : string} option
  val is_raw_equational_fun : mf_context -> term -> bool
  val is_equational_fun : mf_context -> term -> bool
  val equational_fun_axioms : mf_context -> term -> term list

  type intro_triple =
    {variables : term list, side : term list,
     main : term list, conclusion : term}

  val tuple_type : hol_type list -> hol_type
  val joint_intro_triple_for : term list -> term -> intro_triple option
  val const_match : term * term -> bool
  val is_well_founded_inductive_pred : mf_context -> term -> bool
  val fixpoint_refusal_reason : mf_context -> term -> string option
  val first_fixpoint_refusal : mf_context -> term -> string option
  val print_wf_cache : mf_context -> unit
  val is_equational_fun_surely_complete : mf_context -> term -> bool
  val register_codatatype : codatatype_registration -> unit
  val register_quotient : quotient_registration -> unit
  val raw_typedef_data : hol_type -> {pred : term, rty : hol_type} option
  val register_typedef :
    {abs : term, absrep_thms : thm list, rep : term, ty : hol_type} -> unit
  val register_frac_type : frac_info -> unit
  val rat_frac_registration : frac_info
  val real_frac_registration : frac_info
  val is_fun_type : hol_type -> bool
  val is_pair_type : hol_type -> bool
  val is_higher_order_type : hol_type -> bool
  val factor_types : hol_type -> hol_type list
  val int_of_numeral : Arbint.int -> int
  val is_funbox_type : hol_type -> bool
  val is_pairbox_type : hol_type -> bool
  val is_fp_iterator_type : hol_type -> bool
  val is_bisim_iterator_type : hol_type -> bool
  val is_lfp_iterator_type : hol_type -> bool
  val is_gfp_iterator_type : hol_type -> bool
  val is_iterator_type : hol_type -> bool
  val iterator_info_for_type : mf_context -> hol_type -> iterator_info option
  val refresh_iterator_arg_types : mf_context -> term list -> unit

  datatype iterator_marker = IteratorZero | IteratorSuc

  val iterator_marker_of_term : mf_context -> term -> iterator_marker option
  val unrolled_inductive_pred_const : mf_context -> bool -> term -> term
  val fixpoint_bound_const : mf_context -> bool -> term -> term
  val boxed_type_args : hol_type -> hol_type list
  val unarize_unbox_etc_type : hol_type -> hol_type
  val uniterize_unarize_unbox_etc_type : hol_type -> hol_type
  val type_matches_unboxed : hol_type * hol_type -> bool

  datatype box_position =
      InConstr | InSel | InExpr | InPair | InFunLHS | InFunRHS1 | InFunRHS2

  val is_boolean_type : hol_type -> bool
  val is_integer_type : hol_type -> bool
  val box_type : mf_context -> box_position -> hol_type -> hol_type
  val is_codatatype : hol_type -> bool
  val is_quot_type : hol_type -> bool
  val typedef_for_type : hol_type -> typedef_info option
  val is_typedef : hol_type -> bool
  val is_univ_typedef : hol_type -> bool
  val binarization_veto_test : unit -> term -> bool
  val is_data_type : hol_type -> bool
  val harvest_quotient : hol_type -> bool
  val harvest_typedef : hol_type -> bool
  val harvest_registrations :
    unit ->
    {quotients : hol_type list,
     theories_scanned : string list,
     typedefs : hol_type list}
  val data_type_constrs : mf_context -> hol_type -> term list
  val binarized_and_boxed_data_type_constrs :
    mf_context -> bool -> hol_type -> term list
  val raw_constructor_name : term -> string
  val is_nonfree_constr : term -> bool
  val is_constructor_pattern_gen : ('a -> term -> bool) -> 'a -> term -> bool
  val is_constructor_pattern_formula_gen :
    (term list -> term -> bool) -> term -> bool
  val is_free_constr : term -> bool
  val is_constr : term -> bool
  val is_rep_fun : term -> bool
  val mate_of_rep_fun : term -> term
  val first_unregistered_typedef : term list -> hol_type option
  val unregistered_typedef_reason : term list -> string option
  val is_record_get : term -> bool
  val is_named_const : KernelSig.kernelname -> term -> bool
  val is_descr : term -> bool
  val numeral_value : term -> Arbint.int option
  val register_ersatz : ersatz -> unit
  val constructor_name : term -> string
  val constructor_arg_types : term -> hol_type list
  val constructor_result_type : term -> hol_type
  val is_pair_constructor : term -> bool
  val binarized_and_boxed_nth_sel_for_constr :
    mf_context -> bool -> term -> int -> term
  val binarized_and_boxed_constr_for_sel : mf_context -> bool -> term -> term
  val is_suc_constructor : term -> bool
  val s_betapply : term * term -> term
  val s_betapplys : term * term list -> term
  val discriminate_value : mf_context -> term -> term -> term
  val select_nth_constr_arg :
    mf_context -> term -> term -> int -> hol_type -> term
  val generated_selector_argument : term -> term -> term option
  val eta_contract : term -> term
  val coerce_term : mf_context -> hol_type -> hol_type -> term -> term
  val unarize_unbox_etc_term : term -> term
  val optimized_quot_type_axioms : mf_context -> hol_type -> term list
  val optimized_typedef_axioms : hol_type -> term list
  val optimized_inverse_axioms_for_rep_fun : term -> term list
  val codatatype_bisim_axioms : mf_context -> hol_type -> term list
  val assignment_lookup : (''a * 'b) list -> ''a -> 'b option
  val card_of_type : (hol_type * int) list -> hol_type -> int
  val bounded_card_of_type :
    int -> int -> (hol_type * int) list -> hol_type -> int
  val bounded_exact_card_of_type :
    mf_context -> hol_type list -> int -> int -> (hol_type * int) list ->
    hol_type -> int
  val typical_card_of_type : hol_type -> int
  val is_finite_type : mf_context -> hol_type -> bool
  val eta_expand : term -> int -> term
  val unfold_defs_in_term : mf_context -> term -> term
  val make_context : Refute_Core.mf_config -> term list -> mf_context
end
