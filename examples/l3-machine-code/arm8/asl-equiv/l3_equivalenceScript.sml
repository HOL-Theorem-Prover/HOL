open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory updateTheory listTheory
     arithmeticTheory integerTheory
open wordsLib bitstringLib integer_wordLib intLib finite_mapLib
     pairLib optionLib combinLib
open l3_equivalence_lemmasTheory


val _ = new_theory "l3_equivalence";
val _ = set_grammar_ancestry ["arm8_step", "arm8", "armv86a_termination"];

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.prefer_num();

val _ = Globals.show_assums := false;

(******************************************************************************)

Definition flag_rel_def:
  flag_rel b (w : 1 word) ⇔ (w = v2w [b])
End

Definition pstate_rel_def:
  pstate_rel (l3 : arm8$ProcState) (asl : armv86a_types$ProcState) ⇔
    l3.EL = asl.ProcState_EL ∧
    flag_rel l3.SPS asl.ProcState_SP ∧
    flag_rel l3.N asl.ProcState_N ∧
    flag_rel l3.Z asl.ProcState_Z ∧
    flag_rel l3.C asl.ProcState_C ∧
    flag_rel l3.V asl.ProcState_V
End

Definition tcr_el1_rel_def:
  tcr_el1_rel (l3 : TCR_EL1) (asl : 64 word) ⇔
    reg'TCR_EL1 l3 = asl
End

(* L3 TCR_EL2 is 32-bits, though 64-bit with upper 32 bits clear in spec *)
Definition tcr_el2_3_rel_def:
  tcr_el2_3_rel (l3 : TCR_EL2_EL3) asl ⇔
    reg'TCR_EL2_EL3 l3 = (31 >< 0) asl
End

(* XXX version difference here - L3 SCTLRs are only 32-bit *)
Definition sctlr_rel_def:
  sctlr_rel (l3 : arm8$SCTLRType) (asl : 64 word) ⇔
    reg'SCTLRType l3 = (31 >< 0) asl
End

Definition read_rel_def:
  read_rel rel l3 asl asl_reg ⇔
    rel l3 (asl_reg.read_from asl)
End

Definition reg_rel_def:
  reg_rel (l3 : word5 -> word64) (asl : regstate) ⇔
    l3 (n2w 31) = 0w ∧
    LENGTH (R_ref.read_from asl) = 32 ∧
    ∀n. n ≤ 31 ⇒ l3 (n2w n) = EL n (R_ref.read_from asl)
End

Definition mem_rel_def:
  mem_rel (l3 : word64 -> word8) (asl : num |-> bitU list) tags =
    ∀n. FLOOKUP tags n = SOME B0
      ⇒ ∃byt.
          FLOOKUP asl n = SOME byt ∧
          l3 (n2w n) = vec_of_bits byt
End

(* what to do about tagstate? *)
Definition state_rel_def:
  state_rel (l3 : arm8_state) (asl : regstate sequential_state) ⇔
    read_rel pstate_rel l3.PSTATE asl.regstate PSTATE_ref ∧
    read_rel sctlr_rel l3.SCTLR_EL1 asl.regstate SCTLR_EL1_ref ∧
    read_rel sctlr_rel l3.SCTLR_EL2 asl.regstate SCTLR_EL2_ref ∧
    read_rel sctlr_rel l3.SCTLR_EL3 asl.regstate SCTLR_EL3_ref ∧
    read_rel ($=) l3.PC asl.regstate PC_ref ∧
    read_rel ($=) l3.SP_EL0 asl.regstate SP_EL0_ref ∧
    read_rel ($=) l3.SP_EL1 asl.regstate SP_EL1_ref ∧
    read_rel ($=) l3.SP_EL2 asl.regstate SP_EL2_ref ∧
    read_rel ($=) l3.SP_EL3 asl.regstate SP_EL3_ref ∧
    read_rel tcr_el1_rel l3.TCR_EL1 asl.regstate TCR_EL1_ref ∧
    read_rel tcr_el2_3_rel l3.TCR_EL2 asl.regstate TCR_EL2_ref ∧
    read_rel tcr_el2_3_rel l3.TCR_EL3 asl.regstate TCR_EL3_ref ∧
    reg_rel l3.REG asl.regstate ∧
    mem_rel l3.MEM asl.memstate asl.tagstate ∧
    l3.exception = NoException
End

Definition l3_models_asl_def:
  l3_models_asl opcode ⇔
    Decode opcode ≠ Unallocated ∧
    ∀ l3 asl l3'.
      state_rel l3 asl ∧
      Run (Decode opcode) l3 = l3' ∧
      l3'.exception = NoException
    ⇒ case seqS (write_regS SEE_ref (~1)) (ExecuteA64 opcode) asl of
        | (Value _, asl') => state_rel l3' asl'
        | _ => F
End

Definition l3_models_asl_instr_def:
  l3_models_asl_instr instr ⇔
    case Encode instr of
      | ARM8 opcode => l3_models_asl opcode
      | _ => F
End

(******************************************************************************)

(***** stateful simpset *****)
val armv86a_ss = rewrites [
  combinTheory.I_THM,
  lemTheory.w2ui_def,
  sail2_valuesTheory.make_the_value_def,
  sail2_valuesTheory.nat_of_int_def,
  sail2_operators_mwordsTheory.zeros_def,
  sail2_operators_mwordsTheory.concat_vec_def,
  armv86aTheory.Zeros_def,
  armv86aTheory.IsZero_def,
  armv86aTheory.id_def,
  lem_machine_wordTheory.size_itself_def,
  sail2_valuesTheory.size_itself_int_def,
  armv86aTheory.ZeroExtend1_def,
  sail2_operators_mwordsTheory.zero_extend_def,
  sail2_operators_mwordsTheory.not_vec_def,
  EL0_def, EL1_def, EL2_def, EL3_def,
  place_slice_def, shiftl, shiftr,
  sail2_operators_mwordsTheory.extz_vec_def,
  sail2_operators_mwordsTheory.and_vec_def,
  sail2_operators_mwordsTheory.not_vec_def,
  sail2_operators_mwordsTheory.vector_truncate_def
  ];

val _ = augment_srw_ss [
    bitstringLib.v2w_n2w_ss,
    bitstringLib.BITSTRING_GROUND_ss,
    wordsLib.WORD_ss,
    armv86a_ss
  ];

(***** current compset *****)
(*
val _ = computeLib.add_convs [
  (wordsSyntax.word_extract_tm, 3, bitstringLib.extract_v2w_CONV)
  ];
WORD_EXTRACT_ss
*)
val _ = computeLib.add_convs [
    (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)
  ];


(***** rewrites *****)
val unfold_ss =
  simpLib.named_rewrites "unfold_ss"
    [l3_models_asl_instr_def, l3_models_asl_def];

val encode_ss =
  simpLib.named_rewrites "encode_ss" [
    Encode_def,
    e_data_def, e_branch_def, e_load_store_def, e_sf_def, e_LoadStoreImmediate_def,
    EncodeLogicalOp_def, NoOperation_def,
    ShiftType2num_thm, SystemHintOp2num_thm, ShiftType2num_thm
  ];

val monad_ss =
  simpLib.named_rewrites "monad_ss" [
    sail2_state_monadTheory.seqS_def,
    sail2_state_monadTheory.returnS_def,
    sail2_state_monadTheory.bindS_def,
    sail2_state_monadTheory.read_regS_def,
    sail2_state_monadTheory.readS_def,
    sail2_state_monadTheory.write_regS_def,
    sail2_state_monadTheory.updateS_def,
    sail2_state_monadTheory.chooseS_def,
    sail2_state_monadTheory.assert_expS_def,
    sail2_stateTheory.and_boolS_def,
    sail2_stateTheory.or_boolS_def,
    sail2_stateTheory.internal_pickS_def
  ];

val asl_word_ss =
  simpLib.named_rewrites "asl_word_ss" [
    sail2_operators_mwordsTheory.subrange_vec_dec_def,
    sail2_operators_mwordsTheory.subrange_vec_inc_def,
    sail2_operators_mwordsTheory.update_subrange_vec_dec_def,
    sail2_operators_mwordsTheory.update_subrange_vec_inc_def,
    sail2_valuesTheory.update_list_def,
    sail2_valuesTheory.update_list_inc_def,
    sail2_valuesTheory.update_list_dec_def,
    sail2_valuesTheory.access_list_def,
    sail2_valuesTheory.access_list_inc_def,
    sail2_valuesTheory.access_list_dec_def,
    sail2_valuesTheory.subrange_list_def,
    sail2_valuesTheory.subrange_list_dec_def,
    sail2_valuesTheory.subrange_list_inc_def,
    sail2_operators_mwordsTheory.access_vec_dec_def,
    sail2_valuesTheory.access_bv_dec_def,
    sail2_operators_mwordsTheory.vec_of_bits_def,
    sail2_valuesTheory.of_bits_failwith_def,
    sail2_valuesTheory.maybe_failwith_def,
    wordsTheory.bit_field_insert_def,
    preludeTheory.undefined_bitvector_def |>
      REWRITE_RULE [Once FUN_EQ_THM, sail2_state_monadTheory.returnS_def],
    armv86aTheory.integer_subrange_def,
    sail2_operators_mwordsTheory.get_slice_int_def,
    sail2_operatorsTheory.get_slice_int_bv_def,
    l3_equivalence_lemmasTheory.bools_of_int_def,
    sail2_valuesTheory.add_one_bool_ignore_overflow_def,
    sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
  ];

val [unfold_rws, encode_rws, monad_rws, asl_word_rws] =
  map SF [unfold_ss, encode_ss, monad_ss, asl_word_ss];

(***** L3 tactics *****)
fun l3_eval thms = SIMP_RULE (srw_ss()) [] o
                   computeLib.CBV_CONV (arm8_compset thms);

fun l3_eval_tac thms = CONV_TAC (l3_eval thms);

local
  fun get tm =
    Option.getOpt
      (Lib.total lhs tm,
       if boolSyntax.is_neg tm then boolSyntax.F else boolSyntax.T)
in
  fun mk_blast_thm l =
    let
      val lty = Term.type_of l
      val ty = wordsSyntax.dest_word_type lty
      val r =
        blastLib.BBLAST_CONV (boolSyntax.mk_eq (l, Term.mk_var ("_", lty)))
        |> concl |> rhs |> strip_conj |> List.map get |> List.rev
        |> (fn l => listSyntax.mk_list (l, Type.bool))
        |> (fn tm => bitstringSyntax.mk_v2w (tm, ty))
    in
      blastLib.BBLAST_PROVE (boolSyntax.mk_eq (r, l)) |> SIMP_RULE bool_ss []
    end
end

(* Takes an opcode (which may be multiple concatenated fields) and attempts to
   decode fully, simplifying result. Uses arm8_stepLib.arm8_decode. *)
fun l3_decode tm =
  let val _ = type_of tm |>
              assert (fn ty => wordsSyntax.dest_word_type ty =
                        fcpSyntax.mk_numeric_type (Arbnum.fromInt 32))
      fun remove x [] = []
        | remove x (y::ys) = if x ~~ y then remove x ys else (y::remove x ys)
      fun remove_dups [] = []
        | remove_dups (x::xs) = x::(remove_dups (remove x xs));
      val blast_thm = mk_blast_thm tm
      val opc_list = concl blast_thm |> lhs
      val sub_blast_thms = if is_var tm then [] else
                           map mk_blast_thm (remove_dups (find_terms is_var tm))
      val decode_thm = arm8_decode (rand opc_list) |>
                       REWRITE_RULE sub_blast_thms
  in REWRITE_RULE [blast_thm] decode_thm end
  handle _ => raise (mk_HOL_ERR "l3_decode" "l3_decode" "l3_equivalenceTheory");

(* Searches for `Decode opc` in goal and applies l3_decode to `opc` *)
val l3_decode_tac =
  let val decode_tm = prim_mk_const {Name = "Decode", Thy = "arm8"}
      fun find_decode tm = is_comb tm andalso
                           same_const (strip_comb tm |> fst) decode_tm
      fun apply_l3_decode tm = assume_tac (l3_decode (rand tm)) >> gvs[]
  in goal_term (fn tm => apply_l3_decode (find_term find_decode tm)) end

(* Takes `Decode opc = _` and gives possible next steps.
   Uses arm8_stepLib.arm8_next, arm8_stepLib.arm8_run. *)
fun l3_run tm =
  let val decode_tm = prim_mk_const {Name = "Decode", Thy = "arm8"}
      val _ = assert (fn tm => is_eq tm andalso
                      same_const (lhs tm |> strip_comb |> fst) decode_tm) tm
      (* mk_thm below should be OK - arm8_run immediately uses concl *)
      val run_thm = arm8_run (mk_thm ([], tm))
      val to_expand_tm = run_thm |> SPEC_ALL |> concl |> rhs |> rator
      val expand_thms = arm8_next to_expand_tm
  in map (fn thm => REWRITE_RULE [thm] run_thm) expand_thms end
  handle _ => raise (mk_HOL_ERR "l3_run" "l3_run" "l3_equivalenceTheory");

(* Searches for `Decode opc = _` in assumptions and applies l3_run.
   Does not do anything to handle multiple possible next steps. *)
val l3_run_tac =
  qpat_assum `Decode _ = _` (fn thm =>
    map_every (assume_tac o DISCH_ALL) (l3_run (concl thm)) >> gvs[]);


(***** custom compset *****)
local

  fun add_type cmp =
    computeLib.add_datatype_info cmp o Option.valOf o TypeBase.fetch
  fun add_types cmp l = List.app (add_type cmp) l

  val tyvars = [alpha, beta, gamma, delta, etyvar, ftyvar]
  fun mk_cmp_type (thy, (name, arity)) =
    mk_thy_type {Args = List.take (tyvars, arity), Thy = thy, Tyop = name}
  fun add_all_types cmp thy =
    add_types cmp (map (mk_cmp_type o pair thy) (types thy))

  fun add_defs cmp defs = computeLib.add_thms defs cmp
    handle (HOL_ERR _) => ((* PolyML.print defs;*) ())
  fun not_contains_tydef thm = thm |> concl |> find_terms
    (same_const (prim_mk_const {Name = "TYPE_DEFINITION", Thy = "bool"})) |>
    null
  fun add_all_defs cmp thy = app (add_defs cmp o single)
    (definitions thy |> map snd |> filter not_contains_tydef)

  val thys = [
      "lem_machine_word", "lem",
      "sail2_instr_kinds",
      "sail2_operators_bitlists", "sail2_operators_mwords", "sail2_operators",
      "sail2_stateAuxiliary", "sail2_state_monad", "sail2_state",
      "sail2_string", "sail2_valuesAuxiliary", "sail2_values",
      "prelude", "armv86a_types"
    ]
  (*
  val thys = [
      "lem_assert_extra", "lem_basic_classes", "lem_bool", "lem_either",
      "lem_function_extra", "lem_function",
      "lem_list_extra_sail", "lem_list", "lem_machine_word",
      "lem_map_extra", "lem_map", "lem_maybe_extra", "lem_maybe",
      "lem_num_extra", "lem_num", "lem_pervasives_extra_sail",
      "lem_pervasives_sail", "lem_relation", "lem", "lem_set_extra_sail",
      "lem_set_helpers", "lem_set", "lem_show_extra", "lem_show",
      "lem_sorting", "lem_string_extra_sail", "lem_string_sail",
      "lem_tuple", "lem_word",

      "sail2_instr_kinds", "sail2_operators_bitlists", "sail2_operators_mwords",
      "sail2_operators", "sail2_prompt_monad", "sail2_prompt",
      "sail2_stateAuxiliary", "sail2_state_monad", "sail2_state",
      "sail2_string", "sail2_valuesAuxiliary", "sail2_values",

      "prelude", "armv86a_types"
    ]
    *)
in

  val cmp = reduceLib.num_compset();
  val _ = pairLib.add_pair_compset cmp;
  val _ = optionLib.OPTION_rws cmp;
  val _ = combinLib.add_combin_compset cmp;
  val _ = wordsLib.add_words_compset true cmp;
  (* val _ = integer_wordLib.add_integer_word_compset cmp; *)
  val _ = intReduce.add_int_compset cmp;
  val _ = cmp |> computeLib.add_conv
    (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV);
  val _ = cmp |> computeLib.add_conv
    (``$= : α word -> α word -> bool``, 2, QCHANGED_CONV blastLib.BBLAST_CONV);
  val _ = bitstringLib.add_bitstring_compset cmp; (* has to come after BBLAST_CONV *)
  val _ = app (add_all_types cmp) thys;
  val _ = app (add_all_defs cmp) thys;
  val _ = cmp |> computeLib.add_thms [
              armv86aTheory.ExecuteA64_def,
              armv86aTheory.DecodeA64_def,
              armv86aTheory.Zeros_def
            ];
  (* don't look at conditional branches before guard is fully evaluated *)
  (* val _ = computeLib.set_skip cmp boolSyntax.conditional (SOME 1) *)
  val CEVAL = computeLib.CBV_CONV cmp

end

(***** ASL tactics *****)
(* Uses `eval` to execute opcode `tm`. *)
fun asl_execute_helper eval tm =
  let val _ = type_of tm |>
              assert (fn ty => wordsSyntax.dest_word_type ty =
                        fcpSyntax.mk_numeric_type (Arbnum.fromInt 32))
      val blast_thm = mk_blast_thm tm
      val v2w_tm = concl blast_thm |> lhs
      fun remove x [] = []
        | remove x (y::ys) = if x ~~ y then remove x ys else (y::remove x ys)
      fun remove_dups [] = []
        | remove_dups (x::xs) = x::(remove_dups (remove x xs));
      val sub_blast_thms = if is_var tm then [] else
                           map mk_blast_thm (remove_dups (find_terms is_var tm))
      val eval_tm = ``seqS (write_regS SEE_ref (~1)) (ExecuteA64 ^v2w_tm) asl``
  in eval eval_tm |> GEN_ALL |> REWRITE_RULE (blast_thm::sub_blast_thms) end
  handle _ => raise (
    mk_HOL_ERR "asl_execute" "asl_execute" "l3_equivalenceTheory");

val asl_execute = asl_execute_helper EVAL;
val asl_cexecute = asl_execute_helper CEVAL;

(* Looks for `ExecuteA64 opc` and assumes `asl_execute eval opc` *)
fun asl_execute_tac_helper eval =
  let val ExecuteA64_tm = prim_mk_const {Name = "ExecuteA64", Thy = "armv86a"};
      fun find_ExecuteA64 tm = is_comb tm andalso
                               same_const (strip_comb tm |> fst) ExecuteA64_tm
      fun apply_asl_execute tm = assume_tac (asl_execute_helper eval (rand tm))
  in
    goal_term
      (fn tm => apply_asl_execute (find_term find_ExecuteA64 tm))
  end;

val asl_execute_tac = asl_execute_tac_helper EVAL;
val asl_cexecute_tac = asl_execute_tac_helper CEVAL;

(* Rewrites using various state theorems and state relation *)
fun state_rel_tac thms =
  gvs ([
    flag_rel_def,
    pstate_rel_def,
    tcr_el1_rel_def, reg'TCR_EL1_def,
    tcr_el2_3_rel_def, reg'TCR_EL2_EL3_def,
    sctlr_rel_def, reg'SCTLRType_def,
    read_rel_def,
    reg_rel_def, R_ref_def, PSTATE_ref_def, SCTLR_EL1_ref_def,
      SCTLR_EL1_ref_def, SCTLR_EL2_ref_def, SCTLR_EL3_ref_def,
      PC_ref_def,
      SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def,
      TCR_EL1_ref_def, TCR_EL2_ref_def, TCR_EL3_ref_def,
    mem_rel_def,
    state_rel_def,
    sail2_operators_mwordsTheory.vec_of_bits_def,
    sail2_valuesTheory.of_bits_failwith_def,
    sail2_valuesTheory.maybe_failwith_def
    ] @ thms) >>
  rw[flookup_thm, FLOOKUP_UPDATE, APPLY_UPDATE_THM] >> gvs[];

(******************************************************************************)

Theorem l3_models_asl_NoOperation:
  l3_models_asl_instr NoOperation
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >>
  l3_run_tac >>
  asl_execute_tac >> gvs[] >>
  state_rel_tac []
QED

Theorem l3_models_asl_MoveWideOp_Z:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, r)))
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >>
  l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def, monad_rws] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[asl_word_rws, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `hw` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  Cases_on `r = 31w` >> gvs[monad_rws] >- (state_rel_tac []) >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  state_rel_tac[asl_word_rws]
  >- (
    CCONTR_TAC >>
    qpat_x_assum `_ < 0` mp_tac >> gvs[] >>
    Cases_on_word_value `hw` >> gvs[]
    )
  >- (
    gvs[EL_LUPDATE] >>
    `Num (ABS (((&w2n ((hw @@ (0b0w :word4)) :word6)) :int) + (15 :int))) =
      w2n (((hw :word2) @@ (0b0w :word4)) :word6) + 15` by (
        Cases_on_word_value `hw` >> gvs[]) >> gvs[]
    )
  >> (
    gvs[EL_LUPDATE] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (BasicProvers.VAR_EQ_TAC) >>
    gvs[n2w_w2n]
    )
QED

Theorem l3_models_asl_MoveWideOp_N:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, r)))
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >>
  l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def, monad_rws] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[asl_word_rws, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `hw` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  Cases_on `r = 31w` >> gvs[monad_rws] >- (state_rel_tac []) >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >> state_rel_tac[asl_word_rws]
  >- (
    CCONTR_TAC >>
    qpat_x_assum `_ < 0` mp_tac >> gvs[] >>
    Cases_on_word_value `hw` >> gvs[]
    )
  >- (
    gvs[EL_LUPDATE] >>
    `Num (ABS (((&w2n ((hw @@ (0b0w :word4)) :word6)) :int) + (15 :int))) =
      w2n (((hw :word2) @@ (0b0w :word4)) :word6) + 15` by (
        Cases_on_word_value `hw` >> gvs[]) >> gvs[]
    )
  >> (
    gvs[EL_LUPDATE] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (BasicProvers.VAR_EQ_TAC) >>
    gvs[n2w_w2n]
    )
QED

Theorem l3_models_asl_MoveWideOp_K:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_K, hw, i, r)))
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >>
  l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def, monad_rws] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[X_read_def, asl_word_rws, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >>
  Cases_on `r = 31w` >> gvs[monad_rws]
  >- (
    reverse IF_CASES_TAC >- (Cases_on_word_value `hw` >> gvs[]) >>
    gvs[X_set_def, monad_rws] >>
    state_rel_tac []
    ) >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  reverse IF_CASES_TAC
  >- (Cases_on_word_value `hw` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >> state_rel_tac[asl_word_rws]
  >- (
    CCONTR_TAC >>
    qpat_x_assum `_ < 0` mp_tac >> gvs[] >>
    Cases_on_word_value `hw` >> gvs[]
    )
  >- (
    gvs[EL_LUPDATE] >>
    `Num (ABS (((&w2n ((hw @@ (0b0w :word4)) :word6)) :int) + (15 :int))) =
      w2n (((hw :word2) @@ (0b0w :word4)) :word6) + 15` by (
        Cases_on_word_value `hw` >> gvs[]) >> gvs[] >>
    `∀ w : 64 word. (63 >< 0) w = (w2w w : 64 word)` by (
      strip_tac >> irule EXTRACT_ALL_BITS >> gvs[]) >> gvs[]
    )
  >> (
    gvs[EL_LUPDATE] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (VAR_EQ_TAC) >>
    gvs[n2w_w2n]
    )
QED

Theorem l3_asl_AddWithCarry:
  ∀x y carry_b carry_v.
    flag_rel carry_b carry_v
  ⇒ armv86a$AddWithCarry x y carry_v =
     (I ## (λ(a,b,c,d).v2w [a;b;c;d])) (arm8$AddWithCarry (x, y, carry_b))
Proof
  rw[flag_rel_def] >> gvs[armv86aTheory.AddWithCarry_def, AddWithCarry_def] >>
  simp[integer_subrange_def, asl_word_rws] >> conj_asm1_tac
  >- (
    simp[lemTheory.w2ui_def, INT_ADD] >>
    simp[w2n_v2w, v2n, bitTheory.MOD_2EXP_def] >>
    qmatch_goalsub_abbrev_tac `b MOD 2` >>
    `b MOD 2 = b` by (unabbrev_all_tac >> rw[]) >> simp[] >>
    map_every qmatch_goalsub_abbrev_tac [`n2w n`, `TAKE l`] >>
    qspec_then `fixwidth l (n2v n)` mp_tac TAKE_LENGTH_ID >>
    rewrite_tac[length_fixwidth] >> disch_then SUBST_ALL_TAC >>
    unabbrev_all_tac >> simp[v2w_fixwidth]
    ) >>
  simp[lemTheory.w2ui_def, INT_ADD] >>
  simp[w2n_v2w, v2n, bitTheory.MOD_2EXP_def] >>
  qmatch_goalsub_abbrev_tac `b MOD 2` >>
  `b MOD 2 = b` by (unabbrev_all_tac >> rw[]) >> simp[] >>
  qmatch_goalsub_abbrev_tac `n2w stuff` >>
  DEP_REWRITE_TAC[HD_MAP] >> conj_asm1_tac
  >- (
    qsuff_tac `LENGTH (w2v (n2w stuff)) ≠ 0` >- rw[] >>
    rewrite_tac[length_w2v] >> assume_tac EXISTS_HB >> gvs[]
    ) >>
  simp[sail2_valuesTheory.just_list_def] >>
  unabbrev_all_tac >> blastLib.BBLAST_TAC >> rw[] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `w2v stuff` >>
  qspecl_then [`stuff`,`0`] mp_tac el_w2v >> simp[]
QED

(* TODO this proof is tedious and repetitive - automation needed *)
Theorem l3_models_asl_AddSubImmediate:
  ∀b1 b2 i r2 r1.
    (i && ¬0b111111111111w ≠ 0b0w ⇒ i && ¬0b111111111111000000000000w = 0b0w)
  ⇒ l3_models_asl_instr
      (Data (AddSubImmediate@64 (1w, b1, b2, i, r2, r1)))
Proof
  rw[unfold_rws] >> gvs[encode_rws] >>
  reverse $ rpt IF_CASES_TAC >> gvs[]
  >- (
    `i = (0w : 40 word) @@ ((23 >< 12) i : 12 word) @@ (0w : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    qpat_x_assum `_ && i = _` kall_tac >>
    rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
    l3_decode_tac >> rw[] >>
    l3_run_tac >> gvs[] >> pop_assum kall_tac >>
    asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL0" = l3.SP_EL0` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL1" = l3.SP_EL1` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL2" = l3.SP_EL2` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL3" = l3.SP_EL3` by state_rel_tac[] >>
    `flag_rel (l3.PSTATE.SPS)
      ((asl.regstate.ProcState_reg "PSTATE").ProcState_SP)` by
      state_rel_tac [] >>
    `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL =
        l3.PSTATE.EL` by state_rel_tac[] >>
    gvs[
      decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
      ] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[dfn'AddSubImmediate_def] >>
    `flag_rel T 0b1w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    `flag_rel F 0b0w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    strip_tac >> strip_tac >> simp[COND_RATOR, monad_rws] >>
    `(r1 = 31w ⇔ w2n r1 = 31) ∧ (r2 = 31w ⇔ w2n r2 = 31)` by (
        rw[] >> eq_tac >> rw[] >> irule $ iffLR w2n_11 >>
        `w2n (0b11111w : 5 word) = 31` by simp[] >>
        pop_assum SUBST_ALL_TAC >> simp[]) >>
    `w2n r1 ≤ 31 ∧ w2n r2 ≤ 31` by (
      rw[] >> rename1 `w2n a` >>
      assume_tac (w2n_lt |> INST_TYPE [alpha |-> ``:5``]) >>
      pop_assum $ qspec_then `a` assume_tac >> drule SUB_LESS_OR >> simp[]) >>
    simp[]
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, T)` >> gvs[] >>
        simp[write'X_rwt, X_set_def] >>
        reverse IF_CASES_TAC >> gvs[monad_rws]
        >- (
          PairCases_on `r` >> simp[SetTheFlags_def] >>
          state_rel_tac[] >> blastLib.BBLAST_TAC
          ) >>
        PairCases_on `r` >> simp[SetTheFlags_def, int_ge, monad_rws, R_ref_def] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        reverse (Cases_on `l3.PSTATE.SPS`) >>
        gvs[flag_rel_def, monad_rws, asl_word_rws] >- state_rel_tac[] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
        state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, T)` >> gvs[] >>
        simp[SP_set_def, write'SP_def, write'X_rwt, X_set_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        simp[monad_rws, int_ge, COND_RATOR, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, R_ref_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> gvs[asl_word_rws, EL_LUPDATE] >>
        IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      simp[SP_set_def, write'SP_def, R_ref_def, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      simp[monad_rws, COND_RATOR] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, F)` >> gvs[] >>
        simp[SP_set_def, write'SP_def, write'X_rwt, X_set_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        simp[monad_rws, int_ge, COND_RATOR, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, R_ref_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        gvs[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      simp[SP_set_def, write'SP_def, R_ref_def, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      simp[monad_rws, COND_RATOR] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        reverse (Cases_on `l3.PSTATE.SPS`) >>
        gvs[flag_rel_def, monad_rws, asl_word_rws] >- state_rel_tac[] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
        state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, F)` >> gvs[] >>
        simp[SP_set_def, write'SP_def, write'X_rwt, X_set_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        simp[monad_rws, int_ge, COND_RATOR, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, R_ref_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        gvs[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      simp[SP_set_def, write'SP_def, R_ref_def, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      simp[monad_rws, COND_RATOR] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    )
  >- (
    `i = (0w : 52 word) @@ ((11 >< 0) i : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    last_x_assum kall_tac >> rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
    l3_decode_tac >> rw[] >>
    l3_run_tac >> gvs[] >> pop_assum kall_tac >>
    asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL0" = l3.SP_EL0` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL1" = l3.SP_EL1` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL2" = l3.SP_EL2` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL3" = l3.SP_EL3` by state_rel_tac[] >>
    `flag_rel (l3.PSTATE.SPS)
      ((asl.regstate.ProcState_reg "PSTATE").ProcState_SP)` by
      state_rel_tac [] >>
    `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL =
        l3.PSTATE.EL` by state_rel_tac[] >>
    gvs[
      decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
      ] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[dfn'AddSubImmediate_def] >>
    `flag_rel T 0b1w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    `flag_rel F 0b0w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    strip_tac >> strip_tac >> simp[COND_RATOR, monad_rws] >>
    `(r1 = 31w ⇔ w2n r1 = 31) ∧ (r2 = 31w ⇔ w2n r2 = 31)` by (
        rw[] >> eq_tac >> rw[] >> irule $ iffLR w2n_11 >>
        `w2n (0b11111w : 5 word) = 31` by simp[] >>
        pop_assum SUBST_ALL_TAC >> simp[]) >>
    `w2n r1 ≤ 31 ∧ w2n r2 ≤ 31` by (
      rw[] >> rename1 `w2n a` >>
      assume_tac (w2n_lt |> INST_TYPE [alpha |-> ``:5``]) >>
      pop_assum $ qspec_then `a` assume_tac >> drule SUB_LESS_OR >> simp[]) >>
    simp[]
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ¬w2w j, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, ¬w2w j, T)` >> gvs[] >>
        simp[write'X_rwt, X_set_def] >>
        reverse IF_CASES_TAC >> gvs[monad_rws]
        >- (
          PairCases_on `r` >> simp[SetTheFlags_def] >>
          state_rel_tac[] >> blastLib.BBLAST_TAC
          ) >>
        PairCases_on `r` >> simp[SetTheFlags_def, int_ge, monad_rws] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, ¬w2w j, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ¬w2w j, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse $ IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def] >>
        gvs[flag_rel_def] >> Cases_on `¬l3.PSTATE.SPS` >> gvs[]
        >- state_rel_tac[] >>
        simp[monad_rws, COND_RATOR] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
        state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, ¬w2w j, T)` >> gvs[] >>
        simp[write'X_rwt, X_set_def, monad_rws, COND_RATOR, int_ge] >>
        simp[R_ref_def, asl_word_rws] >>
        reverse IF_CASES_TAC >> gvs[]
        >- (
          PairCases_on `r` >> simp[SetTheFlags_def] >>
          state_rel_tac[] >> blastLib.BBLAST_TAC >> simp[EL_LUPDATE] >>
          IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, COND_RATOR, PSTATE_ref_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >> state_rel_tac[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, ¬w2w j, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      simp[SP_set_def, write'SP_def, monad_rws, COND_RATOR, PSTATE_ref_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, w2w j, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse $ IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, w2w j, F)` >> gvs[] >>
        simp[write'X_rwt, X_set_def, monad_rws, COND_RATOR, int_ge] >>
        simp[R_ref_def, asl_word_rws] >>
        IF_CASES_TAC >> gvs[] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, w2w j, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, w2w j, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse $ IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def, COND_RATOR] >>
        gvs[flag_rel_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        Cases_on `¬ l3.PSTATE.SPS` >> gvs[] >- state_rel_tac[] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, w2w j, F)` >> gvs[] >>
        simp[write'X_rwt, X_set_def, write'SP_def, SP_set_def, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        simp[monad_rws, COND_RATOR, int_ge] >>
        simp[R_ref_def, asl_word_rws] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, w2w j, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      simp[SP_set_def, write'SP_def, monad_rws, COND_RATOR, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    )
QED

(******************************************************************************)

val _ = export_theory();
