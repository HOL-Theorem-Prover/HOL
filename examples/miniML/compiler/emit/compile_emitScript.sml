open HolKernel bossLib boolLib EmitTeX
open emitLib fmap_emitTheory int_emitTheory rich_list_emitTheory string_emitTheory bytecode_emitTheory
open CompileTheory compileProofsTheory
val _ = new_theory "compile_emit"

val _ = Parse.temp_type_abbrev("set",``:'a -> bool``)
val _ = Parse.temp_type_abbrev("string",``:char list``)
val _ = Parse.temp_type_abbrev("op_",``:op``) (* EmitML should do this *)
val _ = Parse.disable_tyabbrev_printing "tvarN"
val _ = Parse.disable_tyabbrev_printing "envE"

val underscore_rule = Conv.CONV_RULE let
fun foldthis (tm,(ls,b)) = let
  val (nm,_) = Term.dest_var tm
in if String.size nm > 1 andalso String.sub(nm,0) = #"_" then ("_"::ls,true) else (nm::ls,b) end in
Conv.TOP_SWEEP_CONV
  (fn tm => let
     val (vs, _) = Term.strip_binder NONE tm
     val (vs,true) = List.foldr foldthis ([],false) vs
   in Conv.RENAME_VARS_CONV vs tm end
   handle Bind => raise Conv.UNCHANGED)
end

val data = map
  (fn th => DATATYPE [QUOTE (datatype_thm_to_string th)])
  [ MiniMLTheory.datatype_lit
  , MiniMLTheory.datatype_error
  , MiniMLTheory.datatype_opb
  , MiniMLTheory.datatype_opn
  , MiniMLTheory.datatype_op
  , MiniMLTheory.datatype_log
  , MiniMLTheory.datatype_pat
  , MiniMLTheory.datatype_exp
  , MiniMLTheory.datatype_t
  , MiniMLTheory.datatype_dec
  , datatype_Cprim2
  , datatype_Clprim
  , datatype_Cpat
  , datatype_Cexp
  , datatype_ctbind
  , datatype_cebind
  , datatype_call_context
  , datatype_compiler_state
  , datatype_exp_to_Cexp_state
  , datatype_nt
  , datatype_repl_state
  ]

val init_compiler_state =
prove(
boolSyntax.mk_eq(``init_compiler_state``,
boolSyntax.rhs(Thm.concl(SIMP_CONV (srw_ss()) [init_compiler_state_def]
``<| env := init_compiler_state.env
   ; sz := init_compiler_state.sz
   ; code := init_compiler_state.code
   ; code_length := init_compiler_state.code_length
   ; tail := init_compiler_state.tail
   ; next_label := init_compiler_state.next_label
   ; decl := init_compiler_state.decl
   ; inst_length := init_compiler_state.inst_length
   |>``))), SRW_TAC[][init_compiler_state_def])

val init_repl_state =
prove(
boolSyntax.mk_eq(``init_repl_state``,
boolSyntax.rhs(Thm.concl(SIMP_CONV (srw_ss()) [init_repl_state_def]
``<| cmap := init_repl_state.cmap
   ; cpam := init_repl_state.cpam
   ; vmap := init_repl_state.vmap
   ; nextv := init_repl_state.nextv
   ; cs := init_repl_state.cs
   |>``))), SRW_TAC[][init_repl_state_def])

val defs = map DEFN
[ incsz_def
, free_vars_def
, REWRITE_RULE [set_emitTheory.IS_EMPTY_REWRITE]
    (UNDISCH (SPEC_ALL fsetTheory.num_set_foldl_def))
, emit_def
, i0_def
, i1_def
, i2_def
, error_to_int_def
, compile_varref_def
, fold_num_def
, sdt_def
, ldt_def
, decsz_def
, prim2_to_bc_def
, find_index_def
, replace_calls_def
, emit_ec_def
, underscore_rule compile_def
, init_compiler_state
, init_repl_state
, remove_Gt_Geq_def
, remove_mat_exp_def
, extend_def
, pat_to_Cpat_def
, underscore_rule exp_to_Cexp_def
, least_not_in_def
, remove_mat_vp_def
, remove_mat_def
, compile_exp_def
, repl_exp_def
, t_to_nt_def
, number_constructors_def
, pat_vars_def
, lookup_conv_ty_def
, repl_dec_def
, inst_arg_def
, bcv_to_v_def
]

val num_to_bool = prove(
``num_to_bool n = if n = 0 then F else if n = 1 then T else ARB``,
SRW_TAC[][num_to_bool_primitive_def] THEN
SELECT_ELIM_TAC THEN
SRW_TAC[][relationTheory.WFREC_THM] THEN1
PROVE_TAC[prim_recTheory.WF_LESS] THEN
Cases_on `n` THEN SRW_TAC[][] THEN
Cases_on `n'` THEN SRW_TAC[][])

val _ = eSML "compile" (
  (OPEN ["num","fmap","set","bytecode"])
::(MLSIG "type num = numML.num")
::(MLSIG "type int = intML.int")
::(MLSTRUCT "type int = intML.int")
::(MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::(MLSIG "type 'a set = 'a setML.set")
::(MLSIG "type bc_stack_op = bytecodeML.bc_stack_op")
::(MLSIG "type bc_inst = bytecodeML.bc_inst")
::(MLSIG "type bc_value = bytecodeML.bc_value")
::(MLSIG "val num_to_bool : num -> bool")
::(DEFN_NOSIG num_to_bool)
::data@defs)

val _ = export_theory ();
