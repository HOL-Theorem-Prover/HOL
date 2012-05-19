open HolKernel bossLib boolLib EmitTeX
open bytecode_emitTheory
open CompileTheory compileTerminationTheory
val _ = new_theory "compile_emit"

val _ = Parse.temp_type_abbrev("set",``:'a -> bool``)
val _ = Parse.temp_type_abbrev("string",``:char list``)
val _ = Parse.temp_type_abbrev("op_",``:op``) (* EmitML should do this *)
val _ = Parse.disable_tyabbrev_printing "tvarN"
val _ = Parse.disable_tyabbrev_printing "envE"
val _ = Parse.disable_tyabbrev_printing "ctenv"
val _ = Parse.disable_tyabbrev_printing "alist"

val underscore_rule = Conv.CONV_RULE let
fun foldthis (tm,(ls,n)) = let
  val (nm,_) = Term.dest_var tm
in if String.sub(nm,0) = #"_" then (("us"^(Int.toString n))::ls,n+1) else (nm::ls,n) end in
Conv.TOP_SWEEP_CONV
  (fn tm => let
     val (vs, _) = Term.strip_binder NONE tm
     val (vs,n) = List.foldr foldthis ([],0) vs
   in if n = 0 then raise Conv.UNCHANGED else Conv.RENAME_VARS_CONV vs tm end)
end

val data = map
  (fn th => EmitML.DATATYPE [QUOTE (datatype_thm_to_string th)])
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
  , datatype_ov
  , datatype_Cprim2
  , datatype_Clprim
  , datatype_Cpat
  , datatype_Cexp
  , datatype_ctbind
  , datatype_cebind
  , datatype_call_context
  , datatype_compiler_state
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
   ; cs := init_repl_state.cs
   |>``))), SRW_TAC[][init_repl_state_def])

val defs = map EmitML.DEFN
[ mk_thm([],``ITSET f s a = FOLDR f a (toList s)``)
, incsz_def
, Cpat_vars_def
, free_vars_def
, emit_def
, i0_def
, i1_def
, i2_def
, error_to_int_def
, compile_varref_def
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
, pat_to_Cpat_def
, dest_var_def
, fsetTheory.fresh_var_def
, var_or_new_def
, underscore_rule (
  let open Lib pairSyntax
    val glhs = strip_comb o lhs o #2 o strip_forall o concl
    val (v_to_Cv,rest) =
      partition ((fn c => same_const ``v_to_Cv`` c
                   orelse same_const ``vs_to_Cvs`` c
                   orelse same_const ``env_to_Cenv`` c)
                 o #1 o glhs)
        (CONJUNCTS exp_to_Cexp_def) in
  LIST_CONJ
  ((op ::)
     (((fn th => th |> Q.SPEC `Lit l` |> Q.GEN `l` |> SIMP_RULE (srw_ss()) [hd v_to_Cv]) ## I)
       (pluck (same_const ``Val`` o #1 o strip_comb o el 2 o #2 o glhs)
          rest))) end)
, remove_mat_vp_def
, remove_mat_def
, compile_Cexp_def
, repl_exp_def
, t_to_nt_def
, number_constructors_def
, lookup_conv_ty_def
, repl_dec_def
, inst_arg_def
, v_to_ov_def
, bcv_to_ov_def
]

val num_to_bool = prove(
``num_to_bool n = if n = 0 then F else if n = 1 then T else ARB``,
SRW_TAC[][num_to_bool_primitive_def] THEN
SELECT_ELIM_TAC THEN
SRW_TAC[][relationTheory.WFREC_THM] THEN1
PROVE_TAC[prim_recTheory.WF_LESS] THEN
Cases_on `n` THEN SRW_TAC[][] THEN
Cases_on `n'` THEN SRW_TAC[][])

val _ = EmitML.eSML "compile" (
  (EmitML.OPEN ["num","fmap","set","sum","bytecode"])
::(EmitML.MLSIG "type num = numML.num")
::(EmitML.MLSIG "type int = intML.int")
::(EmitML.MLSTRUCT "type int = intML.int")
::(EmitML.MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::(EmitML.MLSIG "type 'a set = 'a setML.set")
::(EmitML.MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum")
::(EmitML.MLSIG "type bc_stack_op = bytecodeML.bc_stack_op")
::(EmitML.MLSIG "type bc_inst = bytecodeML.bc_inst")
::(EmitML.MLSIG "type bc_value = bytecodeML.bc_value")
::(EmitML.MLSIG "val num_to_bool : num -> bool")
::(EmitML.DEFN_NOSIG num_to_bool)
::data@defs)

val _ = export_theory ();
