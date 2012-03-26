open HolKernel bossLib boolLib EmitTeX
open emitLib fmap_emitTheory int_emitTheory BytecodeTheory bytecodeTheory
val _ = new_theory "bytecode_emit"

val data = map
  (fn th => DATATYPE [QUOTE (datatype_thm_to_string th)])
  [datatype_bc_stack_op,
   datatype_bc_inst,
   datatype_bc_value,
   datatype_bc_state]

val init_state_def =  Define`
  init_state ls = <|
    stack := [];
    code := (Stack (Pops 1))::ls;
    pc := 1;
    refs := FEMPTY;
    exstack := [(0,0)];
    inst_length := λi. 0 |>`

val defs = map DEFN [
optionTheory.OPTION_BIND_def,
bc_fetch_aux_def,bc_fetch_def,bump_pc_def,
bool_to_int_def,isNumber_def,
bc_eval_stack_def,bc_eval1_def,bc_eval_def,
init_state_def]

val _ = eSML "bytecode" (
  (OPEN ["num","int","fmap"])
::(MLSIG "type num = numML.num")
::(MLSIG "type int = intML.int")
::(MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::data@defs)

val _ = export_theory ();
