open HolKernel bossLib boolLib
open emitLib fmap_emitTheory int_emitTheory bytecodeTheory
val _ = new_theory "bytecode_emit"

val data = map DATATYPE [`
  bc_stack_op =
    Pop                     (* pop top of stack *)
  | Pops of num             (* pop n elements under stack top *)
  | PushInt of int          (* push num onto stack *)
  | Cons of num => num      (* push new cons with tag m and n elements *)
  | Load of num             (* push stack[n+1] *)
  | Store of num            (* pop and store in stack[n+1] *)
  | El of num               (* read field n of cons block *)
  | Tag                     (* read tag from cons block *)
  | IsNum | Equal           (* tests *)
  | Add | Sub | Mult | Div2 | Mod2 | Less  (* arithmetic *)`
,
`
  bc_inst =
    Stack of bc_stack_op
  | Jump of num             (* jump to location n *)
  | JumpNil of num          (* conditional jump to location n *)
  | Call of num             (* call location n *)
  | JumpPtr                 (* jump based on code pointer *)
  | CallPtr                 (* call based on code pointer *)
  | Return                  (* pop return address, jump *)
  | Ref                     (* create a new ref cell *)
  | Deref                   (* dereference a ref cell *)
  | Update                  (* update a ref cell *)`
,
`
  bc_value =
    Number of int                  (* integer *)
  | Block of num => bc_value list  (* cons block: tag and payload *)
  | CodePtr of num                 (* code pointer *)
  | RefPtr of num                  (* pointer to ref cell *)`
,
`
  bc_state =
   <| (* main state components *)
      stack : bc_value list;
      code : bc_inst list ;
      pc : num ;
      refs : num |-> bc_value ;
      (* artificial state components *)
      inst_length : bc_inst -> num
   |>`]


val defs = map DEFN [
optionTheory.OPTION_BIND_def,
bc_fetch_aux_def,bc_fetch_def,bump_pc_def,
bool2num_def,isNumber_def,
bc_eval_stack_def,bc_eval1_def,bc_eval_def]

val _ = eSML "bytecode" (
  (OPEN ["num","int","fmap"])
::(MLSIG "type num = numML.num")
::(MLSIG "type int = intML.int")
::(MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::data@defs)

val _ = export_theory ();
