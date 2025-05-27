open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_bytecode";

open stringTheory arithmeticTheory lisp_sexpTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* abstract syntax of bytecode *)

val _ = Hol_datatype `
  bc_inst_type =
  (* stack operations *)
    iPOP
  | iPOPS of num
  | iCONST_NUM of num
  | iCONST_SYM of string
  | iCONST_LOOKUP
  | iDATA of lisp_primitive_op
  | iLOAD of num
  | iSTORE of num
  (* control-flow altering instructions *)
  | iJUMP of num
  | iCALL of num
  | iJNIL of num
  | iJUMP_SYM
  | iCALL_SYM
  | iRETURN
  | iFAIL
  (* special instructions *)
  | iCOMPILE
  | iPRINT`;


val _ = export_theory();

