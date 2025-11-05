Theory lisp_bytecode
Ancestors
  string arithmetic lisp_sexp

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* abstract syntax of bytecode *)

Datatype:
  bc_inst_type =
  (* stack operations *)
    iPOP
  | iPOPS num
  | iCONST_NUM num
  | iCONST_SYM string
  | iCONST_LOOKUP
  | iDATA lisp_primitive_op
  | iLOAD num
  | iSTORE num
  (* control-flow altering instructions *)
  | iJUMP num
  | iCALL num
  | iJNIL num
  | iJUMP_SYM
  | iCALL_SYM
  | iRETURN
  | iFAIL
  (* special instructions *)
  | iCOMPILE
  | iPRINT
End
