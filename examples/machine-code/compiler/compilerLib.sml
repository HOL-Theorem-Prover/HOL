structure compilerLib :> compilerLib =
struct
  
open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib addressTheory;
open prog_armLib prog_ppcLib prog_x86Lib decompilerLib;

open codegenLib helperLib codegen_x86Lib;



fun compile target tm = let
  val (tools,target,s) = 
    if mem target ["arm","ARM"] then (arm_tools,"arm",[]) else 
    if mem target ["x86","i32","386"] then (x86_tools,"x86",to_x86_regs) else 
    if mem target ["ppc","Power","PowerPC"] then (ppc_tools,"ppc",[]) else hd []
  val (code,len) = generate_code target true tm  
  fun append' [] = "" | append' (x::xs) = x ^ "\n" ^ append' xs
  val x = fst (dest_eq tm)
  val name = fst (dest_const (repeat car x)) handle e => fst (dest_var (repeat car x))
  val qcode = [QUOTE (append' code)] : term quotation
  val in_tm = cdr x
  fun ends (FUN_IF (_,c1,c2)) = ends c1 @ ends c2
    | ends (FUN_LET (_,_,c)) = ends c
    | ends (FUN_COND (_,c)) = ends c
    | ends (FUN_VAL t) = if is_var t orelse pairSyntax.is_pair t then [t] else []
  val out_tm2 = hd (ends (tm2ftree (cdr tm)))
  val (in_tm,out_tm) = (subst s in_tm, subst s out_tm2)
  val function_in_out = SOME (in_tm,out_tm)
  val (th1,th2) = basic_decompile tools name function_in_out [QUOTE (append' code)]
  val const = (repeat car o fst o dest_eq o concl o last o CONJUNCTS) th2
  val tm = subst [ repeat car x |-> const ] tm
  val pre = if is_conj (concl th2) then (hd o CONJUNCTS) th2 else TRUTH
  val lemma = prove(``(if ~b then x else y) = (if b then y else x:'a)``,Cases_on `b` THEN REWRITE_TAC [])
(*  
  set_goal([],tm)
*)
  val th3 = prove(tm,
    REPEAT STRIP_TAC
    THEN CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th2]))
    THEN SIMP_TAC bool_ss [LET_DEF]
    THEN REWRITE_TAC [WORD_CMP_NORMALISE] 
    THEN REWRITE_TAC [WORD_HIGHER,WORD_GREATER,WORD_HIGHER_EQ,
           WORD_GREATER_EQ,GSYM WORD_NOT_LOWER,GSYM WORD_NOT_LESS] 
    THEN SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,lemma,
           WORD_OR_CLAUSES]
    THEN CONV_TAC (EVAL_ANY_MATCH_CONV word_patterns)
    THEN SIMP_TAC bool_ss [WORD_SUB_RZERO, WORD_ADD_0, 
                      AC WORD_ADD_COMM WORD_ADD_ASSOC,
                      AC WORD_MULT_COMM WORD_MULT_ASSOC,
                      AC WORD_AND_COMM WORD_AND_ASSOC,
                      AC WORD_OR_COMM WORD_OR_ASSOC,
                      AC WORD_XOR_COMM WORD_XOR_ASSOC])    
  val _ = add_compiler_assignment out_tm2 (fst (dest_eq tm)) name len
  val _ = print (int_to_string len)
  in (th1,th3,pre) end



end;
