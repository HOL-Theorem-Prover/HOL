structure x64_compilerLib :> x64_compilerLib =
struct

open HolKernel boolLib bossLib Parse;
open decompilerLib;
open x64_codegenLib;
open x64_codegen_x64Lib;

open prog_x64Lib;
open prog_x64_extraTheory;
open wordsTheory wordsLib addressTheory;
open helperLib;
open mc_tailrecLib;


fun AUTO_ALPHA_CONV () = let
  val counter = ref (Arbnum.zero)
  fun inc () = let val v = !counter in (counter := Arbnum.+(v,Arbnum.one); v) end
  fun counter_genvar ty = mk_var("auto_"^ Arbnum.toString (inc()),ty)
  fun doit tm =
    if is_abs tm then
      (ALPHA_CONV (counter_genvar (type_of (fst (dest_abs tm)))) THENC
       ABS_CONV doit) tm
    else if is_comb tm then
      (RATOR_CONV doit THENC RAND_CONV doit) tm
    else ALL_CONV tm
  in doit end

val COMPILER_TAC_LEMMA = prove(
  ``!a b:bool. (a /\ a /\ b <=> a /\ b) /\ (a \/ a \/ b <=> a \/ b)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss []);

val COMPILER_TAC =
    SIMP_TAC bool_ss [LET_DEF,word_div_def,word_mod_def,w2w_CLAUSES]
    THEN SIMP_TAC std_ss [WORD_OR_CLAUSES,GUARD_def]
    THEN REWRITE_TAC [WORD_CMP_NORMALISE]
    THEN REWRITE_TAC [WORD_HIGHER,WORD_GREATER,WORD_HIGHER_EQ,
           WORD_GREATER_EQ,GSYM WORD_NOT_LOWER,GSYM WORD_NOT_LESS]
    THEN SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,NOT_IF,
           WORD_OR_CLAUSES]
    THEN CONV_TAC (EVAL_ANY_MATCH_CONV word_patterns)
    THEN SIMP_TAC std_ss [WORD_SUB_RZERO, WORD_ADD_0, IF_IF,
                          AC WORD_ADD_COMM WORD_ADD_ASSOC,
                          AC WORD_MULT_COMM WORD_MULT_ASSOC,
                          AC WORD_AND_COMM WORD_AND_ASSOC,
                          AC WORD_OR_COMM WORD_OR_ASSOC,
                          AC WORD_XOR_COMM WORD_XOR_ASSOC,
                          AC CONJ_COMM CONJ_ASSOC,
                          AC DISJ_COMM DISJ_ASSOC,
                          IMP_DISJ_THM, WORD_MULT_CLAUSES]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC (RAND_CONV (AUTO_ALPHA_CONV ()))
    THEN CONV_TAC ((RATOR_CONV o RAND_CONV) (AUTO_ALPHA_CONV ()))
    THEN SIMP_TAC std_ss [AC CONJ_ASSOC CONJ_COMM, AC DISJ_COMM DISJ_ASSOC,
                          COMPILER_TAC_LEMMA]
    THEN SIMP_TAC std_ss [WORD_SUB_RZERO, WORD_ADD_0, IF_IF,
                          AC WORD_ADD_COMM WORD_ADD_ASSOC,
                          AC WORD_MULT_COMM WORD_MULT_ASSOC,
                          AC WORD_AND_COMM WORD_AND_ASSOC,
                          AC WORD_OR_COMM WORD_OR_ASSOC,
                          AC WORD_XOR_COMM WORD_XOR_ASSOC,
                          AC CONJ_COMM CONJ_ASSOC,
                          AC DISJ_COMM DISJ_ASSOC,
                          IMP_DISJ_THM, WORD_MULT_CLAUSES]
    THEN EQ_TAC
    THEN ONCE_REWRITE_TAC [GSYM DUMMY_EQ_def]
    THEN REWRITE_TAC [FLATTEN_IF]
    THEN REPEAT STRIP_TAC
    THEN ASM_SIMP_TAC std_ss [];

fun x64_basic_compile tm = let
  val target = "x64"
  val (tools,target,model_name,s) = (x64_tools_64,"x64","X64_MODEL",[])
  val x = fst (dest_eq tm)
  val name = fst (dest_const (repeat car x)) handle e => fst (dest_var (repeat car x))
  val _ = echo 1 ("\nCompiling " ^ name ^ " into "^ target ^ "...\n")
  val (code,len) = generate_code model_name true tm
  fun append' [] = "" | append' (x::xs) = x ^ "\n" ^ append' xs
  val qcode = [QUOTE (append' code)] : term quotation
  val in_tm = cdr x
  fun ends (FUN_IF (_,c1,c2)) = ends c1 @ ends c2
    | ends (FUN_LET (_,_,c)) = ends c
    | ends (FUN_COND (_,c)) = ends c
    | ends (FUN_VAL t) = if is_var t orelse pairSyntax.is_pair t then [t] else []
  val out_tm2 = hd (ends (tm2ftree (cdr tm)))
  val (in_tm,out_tm) = (subst s in_tm, subst s out_tm2)
  val function_in_out = SOME (in_tm,out_tm)
  val qcode = ([QUOTE (append' code)]) : term Lib.frag list
  val (th1,th2) = basic_decompile tools name function_in_out qcode
  val _ = print "Proving equivalence, "
  val const = (repeat car o fst o dest_eq o concl o hd o CONJUNCTS) th2
  val tm = subst [ repeat car x |-> const ] tm
  val pre = if is_conj (concl th2) then (last o CONJUNCTS) th2 else TRUTH
  val pre = RW [IF_IF,WORD_TIMES2] pre
  val th3 = auto_prove "compile" (tm,
    REPEAT STRIP_TAC
    THEN CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th2]))
    THEN COMPILER_TAC)
    handle HOL_ERR e => let
      val _ = (show_types := true)
      val _ = print ("\n\nval tm = ``"^ term_to_string tm ^"``;\n\n")
      val _ = (show_types := false)
      in raise HOL_ERR e end;
  val _ = add_compiler_assignment out_tm2 (fst (dest_eq tm)) name len model_name
  val _ = print "done.\n"
  in (th1,th3,pre) end;

fun x64_compile t = let
  val tm = Parse.Term t
  val _ = set_abbreviate_code true
  fun compile_each [] = []
    | compile_each (tm::tms) = let
    val (th,def,pre) = x64_basic_compile tm
    in (th,def,pre) :: compile_each tms end
  val tms = list_dest dest_conj tm
  val xs = compile_each tms
  val defs = map (fn (x,y,z) => y) xs
  val pres = map (fn (x,y,z) => z) xs
  val def = RW [] (foldr (uncurry CONJ) TRUTH defs)
  val pre = RW [] (foldr (uncurry CONJ) TRUTH pres)
  val (th,_,_) = last xs
  val _ = set_abbreviate_code false
  val th = UNABBREV_CODE_RULE th
  in (th,def,pre) end;

val _ = add_compiled (map (SIMP_RULE std_ss [LET_DEF] o Q.INST [`rip`|->`p`])
    [x64_push_r0, x64_push_r1, x64_push_r2, x64_push_r3, x64_push_r6,
     x64_push_r7, x64_push_r8, x64_push_r9, x64_push_r10,
     x64_push_r11, x64_push_r12, x64_push_r13, x64_push_r14,
     x64_push_r15, x64_pop_r0, x64_pop_r1, x64_pop_r2, x64_pop_r3,
     x64_pop_r6, x64_pop_r7, x64_pop_r8, x64_pop_r9, x64_pop_r10,
     x64_pop_r11, x64_pop_r12, x64_pop_r13, x64_pop_r14, x64_pop_r15]);

end;
