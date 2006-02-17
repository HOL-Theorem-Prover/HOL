structure wordUtil :> wordUtil =
struct

open HolKernel boolLib Parse bossLib simpLib;

val arith_ss = old_arith_ss

val definition = DB.fetch "-";

val LEFT_REWRITE_TAC  = GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) empty_rewrites;
val RIGHT_REWRITE_TAC = GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) empty_rewrites;
val std_ss = std_ss ++ rewrites [LET_THM]
val arith_ss = arith_ss ++ rewrites [LET_THM]
val B_SIMP_TAC = SIMP_TAC bool_ss;
val S_SIMP_TAC = SIMP_TAC std_ss;
val A_SIMP_TAC = SIMP_TAC arith_ss;

val ASM_B_SIMP_TAC = ASM_SIMP_TAC bool_ss;
val ASM_S_SIMP_TAC = ASM_SIMP_TAC std_ss;
val ASM_A_SIMP_TAC = ASM_SIMP_TAC arith_ss;

val B_RW_TAC = RW_TAC bool_ss;
val S_RW_TAC = RW_TAC std_ss;
val A_RW_TAC = RW_TAC arith_ss;

val B_FULL_SIMP_TAC = FULL_SIMP_TAC bool_ss;
val S_FULL_SIMP_TAC = FULL_SIMP_TAC std_ss;
val A_FULL_SIMP_TAC = FULL_SIMP_TAC arith_ss;

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);
fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

fun export_doc_theorems() =
  export_theory_as_docfiles (fullPath["help","thms",current_theory()])

end
