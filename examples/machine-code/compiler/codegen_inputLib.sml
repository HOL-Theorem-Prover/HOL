structure codegen_inputLib :> codegen_inputLib =
struct
  
open HolKernel boolLib bossLib Parse;
open helperLib wordsTheory;


(* core code generator input syntax *)

datatype access_type = 
    ACCESS_WORD
  | ACCESS_BYTE;

datatype assign_address_type = 
    ASSIGN_ADDRESS_REG of int 
  | ASSIGN_ADDRESS_OFFSET_ADD of int * Arbnum.num
  | ASSIGN_ADDRESS_OFFSET_SUB of int * Arbnum.num;

datatype assign_monop_type = 
    ASSIGN_MONOP_NOT
  | ASSIGN_MONOP_NEG;

datatype assign_binop_type = 
    ASSIGN_BINOP_ADD
  | ASSIGN_BINOP_SUB
  | ASSIGN_BINOP_MUL
  | ASSIGN_BINOP_MOD
  | ASSIGN_BINOP_DIV
  | ASSIGN_BINOP_AND
  | ASSIGN_BINOP_XOR
  | ASSIGN_BINOP_OR;

datatype assign_x_type = 
    ASSIGN_X_REG of int          (* register number *)
  | ASSIGN_X_CONST of Arbnum.num (* constant *);

datatype assign_exp_type = 
    ASSIGN_EXP_REG of int
  | ASSIGN_EXP_CONST of Arbnum.num  (* constant *)
  | ASSIGN_EXP_STACK of int         (* stack[offset] *)
  | ASSIGN_EXP_BINOP of assign_x_type * assign_binop_type * assign_x_type
  | ASSIGN_EXP_MONOP of assign_monop_type * assign_x_type
  | ASSIGN_EXP_MEMORY of access_type * assign_address_type
  | ASSIGN_EXP_SHIFT_LEFT of assign_x_type * int
  | ASSIGN_EXP_SHIFT_RIGHT of assign_x_type * int
  | ASSIGN_EXP_SHIFT_ARITHMETIC_RIGHT of assign_x_type * int

datatype assign_type = 
    ASSIGN_EXP of int * assign_exp_type        (* register := expression *)
  | ASSIGN_STACK of int * assign_x_type        (* stack[offset] := x *)
  | ASSIGN_MEMORY of access_type * assign_address_type * assign_x_type
                                               (* mem[address] := x *)
  | ASSIGN_OTHER of term * term                (* lhs := rhs *);

datatype guard_compare_type =
    GUARD_COMPARE_LESS of bool       (* true: signed, false: unsigned *)
  | GUARD_COMPARE_LESS_EQUAL of bool (* true: signed, false: unsigned *)
  | GUARD_COMPARE_EQUAL;

datatype guard_type =
    GUARD_NOT of guard_type
  | GUARD_COMPARE of int * guard_compare_type * assign_x_type  (* reg, cmp, reg/const *)
  | GUARD_EQUAL_BYTE of assign_address_type * Arbnum.num 
  | GUARD_TEST of int * assign_x_type
  | GUARD_OTHER of term;


(* term2guard, term2assign *)

fun dest_var_char c tm = 
  if not ((hd o explode o fst o dest_var) tm = c) then hd [] else
    (string_to_int o implode o tl o explode o fst o dest_var) tm
val dest_reg = dest_var_char #"r"
val dest_stack = dest_var_char #"s"
fun dest_n2w tm = if car tm = ``n2w:num->word32`` then numSyntax.dest_numeral (cdr tm) else hd []
fun dest_n2w_byte tm = if car tm = ``n2w:num->word8`` then numSyntax.dest_numeral (cdr tm) else hd []
fun dest_x tm = ASSIGN_X_REG (dest_reg tm) handle e => ASSIGN_X_CONST (dest_n2w tm)
fun dest_address tm = ASSIGN_ADDRESS_REG (dest_reg tm) handle e =>
  (if not ((fst o dest_const o car o car) tm = "word_add") then hd [] else
    ASSIGN_ADDRESS_OFFSET_ADD ((dest_reg o cdr o car) tm, dest_n2w (cdr tm))) handle e =>
  if not ((fst o dest_const o car o car) tm = "word_sub") then hd [] else
    ASSIGN_ADDRESS_OFFSET_SUB ((dest_reg o cdr o car) tm, dest_n2w (cdr tm))

fun basic_term2guard tm = (* expects input to use "~", "<+", "<" and "=" only *)
  if can dest_neg tm then GUARD_NOT (basic_term2guard (dest_neg tm)) else let
    val cmps = [("word_lo", (GUARD_COMPARE_LESS false, GUARD_COMPARE_LESS_EQUAL false)), 
                ("word_lt", (GUARD_COMPARE_LESS true, GUARD_COMPARE_LESS_EQUAL true)), 
                ("=", (GUARD_COMPARE_EQUAL, GUARD_COMPARE_EQUAL))] 
    val (d1,d2) = (snd o hd o filter (fn x => fst x = (fst o dest_const o car o car) tm)) cmps
    val x1 = (cdr o car) tm
    val x2 = cdr tm
    in if can (match_term ``x && y = 0w:word32``) tm then
         GUARD_TEST ((dest_reg o cdr o car o cdr o car) tm, (dest_x o cdr o cdr o car) tm)         
       else if can dest_n2w x1 then 
         GUARD_NOT (GUARD_COMPARE (dest_reg x2, d2, dest_x x1))
       else 
         GUARD_COMPARE (dest_reg x1, d1, dest_x x2) 
       handle e => let
         val (i,_) = match_term ``(f:word32->word8) a = n2w n`` tm handle e =>
                     match_term ``n2w n = (f:word32->word8) a`` tm
         val addr = dest_address (subst i ``a:word32``)        
         val imm = dest_n2w_byte (subst i ``(n2w n):word8``)        
         in GUARD_EQUAL_BYTE (addr,imm) end        
       handle e =>
         GUARD_OTHER tm
    end;

fun term2guard tm = let
  fun f (GUARD_NOT (GUARD_NOT x)) = x | f x = x
  val c = REWRITE_CONV [WORD_HIGHER,WORD_GREATER,WORD_HIGHER_EQ,
    WORD_GREATER_EQ,GSYM WORD_NOT_LOWER,GSYM WORD_NOT_LESS] 
  val tm = ((snd o dest_eq o concl o c) tm) handle e => tm
  in f (basic_term2guard tm) end;

fun basic_term2assign t1 t2 = let
  val binops = [("word_add",ASSIGN_BINOP_ADD), ("word_sub",ASSIGN_BINOP_SUB),
                ("word_mul",ASSIGN_BINOP_MUL), ("word_and",ASSIGN_BINOP_AND),
                ("word_div",ASSIGN_BINOP_DIV), ("word_mod",ASSIGN_BINOP_MOD),
                ("word_xor",ASSIGN_BINOP_XOR), ("word_or",ASSIGN_BINOP_OR)]
  val monops = [("word_1comp",ASSIGN_MONOP_NOT), ("word_2comp",ASSIGN_MONOP_NEG)]
  fun dest_binop tm = 
    ((dest_x o cdr o car) tm,
     (snd o hd o filter (fn x => fst x = (fst o dest_const o car o car) tm)) binops,
     (dest_x o cdr) tm)
  fun dest_monop tm = 
    ((snd o hd o filter (fn x => fst x = (fst o dest_const o car) tm)) monops,
     (dest_x o cdr) tm)
  fun dest_memory tm = 
    if not (is_var (car tm) andalso type_of (car tm) = ``:word32->word32``) then hd [] else
      (ACCESS_WORD,dest_address (cdr tm))
  fun dest_byte_memory tm = 
    if not (is_const (car tm) andalso type_of (car tm) = ``:word8->word32``) then hd [] else
      (ACCESS_BYTE,dest_address (cdr (cdr tm)))
  fun dest_lsl tm = 
    if not ((fst o dest_const o car o car) tm = "word_lsl") then hd [] else
      ((dest_x o cdr o car) tm, (Arbnum.toInt o numSyntax.dest_numeral o cdr) tm)
  fun dest_lsr tm = 
    if not ((fst o dest_const o car o car) tm = "word_lsr") then hd [] else
      ((dest_x o cdr o car) tm, (Arbnum.toInt o numSyntax.dest_numeral o cdr) tm)
  fun dest_asr tm = 
    if not ((fst o dest_const o car o car) tm = "word_asr") then hd [] else
      ((dest_x o cdr o car) tm, (Arbnum.toInt o numSyntax.dest_numeral o cdr) tm)
  fun dest_memory_update tm = 
    if not (is_var (cdr tm) andalso (fst o dest_const o car o car o car) tm = "UPDATE") 
    then hd [] else (ACCESS_WORD, (dest_address o cdr o car o car) tm, (dest_x o cdr o car) tm)
    handle e => (ACCESS_BYTE, (dest_address o cdr o car o car) tm, 
                 (dest_x o cdr o cdr o car) tm 
                 handle e => (ASSIGN_X_CONST o dest_n2w_byte o cdr o car) tm)
  in ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_REG (dest_reg t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_CONST (dest_n2w t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_STACK (dest_stack t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_BINOP (dest_binop t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_MONOP (dest_monop t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_MEMORY (dest_memory t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_MEMORY (dest_byte_memory t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_SHIFT_LEFT (dest_lsl t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_SHIFT_RIGHT (dest_lsr t2)) handle e =>
     ASSIGN_EXP (dest_reg t1, ASSIGN_EXP_SHIFT_ARITHMETIC_RIGHT (dest_asr t2)) handle e =>
     ASSIGN_STACK (dest_stack t1, dest_x t2) handle e =>
     ASSIGN_MEMORY (dest_memory_update t2) handle e =>
     ASSIGN_OTHER (t1,t2)
  end

fun term2assign t1 t2 = let
  fun can_eval (ASSIGN_EXP (_, ASSIGN_EXP_BINOP (ASSIGN_X_CONST _,_,ASSIGN_X_CONST _))) = true
    | can_eval (ASSIGN_EXP (_, ASSIGN_EXP_MONOP (_, ASSIGN_X_CONST _))) = true
    | can_eval (ASSIGN_EXP (_, ASSIGN_EXP_SHIFT_LEFT (ASSIGN_X_CONST i,n))) = true
    | can_eval (ASSIGN_EXP (_, ASSIGN_EXP_SHIFT_RIGHT (ASSIGN_X_CONST i,n))) = true
    | can_eval (ASSIGN_EXP (_, ASSIGN_EXP_SHIFT_ARITHMETIC_RIGHT (ASSIGN_X_CONST i,n))) = true
    | can_eval _ = false
  val t = basic_term2assign t1 t2
  (* fold constants *)
  val t = if not (can_eval t) then t else basic_term2assign t1 ((cdr o concl o EVAL) t2)
  in t end  

end;
