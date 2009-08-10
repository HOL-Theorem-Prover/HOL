structure codegen_x86Lib :> codegen_x86Lib =
struct

open HolKernel boolLib bossLib Parse;
open helperLib x86_encodeLib codegen_inputLib;


val x86_regs = ref [(0,"eax"), (1,"ecx"), (2,"edx"), (3,"ebx"),
                    (4,"edi"), (5,"esi"), (6,"ebp")];

fun set_x86_regs regs = (x86_regs := regs);
fun get_x86_regs ()   = (!x86_regs);

fun x86_reg n = (snd o hd o filter (fn (x,y) => x = n)) (get_x86_regs ())

fun to_x86_regs () = let
  fun foo (i,s) = mk_var("r" ^ int_to_string i,``:word32``) |-> mk_var(s, ``:word32``)
  in map foo (get_x86_regs ()) end

val x86_assign2assembly = let
  fun r i = x86_reg i
  fun s i = "[esp + " ^ int_to_string (4 * i) ^ "]"
  fun address (ASSIGN_ADDRESS_REG i) = "[" ^ r i ^ "]"
    | address (ASSIGN_ADDRESS_OFFSET_ADD (d,i)) = "[" ^ r d ^ " + " ^ Arbnum.toString i ^ "]"
    | address (ASSIGN_ADDRESS_OFFSET_SUB (d,i)) = "[" ^ r d ^ " - " ^ Arbnum.toString i ^ "]"
  fun binop_to_name ASSIGN_BINOP_ADD = "add"
    | binop_to_name ASSIGN_BINOP_AND = "and"
    | binop_to_name ASSIGN_BINOP_SUB = "sub"
    | binop_to_name ASSIGN_BINOP_XOR = "xor"
    | binop_to_name ASSIGN_BINOP_OR = "or"
    | binop_to_name _ = hd []
  fun exp (ASSIGN_X_REG j) = x86_reg j
    | exp (ASSIGN_X_CONST i) = Arbnum.toString i
  fun code_for_binop k ASSIGN_BINOP_MUL
                     (ASSIGN_X_REG i) (ASSIGN_X_REG j) reversed = let
        val k_reg = x86_reg k
        val i_reg = x86_reg i
        val j_reg = x86_reg j
        val (i_reg,j_reg) = if i_reg = "eax" then (i_reg,j_reg) else (j_reg,i_reg)
        in if (i_reg = "eax") andalso (k_reg = "eax") then ["mul " ^ x86_reg j]
           else (print ("\n\nUnable to create x86 code for:   " ^ k_reg ^ " := " ^ i_reg ^
                       " * " ^ j_reg ^ "\n\n"); hd []) end
    | code_for_binop k ASSIGN_BINOP_DIV
                     (ASSIGN_X_REG i) (ASSIGN_X_REG j) reversed = let
        val k_reg = x86_reg k
        val i_reg = x86_reg i
        val j_reg = x86_reg j
        val (i_reg,j_reg) = if i_reg = "eax" then (i_reg,j_reg) else (j_reg,i_reg)
        in if (i_reg = "eax") andalso (k_reg = "eax") then ["xor edx, edx", "div " ^ x86_reg j]
           else (print ("\n\nUnable to create x86 code for:   " ^ k_reg ^ " := " ^ i_reg ^
                       " DIV " ^ j_reg ^ "\n\n"); hd []) end
    | code_for_binop k ASSIGN_BINOP_MOD
                     (ASSIGN_X_REG i) (ASSIGN_X_REG j) reversed = let
        val k_reg = x86_reg k
        val i_reg = x86_reg i
        val j_reg = x86_reg j
        val (i_reg,j_reg) = if i_reg = "eax" then (i_reg,j_reg) else (j_reg,i_reg)
        in if (i_reg = "eax") andalso (k_reg = "edx") then ["xor edx, edx", "mod " ^ x86_reg j]
           else (print ("\n\nUnable to create x86 code for:   " ^ k_reg ^ " := " ^ i_reg ^
                       " MOD " ^ j_reg ^ "\n\n"); hd []) end
    | code_for_binop d b (ASSIGN_X_CONST i) (ASSIGN_X_REG j) reversed =
        code_for_binop d b (ASSIGN_X_REG j) (ASSIGN_X_CONST i) (not reversed)
    | code_for_binop d b (ASSIGN_X_CONST i) (ASSIGN_X_CONST j) reversed = hd []
    | code_for_binop d b (ASSIGN_X_REG i) j reversed =
       if (b = ASSIGN_BINOP_SUB) andalso reversed then
         (if j = ASSIGN_X_REG d then [] else ["mov " ^ x86_reg d ^ ", " ^ exp j]) @
         ["neg " ^ x86_reg d] @ ["add " ^ x86_reg d ^ ", " ^ x86_reg i]
       else
         if (j = ASSIGN_X_REG d) andalso not (i = d) then
           code_for_binop d b (ASSIGN_X_REG d) (ASSIGN_X_REG i) (not reversed)
         else if (i = d) andalso (j = ASSIGN_X_CONST (Arbnum.fromInt 1)) andalso (b = ASSIGN_BINOP_ADD) then
           ["inc " ^ x86_reg d]
         else if (i = d) andalso (j = ASSIGN_X_CONST (Arbnum.fromInt 1)) andalso (b = ASSIGN_BINOP_SUB) then
           ["dec " ^ x86_reg d]
         else if (b = ASSIGN_BINOP_ADD) andalso not (i = d) then
           ["lea " ^ x86_reg d ^ ", [" ^ x86_reg i ^ "+" ^ exp j ^ "]"]
         else
           (if d = i then [] else ["mov " ^ x86_reg d ^ ", " ^ x86_reg i]) @
           [binop_to_name b ^ " " ^ x86_reg d ^ ", " ^ exp j]
  fun monop_to_name ASSIGN_MONOP_NEG = "neg"
    | monop_to_name ASSIGN_MONOP_NOT = "not"
  fun code_for_monop d m j =
    (if j = ASSIGN_X_REG d then [] else ["mov " ^ x86_reg d ^ ", " ^ exp j]) @
    [monop_to_name m ^ " " ^ x86_reg d]
  fun code_for_shift d j n name =
    (if j = ASSIGN_X_REG d then [] else ["mov " ^ x86_reg d ^ ", " ^ exp j]) @
    [name ^ " " ^ x86_reg d ^ ", " ^ int_to_string n]
  fun mov_name ACCESS_WORD = "mov"
    | mov_name ACCESS_BYTE = "mov BYTE"
  fun mem_rhs _ (ASSIGN_X_REG t) = r t
    | mem_rhs ACCESS_WORD (ASSIGN_X_CONST i) = Arbnum.toString i
    | mem_rhs ACCESS_BYTE (ASSIGN_X_CONST i) = let
        val imm8 = Arbnum.toInt i
        val imm8 = if 128 <= imm8 then "-" ^ int_to_string (0 - (imm8 - 256)) else int_to_string imm8
        in imm8 end
  fun f (ASSIGN_EXP (d, ASSIGN_EXP_REG s)) = ["cmov? " ^ r d ^ ", " ^ r s]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_CONST i)) = ["mov " ^ r d ^ ", " ^ Arbnum.toString i]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_STACK i)) = ["mov " ^ r d ^ ", " ^ s i]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_BINOP (i,b,j))) = code_for_binop d b i j false
    | f (ASSIGN_EXP (d, ASSIGN_EXP_MONOP (m,j))) = code_for_monop d m j
    | f (ASSIGN_EXP (d, ASSIGN_EXP_MEMORY (b,a))) = [mov_name b ^ " " ^ r d ^ ", " ^ address a]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_SHIFT_LEFT (j,n))) = code_for_shift d j n "shl"
    | f (ASSIGN_EXP (d, ASSIGN_EXP_SHIFT_RIGHT (j,n))) = code_for_shift d j n "shr"
    | f (ASSIGN_EXP (d, ASSIGN_EXP_SHIFT_ARITHMETIC_RIGHT (j,n))) = code_for_shift d j n "sar"
    | f (ASSIGN_STACK (i,d)) = ["mov " ^ s i ^ ", " ^ mem_rhs ACCESS_WORD d]
    | f (ASSIGN_MEMORY (b,a,d)) = [mov_name b ^ " " ^ address a ^ ", " ^ mem_rhs b d]
    | f (ASSIGN_OTHER (t1,t2)) = hd []
  in f end

fun x86_guard2assembly (GUARD_NOT t) = let
      val (code,(x,y)) = x86_guard2assembly t in (code,(y,x)) end
  | x86_guard2assembly (GUARD_COMPARE (i,cmp,j)) = let
      val rd = x86_reg i
      fun f (ASSIGN_X_REG r) = x86_reg r
        | f (ASSIGN_X_CONST c) = Arbnum.toString c
      val code = ["cmp " ^ rd ^ ", " ^ f j]
      fun g (GUARD_COMPARE_LESS false) = ("b","nb")
        | g (GUARD_COMPARE_LESS true) = ("lt","ge")
        | g (GUARD_COMPARE_LESS_EQUAL false) = ("na","a")
        | g (GUARD_COMPARE_LESS_EQUAL true) = ("le","gt")
        | g (GUARD_COMPARE_EQUAL) = ("e","ne")
      in (code, g cmp) end
  | x86_guard2assembly (GUARD_TEST (i,j)) = let
      val rd = x86_reg i
      fun f (ASSIGN_X_REG r) = x86_reg r
        | f (ASSIGN_X_CONST c) = Arbnum.toString c
      val code = ["test " ^ rd ^ ", " ^ f j]
      in (code, ("e","ne")) end
  | x86_guard2assembly (GUARD_EQUAL_BYTE (a,i)) = let
    fun r i = x86_reg i
    fun address (ASSIGN_ADDRESS_REG i) = "[" ^ r i ^ "]"
      | address (ASSIGN_ADDRESS_OFFSET_ADD (d,i)) = "[" ^ r d ^ " + " ^ Arbnum.toString i ^ "]"
      | address (ASSIGN_ADDRESS_OFFSET_SUB (d,i)) = "[" ^ r d ^ " - " ^ Arbnum.toString i ^ "]"
    in (["cmp BYTE " ^ address a ^ ", " ^ Arbnum.toString i], ("e","ne")) end
  | x86_guard2assembly (GUARD_OTHER tm) = let
      val (t1,t2) = dest_eq tm
      val code = hd (x86_assign2assembly (term2assign t1 t2))
      val code = "cmp" ^ (implode o tl o tl o tl o explode) code
      in ([code], ("e","ne")) end;



fun x86_conditionalise c condition = let
  val c' = String.translate (fn x => if x = #"?" then condition else implode [x]) c
  in if c = c' then hd [] else c' end

fun x86_remove_annotations c =
  if String.substring(c,0,5) = "cmov?" then
    "mov" ^ String.substring(c,5,size(c) - 5)
  else c handle _ => c

fun x86_cond_code tm =
  (* zero     *) if tm = ``xS1 X_ZF`` then ("e","ne") else
  (* sign     *) if tm = ``xS1 X_SF`` then ("s","ns") else
  (* below    *) if tm = ``xS1 X_CF`` then ("b","nb") else hd []


fun x86_encode_instruction s =
  let val s = x86_encode s in (s, (size s) div 2) end

fun x86_encode_branch_aux forward l cond = let
  fun asm NONE = "jmp"
    | asm (SOME c) = if hd (explode c) = #"j" then c else "j" ^ c
  val s = asm cond
  fun address l = s ^ (if forward then " " else " -") ^ int_to_string l
  fun find_encoding f l s = let
    val v = f (l + size s div 2)
    in if s = v then v else find_encoding f l v end
  val i = (if forward then x86_encode (address l)
           else find_encoding (x86_encode o address) l "")
  in (i, (size i) div 2) end

fun x86_flip_cond c =
  if mem c ["ne","jne"] then "e" else
  if mem c ["e","je"] then "ne" else
  if mem c ["ns","jns"] then "s" else
  if mem c ["s","js"] then "ns" else
  if mem c ["na","jna"] then "a" else
  if mem c ["a","ja"] then "na" else
  if mem c ["nb","jnb"] then "b" else
  if mem c ["b","jb"] then "nb" else hd []

fun x86_encode_branch forward l cond =
  x86_encode_branch_aux forward l cond handle Empty =>
  let (* The implementation of long conditional jumps assume
         that short conditional jumps are 2 bytes inlength,
         and that long unconditional branches are 5 bytes. *)
  fun the NONE = hd [] | the (SOME x) = x
  val c = x86_flip_cond (the cond)
  val (xs,i) = x86_encode_branch_aux true 5 (SOME c)
  val _ = if i = 2 then () else hd []
  val l = if forward then l else l+2
  val (ys,j) = x86_encode_branch_aux forward l NONE
  in (xs ^ " " ^ ys, i + j) end

fun x86_branch_to_string NONE = "jmp"
  | x86_branch_to_string (SOME c) = "j" ^ c

end;
