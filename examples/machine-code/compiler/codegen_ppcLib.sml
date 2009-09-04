structure codegen_ppcLib :> codegen_ppcLib =
struct

open HolKernel boolLib bossLib Parse;
open codegen_inputLib helperLib;
open ppc_encodeLib;


val ppc_temp_reg = ref 0;
fun set_ppc_temp_reg i = (ppc_temp_reg := i);
fun get_ppc_temp_reg () = !ppc_temp_reg;

val ppc_assign2assembly = let
  fun r i = int_to_string i
  fun s i = int_to_string (4 * i) ^ ", 13"
  fun assign_const_to_reg i d =
    if Arbnum.<(i,Arbnum.fromInt 32768) then  (* must fit into signed 16-bit word *)
      ["addi " ^ int_to_string d ^ ", 0, " ^ Arbnum.toString i]
    else
      ["addis " ^ int_to_string d ^ ", 0, " ^ Arbnum.toString (Arbnum.div(i,Arbnum.fromInt 65536))] @
      ["ori " ^ int_to_string d ^ ", " ^ int_to_string d ^ ", " ^ Arbnum.toString (Arbnum.mod(i,Arbnum.fromInt 65536))]
  fun address (ASSIGN_ADDRESS_REG i) = "0," ^ r i
    | address (ASSIGN_ADDRESS_OFFSET_ADD (d,i)) = Arbnum.toString i ^ "," ^ r d
    | address (ASSIGN_ADDRESS_OFFSET_SUB (d,i)) = "-" ^ Arbnum.toString i ^ "," ^ r d
  fun binop_to_name ASSIGN_BINOP_ADD = ("add","addi")
    | binop_to_name ASSIGN_BINOP_SUB = ("subfc","__nothing__")
    | binop_to_name ASSIGN_BINOP_MUL = ("mullw","mulli")
    | binop_to_name ASSIGN_BINOP_AND = ("and.","andi.")
    | binop_to_name ASSIGN_BINOP_XOR = ("xor","xori")
    | binop_to_name ASSIGN_BINOP_OR  = ("or","ori")
    | binop_to_name ASSIGN_BINOP_DIV = ("divwu","__nothing__")
    | binop_to_name ASSIGN_BINOP_MOD = ("__nothing__","__nothing__")
  fun code_for_binop d b (ASSIGN_X_REG i) (ASSIGN_X_REG j) reversed =
       if b = ASSIGN_BINOP_DIV then
         [ fst (binop_to_name b) ^ " " ^ r d ^ ", " ^ r i  ^ ", " ^ r j ]
       else
         [ fst (binop_to_name b) ^ " " ^ r d ^ ", " ^ r j  ^ ", " ^ r i ]
    | code_for_binop d b (ASSIGN_X_CONST i) (ASSIGN_X_REG j) reversed =
        code_for_binop d b (ASSIGN_X_REG j) (ASSIGN_X_CONST i) (not reversed)
    | code_for_binop d b (ASSIGN_X_CONST i) (ASSIGN_X_CONST j) reversed = hd []
    | code_for_binop d b (ASSIGN_X_REG i) (ASSIGN_X_CONST j) reversed = let
        val code = assign_const_to_reg j i
        in if length code = 1 then
             if b = ASSIGN_BINOP_SUB then
               [ "addi " ^ r d ^ ", " ^ r i ^ ", -" ^ Arbnum.toString j ]
             else
               [ snd (binop_to_name b) ^ " " ^ r d ^ ", " ^ r i ^ ", " ^ Arbnum.toString j ]
           else if d = i then hd [] else
             assign_const_to_reg j d @
             code_for_binop d b (ASSIGN_X_REG i) (ASSIGN_X_REG d) reversed
        end
  val t = get_ppc_temp_reg ()
  fun f (ASSIGN_EXP (d, ASSIGN_EXP_REG s)) = ["or " ^ r d ^ ", " ^ r s ^ ", " ^ r s]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_CONST i)) = assign_const_to_reg i d
    | f (ASSIGN_EXP (d, ASSIGN_EXP_STACK i)) = ["lwz " ^ r d ^ ", " ^ s i]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_BINOP (i,b,j))) = code_for_binop d b i j false
    | f (ASSIGN_EXP (d, ASSIGN_EXP_MONOP (ASSIGN_MONOP_NOT, ASSIGN_X_REG i))) = ["nor " ^ r d ^ ", " ^ r i ^ ", " ^ r i ]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_MONOP (ASSIGN_MONOP_NEG, ASSIGN_X_REG i))) = ["subfic " ^ r d ^ ", " ^ r i ^ ", 0"]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_MEMORY (ACCESS_WORD,a))) = ["lwz " ^ r d ^ ", " ^ address a]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_MEMORY (ACCESS_BYTE,a))) = ["lbz " ^ r d ^ ", " ^ address a]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_SHIFT_LEFT (ASSIGN_X_REG i,n))) = assign_const_to_reg (Arbnum.fromInt n) (get_ppc_temp_reg ()) @ ["slw " ^ r d ^ ", " ^ r i ^ ", " ^ r (get_ppc_temp_reg ()) ]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_SHIFT_RIGHT (ASSIGN_X_REG i,n))) = ["srawi " ^ r d ^ ", " ^ r i ^ ", " ^ int_to_string n ]
    | f (ASSIGN_EXP (d, ASSIGN_EXP_SHIFT_ARITHMETIC_RIGHT (ASSIGN_X_REG i,n))) = ["srw " ^ r d ^ ", " ^ r i ^ ", " ^ int_to_string n ]
    | f (ASSIGN_STACK (i,ASSIGN_X_REG d)) = ["stw " ^ r d ^ ", " ^ s i]
    | f (ASSIGN_STACK (i,ASSIGN_X_CONST j)) = assign_const_to_reg j t @ ["stw " ^ r t ^ ", " ^ s i]
    | f (ASSIGN_MEMORY (ACCESS_WORD,a,ASSIGN_X_REG d)) = ["stw " ^ r d ^ ", " ^ address a]
    | f (ASSIGN_MEMORY (ACCESS_BYTE,a,ASSIGN_X_REG d)) = ["stb " ^ r d ^ ", " ^ address a]
    | f (ASSIGN_MEMORY (ACCESS_WORD,a,ASSIGN_X_CONST i)) = assign_const_to_reg i t @ ["stw " ^ r t ^ ", " ^ address a]
    | f (ASSIGN_MEMORY (ACCESS_BYTE,a,ASSIGN_X_CONST i)) = assign_const_to_reg i t @ ["stb " ^ r t ^ ", " ^ address a]
    | f _ = hd []
  in f end

fun ppc_guard2assembly (GUARD_NOT t) = let
      val (code,(x,y)) = ppc_guard2assembly t in (code,(y,x)) end
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS false,ASSIGN_X_REG r)) =
      (["cmplw " ^ int_to_string i ^ "," ^ int_to_string r], ("lt","ge"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS false,ASSIGN_X_CONST c)) =
      (["cmplwi " ^ int_to_string i ^ "," ^ Arbnum.toString c], ("lt","ge"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS true,ASSIGN_X_REG r)) =
      (["cmpw " ^ int_to_string i ^ "," ^ int_to_string r], ("lt","ge"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS true,ASSIGN_X_CONST c)) =
      (["cmpwi " ^ int_to_string i ^ "," ^ Arbnum.toString c], ("lt","ge"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS_EQUAL false,ASSIGN_X_REG r)) =
      (["cmplw " ^ int_to_string i ^ "," ^ int_to_string r], ("le","gt"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS_EQUAL false,ASSIGN_X_CONST c)) =
      (["cmplwi " ^ int_to_string i ^ "," ^ Arbnum.toString c], ("le","gt"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS_EQUAL true,ASSIGN_X_REG r)) =
      (["cmpw " ^ int_to_string i ^ "," ^ int_to_string r], ("le","gt"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_LESS_EQUAL true,ASSIGN_X_CONST c)) =
      (["cmpwi " ^ int_to_string i ^ "," ^ Arbnum.toString c], ("le","gt"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_EQUAL,ASSIGN_X_REG r)) =
      (["cmplw " ^ int_to_string i ^ "," ^ int_to_string r], ("eq","ne"))
  | ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_EQUAL,ASSIGN_X_CONST c)) =
      (["cmplwi " ^ int_to_string i ^ "," ^ Arbnum.toString c], ("eq","ne"))
  | ppc_guard2assembly (GUARD_TEST (i,ASSIGN_X_REG r)) =
      (["and. " ^ int_to_string (get_ppc_temp_reg()) ^ "," ^ int_to_string i ^ "," ^ int_to_string r], ("eq","ne"))
  | ppc_guard2assembly (GUARD_TEST (i,ASSIGN_X_CONST c)) =
      (["andi. " ^ int_to_string (get_ppc_temp_reg()) ^ "," ^ int_to_string i ^ "," ^ Arbnum.toString c], ("eq","ne"))
  | ppc_guard2assembly (GUARD_EQUAL_BYTE (a,i)) = hd []
  | ppc_guard2assembly (GUARD_OTHER tm) = let
      val (t1,t2) = dest_eq tm
      fun f (ASSIGN_EXP (i,exp)) = (i,exp) | f _ = hd []
      val (i,exp) = f (term2assign t1 t2)
      val t = get_ppc_temp_reg ()
      val code = (ppc_assign2assembly (ASSIGN_EXP (t, exp)))
      val (code2,c) = ppc_guard2assembly (GUARD_COMPARE (i,GUARD_COMPARE_EQUAL,ASSIGN_X_REG t))
      in (code @ code2,c) end;

fun ppc_conditionalise (x:string) = (hd []):string->string
fun ppc_remove_annotations x = (x:string)

fun ppc_cond_code tm = 
  if eq tm ``pS1 (PPC_CR0 0w)`` then ("lt","ge") else
  if eq tm ``pS1 (PPC_CR0 1w)`` then ("le","gt") else
  if eq tm ``pS1 (PPC_CR0 2w)`` then ("eq","ne") else hd []


fun ppc_encode_instruction s = (ppc_encode s, 4);

fun ppc_encode_branch forward l cond = let
  fun asm NONE = "b"
    | asm (SOME c) = if hd (explode c) = #"b" then c else "b" ^ c
  val l = l div 4
  val code = if forward then asm cond ^ " " ^ int_to_string (l + 1)
                        else asm cond ^ " -" ^ int_to_string l
  in ppc_encode_instruction code end

fun ppc_branch_to_string NONE = "b"
  | ppc_branch_to_string (SOME c) = "b" ^ c

end;
