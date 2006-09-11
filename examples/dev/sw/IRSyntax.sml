structure IRSyntax = struct
  local
  open HolKernel Parse boolLib preARMTheory pairLib simpLib bossLib
       numSyntax optionSyntax listSyntax ILTheory
  in

  exception invalidILExp;

 (*---------------------------------------------------------------------------------*)
 (*      Definition of Data                                                         *) 
 (*---------------------------------------------------------------------------------*)

  datatype operator =  madd | msub | mrsb | mmul | mmla | mmov |
                       mand | morr | meor |
                       mlsl | mlsr | masr | mror |
                       mldr | mstr | mpop | mpush |
                       mmrs | mmsr |
                       mcall

  datatype alias = fp | ip | sp | lr | pc

  datatype exp = NCONST of Arbint.int
               | WCONST of Arbint.int
               | PAIR of exp * exp
               | MEM of int * int               (* base * offset *)
               | TMEM of int
               | REG of int
               | SHIFT of operator * int
               | NA                             (* N/A, for undecided fields *)

   datatype rop = eq | ne | ge | le | gt | lt | al | nv | cc | ls | hi | cs

   type instr = {oper: operator, dst: exp list, src: exp list}

 (*---------------------------------------------------------------------------------*)
 (*      Definition of Basic Operations                                                   *)
 (*---------------------------------------------------------------------------------*)

  fun pair2list (PAIR(v1, v2)) =
        (pair2list v1) @ (pair2list v2)
   |  pair2list v = [v]

  fun fromAlias fp = 11
   |  fromAlias ip = 12
   |  fromAlias sp = 13
   |  fromAlias lr = 14
   |  fromAlias pc = 15

  fun toAlias 11 = fp
   |  toAlias 12 = ip
   |  toAlias 13 = sp
   |  toAlias 14 = lr
   |  toAlias 15 = pc
   |  toAlias _ = raise invalidILExp

  fun convert_op mmov = Term(`MMOV`)
   |  convert_op madd = Term(`MADD`)
   |  convert_op msub = Term(`MSUB`)
   |  convert_op mrsb = Term(`MRSB`)
   |  convert_op mmul = Term(`MMUL`)
   |  convert_op mmla = Term(`MMLA`)
   |  convert_op mand = Term(`MAND`)
   |  convert_op morr = Term(`MORR`)
   |  convert_op meor = Term(`MEOR`)
   |  convert_op mlsl = Term(`MLSL`)
   |  convert_op mlsr = Term(`MLSR`)
   |  convert_op masr = Term(`MASR`)
   |  convert_op mror = Term(`MROR`)
   |  convert_op mldr = Term(`MLDR`)
   |  convert_op mpush = Term(`MPUSH`)
   |  convert_op mstr = Term(`MSTR`)
   |  convert_op mpop = Term(`MPOP`)
   |  convert_op mmrs = Term(`MMRS`)
   |  convert_op mmsr = Term(`MMSR`)
   |  convert_op mcall = raise ERR "annotatedIL" ("Cannot convert mcall to a term");

  fun convert_rop (eq) = Term(`EQ:COND`)
   |  convert_rop (ne) = Term(`NE:COND`)
   |  convert_rop (ge) = Term(`GE:COND`)
   |  convert_rop (lt) = Term(`LT:COND`)
   |  convert_rop (gt) = Term(`GT:COND`)
   |  convert_rop (le) = Term(`LE:COND`)
   |  convert_rop (cc) = Term(`CC:COND`)
   |  convert_rop (ls) = Term(`LS:COND`)
   |  convert_rop (hi) = Term(`HI:COND`)
   |  convert_rop (cs) = Term(`CS:COND`)
   |  convert_rop (al) = Term(`AL:COND`)
   |  convert_rop (nv) = Term(`NV:COND`)


 (*---------------------------------------------------------------------------------*)
 (*      Set input, output and context information                                  *)
 (*      Assistant functions                                                        *)
 (*---------------------------------------------------------------------------------*)

   structure S = Binaryset;

   fun index_of_exp (MEM (base,offset)) =
         10000 + offset
    |  index_of_exp (TMEM i) =
         5000 + i
    |  index_of_exp (REG e) =
         e
    |  index_of_exp NA =
         ~1
    |  index_of_exp _ =
          raise ERR "annotatedIR.eval_exp" ("invalid expression")

   fun expOrder (s1,s2) =
      let val (i1,i2) = (index_of_exp s1, index_of_exp s2)
      in
          if i1 > i2 then GREATER
          else if i1 = i2 then EQUAL
          else LESS
      end;

   fun list2pair l = 
     if null l then NA
     else 
        let fun f [h] = h
             |  f (h::ts) = PAIR (h, f ts)
             |  f _ = raise Fail "list2pair fails"
        in f l
        end

   fun list2set l = 
       if null l then S.empty expOrder
       else S.addList(S.empty expOrder, l);

   fun set2list s = List.filter (fn n => not (n = NA)) (S.listItems s);

   val set2pair = list2pair o set2list;
   val pair2set = list2set o pair2list;

   fun trim_pair (PAIR (NA,e2)) = trim_pair e2
    |  trim_pair (PAIR (e1,NA)) = trim_pair e1
    |  trim_pair (PAIR (e1,e2)) = PAIR (trim_pair e1, trim_pair e2)
    |  trim_pair e = e

 (*---------------------------------------------------------------------------------*)
 (*      Definition of Operations for Term-conversion                               *)
 (*---------------------------------------------------------------------------------*)


fun convert_reg (REG e) =
     rhs (concl (SIMP_CONV std_ss [from_reg_index_def] (mk_comb(Term`from_reg_index:num->MREG`, term_of_int e))))
 |  convert_reg _ = 
     raise ERR "IL" ("invalid expression");

fun convert_mem (MEM (regNo, offset)) =
     mk_pair(convert_reg (REG regNo),
             mk_comb(if offset >= 0 then Term`POS` else Term`NEG`,
                term_of_int (abs offset)))
 |  convert_mem _ = 
     raise ERR "IL" ("invalid expression");

fun convert_shift_const e =
  let 
    fun smsb b = if b then Arbnum.pow(Arbnum.two,Arbnum.fromInt 31) else Arbnum.zero
    fun mror32 x n =
      if n = 0 then x
              else mror32 (Arbnum.+ ((Arbnum.div2 x), smsb (Arbnum.mod2 x = Arbnum.one))) (Int.-(n, 1));
    fun ror32 x n = mror32 x (Int.mod(n, 32));
    fun rol32 x n = ror32 x (Int.-(32,Int.mod(n, 32)));

    fun num2imm(x,n) =
    let val x8 = Arbnum.mod(x,Arbnum.fromInt 256) in
      if x8 = x then
        (Arbnum.fromInt n, x8)
      else
        if n < 15 then
          num2imm(rol32 x 2, n + 1)
        else
          raise ERR ""
            "num2immediate: number cannot be represented as an immediate"
    end

    val (s, c) = num2imm (Arbint.toNat e, 0)
    val shift = mk_comb (Term`n2w:num->word4`, mk_numeral s)
    val const = mk_comb (Term`n2w:num->word8`, mk_numeral c)
  in
    mk_comb (mk_comb(Term`MC`, shift), const)
  end;


fun convert_exp (NCONST e) =
      convert_shift_const e
 |  convert_exp (WCONST e) =
      convert_shift_const e
 |  convert_exp (REG e) =
      mk_comb (Term`MR`, convert_reg (REG e))
 |  convert_exp (PAIR(e1,e2)) =
      mk_pair(convert_exp e1, convert_exp e2)
 |  convert_exp _ =
      raise ERR "IL" ("invalid expression");


fun read_exp st (NCONST e) =
    mk_comb (Term `n2w:num->word32`, mk_numeral (Arbint.toNat e))
  | read_exp st (WCONST e) =
    mk_comb (Term `n2w:num->word32`, mk_numeral (Arbint.toNat e))
  | read_exp st (REG e) =
    let
      val r = convert_reg (REG e);
    in
      Term `read ^st (toREG ^r)`
    end
  | read_exp st (PAIR(e1,e2)) =
    mk_pair(read_exp st e1, read_exp st e2)
  | read_exp st (MEM (b, off)) =
    let
      val t = convert_mem (MEM (b, off))
    in
      Term `read ^st (toMEM ^t)`
    end
 |  read_exp _ _ =
      raise ERR "IL" ("invalid expression");

local
  fun convert_shift_internal e =
    let
      val _ = if (Arbint.>= (e, Arbint.fromInt 32)) then raise ERR "IL" ("invalid expression") else ();
    in
      mk_comb (Term`n2w:num->word5`, mk_numeral (Arbint.toNat e))
    end;
in

fun convert_shift (NCONST e) = convert_shift_internal e
 |  convert_shift (WCONST e) = convert_shift_internal e
 |  convert_shift _ =
      raise ERR "IL" ("invalid expression");
end

 fun convert_stm ({oper = op1, dst = dlist, src = slist}) =
    let
        val ops = convert_op op1
    in 
        if op1 = mpush then
            list_mk_comb (ops, [(term_of_int o index_of_exp) (hd dlist), 
                          mk_list (List.map (term_of_int o index_of_exp) slist, Type `:num`)])
        else if op1 = mpop then 
            list_mk_comb (ops, [(term_of_int o index_of_exp) (hd slist), 
                          mk_list (List.map (term_of_int o index_of_exp) dlist, Type `:num`)])
        else if ((op1 = mlsl) orelse
                 (op1 = mlsr) orelse
                 (op1 = masr) orelse
                 (op1 = mror)) then            
            list_mk_comb (ops, [convert_reg (hd dlist), convert_reg (hd slist), convert_shift (el 2 slist)])
        else if (op1 = mmul) then            
            list_mk_comb (ops, (convert_reg (hd dlist)) :: map convert_reg slist)
        else if op1 = mstr then
            list_mk_comb (ops, (convert_mem (hd dlist)) :: [convert_reg (hd slist)])
        else if op1 = mldr then
            list_mk_comb (ops, (convert_reg (hd dlist)) :: [convert_mem (hd slist)])
        else if op1 = mmov then
            list_mk_comb (ops, (convert_reg (hd dlist)) :: [convert_exp (hd slist)])
        else
            list_mk_comb (ops, [convert_reg (hd dlist), convert_reg (hd slist),
            convert_exp (el 2 slist)])
    end
    handle e =>  raise ERR "IL" ("invalid statement!")



 (*---------------------------------------------------------------------------------*)
 (*     Interface between ARM and IR                                                *)
 (*---------------------------------------------------------------------------------*)

   fun to_rop Assem.EQ = eq
    |  to_rop Assem.NE = ne
    |  to_rop Assem.GE = ge
    |  to_rop Assem.LE = le
    |  to_rop Assem.GT = ge
    |  to_rop Assem.LT = lt
    |  to_rop Assem.CC = cc
    |  to_rop Assem.LS = ls
    |  to_rop Assem.HI = hi
    |  to_rop Assem.CS = cs
    |  to_rop Assem.AL = al
    |  to_rop Assem.NV = nv


   fun to_op Assem.ADD = madd
    |  to_op Assem.SUB = msub
    |  to_op Assem.RSB = mrsb
    |  to_op Assem.MUL = mmul
    |  to_op Assem.MLA = mmla
    |  to_op Assem.AND = mand
    |  to_op Assem.ORR = morr
    |  to_op Assem.EOR = meor
    |  to_op Assem.LSL = mlsl
    |  to_op Assem.LSR = mlsr
    |  to_op Assem.ASR = masr
    |  to_op Assem.ROR = mror
    |  to_op Assem.LDR = mldr
    |  to_op Assem.STR = mstr
    |  to_op Assem.LDMFD = mpop
    |  to_op Assem.STMFD = mpush
    |  to_op Assem.MRS = mmrs
    |  to_op Assem.MSR = mmsr
    |  to_op Assem.BL  = mcall
    |  to_op _ = raise ERR "IL" "No corresponding operator in IL"

   fun to_exp (Assem.MEM {reg = regNo, offset = offset, ...}) =
           MEM(regNo,offset)
    |  to_exp (Assem.TMEM i) =
           TMEM i
    |  to_exp (Assem.NCONST e) =
           NCONST e
    |  to_exp (Assem.WCONST e) =
           WCONST e
    |  to_exp (Assem.REG e) =
           REG e
    |  to_exp (Assem.PAIR(e1,e2)) =
           PAIR (to_exp e1, to_exp e2)
    |  to_exp _ =
           raise ERR "IL" ("No corresponding expression in IL") 

   fun to_inst (Assem.OPER {oper = (oper', cond', flag'), dst = dlist, src = slist, jump = jumps}) =
           {oper = to_op oper', dst = List.map to_exp dlist, src = List.map to_exp slist}
    |  to_inst (Assem.MOVE {dst = dst', src = src'}) =
           {oper = mmov, dst = [to_exp dst'], src = [to_exp src']}
    |  to_inst _ = 
           raise ERR "IL" ("Can convert only data operation instructions") 

   fun to_cond (Assem.OPER {oper = (Assem.CMP, cond1, flag1), dst = dlist1, src = slist1, jump = jumps1},
                Assem.OPER {oper = (Assem.B, cond2, flag2), dst = dlist2, src = slist2, jump = jumps2}) =
        (hd slist1, valOf cond2, hd (tl slist1))
    |  to_cond _ =  raise ERR "IL" ("Fail to obtain the condition from two instructions")


 (*---------------------------------------------------------------------------------*)
 (* Find the inputs, outputs and temporaries for a basic block                      *)
 (*---------------------------------------------------------------------------------*)
  
  structure T = IntMapTable(type key = int fun getInt n = n);

  datatype ACCESS = READ | WRITE | PUSH | POP 
  datatype ROLE = UNKNOWN | INPUT | OUTPUT | INSTACK;

  fun getIO stmL =
   let
     val (regT:((ROLE * ROLE) T.table) ref, memCT:((ROLE * ROLE) T.table) ref, memRT:((ROLE * ROLE) T.table) ref) 
	  = (ref (T.empty), ref (T.empty), ref (T.empty)); 

     fun peekT(t,index) = 
	case T.peek(t,index) of 
	     NONE => (UNKNOWN,UNKNOWN)
	 |   SOME v => v;

     fun ch_mode (UNKNOWN,UNKNOWN) READ = (INPUT,UNKNOWN)
      |  ch_mode (m,UNKNOWN) READ = (INPUT, UNKNOWN)
      |  ch_mode (m,UNKNOWN) WRITE = (m, OUTPUT)
      |  ch_mode (m,OUTPUT) WRITE = (m,OUTPUT)
      |  ch_mode (m,OUTPUT) READ = (m,INSTACK)
      |  ch_mode (m,INSTACK) READ = (m,INSTACK)
      |  ch_mode (m,INSTACK) WRITE = (m,OUTPUT)
      |  ch_mode _ _ = raise Fail "ch_mode: invalidMode";

     fun update_mode (REG r) action = 
	   regT := T.enter (!regT, r, ch_mode (peekT(!regT, r)) action)
      |  update_mode (TMEM i) action = 
           memCT := T.enter (!memCT, i, ch_mode (peekT(!memCT, i)) action)
      |  update_mode _ _ = 
	   ();

     fun one_stm ({oper = op1, dst = dst1, src = src1}) =
	  ( List.map (fn exp => update_mode exp READ) src1;
	    List.map (fn exp => update_mode exp WRITE) dst1
	  );

     fun mk_regL indexL = 
	List.map (fn n => REG n) indexL;

     fun mk_memL indexL =
	List.map TMEM indexL;

     fun filter_inputs mode = 
	 mk_regL (List.filter (fn n => #1 (T.look (!regT,n)) = mode) (T.listKeys (!regT))) @ 
	 mk_memL (List.filter (fn n => #1 (T.look (!memCT,n)) = mode) (T.listKeys (!memCT)));

     fun filter_out_stack mode =
         mk_regL (List.filter (fn n => #2 (T.look (!regT,n)) = mode) (T.listKeys (!regT))) @
         mk_memL (List.filter (fn n => #2 (T.look (!memCT,n)) = mode) (T.listKeys (!memCT)));

     val _ = List.map one_stm stmL;
     val (ins, temps, outs) = (filter_inputs INPUT, filter_out_stack INSTACK, filter_out_stack OUTPUT);

     in
	(ins, temps, outs)
     end


 (*---------------------------------------------------------------------------------*)
 (*      Print a statement                                                          *)
 (*---------------------------------------------------------------------------------*)

  fun print_op mmov = "mmov"
   |  print_op madd = "madd"
   |  print_op msub = "msub"
   |  print_op mrsb = "msrb"
   |  print_op mmul = "mmul"
   |  print_op mmla = "mmla"
   |  print_op mand = "mand"
   |  print_op morr = "morr"
   |  print_op meor = "meor"
   |  print_op mlsl = "mlsl"
   |  print_op mlsr = "mlsr"
   |  print_op masr = "masr"
   |  print_op mror = "mror"
   |  print_op mldr = "mldr"
   |  print_op mstr = "mstr"
   |  print_op mpop = "mpop"
   |  print_op mpush = "mpush"
   |  print_op mmrs = "mmrs"
   |  print_op mmsr = "mmsr"
   |  print_op mcall = "mcall"

  fun print_rop (eq) = "="
   |  print_rop (ne) = "!="
   |  print_rop (ge) = ">="
   |  print_rop (lt) = "<"
   |  print_rop (gt) = ">"
   |  print_rop (le) = "<="
   |  print_rop (cc) = "<+"
   |  print_rop (ls) = "<=+"
   |  print_rop (hi) = ">+"
   |  print_rop (cs) = ">=+"
   |  print_rop (al) = "al"
   |  print_rop (nv) = "nv"


  fun printReg r =
      let fun printAlias fp = "fp"
           |  printAlias ip = "ip"
           |  printAlias sp = "sp"
           |  printAlias lr = "lr"
           |  printAlias pc = "pc"
      in
          if r >= 11 then
              printAlias (toAlias r)
          else "r" ^ Int.toString r
      end

  val address_stride = ref 1;

  fun format_exp (TMEM e) =
        "[" ^ Int.toString e ^ "]"
   |  format_exp (MEM (r,j)) =
        (if j = 0 then
             "[" ^ printReg r ^ "]"
         else
             "[" ^ printReg r ^ ", " ^ "#" ^ Int.toString (j * !address_stride) ^ "]")
   |  format_exp (NCONST e) =
             "#" ^ Int.toString (Arbint.toInt e)
   |  format_exp (WCONST e) =
             "#" ^ Int.toString (Arbint.toInt e) ^ "w"
   |  format_exp (REG e) =
             printReg e
   |  format_exp (PAIR(e1,e2)) =
             "(" ^ format_exp e1 ^ "," ^ format_exp e2 ^ ")"
   |  format_exp _ = 
             raise Fail "format_exp:invalid IR expression";

  fun formatInst {oper = operator, src = sList, dst = dList} =
      if operator = mpush then
           print_op operator  ^ " " ^ format_exp (hd dList) ^ " {" ^ 
           format_exp (hd sList) ^ itlist (curry (fn (exp,str) => "," ^ format_exp exp ^ str)) (tl sList) "" ^
           "}"
      else if operator = mpop then
           print_op operator  ^ " " ^ format_exp (hd sList) ^ " {" ^
           format_exp (hd dList) ^ itlist (curry (fn (exp,str) => "," ^ format_exp exp ^ str)) (tl dList) "" ^
           "}"
      else
          print_op operator  ^ " " ^
          itlist (curry (fn (exp,str) => format_exp exp ^ str)) dList "" ^ " " ^
          (if null sList then ""
           else format_exp (hd sList) ^
               itlist (curry (fn (exp,str) => " " ^ format_exp exp ^ str)) (tl sList) "");


end
end