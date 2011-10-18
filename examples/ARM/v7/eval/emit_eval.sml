structure emit_eval :> emit_eval =
struct

(* intactive use:
  app load
     ["combinML", "pairML", "sumML", "numML", "listML", "setML", "optionML",
      "rich_listML", "basicSizeML", "stringML", "bitML", "fcpML", "wordsML",
      "intML", "sortingML", "patriciaML", "armML"];
*)

local
  open combinML pairML sumML numML listML setML optionML rich_listML basicSizeML
       stringML bitML fcpML wordsML intML sortingML patriciaML armML
in end;

(* ------------------------------------------------------------------------ *)

type arm_mem = armML.word8 patriciaML.ptree

fun mem i = List.exists (fn x => x = i)

fun load_program (s,t) =
let val istrm = TextIO.openIn s
    val a = TextIO.inputAll istrm before TextIO.closeIn istrm
    fun pair [a,b] = (numML.fromHexString a,
                      wordsML.toWord8 (numML.fromHexString b))
      | pair _ = raise Match
in
  a |> String.tokens (fn c => c = #"\n")
    |> List.map (pair o String.tokens Char.isSpace)
    |> patriciaML.ADD_LIST t
end;

val load_programs = List.foldl load_program patriciaML.Empty;

(* ------------------------------------------------------------------------ *)

fun toWord i n = wordsML.fromNum (n, fcpML.ITSELF (numML.fromInt i));
val zero32 = wordsML.toWord32 numML.ZERO;

fun mk_arm_state arch regs psrs md mem =
  armML.arm_state
    (armML.proc numML.ZERO regs,
     armML.proc numML.ZERO psrs,
     combinML.K true,        (* event_register *)
     combinML.K false,       (* interrupt_wait *)
     fn a => case patriciaML.PEEK mem (wordsML.w2n a)
             of SOME d => d
              | NONE => md,
     [],                     (* accesses *)
     armML.ARMinfo (arch,setML.EMPTY,true),
     armML.Coprocessors
       (armML.coproc_state
          (armML.CP14reg zero32,
           armML.CP15reg
            (armML.CP15sctlr (true,  false, false, false, true,  true,
                              false, false, false, false, false, false,
                              false, false, false, false, false, false,
                              true,  false),
             armML.CP15scr   (false, false, false, false, false, false, false),
             armML.CP15nsacr (false, false, false, toWord 14 numML.ZERO),
             armML.CP15vbar  (zero32, zero32),
             zero32)),
        combinML.K (armML.constC false),
        combinML.K (armML.constC ()),
        combinML.K (armML.constC numML.ZERO),
        combinML.K (combinML.K (armML.constC ())),
        combinML.K (armML.constC []),
        combinML.K (combinML.K (armML.constC ())),
        combinML.K (armML.constC zero32),
        combinML.K (combinML.K (armML.constC ())),
        combinML.K (armML.constC (zero32,zero32))),
     armML.ExclusiveMonitors
       ((combinML.K setML.EMPTY, setML.EMPTY),
        combinML.K (armML.constE ()),
        combinML.K (armML.constE ()),
        combinML.K (armML.constE false),
        combinML.K (armML.constE false),
        combinML.K (armML.constE ()),
        combinML.K (armML.constE ())));

(* ------------------------------------------------------------------------ *)

fun w2int w = w |> wordsML.w2n |> numML.toInt |> valOf

fun architecture a =
  case a
  of "armv4"   => armML.ARMv4
   | "armv4t"  => armML.ARMv4T
   | "armv5t"  => armML.ARMv5T
   | "armv5te" => armML.ARMv5TE
   | "armv6"   => armML.ARMv6
   | "armv6k"  => armML.ARMv6K
   | "armv6t2" => armML.ARMv6T2
   | "armv7-a" => armML.ARMv7_A
   | "armv7-r" => armML.ARMv7_R
   | _ => raise Fail "architecture";

fun string_of_rname r =
  case r
  of armML.RName_0usr  => "r0"
   | armML.RName_1usr  => "r1"
   | armML.RName_2usr  => "r2"
   | armML.RName_3usr  => "r3"
   | armML.RName_4usr  => "r4"
   | armML.RName_5usr  => "r5"
   | armML.RName_6usr  => "r6"
   | armML.RName_7usr  => "r7"
   | armML.RName_8usr  => "r8"
   | armML.RName_8fiq  => "r8_fiq"
   | armML.RName_9usr  => "r9"
   | armML.RName_9fiq  => "r9_fiq"
   | armML.RName_10usr => "r10"
   | armML.RName_10fiq => "r10_fiq"
   | armML.RName_11usr => "r11"
   | armML.RName_11fiq => "r11_fiq"
   | armML.RName_12usr => "r12"
   | armML.RName_12fiq => "r12_fiq"
   | armML.RName_SPusr => "sp"
   | armML.RName_SPfiq => "sp_fiq"
   | armML.RName_SPirq => "sp_irq"
   | armML.RName_SPsvc => "sp_svc"
   | armML.RName_SPabt => "sp_abt"
   | armML.RName_SPund => "sp_und"
   | armML.RName_SPmon => "sp_mon"
   | armML.RName_LRusr => "lr"
   | armML.RName_LRfiq => "lr_fiq"
   | armML.RName_LRirq => "lr_irq"
   | armML.RName_LRsvc => "lr_svc"
   | armML.RName_LRabt => "lr_abt"
   | armML.RName_LRund => "lr_und"
   | armML.RName_LRmon => "lr_mon"
   | armML.RName_PC    => "pc";

fun rname i =
  case i
  of 0  => armML.RName_0usr
   | 1  => armML.RName_1usr
   | 2  => armML.RName_2usr
   | 3  => armML.RName_3usr
   | 4  => armML.RName_4usr
   | 5  => armML.RName_5usr
   | 6  => armML.RName_6usr
   | 7  => armML.RName_7usr
   | 8  => armML.RName_8usr
   | 9  => armML.RName_8fiq
   | 10 => armML.RName_9usr
   | 11 => armML.RName_9fiq
   | 12 => armML.RName_10usr
   | 13 => armML.RName_10fiq
   | 14 => armML.RName_11usr
   | 15 => armML.RName_11fiq
   | 16 => armML.RName_12usr
   | 17 => armML.RName_12fiq
   | 18 => armML.RName_SPusr
   | 19 => armML.RName_SPfiq
   | 20 => armML.RName_SPirq
   | 21 => armML.RName_SPsvc
   | 22 => armML.RName_SPabt
   | 23 => armML.RName_SPund
   | 24 => armML.RName_SPmon
   | 25 => armML.RName_LRusr
   | 26 => armML.RName_LRfiq
   | 27 => armML.RName_LRirq
   | 28 => armML.RName_LRsvc
   | 29 => armML.RName_LRabt
   | 30 => armML.RName_LRund
   | 31 => armML.RName_LRmon
   | 32 => armML.RName_PC
   | _ => raise Fail "rname";

fun string_of_psrname p =
  case p
  of armML.CPSR     => "cpsr"
   | armML.SPSR_fiq => "spsr_fiq"
   | armML.SPSR_irq => "spsr_irq"
   | armML.SPSR_svc => "spsr_svc"
   | armML.SPSR_mon => "spsr_mon"
   | armML.SPSR_abt => "spsr_abt"
   | armML.SPSR_und => "spsr_und"

fun psrname i =
  case i
  of 0 => armML.CPSR
   | 1 => armML.SPSR_fiq
   | 2 => armML.SPSR_irq
   | 3 => armML.SPSR_svc
   | 4 => armML.SPSR_mon
   | 5 => armML.SPSR_abt
   | 6 => armML.SPSR_und
   | _ => raise Fail "psrname";

fun encoding armML.Encoding_Thumb   = "16-bit Thumb:\t"
  | encoding armML.Encoding_Thumb2  = "32-bit Thumb:\t"
  | encoding armML.Encoding_ThumbEE = "ThumbEE:\t"
  | encoding armML.Encoding_ARM     = "ARM:\t\t"

fun condition (cond:armML.word4) =
  case w2int cond
  of 0  => "eq"
   | 1  => "ne"
   | 2  => "cs"
   | 3  => "cc"
   | 4  => "mi"
   | 5  => "pl"
   | 6  => "vs"
   | 7  => "vc"
   | 8  => "hi"
   | 9  => "ls"
   | 10 => "ge"
   | 11 => "lt"
   | 12 => "gt"
   | 13 => "le"
   | 14 => "al"
   | _  => raise Fail "condition";

fun data_processing (enc,opc,n) =
  case w2int opc
  of 0  => "and"
   | 1  => "eor"
   | 2  => "sub"
   | 3  => "rsb"
   | 4  => "add"
   | 5  => "adc"
   | 6  => "sbc"
   | 7  => "rsc"
   | 8  => "tst"
   | 9  => "teq"
   | 10 => "cmp"
   | 11 => "cmn"
   | 12 => "orr"
   | 13 => "mov"
   | 14 => "bic"
   | 15 => if enc = armML.Encoding_Thumb2 andalso (w2int n <> 15) then
             "orn"
           else
             "mvn"
   | _  => raise Fail "data_processing";

fun instruction (enc,instr) =
  case instr
  of armML.Unpredictable                      => "unpredictable"
   | armML.Undefined                          => "undefined"
   | armML.Branch (armML.Branch_Target _)     => "branch target"
   | armML.Branch (armML.Branch_Exchange _)   => "branch exchange"
   | armML.Branch (armML.Compare_Branch _)    => "compare branch"
   | armML.Branch (armML.Check_Array _)       => "check array"
   | armML.Branch (armML.Table_Branch_Byte _) => "table branch byte"
   | armML.Branch (armML.Branch_Link_Exchange_Immediate _) =>
       "branch link exchange (imm)"
   | armML.Branch (armML.Branch_Link_Exchange_Register _) =>
       "branch link exchange (reg)"
   | armML.Branch (armML.Handler_Branch_Link _) =>
        "handler branch (link)"
   | armML.Branch (armML.Handler_Branch_Link_Parameter _) =>
        "handler branch with link and parameter"
   | armML.Branch (armML.Handler_Branch_Parameter _) =>
        "handler branch with parameter"
   | armML.DataProcessing (armML.Data_Processing (opc,_,n,_,_)) =>
       data_processing (enc,opc,n)
   | armML.DataProcessing (armML.Add_Sub (add,_,_,_)) =>
       if add then "add (wide)" else "sub (wide)"
   | armML.DataProcessing (armML.Move_Halfword _)     => "move halfword"
   | armML.DataProcessing (armML.Divide _)            => "divide"
   | armML.DataProcessing (armML.Multiply _)          => "multiply"
   | armML.DataProcessing (armML.Multiply_Subtract _) => "multiply subtract"
   | armML.DataProcessing (armML.Multiply_Long _)     => "multiply (long)"
   | armML.DataProcessing (armML.Saturate _)          => "saturate"
   | armML.DataProcessing (armML.Saturate_16 _)       => "saturate (16)"
   | armML.DataProcessing (armML.Select_Bytes _)      => "select bytes"
   | armML.DataProcessing (armML.Extend_Byte _)       => "extend byte"
   | armML.DataProcessing (armML.Extend_Byte_16 _)    => "extend byte (16)"
   | armML.DataProcessing (armML.Extend_Halfword _)   => "extend halfword"
   | armML.DataProcessing (armML.Pack_Halfword _)     => "pack halfword"
   | armML.DataProcessing (armML.Reverse_Bits _)      => "reverse bits"
   | armML.DataProcessing (armML.Byte_Reverse_Word _) => "byte reverse word"
   | armML.DataProcessing (armML.Byte_Reverse_Packed_Halfword _) =>
       "byte reverse packed halfword"
   | armML.DataProcessing (armML.Byte_Reverse_Signed_Halfword _) =>
       "byte reverse signed halfword"
   | armML.DataProcessing (armML.Signed_Halfword_Multiply _) =>
       "signed halfword multiply"
   | armML.DataProcessing (armML.Signed_Multiply_Dual _) =>
       "signed multiply dual"
   | armML.DataProcessing (armML.Signed_Multiply_Long_Dual _) =>
       "signed multiply dual (long)"
   | armML.DataProcessing (armML.Signed_Most_Significant_Multiply _) =>
       "signed most significant multiply"
   | armML.DataProcessing (armML.Signed_Most_Significant_Multiply_Subtract _) =>
       "signed most significant multiply subtract"
   | armML.DataProcessing (armML.Multiply_Accumulate_Accumulate _) =>
       "multiply accumulate accumulate"
   | armML.DataProcessing (armML.Saturating_Add_Subtract _) =>
       "saturating add subtract"
   | armML.DataProcessing (armML.Bit_Field_Clear_Insert _) =>
       "bit field clear/insert"
   | armML.DataProcessing (armML.Bit_Field_Extract _) =>
       "bit field extract"
   | armML.DataProcessing (armML.Count_Leading_Zeroes _) =>
       "count leading zeroes"
   | armML.DataProcessing (armML.Unsigned_Sum_Absolute_Differences _) =>
       "unsigned sum absolute differences"
   | armML.DataProcessing (armML.Parallel_Add_Subtract _) =>
       "parallel add subtract"
   | armML.StatusAccess (armML.Status_to_Register _) =>
       "program status to register (mrs)"
   | armML.StatusAccess (armML.Register_to_Status _) =>
       "register to program status (msr)"
   | armML.StatusAccess (armML.Immediate_to_Status _) =>
       "immediate to program status (msr)"
   | armML.StatusAccess (armML.Change_Processor_State _) =>
       "change processor state"
   | armML.StatusAccess (armML.Set_Endianness _) =>
       "set endianess"
   | armML.LoadStore (armML.Load _)            => "load"
   | armML.LoadStore (armML.Store _)           => "store"
   | armML.LoadStore (armML.Load_Halfword _)   => "load halfword"
   | armML.LoadStore (armML.Store_Halfword _)  => "store halfword"
   | armML.LoadStore (armML.Load_Dual _)       => "load dual"
   | armML.LoadStore (armML.Store_Dual _)      => "store dual"
   | armML.LoadStore (armML.Load_Multiple _)   => "load multiple"
   | armML.LoadStore (armML.Store_Multiple _)  => "store multiple"
   | armML.LoadStore (armML.Load_Exclusive _)  => "load exclusive"
   | armML.LoadStore (armML.Store_Exclusive _) => "store exclusive"
   | armML.LoadStore (armML.Load_Exclusive_Doubleword _) =>
       "load exclusive doubleword"
   | armML.LoadStore (armML.Store_Exclusive_Doubleword _) =>
       "store exclusive doubleword"
   | armML.LoadStore (armML.Load_Exclusive_Halfword _) =>
       "load exclusive halfword"
   | armML.LoadStore (armML.Store_Exclusive_Halfword _) =>
       "store exclusive halfword"
   | armML.LoadStore (armML.Load_Exclusive_Byte _) =>
       "load exclusive byte"
   | armML.LoadStore (armML.Store_Exclusive_Byte _) =>
       "store exclusive byte"
   | armML.LoadStore (armML.Store_Return_State _) =>
       "store return state"
   | armML.LoadStore (armML.Return_From_Exception _) =>
       "return from exception"
   | armML.Miscellaneous armML.Clear_Exclusive         => "clear exclusive"
   | armML.Miscellaneous (armML.Hint _)                => "hint"
   | armML.Miscellaneous (armML.Breakpoint _)          => "breakpoint"
   | armML.Miscellaneous (armML.Swap _)                => "swap"
   | armML.Miscellaneous (armML.Preload_Data _)        => "preload data"
   | armML.Miscellaneous (armML.Preload_Instruction _) => "preload instruction"
   | armML.Miscellaneous (armML.Supervisor_Call _)     => "supervisor call"
   | armML.Miscellaneous (armML.Secure_Monitor_Call _) => "secure monitor call"
   | armML.Miscellaneous (armML.If_Then _)             => "if-then"
   | armML.Miscellaneous (armML.Enterx_Leavex true)    => "enterx"
   | armML.Miscellaneous (armML.Enterx_Leavex false)   => "leavex"
   | armML.Miscellaneous (armML.Data_Memory_Barrier _) => "data memory barrier"
   | armML.Miscellaneous (armML.Data_Synchronization_Barrier _) =>
       "data synchronization barrier"
   | armML.Miscellaneous (armML.Instruction_Synchronization_Barrier _) =>
       "instruction synchronization barrier"
   | armML.Coprocessor _    => "coprocessor"

fun for_se base top f =
 let fun For i = if i > top then () else (f i; For (i+1)) in For base end;

val word8  = wordsML.toWord8 o numML.fromHexString
val word32 = wordsML.toWord32 o numML.fromHexString

fun for_word32 base top f =
 let val t = word32 top
     val b = word32 base
     val one = wordsML.toWord32 numML.ONE
     val add1 = wordsML.word_add one
     fun For i = if wordsML.word_gt i t then
                   ()
                 else
                   (f i; For (add1 i))
 in For b end;

fun hex n s = StringCvt.padLeft #"0" n (wordsML.word_to_hex_string s);

val traceOut = ref TextIO.stdOut;

fun out l = TextIO.output (!traceOut, String.concat (l @ ["\n"]));

fun print_reg_updates ii (s1,s2) =
let val reg1 = armML.arm_state_registers s1
    val reg2 = armML.arm_state_registers s2
    val psr1 = armML.arm_state_psrs s1
    val psr2 = armML.arm_state_psrs s2
    val id = armML.iiid_proc ii
    val first = ref true
in
  for_se 0 32 (fn i =>
    let val r = rname i
        val d = reg2 (id,r)
    in
      if reg1 (id,r) <> d then
        out [if !first then
               (first := false; "Registers:\t")
             else
               "\t\t", string_of_rname r, " <- ", hex 8 d]
      else
        ()
    end);
  for_se 0 6 (fn i =>
    let val r = psrname i
        val d = psr2 (id,r)
    in
      if psr1 (id,r) <> d then
        out [if !first then
               (first := false; "Registers:\t")
             else
               "\t\t", string_of_psrname r, " <- ", hex 8 (armML.encode_psr d)]
      else
        ()
    end)
end;

fun print_mem_updates s =
let val first = ref true in
  List.app (fn acc =>
    case acc
    of armML.MEM_WRITE (a,d) =>
         out [if !first then
                (first := false; "Memory:")
              else
                "", "\t\t[", hex 8 a, "] <- ", hex 2 d]
     | _ => ()) (List.rev (armML.arm_state_accesses s))
end

fun print_instr (opc,(enc,(cond,instr))) =
  out [encoding enc, opc, " ; ", condition cond, ", ", instruction (enc,instr)]

val instruction_printer = ref print_instr;

type run_trace =
  { cycle : bool, pc : bool, ireg : bool, regs : bool, mem : bool,
    rule : int * char };

fun int_to_trace i =
  { cycle = i > 0,
    pc    = i > 1,
    ireg  = i > 2,
    regs  = i > 3,
    mem   = i > 4,
    rule  = if i > 1 then (40,#"-") else (0,#" ") };

fun print_trace ii (trace : run_trace) (cycle,pc,instr,s1,s2) =
  (if #cycle trace then out ["Cycle:\t\t", Int.toString cycle] else ();
   if #pc trace then out ["PC:\t\t", hex 8 pc] else ();
   if #ireg trace then (!instruction_printer) instr else ();
   if #regs trace then print_reg_updates ii (s1,s2) else ();
   if #mem trace then print_mem_updates s2 else ();
   let val (l,c) = #rule trace in
     if l > 0 then out [StringCvt.padLeft c l ""] else ()
   end);

fun print_arm_state s =
let val reg = armML.arm_state_registers s
    val psr = armML.arm_state_psrs s
    val ii = armML.iiid numML.ZERO
    val id = armML.iiid_proc ii
    fun pad n s = StringCvt.padRight #" " n s ^ ": "
in
  out ["General Purpose Registers\n",
       "=========================\n"];
  for_se 0 32 (fn i =>
    let val r = rname i in
      out [pad 9 (string_of_rname r), hex 8 (reg (id,r))]
    end);
  out ["\nProgram Status Registers\n",
       "========================\n"];
  for_se 0 6 (fn i =>
    let val r = psrname i
    in
      out [pad 9 (string_of_psrname r), hex 8 (armML.encode_psr (psr (id,r)))]
    end)
end

(*
fun examine_arm_mem mem =
let
  fun print_arm_mem b t =
        for_word32 b t (fn a => out ["[", hex 8 a, "] : ", hex 2 (mem a)])

   fun print_range () : unit =
     let val _ = print "Enter memory range [hex - hex]: "
         val s = valOf (TextIO.inputLine TextIO.stdIn)
         val (b,t) = case String.tokens
                            (fn c => Char.isSpace c orelse c = #"-") s
                     of [l,r] => let val x = word32 l
                                     val y = word32 r
                                 in
                                   if wordsML.word_lo x y then (l,r) else (r,l)
                                 end
                      | _ => raise Fail "print_arm_mem"
     in
       print_arm_mem b t; print_range ()
     end
in
  print_range ()
end
*)

local
  fun print_line (a,b : wordsML.word8) =
        out ["[", hex 8 (wordsML.toWord32 a), "] : ", hex 2 b]
  fun mem_compare ((a1,_),(a2,_)) =
         if a1 = a2 then
           General.EQUAL
         else if numML.< a1 a2 then
           General.LESS
         else
           General.GREATER
  val print_mem = List.app print_line o Listsort.sort mem_compare
in
  val print_arm_mem = print_mem o patriciaML.toList
  fun print_diff_arm_mem prog1 prog2 =
  let
    val new = Lib.set_diff (patriciaML.toList prog2) (patriciaML.toList prog1)
  in
    out ["\nModified Memory\n",
         "===============\n"];
    print_mem new
  end
end

fun print_arm_run prog (message,prog_state) =
  (if message = "" then () else
     out ["Final Message\n", "=============\n\n", message, "\n"];
   case prog_state
   of SOME (prog',state) =>
        (print_arm_state state; print_diff_arm_mem prog prog')
   | _ => out ["state upredictable"]);

(* ------------------------------------------------------------------------ *)

fun update_prog p [] = p
  | update_prog p (armML.MEM_READ _ :: l) = update_prog p l
  | update_prog p (armML.MEM_WRITE (a,d) :: l) =
      update_prog (patriciaML.ADD p (wordsML.w2n a, d)) l

fun ptree_arm_run run_trace (prog,state) t =
let
  val ii = armML.iiid numML.ZERO
  val arch = case armML.read_arch ii state
             of armML.Error s => raise Fail "couldn't read Architecture"
              | armML.ValueState (a,_) => a
  fun ptree_arm_loop prog' cycle t =
    armML.seqT (armML.waiting_for_interrupt ii) (fn wfi =>
      if wfi orelse t = 0 then
        armML.constT ((prog',cycle),"finished")
      else
        armML.attempt (prog',cycle)
          (armML.fetch_instruction ii
             (armML.ptree_read_word prog') (armML.ptree_read_halfword prog'))
          (fn instr =>
             armML.seqT
               (armML.writeT
                    (armML.arm_state_accesses_fupd (combinML.K []))) (fn _ =>
                  armML.seqT (armML.readT combinML.I) (fn s1 =>
                    armML.seqT (armML.arm_instr ii (pairML.SND instr))
                      (fn _ => armML.seqT (armML.readT combinML.I) (fn s2 =>
                         let
                           val pc = armML.arm_state_registers s1
                                      (numML.ZERO, armML.RName_PC)
                           val _ = print_trace ii run_trace
                                     (cycle,pc,instr,s1,s2)
                         in
                           ptree_arm_loop
                             (update_prog prog' (armML.arm_state_accesses s2))
                             (cycle + 1)
                             (if t < 0 then t else t - 1)
                         end))))))
in
  case ptree_arm_loop prog 0 t state
  of armML.Error e => (e, NONE)
   | armML.ValueState (((prog',c),v), s') =>
       ("at cycle " ^ Int.toString c ^ ": " ^ v, SOME (prog',s'))
end;

(* ------------------------------------------------------------------------ *)

val lower_string = String.implode o map Char.toLower o String.explode;

fun pluck P =
 let fun pl _ [] = raise Fail "pluck: predicate not satisfied"
       | pl A (h::t) = if P h then (h, List.revAppend(A,t)) else pl (h::A) t
 in pl []
 end;

fun init_config prog s =
let val l = s |> String.tokens (fn c => mem c [#",", #";",#"\n"])
              |> map (fn a =>
                   case String.tokens (fn c => c = #"=" orelse Char.isSpace c) a
                   of [l,r] => (lower_string l, lower_string r)
                    | _ => raise Fail "init_config")
    val ((_,arch),l) = pluck (fn (n,_) => n = "arch") l
                         handle Fail _ => (("","armv7-a"),l)
    val ((_,default_reg),l) = pluck (fn (n,_) => n = "reg_") l
                                handle Fail _ => (("","0"),l)
    val ((_,default_psr),l) = pluck (fn (n,_) => n = "_psr") l
                                handle Fail _ => (("","10"),l)
    val ((_,default_mem),l) = pluck (fn (n,_) => n = "mem_") l
                                handle Fail _ => (("","0"),l)
    val dreg = word32 default_reg
    val dpsr = armML.decode_psr (word32 default_psr)
in
  mk_arm_state (architecture arch)
   (fn r => case List.find (fn (n,_) => string_of_rname r = n) l
            of SOME (_,v) => word32 v
             | _ => dreg)
   (fn r => case List.find (fn (n,_) => string_of_psrname r = n) l
            of SOME (_,v) => armML.decode_psr (word32 v)
             | _ => dpsr)
   (word8 default_mem) prog
end

(* ------------------------------------------------------------------------ *)

(*
fun time f x =
  let
    fun p t =
      let
        val s = Time.fmt 3 t
      in
        case size (List.last (String.fields (fn x => x = #".") s)) of 3 => s
        | 2 => s ^ "0"
        | 1 => s ^ "00"
        | _ => raise Fail "time"
      end
    val c = Timer.startCPUTimer ()
    val r = Timer.startRealTimer ()
    fun pt () =
      let
        val {usr, sys, ...} = Timer.checkCPUTimer c
        val real = Timer.checkRealTimer r
      in
        print
        ("User: " ^ p usr ^ "  System: " ^ p sys ^ "  Real: " ^ p real ^ "\n")
      end
    val y = f x handle e => (pt (); raise e)
    val () = pt ()
  in
    y
  end;
*)

fun input_number P message =
let val _ = print message in
  case TextIO.inputLine TextIO.stdIn
  of NONE => input_number P message
   | SOME s => case Int.fromString s
               of SOME n => if P n then n else input_number P message
                | NONE => input_number P message
end

fun arm_run trace prog options count =
let
  val state = init_config prog options
  val out = ptree_arm_run trace (prog,state) count
in
  out
end;

fun main () =
let
  val prog = load_programs (CommandLine.arguments())
  val _ = print "Enter architecture, initial register values and default\
                \ memory content.\n(Enter values as Hex.)\n\
                \For example: arch = ARMv7-A, pc = A00, r0 = AF, r_ = 10,\n\
                \             cpsr = 80000010, _psr = 10, mem_ = 0\n> "
  val options = valOf (TextIO.inputLine TextIO.stdIn)
  val trace = input_number (fn i => 0 <= i andalso i <= 5)
                "Enter trace level [0 - 5]: "
  val count = input_number (fn i => ~1 <= i) "Enter number of cycles: "
in
  case time (arm_run (int_to_trace trace) prog options) count
  of out as (_, SOME _) => print_arm_run prog out
   | (e, NONE) => out [e]
end;

(*
let
  fun pp _ _ (_: 'a patriciaML.ptree) = PolyML.PrettyString "?"
in
  PolyML.addPrettyPrinter pp
end;
val prog = load_programs ["md5.o"];
val options = "pc = 8000, r0 = C0000, lr = A0000, sp = B0000, cpsr = 10";
val trace = 5;

val _ = PolyML.export("HOLarm", main);

gcc -o run HOLarm.o -L$HOME/polyml/lib -lpolymain -lpolyml
*)

end

(* ------------------------------------------------------------------------ *)
