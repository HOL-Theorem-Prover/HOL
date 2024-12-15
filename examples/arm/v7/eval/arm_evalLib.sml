(* ------------------------------------------------------------------------ *)
(*  Ground-term evaluator                                                   *)
(*  =====================                                                   *)
(*  HOL evaluation works best with Moscow ML (standard kernel).             *)
(*  Under Poly/ML 5.3 (experimental kernel) a stack overflow occurs with    *)
(*  all but short runs (Dec. 2009).                                         *)
(* ------------------------------------------------------------------------ *)

structure arm_evalLib :> arm_evalLib =
struct

(* interactive use:
  app load ["arm_evalTheory", "armLib", "patriciaLib"];
*)

open HolKernel boolLib bossLib Parse;

(* ------------------------------------------------------------------------- *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

val ERR = Feedback.mk_HOL_ERR "arm_evalLib";

(* ------------------------------------------------------------------------- *)

val dest_strip = armSyntax.dest_strip;
val eval = boolSyntax.rhs o Thm.concl o bossLib.EVAL;

val lower_string = String.implode o map Char.toLower o String.explode;

fun mk_word i s = wordsSyntax.mk_wordi (Arbnum.fromHexString s,i);

val mk_word5  = mk_word 5;
val mk_word8  = mk_word 8;
val mk_word32 = mk_word 32;

fun mk_bool s =
  case lower_string s
    of "t"     => boolSyntax.T
     | "true"  => boolSyntax.T
     | "f"     => boolSyntax.F
     | "false" => boolSyntax.F
     | _       => raise ERR "mk_bool" ("invalid option: " ^ s);

val toNum = numSyntax.dest_numeral o fst o wordsSyntax.dest_n2w;
fun toHex w = StringCvt.padLeft #"0" w o Arbnum.toHexString;
fun hex w = toHex w o toNum;

local
  fun objdump infile outfile =
  let val _ = OS.FileSys.access (infile, [OS.FileSys.A_READ]) orelse
              raise OS.SysErr ("Cannot read file: " ^ infile,NONE)
      val s = String.concat ["arm-elf-objdump -d -j .text -j .data -j .rodata ",
                             infile, " > ", outfile]
      val _ = OS.Process.isSuccess (OS.Process.system s) orelse
              raise OS.SysErr ("Failed to run arm-elf-objdump",NONE)
  in
    ()
  end

  fun remove_padding s =
    s |> Substring.full
      |> Substring.dropl Char.isSpace
      |> Substring.dropr Char.isSpace
      |> Substring.string;

  fun parse_objdump infile =
  let val istrm = TextIO.openIn infile
      val inp = TextIO.inputAll istrm before TextIO.closeIn istrm
      val l = List.drop (String.tokens (fn c => c = #"\n") inp, 3)
      fun get_tokens s =
            case String.tokens (fn c => c = #":") s
            of (n::instr::rest) =>
                  (n, remove_padding
                        (hd (String.tokens (fn c => c = #"\t") instr)))
             | _ => raise ERR "parse_objdump" "failed to parse line"
  in
    Lib.mapfilter get_tokens l
  end
in
  fun load_elf infile =
  let val tmp = OS.FileSys.tmpName ()
      val _ = objdump infile tmp
  in
    parse_objdump tmp before OS.FileSys.remove tmp
  end
end

local
  fun bytes_of_word s =
  let fun ss i = mk_word8 (String.substring (s,i,2)) in
    List.map ss
      (case String.size s
       of 2 => [0]
        | 4 => [0,2]
        | 8 => [0,2,4,6]
        | _ => raise ERR "bytes_of_word" ("unexpected value: " ^ s))
  end

  fun add_bytes pc_ptree s =
    snd
      (List.foldr
        (fn (tm,(pc,ptree)) =>
           (Arbnum.plus1 pc, patriciaLib.add ptree (pc,tm))) pc_ptree
      (s |> String.tokens Char.isSpace
         |> List.map bytes_of_word
         |> List.rev
         |> List.concat))
in
  fun arm_load base ptree [] = ptree
    | arm_load base ptree ((pc,s)::rest) =
        arm_load base (add_bytes (Arbnum.+(base,pc), ptree) s) rest
end;

fun add_map f m1 m2 =
  List.foldl (fn ((k,v), m') => Redblackmap.insert (m', k, f v)) m1
    (Redblackmap.listItems m2);

type arm_load = patriciaLib.term_ptree * (string, Arbnum.num) Redblackmap.dict;

fun arm_load_from_elf base infile ((ptree,lmap):arm_load) =
  (arm_load (Arbnum.fromHexString base) ptree
    (List.map (Arbnum.fromHexString ## I) (load_elf infile)), lmap) : arm_load;

local
  fun arm_load_from f base x ((ptree,lmap):arm_load) =
    let
      val b = Arbnum.fromHexString base
      val (code, lmap2) = f x
    in
      (arm_load b ptree code,
       add_map (Lib.curry Arbnum.+ b) lmap lmap2) : arm_load
    end
in
  val arm_load_empty : arm_load =
        (patriciaLib.empty, Redblackmap.mkDict String.compare)
  val arm_load_from_file   = arm_load_from armLib.arm_assemble_from_file
  val arm_load_from_quote  = arm_load_from armLib.arm_assemble_from_quote
  val arm_load_from_string = arm_load_from armLib.arm_assemble_from_string
end;

val arm_eval_trace = ref 6;
val _ = Feedback.register_trace ("arm eval", arm_eval_trace, 6);

fun rname i =
  case i
  of 0  => "r0"
   | 1  => "r1"
   | 2  => "r2"
   | 3  => "r3"
   | 4  => "r4"
   | 5  => "r5"
   | 6  => "r6"
   | 7  => "r7"
   | 8  => "r8"
   | 9  => "r8_fiq"
   | 10 => "r9"
   | 11 => "r9_fiq"
   | 12 => "r10"
   | 13 => "r10_fiq"
   | 14 => "r11"
   | 15 => "r11_fiq"
   | 16 => "r12"
   | 17 => "r12_fiq"
   | 18 => "sp"
   | 19 => "sp_fiq"
   | 20 => "sp_irq"
   | 21 => "sp_svc"
   | 22 => "sp_abt"
   | 23 => "sp_und"
   | 24 => "sp_mon"
   | 25 => "lr"
   | 26 => "lr_fiq"
   | 27 => "lr_irq"
   | 28 => "lr_svc"
   | 29 => "lr_abt"
   | 30 => "lr_und"
   | 31 => "lr_mon"
   | 32 => "pc"
   | _ => raise ERR "rname" (Int.toString i);

fun psrname i =
  case i
  of 0 => "cpsr"
   | 1 => "spsr_fiq"
   | 2 => "spsr_irq"
   | 3 => "spsr_svc"
   | 4 => "spsr_mon"
   | 5 => "spsr_abt"
   | 6 => "spsr_und"
   | _ => raise ERR "psrname" (Int.toString i);

fun psrcname i =
  case i
  of 0  => "n"
   | 1  => "z"
   | 2  => "c"
   | 3  => "v"
   | 4  => "q"
   | 5  => "it"
   | 6  => "ge"
   | 7  => "e"
   | 8  => "a"
   | 9  => "i"
   | 10 => "f"
   | 11 => "t"
   | 12 => "m"
   | _ => raise ERR "psrcname" (Int.toString i);

local
  fun out l = print (String.concat (l @ ["\n"]))

  val ptree_arm_next =
        REWRITE_RULE [FUN_EQ_THM] arm_evalTheory.ptree_arm_next_def

  fun encode_psr tm =
        Term.mk_comb(``arm_coretypes$encode_psr``, tm) |> eval |> hex 8

  fun registers s = case (``^s.registers`` |> eval |> dest_strip)
                    of ("proc", [_,c]) =>
                         (case dest_strip c of ("RName_case", l) => SOME l
                                             | _ => NONE)
                     | _ => NONE

  fun psrs s = case (``^s.psrs`` |> eval |> dest_strip)
               of ("proc", [_,c]) =>
                     (case dest_strip c of ("PSRName_case", l) => SOME l
                                         | _ => NONE)
                | _ => NONE

  fun memory s = ``^s.memory``
                    |> eval
                    |> combinSyntax.strip_update |> fst
                    |> map (toNum ## I)
                    |> Listsort.sort (fn ((m,_),(n,_)) => Arbnum.compare (m,n))

  fun print_cycle cycle =
        out ["Cycle:\t\t", cycle |> numSyntax.dest_numeral |> Arbnum.toString]

  fun print_pc pc = out ["PC:\t\t", hex 8 pc]

  fun print_instr instr =
        let val (opc,code as (enc,_,ast)) =
                   case pairSyntax.strip_pair instr
                   of [a,b,c,d] => (a,(b,c,d))
                    | _ => raise ERR "print_instr" ""
            val (m,a) = if term_eq ast arm_astSyntax.Unpredictable_tm then
                          ("Unpredictable","")
                        else
                          armLib.arm_disassemble (armLib.Instruction code)
        in
          out [if term_eq enc armSyntax.Encoding_ARM_tm then
                 "ARM:\t"
               else if term_eq enc armSyntax.Encoding_Thumb_tm then
                 "16-bit Thumb:"
               else if term_eq enc armSyntax.Encoding_ThumbEE_tm then
                 "ThumbEE:"
               else
                 "32-bit Thumb:",
               "\t", stringSyntax.fromHOLstring opc, " ; ", m, " ", a]
        end

  fun print_regs (s,s') =
        case (registers s, registers s')
        of (SOME l1, SOME l2) =>
            (List.foldl
               (fn ((r1,r2), (first,n)) =>
                  (if term_eq r1 r2 then first else
                     (out [if first then "Registers:\t" else "\t\t", rname n,
                           " <- ", hex 8 r2]; false), n + 1))
               (true,0) (Lib.zip l1 l2); ())
         | _ => ()

  fun print_psrs (s,s') =
        case (psrs s, psrs s')
        of (SOME l1, SOME l2) =>
            (List.foldl
               (fn ((r1,r2), (first,n)) =>
                  (if term_eq r1 r2 then first else
                     (out [if first then "PSRs:\t\t" else "\t\t", psrname n,
                           " <- ", encode_psr r2]; false),
                   n + 1))
               (true,0) (Lib.zip l1 l2); ())
         | _ => ()

  fun print_mem s =
        let val l = ``^s.accesses`` |> eval |> listSyntax.dest_list |> fst in
           List.foldr
             (fn (tm,first) =>
                case dest_strip tm
                of ("MEM_WRITE", [a,d]) =>
                     (out [if first then "Memory:\t\t[" else "\t\t[",
                           hex 8 a, "] <- ", hex 2 d]; false)
                 | _ => first) true l; ()
        end

  fun print_trace (instr,pc,cycle,s,s') =
        (if !arm_eval_trace > 0 then print_cycle cycle else ();
         if !arm_eval_trace > 1 then print_pc pc else ();
         if !arm_eval_trace > 2 then print_instr instr else ();
         if !arm_eval_trace > 3 andalso isSome s' then
            print_regs (s,valOf s')
         else
            ();
         if !arm_eval_trace > 4 andalso isSome s' then
            print_psrs (s,valOf s')
         else
            ();
         if !arm_eval_trace > 5 andalso isSome s' then
            print_mem (valOf s')
         else
            ();
         if !arm_eval_trace > 1 then
           out [StringCvt.padLeft #"-" 40 ""]
         else
           ())
in
  fun PTREE_ARM_NEXT_CONV tm =
    case dest_strip tm
    of ("ptree_arm_next", [ii,instr,pc,cycle,s]) =>
           let val thm = (REWR_CONV ptree_arm_next THENC EVAL) tm
               val s' = case (thm |> concl |> rhs |> dest_strip)
                        of ("ValueState", [_,x]) => SOME x
                         | _ => NONE
               val _ = total print_trace (instr,pc,cycle,s,s')
           in
             thm
           end
     | _ => raise ERR "PTREE_ARM_NEXT_CONV" "not application of ptree_arm_next"

  fun print_arm_state thm =
        let val tm = thm |> concl |> rhs
            val (message,s) = pairSyntax.dest_pair tm
        in
          out ["Final Message\n",
               "=============\n\n",
               stringSyntax.fromHOLstring message, "\n"];
          if optionSyntax.is_some s then
            let val s' = optionSyntax.dest_some s
                val r = valOf (registers s')
                val p = valOf (psrs s')
                val m = memory s'
                fun pad n s = StringCvt.padRight #" " n s ^ ": "
            in
              out ["General Purpose Registers\n",
                   "=========================\n"];
              List.foldl
                (fn (r_i,i) => (out [i |> rname |> pad 9, hex 8 r_i]; i + 1))
                0 r;
              out ["\nProgram Status Registers\n",
                     "========================\n"];
              List.foldl
                (fn (r_i,i) =>
                   (out [i |> psrname |> pad 9, encode_psr r_i]; i + 1)) 0 p;
              if not (null m) then
                out ["\nMemory\n",
                       "======\n"]
              else
                ();
              List.app
                (fn (a,d) => (out [pad 11 ("[" ^ toHex 8 a ^ "]"), hex 2 d])) m
            end
          else if optionSyntax.is_none s then
            out ["state upredictable"]
          else
            out ["cannot print state"]
        end handle HOL_ERR _ => raise ERR "print_arm_state" "cannot print state"
end;

val _ = computeLib.add_conv
          (``arm_eval$ptree_arm_next``,5,PTREE_ARM_NEXT_CONV)
          computeLib.the_compset;

local
  fun decode_psr n = Term.mk_comb(``arm_coretypes$decode_psr``, n) |> eval

  val word8ptree =
    patriciaSyntax.mk_ptree_type
      (wordsSyntax.mk_word_type (fcpLib.index_type (Arbnum.fromInt 8)));

  val psr_options = List.tabulate (13, psrcname);

  val options = List.tabulate (33, rname) @
                List.tabulate (7, psrname) @
                ["arch", "reg_default", "psr_default", "mem_default"]

  fun mk_config_map opt s =
  let val l = s |> String.tokens (fn c => mem c [#",", #";"])
                |> map (String.tokens (fn c => c = #"=" orelse Char.isSpace c))
  in
    List.foldl
      (fn (e,d) =>
          case e
          of [r,v] =>
               let val lr = lower_string r
                   val _ = Lib.mem lr opt orelse
                             raise ERR "configure" ("invalid option: " ^ r)
               in
                 Redblackmap.insert (d, lr, v)
               end
           | _ => raise ERR "configure"
                    ("invalid assignment: " ^ String.concat e))
      (Redblackmap.mkDict String.compare) l
  end

  fun mk_mode s = mk_word5
    (case lower_string s
       of "usr" => "10"
        | "fiq" => "11"
        | "irq" => "12"
        | "svc" => "13"
        | "mon" => "16"
        | "abt" => "17"
        | "und" => "1B"
        | "sys" => "1F"
        | _     => raise ERR "mk_mode" ("invalid option: " ^ s))

  fun mk_word typ s =
        wordsSyntax.mk_n2w
          (numSyntax.mk_numeral (Arbnum.fromHexString s),
           wordsSyntax.dest_word_type typ)

  fun configure s =
    let val cmap = mk_config_map options s
        val default_reg = case Redblackmap.peek (cmap,"reg_default")
                            of SOME tm => mk_word32 tm
                             | NONE => wordsSyntax.mk_wordii (0,32)
        val default_psr = case Redblackmap.peek (cmap,"psr_default")
                            of SOME tm => decode_psr (mk_word32 tm)
                             | NONE => decode_psr (mk_word32 "10")
        val default_mem = case Redblackmap.peek (cmap,"mem_default")
                            of SOME tm => mk_word8 tm
                             | NONE => wordsSyntax.mk_wordii (0,8)
        fun lookup_reg s = case Redblackmap.peek (cmap,s)
                             of SOME tm => mk_word32 tm
                              | NONE => default_reg
        fun lookup_psr s = case Redblackmap.peek (cmap,s)
                             of SOME tm => decode_psr (mk_word32 tm)
                              | NONE => default_psr
        fun reg n = mk_var ("r" ^ Int.toString n, ``:word32``)
        fun psr n = mk_var ("r" ^ Int.toString n, ``:ARMpsr``)
        val reg_subst = List.tabulate
                          (33, fn i => (reg i |-> lookup_reg (rname i)))
        val psr_subst = List.tabulate
                          (7, fn i => (psr i |-> lookup_psr (psrname i)))
   in
     (case Option.map lower_string (Redblackmap.peek (cmap,"arch"))
      of SOME "armv4"   => ``arm_coretypes$ARMv4``
       | SOME "armv4t"  => ``arm_coretypes$ARMv4T``
       | SOME "armv5t"  => ``arm_coretypes$ARMv5T``
       | SOME "armv5te" => ``arm_coretypes$ARMv5TE``
       | SOME "armv6"   => ``arm_coretypes$ARMv6``
       | SOME "armv6k"  => ``arm_coretypes$ARMv6K``
       | SOME "armv6t2" => ``arm_coretypes$ARMv6T2``
       | SOME "armv7-a" => ``arm_coretypes$ARMv7_A``
       | SOME "armv7-r" => ``arm_coretypes$ARMv7_R``
       | SOME a => raise ERR "configure" ("not a valid architecture: " ^ a)
       | NONE => ``ARMv7_A``,
      Term.subst reg_subst
        ``RName_case r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
                     r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
                     r26 r27 r28 r29 r30 r31 (r32:word32)``,
     Term.subst psr_subst ``PSRName_case r0 r1 r2 r3 r4 r5 (r6:ARMpsr)``,
     default_mem)
   end
in
  fun encode_psr s =
    let val cmap = mk_config_map psr_options s
        fun psrtype i = case i
                          of 5  => ``:word8``
                           | 6  => ``:word4``
                           | 12 => ``:word5``
                           | _  => ``:bool``
        fun lookup typ s =
              case Redblackmap.peek (cmap,s)
                of SOME tm => if wordsSyntax.is_word_type typ then
                                if s = "m" then
                                  mk_mode tm
                                    handle HOL_ERR _ => mk_word typ tm
                                else
                                  mk_word typ tm
                              else
                                mk_bool tm
                   | NONE => if wordsSyntax.is_word_type typ then
                               if s = "m" then
                                 mk_mode "usr"
                               else
                                 mk_word typ "0"
                             else if s = "e" then
                               boolSyntax.T
                             else
                               boolSyntax.F
        val psr_subst = List.tabulate
                          (13, fn i => let val typ = psrtype i in
                                 (mk_var ("r" ^ Int.toString i, typ) |->
                                  lookup typ (psrcname i)) end)
    in
      ``encode_psr
          <| N := r0; Z := r1; C := r2; V := r3; Q := r4; IT := r5; J := F;
             Reserved := 0w; GE := r6; E := r7; A := r8; I := r9; F := r10;
             T := r11; M := r12 |>``
        |> Term.subst psr_subst
        |> eval
        |> wordsSyntax.dest_n2w |> fst
        |> numSyntax.dest_numeral
        |> Arbnum.toHexString
    end

  fun arm_eval s prog n =
  let val (arch,reg,psr,mem) = configure s
      val _ = type_of prog = word8ptree andalso null (Term.free_vars prog)
                orelse raise ERR "arm_eval"
                         "program is not ground term of type :word8 ptree"
      val c = numSyntax.term_of_int n
  in
    EVAL ``ptree_arm_run ^prog (mk_arm_state ^arch ^reg ^psr ^mem ^prog) ^c``
  end
end;

local
  val address = StringCvt.padLeft #"0" 4 o Arbnum.toHexString
  fun line (n,tm) = String.concat [address n, " ", hex 2 tm]
  val pp_code = patriciaLib.custom_pp_term_ptree
                  (fn pps => fn b => ())
                  (fn pps => fn x => PP.add_string pps (line x)) ~1
in
  fun output_program_to_stream ostrm t =
  let val pps = PP.mk_ppstream { consumer = fn s => TextIO.output(ostrm, s),
                                 linewidth = 11,
                                 flush = fn () => TextIO.flushOut ostrm }
  in
    pp_code pps t before PP.flush_ppstream pps
  end
end;

fun output_program opt t =
  case opt
  of SOME s =>
       let val ostrm = TextIO.openOut s in
         output_program_to_stream ostrm t before TextIO.closeOut ostrm
       end
   | NONE =>
       output_program_to_stream TextIO.stdOut t;

(* Standalone assembler (Poly/ML):

open arm_evalLib;

fun main () =
let val opt =
          case CommandLine.arguments()
          of [infile] =>
                SOME {base = "0", infile = infile, outfile = NONE}
           | [infile,outfile] =>
                SOME {base = "0", infile = infile, outfile = SOME outfile}
           | ["-b", base, infile] =>
                if Lib.can Arbnum.fromHexString base then
                  SOME {base = base, infile = infile, outfile = NONE}
                else
                  NONE
           | ["-b", base,infile,outfile] =>
                if Lib.can Arbnum.fromHexString base then
                  SOME {base = base, infile = infile, outfile = SOME outfile}
                else
                  NONE
           | _ => NONE
in
  case opt
  of SOME {base,infile,outfile} => let
         val e = OS.Path.ext infile
         val elf = case e
                   of SOME "o" => true
                    | SOME _ => false
                    | NONE => true
         val (load,m) = if elf then
                          (arm_load_from_elf, "converted ")
                        else
                          (arm_load_from_file, "assembled ")
         val tree = fst (load base infile arm_load_empty)
         val _ = output_program outfile tree
       in
         case outfile
         of SOME s =>
              print ("Successfully " ^ m ^ infile ^ " to " ^ s  ^ "\n")
          | NONE => ()
       end
   | NONE => print ("usage: " ^ CommandLine.name() ^
                    " [-b <base address>] <input file> [<output file>]\n")
end handle
   HOL_ERR {origin_function,message,...} =>
     print (origin_function ^ ": " ^ message ^ "\n")
 | SysErr (s, _) => print (s ^ "\n")
 | Io {name, cause = SysErr (s, _), function} =>
     print (function ^ ": " ^ s ^ ": " ^ name ^ "\n");

val _ = PolyML.export("HOLas", main);

gcc -o HOLas HOLas.o -L$HOME/polyml/lib -lpolymain -lpolyml
*)

(* val _ = installPP (mosmlpp patriciaLib.pp_term_ptree); *)

(* ------------------------------------------------------------------------- *)

end
