(* interactive use:
val HOLDIR = "/local/scratch/acjf3/HOL/";
val _ = loadPath := !loadPath @ ".." :: map (fn x => HOLDIR ^ x)
     ["tools/mlyacc/mlyacclib", "tools/mlton/pre",
      "src/portableML", "src/theoryML"];
val _ = app load ["assemblerML", "armML"];
val _ = app load ["OS", "Bool", "Time", "Timer", "CommandLine",
                  "Redblackmap", "ListPair"];
*)

(* ------------------------------------------------------------------------- *)

structure memoryML :>
sig
  type mem

  val empty_memory    : mem
  val mem_updates     : armML.word30 list ref
  val mem_items       : mem -> (armML.word30 * armML.word32) list
  val mem_read        : mem * armML.word30 -> armML.word32
  val MEM_READ        : mem -> armML.word32 -> armML.word32 option
  val MEM_WRITE       : mem -> armML.word32 -> armML.data -> mem option
  val MEM_WRITE_BLOCK : mem -> armML.word30 -> armML.word32 list -> mem
end =
struct
  open numML wordsML armML

  fun toWord s i = n2w_itself(i, fcpML.ITSELF(fromInt s));
  val toWord32 = toWord 32: num -> word32

  type mem = (word30, word32) Redblackmap.dict

  val mem_updates = ref ([]: word30 list)

  fun mem_items (m:mem) = Redblackmap.listItems m

  fun word_compare(v, w) =
    let val m = w2n v and n = w2n w in
      if m = n then
        EQUAL
      else
        if numML.< m n then LESS else GREATER
    end

  val empty_memory = (Redblackmap.mkDict word_compare):mem

  val fromNum32 = toWord32 o numML.fromHexString

  fun mem_read (m,a) = Redblackmap.find(m:mem, a)
                         handle NotFound => fromNum32 "E6000010"

  fun MEM_READ m a = SOME (mem_read (m,armML.ADDR30 a))

  fun mem_write m a w =
        (if isSome (List.find (fn b => word_compare(a, b) = EQUAL)
                              (!mem_updates)) then
           Redblackmap.insert(m:mem, a, w)
         else
           (mem_updates := a :: !mem_updates; m))

  fun MEM_WRITE_BYTE mem addr word =
        let val addr30 = ADDR30 addr
        in
           mem_write mem addr30
             (SET_BYTE
                (word_extract_itself
                   (fcpML.ITSELF (numML.fromDecString"2")) ONE ZERO
                   addr) word (mem_read (mem,addr30)))
        end
   
  fun MEM_WRITE_HALF mem addr word =
        let val addr30 = ADDR30 addr
        in
           mem_write mem addr30
             (SET_HALF (word_index addr ONE) word
                (mem_read (mem,addr30)))
        end

  fun MEM_WRITE_WORD mem addr word = mem_write mem (ADDR30 addr) word

  fun MEM_WRITE mem addr data =
        SOME (case data
         of Byte(b) => MEM_WRITE_BYTE mem addr b
          | Half(hw) => MEM_WRITE_HALF mem addr hw
          | Word(w) => MEM_WRITE_WORD mem addr w)

  fun MEM_WRITE_BLOCK m a [] = m
    | MEM_WRITE_BLOCK m a (w::l) =
        MEM_WRITE_BLOCK (Redblackmap.insert(m:mem, a, w))
          (word_add a (n2w_itself (ONE,fcpML.ITSELF(numML.fromInt 30)))) l
end;

(* ------------------------------------------------------------------------- *)

exception Parse;

fun toWord s i = wordsML.n2w_itself(i, fcpML.ITSELF(numML.fromInt s));

fun toWord4 i = toWord 4 (numML.fromInt i): wordsML.word4
val toWord16 = toWord 16: numML.num -> wordsML.word16;
val toWord30 = toWord 30: numML.num -> wordsML.word30;
val toWord32 = toWord 32: numML.num -> wordsML.word32

val num2Arbnum = Arbnum.fromHexString o numML.toHexString;

fun string2num s =
  case String.explode s of
    (#"0"::(#"x"::ls)) => numML.fromHexString (String.extract(s,2,NONE))
  | (#"0"::(#"b"::ls)) => numML.fromBinString (String.extract(s,2,NONE))
  | (#"0"::ls) => numML.fromOctString (String.extract(s,1,NONE))
  | ls => numML.fromString s;

fun toHexString_w2n n = "0x" ^ numML.toHexString (wordsML.w2n n);

fun for base top f =
 let fun For i = if i>top then [] else f i::For(i+1) in For base end;

fun for_se base top f =
 let fun For i = if i>top then () else (f i; For(i+1)) in For base end;

(* ------------------------------------------------------------------------- *)

fun string2mode s =
  case s of
    "usr" => armML.usr
  | "fiq" => armML.fiq
  | "irq" => armML.irq
  | "svc" => armML.svc
  | "abt" => armML.abt
  | "und" => armML.und
  | _ => raise Parse;

fun mode2string m =
  case m of
    armML.usr => "usr"
  | armML.fiq => "fiq"
  | armML.irq => "irq"
  | armML.svc => "svc"
  | armML.abt => "abt"
  | armML.und => "und"
  | _ => "";

fun register2string r =
  case r of
    armML.r0 => "r0" | armML.r1 => "r1" | armML.r2 => "r2"
  | armML.r3 => "r3" | armML.r4 => "r4" | armML.r5 => "r5"
  | armML.r6 => "r6" | armML.r7 => "r7" | armML.r8 => "r8"
  | armML.r9 => "r9" | armML.r10 => "r10" | armML.r11 => "r11"
  | armML.r12 => "r12" | armML.r13 => "sp" | armML.r14 => "lr"
  | armML.r15 => "pc"
  | armML.r8_fiq => "r8_fiq" | armML.r9_fiq => "r9_fiq"
  | armML.r10_fiq => "r10_fiq" | armML.r11_fiq => "r11_fiq"
  | armML.r12_fiq => "r12_fiq" | armML.r13_fiq => "r13_fiq"
  | armML.r14_fiq => "r14_fiq"
  | armML.r13_irq => "r13_irq" | armML.r14_irq => "r14_fiq"
  | armML.r13_svc => "r13_svc" | armML.r14_svc => "r14_svc"
  | armML.r13_abt => "r13_abt" | armML.r14_abt => "r14_abt"
  | armML.r13_und => "r13_und" | armML.r14_und => "r14_und";

local
  fun namedReg s = toWord4
   (case s of
      "sl" => 10
    | "fp" => 11
    | "ip" => 12
    | "sp" => 13
    | "lr" => 14
    | "pc" => 15
    | _ => raise Parse);

  fun toReg(x, y) =
        case Int.fromString (String.implode x) of
            SOME i => if i < 16 then (toWord4 i, y) else raise Parse
          | NONE => raise Parse

  fun toNamedReg(x, y) = (namedReg(String.implode (map Char.toLower x)),y)

  fun getReg l =
    case l of
      [r, n1] => (if Char.toUpper r = #"R" then toReg([n1],[])
                  else toNamedReg([r,n1],[]))
    | r :: (n1 :: (n2 :: ls)) =>
        if Char.toUpper r = #"R" then
          if n1 = #"1" then
            if Char.isDigit n2 then toReg([n1,n2],ls)
            else (toWord4 1, n2::ls)
          else
            toReg([n1],n2::ls)
        else toNamedReg([r,n1], n2::ls)
    | _ => raise Parse

  fun getRegister l =
    let val (i,rest) = getReg l in
       case rest of
         [] => (i,armML.usr)
       | (#"_" :: ls) =>
           if length ls = 3 then
             (i,string2mode (String.implode (map Char.toLower ls)))
           else
             raise Parse
       | _ => raise Parse
    end
in
  val register = getRegister o String.explode;
end;

(* ------------------------------------------------------------------------- *)

datatype env =
   ENV of {N:bool, Z:bool, C:bool, V:bool, T:bool, M:armML.mode,
           Wreg:bool, Wmem:bool, Wmode:bool, Wthumb:bool, Wflags:bool,
           Wireg:bool, cycles:int, E:bool, mem:string, reg:armML.registers,
           psr:armML.psrs};

fun update_switch fld (ENV e) =
  let val {N,Z,C,V,T,M,E,mem,reg,cycles,
           Wreg,Wmem,Wmode,Wthumb,Wflags,Wireg,psr} = e
  in
    ENV
    {N = if fld = "N" then true else N,
     Z = if fld = "Z" then true else Z,
     C = if fld = "Z" then true else C,
     V = if fld = "V" then true else V,
     T = if fld = "T" then true else T,
     E = if fld = "E" then true else E,
     Wreg   = if fld = "Wreg"   orelse fld = "Wall" then true else Wreg,
     Wmem   = if fld = "Wmem"   orelse fld = "Wall" then true else Wmem,
     Wmode  = if fld = "Wmode"  orelse fld = "Wall" then true else Wmode,
     Wthumb = if fld = "Wthumb" orelse fld = "Wall" then true else Wthumb,
     Wflags = if fld = "Wflags" orelse fld = "Wall" then true else Wflags,
     Wireg  = if fld = "Wireg"  orelse fld = "Wall" then true else Wireg,
     M = M, mem = mem, reg = reg, cycles = cycles, psr = psr}
  end;

fun update_cycles i (ENV e) =
  let val {N,Z,C,V,T,M,E,mem,reg,cycles,
           Wreg,Wmem,Wmode,Wthumb,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, T = T, M = M, E = E, mem = mem, reg = reg,
         cycles = i, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode, Wthumb = Wthumb,
         Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_mode m (ENV e) =
  let val {N,Z,C,V,T,M,E,mem,reg,cycles,
           Wreg,Wmem,Wmode,Wthumb,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, T = T, M = m, E = E, mem = mem, reg = reg,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wthumb = Wthumb, Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_mem m (ENV e) =
  let val {N,Z,C,V,T,M,E,mem,reg,cycles,
           Wreg,Wmem,Wmode,Wthumb,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, T = T, M = M, E = E, mem = m, reg = reg,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wthumb = Wthumb, Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_reg r (ENV e) =
  let val {N,Z,C,V,T,M,E,mem,reg,cycles,
           Wreg,Wmem,Wmode,Wthumb,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, T = T, M = M, E = E, mem = mem, reg = r,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wthumb = Wthumb, Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_psr (p, n) (ENV e) =
  let val {N,Z,C,V,T,M,E,mem,reg,cycles,
           Wreg,Wmem,Wmode,Wthumb,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, T = T, M = M, E = E, mem = mem, reg = reg,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wthumb = Wthumb, Wflags = Wflags, Wireg = Wireg,
         psr = combinML.UPDATE p n psr}
  end;

fun proj_ENV (ENV e) = e;
val toLowerString = String.map Char.toLower;
val toSpaces = String.map (fn _ => #" ");

val usage_message = let val x = "Usage: " ^ CommandLine.name() in
  "An ARM emulator (generated from a HOL model of the ARM7's ISA).\n" ^ x ^
  " [-cycles n] [-rN_m n] [-SPSR_m n] [-N] [-Z] [-C] [-V] [-T] [-M m] [-E]\n" ^
  toSpaces x ^
  " [-Wreg] [-Wmem] [-Wmode] [-Wflags] [-Wthumb] [-Wireg] [-Wall] file\n" ^
  "Options:\n\
  \-cycles n - upper limit on the run length (will be " ^
               Int.toString (valOf Int.maxInt) ^ " by default)\n\
  \-rN_m n   - set a Register e.g. -r8_fiq 0x20 -pc 0b101100\n\
  \-SPSR_m n - set a Saved Program Status Register e.g. -SPSR_svc 0x20\n\
  \-N        - set the Negative flag (will be clear by default)\n\
  \-Z        - set the Zero flag\n\
  \-C        - set the Carry flag\n\
  \-V        - set the oVerflow flag\n\
  \-T        - set the Thumb flag\n\
  \-M {usr,fiq,irq,svc,abt,und}\n\
  \          - set the mode (will be \"usr\" by default)\n\
  \-E        - load the default \"rudimentary\" exception handler\n\
  \-Wreg     - watch register updates\n\
  \-Wmem     - watch memory updates\n\
  \-Wmode    - watch mode changes\n\
  \-Wthumb   - watch thumb mode changes\n\
  \-Wflags   - watch changes to the status flags\n\
  \-Wireg    - watch the instruction register\n\
  \-Wall     - watch everything\n"
end;

fun setOptions l env =
  let fun set_switch x rest = setOptions rest (update_switch x env)
      fun set_psr x s rest =
            setOptions rest (update_psr(x,toWord32 (string2num s)) env)
              handle _ => setOptions (s::rest) env
  in
    case l of
      [] => env
    | ["--help"] => (print usage_message; OS.Process.exit OS.Process.success)
    | ("-N"::ls) => set_switch "N" ls
    | ("-Z"::ls) => set_switch "Z" ls
    | ("-C"::ls) => set_switch "C" ls
    | ("-V"::ls) => set_switch "V" ls
    | ("-T"::ls) => set_switch "T" ls
    | ("-E"::ls) => set_switch "E" ls
    | ("-Wreg"::ls)   => set_switch "Wreg" ls
    | ("-Wmem"::ls)   => set_switch "Wmem" ls
    | ("-Wmode"::ls)  => set_switch "Wmode" ls
    | ("-Wthumb"::ls) => set_switch "Wthumb" ls
    | ("-Wflags"::ls) => set_switch "Wflags" ls
    | ("-Wireg"::ls)  => set_switch "Wireg" ls
    | ("-Wall"::ls)   => set_switch "Wall" ls
    | ("-M"::(s::ls)) =>
        (setOptions ls (update_mode (string2mode (toLowerString s)) env)
           handle Parse => setOptions (s::ls) env)
    | ("-cycles"::(s::ls)) =>
       (case Int.fromString s of
          SOME i => setOptions ls (update_cycles i env)
        | NONE => setOptions (s::ls) env)
    | ("-SPSR_fiq"::(s::ls)) => set_psr armML.SPSR_fiq s ls
    | ("-SPSR_irq"::(s::ls)) => set_psr armML.SPSR_irq s ls
    | ("-SPSR_svc"::(s::ls)) => set_psr armML.SPSR_svc s ls
    | ("-SPSR_abt"::(s::ls)) => set_psr armML.SPSR_abt s ls
    | ("-SPSR_und"::(s::ls)) => set_psr armML.SPSR_und s ls
    | (r::(s::ls)) =>
       (let val _ = String.sub(r,0) = #"-" orelse raise Parse
            val reg = #reg (proj_ENV env)
            val (n,m) = register (String.extract(r,1,NONE))
            val d = toWord32 (string2num s)
        in
          setOptions ls (update_reg (armML.REG_WRITE reg m n d) env)
        end handle _ => setOptions (s::ls) env)
    | [s] => update_mem s env
  end;

(* ------------------------------------------------------------------------- *)

local
  open assemblerML;
  fun add1 a = Data.add32 a Arbnum.one;
  fun add2 a = Data.add32 a Arbnum.two;
  val mul2 = Data.mul2;
  val div2 = Data.div2;
  val start = Arbnum.zero;
  datatype arm_thumb = Thumb of Arbnum.num | ARM of Arbnum.num | OTHER;

  val fromArbnum16 = toWord16 o numML.fromHexString o Arbnum.toHexString;
  val fromArbnum30 = toWord30 o numML.fromHexString o Arbnum.toHexString;
  val fromArbnum32 = toWord32 o numML.fromHexString o Arbnum.toHexString;

  fun advance_pc i n =
        case i of
          Data.Mark m                    => div2 m
        | Data.Code (Data.Instruction i) => add2 n
        | Data.Code (Data.Data n)        => add2 n
        | Data.Code (Data.Thumb i)       => add1 n
        | Data.Code (Data.ThumbData n)   => add1 n
        | Data.BranchS b                 => add2 n
        | Data.BranchN b                 => add2 n
        | Data.ThumbBranchS (c,l,s)      => if l then add2 n else add1 n
        | Data.ThumbBranchN (c,l,x)      => if l then add2 n else add1 n
        | Data.Label s                   => n;

  fun mk_links [] dict n = dict
    | mk_links (h::r) dict n =
       let val dict' =
             case h of
               Data.Label s =>
                 Redblackmap.insert(dict, s, "0x" ^ Arbnum.toHexString (mul2 n))
             | _ => dict
       in
         mk_links r dict' (advance_pc h n)
       end;

  fun mk_link_table code =
    let val dict = Redblackmap.mkDict String.compare in
      mk_links code dict start
    end;

  fun x_label (Data.BranchS (c, l, s)) = (Data.BranchS (c, l, ""), s)
    | x_label (Data.ThumbBranchS (c, l, s)) = (Data.ThumbBranchS (c, l, ""), s)
    | x_label x = (x,"");

  fun br_to_word i dict n =
        let val (xi, label) = x_label i
            val s = assembler_to_string NONE xi NONE
            val address = Redblackmap.find(dict, label)
        in
          encode_arm ("0x" ^ Arbnum.toHexString n ^ ": " ^ s ^ address)
        end;

  fun lcons h [] = [[h]]
    | lcons h (x::l) = (h::x)::l;

  fun arm_or_thumb i n =
        case i of
          Data.Instruction i => ARM n
        | Data.Thumb i       => Thumb n
        | Data.Data x        => ARM n
        | Data.ThumbData x   => Thumb x;

  fun arm_or_thumb2 n =
        if Arbnum.<(n, Arbnum.fromHexString("10000")) then
          Thumb n
        else
          ARM n;

  fun assembler_to_word i dict n =
       case i of
         Data.Code c         => arm_or_thumb c
                                  (arm_to_num (validate_instruction c))
       | Data.BranchS b      => ARM (br_to_word i dict n)
       | Data.ThumbBranchS b => arm_or_thumb2 (br_to_word i dict n)
       | Data.BranchN b      => ARM (arm_to_num (branch_to_arm b n))
       | Data.ThumbBranchN b => arm_or_thumb2 (arm_to_num (branch_to_thumb b n))
       | _ => OTHER;

  fun do_link m l n [] dict = ListPair.zip(m, l)
    | do_link m l n (h::r) dict =
        let val (nm, nl, nn) =
          case h of
            Data.Mark mk =>
               let val k = div2 mk in
                 if k = n then
                   (m, l, n)
                 else if null (hd l) then
                   (k::(tl m), l, k)
                 else
                   (k::m, []::l, k)
               end
          | Data.Label s => (m, l, n)
          | _ => (m, lcons (assembler_to_word h dict (mul2 n)) l,
                  advance_pc h n)
        in
          do_link nm nl nn r dict
        end;

  fun do_links code =
        let val l = do_link [start] [[]] start code (mk_link_table code) in
          rev (map (fn (a,b) => (a,rev b)) l)
        end;

  fun check_aligned n = Data.even n orelse raise Parse;

  fun join_half_words a b =
        wordsML.word_concat_itself
          (fcpML.ITSELF(numML.fromInt 32):
            unit wordsML.bit0 wordsML.bit0
            wordsML.bit0 wordsML.bit0 wordsML.bit0 wordsML.itself)
          (fromArbnum16 b) (fromArbnum16 a);

  val UND_ = Arbnum.fromHexString "DE00";

  fun do_form_words [] r n = rev r
    | do_form_words [a] r n =
       (case a of
          ARM x   => (check_aligned n; rev (fromArbnum32 x::r))
        | Thumb x => if Data.even n then
                       rev ((join_half_words x UND_)::r)
                     else
                       rev ((join_half_words UND_ x)::r)
        | _ => raise Parse)
    | do_form_words (a::b::t) r n =
       (case a of
          ARM x =>
            (check_aligned n; do_form_words (b::t) (fromArbnum32 x::r) (add2 n))
        | Thumb x =>
            if Data.even n then
              case b of
                Thumb y => do_form_words t ((join_half_words x y)::r) (add2 n)
              | _ => raise Parse
            else
              do_form_words (b::t) ((join_half_words UND_ x)::r) (add1 n)
        | _ => raise Parse);

  fun form_words(n, c) = (fromArbnum30 (div2 n), do_form_words c [] n);

(*
fun dt (Thumb n) = decode_thumb NONE n
  | dt (ARM n) = decode_arm NONE n
  | dt _ = "";

map (fn (n,ll) => map dt ll) l
*)

  fun assemble_assembler m a = let
    val l = map form_words (do_links a)
  in
    foldr (fn ((a,c),t) => memoryML.MEM_WRITE_BLOCK t a c) m l
  end
in
  fun assemble m file = assemble_assembler m (assemblerML.parse_arm file);
  fun list_assemble m l =
    let val c = String.concat (map (fn s => s ^ "\n") l)
    in
      assemble_assembler m (assemblerML.string_to_code c)
    end;
  fun assemble1 m t = list_assemble m [t];
end;

(* ------------------------------------------------------------------------- *)

fun dest_state state =
let
  val (s,(cp,(mem,()))) = state
  val regs = armML.arm_state_regs s
  val exc = armML.arm_state_exception s
  val reg = armML.regs_reg regs
  val psr = armML.regs_psr regs
in
  (reg,psr,exc,cp,mem)
end;

local
  fun regName(i, m) = "r" ^ (Int.toString i) ^
    (if m = armML.usr orelse i < 8 orelse i = 15 orelse
        i <= 12 andalso not (m = armML.fiq) then "" else "_" ^ mode2string m);

  fun regString reg (i, m) = regName(i, m) ^ " = " ^
    toHexString_w2n (armML.REG_READ false reg m (toWord4 i));

  fun print_reg ostrm reg i =
    if i < 8 then
      TextIO.output(ostrm,regString reg (i, armML.usr) ^ "\n")
    else if i <= 12 then
     (TextIO.output(ostrm,regString reg (i, armML.usr) ^ "; ");
      TextIO.output(ostrm,regString reg (i, armML.fiq) ^ "\n"))
    else if i < 15 then
     (app (fn m => TextIO.output(ostrm,regString reg (i, m) ^ "; "))
        [armML.usr, armML.fiq, armML.irq, armML.svc, armML.abt];
      TextIO.output(ostrm,regString reg (i, armML.und) ^ "\n"))
    else
      TextIO.output(ostrm,
        "r15 = " ^ toHexString_w2n (armML.FETCH_PC reg) ^ "\n");

  fun print_psr ostrm s p =
    let
      val ((n,(z,(c,v))),(i,(f,(t,m)))) = armML.DECODE_PSR p
      val m = armML.DECODE_MODE m
    in
      TextIO.output(ostrm,
        s ^ " = {N = " ^ Bool.toString n ^ ", " ^
                "Z = " ^ Bool.toString z ^ ", " ^
                "C = " ^ Bool.toString c ^ ", " ^
                "V = " ^ Bool.toString v ^ ",\n" ^
                toSpaces (s ^ " = {") ^
                "I = " ^ Bool.toString i ^ ", " ^
                "F = " ^ Bool.toString f ^ ", " ^
                "T = " ^ Bool.toString t ^ ", " ^
                "mode = " ^ mode2string m ^ "}\n")
    end;

  fun print_line ostrm (l,c) =
    let val n = numML.* (wordsML.w2n l) (numML.fromInt 4)
        val m = wordsML.w2n c
    in
      TextIO.output(ostrm,
        "0x" ^ numML.toHexString n ^ ": 0x" ^ numML.toHexString m ^ "; ");
      TextIO.output(ostrm,
        assemblerML.decode_arm (SOME (num2Arbnum n)) (num2Arbnum m) ^ "\n")
    end
in
  fun print_state fname state count =
    let val ostrm = TextIO.openOut fname
        val (reg,psr,_,_,mem) = dest_state state
        val items = memoryML.mem_items mem
    in
      TextIO.output(ostrm,"Instuctions Run:" ^ Int.toString count ^ "\n");
      TextIO.output(ostrm,"\nRegisters\n---------\n");
      for_se 0 15 (print_reg ostrm reg);

      TextIO.output(ostrm,"\nProgram Status\n--------------\n");
      print_psr ostrm "CPSR" (armML.CPSR_READ psr);
      print_psr ostrm "SPSR_fiq" (armML.SPSR_READ psr armML.fiq);
      print_psr ostrm "SPSR_irq" (armML.SPSR_READ psr armML.irq);
      print_psr ostrm "SPSR_svc" (armML.SPSR_READ psr armML.svc);
      print_psr ostrm "SPSR_abt" (armML.SPSR_READ psr armML.abt);
      print_psr ostrm "SPSR_und" (armML.SPSR_READ psr armML.und);

      if items = [] then () else
        (TextIO.output(ostrm,"\nMemory\n------\n");
         map (print_line ostrm) items;());

      TextIO.closeOut ostrm
  end
end;

(* ------------------------------------------------------------------------- *)

val int2register = armML.num2register o numML.fromInt;

fun gen_tabulate f g n =
  let fun do_tab i l =
    if i = 0 then l
    else let val x = i - 1 in
      do_tab x (if f x then (g x)::l else l)
    end
  in
    do_tab n []
  end;

fun reg_updates reg1 reg2 =
  gen_tabulate
    (fn i => let val r = int2register i in not (reg1 r = reg2 r) end)
    int2register 31;

fun printer (Wreg, Wmem, Wmode, Wflags, Wthumb, Wireg) cycle s ns =
  if Wireg orelse Wreg orelse Wmem orelse Wflags orelse Wmode orelse Wthumb then
    let
      val (reg1,psr1,exc1,_,mem1) = dest_state s
      val (reg2,psr2,exc2,_,mem2) = dest_state ns
      val cpsr1 = armML.CPSR_READ psr1
      val cpsr2 = armML.CPSR_READ psr2
      val (nzcv1, (i1, (f1, (t1, m1)))) = armML.DECODE_PSR cpsr1
      val (nzcv2, (i2, (f2, (t2, m2)))) = armML.DECODE_PSR cpsr2

      fun print_ireg ireg = print ("> " ^
            (if t1 then assemblerML.decode_thumb else assemblerML.decode_arm)
               NONE (num2Arbnum (wordsML.w2n ireg)) ^ "\n")

      fun print_reg i = print
            ("; " ^ register2string i ^ " := " ^ toHexString_w2n (reg2(i)))

      fun print_mem a = print
            ("; mem[" ^ toHexString_w2n a ^ "] := " ^
             toHexString_w2n (memoryML.mem_read(mem2, a)))

      fun print_bool b = print (if b then "1" else "0")

      fun print_nzcv (n,(z,(c, v))) = (print "; NZCV := ";
            print_bool n; print_bool z; print_bool c; print_bool v)

      fun print_thumb t = print (if t then "; Thumb mode" else "; ARM mode");

      fun print_mode m = print
            ("; mode := " ^ mode2string (armML.DECODE_MODE m))
    in
      ((if Wireg then
          if exc1 = armML.software then
            let
              val p = armML.OUT_NO_PIPE memoryML.MEM_READ
                        ((), (pairML.FST s, mem1))
            in
              print_ireg (armML.pipe_output_ireg p)
            end
          else
            print "> undefined exception\n"
        else
          ());
       print ("- t = " ^ Int.toString cycle);
       (if Wreg then app print_reg (reg_updates reg1 reg2) else ());
       (if Wmem then app print_mem (rev (!memoryML.mem_updates)) else ());
       (if not Wflags orelse nzcv1 = nzcv2 then () else print_nzcv nzcv2);
       (if not Wthumb orelse t1 = t2 then () else print_thumb t2);
       (if not Wmode orelse m1 = m2 then () else print_mode m2);
       print "\n")
    end
  else
    ();

(* ------------------------------------------------------------------------- *)
(* Taken from Joe Hurd's $HOLDIR/tools/mlton/src/mlibPortable.sml *)

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
        val {usr, sys, gc} = Timer.checkCPUTimer c
        val real = Timer.checkRealTimer r
      in
        print
        ("User: " ^ p usr ^ "  System: " ^ p sys ^
         "  GC: " ^ p gc ^ "  Real: " ^ p real ^ "\n")
      end
    val y = f x handle e => (pt (); raise e)
    val () = pt ()
  in
    y
  end;

(* ------------------------------------------------------------------------- *)

val env =
  let val initial_psr =
            armML.SET_NZCV (false,(false,(false,false)))
           (armML.SET_IFTM false false false armML.usr
           (toWord32 (numML.fromInt 0)))
  in
    ENV {N = false, Z = false, C = false, V = false, T = false, M = armML.usr,
      E = false, mem = "", reg = armML.empty_registers,
      psr = fn x => initial_psr, cycles = valOf Int.maxInt,
      Wreg = false, Wmem = false, Wmode = false,
      Wflags = false, Wthumb = false, Wireg = false}
  end;

val e = proj_ENV (setOptions (CommandLine.arguments()) env);
val watches = (#Wreg e, #Wmem e, #Wmode e, #Wflags e, #Wthumb e, #Wireg e);

val count = ref 0;

fun STATE_1STAGE cp write read (s,i) t =
  if t = 0 then s
  else
    let
      val _ = count := !count + 1
      val _ = memoryML.mem_updates := []
      val p = t - 1
      val n = armML.NEXT_1STAGE cp write read (s, i (numML.fromInt p))
      val _ = printer watches (!count) s n
    in
      if armML.arm_state_exception (pairML.FST s) = armML.undefined then
        n
      else
        STATE_1STAGE cp write read (n,i) p
    end;

(* ------------------------------------------------------------------------- *)

fun printn s = print (s ^ "\n");

val init_mem = if #E e then
  list_assemble memoryML.empty_memory
    ["0x0: movs pc, #32",
     "label: b label",
     "movs pc, r14",
     "subs pc, r14, #4",
     "subs pc, r14, #8",
     "movs pc, r14",
     "subs pc, r14, #4",
     "subs pc, r14, #4"]
  else memoryML.empty_memory;

val init_mem =
  let val m = #mem e in
    if not (m = "") then
      assemble init_mem m
        handle Data.BadInstruction s =>
                  (printn s; raise Fail ("Could not load file: " ^ m))
             | Data.Parse s =>
                  (printn s; raise Fail ("Could not load file: " ^ m))
             | _ => raise Fail ("Could not load file: " ^ m)
    else
      init_mem
  end;

val cpsr = armML.SET_NZCV (#N e,(#Z e,(#C e,#V e)))
      (armML.SET_IFTM false false (#T e) (#M e) (toWord32 (numML.fromInt 0)));

val psr = armML.CPSR_WRITE (#psr e) cpsr;

val init_state =
let
  val state = armML.arm_state (armML.regs (#reg e, psr), armML.software)
in
  (state,((),(init_mem, ())))
end;

val NO_CP =
  armML.coproc(fn u => fn i => true,
  fn s => raise Fail "",
  fn s => raise Fail "",
  fn s => raise Fail "",
  fn s => raise Fail "",
  fn s => raise Fail "",
  fn s => raise Fail "") : unit armML.coproc;

val STATE = STATE_1STAGE NO_CP memoryML.MEM_WRITE memoryML.MEM_READ;

val final_state = time (STATE (init_state,armML.NO_IRPTS)) (#cycles e);

val _ = print_state "run.in" init_state 0;
val _ = print_state "run.out" final_state (!count);

(* ------------------------------------------------------------------------- *)

