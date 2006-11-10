(* interactive use:
val HOLDIR = "/local/scratch/acjf3/hol98/";
val _ = loadPath := !loadPath @ ".." :: map (fn x => HOLDIR ^ x)
     ["tools/mlyacc/mlyacclib", "tools/mlton/pre",
      "src/portableML", "src/theoryML"];
val _ = app load ["assemblerML", "armML", "sizesML"];
val _ = app load ["OS", "Bool", "Time", "Timer", "CommandLine", "ListPair"];
*)

(* ------------------------------------------------------------------------- *)

exception Parse;

val _ = sizesML.sizes();

fun toWord s i = wordsML.n2w_itself(i, fcpML.Tyop (s, []));

fun toWord4 i = toWord "i4" (numML.fromInt i): wordsML.word4
val toWord30 = toWord "i30": numML.num -> wordsML.word30;
val toWord32 = toWord "i32": numML.num -> wordsML.word32

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
   ENV of {N:bool, Z:bool, C:bool, V:bool, M:armML.mode,
           Wreg:bool, Wmem:bool, Wmode:bool, Wflags:bool,
           Wireg:bool, cycles:int, E:bool, mem:string, reg:armML.registers,
           psr:armML.psrs};

fun update_switch fld (ENV e) =
  let val {N,Z,C,V,E,M,mem,reg,cycles,Wreg,Wmem,Wmode,Wflags,Wireg,psr} = e
  in
    ENV
    {N = if fld = "N" then true else N,
     Z = if fld = "Z" then true else Z,
     C = if fld = "Z" then true else C,
     V = if fld = "V" then true else V,
     E = if fld = "E" then true else E,
     Wreg   = if fld = "Wreg"   orelse fld = "Wall" then true else Wreg,
     Wmem   = if fld = "Wmem"   orelse fld = "Wall" then true else Wmem,
     Wmode  = if fld = "Wmode"  orelse fld = "Wall" then true else Wmode,
     Wflags = if fld = "Wflags" orelse fld = "Wall" then true else Wflags,
     Wireg  = if fld = "Wireg"  orelse fld = "Wall" then true else Wireg,
     M = M, mem = mem, reg = reg, cycles = cycles, psr = psr}
  end;

fun update_cycles i (ENV e) =
  let val {N,Z,C,V,E,M,mem,reg,cycles,Wreg,Wmem,Wmode,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, E = E, M = M, mem = mem, reg = reg,
         cycles = i, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode, Wflags = Wflags,
         Wireg = Wireg, psr = psr}
  end;

fun update_mode m (ENV e) =
  let val {N,Z,C,V,E,M,mem,reg,cycles,Wreg,Wmem,Wmode,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, E = E, M = m, mem = mem, reg = reg,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_mem m (ENV e) =
  let val {N,Z,C,V,E,M,mem,reg,cycles,Wreg,Wmem,Wmode,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, E = E, M = M, mem = m, reg = reg,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_reg r (ENV e) =
  let val {N,Z,C,V,E,M,mem,reg,cycles,Wreg,Wmem,Wmode,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, E = E, M = M, mem = mem, reg = r,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wflags = Wflags, Wireg = Wireg, psr = psr}
  end;

fun update_psr (p, n) (ENV e) =
  let val {N,Z,C,V,E,M,mem,reg,cycles,Wreg,Wmem,Wmode,Wflags,Wireg,psr} = e in
    ENV {N = N, Z = Z, C = C, V = V, E = E, M = M, mem = mem, reg = reg,
         cycles = cycles, Wreg = Wreg, Wmem = Wmem, Wmode = Wmode,
         Wflags = Wflags, Wireg = Wireg, psr = bsubstML.:- p n psr}
  end;

fun proj_ENV (ENV e) = e;
val toLowerString = String.map Char.toLower;
val toSpaces = String.map (fn _ => #" ");

val usage_message = let val x = "Usage: " ^ CommandLine.name() in
  "An ARM emulator (generated from a HOL model of the ARM7's ISA).\n" ^
  x ^ " [-cycles n] [-rN_m n] [-SPSR_m n] [-N] [-Z] [-C] [-V] [-M m] [-E]\n" ^
  toSpaces x ^ " [-Wreg] [-Wmem] [-Wmode] [-Wflags] [-Wireg] [-Wall] file\n" ^
  "Options:\n\
  \-cycles n - upper limit on the run length (will be " ^
               Int.toString (valOf Int.maxInt) ^ " by default)\n\
  \-rN_m n   - set a Register e.g. -r8_fiq 0x20 -pc 0b101100\n\
  \-SPSR_m n - set a Saved Program Status Register e.g. -SPSR_svc 0x20\n\
  \-N        - set the Negative flag (will be clear by default)\n\
  \-Z        - set the Zero flag\n\
  \-C        - set the Carry flag\n\
  \-V        - set the oVerflow flag\n\
  \-M {usr,fiq,irq,svc,abt,und}\n\
  \          - set the mode (will be \"usr\" by default)\n\
  \-E        - load the default \"rudimentary\" exception handler\n\
  \-Wreg     - watch register updates\n\
  \-Wmem     - watch memory updates\n\
  \-Wmode    - watch mode changes\n\
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
    | ("-E"::ls) => set_switch "E" ls
    | ("-Wreg"::ls)   => set_switch "Wreg" ls
    | ("-Wmem"::ls)   => set_switch "Wmem" ls
    | ("-Wmode"::ls)  => set_switch "Wmode" ls
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
  fun add1 a = Data.add32 a Arbnum.one;
  fun div4 a = Arbnum.div(a,Arbnum.fromInt 4);
  fun mul4 a = Arbnum.*(a,Arbnum.fromInt 4);
  val start = Arbnum.zero;
  val fromArbnum30 = toWord30 o numML.fromHexString o Arbnum.toHexString;
  val fromArbnum32 = toWord32 o numML.fromHexString o Arbnum.toHexString;

  fun mk_links [] dict n = dict
    | mk_links (h::r) dict n =
        case h of
          Data.Code c => mk_links r dict (add1 n)
        | Data.BranchS b => mk_links r dict (add1 n)
        | Data.BranchN b => mk_links r dict (add1 n)
        | Data.Label s =>
            mk_links r
             (Redblackmap.insert(dict, s, "0x" ^ Arbnum.toHexString (mul4 n))) n
        | Data.Mark m => mk_links r dict (div4 m);

  fun mk_link_table code =
    let val dict = Redblackmap.mkDict String.compare in
      mk_links code dict start
    end;

  fun br_to_word32 (cond,link,label) dict n =
    let val s = assemblerML.assembler_to_string
                   NONE (Data.BranchS(cond,link,"")) NONE
        val address = Redblackmap.find(dict, label)
    in
      (fromArbnum32 o assemblerML.encode_arm)
        ("0x" ^ Arbnum.toHexString (mul4 n) ^ ": " ^ s ^ address)
    end;

  fun is_label (Data.Label s) = true | is_label _ = false;

  fun lcons h [] = [[h]]
    | lcons h (x::l) = (h::x)::l;

  fun do_link m l [] dict n = ListPair.zip(m, l)
    | do_link m l (h::r) dict n =
        case h of
           Data.Code c =>
             do_link m (lcons (fromArbnum32 (assemblerML.arm_to_num
               (assemblerML.validate_instruction c))) l) r dict (add1 n)
         | Data.BranchS b =>
             do_link m (lcons (br_to_word32 b dict n) l) r dict (add1 n)
         | Data.BranchN b =>
             let val t = fromArbnum32 (assemblerML.arm_to_num
                           (assemblerML.branch_to_arm b (mul4 n)))
             in
               do_link m (lcons t l) r dict (add1 n)
             end
         | Data.Label s => do_link m l r dict n
         | Data.Mark mk => let val k = div4 mk in
               if k = n then
                 do_link m l r dict n
               else if null (hd l) then
                 do_link (k::(tl m)) l r dict k
               else
                 do_link (k::m) ([]::l) r dict k
             end;

  fun do_links code =
        let val l = do_link [start] [[]] code (mk_link_table code) start in
          rev (map (fn (a,b) => (a,rev b)) l)
        end;

  fun assemble_assembler m a = let
    val l = do_links a
    val b = map (fn (m,c) => (fromArbnum30 m, c)) l
  in
    foldr (fn ((a,c),t) => bsubstML.MEM_WRITE_BLOCK t a c) m b
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

local
  fun regName(i, m) = "r" ^ (Int.toString i) ^
    (if m = armML.usr orelse i < 8 orelse i = 15 orelse
        i <= 12 andalso not (m = armML.fiq) then "" else "_" ^ mode2string m);

  fun regString reg (i, m) = regName(i, m) ^ " = " ^
    toHexString_w2n (armML.REG_READ reg m (toWord4 i));

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
      val ((n,(z,(c,v))),(i,(f,m))) = armML.DECODE_PSR p
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
        val reg = armML.arm_mem_state_registers state
        val psr = armML.arm_mem_state_psrs state
        val mem = armML.arm_mem_state_memory state
        val items = bsubstML.MEM_ITEMS mem
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

fun printer (Wreg, Wmem, Wmode, Wflags, Wireg) cycle s ns =
  if Wireg orelse Wreg orelse Wmem orelse Wflags orelse Wmode then
    let val reg1 = armML.arm_mem_state_registers s
        val reg2 = armML.arm_mem_state_registers ns
        val mem1 = armML.arm_mem_state_memory s
        val mem2 = armML.arm_mem_state_memory ns
        val cpsr1 = armML.CPSR_READ (armML.arm_mem_state_psrs s)
        val cpsr2 = armML.CPSR_READ (armML.arm_mem_state_psrs ns)
        val (nzcv1, (i1, (f1, m1))) = armML.DECODE_PSR cpsr1
        val (nzcv2, (i2, (f2, m2))) = armML.DECODE_PSR cpsr2

        fun print_ireg ireg = print ("> " ^
              assemblerML.decode_arm NONE (num2Arbnum (wordsML.w2n ireg)) ^
              "\n")

        fun print_reg i = print
              ("; " ^ register2string i ^ " := " ^ toHexString_w2n (reg2(i)))

        fun print_mem a = print
              ("; mem[" ^ toHexString_w2n a ^ "] := " ^
               toHexString_w2n (bsubstML.MEM_READ(mem2,a)))

        fun print_bool b = print (if b then "1" else "0")
        fun print_nzcv (n,(z,(c, v))) = (print "; NZCV := ";
              print_bool n; print_bool z; print_bool c; print_bool v)

        fun print_mode m = print
              ("; mode := " ^ mode2string (armML.DECODE_MODE m))
    in
      ((if Wireg then
          print_ireg
            (bsubstML.MEM_READ(mem1,bsubstML.ADDR30 (armML.FETCH_PC reg1)))
        else
          ());
       print ("- t = " ^ Int.toString cycle);
       (if Wreg then app print_reg (reg_updates reg1 reg2) else ());
       (if Wmem then app print_mem (rev (!bsubstML.mem_updates)) else ());
       (if not Wflags orelse nzcv1 = nzcv2 then () else print_nzcv nzcv2);
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
  let val initial_psr = armML.SET_NZCV (false,(false,(false,false)))
      (armML.SET_IFMODE false false armML.usr (toWord32 (numML.fromInt 0)))
  in
    ENV {N = false, Z = false, C = false, V = false, E = false, M = armML.usr,
      mem = "", reg = armML.empty_registers, psr = fn x => initial_psr,
      cycles = valOf Int.maxInt, Wreg = false, Wmem = false, Wmode = false,
      Wflags = false, Wireg = false}
  end;

val e = proj_ENV (setOptions (CommandLine.arguments()) env);
val watches = (#Wreg e, #Wmem e, #Wmode e, #Wflags e, #Wireg e);

val count = ref 0;

fun STATE_ARM_MEM n s =
  if n = 0 then s
  else
    let val _ = count := !count + 1
        val _ = armML.mem_updates := []
        val ns = armML.NEXT_ARM_MEM s
        val _ = printer watches (!count) s ns
    in
      if armML.arm_mem_state_undefined s then
        ns
      else
        STATE_ARM_MEM (n - 1) ns
    end;

(* ------------------------------------------------------------------------- *)

val init_mem = if #E e then
  list_assemble bsubstML.empty_memory
    ["0x0: movs pc, #32",
     "label: b label",
     "movs pc, r14",
     "subs pc, r14, #4",
     "subs pc, r14, #8",
     "movs pc, r14",
     "subs pc, r14, #4",
     "subs pc, r14, #4"]
  else bsubstML.empty_memory;

val init_mem =
  let val m = #mem e in
    if not (m = "") then
      assemble init_mem m handle _ =>
        raise Fail ("Could not load file: " ^ m)
    else
      init_mem
  end;

val cpsr = armML.SET_NZCV (#N e,(#Z e,(#C e,#V e)))
      (armML.SET_IFMODE false false (#M e) (toWord32 (numML.fromInt 0)));

val psr = armML.CPSR_WRITE (#psr e) cpsr;

val init_state = armML.arm_mem_state (#reg e, psr, init_mem, false);

val final_state = time (STATE_ARM_MEM (#cycles e)) init_state;

val _ = print_state "run.in" init_state 0;
val _ = print_state "run.out" final_state (!count);

(* ------------------------------------------------------------------------- *)

