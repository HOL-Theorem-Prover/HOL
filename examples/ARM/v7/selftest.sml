open HolKernel Parse boolLib bossLib
open armLib arm_random_testingLib;

val _ = wordsLib.guess_lengths();

val _ = set_trace "Unicode" 0;
val _ = set_trace "arm steps" 3;
val _ = set_trace "arm step" 2;
val _ = set_trace "notify type variable guesses" 0;
val _ = set_trace "notify word length guesses" 0;

fun die() = ()
fun die() = OS.Process.exit OS.Process.failure

fun test str f x = let
  val rt = Timer.startRealTimer ()
  val res = Lib.total f x
  val elapsed = Timer.checkRealTimer rt
in
  TextIO.print ("\n" ^ str ^ " ... " ^ Time.toString elapsed ^ "s" ^
                (case res of
                   NONE => "FAILED!"
                 | _ => "\n") ^ "\n");
  case res of NONE => die() | _ => ()
end

fun time_to_minutes e =
let
  val s = Time.toSeconds e
  val minutes = Int.quot (s, 60);
  val seconds = Int.rem (s, 60);
in
  Int.toString minutes ^ "m " ^
  StringCvt.padLeft #"0" 2 (Int.toString seconds) ^ "s"
end;

local
  val updates_compare = Lib.pair_compare (Term.compare, Term.compare)
  val updates_empty = Redblackset.empty updates_compare
  fun updates_to_set l = Redblackset.addList (updates_empty, l)
  fun print_differences (s1,s2) = let
        val delta = Redblackset.listItems o Redblackset.difference
        val d1 = delta (s1, s2)
        val d2 = delta (s2, s1)
        val t2s = trace ("types",2) term_to_string
        fun update (l,r) = "[" ^ t2s l ^ " <- " ^ t2s r ^ "]\n"
      in
        print "Expecting:\n";
        List.app (print o update) d2;
        print "\nGot:\n";
        List.app (print o update) d1
      end
in
  fun step opt instr =
  let
    val opc = case arm_assemble_from_string instr
              of ([(_,n)],_) => n
               | _ => raise ERR "validate_arm_step" ""
  in
    case arm_step_updates opt opc
    of (_, Simple_step l) => l
     | _ => raise ERR "validate_arm_step" ""
  end

  fun validate_arm_step opt (instr,upds) =
  let
    val _ = print ("Validating step theorem for: " ^ instr ^ " ...\n")
    val cmp = (updates_to_set (step opt instr), updates_to_set upds)
  in
    Redblackset.equal cmp orelse
      (print_differences cmp; raise ERR "validate_arm_step" "")
  end
end

fun flag tm = mk_var (fst (dest_const tm), bool);

val psrN = flag ``psrN``
val psrZ = flag ``psrZ``
val psrC = flag ``psrC``
val psrV = flag ``psrV``
val psrQ = flag ``psrQ``
val psrE = flag ``psrE``
val psrA = flag ``psrA``
val psrI = flag ``psrI``
val psrF = flag ``psrF``

val sctlrNMFI = flag ``sctlrNMFI``

val GE = mk_var ("GE", ``:word4``);

val mode = mk_var ("mode", ``:word5``);

fun reg i = mk_var ("r" ^ Int.toString i, ``:word32``);

val r0  = reg 0
val r1  = reg 1
val r2  = reg 2
val r3  = reg 3
val r4  = reg 4
val r5  = reg 5
val r6  = reg 6
val r7  = reg 7
val r8  = reg 8
val r9  = reg 9
val r10 = reg 10
val r11 = reg 11
val r12 = reg 12
val r13 = reg 13
val r14 = reg 14
val r15 = reg 15

val mem = mk_var ("mem", ``:word32 -> word8``);

val _ = print "Starting tests ... \n\n";

val tt = Timer.startRealTimer ()

(* start tests *)

val _ = test "print_arm_assemble_from_quote" (print_arm_assemble_from_quote "0")
  `     ARCH    ARMv7
        ARM
        ALIGN   4

        ASCII   "abcd"
        BYTE    31,32
        SHORT   0xfaDB
        WORD    0b100010000,07030

        SPACE   20

        ALIGN   8

        adc     r1,#99
        adc     r1,r2
        adcs    r1,r2,#0xFF0000
        adc     pc,r3,r4,asr #29
.label: adc     sp,r3,r4,lsl lr
        adc     lr,r4,ror #0b1000
        adc     r8,r9,r4,rrx

        adr     sp,.label
        adr     r1,+#0xab0008
        adr     r2,-#20

        asr     r3,#11
        asr     r3,r9
        asr     r3,r9,r4
        rrx     r3
        rrx     r3,r5
        ror     r3,r5

        beq     .label
        bne     .label
        bcs     .label
        bcc     .label
        bmi     .label
        bpl     .label
        bvs     .label
        bvc     .label
        bhi     .label
        bls     .label
        bge     .label
        blt     .label
        bgt     .label
        ble     .label
        `;

(*
val go = step "v4";
*)
val _ = test "validate_arm_step" (fn l => List.map (validate_arm_step "v4") l)
  [("ldm r1!,{r1,r2}",
    [(r1, ``ARB:word32``),
     (r15, ``^r15 + 4w``),
     (r2, ``^mem (r1 + 7w) @@ mem (r1 + 6w) @@
             mem (r1 + 5w) @@ mem (r1 + 4w)``)]),
   ("stm r1!,{r0,r1}",
    [(``^mem (r1 + 7w)``, ``ARB:word8``),
     (``^mem (r1 + 6w)``, ``ARB:word8``),
     (``^mem (r1 + 5w)``, ``ARB:word8``),
     (``^mem (r1 + 4w)``, ``ARB:word8``),
     (``^mem (r1 + 3w)``, ``(31 >< 24) ^r0``),
     (``^mem (r1 + 2w)``, ``(23 >< 16) ^r0``),
     (``^mem (r1 + 1w)``, ``(15 >< 8) ^r0``),
     (``^mem r1``, ``(7 >< 0) ^r0``),
     (r1, ``^r1 + 8w``),
     (r15, ``^r15 + 4w``)]),
   ("TST r5, #3",
    [(psrN, ``word_msb (^r5 && 3w)``),
     (psrZ, ``(^r5) && 3w = 0w``),
     (r15, ``^r15 + 4w``)]),
   ("ADD r1, #10",
    [(r1, ``^r1 + 10w``),
     (r15, ``^r15 + 4w``)]),
   ("CMP r1, #10",
    [(psrN, ``word_msb (^r1 + 0xFFFFFFF6w)``),
     (psrZ, ``^r1 + 0xFFFFFFF6w = 0w``),
     (psrC, ``CARRY_OUT ^r1 0xFFFFFFF5w T``),
     (psrV, ``OVERFLOW ^r1 0xFFFFFFF5w T``),
     (r15, ``^r15 + 4w``)]),
   ("TST r2, #6",
    [(psrN, ``word_msb (^r2 && 6w)``),
     (psrZ, ``^r2 && 6w = 0w``),
     (r15, ``^r15 + 4w``)]),
   ("SUBCS r1, r1, #10",
    [(r1, ``^r1 + 0xFFFFFFF6w``),
     (r15, ``^r15 + 4w``)]),
   ("MOV r0, #0",
    [(r0, ``0w : word32``),
     (r15, ``^r15 + 4w``)]),
   ("CMP r1, #0",
    [(psrN, ``word_msb ^r1``),
     (psrZ, ``^r1 = 0w``),
     (psrC, ``CARRY_OUT ^r1 0xFFFFFFFFw T``),
     (psrV, ``OVERFLOW ^r1 0xFFFFFFFFw T``),
     (r15, ``^r15 + 4w``)]),
   ("ADDNE r0, r0, #1",
    [(r0, ``^r0 + 1w``),
     (r15, ``^r15 + 4w``)]),
   ("LDRNE r1, [r1]",
    [(r1, ``^mem (r1 + 3w) @@ mem (r1 + 2w) @@ mem (r1 + 1w) @@ mem r1``),
     (r15, ``^r15 + 4w``)]),
   ("BNE -#12",
    [(r15, ``^r15 + 0xFFFFFFF4w``)]),
   ("MOVGT r2, #5",
    [(r2, ``5w : word32``),
     (r15, ``^r15 + 4w``)]),
   ("LDRBNE r2, [r3]",
    [(r2, ``w2w (^mem r3) : word32``),
     (r15, ``^r15 + 4w``)]),
   ("BNE +#420",
    [(r15, ``^r15 + 420w``)]),
   ("LDRLS r2, [r11, #-40]",
    [(r2,
     ``^mem (r11 + 0xFFFFFFDBw) @@ mem (r11 + 0xFFFFFFDAw) @@
        mem (r11 + 0xFFFFFFD9w) @@ mem (r11 + 0xFFFFFFD8w)``),
    (r15, ``^r15 + 4w``)]),
   ("SUBLS r2, r2, #1",
    [(r2, ``^r2 + 0xFFFFFFFFw``),
     (r15, ``^r15 + 4w``)]),
   ("SUBLS r11, r11, #4",
    [(r11, ``^r11 + 0xFFFFFFFCw``),
     (r15, ``^r15 + 4w``)]),
   ("MOVGT r12, r0",
    [(r12, ``^r0``),
     (r15, ``^r15 + 4w``)]),
   ("ADD r0, pc, #16",
    [(r0, ``^r15 + 24w``),
     (r15, ``^r15 + 4w``)]),
   ("SUB r0, pc, #60",
    [(r0, ``^r15 + 0xFFFFFFCCw``),
     (r15, ``^r15 + 4w``)]),
   ("ADD r5, pc, #4096",
    [(r5, ``^r15 + 4104w``),
     (r15, ``^r15 + 4w``)]),
   ("STRB r2, [r3]",
    [(``^mem r3``, ``w2w ^r2 : word8``),
     (r15, ``^r15 + 4w``)]),
   ("STMIA r4, {r5-r10}",
    [(``^mem (r4 + 23w)``, ``(31 >< 24) ^r10``),
     (``^mem (r4 + 22w)``, ``(23 >< 16) ^r10``),
     (``^mem (r4 + 21w)``, ``(15 >< 8) ^r10``),
     (``^mem (r4 + 20w)``, ``(7 >< 0) ^r10``),
     (``^mem (r4 + 19w)``, ``(31 >< 24) ^r9``),
     (``^mem (r4 + 18w)``, ``(23 >< 16) ^r9``),
     (``^mem (r4 + 17w)``, ``(15 >< 8) ^r9``),
     (``^mem (r4 + 16w)``, ``(7 >< 0) ^r9``),
     (``^mem (r4 + 15w)``, ``(31 >< 24) ^r8``),
     (``^mem (r4 + 14w)``, ``(23 >< 16) ^r8``),
     (``^mem (r4 + 13w)``, ``(15 >< 8) ^r8``),
     (``^mem (r4 + 12w)``, ``(7 >< 0) ^r8``),
     (``^mem (r4 + 11w)``, ``(31 >< 24) ^r7``),
     (``^mem (r4 + 10w)``, ``(23 >< 16) ^r7``),
     (``^mem (r4 + 9w)``, ``(15 >< 8) ^r7``),
     (``^mem (r4 + 8w)``, ``(7 >< 0) ^r7``),
     (``^mem (r4 + 7w)``, ``(31 >< 24) ^r6``),
     (``^mem (r4 + 6w)``, ``(23 >< 16) ^r6``),
     (``^mem (r4 + 5w)``, ``(15 >< 8) ^r6``),
     (``^mem (r4 + 4w)``, ``(7 >< 0) ^r6``),
     (``^mem (r4 + 3w)``, ``(31 >< 24) ^r5``),
     (``^mem (r4 + 2w)``, ``(23 >< 16) ^r5``),
     (``^mem (r4 + 1w)``, ``(15 >< 8) ^r5``),
     (``^mem r4``, ``(7 >< 0) ^r5``),
     (r15, ``^r15 + 4w``)]),
   ("LDMIA r4, {r5-r10}",
    [(r15, ``^r15 + 4w``),
     (r10,
      ``^mem (r4 + 23w) @@ mem (r4 + 22w) @@
         mem (r4 + 21w) @@ mem (r4 + 20w)``),
     (r9,
      ``^mem (r4 + 19w) @@ mem (r4 + 18w) @@
         mem (r4 + 17w) @@ mem (r4 + 16w)``),
     (r8,
      ``^mem (r4 + 15w) @@ mem (r4 + 14w) @@
         mem (r4 + 13w) @@ mem (r4 + 12w)``),
     (r7,
      ``^mem (r4 + 11w) @@ mem (r4 + 10w) @@
         mem (r4 + 9w) @@ mem (r4 + 8w)``),
     (r6,
      ``^mem (r4 + 7w) @@ mem (r4 + 6w) @@ mem (r4 + 5w) @@ mem (r4 + 4w)``),
     (r5,
      ``^mem (r4 + 3w) @@ mem (r4 + 2w) @@ mem (r4 + 1w) @@ mem r4``)]),
   ("STRB r2, [r1], #1",
    [(``^mem ^r1``, ``w2w ^r2 : word8``),
     (r15, ``^r15 + 4w``),
     (r1, ``^r1 + 1w``)]),
   ("STMIB r8!, {r14}",
    [(``^mem (r8 + 7w)``, ``(31 >< 24) ^r14``),
     (``^mem (r8 + 6w)``, ``(23 >< 16) ^r14``),
     (``^mem (r8 + 5w)``, ``(15 >< 8) ^r14``),
     (``^mem (r8 + 4w)``, ``(7 >< 0) ^r14``),
     (r8, ``^r8 + 4w``),
     (r15, ``^r15 + 4w``)]),
   ("LDR pc, [r8]",
    [(r15, ``^mem (r8 + 3w) @@ mem (r8 + 2w) @@ mem (r8 + 1w) @@ mem r8``)]),
   ("LDRLS pc, [r8], #-4",
    [(r15, ``^mem (r8 + 3w) @@ mem (r8 + 2w) @@ mem (r8 + 1w) @@ mem r8``),
     (r8, ``^r8 + 0xFFFFFFFCw``)]),
   ("LDMIA sp!, {r0-r2, r15}",
    [(r13, ``^r13 + 16w``),
     (r15,
      ``^mem (r13 + 15w) @@ mem (r13 + 14w) @@
         mem (r13 + 13w) @@ mem (r13 + 12w)``),
     (r2,
      ``^mem (r13 + 11w) @@ mem (r13 + 10w) @@
         mem (r13 + 9w) @@ mem (r13 + 8w)``),
     (r1,
      ``^mem (r13 + 7w) @@ mem (r13 + 6w) @@
         mem (r13 + 5w) @@ mem (r13 + 4w)``),
     (r0,
      ``^mem (r13 + 3w) @@ mem (r13 + 2w) @@
         mem (r13 + 1w) @@ mem r13``)]),
   ("LDR r0, [pc, #308]",
    [(r0,
     ``^mem (r15 + 319w) @@ mem (r15 + 318w) @@
        mem (r15 + 317w) @@ mem (r15 + 316w)``),
    (r15, ``^r15 + 4w``)]),
   ("LDR r1, [pc, #-20]",
    [(r1,
     ``^mem (r15 + 0xFFFFFFF7w) @@ mem (r15 + 0xFFFFFFF6w) @@
        mem (r15 + 0xFFFFFFF5w) @@ mem (r15 + 0xFFFFFFF4w)``),
    (r15, ``^r15 + 4w``)]),
   ("STMDB sp!, {r0-r2, r15}",
    [(``^mem (r13 + 0xFFFFFFFFw)``, ``(31 >< 24) (^r15 + 8w)``),
     (``^mem (r13 + 0xFFFFFFFEw)``, ``(23 >< 16) (^r15 + 8w)``),
     (``^mem (r13 + 0xFFFFFFFDw)``, ``(15 >< 8) (^r15 + 8w)``),
     (``^mem (r13 + 0xFFFFFFFCw)``, ``(7 >< 0) (^r15 + 8w)``),
     (``^mem (r13 + 0xFFFFFFFBw)``, ``(31 >< 24) ^r2``),
     (``^mem (r13 + 0xFFFFFFFAw)``, ``(23 >< 16) ^r2``),
     (``^mem (r13 + 0xFFFFFFF9w)``, ``(15 >< 8) ^r2``),
     (``^mem (r13 + 0xFFFFFFF8w)``, ``(7 >< 0) ^r2``),
     (``^mem (r13 + 0xFFFFFFF7w)``, ``(31 >< 24) ^r1``),
     (``^mem (r13 + 0xFFFFFFF6w)``, ``(23 >< 16) ^r1``),
     (``^mem (r13 + 0xFFFFFFF5w)``, ``(15 >< 8) ^r1``),
     (``^mem (r13 + 0xFFFFFFF4w)``, ``(7 >< 0) ^r1``),
     (``^mem (r13 + 0xFFFFFFF3w)``, ``(31 >< 24) ^r0``),
     (``^mem (r13 + 0xFFFFFFF2w)``, ``(23 >< 16) ^r0``),
     (``^mem (r13 + 0xFFFFFFF1w)``, ``(15 >< 8) ^r0``),
     (``^mem (r13 + 0xFFFFFFF0w)``, ``(7 >< 0) ^r0``),
     (r13, ``^r13 + 0xFFFFFFF0w``),
     (r15, ``^r15 + 4w``)]),
   ("SWPB r2, r4, [r3]",
    [(``^mem r3``, ``w2w ^r4 : word8``),
     (r2, ``w2w (^mem r3) : word32``),
     (r15, ``^r15 + 4w``)]),
   ("SWP r2, r4, [r3]",
    [(``^mem (r3 + 3w)``, ``(31 >< 24) ^r4``),
     (``^mem (r3 + 2w)``, ``(23 >< 16) ^r4``),
     (``^mem (r3 + 1w)``, ``(15 >< 8) ^r4``),
     (``^mem r3``, ``(7 >< 0) ^r4``),
     (r2, ``^mem (r3 + 3w) @@ mem (r3 + 2w) @@ mem (r3 + 1w) @@ mem r3``),
     (r15, ``^r15 + 4w``)]),
   ("LDRH r2, [r3]",
    [(r2, ``w2w (^mem (r3 + 1w) @@ mem r3) : word32``),
     (r15, ``^r15 + 4w``)]),
   ("STRH r2, [r3]",
    [(``^mem (r3 + 1w)``, ``(15 >< 8) ^r2``),
     (``^mem r3``, ``(7 >< 0) ^r2``),
     (r15, ``^r15 + 4w``)]),
   ("MSR CPSR, r1",
    [(psrN, ``^r1 ' 31``),
     (psrZ, ``^r1 ' 30``),
     (psrC, ``^r1 ' 29``),
     (psrV, ``^r1 ' 28``),
     (psrQ, ``^r1 ' 27``),
     (GE, ``(19 >< 16) ^r1``),
     (psrE, ``^r1 ' 9``),
     (r15, ``^r15 + 4w``)]),
   ("MSR CPSR, #219",
    [(psrN, ``F``), (psrZ, ``F``),
     (psrC, ``F``), (psrV, ``F``),
     (psrQ, ``F``), (GE, ``0w : word4``),
     (r15, ``^r15 + 4w``)])
  ];

(*
val go = step "v4,sys";
*)
val _ = test "validate_arm_step"
        (fn l => List.map (validate_arm_step "v4,sys") l)
  [("MSR CPSR, r1",
    [(psrN, ``^r1 ' 31``),
     (psrZ, ``^r1 ' 30``),
     (psrC, ``^r1 ' 29``),
     (psrV, ``^r1 ' 28``),
     (psrQ, ``^r1 ' 27``),
     (GE, ``(19 >< 16) ^r1``),
     (psrE, ``^r1 ' 9``),
     (psrA, ``^r1 ' 8``),
     (psrI, ``^r1 ' 7``),
     (psrF, ``if ~^sctlrNMFI \/ ~r1 ' 6 then ^r1 ' 6 else ^psrF``),
     (mode, ``(4 >< 0) ^r1``),
     (r15, ``^r15 + 4w``)]),
   ("MSR CPSR, #219",
    [(psrN, ``F``), (psrZ, ``F``),
     (psrC, ``F``), (psrV, ``F``),
     (psrQ, ``F``), (GE, ``0w : word4``),
     (psrA, ``F``), (psrI, ``T``),
     (psrF, ``~^sctlrNMFI \/ ^psrF``),
     (mode, ``27w : word5``),
     (r15, ``^r15 + 4w``)])
  ];

val _ = test "arm_steps_from_quote v7 conds" (arm_steps_from_quote "v7")`
        movseq  r1,r2
        movsne  r1,r2
        movscs  r1,r2
        movscc  r1,r2
        movsmi  r1,r2
        movspl  r1,r2
        movsvs  r1,r2
        movsvc  r1,r2
        movshi  r1,r2
        movsls  r1,r2
        movsge  r1,r2
        movslt  r1,r2
        movsgt  r1,r2
        movsle  r1,r2
        `;

val _ = test "arm_steps_from_quote v4" (arm_steps_from_quote "v4,fiq")`
        adds    pc,pc,#4
        subs    pc,pc,#4
        ldr     pc,[r2,#-5]
// not supported
//      ldr     pc,[pc,r1]
        ldr     pc,[r1,-r2]!
        ldr     r2,[pc,-r3]
        ldr     r2,[r3],#-5
        ldr     pc,[r3],#-5
        ldr     pc,[r1],r2
        `;

val _ = test "arm_steps_from_quote v5" (arm_steps_from_quote "v5,fiq")`
        adds    pc,pc,#4
        subs    pc,pc,#4
        eor     pc,r1,#2
        eor     pc,r1,pc
        ldr     pc,[r2,#-5]
        ldr     pc,[pc,r1]
        ldr     pc,[r1,-r2]!
        ldr     r2,[pc,-r3]
        ldr     r2,[r3],#-5
        ldr     pc,[r3],#-5
        ldr     pc,[r1],r2
        `;

val _ = test "arm_steps_from_quote v6" (arm_steps_from_quote "v6,fiq")`
        adds    pc,pc,#3
        subs    pc,pc,#3
        ldr     pc,[r2,#-5]
        ldr     pc,[pc,r1]
        ldr     pc,[r1,-r2]!
        ldr     r2,[pc,-r3]
        ldr     r2,[r3],#-5
        ldr     pc,[r3],#-5
        ldr     pc,[r1],r2
        `;

val _ = test "arm_steps_from_quote v7" (arm_steps_from_quote "v7,fiq")`
        adc     r1,pc,r2
        adcs    r1,r10,r3,lsl r10
        add     pc,sp,#4
        adds    pc,pc,#3
        add     pc,r1,#3
        add     r1,r2,r3,ror r4
        and     r1,r2
        asr     r1,#4
        asr     r1,r2,r3
        movs    pc,lr
        b       +#16
        bfc     r10,#10,#0b1100
        bfi     r10,r9,#0xA,#5
        bic     r1,r2
        bkpt    #10
        bl      -#24
        blx     sp
        bx      sp
        clz     r1,r8
        cmn     r10,r8
        cmp     r10,r8
        cpsie   aif,#0b10000
        dbg     #4
        dmb     sy
        dsb     sy
        eor     pc,r8
        isb     sy
        ldmia   r1!,{r3-r5}
        ldmia   sp,{r3,pc}
        ldmdb   r1,{r1-r3}^
        ldmda   r1,{r1,r5,pc}^
        ldr     r1,[r2,#+3]
        ldr     pc,[r2,#-5]
        ldr     pc,[pc,r1]
        ldr     pc,[r1,-r2]!
        ldr     r2,[pc,-r3]
        ldr     r2,[r3],#-5
        ldr     pc,[r3],#-5
        ldr     pc,[r1],r2
        ldrb    r1,[r2,#+3]
        ldrb    r2,[pc,-r3]
        ldrb    r2,[r3],#-5
        ldrh    r1,[r2,#+3]
        ldrh    r2,[pc,-r3]
        ldrh    r2,[r3],#-5
        ldrsb   r1,[r2,#+3]
        ldrsb   r2,[pc,-r3]
        ldrsb   r2,[r3],#-5
        ldrsh   r1,[r2,#+3]
        ldrsh   r2,[pc,-r3]
        ldrsh   r2,[r3],#-5
        mlas    r8,r9,r10,r11
        mls     r8,r9,r10,r11
        movt    r8,#0xABCD
        movw    r8,#0xEF01
        mrs     r1,cpsr
        mrs     r1,spsr
        msr     cpsr,#16
        msr     cpsr,r1
        msr     spsr,#16
        msr     spsr,r1
        muls    r1,r3,r4
        mvn     r3,r4,rrx
        nop
        orr     r3,r4,lsl r6
        pkhbt   r1,r2,r3,lsl #4
        pld     [r2]
        pli     [r2,-r2]
        pop     {r5,r9}
        push    {r5,r9}
        qadd    r1,r2,r3
        qadd16  r1,r2,r3
        qadd8   r1,r2,r3
        qasx    r1,r2,r3
        qdadd   r1,r2,r3
        qdsub   r1,r2,r3
        qsax    r1,r2,r3
        qsub    r1,r2,r3
        qsub16  r1,r2,r3
        qsub8   r1,r2,r3
        rbit    r8,r9
        rev     r8,r9
        rev16   r8,r9
        revsh   r8,r9
        rfeia   r2!
        rsb     r3,r6,r8
        rsc     pc,r6,r8
        sadd16  r1,r2,r3
        sadd8   r1,r2,r3
        sasx    r1,r2,r3
        sbc     pc,r6,r8
        sbfx    r1,r2,#3,#4
        sel     r1,r2,r3
        setend  be
        sev
        shadd16 r5,r9,r2
        shadd8  r5,r9,r2
        shasx   r5,r9,r2
        shsax   r5,r9,r2
        shsub16 r5,r9,r2
        shsub8  r5,r9,r2
        smlabb  r0,r1,r2,r3
        smlabt  r0,r1,r2,r3
        smlatb  r0,r1,r2,r3
        smlatt  r0,r1,r2,r3
        smlad   r0,r1,r2,r3
        smladx  r0,r1,r2,r3
        smlal   r0,r1,r2,r3
        smlalbb r0,r1,r2,r3
        smlalbt r0,r1,r2,r3
        smlaltb r0,r1,r2,r3
        smlaltt r0,r1,r2,r3
        smlawb  r0,r1,r2,r3
        smlawt  r0,r1,r2,r3
        smull   r0,r1,r2,r3
        smulbb  r0,r1,r2
        smulbt  r0,r1,r2
        smultb  r0,r1,r2
        smultt  r0,r1,r2
        smulwb  r0,r1,r2
        smulwt  r0,r1,r2
        smlsd   r0,r1,r2,r3
        smlsld  r0,r1,r2,r3
        smmla   r1,r2,r3,r4
        smmls   r1,r2,r3,r4
        smmul   r1,r2,r3
        smuad   r1,r2,r3
        smusd   r1,r2,r3
        srs     sp!,#31
        ssat    r1,#2,r3
        ssat16  r1,#2,r3
        ssax    r1,r2,r3
        ssub16  r1,r2,r3
        ssub8   r1,r2,r3
        stm     r1!,{r2-r4}
        strb    r1,[r2,#4]
        strh    r1,[r2,#4]
        str     r1,[r2,#4]
        strd    r0,r1,[r2,#4]
        subs    r1,r2,#3
        svc     #8
        swp     r1,r2,[r3]
        swpb    r1,r2,[r3]
        sxtab   r1,r2,r3
        sxtab16 r1,r2,r3
        sxtah   r1,r2,r3
        sxtb    r1,r2
        sxtb16  r1,r2
        sxth    r1,r2
        teq     r1,r2
        tst     r1,r2
        uadd16  r1,r2,r3
        uadd8   r1,r2,r3
        uasx    r1,r2,r3
        ubfx    r1,r2,#3,#4
        uhadd16 r1,r2,r3
        uhadd8  r1,r2,r3
        uhasx   r1,r2,r3
        uhsax   r1,r2,r3
        uhsub16 r1,r2,r3
        uhsub8  r1,r2,r3
        umaal   r0,r1,r2,r3
        umlal   r0,r1,r2,r3
        umull   r0,r1,r2,r3
        uqadd16 r1,r2,r3
        uqadd8  r1,r2,r3
        uqasx   r1,r2,r3
        uqsax   r1,r2,r3
        uqsub16 r1,r2,r3
        uqsub8  r1,r2,r3
        usad8   r1,r2,r3
        usada8  r1,r2,r3,r4
        usat    r1,#2,r3
        usat16  r1,#2,r3
        usax    r1,r2,r3
        usub16  r1,r2,r3
        usub8   r1,r2,r3
        uxtab   r1,r2,r3
        uxtab16 r1,r2,r3
        uxtah   r1,r2,r3
        uxtb    r1,r2
        uxtb16  r1,r2
        uxth    r1,r2
        wfe
        wfi
        yield
        `;

val _ = test "arm_steps_from_quote ThumbEE" (arm_steps_from_quote "v7-R,thumb")`
        ARCH    ARMv7-R
        THUMBX

        chka    r1,r2
        hbl     #4
        hblp    #4,#5
        hbp     #4,#5
        ldr     r1,[r2,#8]
        str     r1,[r2],#8
        pop     {r3,r4}
        push    {r3,r4}
        leavex

        THUMB
        sdiv    r1,r2,r3
        tbb     [r1,r2]
        tbh     [r1,r2,LSL #1]
        udiv    r1,r2,r3
        enterx
        `;

val elapsed = Timer.checkRealTimer tt;

val _ = print ("\nTotal time: " ^ time_to_minutes elapsed ^ "\n");

val _ = OS.Process.exit OS.Process.success;
