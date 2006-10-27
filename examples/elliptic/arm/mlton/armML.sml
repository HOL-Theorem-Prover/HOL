structure armML :> armML =
struct
  nonfix empty_registers NEXT_ARM_MEM TRANSFERS LOAD_STORE empty_memory
         MEM_WRITE_BLOCK MEM_WRITE MEM_WRITE_WORD MEM_WRITE_BYTE
         MEM_READ SET_BYTE ADDR30 OUT_ARM NEXT_ARM PROJ_IF_FLAGS
         interrupt2exception PROJ_Reset PROJ_Dabort IS_Reset RUN_ARM
         CONDITION_PASSED CONDITION_PASSED2 LDC_STC ADDR_MODE5 MCR_OUT
         MRC SWP LDM_STM STM_LIST LDM_LIST ADDR_MODE4 FIRST_ADDRESS
         WB_ADDRESS ADDRESS_LIST REGISTER_LIST LDR_STR ==> ADDR_MODE2
         UP_DOWN BW_READ MLA_MUL ALU_multiply MSR MRS DATA_PROCESSING
         TEST_OR_COMP ARITHMETIC ALU ORR EOR AND ADD SUB ALU_logic
         ALU_arith_neg ALU_arith ADDR_MODE1 SHIFT_REGISTER
         SHIFT_IMMEDIATE SHIFT_REGISTER2 SHIFT_IMMEDIATE2 IMMEDIATE ROR
         ASR LSR LSL BRANCH EXCEPTION exception2mode SPSR_WRITE
         CPSR_WRITE CPSR_READ SPSR_READ mode2psr CARRY NZCV DECODE_MODE
         SET_IFMODE mode_num SET_NZ SET_NZC SET_NZCV FETCH_PC INC_PC
         REG_WRITE REG_READ num2condition num2register register2num
         exceptions2num state_out_out state_out_state mode_reg2num USER
         ::- :- DECODE_INST DECODE_LDC_STC DECODE_SWP DECODE_LDM_STM
         DECODE_MLA_MUL DECODE_LDR_STR DECODE_MSR DECODE_MRS
         DECODE_DATAP DECODE_BRANCH DECODE_PSR memop_size CPWrite
         CPMemWrite CPMemRead MemWrite MemRead arm_input_size
         arm_input_ireg_fupd arm_input_data_fupd
         arm_input_interrupt_fupd arm_input_no_cp_fupd arm_input_ireg
         arm_input_data arm_input_interrupt arm_input_no_cp arm_input
         interrupt_size Irq Fiq Dabort Prefetch Undef Reset regs_size
         regs_reg_fupd regs_psr_fupd regs_reg regs_psr regs
         arm_mem_state_size arm_mem_state_registers_fupd
         arm_mem_state_psrs_fupd arm_mem_state_memory_fupd
         arm_mem_state_undefined_fupd arm_mem_state_registers
         arm_mem_state_psrs arm_mem_state_memory arm_mem_state_undefined
         arm_mem_state arm_state_size arm_state_registers_fupd
         arm_state_psrs_fupd arm_state_ireg_fupd
         arm_state_exception_fupd arm_state_registers arm_state_psrs
         arm_state_ireg arm_state_exception arm_state state_out
         state_inp iclass_size unexec stc ldc mrc mcr cdp_und swi_ex br
         stm ldm str ldr mla_mul reg_shift data_proc mrs_msr swp
         exceptions_size fast interrupt address dabort pabort software
         undefined reset condition_size NV LE LT LS VC PL CC NE AL GT GE
         HI VS MI CS EQ mode_size safe und abt svc irq fiq usr psr_size
         SPSR_und SPSR_abt SPSR_svc SPSR_irq SPSR_fiq CPSR register_size
         r14_und r13_und r14_abt r13_abt r14_svc r13_svc r14_irq r13_irq
         r14_fiq r13_fiq r12_fiq r11_fiq r10_fiq r9_fiq r8_fiq r15 r14
         r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 * / div mod + - ^
         @ <> > < >= <= := o before;
  
  open numML setML fcpML listML rich_listML bitML wordsML;
  datatype register
       = r0
       | r1
       | r2
       | r3
       | r4
       | r5
       | r6
       | r7
       | r8
       | r9
       | r10
       | r11
       | r12
       | r13
       | r14
       | r15
       | r8_fiq
       | r9_fiq
       | r10_fiq
       | r11_fiq
       | r12_fiq
       | r13_fiq
       | r14_fiq
       | r13_irq
       | r14_irq
       | r13_svc
       | r14_svc
       | r13_abt
       | r14_abt
       | r13_und
       | r14_und
  fun register_size x = ZERO
    
  datatype psr
       = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und
  fun psr_size x = ZERO
    
  datatype mode = usr | fiq | irq | svc | abt | und | safe
  fun mode_size x = ZERO
    
  datatype condition
       = EQ
       | CS
       | MI
       | VS
       | HI
       | GE
       | GT
       | AL
       | NE
       | CC
       | PL
       | VC
       | LS
       | LT
       | LE
       | NV
  fun condition_size x = ZERO
    
  datatype exceptions
       = reset
       | undefined
       | software
       | pabort
       | dabort
       | address
       | interrupt
       | fast
  fun exceptions_size x = ZERO
    
  datatype iclass
       = swp
       | mrs_msr
       | data_proc
       | reg_shift
       | mla_mul
       | ldr
       | str
       | ldm
       | stm
       | br
       | swi_ex
       | cdp_und
       | mcr
       | mrc
       | ldc
       | stc
       | unexec
  fun iclass_size x = ZERO
    
  datatype ('a,'b)state_inp = state_inp of 'a * (num -> 'b)
  datatype ('a,'b)state_out = state_out of 'a * 'b
  type registers = register->word32
  type psrs = psr->word32
  type mem = (word30, word32) Redblackmap.dict
  datatype
  arm_state = arm_state of (registers) * (psrs) * word32 * exceptions
  fun arm_state_exception (arm_state(f,f0,c,e)) = e
    
  fun arm_state_ireg (arm_state(f,f0,c,e)) = c
    
  fun arm_state_psrs (arm_state(f,f0,c,e)) = f0
    
  fun arm_state_registers (arm_state(f,f0,c,e)) = f
    
  fun arm_state_exception_fupd f1 (arm_state(f,f0,c,e)) =
        arm_state(f,f0,c,f1 e)
    
  fun arm_state_ireg_fupd f1 (arm_state(f,f0,c,e)) =
        arm_state(f,f0,f1 c,e)
    
  fun arm_state_psrs_fupd f1 (arm_state(f,f0,c,e)) =
        arm_state(f,f1 f0,c,e)
    
  fun arm_state_registers_fupd f1 (arm_state(f,f0,c,e)) =
        arm_state(f1 f,f0,c,e)
    
  fun arm_state_size (arm_state(a0,a1,a2,a3)) =
        + ONE (exceptions_size a3)
    
  datatype
  arm_mem_state = arm_mem_state of (registers) * (psrs) * (mem) * bool
  fun arm_mem_state_undefined (arm_mem_state(f,f0,f1,b)) = b
    
  fun arm_mem_state_memory (arm_mem_state(f,f0,f1,b)) = f1
    
  fun arm_mem_state_psrs (arm_mem_state(f,f0,f1,b)) = f0
    
  fun arm_mem_state_registers (arm_mem_state(f,f0,f1,b)) = f
    
  fun arm_mem_state_undefined_fupd f2 (arm_mem_state(f,f0,f1,b)) =
        arm_mem_state(f,f0,f1,f2 b)
    
  fun arm_mem_state_memory_fupd f2 (arm_mem_state(f,f0,f1,b)) =
        arm_mem_state(f,f0,f2 f1,b)
    
  fun arm_mem_state_psrs_fupd f2 (arm_mem_state(f,f0,f1,b)) =
        arm_mem_state(f,f2 f0,f1,b)
    
  fun arm_mem_state_registers_fupd f2 (arm_mem_state(f,f0,f1,b)) =
        arm_mem_state(f2 f,f0,f1,b)
    
  fun arm_mem_state_size (arm_mem_state(a0,a1,a2,a3)) = ONE
    
  datatype regs = regs of (registers) * (psrs)
  fun regs_psr (regs(f,f0)) = f0
    
  fun regs_reg (regs(f,f0)) = f
    
  fun regs_psr_fupd f1 (regs(f,f0)) = regs(f,f1 f0)
    
  fun regs_reg_fupd f1 (regs(f,f0)) = regs(f1 f,f0)
    
  fun regs_size (regs(a0,a1)) = ONE
    
  datatype interrupt
       = Reset of regs | Undef | Prefetch | Dabort of num | Fiq | Irq
  fun interrupt_size (Reset(a)) = + ONE (regs_size a)
    | interrupt_size Undef = ZERO
    | interrupt_size Prefetch = ZERO
    | interrupt_size (Dabort(a)) = + ONE a
    | interrupt_size Fiq = ZERO
    | interrupt_size Irq = ZERO
    
  datatype
  arm_input = arm_input of word32 * word32 list * interrupt option *
                           bool
  fun arm_input_no_cp (arm_input(c,l,o,b)) = b
    
  fun arm_input_interrupt (arm_input(c,l,o,b)) = o
    
  fun arm_input_data (arm_input(c,l,o,b)) = l
    
  fun arm_input_ireg (arm_input(c,l,o,b)) = c
    
  fun arm_input_no_cp_fupd f (arm_input(c,l,o,b)) = arm_input(c,l,o,f b)
    
  fun arm_input_interrupt_fupd f (arm_input(c,l,o,b)) =
        arm_input(c,l,f o,b)
    
  fun arm_input_data_fupd f (arm_input(c,l,o,b)) = arm_input(c,f l,o,b)
    
  fun arm_input_ireg_fupd f (arm_input(c,l,o,b)) = arm_input(f c,l,o,b)
    
  fun arm_input_size (arm_input(a0,a1,a2,a3)) =
        + ONE
          (+ (list_size (fn v => ZERO) a1)
             (case a2
              of optionML.NONE => ZERO
               | optionML.SOME(x) => SUC(interrupt_size x)))
    
  datatype memop
       = MemRead of word32
       | MemWrite of bool * word32 * word32
       | CPMemRead of word32
       | CPMemWrite of word32
       | CPWrite of word32
  fun memop_size (MemRead(a)) = ONE
    | memop_size (MemWrite(a0,a1,a2)) = ONE
    | memop_size (CPMemRead(a)) = ONE
    | memop_size (CPMemWrite(a)) = ONE
    | memop_size (CPWrite(a)) = ONE
    
  val mem_updates = ref ([]: wordsML.word30 list);
  fun DECODE_PSR w =
        let val (q0,m) = DIVMOD_2EXP (fromString"5") (w2n w)
            val (q1,i) = DIVMOD_2EXP ONE (DIV2 q0)
            val (q2,f) = DIVMOD_2EXP ONE q1
            val (q3,V) = DIVMOD_2EXP ONE (DIV_2EXP (fromString"20") q2)
            val (q4,C) = DIVMOD_2EXP ONE q3
            val (q5,Z) = DIVMOD_2EXP ONE q4
        in
           ((ODD
               q5,(Z
                   =
                   ONE,(C
                        =
                        ONE,V
                            =
                            ONE))),(f
                                    =
                                    ONE,(i
                                         =
                                         ONE,n2w_itself
                                               (m,(Tyop ("i5", []))))))
        end
    
  fun DECODE_BRANCH w =
        let val (L,offset) = DIVMOD_2EXP (fromString"24") (w2n w)
        in
           (ODD L,n2w_itself (offset,(Tyop ("i24", []))))
        end
    
  fun DECODE_DATAP w =
        let val (q0,opnd2) = DIVMOD_2EXP (fromString"12") (w2n w)
            val (q1,Rd) = DIVMOD_2EXP (fromString"4") q0
            val (q2,Rn) = DIVMOD_2EXP (fromString"4") q1
            val (q3,S) = DIVMOD_2EXP ONE q2
            val (q4,opcode) = DIVMOD_2EXP (fromString"4") q3
        in
           (ODD
              q4,(n2w_itself
                    (opcode,(Tyop ("i4", []))),(S
                                                =
                                                ONE,(n2w_itself
                                                       (Rn,(Tyop ("i4", []))),(n2w_itself
                                                                                 (Rd,(Tyop ("i4", []))),n2w_itself
                                                                                                          (opnd2,(Tyop ("i12", []))))))))
        end
    
  fun DECODE_MRS w =
        let val (q,Rd) =
                DIVMOD_2EXP (fromString"4")
                  (DIV_2EXP (fromString"12") (w2n w))
        in
           (ODD
              (DIV_2EXP (fromString"6")
                 q),n2w_itself (Rd,(Tyop ("i4", []))))
        end
    
  fun DECODE_MSR w =
        let val (q0,opnd) = DIVMOD_2EXP (fromString"12") (w2n w)
            val (q1,bit16) =
                DIVMOD_2EXP ONE (DIV_2EXP (fromString"4") q0)
            val (q2,bit19) = DIVMOD_2EXP ONE (DIV_2EXP TWO q1)
            val (q3,R) = DIVMOD_2EXP ONE (DIV_2EXP TWO q2)
        in
           (ODD
              (DIV_2EXP TWO
                 q3),(R
                      =
                      ONE,(bit19
                           =
                           ONE,(bit16
                                =
                                ONE,(n2w_itself
                                       (MOD_2EXP (fromString"4")
                                          opnd,(Tyop ("i4", []))),n2w_itself
                                                                    (opnd,(Tyop ("i12", []))))))))
        end
    
  fun DECODE_LDR_STR w =
        let val (q0,offset) = DIVMOD_2EXP (fromString"12") (w2n w)
            val (q1,Rd) = DIVMOD_2EXP (fromString"4") q0
            val (q2,Rn) = DIVMOD_2EXP (fromString"4") q1
            val (q3,L) = DIVMOD_2EXP ONE q2
            val (q4,W) = DIVMOD_2EXP ONE q3
            val (q5,B) = DIVMOD_2EXP ONE q4
            val (q6,U) = DIVMOD_2EXP ONE q5
            val (q7,P) = DIVMOD_2EXP ONE q6
        in
           (ODD
              q7,(P
                  =
                  ONE,(U
                       =
                       ONE,(B
                            =
                            ONE,(W
                                 =
                                 ONE,(L
                                      =
                                      ONE,(n2w_itself
                                             (Rn,(Tyop ("i4", []))),(n2w_itself
                                                                       (Rd,(Tyop ("i4", []))),n2w_itself
                                                                                                (offset,(Tyop ("i12", [])))))))))))
        end
    
  fun DECODE_MLA_MUL w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString"4") (w2n w)
            val (q1,Rs) =
                DIVMOD_2EXP (fromString"4")
                  (DIV_2EXP (fromString"4") q0)
            val (q2,Rn) = DIVMOD_2EXP (fromString"4") q1
            val (q3,Rd) = DIVMOD_2EXP (fromString"4") q2
            val (q4,S) = DIVMOD_2EXP ONE q3
            val (q5,A) = DIVMOD_2EXP ONE q4
            val (q6,Sgn) = DIVMOD_2EXP ONE q5
        in
           (ODD
              q6,(Sgn
                  =
                  ONE,(A
                       =
                       ONE,(S
                            =
                            ONE,(n2w_itself
                                   (Rd,(Tyop ("i4", []))),(n2w_itself
                                                             (Rn,(Tyop ("i4", []))),(n2w_itself
                                                                                       (Rs,(Tyop ("i4", []))),n2w_itself
                                                                                                                (Rm,(Tyop ("i4", []))))))))))
        end
    
  fun DECODE_LDM_STM w =
        let val (q0,list) = DIVMOD_2EXP (fromString"16") (w2n w)
            val (q1,Rn) = DIVMOD_2EXP (fromString"4") q0
            val (q2,L) = DIVMOD_2EXP ONE q1
            val (q3,W) = DIVMOD_2EXP ONE q2
            val (q4,S) = DIVMOD_2EXP ONE q3
            val (q5,U) = DIVMOD_2EXP ONE q4
        in
           (ODD
              q5,(U
                  =
                  ONE,(S
                       =
                       ONE,(W
                            =
                            ONE,(L
                                 =
                                 ONE,(n2w_itself
                                        (Rn,(Tyop ("i4", []))),n2w_itself
                                                                 (list,(Tyop ("i16", [])))))))))
        end
    
  fun DECODE_SWP w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString"4") (w2n w)
            val (q1,Rd) =
                DIVMOD_2EXP (fromString"4")
                  (DIV_2EXP (fromString"8") q0)
            val (q2,Rn) = DIVMOD_2EXP (fromString"4") q1
        in
           (ODD
              (DIV_2EXP TWO
                 q2),(n2w_itself
                        (Rn,(Tyop ("i4", []))),(n2w_itself
                                                  (Rd,(Tyop ("i4", []))),n2w_itself
                                                                           (Rm,(Tyop ("i4", []))))))
        end
    
  fun DECODE_LDC_STC w =
        let val (q0,offset) = DIVMOD_2EXP (fromString"8") (w2n w)
            val (q1,Rn) =
                DIVMOD_2EXP (fromString"4")
                  (DIV_2EXP (fromString"8") q0)
            val (q2,L) = DIVMOD_2EXP ONE q1
            val (q3,W) = DIVMOD_2EXP ONE q2
            val (q4,U) = DIVMOD_2EXP ONE (DIV2 q3)
        in
           (ODD
              q4,(U
                  =
                  ONE,(W
                       =
                       ONE,(L
                            =
                            ONE,(n2w_itself
                                   (Rn,(Tyop ("i4", []))),n2w_itself
                                                            (offset,(Tyop ("i8", []))))))))
        end
    
  fun DECODE_INST w =
        let val (q0,b4) =
                DIVMOD_2EXP ONE (DIV_2EXP (fromString"4") (w2n w))
            val (q1,b65) = DIVMOD_2EXP TWO q0
            val (q2,b7) = DIVMOD_2EXP ONE q1
            val (q3,b20) =
                DIVMOD_2EXP ONE (DIV_2EXP (fromString"12") q2)
            val (q4,b21) = DIVMOD_2EXP ONE q3
            val (q5,b23) = DIVMOD_2EXP ONE (DIV2 q4)
            val (q6,b24) = DIVMOD_2EXP ONE q5
            val (q7,b25) = DIVMOD_2EXP ONE q6
            val bits2726 = MOD_2EXP TWO q7
            val
                (bit25,(bit24,(bit23,(bit21,(bit20,(bit7,(bits65,bit4)))))))
                =
                (b25
                 =
                 ONE,(b24
                      =
                      ONE,(b23
                           =
                           ONE,(b21
                                =
                                ONE,(b20
                                     =
                                     ONE,(b7 = ONE,(b65,b4 = ONE)))))))
        in
           if bits2726 = ZERO
             then (if bit24 andalso (not bit23 andalso not bit20)
                     then (if bit25 orelse not bit4 then mrs_msr
                             else if not bit21
                                     andalso
                                     (BITS (fromString"11")
                                        (fromString"5") (w2n w)
                                      =
                                      (fromString"4")) then swp
                                    else cdp_und)
                     else if not bit25 andalso bit4
                            then (if not bit7 then reg_shift
                                    else if not bit24
                                            andalso
                                            (bits65 = ZERO) then mla_mul
                                           else cdp_und) else data_proc)
             else if bits2726 = ONE
                    then (if bit25 andalso bit4 then cdp_und
                            else if bit20 then ldr else str)
                    else if bits2726 = TWO
                           then (if bit25 then br
                                   else if bit20 then ldm else stm)
                           else if bit25
                                  then (if bit24 then swi_ex
                                          else if bit4
                                                 then (if bit20 then mrc
                                                         else mcr)
                                                 else cdp_und)
                                  else if bit20 then ldc else stc
        end
    
  fun :- a b = fn m => fn c => if a = c then b else m c
    
  fun ::- a l =
        fn m => fn b =>
        if word_ls a b andalso < (- (w2n b) (w2n a)) (LENGTH l)
          then EL (- (w2n b) (w2n a)) l else m b
    
  fun USER mode = (mode = usr) orelse (mode = safe)
    
  fun mode_reg2num m w =
        let val n = w2n w
        in
           if (n = (fromString"15"))
              orelse
              (USER m
               orelse
               ((m = fiq) andalso < n (fromString"8")
                orelse
                not (m = fiq) andalso < n (fromString"13"))) then n
             else case m
                   of usr => raise Fail ""
                    | fiq => + n (fromString"8")
                    | irq => + n (fromString"10")
                    | svc => + n (fromString"12")
                    | abt => + n (fromString"14")
                    | und => + n (fromString"16")
                    | safe => raise Fail ""
        end
    
  fun state_out_state (state_out (a,b)) = a
    
  fun state_out_out (state_out (a,b)) = b
    
  fun exceptions2num reset = ZERO
    | exceptions2num undefined = ONE
    | exceptions2num software = TWO
    | exceptions2num pabort = (fromString"3")
    | exceptions2num dabort = (fromString"4")
    | exceptions2num address = (fromString"5")
    | exceptions2num interrupt = (fromString"6")
    | exceptions2num fast = (fromString"7")
    
  fun register2num r0 = ZERO
    | register2num r1 = ONE
    | register2num r2 = TWO
    | register2num r3 = (fromString"3")
    | register2num r4 = (fromString"4")
    | register2num r5 = (fromString"5")
    | register2num r6 = (fromString"6")
    | register2num r7 = (fromString"7")
    | register2num r8 = (fromString"8")
    | register2num r9 = (fromString"9")
    | register2num r10 = (fromString"10")
    | register2num r11 = (fromString"11")
    | register2num r12 = (fromString"12")
    | register2num r13 = (fromString"13")
    | register2num r14 = (fromString"14")
    | register2num r15 = (fromString"15")
    | register2num r8_fiq = (fromString"16")
    | register2num r9_fiq = (fromString"17")
    | register2num r10_fiq = (fromString"18")
    | register2num r11_fiq = (fromString"19")
    | register2num r12_fiq = (fromString"20")
    | register2num r13_fiq = (fromString"21")
    | register2num r14_fiq = (fromString"22")
    | register2num r13_irq = (fromString"23")
    | register2num r14_irq = (fromString"24")
    | register2num r13_svc = (fromString"25")
    | register2num r14_svc = (fromString"26")
    | register2num r13_abt = (fromString"27")
    | register2num r14_abt = (fromString"28")
    | register2num r13_und = (fromString"29")
    | register2num r14_und = (fromString"30")
    
  fun num2register n =
        if n = ZERO then r0
          else if n = ONE then r1
                 else if n = TWO then r2
                        else if n = (fromString"3") then r3
                               else if n = (fromString"4") then r4
                                      else if n = (fromString"5")
                                             then r5
                                             else if n = (fromString"6")
                                                    then r6
                                                    else if n
                                                            =
                                                            (
                                                            fromString
                                                            "7"
                                                            ) then r7
                                                           else if n
                                                                   =
                                                                   (
                                                                   fromString
                                                                   "8"
                                                                   )
                                                                  then r8
                                                                  else if n
                                                                          =
                                                                          (
                                                                          fromString
                                                                          "9"
                                                                          )
                                                                         then r9
                                                                         else if n
                                                                                 =
                                                                                 (
                                                                                 fromString
                                                                                 "10"
                                                                                 )
                                                                                then r10
                                                                                else if n
                                                                                        =
                                                                                        (
                                                                                        fromString
                                                                                        "11"
                                                                                        )
                                                                                       then r11
                                                                                       else if n
                                                                                               =
                                                                                               (
                                                                                               fromString
                                                                                               "12"
                                                                                               )
                                                                                              then r12
                                                                                              else if n
                                                                                                      =
                                                                                                      (
                                                                                                      fromString
                                                                                                      "13"
                                                                                                      )
                                                                                                     then r13
                                                                                                     else if n
                                                                                                             =
                                                                                                             (
                                                                                                             fromString
                                                                                                             "14"
                                                                                                             )
                                                                                                            then r14
                                                                                                            else if n
                                                                                                                    =
                                                                                                                    (
                                                                                                                    fromString
                                                                                                                    "15"
                                                                                                                    )
                                                                                                                   then r15
                                                                                                                   else if n
                                                                                                                           =
                                                                                                                           (
                                                                                                                           fromString
                                                                                                                           "16"
                                                                                                                           )
                                                                                                                          then r8_fiq
                                                                                                                          else if n
                                                                                                                                  =
                                                                                                                                  (
                                                                                                                                  fromString
                                                                                                                                  "17"
                                                                                                                                  )
                                                                                                                                 then r9_fiq
                                                                                                                                 else if n
                                                                                                                                         =
                                                                                                                                         (
                                                                                                                                         fromString
                                                                                                                                         "18"
                                                                                                                                         )
                                                                                                                                        then r10_fiq
                                                                                                                                        else if n
                                                                                                                                                =
                                                                                                                                                (
                                                                                                                                                fromString
                                                                                                                                                "19"
                                                                                                                                                )
                                                                                                                                               then r11_fiq
                                                                                                                                               else if n
                                                                                                                                                       =
                                                                                                                                                       (
                                                                                                                                                       fromString
                                                                                                                                                       "20"
                                                                                                                                                       )
                                                                                                                                                      then r12_fiq
                                                                                                                                                      else if n
                                                                                                                                                              =
                                                                                                                                                              (
                                                                                                                                                              fromString
                                                                                                                                                              "21"
                                                                                                                                                              )
                                                                                                                                                             then r13_fiq
                                                                                                                                                             else if n
                                                                                                                                                                     =
                                                                                                                                                                     (
                                                                                                                                                                     fromString
                                                                                                                                                                     "22"
                                                                                                                                                                     )
                                                                                                                                                                    then r14_fiq
                                                                                                                                                                    else if n
                                                                                                                                                                            =
                                                                                                                                                                            (
                                                                                                                                                                            fromString
                                                                                                                                                                            "23"
                                                                                                                                                                            )
                                                                                                                                                                           then r13_irq
                                                                                                                                                                           else if n
                                                                                                                                                                                   =
                                                                                                                                                                                   (
                                                                                                                                                                                   fromString
                                                                                                                                                                                   "24"
                                                                                                                                                                                   )
                                                                                                                                                                                  then r14_irq
                                                                                                                                                                                  else if n
                                                                                                                                                                                          =
                                                                                                                                                                                          (
                                                                                                                                                                                          fromString
                                                                                                                                                                                          "25"
                                                                                                                                                                                          )
                                                                                                                                                                                         then r13_svc
                                                                                                                                                                                         else if n
                                                                                                                                                                                                 =
                                                                                                                                                                                                 (
                                                                                                                                                                                                 fromString
                                                                                                                                                                                                 "26"
                                                                                                                                                                                                 )
                                                                                                                                                                                                then r14_svc
                                                                                                                                                                                                else if n
                                                                                                                                                                                                        =
                                                                                                                                                                                                        (
                                                                                                                                                                                                        fromString
                                                                                                                                                                                                        "27"
                                                                                                                                                                                                        )
                                                                                                                                                                                                       then r13_abt
                                                                                                                                                                                                       else if n
                                                                                                                                                                                                               =
                                                                                                                                                                                                               (
                                                                                                                                                                                                               fromString
                                                                                                                                                                                                               "28"
                                                                                                                                                                                                               )
                                                                                                                                                                                                              then r14_abt
                                                                                                                                                                                                              else if n
                                                                                                                                                                                                                      =
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                      fromString
                                                                                                                                                                                                                      "29"
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                     then r13_und
                                                                                                                                                                                                                     else if n
                                                                                                                                                                                                                             =
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                             fromString
                                                                                                                                                                                                                             "30"
                                                                                                                                                                                                                             )
                                                                                                                                                                                                                            then r14_und
                                                                                                                                                                                                                            else raise Fail
                                                                                                                                                                                                                                    "num2register: 30 < n"
    
  fun num2condition n =
        if n = ZERO then EQ
          else if n = ONE then CS
                 else if n = TWO then MI
                        else if n = (fromString"3") then VS
                               else if n = (fromString"4") then HI
                                      else if n = (fromString"5")
                                             then GE
                                             else if n = (fromString"6")
                                                    then GT
                                                    else if n
                                                            =
                                                            (
                                                            fromString
                                                            "7"
                                                            ) then AL
                                                           else if n
                                                                   =
                                                                   (
                                                                   fromString
                                                                   "8"
                                                                   )
                                                                  then NE
                                                                  else if n
                                                                          =
                                                                          (
                                                                          fromString
                                                                          "9"
                                                                          )
                                                                         then CC
                                                                         else if n
                                                                                 =
                                                                                 (
                                                                                 fromString
                                                                                 "10"
                                                                                 )
                                                                                then PL
                                                                                else if n
                                                                                        =
                                                                                        (
                                                                                        fromString
                                                                                        "11"
                                                                                        )
                                                                                       then VC
                                                                                       else if n
                                                                                               =
                                                                                               (
                                                                                               fromString
                                                                                               "12"
                                                                                               )
                                                                                              then LS
                                                                                              else if n
                                                                                                      =
                                                                                                      (
                                                                                                      fromString
                                                                                                      "13"
                                                                                                      )
                                                                                                     then LT
                                                                                                     else if n
                                                                                                             =
                                                                                                             (
                                                                                                             fromString
                                                                                                             "14"
                                                                                                             )
                                                                                                            then LE
                                                                                                            else if n
                                                                                                                    =
                                                                                                                    (
                                                                                                                    fromString
                                                                                                                    "15"
                                                                                                                    )
                                                                                                                   then NV
                                                                                                                   else raise Fail
                                                                                                                           "num2condition: 15 < n"
    
  fun REG_READ reg m n =
        if word_eq n (n2w_itself ((fromString"15"),(Tyop ("i4", []))))
          then word_add (reg r15)
                 (n2w_itself ((fromString"8"),(Tyop ("i32", []))))
          else reg (num2register (mode_reg2num m n))
    
  fun REG_WRITE reg m n d = :- (num2register (mode_reg2num m n)) d reg
    
  fun INC_PC reg =
        :- r15
          (word_add (reg r15)
             (n2w_itself ((fromString"4"),(Tyop ("i32", []))))) reg
    
  fun FETCH_PC reg = reg r15
    
  fun SET_NZCV (N,(Z,(C,V))) w =
        word_modify (fn i => fn b =>
          (i = (fromString"31")) andalso N
          orelse
          ((i = (fromString"30")) andalso Z
           orelse
           ((i = (fromString"29")) andalso C
            orelse
            ((i = (fromString"28")) andalso V
             orelse
             < i (fromString"28") andalso b)))) w
    
  fun SET_NZC (N,(Z,C)) w =
        SET_NZCV (N,(Z,(C,index w (fromString"28")))) w
    
  fun SET_NZ (N,Z) w = SET_NZC (N,(Z,index w (fromString"29"))) w
    
  fun mode_num mode =
        case mode
         of usr => n2w_itself ((fromString"16"),(Tyop ("i5", [])))
          | fiq => n2w_itself ((fromString"17"),(Tyop ("i5", [])))
          | irq => n2w_itself ((fromString"18"),(Tyop ("i5", [])))
          | svc => n2w_itself ((fromString"19"),(Tyop ("i5", [])))
          | abt => n2w_itself ((fromString"23"),(Tyop ("i5", [])))
          | und => n2w_itself ((fromString"27"),(Tyop ("i5", [])))
          | safe => n2w_itself (ZERO,(Tyop ("i5", [])))
    
  fun SET_IFMODE irq' fiq' mode w =
        word_modify (fn i => fn b =>
          (< (fromString"7") i orelse (i = (fromString"5"))) andalso b
          orelse
          ((i = (fromString"7")) andalso irq'
           orelse
           ((i = (fromString"6")) andalso fiq'
            orelse
            < i (fromString"5") andalso index (mode_num mode) i))) w
    
  fun DECODE_MODE m =
        case word_eq m (n2w_itself ((fromString"16"),(Tyop ("i5", []))))
         of true => usr
          | false =>
               (case
                  word_eq m
                    (n2w_itself ((fromString"17"),(Tyop ("i5", []))))
                of true => fiq
                 | false =>
                      (case
                         word_eq m
                           (n2w_itself
                              ((fromString"18"),(Tyop ("i5", []))))
                       of true => irq
                        | false =>
                             (case
                                word_eq m
                                  (n2w_itself
                                     ((
                                      fromString
                                      "19"
                                      ),(Tyop ("i5", []))))
                              of true => svc
                               | false =>
                                    (case
                                       word_eq m
                                         (n2w_itself
                                            ((
                                             fromString
                                             "23"
                                             ),(Tyop ("i5", []))))
                                     of true => abt
                                      | false =>
                                           (case
                                              word_eq m
                                                (n2w_itself
                                                   ((
                                                    fromString
                                                    "27"
                                                    ),(Tyop ("i5", []))))
                                            of true => und
                                             | false => safe)))))
    
  fun NZCV w =
        (index w
           (
           fromString
           "31"
           ),(index w
                (
                fromString
                "30"
                ),(index w (fromString"29"),index w (fromString"28"))))
    
  fun CARRY (n,(z,(c,v))) = c
    
  fun mode2psr mode =
        case mode
         of usr => CPSR
          | fiq => SPSR_fiq
          | irq => SPSR_irq
          | svc => SPSR_svc
          | abt => SPSR_abt
          | und => SPSR_und
          | safe => CPSR
    
  fun SPSR_READ psr mode = psr (mode2psr mode)
    
  fun CPSR_READ psr = psr CPSR
    
  fun CPSR_WRITE psr cpsr = :- CPSR cpsr psr
    
  fun SPSR_WRITE psr mode spsr =
        if USER mode then psr else :- (mode2psr mode) spsr psr
    
  fun exception2mode e =
        case e
         of reset => svc
          | undefined => und
          | software => svc
          | pabort => abt
          | dabort => abt
          | address => svc
          | interrupt => irq
          | fast => fiq
    
  fun EXCEPTION reg psr e =
        let val cpsr = CPSR_READ psr
            val fiq' =
                ((e = reset) orelse (e = fast))
                orelse
                index cpsr (fromString"6")
            and mode' = exception2mode e
            and pc =
                n2w_itself
                  ( *  (fromString"4")
                     (exceptions2num e),(Tyop ("i32", [])))
            val reg' =
                REG_WRITE reg mode'
                  (n2w_itself ((fromString"14"),(Tyop ("i4", []))))
                  (word_add (FETCH_PC reg)
                     (n2w_itself ((fromString"4"),(Tyop ("i32", [])))))
        in
           regs(REG_WRITE reg' usr
                  (n2w_itself ((fromString"15"),(Tyop ("i4", [])))) pc,
           CPSR_WRITE (SPSR_WRITE psr mode' cpsr)
             (SET_IFMODE true fiq' mode' cpsr))
        end
    
  fun BRANCH reg psr mode ireg =
        let val (L,offset) = DECODE_BRANCH ireg
            and pc =
                REG_READ reg usr
                  (n2w_itself ((fromString"15"),(Tyop ("i4", []))))
            val br_addr =
                word_add pc
                  (word_lsl (sw2sw_itself (Tyop ("i32", [])) offset)
                     TWO)
            val pc_reg =
                REG_WRITE reg usr
                  (n2w_itself ((fromString"15"),(Tyop ("i4", []))))
                  br_addr
        in
           regs(if L
                  then REG_WRITE pc_reg mode
                         (n2w_itself
                            ((fromString"14"),(Tyop ("i4", []))))
                         (word_add (FETCH_PC reg)
                            (n2w_itself
                               ((fromString"4"),(Tyop ("i32", [])))))
                  else pc_reg,
           psr)
        end
    
  fun LSL m n c =
        if word_eq n (n2w_itself (ZERO,(Tyop ("i8", [])))) then (c,m)
          else (word_ls n
                  (n2w_itself ((fromString"32"),(Tyop ("i8", []))))
                andalso
                index m (- (fromString"32") (w2n n)),word_lsl m (w2n n))
    
  fun LSR m n c =
        if word_eq n (n2w_itself (ZERO,(Tyop ("i8", []))))
          then LSL m (n2w_itself (ZERO,(Tyop ("i8", [])))) c
          else (word_ls n
                  (n2w_itself ((fromString"32"),(Tyop ("i8", []))))
                andalso
                index m (- (w2n n) ONE),word_lsr m (w2n n))
    
  fun ASR m n c =
        if word_eq n (n2w_itself (ZERO,(Tyop ("i8", []))))
          then LSL m (n2w_itself (ZERO,(Tyop ("i8", [])))) c
          else (index m
                  (MIN (fromString"31")
                     (- (w2n n) ONE)),word_asr m (w2n n))
    
  fun ROR m n c =
        if word_eq n (n2w_itself (ZERO,(Tyop ("i8", []))))
          then LSL m (n2w_itself (ZERO,(Tyop ("i8", [])))) c
          else (index m
                  (- (w2n (w2w_itself (Tyop ("i5", [])) n))
                     ONE),word_ror m (w2n n))
    
  fun IMMEDIATE C opnd2 =
        let val rot =
                word_extract_itself (Tyop ("i8", [])) (fromString"11")
                  (fromString"8") opnd2
            and imm =
                word_extract_itself (Tyop ("i32", [])) (fromString"7")
                  ZERO opnd2
        in
           ROR imm (word_mul (n2w_itself (TWO,(Tyop ("i8", [])))) rot) C
        end
    
  fun SHIFT_IMMEDIATE2 shift sh rm c =
        case word_eq sh (n2w_itself (ZERO,(Tyop ("i2", []))))
         of true => LSL rm shift c
          | false =>
               (case word_eq sh (n2w_itself (ONE,(Tyop ("i2", []))))
                of true =>
                      LSR rm
                        (if word_eq shift
                              (n2w_itself (ZERO,(Tyop ("i8", []))))
                           then n2w_itself
                                  ((fromString"32"),(Tyop ("i8", [])))
                           else shift) c
                 | false =>
                      (case
                         word_eq sh (n2w_itself (TWO,(Tyop ("i2", []))))
                       of true =>
                             ASR rm
                               (if word_eq shift
                                     (n2w_itself
                                        (ZERO,(Tyop ("i8", []))))
                                  then n2w_itself
                                         ((
                                          fromString
                                          "32"
                                          ),(Tyop ("i8", [])))
                                  else shift) c
                        | false =>
                             if word_eq shift
                                  (n2w_itself (ZERO,(Tyop ("i8", []))))
                               then word_rrx (c,rm)
                               else ROR rm shift c))
    
  fun SHIFT_REGISTER2 shift sh rm c =
        case word_eq sh (n2w_itself (ZERO,(Tyop ("i2", []))))
         of true => LSL rm shift c
          | false =>
               (case word_eq sh (n2w_itself (ONE,(Tyop ("i2", []))))
                of true => LSR rm shift c
                 | false =>
                      (case
                         word_eq sh (n2w_itself (TWO,(Tyop ("i2", []))))
                       of true => ASR rm shift c
                        | false => ROR rm shift c))
    
  fun SHIFT_IMMEDIATE reg mode C w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString"4") (w2n w)
            val (q1,Sh) = DIVMOD_2EXP TWO (DIV2 q0)
            val shift = MOD_2EXP (fromString"5") q1
            val rm =
                REG_READ reg mode (n2w_itself (Rm,(Tyop ("i4", []))))
        in
           SHIFT_IMMEDIATE2 (n2w_itself (shift,(Tyop ("i8", []))))
             (n2w_itself (Sh,(Tyop ("i2", [])))) rm C
        end
    
  fun SHIFT_REGISTER reg mode C w =
        let val (q0,Rm) = DIVMOD_2EXP (fromString"4") (w2n w)
            val (q1,Sh) = DIVMOD_2EXP TWO (DIV2 q0)
            val Rs = MOD_2EXP (fromString"4") (DIV2 q1)
            val shift =
                MOD_2EXP (fromString"8")
                  (w2n
                     (REG_READ reg mode
                        (n2w_itself (Rs,(Tyop ("i4", []))))))
            and rm =
                REG_READ (INC_PC reg) mode
                  (n2w_itself (Rm,(Tyop ("i4", []))))
        in
           SHIFT_REGISTER2 (n2w_itself (shift,(Tyop ("i8", []))))
             (n2w_itself (Sh,(Tyop ("i2", [])))) rm C
        end
    
  fun ADDR_MODE1 reg mode C Im opnd2 =
        if Im then IMMEDIATE C opnd2
          else if index opnd2 (fromString"4")
                 then SHIFT_REGISTER reg mode C opnd2
                 else SHIFT_IMMEDIATE reg mode C opnd2
    
  fun ALU_arith f rn op2 =
        let val sign = word_msb rn
            and (q,r) =
                DIVMOD_2EXP (fromString"32") (f (w2n rn) (w2n op2))
            val res = n2w_itself (r,(Tyop ("i32", [])))
        in
           ((word_msb
               res,(r
                    =
                    ZERO,(ODD
                            q,(word_msb op2 = sign)
                              andalso
                              not (word_msb res = sign)))),res)
        end
    
  fun ALU_arith_neg f rn op2 =
        let val sign = word_msb rn
            and (q,r) =
                DIVMOD_2EXP (fromString"32")
                  (f (w2n rn) (w2n (word_2comp op2)))
            val res = n2w_itself (r,(Tyop ("i32", [])))
        in
           ((word_msb
               res,(r
                    =
                    ZERO,(ODD q
                          orelse
                          word_eq op2
                            (n2w_itself
                               (ZERO,(Tyop ("i32", [])))),not
                                                            (word_msb
                                                               op2
                                                             =
                                                             sign)
                                                          andalso
                                                          not
                                                            (word_msb
                                                               res
                                                             =
                                                             sign)))),res)
        end
    
  fun ALU_logic res =
        ((word_msb
            res,(word_eq res
                   (n2w_itself
                      (ZERO,(Tyop ("i32", [])))),(false,false))),res)
    
  fun SUB a b c =
        ALU_arith_neg (fn x => fn y =>
          + (+ x y) (if c then ZERO else (fromString"4294967295"))) a b
    
  fun ADD a b c =
        ALU_arith (fn x => fn y => + (+ x y) (if c then ONE else ZERO))
          a b
    
  fun AND a b = ALU_logic (word_and a b)
    
  fun EOR a b = ALU_logic (word_xor a b)
    
  fun ORR a b = ALU_logic (word_or a b)
    
  fun ALU opc rn op2 c =
        case word_eq opc (n2w_itself (ZERO,(Tyop ("i4", []))))
         of true => AND rn op2
          | false =>
               (case word_eq opc (n2w_itself (ONE,(Tyop ("i4", []))))
                of true => EOR rn op2
                 | false =>
                      (case
                         word_eq opc
                           (n2w_itself (TWO,(Tyop ("i4", []))))
                       of true => SUB rn op2 true
                        | false =>
                             (case
                                word_eq opc
                                  (n2w_itself
                                     ((
                                      fromString
                                      "4"
                                      ),(Tyop ("i4", []))))
                              of true => ADD rn op2 false
                               | false =>
                                    (case
                                       word_eq opc
                                         (n2w_itself
                                            ((
                                             fromString
                                             "3"
                                             ),(Tyop ("i4", []))))
                                     of true =>
                                           ADD (word_1comp rn) op2 true
                                      | false =>
                                           (case
                                              word_eq opc
                                                (n2w_itself
                                                   ((
                                                    fromString
                                                    "5"
                                                    ),(Tyop ("i4", []))))
                                            of true => ADD rn op2 c
                                             | false =>
                                                  (case
                                                     word_eq opc
                                                       (n2w_itself
                                                          ((
                                                           fromString
                                                           "6"
                                                           ),(Tyop ("i4", []))))
                                                   of true =>
                                                         SUB rn op2 c
                                                    | false =>
                                                         (case
                                                            word_eq opc
                                                              (n2w_itself
                                                                 ((
                                                                  fromString
                                                                  "7"
                                                                  ),(Tyop ("i4", []))))
                                                          of true =>
                                                                ADD
                                                                  (word_1comp
                                                                     rn)
                                                                  op2 c
                                                           | false =>
                                                                (case
                                                                   word_eq
                                                                     opc
                                                                     (n2w_itself
                                                                        ((
                                                                         fromString
                                                                         "8"
                                                                         ),(Tyop ("i4", []))))
                                                                 of true =>
                                                                       AND
                                                                         rn
                                                                         op2
                                                                  | false =>
                                                                       (case
                                                                          word_eq
                                                                            opc
                                                                            (n2w_itself
                                                                               ((
                                                                                fromString
                                                                                "9"
                                                                                ),(Tyop ("i4", []))))
                                                                        of true =>
                                                                              EOR
                                                                                rn
                                                                                op2
                                                                         | false =>
                                                                              (case
                                                                                 word_eq
                                                                                   opc
                                                                                   (n2w_itself
                                                                                      ((
                                                                                       fromString
                                                                                       "10"
                                                                                       ),(Tyop ("i4", []))))
                                                                               of true =>
                                                                                     SUB
                                                                                       rn
                                                                                       op2
                                                                                       true
                                                                                | false =>
                                                                                     (case
                                                                                        word_eq
                                                                                          opc
                                                                                          (n2w_itself
                                                                                             ((
                                                                                              fromString
                                                                                              "11"
                                                                                              ),(Tyop ("i4", []))))
                                                                                      of true =>
                                                                                            ADD
                                                                                              rn
                                                                                              op2
                                                                                              false
                                                                                       | false =>
                                                                                            (case
                                                                                               word_eq
                                                                                                 opc
                                                                                                 (n2w_itself
                                                                                                    ((
                                                                                                     fromString
                                                                                                     "12"
                                                                                                     ),(Tyop ("i4", []))))
                                                                                             of true =>
                                                                                                   ORR
                                                                                                     rn
                                                                                                     op2
                                                                                              | false =>
                                                                                                   (case
                                                                                                      word_eq
                                                                                                        opc
                                                                                                        (n2w_itself
                                                                                                           ((
                                                                                                            fromString
                                                                                                            "13"
                                                                                                            ),(Tyop ("i4", []))))
                                                                                                    of true =>
                                                                                                          ALU_logic
                                                                                                            op2
                                                                                                     | false =>
                                                                                                          (case
                                                                                                             word_eq
                                                                                                               opc
                                                                                                               (n2w_itself
                                                                                                                  ((
                                                                                                                   fromString
                                                                                                                   "14"
                                                                                                                   ),(Tyop ("i4", []))))
                                                                                                           of true =>
                                                                                                                 AND
                                                                                                                   rn
                                                                                                                   (word_1comp
                                                                                                                      op2)
                                                                                                            | false =>
                                                                                                                 ALU_logic
                                                                                                                   (word_1comp
                                                                                                                      op2)))))))))))))))
    
  fun ARITHMETIC opcode =
        (index opcode TWO orelse index opcode ONE)
        andalso
        (not (index opcode (fromString"3"))
         orelse
         not (index opcode TWO))
    
  fun TEST_OR_COMP opcode =
        word_eq (word_bits (fromString"3") TWO opcode)
          (n2w_itself (TWO,(Tyop ("i4", []))))
    
  fun DATA_PROCESSING reg psr C mode ireg =
        let val (I,(opcode,(S,(Rn,(Rd,opnd2))))) = DECODE_DATAP ireg
            val (C_s,op2) = ADDR_MODE1 reg mode C I opnd2
            and pc_reg = INC_PC reg
            val rn =
                REG_READ
                  (if not I andalso index opnd2 (fromString"4")
                     then pc_reg else reg) mode Rn
            val ((N,(Z,(C_alu,V))),res) = ALU opcode rn op2 C
            and tc = TEST_OR_COMP opcode
        in
           regs(if tc then pc_reg else REG_WRITE pc_reg mode Rd res,
           if S
             then CPSR_WRITE psr
                    (if word_eq Rd
                          (n2w_itself
                             ((fromString"15"),(Tyop ("i4", []))))
                        andalso
                        not tc then SPSR_READ psr mode
                       else (if ARITHMETIC opcode
                               then SET_NZCV (N,(Z,(C_alu,V)))
                               else SET_NZC (N,(Z,C_s)))
                            (CPSR_READ psr)) else psr)
        end
    
  fun MRS reg psr mode ireg =
        let val (R,Rd) = DECODE_MRS ireg
            val word = if R then SPSR_READ psr mode else CPSR_READ psr
        in
           regs(REG_WRITE (INC_PC reg) mode Rd word,psr)
        end
    
  fun MSR reg psr mode ireg =
        let val (I,(R,(bit19,(bit16,(Rm,opnd))))) = DECODE_MSR ireg
        in
           if USER mode andalso (R orelse not bit19 andalso bit16)
              orelse
              not bit19 andalso not bit16 then regs(INC_PC reg,psr)
             else let val psrd =
                          if R then SPSR_READ psr mode
                            else CPSR_READ psr
                      and src =
                          if I then pairML.SND (IMMEDIATE false opnd)
                            else REG_READ reg mode Rm
                      val psrd' =
                          word_modify (fn i => fn b =>
                            <= (fromString"28") i
                            andalso
                            (if bit19 then index src i else b)
                            orelse
                            (<= (fromString"8") i
                             andalso
                             (<= i (fromString"27") andalso b)
                             orelse
                             <= i (fromString"7")
                             andalso
                             (if bit16 andalso not (USER mode)
                                then index src i else b))) psrd
                  in
                     regs(INC_PC reg,
                     if R then SPSR_WRITE psr mode psrd'
                       else CPSR_WRITE psr psrd')
                  end
        end
    
  fun ALU_multiply L Sgn A rd rn rs rm =
        let val res =
                word_add
                  (if A
                     then (if L
                             then word_concat_itself (Tyop ("i64", []))
                                    rd rn
                             else w2w_itself (Tyop ("i64", [])) rn)
                     else n2w_itself (ZERO,(Tyop ("i64", []))))
                  (if L andalso Sgn
                     then word_mul (sw2sw_itself (Tyop ("i64", [])) rm)
                            (sw2sw_itself (Tyop ("i64", [])) rs)
                     else word_mul (w2w_itself (Tyop ("i64", [])) rm)
                            (w2w_itself (Tyop ("i64", [])) rs))
            val resHi =
                word_extract_itself (Tyop ("i32", [])) (fromString"63")
                  (fromString"32") res
            and resLo =
                word_extract_itself (Tyop ("i32", [])) (fromString"31")
                  ZERO res
        in
           if L
             then (word_msb
                     res,(word_eq res
                            (n2w_itself
                               (ZERO,(Tyop ("i64", [])))),(resHi,resLo)))
             else (word_msb
                     resLo,(word_eq resLo
                              (n2w_itself
                                 (ZERO,(Tyop ("i32", [])))),(rd,resLo)))
        end
    
  fun MLA_MUL reg psr mode ireg =
        let val (L,(Sgn,(A,(S,(Rd,(Rn,(Rs,Rm))))))) =
                DECODE_MLA_MUL ireg
            val pc_reg = INC_PC reg
            val rd = REG_READ reg mode Rd
            and rn = REG_READ reg mode Rn
            and rs = REG_READ reg mode Rs
            and rm = REG_READ reg mode Rm
            val (N,(Z,(resHi,resLo))) = ALU_multiply L Sgn A rd rn rs rm
        in
           if word_eq Rd
                (n2w_itself ((fromString"15"),(Tyop ("i4", []))))
              orelse
              (word_eq Rd Rm
               orelse
               L
               andalso
               (word_eq Rn
                  (n2w_itself ((fromString"15"),(Tyop ("i4", []))))
                orelse
                (word_eq Rn Rm orelse word_eq Rd Rn)))
             then regs(pc_reg,psr)
             else regs(if L
                         then REG_WRITE (REG_WRITE pc_reg mode Rn resLo)
                                mode Rd resHi
                         else REG_WRITE pc_reg mode Rd resLo,
                  if S
                    then CPSR_WRITE psr (SET_NZ (N,Z) (CPSR_READ psr))
                    else psr)
        end
    
  fun BW_READ B align data =
        let val l =  *  (fromString"8") (w2n align)
        in
           if B then word_bits (+ l (fromString"7")) l data
             else word_ror data l
        end
    
  fun UP_DOWN u = if u then word_add else word_sub
    
  fun ADDR_MODE2 reg mode C Im P U Rn offset =
        let val addr = REG_READ reg mode Rn
            val wb_addr =
                UP_DOWN U addr
                  (if Im
                     then pairML.SND (SHIFT_IMMEDIATE reg mode C offset)
                     else w2w_itself (Tyop ("i32", [])) offset)
        in
           (if P then wb_addr else addr,wb_addr)
        end
    
  fun ==> A B = not A orelse B
    
  fun LDR_STR reg psr C mode isdabort data ireg =
        let val (I,(P,(U,(B,(W,(L,(Rn,(Rd,offset)))))))) =
                DECODE_LDR_STR ireg
            val (addr,wb_addr) = ADDR_MODE2 reg mode C I P U Rn offset
            val pc_reg = INC_PC reg
            val wb_reg =
                if ==> P W then REG_WRITE pc_reg mode Rn wb_addr
                  else pc_reg
        in
           state_out(regs(if ==> L isdabort then wb_reg
                            else REG_WRITE wb_reg mode Rd
                                   (BW_READ B
                                      (word_extract_itself
                                         (Tyop ("i2", [])) ONE ZERO
                                         addr) (HD data)),
                     psr),
           [if L then MemRead(addr)
              else MemWrite(B,addr,REG_READ pc_reg mode Rd)])
        end
    
  fun REGISTER_LIST w =
        let val (q0,b0) = DIVMOD_2EXP ONE (w2n w)
            val (q1,b1) = DIVMOD_2EXP ONE q0
            val (q2,b2) = DIVMOD_2EXP ONE q1
            val (q3,b3) = DIVMOD_2EXP ONE q2
            val (q4,b4) = DIVMOD_2EXP ONE q3
            val (q5,b5) = DIVMOD_2EXP ONE q4
            val (q6,b6) = DIVMOD_2EXP ONE q5
            val (q7,b7) = DIVMOD_2EXP ONE q6
            val (q8,b8) = DIVMOD_2EXP ONE q7
            val (q9,b9) = DIVMOD_2EXP ONE q8
            val (q10,b10) = DIVMOD_2EXP ONE q9
            val (q11,b11) = DIVMOD_2EXP ONE q10
            val (q12,b12) = DIVMOD_2EXP ONE q11
            val (q13,b13) = DIVMOD_2EXP ONE q12
            val (q14,b14) = DIVMOD_2EXP ONE q13
        in
           MAP pairML.SND
             (FILTER pairML.FST
                [(b0 = ONE,n2w_itself (ZERO,(Tyop ("i4", [])))),
                 (b1 = ONE,n2w_itself (ONE,(Tyop ("i4", [])))),
                 (b2 = ONE,n2w_itself (TWO,(Tyop ("i4", [])))),
                 (b3
                  =
                  ONE,n2w_itself ((fromString"3"),(Tyop ("i4", [])))),
                 (b4
                  =
                  ONE,n2w_itself ((fromString"4"),(Tyop ("i4", [])))),
                 (b5
                  =
                  ONE,n2w_itself ((fromString"5"),(Tyop ("i4", [])))),
                 (b6
                  =
                  ONE,n2w_itself ((fromString"6"),(Tyop ("i4", [])))),
                 (b7
                  =
                  ONE,n2w_itself ((fromString"7"),(Tyop ("i4", [])))),
                 (b8
                  =
                  ONE,n2w_itself ((fromString"8"),(Tyop ("i4", [])))),
                 (b9
                  =
                  ONE,n2w_itself ((fromString"9"),(Tyop ("i4", [])))),
                 (b10
                  =
                  ONE,n2w_itself ((fromString"10"),(Tyop ("i4", [])))),
                 (b11
                  =
                  ONE,n2w_itself ((fromString"11"),(Tyop ("i4", [])))),
                 (b12
                  =
                  ONE,n2w_itself ((fromString"12"),(Tyop ("i4", [])))),
                 (b13
                  =
                  ONE,n2w_itself ((fromString"13"),(Tyop ("i4", [])))),
                 (b14
                  =
                  ONE,n2w_itself ((fromString"14"),(Tyop ("i4", [])))),
                 (ODD
                    q14,n2w_itself
                          ((fromString"15"),(Tyop ("i4", []))))])
        end
    
  fun ADDRESS_LIST start n =
        GENLIST (fn i =>
          word_add start
            (word_mul (n2w_itself ((fromString"4"),(Tyop ("i32", []))))
               (n2w_itself (i,(Tyop ("i32", [])))))) n
    
  fun WB_ADDRESS U base len =
        UP_DOWN U base
          (n2w_itself ( *  (fromString"4") len,(Tyop ("i32", []))))
    
  fun FIRST_ADDRESS P U base wb =
        if U
          then (if P
                  then word_add base
                         (n2w_itself
                            ((fromString"4"),(Tyop ("i32", []))))
                  else base)
          else if P then wb
                 else word_add wb
                        (n2w_itself
                           ((fromString"4"),(Tyop ("i32", []))))
    
  fun ADDR_MODE4 P U base list =
        let val rp_list = REGISTER_LIST list
            val len = LENGTH rp_list
            val wb = WB_ADDRESS U base len
            val addr_list = ADDRESS_LIST (FIRST_ADDRESS P U base wb) len
        in
           (rp_list,(addr_list,wb))
        end
    
  fun LDM_LIST reg mode rp_list data =
        FOLDL (fn reg' => fn (rp,rd) => REG_WRITE reg' mode rp rd) reg
          (ZIP (rp_list,data))
    
  fun STM_LIST reg mode bl_list =
        MAP (fn (rp,addr) => MemWrite(false,addr,REG_READ reg mode rp))
          bl_list
    
  fun LDM_STM reg psr mode dabort_t data ireg =
        let val (P,(U,(S,(W,(L,(Rn,list)))))) = DECODE_LDM_STM ireg
            val pc_in_list = index list (fromString"15")
            and rn = REG_READ reg mode Rn
            val (rp_list,(addr_list,rn')) = ADDR_MODE4 P U rn list
            and mode' =
                if S andalso ==> L (not pc_in_list) then usr else mode
            and pc_reg = INC_PC reg
            val wb_reg =
                if W
                   andalso
                   not
                     (word_eq Rn
                        (n2w_itself
                           ((fromString"15"),(Tyop ("i4", [])))))
                  then REG_WRITE pc_reg (if L then mode else mode') Rn
                         rn' else pc_reg
        in
           state_out(if L
                       then regs(let val t =
                                         if optionML.IS_SOME dabort_t
                                           then optionML.THE dabort_t
                                           else LENGTH rp_list
                                     val ldm_reg =
                                         LDM_LIST wb_reg mode'
                                           (FIRSTN t rp_list)
                                           (FIRSTN t data)
                                 in
                                    if optionML.IS_SOME dabort_t
                                       andalso
                                       not
                                         (word_eq Rn
                                            (n2w_itself
                                               ((
                                                fromString
                                                "15"
                                                ),(Tyop ("i4", [])))))
                                      then REG_WRITE ldm_reg mode' Rn
                                             (REG_READ wb_reg mode' Rn)
                                      else ldm_reg
                                 end,
                            if S
                               andalso
                               (pc_in_list
                                andalso
                                not (optionML.IS_SOME dabort_t))
                              then CPSR_WRITE psr (SPSR_READ psr mode)
                              else psr) else regs(wb_reg,psr),
           if L then MAP MemRead addr_list
             else STM_LIST
                    (if word_eq (HD rp_list) Rn then pc_reg else wb_reg)
                    mode' (ZIP (rp_list,addr_list)))
        end
    
  fun SWP reg psr mode isdabort data ireg =
        let val (B,(Rn,(Rd,Rm))) = DECODE_SWP ireg
            val rn = REG_READ reg mode Rn
            and pc_reg = INC_PC reg
            val rm = REG_READ pc_reg mode Rm
        in
           state_out(regs(if isdabort then pc_reg
                            else REG_WRITE pc_reg mode Rd
                                   (BW_READ B
                                      (word_extract_itself
                                         (Tyop ("i2", [])) ONE ZERO rn)
                                      data),
                     psr),
           [MemRead(rn),MemWrite(B,rn,rm)])
        end
    
  fun MRC reg psr mode data ireg =
        let val Rd =
                word_extract_itself (Tyop ("i4", [])) (fromString"15")
                  (fromString"12") ireg
            and pc_reg = INC_PC reg
        in
           if word_eq Rd
                (n2w_itself ((fromString"15"),(Tyop ("i4", []))))
             then regs(pc_reg,
                  CPSR_WRITE psr (SET_NZCV (NZCV data) (CPSR_READ psr)))
             else regs(REG_WRITE pc_reg mode Rd data,psr)
        end
    
  fun MCR_OUT reg mode ireg =
        let val Rn =
                word_extract_itself (Tyop ("i4", [])) (fromString"15")
                  (fromString"12") ireg
        in
           [CPWrite(REG_READ (INC_PC reg) mode Rn)]
        end
    
  fun ADDR_MODE5 reg mode P U Rn offset =
        let val addr = REG_READ reg mode Rn
            val wb_addr =
                UP_DOWN U addr
                  (word_lsl (w2w_itself (Tyop ("i32", [])) offset) TWO)
        in
           (if P then wb_addr else addr,wb_addr)
        end
    
  fun LDC_STC reg psr mode ireg =
        let val (P,(U,(W,(L,(Rn,offset))))) = DECODE_LDC_STC ireg
            val (addr,wb_addr) = ADDR_MODE5 reg mode P U Rn offset
            val pc_reg = INC_PC reg
            val wb_reg =
                if W
                   andalso
                   not
                     (word_eq Rn
                        (n2w_itself
                           ((fromString"15"),(Tyop ("i4", [])))))
                  then REG_WRITE pc_reg mode Rn wb_addr else pc_reg
        in
           state_out(regs(wb_reg,psr),
           [(if L then CPMemRead else CPMemWrite) addr])
        end
    
  fun CONDITION_PASSED2 (N,(Z,(C,V))) cond =
        case cond
         of EQ => Z
          | CS => C
          | MI => N
          | VS => V
          | HI => C andalso not Z
          | GE => N = V
          | GT => not Z andalso (N = V)
          | AL => true
          | NE => not Z
          | CC => not C
          | PL => not N
          | VC => not V
          | LS => not C orelse Z
          | LT => not (N = V)
          | LE => Z orelse not (N = V)
          | NV => false
    
  fun CONDITION_PASSED flags ireg =
        let val pass =
                CONDITION_PASSED2 flags
                  (num2condition
                     (w2n
                        (word_bits (fromString"31") (fromString"29")
                           ireg)))
        in
           if index ireg (fromString"28") then not pass else pass
        end
    
  fun RUN_ARM state dabt data cp_abort =
        let val ireg = arm_state_ireg state
            and reg = arm_state_registers state
            and psr = arm_state_psrs state
        in
           if not (arm_state_exception state = software)
             then EXCEPTION reg psr (arm_state_exception state)
             else let val (nzcv,(i,(f,m))) = DECODE_PSR (CPSR_READ psr)
                  in
                     if not (CONDITION_PASSED nzcv ireg)
                       then regs(INC_PC reg,psr)
                       else let val ic = DECODE_INST ireg
                                and mode = DECODE_MODE m
                            in
                               if (ic = data_proc)
                                  orelse
                                  (ic = reg_shift)
                                 then DATA_PROCESSING reg psr
                                        (CARRY nzcv) mode ireg
                                 else if ic = mla_mul
                                        then MLA_MUL reg psr mode ireg
                                        else if ic = br
                                               then BRANCH reg psr mode
                                                      ireg
                                               else if (ic = ldr)
                                                       orelse
                                                       (ic = str)
                                                      then state_out_state
                                                             (LDR_STR
                                                                reg psr
                                                                (CARRY
                                                                   nzcv)
                                                                mode
                                                                (optionML.IS_SOME
                                                                   dabt)
                                                                data
                                                                ireg)
                                                      else if (ic = ldm)
                                                              orelse
                                                              (ic = stm)
                                                             then state_out_state
                                                                    (LDM_STM
                                                                       reg
                                                                       psr
                                                                       mode
                                                                       dabt
                                                                       data
                                                                       ireg)
                                                             else if ic
                                                                     =
                                                                     swp
                                                                    then state_out_state
                                                                           (SWP
                                                                              reg
                                                                              psr
                                                                              mode
                                                                              (optionML.IS_SOME
                                                                                 dabt)
                                                                              (HD
                                                                                 data)
                                                                              ireg)
                                                                    else if ic
                                                                            =
                                                                            swi_ex
                                                                           then EXCEPTION
                                                                                  reg
                                                                                  psr
                                                                                  software
                                                                           else if ic
                                                                                   =
                                                                                   mrs_msr
                                                                                  then (if index
                                                                                             ireg
                                                                                             (
                                                                                             fromString
                                                                                             "21"
                                                                                             )
                                                                                          then MSR
                                                                                                 reg
                                                                                                 psr
                                                                                                 mode
                                                                                                 ireg
                                                                                          else MRS
                                                                                                 reg
                                                                                                 psr
                                                                                                 mode
                                                                                                 ireg)
                                                                                  else if cp_abort
                                                                                         then regs(reg,
                                                                                              psr)
                                                                                         else if ic
                                                                                                 =
                                                                                                 mrc
                                                                                                then MRC
                                                                                                       reg
                                                                                                       psr
                                                                                                       mode
                                                                                                       (ELL
                                                                                                          ONE
                                                                                                          data)
                                                                                                       ireg
                                                                                                else if (ic
                                                                                                         =
                                                                                                         ldc)
                                                                                                        orelse
                                                                                                        (ic
                                                                                                         =
                                                                                                         stc)
                                                                                                       then state_out_state
                                                                                                              (LDC_STC
                                                                                                                 reg
                                                                                                                 psr
                                                                                                                 mode
                                                                                                                 ireg)
                                                                                                       else if (ic
                                                                                                                =
                                                                                                                cdp_und)
                                                                                                               orelse
                                                                                                               (ic
                                                                                                                =
                                                                                                                mcr)
                                                                                                              then regs(INC_PC
                                                                                                                          reg,
                                                                                                                   psr)
                                                                                                              else regs(reg,
                                                                                                                   psr)
                            end
                  end
        end
    
  fun IS_Reset (optionML.SOME(Reset(x))) = true
    | IS_Reset (optionML.SOME(Irq)) = false
    | IS_Reset (optionML.SOME(Fiq)) = false
    | IS_Reset (optionML.SOME(Dabort(v3))) = false
    | IS_Reset (optionML.SOME(Prefetch)) = false
    | IS_Reset (optionML.SOME(Undef)) = false
    | IS_Reset optionML.NONE = false
    
  fun PROJ_Dabort (optionML.SOME(Dabort(x))) = optionML.SOME(x)
    | PROJ_Dabort (optionML.SOME(Irq)) = optionML.NONE
    | PROJ_Dabort (optionML.SOME(Fiq)) = optionML.NONE
    | PROJ_Dabort (optionML.SOME(Prefetch)) = optionML.NONE
    | PROJ_Dabort (optionML.SOME(Undef)) = optionML.NONE
    | PROJ_Dabort (optionML.SOME(Reset(v2))) = optionML.NONE
    | PROJ_Dabort optionML.NONE = optionML.NONE
    
  fun PROJ_Reset (optionML.SOME(Reset(x))) = x
    
  fun interrupt2exception state (i',f') irpt =
        let val ireg = arm_state_ireg state
            and reg = arm_state_registers state
            and psr = arm_state_psrs state
            val (flags,(i,(f,m))) = DECODE_PSR (CPSR_READ psr)
            val pass =
                (arm_state_exception state = software)
                andalso
                CONDITION_PASSED flags ireg
            and ic = DECODE_INST ireg
            val old_flags = pass andalso (ic = mrs_msr)
        in
           case irpt
            of optionML.NONE => software
             | optionML.SOME(Reset(x)) => reset
             | optionML.SOME(Undef) =>
                  if pass
                     andalso
                     IN ic
                       (INSERT
                          (cdp_und,INSERT
                                     (mrc,INSERT
                                            (mcr,INSERT
                                                   (stc,INSERT
                                                          (ldc,EMPTY))))))
                    then undefined else software
             | optionML.SOME(Prefetch) => pabort
             | optionML.SOME(Dabort(t)) => dabort
             | optionML.SOME(Fiq) =>
                  if (if old_flags then f else f') then software
                    else fast
             | optionML.SOME(Irq) =>
                  if (if old_flags then i else i') then software
                    else interrupt
        end
    
  fun PROJ_IF_FLAGS psr =
        let val (flags,(i,(f,m))) = DECODE_PSR (CPSR_READ psr)
        in
           (i,f)
        end
    
  fun NEXT_ARM state inp =
        let val r =
                if IS_Reset (arm_input_interrupt inp)
                  then PROJ_Reset (arm_input_interrupt inp)
                  else RUN_ARM state
                         (PROJ_Dabort (arm_input_interrupt inp))
                         (arm_input_data inp) (arm_input_no_cp inp)
        in
           arm_state(regs_reg r,
           regs_psr r,
           arm_input_ireg inp,
           interrupt2exception state (PROJ_IF_FLAGS (regs_psr r))
             (arm_input_interrupt inp))
        end
    
  fun OUT_ARM state =
        let val ireg = arm_state_ireg state
            and reg = arm_state_registers state
            and psr = arm_state_psrs state
            val (nzcv,(i,(f,m))) = DECODE_PSR (CPSR_READ psr)
        in
           if (arm_state_exception state = software)
              andalso
              CONDITION_PASSED nzcv ireg
             then let val ic = DECODE_INST ireg
                      and mode = DECODE_MODE m
                  in
                     if (ic = ldr) orelse (ic = str)
                       then let val
                                    (I,(P,(U,(B,(W,(L,(Rn,(Rd,offset))))))))
                                    = DECODE_LDR_STR ireg
                                val (addr,wb_addr) =
                                    ADDR_MODE2 reg mode (CARRY nzcv) I P
                                      U Rn offset
                                val pc_reg = INC_PC reg
                            in
                               [if L then MemRead(addr)
                                  else MemWrite(B,
                                       addr,
                                       REG_READ pc_reg mode Rd)]
                            end
                       else if (ic = ldm) orelse (ic = stm)
                              then let val (P,(U,(S,(W,(L,(Rn,list))))))
                                           = DECODE_LDM_STM ireg
                                       val pc_in_list =
                                           index list (fromString"15")
                                       and rn = REG_READ reg mode Rn
                                       val (rp_list,(addr_list,rn')) =
                                           ADDR_MODE4 P U rn list
                                       and mode' =
                                           if S
                                              andalso
                                              ==> L (not pc_in_list)
                                             then usr else mode
                                       and pc_reg = INC_PC reg
                                       val wb_reg =
                                           if W
                                              andalso
                                              not
                                                (word_eq Rn
                                                   (n2w_itself
                                                      ((
                                                       fromString
                                                       "15"
                                                       ),(Tyop ("i4", [])))))
                                             then REG_WRITE pc_reg
                                                    (if L then mode
                                                       else mode') Rn
                                                    rn' else pc_reg
                                   in
                                      if L then MAP MemRead addr_list
                                        else STM_LIST
                                               (if word_eq (HD rp_list)
                                                     Rn then pc_reg
                                                  else wb_reg) mode'
                                               (ZIP (rp_list,addr_list))
                                   end
                              else if ic = swp
                                     then let val (B,(Rn,(Rd,Rm))) =
                                                  DECODE_SWP ireg
                                              val rn =
                                                  REG_READ reg mode Rn
                                              and pc_reg = INC_PC reg
                                              val rm =
                                                  REG_READ pc_reg mode
                                                    Rm
                                          in
                                             [MemRead(rn),
                                              MemWrite(B,rn,rm)]
                                          end
                                     else if (ic = ldc)
                                             orelse
                                             (ic = stc)
                                            then state_out_out
                                                   (LDC_STC reg psr mode
                                                      ireg)
                                            else if ic = mcr
                                                   then MCR_OUT reg mode
                                                          ireg else []
                  end else []
        end
    
  fun ADDR30 addr =
        word_extract_itself (Tyop ("i30", [])) (fromString"31") TWO addr
    
  fun SET_BYTE oareg b w =
        word_modify (fn i => fn x =>
          < i (fromString"8")
          andalso
          (if word_eq oareg (n2w_itself (ZERO,(Tyop ("i2", []))))
             then index b i else x)
          orelse
          ((<= (fromString"8") i andalso < i (fromString"16"))
           andalso
           (if word_eq oareg (n2w_itself (ONE,(Tyop ("i2", []))))
              then index b (- i (fromString"8")) else x)
           orelse
           ((<= (fromString"16") i andalso < i (fromString"24"))
            andalso
            (if word_eq oareg (n2w_itself (TWO,(Tyop ("i2", []))))
               then index b (- i (fromString"16")) else x)
            orelse
            (<= (fromString"24") i andalso < i (fromString"32"))
            andalso
            (if word_eq oareg
                  (n2w_itself ((fromString"3"),(Tyop ("i2", []))))
               then index b (- i (fromString"24")) else x)))) w
    
  fun fromHexNum s n =
        wordsML.fromNum(numML.fromHexString n, fcpML.Tyop (s, []));

  val fromNum32 = (fromHexNum "i32"): string -> word32;

  fun MEM_READ(m,a) = Redblackmap.find(m, a)
                       handle NotFound => fromNum32 "E6000010";
    
  fun MEM_WRITE_BYTE mem addr word =
        let val addr30 = ADDR30 addr
        in
           Redblackmap.insert(mem, (addr30: word30),
             SET_BYTE
                (word_extract_itself (Tyop ("i2", [])) ONE ZERO addr)
                (word_extract_itself (Tyop ("i8", [])) (fromString"7")
                   ZERO word) (MEM_READ(mem,addr30)))
        end

  fun MEM_WRITE_WORD (mem:mem) addr word =
        Redblackmap.insert(mem,ADDR30 addr,word)

  fun MEM_WRITE b m a =
        (:= (mem_updates, ADDR30 a :: !mem_updates);
          if b then MEM_WRITE_BYTE m a else MEM_WRITE_WORD m a)

  fun MEM_WRITE_BLOCK m (a: word30) [] = m
    | MEM_WRITE_BLOCK m a (d::l) =
       (:= (mem_updates, ADDR30 a :: !mem_updates);
        MEM_WRITE_BLOCK (Redblackmap.insert(m, a, (d: word32)))
          (word_add a (n2w_itself (ONE,(Tyop ("i30", []))))) l)
    
  fun word_compare(v, w) =
    let val m = w2n v and n = w2n w in
      if m = n then
        EQUAL
      else
        if < m n then LESS else GREATER
    end

  val empty_memory = (Redblackmap.mkDict word_compare):mem

  fun LOAD_STORE data mem [] = (mem,data)
    | LOAD_STORE data mem (r::rs) =
        (case r
         of MemRead(addr) =>
               LOAD_STORE (SNOC (MEM_READ (mem,ADDR30 addr)) data) mem
                 rs
          | MemWrite(b,addr',word) =>
               LOAD_STORE data (MEM_WRITE b mem addr' word) rs
          | CPMemRead(v11) => LOAD_STORE data mem rs
          | CPMemWrite(v12) => LOAD_STORE data mem rs
          | CPWrite(v13) => LOAD_STORE data mem rs)
    
  val TRANSFERS = LOAD_STORE []
    
  fun NEXT_ARM_MEM state =
        let val ireg =
                MEM_READ
                  (arm_mem_state_memory
                     state,ADDR30
                             (FETCH_PC (arm_mem_state_registers state)))
            val s =
                arm_state(arm_mem_state_registers state,
                arm_mem_state_psrs state,
                ireg,
                if arm_mem_state_undefined state then undefined
                  else software)
            val (mem,data) =
                TRANSFERS (arm_mem_state_memory state) (OUT_ARM s)
            and flags =
                pairML.FST
                  (DECODE_PSR (CPSR_READ (arm_mem_state_psrs state)))
            val r = RUN_ARM s optionML.NONE data true
        in
           arm_mem_state(regs_reg r,
           regs_psr r,
           mem,
           not (arm_mem_state_undefined state)
           andalso
           (CONDITION_PASSED flags ireg
            andalso
            IN (DECODE_INST ireg)
              (INSERT
                 (cdp_und,INSERT
                            (mrc,INSERT
                                   (mcr,INSERT
                                          (stc,INSERT (ldc,EMPTY))))))))
        end
    
  val empty_registers = fn n => n2w_itself (ZERO,(Tyop ("i32", [])))
    
end
