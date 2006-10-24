signature armML = 
sig
  type 'a word = 'a wordsML.word
  type num = numML.num
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
  val register_size : register -> num
  datatype psr
       = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und
  val psr_size : psr -> num
  datatype mode = usr | fiq | irq | svc | abt | und | safe
  val mode_size : mode -> num
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
  val condition_size : condition -> num
  eqtype exceptions
  val exceptions_size : exceptions -> num
  eqtype iclass
  val iclass_size : iclass -> num
  type ('a,'b) state_inp
  type ('a,'b) state_out
  type word2 = wordsML.word2
  type word4 = wordsML.word4
  type word5 = wordsML.word5
  type word8 = wordsML.word8
  type word12 = wordsML.word12
  type word16 = wordsML.word16
  type word24 = wordsML.word24
  type word30 = wordsML.word30
  type word32 = wordsML.word32
  type registers = register->word32
  type psrs = psr->word32
  type mem = (word30, word32) Redblackmap.dict
  datatype
  arm_state = arm_state of (registers) * (psrs) * word32 * exceptions
  val arm_state_exception : arm_state -> exceptions
  val arm_state_ireg : arm_state -> word32
  val arm_state_psrs : arm_state -> psrs
  val arm_state_registers : arm_state -> registers
  val arm_state_exception_fupd
     : (exceptions -> exceptions) -> arm_state -> arm_state
  val arm_state_ireg_fupd : (word32 -> word32) -> arm_state -> arm_state
  val arm_state_psrs_fupd : (psrs -> psrs) -> arm_state -> arm_state
  val arm_state_registers_fupd
     : (registers -> registers) -> arm_state -> arm_state
  val arm_state_size : arm_state -> num
  datatype
  arm_mem_state = arm_mem_state of (registers) * (psrs) * (mem) * bool
  val arm_mem_state_undefined : arm_mem_state -> bool
  val arm_mem_state_memory : arm_mem_state -> mem
  val arm_mem_state_psrs : arm_mem_state -> psrs
  val arm_mem_state_registers : arm_mem_state -> registers
  val arm_mem_state_undefined_fupd
     : (bool -> bool) -> arm_mem_state -> arm_mem_state
  val arm_mem_state_memory_fupd
     : (mem -> mem) -> arm_mem_state -> arm_mem_state
  val arm_mem_state_psrs_fupd
     : (psrs -> psrs) -> arm_mem_state -> arm_mem_state
  val arm_mem_state_registers_fupd
     : (registers -> registers) -> arm_mem_state -> arm_mem_state
  val arm_mem_state_size : arm_mem_state -> num
  datatype regs = regs of (registers) * (psrs)
  val regs_psr : regs -> psrs
  val regs_reg : regs -> registers
  val regs_psr_fupd : (psrs -> psrs) -> regs -> regs
  val regs_reg_fupd : (registers -> registers) -> regs -> regs
  val regs_size : regs -> num
  datatype interrupt
       = Reset of regs | Undef | Prefetch | Dabort of num | Fiq | Irq
  val interrupt_size : interrupt -> num
  datatype
  arm_input = arm_input of word32 * word32 list * interrupt option *
                           bool
  val arm_input_no_cp : arm_input -> bool
  val arm_input_interrupt : arm_input -> interrupt option
  val arm_input_data : arm_input -> word32 list
  val arm_input_ireg : arm_input -> word32
  val arm_input_no_cp_fupd : (bool -> bool) -> arm_input -> arm_input
  val arm_input_interrupt_fupd
     : (interrupt option -> interrupt option) -> arm_input -> arm_input
  val arm_input_data_fupd
     : (word32 list -> word32 list) -> arm_input -> arm_input
  val arm_input_ireg_fupd : (word32 -> word32) -> arm_input -> arm_input
  val arm_input_size : arm_input -> num
  datatype memop
       = MemRead of word32
       | MemWrite of bool * word32 * word32
       | CPMemRead of word32
       | CPMemWrite of word32
       | CPWrite of word32
  val memop_size : memop -> num
  val DECODE_PSR
     : word32 ->
       (bool * (bool * (bool * bool))) * (bool * (bool * word5))
  val DECODE_BRANCH : word32 -> bool * word24
  val DECODE_DATAP
     : word32 -> bool * (word4 * (bool * (word4 * (word4 * word12))))
  val DECODE_MRS : word32 -> bool * word4
  val DECODE_MSR
     : word32 -> bool * (bool * (bool * (bool * (word4 * word12))))
  val DECODE_LDR_STR
     : word32 ->
       bool *
       (bool *
        (bool * (bool * (bool * (bool * (word4 * (word4 * word12)))))))
  val DECODE_MLA_MUL
     : word32 ->
       bool *
       (bool * (bool * (bool * (word4 * (word4 * (word4 * word4))))))
  val DECODE_LDM_STM
     : word32 ->
       bool * (bool * (bool * (bool * (bool * (word4 * word16)))))
  val DECODE_SWP : word32 -> bool * (word4 * (word4 * word4))
  val DECODE_LDC_STC
     : word32 -> bool * (bool * (bool * (bool * (word4 * word8))))
  val DECODE_INST : word32 -> iclass
  val :- : ''a -> 'b -> (''a -> 'b) -> ''a -> 'b
  val ::- : 'a word -> 'b list -> ('a word -> 'b) -> 'a word -> 'b
  val USER : mode -> bool
  val mode_reg2num : mode -> word4 -> num
  val state_out_state : ('a, 'b) state_out -> 'a
  val state_out_out : ('a, 'b) state_out -> 'b
  val exceptions2num : exceptions -> num
  val register2num : register -> num
  val num2register : num -> register
  val num2condition : num -> condition
  val REG_READ : registers -> mode -> word4 -> word32
  val REG_WRITE : registers -> mode -> word4 -> word32 -> registers
  val INC_PC : registers -> registers
  val FETCH_PC : registers -> word32
  val SET_NZCV : bool * (bool * (bool * bool)) -> word32 -> word32
  val SET_NZC : bool * (bool * bool) -> word32 -> word32
  val SET_NZ : bool * bool -> word32 -> word32
  val mode_num : mode -> word5
  val SET_IFMODE : bool -> bool -> mode -> word32 -> word32
  val DECODE_MODE : word5 -> mode
  val NZCV : word32 -> bool * (bool * (bool * bool))
  val CARRY : 'b * ('c * ('a * 'd)) -> 'a
  val mode2psr : mode -> psr
  val SPSR_READ : psrs -> mode -> word32
  val CPSR_READ : psrs -> word32
  val CPSR_WRITE : psrs -> word32 -> psrs
  val SPSR_WRITE : psrs -> mode -> word32 -> psrs
  val exception2mode : exceptions -> mode
  val EXCEPTION : registers -> psrs -> exceptions -> regs
  val BRANCH : registers -> psrs -> mode -> word32 -> regs
  val LSL : word32 -> word8 -> bool -> bool * word32
  val LSR : word32 -> word8 -> bool -> bool * word32
  val ASR : word32 -> word8 -> bool -> bool * word32
  val ROR : word32 -> word8 -> bool -> bool * word32
  val IMMEDIATE : bool -> word12 -> bool * word32
  val SHIFT_IMMEDIATE2
     : word8 -> word2 -> word32 -> bool -> bool * word32
  val SHIFT_REGISTER2
     : word8 -> word2 -> word32 -> bool -> bool * word32
  val SHIFT_IMMEDIATE
     : registers -> mode -> bool -> word12 -> bool * word32
  val SHIFT_REGISTER
     : registers -> mode -> bool -> word12 -> bool * word32
  val ADDR_MODE1
     : registers -> mode -> bool -> bool -> word12 -> bool * word32
  val ALU_arith
     : (num -> num -> num) ->
       word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ALU_arith_neg
     : (num -> num -> num) ->
       word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ALU_logic : word32 -> (bool * (bool * (bool * bool))) * word32
  val SUB
     : word32 ->
       word32 -> bool -> (bool * (bool * (bool * bool))) * word32
  val ADD
     : word32 ->
       word32 -> bool -> (bool * (bool * (bool * bool))) * word32
  val AND : word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val EOR : word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ORR : word32 -> word32 -> (bool * (bool * (bool * bool))) * word32
  val ALU
     : word4 ->
       word32 ->
       word32 -> bool -> (bool * (bool * (bool * bool))) * word32
  val ARITHMETIC : word4 -> bool
  val TEST_OR_COMP : word4 -> bool
  val DATA_PROCESSING
     : registers -> psrs -> bool -> mode -> word32 -> regs
  val MRS : registers -> psrs -> mode -> word32 -> regs
  val MSR : registers -> psrs -> mode -> word32 -> regs
  val ALU_multiply
     : bool ->
       bool ->
       bool ->
       word32 ->
       'a word ->
       'b word -> 'c word -> bool * (bool * (word32 * word32))
  val MLA_MUL : registers -> psrs -> mode -> word32 -> regs
  val BW_READ : bool -> word2 -> word32 -> word32
  val UP_DOWN : bool -> 'a word -> 'a word -> 'a word
  val ADDR_MODE2
     : registers ->
       mode ->
       bool ->
       bool -> bool -> bool -> word4 -> word12 -> word32 * word32
  val ==> : bool -> bool -> bool
  val LDR_STR
     : registers ->
       psrs ->
       bool ->
       mode ->
       bool -> word32 list -> word32 -> (regs, memop list) state_out
  val REGISTER_LIST : word16 -> word4 list
  val ADDRESS_LIST : word32 -> num -> word32 list
  val WB_ADDRESS : bool -> word32 -> num -> word32
  val FIRST_ADDRESS : bool -> bool -> word32 -> word32 -> word32
  val ADDR_MODE4
     : bool ->
       bool -> word32 -> word16 -> word4 list * (word32 list * word32)
  val LDM_LIST
     : registers -> mode -> word4 list -> word32 list -> registers
  val STM_LIST
     : registers -> mode -> (word4 * word32) list -> memop list
  val LDM_STM
     : registers ->
       psrs ->
       mode ->
       num option ->
       word32 list -> word32 -> (regs, memop list) state_out
  val SWP
     : registers ->
       psrs ->
       mode -> bool -> word32 -> word32 -> (regs, memop list) state_out
  val MRC : registers -> psrs -> mode -> word32 -> word32 -> regs
  val MCR_OUT : registers -> mode -> word32 -> memop list
  val ADDR_MODE5
     : registers ->
       mode -> bool -> bool -> word4 -> word8 -> word32 * word32
  val LDC_STC
     : registers ->
       psrs -> mode -> word32 -> (regs, memop list) state_out
  val CONDITION_PASSED2
     : bool * (bool * (bool * bool)) -> condition -> bool
  val CONDITION_PASSED : bool * (bool * (bool * bool)) -> word32 -> bool
  val RUN_ARM : arm_state -> num option -> word32 list -> bool -> regs
  val IS_Reset : interrupt option -> bool
  val PROJ_Dabort : interrupt option -> num option
  val PROJ_Reset : interrupt option -> regs
  val interrupt2exception
     : arm_state -> bool * bool -> interrupt option -> exceptions
  val PROJ_IF_FLAGS : psrs -> bool * bool
  val NEXT_ARM : arm_state -> arm_input -> arm_state
  val OUT_ARM : arm_state -> memop list
  val ADDR30 : word32 -> word30
  val SET_BYTE : word2 -> word8 -> word32 -> word32
  val MEM_READ : mem * word30 -> word32
  val MEM_WRITE_BYTE : mem -> word32 -> word32 -> mem
  val MEM_WRITE_WORD : mem -> word32 -> word32 -> mem
  val MEM_WRITE : bool -> mem -> word32 -> word32 -> mem
  val MEM_WRITE_BLOCK : mem -> word30 -> word32 list -> mem
  val empty_memory : mem
  val LOAD_STORE : word32 list -> mem -> memop list -> mem * word32 list
  val TRANSFERS : mem -> memop list -> mem * word32 list
  val NEXT_ARM_MEM : arm_mem_state -> arm_mem_state
  val empty_registers : registers
end
