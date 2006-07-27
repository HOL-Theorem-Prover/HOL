signature armML = 
sig
  type ('a, 'b) cart = ('a, 'b) wordsML.cart
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
  datatype psrs
       = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und
  val psrs_size : psrs -> num
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
  eqtype i2
  eqtype i4
  eqtype i5
  eqtype i8
  eqtype i12
  eqtype i16
  eqtype i24
  eqtype i30
  eqtype i32
  datatype state_arm
       = ARM of (register -> (bool, i32) cart) *
                (psrs -> (bool, i32) cart)
  val state_arm_size : state_arm -> num
  datatype state_arm_ex
       = ARM_EX of state_arm * (bool, i32) cart * exceptions
  val state_arm_ex_size : state_arm_ex -> num
  datatype memop
       = MemRead of (bool, i32) cart
       | MemWrite of bool * (bool, i32) cart * (bool, i32) cart
       | CPMemRead of bool * (bool, i32) cart
       | CPMemWrite of bool * (bool, i32) cart
       | CPWrite of (bool, i32) cart
  val memop_size : memop -> num
  type interrupts
  datatype
  state_arme = state_arme of
    (register -> (bool, i32) cart) *
    (psrs -> (bool, i32) cart) *
    ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict *
    bool
  val state_arme_undefined : state_arme -> bool
  val state_arme_memory
     : state_arme -> ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict
  val state_arme_psrs : state_arme -> psrs -> (bool, i32) cart
  val state_arme_registers : state_arme -> register -> (bool, i32) cart
  val state_arme_undefined_fupd
     : (bool -> bool) -> state_arme -> state_arme
  val state_arme_memory_fupd
     : (((bool, i30) cart, (bool, i32) cart) Redblackmap.dict ->
        ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict) ->
       state_arme -> state_arme
  val state_arme_psrs_fupd
     : ((psrs -> (bool, i32) cart) -> psrs -> (bool, i32) cart) ->
       state_arme -> state_arme
  val state_arme_registers_fupd
     : ((register -> (bool, i32) cart) -> register -> (bool, i32) cart)
       -> state_arme -> state_arme
  val state_arme_size : state_arme -> num
  val DECODE_PSR
     : (bool, i32) cart ->
       (bool * (bool * (bool * bool))) *
       (bool * (bool * (bool, i5) cart))
  val DECODE_BRANCH : (bool, i32) cart -> bool * (bool, i24) cart
  val DECODE_DATAP
     : (bool, i32) cart ->
       bool *
       ((bool, i4) cart *
        (bool *
         ((bool, i4) cart * ((bool, i4) cart * (bool, i12) cart))))
  val DECODE_MRS : (bool, i32) cart -> bool * (bool, i4) cart
  val DECODE_MSR
     : (bool, i32) cart ->
       bool *
       (bool * (bool * (bool * ((bool, i4) cart * (bool, i12) cart))))
  val DECODE_LDR_STR
     : (bool, i32) cart ->
       bool *
       (bool *
        (bool *
         (bool *
          (bool *
           (bool *
            ((bool, i4) cart *
             ((bool, i4) cart * (bool, i12) cart)))))))
  val DECODE_MLA_MUL
     : (bool, i32) cart ->
       bool *
       (bool *
        (bool *
         (bool *
          ((bool, i4) cart *
           ((bool, i4) cart * ((bool, i4) cart * (bool, i4) cart))))))
  val DECODE_LDM_STM
     : (bool, i32) cart ->
       bool *
       (bool *
        (bool * (bool * (bool * ((bool, i4) cart * (bool, i16) cart)))))
  val DECODE_SWP
     : (bool, i32) cart ->
       bool * ((bool, i4) cart * ((bool, i4) cart * (bool, i4) cart))
  val DECODE_LDC_STC
     : (bool, i32) cart ->
       bool *
       (bool * (bool * (bool * ((bool, i4) cart * (bool, i8) cart))))
  val DECODE_INST : (bool, i32) cart -> iclass
  val :- : ''a -> 'b -> (''a -> 'b) -> ''a -> 'b
  val ::-
     : (bool, 'a) cart ->
       'b list -> ((bool, 'a) cart -> 'b) -> (bool, 'a) cart -> 'b
  val USER : mode -> bool
  val mode_reg2num : mode -> (bool, i4) cart -> num
  val state_out_state : ('a, 'b) state_out -> 'a
  val state_out_out : ('a, 'b) state_out -> 'b
  val num2register : num -> register
  val num2condition : num -> condition
  val exceptions2num : exceptions -> num
  val register2num : register -> num
  val REG_READ
     : (register -> (bool, i32) cart) ->
       mode -> (bool, i4) cart -> (bool, i32) cart
  val REG_WRITE
     : (register -> (bool, i32) cart) ->
       mode ->
       (bool, i4) cart ->
       (bool, i32) cart -> register -> (bool, i32) cart
  val INC_PC
     : (register -> (bool, i32) cart) -> register -> (bool, i32) cart
  val FETCH_PC : (register -> (bool, i32) cart) -> (bool, i32) cart
  val SET_NZCV
     : bool * (bool * (bool * bool)) ->
       (bool, i32) cart -> (bool, i32) cart
  val SET_NZC
     : bool * (bool * bool) -> (bool, i32) cart -> (bool, i32) cart
  val SET_NZ : bool * bool -> (bool, i32) cart -> (bool, i32) cart
  val mode_num : mode -> (bool, i5) cart
  val SET_IFMODE
     : bool -> bool -> mode -> (bool, i32) cart -> (bool, i32) cart
  val DECODE_MODE : (bool, i5) cart -> mode
  val NZCV : (bool, i32) cart -> bool * (bool * (bool * bool))
  val CARRY : 'b * ('c * ('a * 'd)) -> 'a
  val mode2psr : mode -> psrs
  val SPSR_READ : (psrs -> (bool, i32) cart) -> mode -> (bool, i32) cart
  val CPSR_READ : (psrs -> (bool, i32) cart) -> (bool, i32) cart
  val CPSR_WRITE
     : (psrs -> (bool, i32) cart) ->
       (bool, i32) cart -> psrs -> (bool, i32) cart
  val SPSR_WRITE
     : (psrs -> (bool, i32) cart) ->
       mode -> (bool, i32) cart -> psrs -> (bool, i32) cart
  val exceptions2mode : exceptions -> mode
  val EXCEPTION : state_arm -> exceptions -> state_arm
  val BRANCH : state_arm -> mode -> (bool, i32) cart -> state_arm
  val LSL
     : (bool, i32) cart ->
       (bool, i8) cart -> bool -> bool * (bool, i32) cart
  val LSR
     : (bool, i32) cart ->
       (bool, i8) cart -> bool -> bool * (bool, i32) cart
  val ASR
     : (bool, i32) cart ->
       (bool, i8) cart -> bool -> bool * (bool, i32) cart
  val ROR
     : (bool, i32) cart ->
       (bool, i8) cart -> bool -> bool * (bool, i32) cart
  val IMMEDIATE : bool -> (bool, i12) cart -> bool * (bool, i32) cart
  val SHIFT_IMMEDIATE2
     : (bool, i8) cart ->
       (bool, i2) cart ->
       (bool, i32) cart -> bool -> bool * (bool, i32) cart
  val SHIFT_REGISTER2
     : (bool, i8) cart ->
       (bool, i2) cart ->
       (bool, i32) cart -> bool -> bool * (bool, i32) cart
  val SHIFT_IMMEDIATE
     : (register -> (bool, i32) cart) ->
       mode -> bool -> (bool, i12) cart -> bool * (bool, i32) cart
  val SHIFT_REGISTER
     : (register -> (bool, i32) cart) ->
       mode -> bool -> (bool, i12) cart -> bool * (bool, i32) cart
  val ADDR_MODE1
     : (register -> (bool, i32) cart) ->
       mode ->
       bool -> bool -> (bool, i12) cart -> bool * (bool, i32) cart
  val ALU_arith
     : (num -> num -> num) ->
       (bool, i32) cart ->
       (bool, i32) cart ->
       (bool * (bool * (bool * bool))) * (bool, i32) cart
  val ALU_arith_neg
     : (num -> num -> num) ->
       (bool, i32) cart ->
       (bool, i32) cart ->
       (bool * (bool * (bool * bool))) * (bool, i32) cart
  val ALU_logic
     : (bool, i32) cart ->
       (bool * (bool * (bool * bool))) * (bool, i32) cart
  val SUB
     : (bool, i32) cart ->
       (bool, i32) cart ->
       bool -> (bool * (bool * (bool * bool))) * (bool, i32) cart
  val ADD
     : (bool, i32) cart ->
       (bool, i32) cart ->
       bool -> (bool * (bool * (bool * bool))) * (bool, i32) cart
  val AND
     : (bool, i32) cart ->
       (bool, i32) cart ->
       (bool * (bool * (bool * bool))) * (bool, i32) cart
  val EOR
     : (bool, i32) cart ->
       (bool, i32) cart ->
       (bool * (bool * (bool * bool))) * (bool, i32) cart
  val ORR
     : (bool, i32) cart ->
       (bool, i32) cart ->
       (bool * (bool * (bool * bool))) * (bool, i32) cart
  val ALU
     : (bool, i4) cart ->
       (bool, i32) cart ->
       (bool, i32) cart ->
       bool -> (bool * (bool * (bool * bool))) * (bool, i32) cart
  val ARITHMETIC : (bool, i4) cart -> bool
  val TEST_OR_COMP : (bool, i4) cart -> bool
  val DATA_PROCESSING
     : state_arm -> bool -> mode -> (bool, i32) cart -> state_arm
  val MRS : state_arm -> mode -> (bool, i32) cart -> state_arm
  val MSR : state_arm -> mode -> (bool, i32) cart -> state_arm
  val ALU_multiply
     : bool ->
       bool ->
       bool ->
       (bool, i32) cart ->
       (bool, 'a) cart ->
       (bool, 'b) cart ->
       (bool, 'c) cart ->
       bool * (bool * ((bool, i32) cart * (bool, i32) cart))
  val MLA_MUL : state_arm -> mode -> (bool, i32) cart -> state_arm
  val BW_READ
     : bool -> (bool, i2) cart -> (bool, i32) cart -> (bool, i32) cart
  val UP_DOWN
     : bool -> (bool, 'a) cart -> (bool, 'a) cart -> (bool, 'a) cart
  val ADDR_MODE2
     : (register -> (bool, i32) cart) ->
       mode ->
       bool ->
       bool ->
       bool ->
       bool ->
       (bool, i4) cart ->
       (bool, i12) cart -> (bool, i32) cart * (bool, i32) cart
  val ==> : bool -> bool -> bool
  val LDR_STR
     : state_arm ->
       bool ->
       mode ->
       bool ->
       (bool, i32) cart list ->
       (bool, i32) cart -> (state_arm, memop list) state_out
  val REGISTER_LIST : (bool, i16) cart -> (bool, i4) cart list
  val ADDRESS_LIST : (bool, i32) cart -> num -> (bool, i32) cart list
  val WB_ADDRESS : bool -> (bool, i32) cart -> num -> (bool, i32) cart
  val FIRST_ADDRESS
     : bool ->
       bool -> (bool, i32) cart -> (bool, i32) cart -> (bool, i32) cart
  val ADDR_MODE4
     : bool ->
       bool ->
       (bool, i32) cart ->
       (bool, i16) cart ->
       (bool, i4) cart list * ((bool, i32) cart list * (bool, i32) cart)
  val LDM_LIST
     : (register -> (bool, i32) cart) ->
       mode ->
       (bool, i4) cart list ->
       (bool, i32) cart list -> register -> (bool, i32) cart
  val STM_LIST
     : (register -> (bool, i32) cart) ->
       mode -> ((bool, i4) cart * (bool, i32) cart) list -> memop list
  val LDM_STM
     : state_arm ->
       mode ->
       num option ->
       (bool, i32) cart list ->
       (bool, i32) cart -> (state_arm, memop list) state_out
  val SWP
     : state_arm ->
       mode ->
       bool ->
       (bool, i32) cart ->
       (bool, i32) cart -> (state_arm, memop list) state_out
  val MRC
     : state_arm ->
       mode -> (bool, i32) cart -> (bool, i32) cart -> state_arm
  val MCR_OUT : state_arm -> mode -> (bool, i32) cart -> memop list
  val ADDR_MODE5
     : (register -> (bool, i32) cart) ->
       mode ->
       bool ->
       bool ->
       (bool, i4) cart ->
       (bool, i8) cart -> (bool, i32) cart * (bool, i32) cart
  val LDC_STC
     : state_arm ->
       mode -> (bool, i32) cart -> (state_arm, memop list) state_out
  val CONDITION_PASSED2
     : bool * (bool * (bool * bool)) -> condition -> bool
  val CONDITION_PASSED
     : bool * (bool * (bool * bool)) -> (bool, i32) cart -> bool
  val EXEC_INST
     : state_arm_ex ->
       num option -> (bool, i32) cart list -> bool -> state_arm
  val IS_Dabort : interrupts option -> bool
  val IS_Reset : interrupts option -> bool
  val PROJ_Dabort : interrupts option -> num
  val PROJ_Reset : interrupts option -> state_arm
  val interrupt2exceptions
     : state_arm_ex -> bool * bool -> interrupts option -> exceptions
  val PROJ_IF_FLAGS : state_arm -> bool * bool
  val NEXT_ARM
     : state_arm_ex ->
       interrupts option *
       (bool * ((bool, i32) cart * (bool, i32) cart list)) ->
       state_arm_ex
  val OUT_ARM : state_arm_ex -> memop list
  val ADDR30 : (bool, i32) cart -> (bool, i30) cart
  val SET_BYTE
     : (bool, i2) cart ->
       (bool, i8) cart -> (bool, i32) cart -> (bool, i32) cart
  val MEM_READ
     : ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict *
       (bool, i30) cart -> (bool, i32) cart
  val MEM_WRITE_BYTE
     : ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict ->
       (bool, i32) cart ->
       (bool, i32) cart -> ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict
  val MEM_WRITE_WORD
     : ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict ->
       (bool, i32) cart ->
       (bool, i32) cart -> ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict
  val MEM_WRITE
     : bool ->
       ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict ->
       (bool, i32) cart ->
       (bool, i32) cart -> ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict
  val MEM_WRITE_BLOCK
     : ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict ->
       (bool, i30) cart ->
       (bool, i32) cart list ->
       ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict
  val TRANSFERS
     : ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict ->
       (bool, i32) cart list ->
       memop list ->
       ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict *
        (bool, i32) cart list
  val NEXT_ARMe : state_arme -> state_arme
  val empty_memory : ((bool, i30) cart, (bool, i32) cart) Redblackmap.dict
  val empty_registers : register -> (bool, i32) cart
end
