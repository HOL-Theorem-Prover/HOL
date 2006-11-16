(* interactive use:

quietdec := true;
loadPath := (concat Globals.HOLDIR "/examples/dev/sw") :: !loadPath;

app load ["numLib", "pred_setSimps", "pred_setTheory",
     "arithmeticTheory", "wordsTheory", "pairTheory", "listTheory", "whileTheory", "finite_mapTheory"];

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory
     arithmeticTheory wordsTheory pairTheory listTheory whileTheory finite_mapTheory;

val _ = new_theory "preARM";

(*----------------------------------------------------------------------------*)
(* Registers	                                                              *)
(*----------------------------------------------------------------------------*)

val _ = type_abbrev("REGISTER", Type`:num`);

(*----------------------------------------------------------------------------*)
(* CPSR, In user programs only the top 4 bits of the CPSR are relevant        *)
(* N - the result was negative                                                *)
(* Z - the result was zero                                                    *)
(* C - the result produced a carry out                                        *)
(* V - the result generated an arithmetic overflow                            *)
(*----------------------------------------------------------------------------*)

val _ = type_abbrev("CPSR", Type`:word32`);
val _ = Hol_datatype `SRS = SN | SZ | SC | SV`;

val getS_def = Define
        `getS (cpsr : CPSR) (flag:SRS) =
            case flag of
                 SN -> cpsr %% 31 ||
                 SZ -> cpsr %% 30 ||
                 SC -> cpsr %% 29 ||
                 SV -> cpsr %% 28
        `;

val getS_thm = Q.store_thm (
	"getS_thm",
        `(getS (cpsr : CPSR) SN = cpsr %% 31) /\ 
	 (getS (cpsr : CPSR) SZ = cpsr %% 30) /\
	 (getS (cpsr : CPSR) SC = cpsr %% 29) /\
	 (getS (cpsr : CPSR) SV = cpsr %% 28)
	`,
	RW_TAC std_ss [getS_def]);


val setS_def = Define
        `setS (cpsr : CPSR) (flag:SRS) =
            case flag of
                 SN -> (cpsr !! 0x80000000w) ||
                 SZ -> (cpsr !! 0x40000000w) ||
                 SC -> (cpsr !! 0x20000000w) ||
                 SV -> (cpsr !! 0x10000000w)
        `;

val setS_thm = Q.store_thm (
   "setS_thm",
        `(setS (cpsr : CPSR) SN = (cpsr !! 0x80000000w)) /\
    (setS (cpsr : CPSR) SZ = (cpsr !! 0x40000000w)) /\
    (setS (cpsr : CPSR) SC = (cpsr !! 0x20000000w)) /\
    (setS (cpsr : CPSR) SV = (cpsr !! 0x10000000w))
        `,
   RW_TAC std_ss [setS_def]);

val setNZCV_def = Define
         `setNZCV (cpsr : CPSR) (N, Z, C, V) =
            word_modify
              (\i b.
                 (i = 31) /\ N \/ (i = 30) /\ Z \/ (i = 29) /\ C \/
                 (i = 28) /\ V \/ i < 28 /\ b) cpsr`;

val setNZCV_thm = Q.store_thm (
   "setNZCV_thm",
   `(getS (setNZCV (cpsr : CPSR) (N,Z,C,V)) SN = N) /\
    (getS (setNZCV (cpsr : CPSR) (N,Z,C,V)) SZ = Z) /\
    (getS (setNZCV (cpsr : CPSR) (N,Z,C,V)) SC = C) /\
    (getS (setNZCV (cpsr : CPSR) (N,Z,C,V)) SV = V)`,
   
   RW_TAC (std_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss) [getS_def, setNZCV_def, word_modify_def]);


(*-------------------------------------------------------------------------------*)
(* Operator			                                                 *)
(*-------------------------------------------------------------------------------*)

val _ = Hol_datatype ` OPERATOR = MOV |
			ADD | SUB | RSB | MUL | MLA |
                        AND | ORR | EOR | CMP | TST |
                        LSL | LSR | ASR | ROR |
                        LDR | STR | LDMFD | STMFD |
                        MRS | MSR |
                        B | BL
             `;

(*-------------------------------------------------------------------------------*)
(* Condition Codes                                                                      *)
(*-------------------------------------------------------------------------------*)

val _ = Hol_datatype ` COND = EQ | CS | MI | VS | HI | GE | GT | AL |
                              NE | CC | PL | VC | LS | LT | LE | NV`;

(*-------------------------------------------------------------------------------*)
(* Expressions			                                                 *)
(*-------------------------------------------------------------------------------*)

val _ = type_abbrev("ADDR", Type`:num`);
val _ = type_abbrev("DATA", Type`:word32`);
val _ = type_abbrev("DISTANCE", Type`:num`);

val _ = Hol_datatype `OFFSET = POS of DISTANCE
               | NEG of DISTANCE
             `;


val _ = Hol_datatype `EXP = MEM of num # OFFSET			(* (register, offset) *) 
                  | NCONST of num
		  | WCONST of word32
                  | REG of REGISTER
		  | WREG of REGISTER
             `;

val FP_def =
  Define `FP = REG 11`;

val IP_def =
  Define `IP = REG 12`;

val SP_def =
  Define `SP = REG 13`;

val LR_def =
  Define `LR = REG 14`;

val PC_def =
  Define `PC = REG 15`;

(*-------------------------------------------------------------------------------*)
(* Operations                                                                    *)
(*-------------------------------------------------------------------------------*)

(* An instruction: ((operator, condition code, set flags), destination, source, jump)					 *)
val _ = type_abbrev("OPERATION", Type`:OPERATOR # (COND option) # bool`);
val _ = type_abbrev("INST", Type`:OPERATION # (EXP option) # (EXP list) # (OFFSET option)`);

(*---------------------------------------------------------------------------------*)
(* State                                                                           *)
(*---------------------------------------------------------------------------------*)
  
val _ = type_abbrev("STATE", Type`: ADDR # CPSR # (REGISTER |-> DATA) # (ADDR |-> DATA)`);

val FORALL_DSTATE = Q.store_thm
  ("FORALL_DSTATE",
    `(!s:(REGISTER |-> DATA) # (ADDR |-> DATA). P s) = 
	!regs mem. P (regs,mem)`,
    SIMP_TAC std_ss [FORALL_PROD]);

val FORALL_STATE = Q.store_thm
  ("FORALL_STATE",
    `(!s:STATE. P s) = !pc pcsr regs mem. P (pc,pcsr,(regs,mem))`,
    SIMP_TAC std_ss [FORALL_PROD]);  
               
(*---------------------------------------------------------------------------------*)
(* Read and write registers and memory                                             *)
(*---------------------------------------------------------------------------------*)

val read_def =
  Define `
    read (regs,mem) (exp:EXP) =
      case exp of
        MEM (r,offset) -> 
	    (case offset of 
		  POS k -> mem ' (w2n (regs ' r) + k) ||
		  NEG k -> mem ' (w2n (regs ' r) - k)
	    )	||
	NCONST i -> n2w i     ||
        WCONST w -> w         ||
        REG r -> regs ' r
`;

val read_thm = Q.store_thm (
  "read_thm",
  ` (read (regs,mem) (MEM (r,POS k)) = mem ' (w2n (regs ' r) + k)) /\
    (read (regs,mem) (MEM (r,NEG k)) = mem ' (w2n (regs ' r) - k)) /\
    (read (regs,mem) (NCONST i) = n2w i) /\
    (read (regs,mem) (WCONST w) = w) /\
    (read (regs,mem) (REG r) = regs ' r)`,
    RW_TAC std_ss [read_def]);

val write_def =
  Define `
    write (regs,mem) (exp:EXP) (v:DATA)=
      case exp of
        MEM (r,offset) -> 
	    (regs,
             (case offset of
                   POS k -> mem |+ (w2n (regs ' r) + k, v) ||
                   NEG k -> mem |+ (w2n (regs ' r) - k, v)
             ))   	 ||
        REG r -> ( regs |+ (r, v),
                   mem ) ||
        _ -> (regs, mem)
  `;

val write_thm = Q.store_thm (
  "write_thm",
  ` (write (regs,mem) (MEM (r,POS k)) v = (regs, mem |+ (w2n (regs ' r) + k, v))) /\
    (write (regs,mem) (MEM (r,NEG k)) v = (regs, mem |+ (w2n (regs ' r) - k, v))) /\
    (write (regs,mem) (REG r) v = (regs |+ (r, v), mem))`,
    RW_TAC std_ss [write_def]);                      

(*---------------------------------------------------------------------------------*)
(* Decoding and execution of an instruction                                        *)
(* All instructions are executed conditionally                                     *)
(*---------------------------------------------------------------------------------*)

val goto_def =
  Define `
    goto (pc, SOME jump) =
        case jump of
            POS n -> pc + n  || 
            NEG n -> pc - n
   `;

val goto_thm = Q.store_thm (
  "goto_thm",
  ` (goto (pc, SOME (POS n)) = pc + n) /\
    (goto (pc, SOME (NEG n)) = pc - n)
  `,
  RW_TAC std_ss [goto_def]);


val decode_op_def = 
  Define `
  decode_op (pc,cpsr,s) (op,dst,src,jump) =
     case op of
          MOV -> (cpsr, write s (THE dst) (read s (HD src)))
              ||

          (* we assume that the stack goes from low addresses to high addresses even it is "FD",
             change LDMFD to be LDMFA if necessary *)

	  LDMFD -> (case THE dst of
			REG r ->
			     (* We must read values from the original state instead of the updated state *)
			    (cpsr, FST (FOLDL (\(s1,i) reg. (write s1 reg (read s (MEM(r,POS(i+1)))), i+1)) (s,0) src))
                    ||
                        WREG r ->
			    (cpsr, write (FST (FOLDL (\(s1,i) reg. (write s1 reg (read s (MEM(r,POS(i+1)))), i+1)) (s,0) src))
						 (REG r) (read s (REG r) + n2w (LENGTH src)))
		   )
	      ||

          (* we assume that the stack goes from low addresses to high addresses even it is "FD",
             change STMFA to be STMFD if necessary *)

	  STMFD -> (case THE dst of
                        REG r ->
                                (cpsr,
			         (* We must read values from the original state instead of the updated state *)
                                 FST (FOLDL (\(s1,i) reg. (write s1 (MEM(r,NEG i)) (read s reg), i+1)) (s,0) (REVERSE src))) ||
                        WREG r ->
                                (cpsr,
				 write (FST (FOLDL (\(s1,i) reg. (write s1 (MEM(r,NEG i)) (read s reg), i+1)) (s,0) (REVERSE src)))
					(REG r) (read s (REG r) - n2w (LENGTH src)))
		   )
	      ||
          ADD -> (cpsr, (write s (THE dst) (read s (HD src) + read s (HD (TL (src))))))
              ||
          SUB -> (cpsr, (write s (THE dst) (read s (HD src) - read s (HD (TL (src))))))
              ||
          RSB -> (cpsr, (write s (THE dst) (read s (HD (TL (src))) - read s (HD src))))
              ||
          MUL -> (cpsr, (write s (THE dst) (read s (HD src) * read s (HD (TL (src))))))
              ||
	  MLA -> (cpsr, (write s (THE dst) (read s (HD src) * read s (HD (TL (src))) + 
						  read s (HD (TL (TL (src)))) )))
              ||
          AND -> (cpsr, (write s (THE dst) (read s (HD src) && read s (HD (TL (src))))))
              ||
          ORR -> (cpsr, (write s (THE dst) (read s (HD src) !! read s (HD (TL (src))))))
              ||
          EOR -> (cpsr, (write s (THE dst) (read s (HD src) ?? read s (HD (TL (src))))))
              ||

          LSL -> (cpsr, (write s (THE dst) 
				(read s (HD src) << w2n (read s (HD (TL (src)))))))
              ||
          LSR -> (cpsr, (write s (THE dst) 
				(read s (HD src) >>> w2n (read s (HD (TL (src)))))))
              ||
          ASR -> (cpsr, (write s (THE dst) 
				(read s (HD src) >> w2n (read s (HD (TL (src)))))))
              ||
          ROR -> (cpsr, (write s (THE dst) 
				(read s (HD src) #>> w2n (read s (HD (TL (src)))))))
              ||

          CMP -> (let a = read s (HD src) in
                 let b = read s (HD (TL (src))) in
                 (setNZCV cpsr (word_msb (a - b),
                                a = b,
                                b <=+ a,
                                ~(word_msb a = word_msb b) /\ ~(word_msb a = word_msb (a - b))), s))
              ||
          
          (*  The carry flag is always set to false. This does not correspond to
              real ARM assembler. There you could set the carry flag by passing
              an shift as second argument. *)
          TST -> (let a = read s (HD src) in
                 let b = read s (HD (TL (src))) in
                 (setNZCV cpsr (word_msb (a && b),
                                (a && b) = 0w,
                                F,
                                cpsr %% 28), s))

              ||

          LDR -> (cpsr, (write s (THE dst) (read s (HD src))))
		(* write the value in src (i.e. the memory) to the dst (i.e. the register)*)
              ||

          STR -> (cpsr, (write s (HD src) (read s (THE dst))))   
		(* write the value in src (i.e. the register) to the dst (i.e. the memory)*)
              ||

          MSR -> (read s (HD src), s)
              ||
          MRS -> (cpsr, (write s (THE dst) cpsr))
	      ||

	  B   -> (cpsr, s)
	      || 
          BL ->  (cpsr, write s (REG 14) (n2w (SUC pc)))
  `;

val decode_op_thm = Q.store_thm
("decode_op_thm",
  `!pc cpsr s dst src jump.
  (decode_op (pc,cpsr,s) (MOV,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src)))) /\
  (decode_op (pc,cpsr,s) (ADD,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) + read s (HD (TL src))))) /\
  (decode_op (pc,cpsr,s) (SUB,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) - read s (HD (TL src))))) /\
  (decode_op (pc,cpsr,s) (RSB,SOME dst,src,jump) = (cpsr, write s dst (read s (HD (TL src)) - read s (HD src)))) /\
  (decode_op (pc,cpsr,s) (MUL,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) * read s (HD (TL src))))) /\
  (decode_op (pc,cpsr,s) (MLA,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) * read s (HD (TL src)) + read s (HD (TL (TL src)))))) /\
  (decode_op (pc,cpsr,s) (AND,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) && read s (HD (TL src))))) /\
  (decode_op (pc,cpsr,s) (ORR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) !! read s (HD (TL src))))) /\
  (decode_op (pc,cpsr,s) (EOR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) ?? read s (HD (TL src))))) /\
  (decode_op (pc,cpsr,s) (CMP,NONE,src,jump) = (
      let a = read s (HD src) in
      let b = read s (HD (TL (src))) in
         (setNZCV cpsr (word_msb (a - b),
                        a = b,
                        b <=+ a,
                        ~(word_msb a = word_msb b) /\ ~(word_msb a = word_msb (a - b))), s))) /\
  (decode_op (pc,cpsr,s) (TST,NONE,src,jump) = 
      (let a = read s (HD src) in
                     let b = read s (HD (TL (src))) in
                     (setNZCV cpsr (word_msb (a && b),
                                    (a && b) = 0w,
                                    F,
                                    cpsr %% 28), s))) /\
  (decode_op (pc,cpsr,s) (LSL,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) << w2n (read s (HD (TL src)))))) /\
  (decode_op (pc,cpsr,s) (LSR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) >>> w2n (read s (HD (TL src)))))) /\
  (decode_op (pc,cpsr,s) (ASR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) >> w2n (read s (HD (TL src)))))) /\
  (decode_op (pc,cpsr,s) (ROR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) #>> w2n (read s (HD (TL src)))))) /\
  (decode_op (pc,cpsr,s) (LDR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src)))) /\
  (decode_op (pc,cpsr,s) (STR,SOME dst,src,jump) = (cpsr, write s (HD src) (read s dst))) /\
  (decode_op (pc,cpsr,s) (LDMFD, SOME (REG r),src,jump) =
              (cpsr, FST (FOLDL
                          (\(s1,i) reg.
                             (write s1 reg (read s (MEM (r,POS (i + 1)))),
                              i + 1)) (s,0) src))) /\
  (decode_op (pc,cpsr,s) (LDMFD,SOME (WREG r),src,jump) =
              (cpsr, write (FST
                             (FOLDL
                               (\(s1,i) reg.
                                (write s1 reg
                                   (read s (MEM (r,POS (i + 1)))),i + 1))
                               (s,0) src)) (REG r)
                       	     (read s (REG r) + n2w (LENGTH src)))) /\
  (decode_op (pc,cpsr,s) (STMFD,SOME (REG r),src,jump) =
                  (cpsr, FST (FOLDL
                          (\(s1,i) reg.
                             (write s1 (MEM (r,NEG i)) (read s reg),i + 1))
                          (s,0) (REVERSE src)))) /\
  (decode_op (pc,cpsr,s) (STMFD,SOME (WREG r),src,jump) =
                  (cpsr, write (FST
                          (FOLDL
                             (\(s1,i) reg.
                                (write s1 (MEM (r,NEG i)) (read s reg),
                                 i + 1)) (s,0) (REVERSE src))) (REG r)
                       (read s (REG r) - n2w (LENGTH src)))) /\
  (decode_op (pc,cpsr,s) (MRS,SOME dst,src,jump) = (cpsr,write s dst cpsr)) /\
  (decode_op (pc,cpsr,s) (MSR,NONE,src,jump) = (read s (HD src),s)) /\
  (decode_op (pc,cpsr,s) (B,NONE,src,jump) = (cpsr,s)) /\
  (decode_op (pc,cpsr,s) (BL,NONE,src,jump) = (cpsr,write s (REG 14) (n2w (SUC pc))))`,
 
   RW_TAC std_ss [decode_op_def]);
  
val decode_cond_cpsr_def = 
    Define `(decode_cond_cpsr cpsr EQ = getS cpsr SZ) /\
            (decode_cond_cpsr cpsr CS = getS cpsr SC) /\
            (decode_cond_cpsr cpsr MI = getS cpsr SN) /\
            (decode_cond_cpsr cpsr VS = getS cpsr SV) /\
            (decode_cond_cpsr cpsr HI = ((getS cpsr SC) /\ ~(getS cpsr SZ))) /\
            (decode_cond_cpsr cpsr GE = ((getS cpsr SN) = (getS cpsr SV))) /\
            (decode_cond_cpsr cpsr GT = (~(getS cpsr SZ) /\ ((getS cpsr SN) = (getS cpsr SV)))) /\
            (decode_cond_cpsr cpsr AL = T) /\
            (decode_cond_cpsr cpsr NE = ~(getS cpsr SZ)) /\
            (decode_cond_cpsr cpsr CC = ~(getS cpsr SC)) /\
            (decode_cond_cpsr cpsr PL = ~(getS cpsr SN)) /\
            (decode_cond_cpsr cpsr VC = ~(getS cpsr SV)) /\
            (decode_cond_cpsr cpsr LS = (~(getS cpsr SC) \/ (getS cpsr SZ))) /\
            (decode_cond_cpsr cpsr LT = ~((getS cpsr SN) = (getS cpsr SV))) /\
            (decode_cond_cpsr cpsr LE = ((getS cpsr SZ) \/ ~((getS cpsr SN) = (getS cpsr SV)))) /\
            (decode_cond_cpsr cpsr NV = F)`


val decode_cond_def = 
  Define `
    (decode_cond ((pc,cpsr,s):STATE) (((op,cond,sflag), dst, src, jump):INST)) =
        (case cond of
            NONE -> (pc+1, decode_op (pc,cpsr,s) (op,dst,src,jump))
                ||
            SOME c -> 
		          if (decode_cond_cpsr cpsr c) then (goto(pc,jump), decode_op (pc,cpsr,s) (op,dst,src,jump))
			        else (pc+1, cpsr, s))
  `;

val decode_cond_thm = Q.store_thm
( "decode_cond_thm",
  `!pc cpsr s op sflag dst src jump.
	  (decode_cond (pc,cpsr,s) ((op,NONE,sflag),dst,src,jump) = (pc+1, decode_op (pc,cpsr,s) (op,dst,src,jump))) /\
     (decode_cond (pc,cpsr,s) ((op,SOME AL,sflag),dst,src,jump) = (goto(pc,jump), decode_op (pc,cpsr,s) (op,dst,src,jump))) /\
	  (decode_cond (pc,cpsr,s) ((op,SOME NV,sflag),dst,src,jump) = (pc+1, cpsr, s))`,

  RW_TAC std_ss [decode_cond_def, decode_cond_cpsr_def]);



(*---------------------------------------------------------------------------------*)
(* Upload instructions into the instruction buffer                                 *)
(*---------------------------------------------------------------------------------*)

(* upload and uploadCode: upload the instructions into the instruction buffer beginning from start                                      *)
(* By default, the code is uploaded to the buffer starting from address 0 (this is what the uploadCode describes                        *)

val upload_def = Define `
    (upload (stm::stmL) iB start = upload stmL (\addr. if addr = start then stm else iB addr) (SUC start)) /\
    (upload ([]) iB start = iB)
  `;


val UPLOAD_NOT_AFFECT_LOWER = Q.store_thm (
   "UPLOAD_NOT_AFFECT_LOWER",
  `!instL iB start n. n < start ==>
        ((upload instL iB start) n = iB n)`,
   Induct_on `instL` THEN 
   RW_TAC std_ss [upload_def] THEN
   Induct_on `n` THEN
   RW_TAC std_ss [upload_def] THEN           
   `SUC n < SUC start` by RW_TAC arith_ss [] THEN
   RES_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (ASSUME_TAC o Q.SPEC `(\addr:num. if addr = start then h else iB addr)`) THEN
   FULL_SIMP_TAC arith_ss []
   );

val UPLOAD_LEM = Q.store_thm (
   "UPLOAD_LEM",
   `!instL iB start n. n < LENGTH instL ==>
        ((upload instL iB start) (start+n) = EL n instL)`,
    Induct_on `n` THEN Induct_on `instL` THEN RW_TAC list_ss [upload_def] THENL [
        RW_TAC arith_ss [UPLOAD_NOT_AFFECT_LOWER],
        RES_TAC THEN 
          POP_ASSUM (ASSUME_TAC o Q.SPECL [`SUC start`,`(\addr. if addr = start then h else iB addr)`]) THEN
          METIS_TAC [ADD_SUC, SUC_ADD_SYM, ADD_SYM]
    ]
   );

val UPLOAD_START_POINT_INDEPENDENT = Q.store_thm (
  "UPLOAD_START_POINT_INDEPENDENT",
  `!instL start1 start2 iB addr. addr < LENGTH instL ==>
	((upload instL iB start1) (start1+addr) = (upload instL iB start2) (start2+addr))`,
   RW_TAC std_ss [UPLOAD_LEM]
  );         

val uploadCode_def =
  Define `uploadCode instL iB = upload instL iB 0`;

                                     
val UPLOADCODE_LEM = Q.store_thm (
   "UPLOADCODE_LEM",
   `!instL iB n. n < LENGTH instL ==>
        ((uploadCode instL iB) n = EL n instL)`,
    RW_TAC std_ss [uploadCode_def] THEN
    IMP_RES_TAC UPLOAD_LEM THEN
    POP_ASSUM (ASSUME_TAC o Q.SPECL [`0`,`iB`]) THEN
    FULL_SIMP_TAC arith_ss []
   );
        
val uploadSeg_def = Define `
    (uploadSeg 0 segs iB = iB) /\
    (uploadSeg (SUC n) segs iB = 
	upload (EL n segs) (uploadSeg n segs iB) (10 * n))`;

val UPLOADSEG_LEM = Q.store_thm
  ("UPLOADSEG_LEM",
   `!n segs instB. uploadSeg n segs instB = 
	(if n > 0 then upload (EL (PRE n) segs) (uploadSeg (PRE n) segs instB) (10 * (PRE n)) else instB)`,
    Cases_on `n` THEN RW_TAC list_ss [uploadSeg_def]
  );

(*---------------------------------------------------------------------------------*)
(* Running of a ARM program                                                        *)
(* Run the instruction in the instruction buffer for n steps                       *)
(*---------------------------------------------------------------------------------*)

val (run_def,run_ind) =
 Defn.tprove
  (Hol_defn "run"
    `run n instB P (pc,cpsr,st) =
        if n = 0 then (pc,cpsr,st)
        else
	   if P (pc,cpsr,st) then (pc,cpsr,st)
           else run (n-1) instB P (decode_cond (pc,cpsr,st) (instB pc))`,
    WF_REL_TAC `measure FST`);

val _ = save_thm("run_def", run_def);
val _ = save_thm("run_ind", run_ind);

val RUN_LEM_1 = Q.store_thm
  ("RUN_LEM_1",
   `!n instB s.
        (run (SUC n) instB P s =
		if P s then s
                else run n instB P (decode_cond s (instB (FST s)))
        ) /\
        (run 0 instB P s = s)`,
   SIMP_TAC list_ss [FORALL_STATE] THEN REPEAT GEN_TAC THEN
   RW_TAC list_ss [Once run_def, LET_THM] THENL [
        RW_TAC list_ss [Once run_def, LET_THM],
        RW_TAC list_ss [Once run_def, LET_THM]
   ]
  );

val RUN_LEM_2 = Q.store_thm
  ("RUN_LEM_2",
   `!n instB P s. P s ==> (run n instB P s = s)`,
   SIMP_TAC list_ss [FORALL_STATE] THEN
   Induct_on `n` THEN RW_TAC list_ss [RUN_LEM_1]
  );


val RUN_THM_1 = Q.store_thm
  ("RUN_THM_1",
   `!m n s instB.
        (run (m+n) instB P s = run n instB P (run m instB P s))`,
  Induct_on `m` THEN REPEAT GEN_TAC THENL [
        RW_TAC list_ss [RUN_LEM_1],
        `SUC m + n = SUC (m + n)` by RW_TAC list_ss [ADD_SUC] THEN
        ASM_REWRITE_TAC [] THEN RW_TAC list_ss [RUN_LEM_1] THEN
	RW_TAC list_ss [RUN_LEM_2]
  	]
  );

val _ = Globals.priming := NONE;

(*---------------------------------------------------------------------------------*)
(* An assistant theorem about LEAST                                                *)
(*---------------------------------------------------------------------------------*)

val LEAST_ADD_LEM = Q.store_thm
 ("LEAST_ADD_LEM",
  `!P m. (?n. P n) /\ m <= (LEAST n. P n) ==>
           ((LEAST n. P n) = (LEAST n. P (m + n)) + m)`,
  Induct_on `m` THENL [
    RW_TAC list_ss [],
    REPEAT STRIP_TAC THEN LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
        `(LEAST n. P n) <= n` by METIS_TAC [FULL_LEAST_INTRO] THEN
        `n = n - SUC m + SUC m` by RW_TAC arith_ss [] THEN
        METIS_TAC [],
        LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
            METIS_TAC [],
            `n'' <= n' + SUC m` by METIS_TAC [LESS_CASES] THEN
            `(LEAST n. P n) <= n''` by METIS_TAC [FULL_LEAST_INTRO] THEN
            `(n'' - SUC m) + SUC m = n''` by RW_TAC arith_ss [] THEN
            `n' <= n'' - SUC m` by METIS_TAC [LESS_CASES] THEN
            `n' + SUC m <= n''` by RW_TAC arith_ss [] THEN
            RW_TAC arith_ss []]
        ]]
  );

(*----------------------------------------------------------------------------*)
(* Assistant theorems for the FUNPOW                                          *)
(*----------------------------------------------------------------------------*)

val FUNPOW_THM_1 = Q.store_thm
  ("FUNPOW_THM_1",
  ` (!f. FUNPOW f 0 = \x.x) /\
    (!f n. FUNPOW f (SUC n) = f o (FUNPOW f n))`,
   RW_TAC list_ss [FUN_EQ_THM, FUNPOW_SUC] THEN
   RW_TAC list_ss [FUNPOW]
  );

val FUNPOW_THM_2 = Q.store_thm
  ("FUNPOW_THM_2",
  ` (!f. FUNPOW f 0 = \x.x) /\
    (!f n. FUNPOW f (SUC n) = (FUNPOW f n) o f)`,
   RW_TAC list_ss [FUN_EQ_THM, FUNPOW]
  );

val FUNPOW_FUNPOW = Q.store_thm
  ("FUNPOW_FUNPOW",
  ` !f m n. (FUNPOW f m) o (FUNPOW f n) = FUNPOW f (m+n)`,
   Induct_on `m` THENL [
       RW_TAC list_ss [FUNPOW_THM_1] THEN
       METIS_TAC [],
       RW_TAC list_ss [FUNPOW_THM_1, GSYM SUC_ADD_SYM]
   ]
  );


(*----------------------------------------------------------------------------*)
(* Assistant theorems for the WHILE and LEAST                                 *)
(* We use the "shortest" as a short-hand of the LEAST-FUNPOW                  *)
(*----------------------------------------------------------------------------*)

val stopAt_def = Define `
   stopAt P g x =
       ?n. P (FUNPOW g n x)`;


val shortest_def = Define `
    shortest P g x =
        LEAST n. P (FUNPOW g n x)`;


val STOPAT_THM = Q.store_thm
  ("STOPAT_THM",
   `!m P g x.
       stopAt P g x /\
       m <= shortest P g x ==>
       stopAt P g (FUNPOW g m x)`,
    Cases_on `m` THENL [
        RW_TAC std_ss [shortest_def, stopAt_def, FUNPOW],
        RW_TAC std_ss [stopAt_def,shortest_def] THEN
        `~(n' < LEAST n. P (FUNPOW g n x))` by METIS_TAC [Q.SPEC `\n. P(FUNPOW g n x)` LESS_LEAST] THEN
        `SUC n <= n'` by RW_TAC arith_ss [] THEN
        Q.EXISTS_TAC `n' - SUC n` THEN
        RW_TAC arith_ss [SIMP_RULE std_ss [FUN_EQ_THM] FUNPOW_FUNPOW]
    ]
  );

val SHORTEST_STOP = Q.store_thm
  ("SHORTEST_STOP",
   `!x P g.
       stopAt P g x ==>
       P (FUNPOW g (shortest P g x) x)`,
    RW_TAC std_ss [stopAt_def, shortest_def] THEN
    METIS_TAC [Q.SPECL [`\n. P (FUNPOW g n x)`,`x`] LEAST_INTRO]
  );  

val SHORTEST_LEM = Q.store_thm
  ("SHORTEST_LEM",
   `!x P g.
       (P x ==> (shortest P g x = 0)) /\
       (stopAt P g x ==>
       ((0 = shortest P g x) ==> P x) /\
       (~(P x) = 1 <= shortest P g x))`,
    REWRITE_TAC [stopAt_def, shortest_def] THEN REPEAT GEN_TAC THEN 
    `(P x ==> ((LEAST n. P (FUNPOW g n x)) = 0))` by ALL_TAC THENL [
       STRIP_TAC THEN
       `P (FUNPOW g 0 x)` by METIS_TAC [FUNPOW] THEN
	    `~(0 < (LEAST n. P (FUNPOW g n x)))` by METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`\n.P (FUNPOW g n x)`, `0`] LESS_LEAST)] THEN
	    RW_TAC arith_ss [],
       STRIP_TAC THENL [
           RW_TAC std_ss [],
           STRIP_TAC THEN
           `(0 = LEAST n. P (FUNPOW g n x)) ==> P x` by METIS_TAC [Q.SPEC `\n. P (FUNPOW g n x)` LEAST_EXISTS_IMP, FUNPOW] THEN
           RW_TAC std_ss [] THEN EQ_TAC THEN STRIP_TAC THEN
           FULL_SIMP_TAC arith_ss []
       ]]
  );
	       
val SHORTEST_THM = Q.store_thm
  ("SHORTEST_THM",
   `!x P g m.
       stopAt P g x /\
       m <= shortest P g x ==>
       (shortest P g x = (shortest P g (FUNPOW g m x) + m))`,
    RW_TAC std_ss [shortest_def, stopAt_def] THEN
    REWRITE_TAC [SIMP_RULE std_ss [FUN_EQ_THM] FUNPOW_FUNPOW] THEN
    CONV_TAC (DEPTH_CONV (ONCE_REWRITE_CONV [Once ADD_SYM])) THEN
    HO_MATCH_MP_TAC LEAST_ADD_LEM THEN
    METIS_TAC []
  );

val SHORTEST_CASES = Q.store_thm
  ("SHORTEST_CASES",
   `!x P g.
       stopAt P g x ==>
       (P x ==> (shortest P g x = 0)) /\
       (~P x ==> (shortest P g x = SUC (shortest P g (g x))))`,
    RW_TAC std_ss [] THENL [
         METIS_TAC [SHORTEST_LEM],
         `1 <= shortest P g x` by METIS_TAC [SHORTEST_LEM] THEN
           IMP_RES_TAC SHORTEST_THM THEN
           ASSUME_TAC (DECIDE ``1 = SUC 0``) THEN
           METIS_TAC [FUNPOW, SUC_ONE_ADD, ADD_SYM]
   ]
  );

val SHORTEST_INDUCTIVE = Q.store_thm
  ("SHORTEST_INDUCTIVE",
   `!P g x n.
       stopAt P g x /\
       (shortest P g x = SUC n) ==>
       stopAt P g (g x) /\
       ~(P x) /\
       (n = shortest P g (g x))`,
    RW_TAC std_ss [] THENL [
        `SUC 0 <= shortest P g x` by RW_TAC arith_ss [] THEN
            METIS_TAC [Q.SPEC `SUC 0` STOPAT_THM, FUNPOW],
        `~(shortest P g x = 0)` by RW_TAC arith_ss [] THEN
            METIS_TAC [SHORTEST_CASES],
        `SUC 0 <= shortest P g x` by RW_TAC arith_ss [] THEN
             IMP_RES_TAC (Q.SPECL [`x`, `P`, `g`, `SUC 0`] SHORTEST_THM) THEN
             FULL_SIMP_TAC arith_ss [FUNPOW]
    ]
  );


(*----------------------------------------------------------------------------*)
(* Stop when a specific condition holds                                       *)
(*----------------------------------------------------------------------------*)

val TERD_WHILE_EQ_UNROLL = Q.store_thm
  ("TERD_WHILE_EQ_UNROLL",
   `!x P g.
    stopAt P g x ==>
        (WHILE ($~ o P) g x = FUNPOW g (shortest P g x) x)`,
   Induct_on `shortest P g x` THENL [
       REWRITE_TAC [Once EQ_SYM_EQ] THEN
           REPEAT STRIP_TAC THEN
           IMP_RES_TAC SHORTEST_LEM THEN
           RW_TAC std_ss [Once WHILE, FUNPOW],
        
        REPEAT GEN_TAC THEN
           POP_ASSUM (ASSUME_TAC o (Q.SPECL [`P`, `g:'a ->'a`, `g (x:'a)`])) THEN 
           REWRITE_TAC [Once EQ_SYM_EQ] THEN
           REPEAT STRIP_TAC THEN
           `1 <= shortest P g x` by RW_TAC arith_ss [] THEN
           IMP_RES_TAC SHORTEST_THM THEN
	   `~( P x)` by METIS_TAC [SHORTEST_LEM] THEN
           `stopAt P g (g x)` by ALL_TAC THENL [
               FULL_SIMP_TAC std_ss [stopAt_def] THEN
                   Cases_on `n` THEN
	           FULL_SIMP_TAC std_ss [FUNPOW] THEN
                   METIS_TAC [],
	       PAT_ASSUM ``shortest P g x = k + 1`` (ASSUME_TAC o REWRITE_RULE [REWRITE_RULE [Once ADD_SYM] (GSYM SUC_ONE_ADD)]) THEN
                   ASSUME_TAC (DECIDE ``1 = SUC 0``) THEN
                   REWRITE_TAC [Once WHILE] THEN
                   `v = shortest P g (g x)` by METIS_TAC [FUNPOW, numTheory.INV_SUC] THEN
		   FULL_SIMP_TAC std_ss [FUNPOW]
           ]
   ]
  );                 

(*----------------------------------------------------------------------------*)
(* Unroll the WHILE once, stop unrolling when a condition holds               *)
(*----------------------------------------------------------------------------*)

val UNROLL_ADVANCE = Q.store_thm
  ("UNROLL_ADVANCE",
   `!P g x.
        stopAt P g x ==>
        (FUNPOW g (shortest P g x) x =
                if (P x) then x
                else FUNPOW g (shortest P g (g x)) (g x)
        )`,
   RW_TAC list_ss [] THEN
   METIS_TAC [SHORTEST_CASES, FUNPOW]
  );

val WHILE_STILL = Q.store_thm
  ("WHILE_STILL",
   `!P g x.
        stopAt P g x ==>
	    (WHILE ($~ o P) g (WHILE ($~ o P) g x) = WHILE ($~ o P) g x)`,
   SIMP_TAC std_ss [TERD_WHILE_EQ_UNROLL] THEN
   RW_TAC std_ss [stopAt_def, shortest_def] THEN
   IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPEC `\n.P (FUNPOW g n x)` LEAST_EXISTS_IMP)) THEN
   RW_TAC std_ss [Once WHILE]
  );


(*---------------------------------------------------------------------------------*)
(*                    Run to a particular position                                 *)
(* Run the instructions in the instruction buffer until the pc reaches a specific  *)
(*	position. The running may not terminate and keep going on                  *) 
(*---------------------------------------------------------------------------------*)

val _ = type_abbrev("STATEPCS", Type`:STATE # (num->bool)`);

val step_def = Define `
  step instB =
       \(s,pcS).(decode_cond s (instB (FST s)),FST s INSERT pcS)`;

val step_FORM1 = Q.store_thm
  ("step_FORM1",
   `!instB. step instB =
	 \s.(decode_cond (FST s) (instB (FST (FST s))),FST (FST s) INSERT (SND s))`,
   RW_TAC std_ss [FUN_EQ_THM] THEN
   `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
   RW_TAC std_ss [step_def]
  );

val STATE_PCS_SEPERATE = Q.store_thm
  ("STATE_PCS_SEPERATE",
  `!m pcS0 pcS1 instB s. FST (FUNPOW (step instB) m (s,pcS0)) =
                         FST (FUNPOW (step instB) m (s,pcS1))`,
  Induct_on `m` THEN RW_TAC std_ss [FUNPOW] THEN
  FULL_SIMP_TAC std_ss [step_def]
  );

val STOPAT_ANY_PCS = Q.store_thm
  ("STOPAT_ANY_PCS",
   `!pcS0 pcS1 instB j s.
       stopAt (\s:STATEPCS. (FST s = j)) (step instB) (s,pcS0) ==>
          stopAt (\s:STATEPCS. (FST s = j)) (step instB) (s,pcS1)`,
    RW_TAC std_ss [stopAt_def] THEN
    Q.EXISTS_TAC `n` THEN
    RW_TAC std_ss [STATE_PCS_SEPERATE]
  );

val STOPAT_ANY_PCS_2 = Q.store_thm
  ("STOPAT_ANY_PCS_2",
   `!pcS0 pcS1 instB j s.
       stopAt (\s:STATEPCS. (FST (FST s) = j)) (step instB) (s,pcS0) ==>
          stopAt (\s:STATEPCS. (FST (FST s) = j)) (step instB) (s,pcS1)`,
    RW_TAC std_ss [stopAt_def] THEN
    Q.EXISTS_TAC `n` THEN
    METIS_TAC [STATE_PCS_SEPERATE]
  );
      

val SHORTEST_INDEPENDENT_OF_PCS = Q.store_thm
  ("SHORTEST_INDEPENDENT_OF_PCS",
  `!s0 s1 instB j.
        stopAt (\s. FST (FST s) = j) (step instB) s0 /\ 
        (FST s0 = FST s1) ==>
	    (shortest (\s. FST (FST s) = j) (step instB) s0 =
             shortest (\s. FST (FST s) = j) (step instB) s1)`,
  Induct_on `shortest (\s. FST (FST s) = j) (step instB) s0` THENL [ 
      RW_TAC std_ss [] THEN
          IMP_RES_TAC SHORTEST_LEM THEN
          FULL_SIMP_TAC std_ss [] THEN
          `(\s. FST (FST s) = j) s1` by RW_TAC std_ss [] THEN
          IMP_RES_TAC SHORTEST_LEM THEN
          METIS_TAC [],
      REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [] THEN
          IMP_RES_TAC SHORTEST_INDUCTIVE THEN
          `?st. (?pcS0. s0 = (st,pcS0)) /\ (?pcS1. s1 = (st,pcS1))` by METIS_TAC [ABS_PAIR_THM, FST] THEN
          Q.PAT_ASSUM `!j instB s0.p` (MP_TAC o Q.SPECL [`j`,`instB`,`step instB s0`]) THEN
          FULL_SIMP_TAC std_ss [] THEN
          STRIP_TAC THEN
          POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [Ntimes step_def 2] o (Q.SPEC `step instB (st,pcS1)`)) THEN
	  ASM_REWRITE_TAC [] THEN
          IMP_RES_TAC STOPAT_ANY_PCS_2 THEN
          `~(\s. FST (FST s) = j) (st,pcS1)` by METIS_TAC [FST] THEN
          `SUC 0 <= shortest (\s:STATEPCS. FST (FST s) = j) (step instB) (st,pcS1)` by METIS_TAC [Q.SPECL [`(st,pcS1)`,`(\s:STATEPCS. FST (FST s) = j)`,
			`step instB`] (INST_TYPE [alpha |-> Type`:STATEPCS`] SHORTEST_LEM), DECIDE (Term `1 = SUC 0`)] THEN
          `shortest (\s. FST (FST s) = j) (step instB) (st,pcS1)  = shortest (\s. FST (FST s) = j) (step instB) (step instB (st,pcS1)) + SUC 0`
                by METIS_TAC [FUNPOW, SHORTEST_THM] THEN
           RW_TAC arith_ss []
       ]
  );

val runTo_def = Define `
  runTo instB j (s,pcS) =
	WHILE (\(s,pcS). ~(FST s = j)) (step instB) (s,pcS)`;

(*----------------------------------------------------------------------------*)
(* A bunch of theorems about runTo                                            *)
(*----------------------------------------------------------------------------*)

val runTo_FORM1 = Q.store_thm
  ("runTo_FORM1",
   `!instB j s. runTo instB j s =
	WHILE (\s. ~(FST (FST s) = j)) (step instB) s`,
   REPEAT GEN_TAC THEN
   `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
   RW_TAC std_ss [runTo_def] THEN
   `(\s:STATEPCS. ~(FST (FST s) = j)) = (\(s,pcS). ~(FST s = j))` by ALL_TAC THENL [
       RW_TAC std_ss [FUN_EQ_THM] THEN
           `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
           RW_TAC std_ss [],
       RW_TAC std_ss []
   ]
  );

val RUNTO_ADVANCE = Q.store_thm
  ("RUNTO_ADVANCE",
   `!instB j s pcS.
        (runTo instB j (s,pcS) =
                if (FST s = j) then (s,pcS)
                else runTo instB j (decode_cond s (instB (FST s)), FST s INSERT pcS)
        )`,
   RW_TAC list_ss [runTo_def, step_def] THENL [
        RW_TAC list_ss [Once WHILE],
        RW_TAC list_ss [Once WHILE]
	]
  );

val RUNTO_EXPAND_ONCE = Q.store_thm
  ("RUNTO_EXPAND_ONCE",
   `!instB j s.
        (runTo instB j s =
                if (FST (FST s) = j) then s
                else runTo instB j (step instB s)
        )`,
   REPEAT STRIP_TAC THEN
   `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
   RW_TAC list_ss [step_def, Once RUNTO_ADVANCE]
  );


val UNROLL_RUNTO = Q.store_thm
  ("UNROLL_RUNTO",
   `!instB j s.
       stopAt (\s:STATEPCS. (FST (FST s) = j)) (step instB) s ==>
          (runTo instB j s = FUNPOW (step instB) (shortest (\s.(FST (FST s) = j)) (step instB) s) s)`,

    RW_TAC std_ss [runTo_FORM1] THEN
    ASSUME_TAC (INST_TYPE [alpha |-> Type `:STATEPCS`] TERD_WHILE_EQ_UNROLL) THEN
    RES_TAC THEN
    `$~ o (\s:STATEPCS. (FST (FST s) = j)) = (\s:STATEPCS. ~(FST (FST s) = j))` by RW_TAC std_ss [FUN_EQ_THM] THEN
    METIS_TAC []
  );



val terd_def = Define `
  terd instB j s =
	stopAt (\s:STATEPCS.FST (FST s) = j) (step instB) s`;


val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;


val RUNTO_STATE_PCS_SEPERATE = Q.store_thm
  ("RUNTO_STATE_PCS_SEPERATE",
  `!j pcS0 pcS1 instB s. 
            stopAt (\s:STATEPCS.FST (FST s) = j) (step instB) (s,pcS0) ==>
            (FST (runTo instB j (s,pcS0)) = FST (runTo instB j (s,pcS1)))`,
  RW_TAC std_ss [UNROLL_RUNTO] THEN
  IMP_RES_TAC STOPAT_ANY_PCS_2 THEN
  RW_TAC std_ss [UNROLL_RUNTO] THEN
  `FST (s,pcS0) = FST (s,pcS1)` by RW_TAC std_ss [] THEN
  METIS_TAC [SHORTEST_INDEPENDENT_OF_PCS, STATE_PCS_SEPERATE]
  );


val RUNTO_STILL = Q.store_thm
  ("RUNTO_STILL",
  `!j k instB s.
        terd instB j s ==>
        (runTo instB j (runTo instB j s) =
                 runTo instB j s)`,
   RW_TAC std_ss [terd_def, runTo_FORM1] THEN
   `$~ o (\s:STATEPCS. FST (FST s) = j) = (\s:STATEPCS. ~(FST (FST s) = j))` by RW_TAC std_ss [FUN_EQ_THM] THEN
   METIS_TAC [WHILE_STILL]
  );


val RUNTO_PCS_GROW = Q.store_thm
  ("RUNTO_PCS_GROW",
   `!n j instB s.
        (SND s) SUBSET SND (FUNPOW (step instB) n s)`,
   RW_TAC std_ss [terd_def] THEN
   Q.ID_SPEC_TAC `s` THEN
   Induct_on `n` THENL [
           RW_TAC std_ss [FUNPOW] THEN
               RW_TAC set_ss [Once step_FORM1],
           RW_TAC std_ss [FUNPOW] THEN 
               FULL_SIMP_TAC std_ss [FUNPOW, SIMP_RULE std_ss [FUN_EQ_THM] FUNPOW_FUNPOW] THEN
               POP_ASSUM (ASSUME_TAC o Q.SPECL [`step instB s`]) THEN
               POP_ASSUM MP_TAC THEN
               RW_TAC std_ss [Once step_FORM1] THEN
               `SND s SUBSET (FST (FST s) INSERT SND s)` by RW_TAC set_ss [SUBSET_INSERT_RIGHT] THEN
               METIS_TAC [SUBSET_TRANS]
           ]
   );
  

val RUNTO_PCS_MEMBERS = Q.store_thm
  ("RUNTO_PCS_MEMBERS",
   `!n m instB s. m < n ==>
        FST (FST (FUNPOW (step instB) m s)) IN (SND (FUNPOW(step instB) n s))`,
   Induct_on `n` THEN
   RW_TAC std_ss [] THEN
   Cases_on `m = n` THENL [
       RW_TAC std_ss [FUNPOW_SUC] THEN
       Q.ABBREV_TAC `f = FUNPOW (step instB) m` THEN
       RW_TAC set_ss [Once step_FORM1],
       RW_TAC std_ss [FUNPOW_SUC] THEN
       `m < n` by RW_TAC arith_ss [] THEN
       `SND (FUNPOW (step instB) n s) SUBSET SND (FUNPOW (step instB) (SUC 0) (FUNPOW (step instB) n s))` by METIS_TAC [RUNTO_PCS_GROW]
       THEN FULL_SIMP_TAC set_ss [FUNPOW, SUBSET_DEF]
   ]
 );

val RUNTO_PCS_MEMBERS_2 = Q.store_thm
  ("RUNTO_PCS_MEMBERS_2",
   `!n m instB s pcS. m < n ==>
        FST (FST (FUNPOW (step instB) m (s,pcS))) IN (SND (FUNPOW(step instB) n (s,{})))`,
   Induct_on `n` THEN
   RW_TAC std_ss [] THEN
   Cases_on `m = n` THENL [
       RW_TAC std_ss [FUNPOW_SUC] THEN
       Q.ABBREV_TAC `f = FUNPOW (step instB) m` THEN
       RW_TAC set_ss [Once step_FORM1] THEN
       Q.UNABBREV_TAC `f` THEN
       METIS_TAC [STATE_PCS_SEPERATE, FST],
       RW_TAC std_ss [FUNPOW_SUC] THEN
       `m < n` by RW_TAC arith_ss [] THEN
       `SND (FUNPOW (step instB) n (s,{})) SUBSET SND (FUNPOW (step instB) (SUC 0) (FUNPOW (step instB) n (s,{})))` by METIS_TAC [RUNTO_PCS_GROW]
       THEN FULL_SIMP_TAC set_ss [FUNPOW, SUBSET_DEF]
   ]
 );

val RUNTO_PCS_UNION_LEM = Q.store_thm
  ("RUNTO_PCS_UNION_LEM",
   `!n instB s pcS pcS'.
          pcS' SUBSET SND (FUNPOW (step instB) n (s,pcS)) ==>
          (SND (FUNPOW (step instB) n (s,pcS)) UNION pcS' =
                  (SND (FUNPOW (step instB) n (s, pcS')) UNION pcS))`,
   Induct_on `n` THENL [
       RW_TAC set_ss [FUNPOW, UNION_COMM, SUBSET_UNION_ABSORPTION],

       RW_TAC std_ss [FUNPOW] THEN
       `?s1 pcS1. (step instB) (s,pcS) = (s1,pcS1)` by METIS_TAC [ABS_PAIR_THM] THEN
       Q.PAT_ASSUM `!instB.p` (ASSUME_TAC o Q.SPECL [`instB`,`s1`,`pcS1`, `FST (s:STATE) INSERT pcS'`]) THEN
       `FST (s:STATE) INSERT pcS' SUBSET SND (FUNPOW (step instB) n (s1,pcS1))` by (FULL_SIMP_TAC set_ss [step_def] THEN RW_TAC set_ss [INSERT_SUBSET,
           (SIMP_RULE arith_ss [step_def] o REWRITE_RULE [FUNPOW] o Q.SPECL [`SUC n`, `0`, `instB`,`(s,pcS)`]) RUNTO_PCS_MEMBERS]) THEN
       `step instB (s,pcS') = (s1,FST s INSERT pcS')` by FULL_SIMP_TAC std_ss [step_def] THEN
        RES_TAC THEN
        RW_TAC std_ss [] THEN
       `FST (s:STATE) IN SND (FUNPOW (step instB) n (s1,FST s INSERT pcS'))` by (FULL_SIMP_TAC set_ss [step_def] THEN 
	      RW_TAC set_ss [(SIMP_RULE arith_ss [step_def] o REWRITE_RULE [FUNPOW] o 
              Q.SPECL [`SUC n`, `0`, `instB`,`(s,pcS')`]) RUNTO_PCS_MEMBERS, RUNTO_PCS_GROW]) THEN
       `pcS1 = FST (s:STATE) INSERT pcS` by FULL_SIMP_TAC std_ss [step_def] THEN
       FULL_SIMP_TAC set_ss [] THEN
       METIS_TAC [INSERT_UNION, UNION_COMM]
    ]
   );


val RUNTO_PCS_UNION = Q.store_thm
  ("RUNTO_PCS_UNION",
   `!n instB s pcS. 
       stopAt (\s:STATEPCS.FST (FST s) = j) (step instB) (s,pcS) ==>
       (SND (runTo instB j (s,pcS)) =
            (SND (runTo instB j (s, ({}))) UNION pcS))`,
    RW_TAC std_ss [UNROLL_RUNTO] THEN
    IMP_RES_TAC (Q.SPECL [`pcS`,`{}`,`instB`,`j`,`s`] STOPAT_ANY_PCS_2) THEN
    RW_TAC std_ss [UNROLL_RUNTO] THEN
    METIS_TAC [SHORTEST_INDEPENDENT_OF_PCS, RUNTO_PCS_UNION_LEM, EMPTY_SUBSET, UNION_EMPTY, FST]
   );


val RUNTO_COMPOSITION_LEM = Q.store_thm
  ("RUNTO_COMPOSITION_LEM",
   `!j k instB s0 pcS0.
        terd instB j (s0,pcS0) ==>
        let (s1,pcS1) = runTo instB j (s0,pcS0) in
            ~(k IN ((FST s0) INSERT pcS1)) ==>
                (runTo instB k (s0,pcS0) = runTo instB k (s1,pcS1))`,
  REPEAT GEN_TAC THEN
  Cases_on `k = j` THENL [
      RW_TAC std_ss [] THEN
      METIS_TAC [RUNTO_STILL],

      POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `j` THEN
      Q.ID_SPEC_TAC `s0` THEN  Q.ID_SPEC_TAC `pcS0` THEN
      SIMP_TAC std_ss [terd_def, UNROLL_RUNTO, FORALL_STATE] THEN
      Induct_on `shortest (\s. FST (FST s) = j) (step instB) ((pc,pcsr,regs,mem),pcS0)` THENL [
          REWRITE_TAC [Once EQ_SYM_EQ] THEN
              RW_TAC std_ss [FUNPOW],
          REWRITE_TAC [Once EQ_SYM_EQ] THEN
              REPEAT GEN_TAC THEN
              `?pc1 cpsr1 regs1 mem1 pcS1. step instB ((pc,pcsr,regs,mem),pcS0) = ((pc1,cpsr1,regs1,mem1),pcS1)` by METIS_TAC [ABS_PAIR_THM] THEN
          PAT_ASSUM ``!j instB pcsr regs mem pcS0. P`` (ASSUME_TAC o Q.SPECL [`j`,`instB`,`pc1`,`cpsr1`,`regs1`,`mem1`,`pcS1`]) THEN
          REPEAT STRIP_TAC THEN
          Q.ABBREV_TAC `s0 = (pc,pcsr,regs,mem)` THEN
          Q.ABBREV_TAC `s1 = (pc1,cpsr1,regs1,mem1)` THEN
          `1 <= shortest (\s. FST (FST s) = j) (step instB) (s0,pcS0)` by RW_TAC arith_ss [] THEN
          `shortest (\s. FST (FST s) = j) (step instB) (s0,pcS0) =
              SUC (shortest (\s. FST (FST s) = j) (step instB) (s1,pcS1))` by METIS_TAC [SHORTEST_LEM, SHORTEST_CASES] THEN
          ASM_REWRITE_TAC [FUNPOW] THEN
          FULL_SIMP_TAC std_ss [] THEN

          `stopAt (\s. FST (FST s) = j) (step instB) (FUNPOW (step instB) (SUC 0) (s0,pcS0))` by
               METIS_TAC [ONE, Q.SPECL [`1`,`(\s:STATEPCS. FST (FST s) = j)`]
                          (INST_TYPE [alpha |-> Type `:STATE # (num->bool)`] STOPAT_THM)] THEN
          POP_ASSUM MP_TAC THEN
          ASM_REWRITE_TAC [FUNPOW] THEN
          STRIP_TAC THEN RES_TAC THEN
          `?Sn pcSn. FUNPOW (step instB) v (s1,pcS1) = (Sn,pcSn)` by METIS_TAC [ABS_PAIR_THM] THEN
          FULL_SIMP_TAC std_ss [LET_THM] THEN
          STRIP_TAC THEN
          Q.UNABBREV_TAC `s0` THEN
          Cases_on `pc = k` THENL [
              FULL_SIMP_TAC set_ss [],
              Cases_on `v` THENL [
                  FULL_SIMP_TAC set_ss [FUNPOW] THEN
                      RW_TAC std_ss [runTo_def, Once WHILE],

                  ASSUME_TAC (DECIDE ``n < SUC n``) THEN
                  `FST (FST (FUNPOW (step instB) n (s1,pcS1))) IN pcSn /\ pcS1 SUBSET SND (FUNPOW (step instB) n (s1,pcS1))`
                            by METIS_TAC [RUNTO_PCS_GROW, RUNTO_PCS_MEMBERS, SND] THEN
                  FULL_SIMP_TAC set_ss [] THEN
                   ASSUME_TAC (DECIDE ``0 < SUC n``) THEN
                   IMP_RES_TAC RUNTO_PCS_MEMBERS THEN
                   `FST (FST (s1,pcS1)) IN SND (Sn,pcSn)` by METIS_TAC [FUNPOW] THEN
                   Q.UNABBREV_TAC `s1` THEN
                   FULL_SIMP_TAC set_ss [] THEN
                   `~(k = pc1)` by (ALL_TAC THEN STRIP_TAC THEN (FULL_SIMP_TAC std_ss [IN_DEF])) THEN
                   `runTo instB k ((pc,pcsr,regs,mem),pcS0) = runTo instB k ((pc1,cpsr1,regs1,mem1),pcS1)` by
                                  FULL_SIMP_TAC std_ss [runTo_def, Once WHILE] THEN
                   METIS_TAC []
          ]
        ]
     ]
    ]
  );

       
val RUNTO_COMPOSITION = Q.store_thm
  ("RUNTO_COMPOSITION",
   `!j k instB s0 pcS0 s1 pcS1.
        terd instB j (s0,pcS0) /\ 
        ((s1,pcS1) = runTo instB j (s0,pcS0)) /\
	~(k IN ((FST s0) INSERT pcS1)) ==>
	        (runTo instB k (s0,pcS0) = runTo instB k (s1,pcS1))`,
    RW_TAC std_ss [] THEN
    IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] RUNTO_COMPOSITION_LEM) THEN
    `?s' pcS'. runTo instB j (s0,pcS0) = (s',pcS')` by METIS_TAC [ABS_PAIR_THM] THEN
    FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC [FST,SND]
  );

(*---------------------------------------------------------------------------------*)
(* Restriction on the modelling of registers and memory                            *)
(*---------------------------------------------------------------------------------*)

val in_regs_dom_def = Define `
  in_regs_dom regs = 
      0 IN (FDOM regs) /\ 1 IN (FDOM regs) /\ 2 IN (FDOM regs) /\ 3 IN (FDOM regs) /\
      4 IN (FDOM regs) /\ 5 IN (FDOM regs) /\ 6 IN (FDOM regs) /\ 7 IN (FDOM regs) /\
      8 IN (FDOM regs) /\ 9 IN (FDOM regs) /\ 10 IN (FDOM regs) /\ 11 IN (FDOM regs) /\
      12 IN (FDOM regs) /\ 13 IN (FDOM regs) /\ 14 IN (FDOM regs)`;

  
val in_mem_dom_def = Define `
  in_mem_dom mem = 
       !i:num. i IN (FDOM mem)`;


val FUPDATE_REFL = Q.store_thm
  ("FUPDATE_REFL",
   `!i f. i IN FDOM f ==> (f |+ (i,f ' i) = f)`,
  RW_TAC list_ss [fmap_EXT] THENL [
       RW_TAC list_ss [FDOM_EQ_FDOM_FUPDATE],
       Cases_on `x = i` THEN
       RW_TAC list_ss [FAPPLY_FUPDATE_THM]
  ]
  );

(*------------------------------------------------------------------------------------------------------*)
(* Additional theorems for finite maps                                                                  *)
(*------------------------------------------------------------------------------------------------------*)

(* Sort in ascending order                                                                              *)
val FUPDATE_LT_COMMUTES = Q.store_thm (
  "FUPDATE_LT_COMMUTES",
  ` !f a b c d. c < a ==> (f |+ (a:num, b:word32) |+ (c,d) = f |+ (c,d) |+ (a,b))`,
    RW_TAC arith_ss [FUPDATE_COMMUTES]
    );

(* Sort in descending order                                                                             *)
val FUPDATE_GT_COMMUTES = Q.store_thm (
  "FUPDATE_GT_COMMUTES",
  ` !f a b c d. c > a ==> (f |+ (a:ADDR,b:'b) |+ (c,d) = f |+ (c,d) |+ (a,b))`,
    RW_TAC arith_ss [FUPDATE_COMMUTES]
    );

val _ = export_theory();
