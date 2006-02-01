open HolKernel Parse boolLib bossLib numLib
     arithmeticTheory word32Theory pairTheory listTheory whileTheory finite_mapTheory;

val _ = new_theory "preARM";

(*----------------------------------------------------------------------------*)
(* Preprocessing                                                              *)
(*----------------------------------------------------------------------------*)

(*
val _ = add_rule{term_name   = "COND",
fixity      = Infix (HOLgrammars.RIGHT, 3),
pp_elements = [HardSpace 1, TOK "=>", BreakSpace(1,0), TM, BreakSpace(1,0), TOK "|", HardSpace 1],
paren_style = OnlyIfNecessary,
block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))};
*)

(*
val _ = add_rule{term_name   = "COND",
fixity      = TruePrefix 70,
pp_elements = [PPBlock([TOK "if", BreakSpace(1,2), TM, BreakSpace(1,0),TOK "then"], (CONSISTENT, 0)),
	       BreakSpace(1,2), TM, BreakSpace(1,0), TOK "else", BreakSpace(1,2)],
paren_style = Always,
block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))};
*)

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
                 SN -> MSB cpsr ||
                 SZ -> MSB (cpsr << 1) ||
                 SC -> MSB (cpsr << 2) ||
                 SV -> MSB (cpsr << 3)
        `;

val getS_thm = Q.store_thm (
	"getS_thm",
        `(getS (cpsr : CPSR) SN = MSB cpsr) /\ 
	 (getS (cpsr : CPSR) SZ = MSB (cpsr << 1)) /\
	 (getS (cpsr : CPSR) SC = MSB (cpsr << 2)) /\
	 (getS (cpsr : CPSR) SV = MSB (cpsr << 3))
	`,
	RW_TAC std_ss [getS_def]);


val setS_def = Define
        `setS (cpsr : CPSR) (flag:SRS) =
            case flag of
                 SN -> (cpsr | 0x80000000w) ||
                 SZ -> (cpsr | 0x40000000w) ||
                 SC -> (cpsr | 0x20000000w) ||
                 SV -> (cpsr | 0x10000000w)
        `;

val setS_thm = Q.store_thm (
	"setS_thm",
        `(setS (cpsr : CPSR) SN = (cpsr | 0x80000000w)) /\
	 (setS (cpsr : CPSR) SZ = (cpsr | 0x40000000w)) /\
	 (setS (cpsr : CPSR) SC = (cpsr | 0x20000000w)) /\
	 (setS (cpsr : CPSR) SV = (cpsr | 0x10000000w))
        `,
	RW_TAC std_ss [setS_def]);


(*-------------------------------------------------------------------------------*)
(* Operator			                                                 *)
(*-------------------------------------------------------------------------------*)

val _ = Hol_datatype ` OPERATOR = MOV |
			ADD | SUB | RSB | MUL | MLA |
                        AND | ORR | EOR | CMP | TST |
                        LSL | LSR | ASR | ROR |
                        LDR | STR | LDMFD | STMFD |
                        MRS | MSR |
                        B | BL |
                        SWI
             `;

(*-------------------------------------------------------------------------------*)
(* Condition Codes                                                                      *)
(*-------------------------------------------------------------------------------*)

val _ = Hol_datatype ` COND = EQ | NE | GE | LE | GT | LT | AL | NV`;

(*-------------------------------------------------------------------------------*)
(* Expressions			                                                 *)
(*-------------------------------------------------------------------------------*)

val _ = type_abbrev("ADDR", Type`:num`);

val _ = Hol_datatype `OFFSET = POS of ADDR
               | NEG of ADDR
	       | INR
             `;


val _ = Hol_datatype `EXP = MEM of num # OFFSET			(* (register, offset) *) 
                  | NCONST of num
		  | WCONST of word32
                  | REG of REGISTER
		  | WREG of REGISTER
             `;

val _ = type_abbrev("DATA", Type`:word32`);

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

val FORALL_STATUS = Q.store_thm
  ("FORALL_STATUS",
    `(!s:CPSR # (REGISTER |-> DATA) # (ADDR |-> DATA). P s) = 
	!pcsr regs mem. P (pcsr,(regs,mem))`,
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
(*---------------------------------------------------------------------------------*)

val goto_def =
  Define `
    goto (pc, SOME jump) =
        case jump of
            POS n -> pc + n  || 
            NEG n -> pc - n  ||
	    INR ->   pc
   `;

val goto_thm = Q.store_thm (
  "goto_thm",
  ` (goto (pc, SOME (POS n)) = pc + n) /\
    (goto (pc, SOME (NEG n)) = pc - n) /\
    (goto (pc, SOME INR) = pc)
  `,
  RW_TAC std_ss [goto_def]);


val read_pc = 
  Define `
    read_pc (cpsr,s) = 
		(w2n (read s (REG 15)), cpsr, s)`;

val set_pc =
  Define `
    set_pc s pc =
                (pc, FST s, write (SND s) (REG 15) (n2w pc))`;


val decode1_def = 
  Define `
  decode1 (pc,cpsr,s) (op,dst,src,jump) =
     case op of
          MOV -> (cpsr, write s (THE dst) (read s (HD src)))
              ||

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
          AND -> (cpsr, (write s (THE dst) (read s (HD src) & read s (HD (TL (src))))))
              ||
          ORR -> (cpsr, (write s (THE dst) (read s (HD src) | read s (HD (TL (src))))))
              ||
          EOR -> (cpsr, (write s (THE dst) (read s (HD src) # read s (HD (TL (src))))))
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

          CMP -> if read s (HD src) = read s (HD (TL (src))) then
                      (setS 0w SZ, s)
                 else if read s (HD src) <. read s (HD (TL (src))) then
                      (setS 0w SN, s)
                 else (setS 0w SC, s)
              ||
          TST -> if read s (HD src) & read s (HD (TL (src))) = 0w then
                      (setS cpsr SZ, s)
                 else (cpsr, s)
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

	  B   -> (cpsr, write s (REG 15) (n2w (goto(pc,jump))))
	      || 
          BL ->  (cpsr, write (write s (REG 14) (n2w (pc+1))) (REG 15) (n2w (goto(pc,jump))))
              ||

          _  ->  ARB
  `;

val decode1_thm = Q.store_thm
("decode1_thm",
  `!pc cpsr s dst src jump.
  (decode1 (pc,cpsr,s) (MOV,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src)))) /\
  (decode1 (pc,cpsr,s) (ADD,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) + read s (HD (TL src))))) /\
  (decode1 (pc,cpsr,s) (SUB,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) - read s (HD (TL src))))) /\
  (decode1 (pc,cpsr,s) (RSB,SOME dst,src,jump) = (cpsr, write s dst (read s (HD (TL src)) - read s (HD src)))) /\
  (decode1 (pc,cpsr,s) (MUL,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) * read s (HD (TL src))))) /\
  (decode1 (pc,cpsr,s) (MLA,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) * read s (HD (TL src)) + read s (HD (TL (TL src)))))) /\
  (decode1 (pc,cpsr,s) (AND,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) & read s (HD (TL src))))) /\
  (decode1 (pc,cpsr,s) (ORR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) | read s (HD (TL src))))) /\
  (decode1 (pc,cpsr,s) (EOR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) # read s (HD (TL src))))) /\
  (decode1 (pc,cpsr,s) (CMP,NONE,src,jump) = (if read s (HD src) = read s (HD (TL src))
                                             then (setS 0w SZ,s)
                                             else (if read s (HD src) <. read s (HD (TL src))
                                                   then (setS 0w SN,s)
                                                   else (setS 0w SC,s)))) /\
  (decode1 (pc,cpsr,s) (TST,NONE,src,jump) = (if read s (HD src) & read s (HD (TL src)) = 0w
                                             then (setS cpsr SZ,s) else (cpsr,s))) /\
  (decode1 (pc,cpsr,s) (LSL,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) << w2n (read s (HD (TL src)))))) /\
  (decode1 (pc,cpsr,s) (LSR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) >>> w2n (read s (HD (TL src)))))) /\
  (decode1 (pc,cpsr,s) (ASR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) >> w2n (read s (HD (TL src)))))) /\
  (decode1 (pc,cpsr,s) (ROR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src) #>> w2n (read s (HD (TL src)))))) /\
  (decode1 (pc,cpsr,s) (LDR,SOME dst,src,jump) = (cpsr, write s dst (read s (HD src)))) /\
  (decode1 (pc,cpsr,s) (STR,SOME dst,src,jump) = (cpsr, write s (HD src) (read s dst))) /\
  (decode1 (pc,cpsr,s) (LDMFD, SOME (REG r),src,jump) =
              (cpsr, FST (FOLDL
                          (\(s1,i) reg.
                             (write s1 reg (read s (MEM (r,POS (i + 1)))),
                              i + 1)) (s,0) src))) /\
  (decode1 (pc,cpsr,s) (LDMFD,SOME (WREG r),src,jump) =
              (cpsr, write (FST
                             (FOLDL
                               (\(s1,i) reg.
                                (write s1 reg
                                   (read s (MEM (r,POS (i + 1)))),i + 1))
                               (s,0) src)) (REG r)
                       	     (read s (REG r) + n2w (LENGTH src)))) /\
  (decode1 (pc,cpsr,s) (STMFD,SOME (REG r),src,jump) =
                  (cpsr, FST (FOLDL
                          (\(s1,i) reg.
                             (write s1 (MEM (r,NEG i)) (read s reg),i + 1))
                          (s,0) (REVERSE src)))) /\
  (decode1 (pc,cpsr,s) (STMFD,SOME (WREG r),src,jump) =
                  (cpsr, write (FST
                          (FOLDL
                             (\(s1,i) reg.
                                (write s1 (MEM (r,NEG i)) (read s reg),
                                 i + 1)) (s,0) (REVERSE src))) (REG r)
                       (read s (REG r) - n2w (LENGTH src)))) /\
  (decode1 (pc,cpsr,s) (MRS,SOME dst,src,jump) = (cpsr,write s dst cpsr)) /\
  (decode1 (pc,cpsr,s) (MSR,NONE,src,jump) = (read s (HD src),s)) /\
  (decode1 (pc,cpsr,s) (B,NONE,src,jump) = (cpsr,write s (REG 15) (n2w (goto (pc,jump))))) /\
  (decode1 (pc,cpsr,s) (BL,NONE,src,jump) = (cpsr,write (write s (REG 14) (n2w (pc+1))) (REG 15)
                                                    (n2w (goto (pc,jump)))))`,
 
   RW_TAC std_ss [decode1_def]);
  

  
val decode2_def =
  Define `
    decode2 ((pc,cpsr,s):STATE) (((op,cond,sflag), dst, src, jump):INST) =
        case cond of
            NONE -> set_pc (decode1 (pc,cpsr,s) (op,dst,src,jump)) (pc+1)
                ||
            SOME c -> 
		(case c of 
		     EQ -> if getS cpsr SZ then read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
			    else (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
		 ||  
		     NE -> if getS cpsr SZ then (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
                            else read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
                 ||
            	     GT -> if getS cpsr SC then read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
			   else (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
                 ||
            	     LE -> if getS cpsr SC then (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
			   else read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
                 ||
            	     GE -> if getS cpsr SN then (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
                                     else read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
                 ||  
	             LT -> if getS cpsr SN then read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
                                     else (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
                 ||
		     AL -> read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
                 ||
                     NV -> (pc+1, cpsr, write s (REG 15) (n2w (pc+1)))
		)
  `;

val decode2_thm = Q.store_thm
( "decode2_thm",
  `!pc cpsr s op sflag dst src jump.
  (decode2 (pc,cpsr,s) ((op,NONE,sflag),dst,src,jump) = set_pc (decode1 (pc,cpsr,s) (op,dst,src,jump)) (pc + 1)) /\
  (decode2 (pc,cpsr,s) ((op,SOME EQ,sflag),dst,src,jump) =
              (if getS cpsr SZ then
                 read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
               else
                 (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1))))) /\
  (decode2 (pc,cpsr,s) ((op,SOME NE,sflag),dst,src,jump) =
              (if getS cpsr SZ then
                 (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1)))
               else
                 read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump)))) /\
  (decode2 (pc,cpsr,s) ((op,SOME GE,sflag),dst,src,jump) =
              (if getS cpsr SN then
                 (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1)))
               else
                 read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump)))) /\
  (decode2 (pc,cpsr,s) ((op,SOME LE,sflag),dst,src,jump) =
              (if getS cpsr SC then
                 (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1)))
               else
                 read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump)))) /\
  (decode2 (pc,cpsr,s) ((op,SOME GT,sflag),dst,src,jump) =
              (if getS cpsr SC then
                 read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
               else
                 (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1))))) /\
  (decode2 (pc,cpsr,s) ((op,SOME LT,sflag),dst,src,jump) =
              (if getS cpsr SN then
                 read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))
               else
                 (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1))))) /\
  (decode2 (pc,cpsr,s) ((op,SOME AL,sflag),dst,src,jump) = read_pc (decode1 (pc,cpsr,s) (op,dst,src,jump))) /\
  (decode2 (pc,cpsr,s) ((op,SOME NV,sflag),dst,src,jump) = (pc + 1,cpsr,write s (REG 15) (n2w (pc + 1))))`,
  RW_TAC std_ss [decode2_def]);


(*---------------------------------------------------------------------------------*)
(* Upload instructions into the instruction buffer                                 *)
(*---------------------------------------------------------------------------------*)

(* upload and uploadCode: upload the instructions into the instruction buffer beginning from start                                      *)
(* By default, the code is uploaded to the buffer starting from address 0 (this is what the uploadCode describes                        *)
                                     
val upload_def =
  Define `  
    (upload (stm::rest) iB start =
        \addr. if addr = start then stm
               else (upload rest iB (SUC start)) addr) /\
    (upload ([]) iB start = iB)
  `;
                
val UPLOAD_LEM = Q.store_thm (
  "UPLOAD_LEM",
  `!instL start instB addr. addr < LENGTH instL ==>
	((upload instL instB start) (start+addr) = (upload instL instB 0) addr)`,
  Induct_on `addr` THEN Induct_on `instL` THEN RW_TAC list_ss [upload_def] THEN
  Induct_on `start` THEN RW_TAC list_ss [] THEN
  METIS_TAC [SUC_ADD_SYM, ADD_SYM]
  );         

            
val uploadCode_def =
  Define `uploadCode instL iB = upload instL iB 0`;

                                     
val UPLOADCODE_LEM = Q.store_thm (
   "UPLOADCODE_LEM",
   `!instL instB n. n < LENGTH instL ==>
        ((uploadCode instL instB) n = EL n instL)`,
    SIMP_TAC list_ss [uploadCode_def] THEN Induct_on `n` THEN
    Induct_on `instL` THEN RW_TAC list_ss [upload_def, LENGTH] THEN
    METIS_TAC [SUC_ONE_ADD, UPLOAD_LEM, ADD_SYM]
   );
        
val UPLOAD_THM = Q.store_thm (
    "UPLOAD_THM",
   `!instL instB n. n < LENGTH instL ==>
        ((upload instL instB start) (start+n) = EL n instL)`,
    METIS_TAC [uploadCode_def, UPLOAD_LEM, UPLOADCODE_LEM ]
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
(*---------------------------------------------------------------------------------*)

val (run_def,run_ind) =
 Defn.tprove
  (Hol_defn "run"
    `run n (instB,byn) (pc,cpsr,st) =
        if n = 0 then (pc,cpsr,st)
        else
            if pc = byn then (pc,cpsr,st)
            else
                run (n-1) (instB,byn) (decode2 (pc,cpsr,st) (instB pc))`,
    WF_REL_TAC `measure FST`);

val _ = save_thm("run_def", run_def);
val _ = save_thm("run_ind", run_ind);

val RUN_LEM_1 = Q.store_thm
  ("RUN_LEM_1",
   `!n instB byn s.
        (run (SUC n) (instB,byn) s =
                if FST s = byn then s
                else run n (instB,byn) (decode2 s (instB (FST s)))
        ) /\
        (run 0 (instB,byn) s = s)`,
   SIMP_TAC list_ss [FORALL_STATE] THEN REPEAT GEN_TAC THEN
   RW_TAC list_ss [Once run_def, LET_THM] THENL [
        RW_TAC list_ss [Once run_def, LET_THM],
        RW_TAC list_ss [Once run_def, LET_THM] THEN
        Q.ABBREV_TAC `x = decode2 (pc,pcsr,regs,mem) (instB pc)` THEN
        ` x = (FST x, FST (SND x), SND (SND x))` by RW_TAC list_ss [] THEN
        ONCE_ASM_REWRITE_TAC [] THEN RW_TAC list_ss []]
  );

val RUN_LEM_2 = Q.store_thm
  ("RUN_LEM_2",
   `!n instB s. run n (instB,FST s) s = s`,
   SIMP_TAC list_ss [FORALL_STATE] THEN
   Induct_on `n` THEN RW_TAC list_ss [RUN_LEM_1]
  );

val FORALL_INSTM = Q.store_thm
  ("FORALL_INSTM",
    `(!instM : (num -> INST) # num. P instM) =
        !instB byn. P (instB,byn)`,
    SIMP_TAC std_ss [FORALL_PROD]);

val RUN_THM_1 = Q.store_thm
  ("RUN_THM_1",
   `!m n s instM.
        (run (m+n) instM s = run n instM (run m instM s))`,
  SIMP_TAC std_ss [FORALL_INSTM] THEN
  Induct_on `m` THEN REPEAT GEN_TAC THENL [
        RW_TAC list_ss [RUN_LEM_1],
        `SUC m + n = SUC (m + n)` by RW_TAC list_ss [ADD_SUC] THEN
        ASM_REWRITE_TAC [] THEN RW_TAC list_ss [RUN_LEM_1] THEN
        RW_TAC list_ss [RUN_LEM_2]]
  );

val RUN_THM_2 = Q.store_thm
  ("RUN_THM_2",
   `!m n s instM. m <= n ==>
        (run n instM s = run (n-m) instM (run m instM s))`,
  RW_TAC list_ss [FORALL_INSTM] THEN `?k. n = k + m` by PROVE_TAC [LESS_EQUAL_ADD, ADD_SYM] THEN
  ASM_REWRITE_TAC [] THEN METIS_TAC [SUB_ADD, RUN_THM_1, ADD_SYM]
  );

val RUN_ONE_STEP = Q.store_thm
  ("RUN_ONE_STEP",
   `!instB byn pc cpsr st. run 1 (instB,byn) (pc,cpsr,st) = 
            if pc = byn then (pc,cpsr,st)
            else
                decode2 (pc,cpsr,st) (instB pc)`,
  RW_TAC std_ss [Once run_def] THEN
  RW_TAC std_ss [RUN_LEM_1]
  );


val _ = Globals.priming := NONE;

(*---------------------------------------------------------------------------------*)
(* Run for the minimum number of steps to stop at a given position                 *)
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

(*---------------------------------------------------------------------------------*)
(* Termination and minimum number of steps                                         *)
(*---------------------------------------------------------------------------------*)

(* terminate: specifies that the execution of instructions would terminates at the label (pc0+len) within n steps               *)

val terminated_def =
 Define
   `terminated (instB,byn) s = ?n. FST (run n (instB,byn) s) = byn`;


val TERMINATED_THM = Q.store_thm
  ("TERMINATED_THM",
   `!m s iB byn n.
       terminated (iB,byn) s ==> terminated (iB,byn) (run m (iB,byn) s)`,
  RW_TAC list_ss [terminated_def, GSYM RUN_THM_1] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  RW_TAC list_ss [RUN_THM_1] THEN
  Q.EXISTS_TAC `n` THEN
  METIS_TAC [RUN_LEM_2]
  );

(* minStep is the minimum number of steps for the program to terminate                                                           *)

val minStep_def =
  Define `minStep (instB,byn) s = LEAST n. FST (run n (instB,byn) s) = byn`;


val MINSTEP_THM = Q.store_thm
  ("MIN_STEP_THM",
   `!s instB byn m.
       (terminated (instB,byn) s) /\
       (m <= minStep (instB,byn) s) ==>
       (minStep (instB,byn) s = (minStep (instB,byn) (run m (instB,byn) s) + m))`,
    RW_TAC list_ss [terminated_def, minStep_def] THEN
    RW_TAC list_ss [ONCE_REWRITE_RULE [EQ_SYM_EQ] RUN_THM_1] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    HO_MATCH_MP_TAC LEAST_ADD_LEM THEN
    METIS_TAC []
  );

(*---------------------------------------------------------------------------------*)
(*                    Run to a particular position                                 *)
(*---------------------------------------------------------------------------------*)

val runTo_def = Define `
  !instB byn s pcS.
  runTo instB byn s =
      WHILE (\s. ~(FST s = byn))
           (\s. decode2 s (instB (FST s))) s`;

val RUNTO_LEM_1 = Q.store_thm
  ("RUNTO_LEM_1",
   `!n instB byn s.
       runTo instB byn s =
           if FST s = byn then s
           else runTo instB byn (decode2 s (instB (FST s)))`,
   REPEAT STRIP_TAC THEN Cases_on `FST s = byn` THENL [
       RW_TAC list_ss [runTo_def, Once WHILE],
       RW_TAC list_ss [runTo_def, Once WHILE]]
  );

val RUNTO_LEM_2 = Q.store_thm
  ("RUNTO_LEM_2",
   `!instB s pcS. runTo instB (FST s) s = s`,
   METIS_TAC [RUNTO_LEM_1]
  );


val RUNTO_AFTER_N_STEPS = Q.store_thm
  ("RUNTO_AFTER_N_STEPS",
   `!m instB byn s. runTo instB byn s = runTo instB byn (run m (instB,byn) s)`,
    Induct_on `m` THENL [
        RW_TAC list_ss [RUN_LEM_1],
        REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN 
        ASSUME_TAC ( REWRITE_RULE [ADD_SYM, GSYM SUC_ONE_ADD] (Q.SPECL [`m`, `1`] RUN_THM_1)) THEN
        `1 = SUC 0` by SIMP_TAC std_ss [] THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [Once RUN_LEM_1] THEN
        REWRITE_TAC [Once RUN_LEM_1] THEN
        STRIP_TAC THEN
        Cases_on `FST (run m (instB,byn) s) = byn` THENL [
            METIS_TAC [],
            METIS_TAC [RUNTO_LEM_1]
        ]
    ]
   );

(*
val RUNTO_THM = Q.store_thm
  ("RUNTO_THM",
   `!k instB t s0 s1 pcS0 pcS1. (((s1,pcS1) = run instB k (s0,pcS0)) /\ ~(t IN pcS1)) ==>
        (run instB t (s0,pcS0) = run instB t (s1,pcS1))`,

    RW_TAC list_ss [runTo_def, minStep_def, stopAt_def] THEN
    LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
        METIS_TAC [],
        LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
             REWRITE_TAC [GSYM RUN_THM_1] THEN
             Q.EXISTS_TAC `0` THEN
             RW_TAC arith_ss [],
             METIS_TAC [RUN_LEM_2]]
    ]
   );
*)


(*
val runTo_def = Define `
  !instB byn s pcS.
  runTo instB byn (s,pcS) =
      WHILE (\(s,pcS). ~(FST s = byn))
           (\(s,pcS). (decode2 s (instB (FST s)),FST s INSERT pcS)) (s,pcS)`;

val RUNTO_LEM_1 = Q.store_thm
  ("RUNTO_LEM_1",
   `!n instB byn s.
       runTo instB byn (s,pcS) =
           if FST s = byn then (s,pcS)
           else runTo instB byn (decode2 s (instB (FST s)), (FST s) INSERT pcS)`,
   REPEAT STRIP_TAC THEN Cases_on `FST s = byn` THENL [
       RW_TAC list_ss [runTo_def, Once WHILE],
       RW_TAC list_ss [runTo_def, Once WHILE]]
  );

val RUNTO_LEM_2 = Q.store_thm
  ("RUNTO_LEM_2",
   `!instB s pcS. runTo instB (FST s) (s,pcS) = (s,pcS)`,
   METIS_TAC [RUN_LEM_1]
  );


val RUNTO_THM_1 = Q.store_thm
  ("RUNTO_THM_1",
   `!m instB byn s. runTo instB byn (run m (instB,byn) s)`,

    RW_TAC list_ss [runTo_def, minStep_def, stopAt_def] THEN
    LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
        METIS_TAC [],

        LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
             REWRITE_TAC [GSYM RUN_THM_1] THEN
             Q.EXISTS_TAC `0` THEN
             RW_TAC arith_ss [],
             METIS_TAC [RUN_LEM_2]]
    ]
   );


val RUNTO_THM_1 = Q.store_thm
  ("RUNTO_THM_1",
   `!k instB t s0 s1 pcS0 pcS1. (((s1,pcS1) = run instB k (s0,pcS0)) /\ ~(t IN pcS1)) ==>
        (run instB t (s0,pcS0) = run instB t (s1,pcS1))`,

    RW_TAC list_ss [runTo_def, minStep_def, stopAt_def] THEN
    LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
        METIS_TAC [],
        LEAST_ELIM_TAC THEN RW_TAC list_ss [] THENL [
             REWRITE_TAC [GSYM RUN_THM_1] THEN
             Q.EXISTS_TAC `0` THEN
             RW_TAC arith_ss [],
             METIS_TAC [RUN_LEM_2]]
    ]
   );

*)

(*---------------------------------------------------------------------------------*)
(* A breakpoint of the problem is at the critical path iff it is at the shorest    *)
(* runnning path of an execution                                                   *)
(*---------------------------------------------------------------------------------*)

(*
val atCritPath_def =
  Define `atCritPath p t instM s = 
         minStep2 p instM s +  minStep2 t instM (runTo p instM s) <= minStep2 t instM s`;

val ATCRITPATH_LEM = Q.store_thm
  ("ATCRITPATH_LEM",
   `!p t instM s. 
    atCritPath p t instM s ==>     
        minStep2 p instM s <= minStep2 t instM s /\ minStep2 t instM (runTo p instM s) <= minStep2 t instM s`,
    RW_TAC list_ss [atCritPath_def]
  );
*)

(*---------------------------------------------------------------------------------*)
(* Run to termination                                                              *)
(*---------------------------------------------------------------------------------*)

val terRun_def =
  Define
   `terRun (instB,byn) s = runTo instB byn s`;

val TERRUN_THM = Q.store_thm
  ("TERRUN_THM",
   `!m s iB byn n.
        (terRun (iB,byn) s = terRun (iB,byn) (run m (iB,byn) s))`,
   RW_TAC arith_ss [terRun_def, RUNTO_AFTER_N_STEPS]
  );

val TERRUN_STOP = Q.store_thm
  ("TERRUN_STOP",
   `!s iB byn. (FST s = byn) ==>
        (terRun (iB,byn) s = s)`,
  RW_TAC list_ss [terRun_def] THEN
  RW_TAC list_ss [RUNTO_LEM_2]
  );

(*---------------------------------------------------------------------------------*)
(* ARM program destruction                                                         *)
(*---------------------------------------------------------------------------------*)

(* Theorem of Sequential Composition                                      			                                  *)
(*
val RUN_LEM_1 = Q.prove (
    `!blk m start status.
	(FST (runL m blk (start,status)) + start = FST (run m (upload blk start) (start,status))) /\
	(SND (runL m blk (start,status)) = SND (run m (upload blk start) (start,status)))`,
     SIMP_TAC std_ss [FORALL_STATUS] THEN 
     RW_TAC list_ss [runL_def, uploadCode_def] THEN Induct_on `m` THENL [
	RW_TAC list_ss [run_def],

	RW_TAC list_ss [run_def, LET_THM] THEN POP_ASSUM (ASSUME_TAC o SYM) THEN
	ASM_REWRITE_TAC [] THEN 

	RW_TAC list_ss [runL_def, run_def],


val SEQ_COMP = Q.prove (
    `!blk1 blk2 m1 m2 s. e1e1 m1 blk1 s ==>
        (SND (runL m2 blk2 (runL m1 blk1 s)) = SND (runL (m1+m2) (blk1 ++ blk2) s))`,
    SIMP_TAC std_ss [FORALL_STATE] THEN Induct_on `m2` THENL [
    RW_TAC list_ss [e1e1_def] THEN RW_TAC list_ss [Once runL_def, run_def],
    
  );

   
val COND_COMP = Q.prove (
    `(terminate cond /\ terminate tblk /\ terminate fblk) ==>
        !s. ?m1 m2 m3. runL m3 (cond ++ tblk ++ fblk) s =
                let c = runL m0 cond s in
                if getCond c then runL m1 tblk c
                else runL m2 fblk c`,
*)

val EL_THM = Q.prove
  (`!n:num. EL n (h::t) = (if n > 0 then EL (PRE n) t else h)`,
    Cases_on `n` THEN RW_TAC list_ss [EL]
  );




(*---------------------------------------------------------------------------------*)
(* Restriction on the modelling of registers and memory                            *)
(*---------------------------------------------------------------------------------*)

val in_regs_dom_def = Define `
  in_regs_dom regs = 
      0 IN (FDOM regs) /\ 1 IN (FDOM regs) /\ 2 IN (FDOM regs) /\ 3 IN (FDOM regs) /\
      4 IN (FDOM regs) /\ 5 IN (FDOM regs) /\ 6 IN (FDOM regs) /\ 7 IN (FDOM regs) /\
      8 IN (FDOM regs) /\ 9 IN (FDOM regs) /\ 10 IN (FDOM regs) /\ 11 IN (FDOM regs) /\
      12 IN (FDOM regs) /\ 13 IN (FDOM regs) /\ 14 IN (FDOM regs) /\ 15 IN (FDOM regs)`;

  
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

(*---------------------------------------------------------------------------------*)
(* Bisimulation. Compare source codes and  ARM codes synchronously                 *)
(*---------------------------------------------------------------------------------*)

val _ = export_theory();
