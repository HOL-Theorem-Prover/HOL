(*
  quietdec := true;
  val armDir = concat Globals.HOLDIR "/examples/elliptic/arm";
  val yaccDir = concat Globals.HOLDIR "/tools/mlyacc/mlyacclib";
  loadPath := !loadPath @ [armDir,yaccDir];
  loadPath := "/home/mom22/machine-code" :: !loadPath;
*)

open HolKernel boolLib bossLib;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open arm_evalTheory armTheory listTheory bsubstTheory pairTheory; 

open set_sepTheory progTheory;

(*
  quietdec := false;
*)


val _ = new_theory "arm_prog";

val _ = Parse.hide "regs"

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;


(* ----------------------------------------------------------------------------- *)
(* Some abbreviating definitions for ARM                                         *)
(* ----------------------------------------------------------------------------- *)

val state_mode_def = Define `
  state_mode s = DECODE_MODE ((4 >< 0) (CPSR_READ s.psrs))`;

val reg_def = Define `
  reg r s = if r = 15w then s.registers r15 else REG_READ s.registers (state_mode s) r`;

val mem_def = Define `mem a s = s.memory a`;

val statusN_def = Define `statusN s = CPSR_READ s.psrs %% 31`;
val statusZ_def = Define `statusZ s = CPSR_READ s.psrs %% 30`;
val statusC_def = Define `statusC s = CPSR_READ s.psrs %% 29`;
val statusV_def = Define `statusV s = CPSR_READ s.psrs %% 28`;
val status_def = Define `status s = (statusN s,statusZ s,statusC s,statusV s)`;

val set_status_def = Define `
  set_status (n,z,c,v) s = CPSR_WRITE s.psrs (SET_NZCV (n,z,c,v) (CPSR_READ s.psrs))`;

val status_THM = store_thm("status_THM",
  ``!s. status s = NZCV (CPSR_READ s.psrs)``,
  REWRITE_TAC [status_def,NZCV_def,statusN_def,statusZ_def,statusC_def,statusV_def]);


(* ----------------------------------------------------------------------------- *)
(* The ARM set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  ARMel =  Reg of word4 => word32
         | Mem of word30 => word32  
         | Status of bool # bool # bool # bool
         | Undef of bool
         | Rest of arm_mem_state`;

val ARMel_11 = DB.fetch "-" "ARMel_11";
val ARMel_distinct = DB.fetch "-" "ARMel_distinct";

val _ = Parse.type_abbrev("ARMset",``:ARMel set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from ARM to ARMset                                                 *)
(* ----------------------------------------------------------------------------- *)

(* Erasing registers *)

val REG_OWRT_def = Define `
  (REG_OWRT 0 regs m = regs) /\ 
  (REG_OWRT (SUC n) regs m = REG_OWRT n (REG_WRITE regs m (n2w n) 0w) m)`;

val REG_OWRT_LEMMA = prove(
  ``!n k regs. 
       w2n k < n ==> 
        (REG_OWRT n (REG_WRITE regs m k x) m = REG_OWRT n regs m)``,
  Induct_on `n` << [
    `!n. ~(n<0)` by DECIDE_TAC
    \\ ASM_REWRITE_TAC [REG_OWRT_def],
    REPEAT STRIP_TAC
    \\ REWRITE_TAC [REG_OWRT_def]
    \\ Cases_on `n = w2n k` << [
      ASM_REWRITE_TAC [n2w_w2n,REG_WRITE_WRITE],
      `w2n k < n` by DECIDE_TAC
      \\ Cases_on `n2w n = k` << [
         ASM_REWRITE_TAC [REG_WRITE_WRITE],
         METIS_TAC [REG_WRITE_WRITE_COMM]]]]);
    
val REG_OWRT_WRITE = prove(
  ``!regs m k x. REG_OWRT 16 (REG_WRITE regs m k x) m = REG_OWRT 16 regs m``,
  ASSUME_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:i4``] w2n_lt))
  \\ METIS_TAC [REG_OWRT_LEMMA]);

val REG_OWRT_WRITEL = prove(
  ``!xs regs m. REG_OWRT 16 (REG_WRITEL regs m xs) m = REG_OWRT 16 regs m``,
  Induct \\ REWRITE_TAC [REG_WRITEL_def,REG_OWRT_WRITE] \\ Cases_on `h`
  \\ ASM_REWRITE_TAC [REG_WRITEL_def,REG_OWRT_WRITE]);

val REG_OWRT_WRITE_PC = prove(
  ``!regs m. REG_OWRT 16 (REG_WRITE regs usr 15w z) m = REG_OWRT 16 regs m``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [REG_OWRT_def,GSYM (EVAL ``SUC 15``)]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x m = f y m)``)
  \\ SIMP_TAC std_ss [REG_WRITE_def,mode_reg2num_def,EVAL ``w2n (15w:word4)``]
  \\ SIMP_TAC std_ss [LET_DEF,num2register_thm]
  \\ SRW_TAC [] [FUN_EQ_THM,SUBST_def]);
    
val REG_OWRT_INC_PC = prove(
  ``!regs m. REG_OWRT 16 (INC_PC regs) m = REG_OWRT 16 regs m``,
  REWRITE_TAC [INC_PC,REG_OWRT_WRITE_PC]);

val REG_OWRT_ALL = save_thm("REG_OWRT_ALL",
  GEN_ALL (CONJ (SPEC_ALL REG_OWRT_INC_PC) 
                (CONJ (SPEC_ALL REG_OWRT_WRITE_PC) 
                      (CONJ (SPEC_ALL REG_OWRT_WRITE) 
                            (SPEC_ALL REG_OWRT_WRITEL)))));

val REG_OWRT_ALL_EQ_REG_WRITEL = prove( 
  ``REG_OWRT 16 regs m = 
    REG_WRITEL regs m [(0w,0w);(1w,0w);(2w,0w);(3w,0w);(4w,0w);(5w,0w);(6w,0w);
                       (7w,0w);(8w,0w);(9w,0w);(10w,0w);(11w,0w);(12w,0w);(13w,0w);
                       (14w,0w);(15w,0w)]``,
  REWRITE_TAC [REG_WRITEL_def]
  \\ REWRITE_TAC [GSYM (EVAL ``SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 
                              (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))))))``)]
  \\ REWRITE_TAC [REG_OWRT_def]
  \\ SIMP_TAC std_ss []);

val owrt_visible_regs_def = Define `
  owrt_visible_regs s = REG_OWRT 16 s.registers (state_mode s)`;

val owrt_visible_def = Define `
  owrt_visible s = <| registers := owrt_visible_regs s;
                      psrs := set_status (F,F,F,F) s;
                      memory := (\a. 0w); 
                      undefined := F|>`;


(* Main definition *)

val arm2set_def = Define `
  arm2set s =
    { Reg a (reg a s) |a| T } UNION
    { Mem a (mem a s) |a| T } UNION
    { Status (status s); Undef s.undefined; Rest (owrt_visible s) }`;


(* ----------------------------------------------------------------------------- *)
(* Converting from ARMset to ARM                                                 *)
(* ----------------------------------------------------------------------------- *)

val ARMsets_def = Define `ARMsets = { arm2set s |s| T }`;

val set2undef_def = Define `
  set2undef set = @u. Undef u IN set`;

val set2psrs_def = Define `
  set2psrs set = set_status (@s. Status s IN set) (@r. Rest r IN set)`;

val set2mem_def = Define `
  set2mem set = @f. !a x. Mem a x IN set ==> (f a = x)`;

val set2mode_def = Define `
  set2mode set = state_mode (@r. Rest r IN set)`;

val set2reg_def = Define `
  set2reg r set = @x. Reg r x IN set`;

val set2regs_def = Define `
  set2regs set = 
    REG_WRITEL (@r. Rest r IN set).registers (set2mode set)
      (MAP (\x. (x,set2reg x set)) 
        [15w;14w;13w;12w;11w;10w;9w;8w;7w;6w;5w;4w;3w;2w;1w;0w])`;

val set2arm_def = Define `
  set2arm set = <| registers := set2regs set;
                   psrs := set2psrs set;
                   memory := set2mem set; 
                   undefined := set2undef set |>`;

val set2undef_arm2set = prove(
  ``!s. set2undef (arm2set s) = s.undefined``,
  SRW_TAC [] [set2undef_def,arm2set_def]);

val set2mem_arm2set = prove(
  ``!s. set2mem (arm2set s) = s.memory``,
  SRW_TAC [] [set2mem_def,arm2set_def,mem_def] \\ METIS_TAC []);

val set2psrs_arm2set = prove(
  ``!s. set2psrs (arm2set s) = s.psrs``,
  SRW_TAC [] [set2psrs_def,arm2set_def]
  \\ SRW_TAC [] [set_status_def,status_def,statusN_def,
                 statusZ_def,statusC_def,statusV_def,owrt_visible_def]
  \\ CONV_TAC arm_rulesLib.PSR_CONV
  \\ REWRITE_TAC []);

val set2mode_arm2set = prove(
  ``!s. set2mode (arm2set s) = state_mode s``,
  SRW_TAC [] [set2mode_def,arm2set_def]
  \\ SRW_TAC [] [state_mode_def,owrt_visible_def,set_status_def]
  \\ CONV_TAC arm_rulesLib.PSR_CONV
  \\ REWRITE_TAC []);
  
val REG_WRITE_ELIM = prove(
  ``!s x. REG_WRITE s.registers (state_mode s) x (reg x s) = s.registers``,
  REPEAT STRIP_TAC
  \\ Cases_on `x = 15w`
  \\ ASM_SIMP_TAC std_ss [reg_def] << [
    SRW_TAC [] [REG_WRITE_def,mode_reg2num_def,EVAL ``w2n (15w:word4)``]
    \\ Q.UNABBREV_TAC `n`
    \\ SRW_TAC [] [SUBST_def,FUN_EQ_THM,num2register_thm],
    ASM_REWRITE_TAC [REG_READ_def]
    \\ ASM_REWRITE_TAC [REG_WRITE_def,SUBST_def]
    \\ SRW_TAC [] [FUN_EQ_THM]]);

fun MK_WRITE_WRITE_COMM x y =
  let 
    val th = SPEC_ALL REG_WRITE_WRITE_COMM
    val th = Q.INST [`n1`|->y,`n2`|->x] th
    val th = CONV_RULE (RATOR_CONV EVAL) th
  in
    BETA_RULE th
  end;

fun MK_WRITE_WRITEs [] = []
  | MK_WRITE_WRITEs (x::xs) =
    let
      val rw = map (fn y => MK_WRITE_WRITE_COMM x y) xs 
    in
      rw @ MK_WRITE_WRITEs xs
    end;

val WRITE_WRITE_ss = 
  rewrites(MK_WRITE_WRITEs 
           [`0w`,`1w`,`2w`,`3w`,`4w`,`5w`,`6w`,`7w`,`8w`,`9w`,`10w`,`11w`,`12w`,`13w`,`14w`,`15w`]);

val set2regs_arm2set_LEMMA = prove(
  ``REG_WRITEL
      (REG_WRITEL s.registers (state_mode s)
         [(0w,0w); (1w,0w); (2w,0w); (3w,0w); (4w,0w); (5w,0w); (6w,0w);
          (7w,0w); (8w,0w); (9w,0w); (10w,0w); (11w,0w); (12w,0w); (13w,0w);
          (14w,0w); (15w,0w)]) (state_mode s)
      [(15w,reg 15w s); (14w,reg 14w s); (13w,reg 13w s); (12w,reg 12w s);
       (11w,reg 11w s); (10w,reg 10w s); (9w,reg 9w s); (8w,reg 8w s);
       (7w,reg 7w s); (6w,reg 6w s); (5w,reg 5w s); (4w,reg 4w s);
       (3w,reg 3w s); (2w,reg 2w s); (1w,reg 1w s); (0w,reg 0w s)] =
    REG_WRITEL s.registers (state_mode s)
      [(0w,reg 0w s); (1w,reg 1w s); (2w,reg 2w s); (3w,reg 3w s);
       (4w,reg 4w s); (5w,reg 5w s); (6w,reg 6w s); (7w,reg 7w s);
       (8w,reg 8w s); (9w,reg 9w s); (10w,reg 10w s); (11w,reg 11w s);
       (12w,reg 12w s); (13w,reg 13w s); (14w,reg 14w s); (15w,reg 15w s)]``,
  SIMP_TAC (bool_ss++WRITE_WRITE_ss) [REG_WRITE_WRITE,REG_WRITEL_def]);
  
val set2regs_arm2set = prove(
  ``!s. set2regs (arm2set s) = s.registers``,
  SRW_TAC [] [set2regs_def,set2mode_arm2set]
  \\ SRW_TAC [] [arm2set_def,owrt_visible_regs_def,owrt_visible_def,set2reg_def]
  \\ REWRITE_TAC [REG_OWRT_ALL_EQ_REG_WRITEL]
  \\ REWRITE_TAC [set2regs_arm2set_LEMMA] (* alternatively use: REG_WRITEL_CONV *)
  \\ REWRITE_TAC [REG_WRITEL_def,REG_WRITE_ELIM]);


(* lemmas *)

val set2arm_arm2set = store_thm("set2arm_arm2set",
  ``!s. set2arm (arm2set s) = s``,
  SRW_TAC [] [set2arm_def,set2undef_arm2set,set2mem_arm2set,
              set2regs_arm2set,set2psrs_arm2set]
  \\ SRW_TAC [] [arm_mem_state_component_equality]);

val arm2set_set2arm = store_thm("arm2set_set2arm",
  ``!s::ARMsets. arm2set (set2arm s) = s``,
  SRW_TAC [] [RES_FORALL,ARMsets_def] \\ REWRITE_TAC [set2arm_arm2set]);


(* ----------------------------------------------------------------------------- *)
(* Definitions of partial arm2set                                                *)
(* ----------------------------------------------------------------------------- *)

val arm2set'_def = Define `
  arm2set' (rs,ns,st,ud,rt) s =
    { Reg a (reg a s) | a IN rs } UNION
    { Mem a (mem a s) | a IN ns } UNION
    (if st then { Status (status s) } else {}) UNION
    (if ud then { Undef s.undefined } else {}) UNION
    (if rt then { Rest (owrt_visible s) } else {})`;

val arm2set''_def = Define `
  arm2set'' x s = arm2set s DIFF arm2set' x s`;


(* lemmas with INSERT, IN and DELETE ------------------------------------------- *)

val PUSH_IN_INTO_IF = prove(
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``,
  METIS_TAC []);

val IN_arm2set = store_thm("IN_arm2set",``
  (!r x s. Reg r x IN (arm2set s) = (x = reg r s)) /\
  (!p x s. Mem p x IN (arm2set s) = (x = mem p s)) /\
  (!x s. Status x IN (arm2set s) = (x = status s)) /\
  (!x s. Undef x IN (arm2set s) = (x = s.undefined)) /\
  (!x s. Rest x IN (arm2set s) = (x = owrt_visible s))``,
  SRW_TAC [] [arm2set_def,IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]);

val IN_arm2set' = store_thm("IN_arm2set'",``
  (!r x s. Reg r x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = reg r s) /\ (r IN rs))) /\
  (!p x s. Mem p x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = mem p s) /\ (p IN ns))) /\
  (!x s. Status x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = status s) /\ st)) /\
  (!x s. Undef x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = s.undefined) /\ ud)) /\
  (!x s. Rest x IN (arm2set' (rs,ns,st,ud,rt) s) = ((x = owrt_visible s) /\ rt))``,
  SRW_TAC [] [arm2set'_def,IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,
              PUSH_IN_INTO_IF] \\ METIS_TAC []);

val IN_arm2set'' = store_thm("IN_arm2set''",``
  (!r x s. Reg r x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = reg r s) /\ ~(r IN rs))) /\
  (!p x s. Mem p x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = mem p s) /\ ~(p IN ns))) /\
  (!x s. Status x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = status s) /\ ~st)) /\
  (!x s. Undef x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = s.undefined) /\ ~ud)) /\
  (!x s. Rest x IN (arm2set'' (rs,ns,st,ud,rt) s) = ((x = owrt_visible s) /\ ~rt))``,
  SRW_TAC [] [arm2set'_def,arm2set''_def,arm2set_def,IN_UNION,GSPECIFICATION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

val INSERT_arm2set' = store_thm("INSERT_arm2set'",``
  (!r x s. arm2set' (r INSERT rs,ns,st,ud,rt) s = 
           Reg r (reg r s) INSERT arm2set' (rs,ns,st,ud,rt) s) /\
  (!p x s. arm2set' (rs,p INSERT ns,st,ud,rt) s = 
           Mem p (mem p s) INSERT arm2set' (rs,ns,st,ud,rt) s) /\
  (!x s. arm2set' (rs,ns,T,ud,rt) s = 
           Status (status s) INSERT arm2set' (rs,ns,F,ud,rt) s) /\
  (!x s. arm2set' (rs,ns,st,T,rt) s = 
           Undef (s.undefined) INSERT arm2set' (rs,ns,st,F,rt) s) /\
  (!x s. arm2set' (rs,ns,st,ud,T) s = 
           Rest (owrt_visible s) INSERT arm2set' (rs,ns,st,ud,F) s) /\
  (!s. arm2set' ({},{},F,F,F) s = {})``,
  SRW_TAC [] [EXTENSION] \\ Cases_on `x` \\  SRW_TAC [] [IN_arm2set']
  \\ METIS_TAC []);

val DELETE_arm2set' = store_thm("DELETE_arm2set'",``
  (!r p s. (arm2set' (rs,ns,st,ud,rt) s) DELETE Reg r (reg r s) = 
           (arm2set' (rs DELETE r,ns,st,ud,rt) s)) /\
  (!r p s. (arm2set' (rs,ns,st,ud,rt) s) DELETE Mem p (mem p s) = 
           (arm2set' (rs,ns DELETE p,st,ud,rt) s)) /\
  (!x s.   (arm2set' (rs,ns,st,ud,rt) s) DELETE Status (status s) = 
            arm2set' (rs,ns,F,ud,rt) s) /\
  (!x s.   (arm2set' (rs,ns,st,ud,rt) s) DELETE Undef (s.undefined) = 
            arm2set' (rs,ns,st,F,rt) s) /\
  (!x s.   (arm2set' (rs,ns,st,ud,rt) s) DELETE Rest (owrt_visible s) = 
            arm2set' (rs,ns,st,ud,F) s)``,
  SRW_TAC [] [arm2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val arm2set''_THM = prove(
  ``arm2set'' (rs,ns,st,ud,rt) s =
    {Reg a (reg a s) |a| ~(a IN rs)} UNION 
    {Mem a (mem a s) |a| ~(a IN ns)} UNION
    (if ~ st then {Status (status s)} else {}) UNION
    (if ~ ud then {Undef s.undefined} else {}) UNION
    (if ~ rt then {Rest (owrt_visible s)} else {})``,
  REWRITE_TAC [arm2set''_def,arm2set'_def,EXTENSION,arm2set_def]
  \\ FULL_SIMP_TAC bool_ss 
        [IN_UNION,IN_DIFF,IN_INSERT,NOT_IN_EMPTY,GSPECIFICATION,PAIR_EQ]
  \\ STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [
    METIS_TAC [],
    METIS_TAC [],
    Cases_on `st` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    Cases_on `ud` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    Cases_on `rt` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],
    `!k. ?a. x = Reg a (reg a s)` by METIS_TAC []
    \\ SRW_TAC [] [] \\ METIS_TAC [],    
    `!k. ?a. x = Mem a (mem a s)` by METIS_TAC []
    \\ SRW_TAC [] [] \\ METIS_TAC [],
    Cases_on `st` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] [],
    Cases_on `ud` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] [],    
    Cases_on `rt` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] []]);

val arm2set''_EQ = store_thm ("arm2set''_EQ", 
  ``!rs ns st ud rt s s'.
      (arm2set'' (rs,ns,st,ud,rt) s = arm2set'' (rs,ns,st,ud,rt) s') = 
	(!r. (~(r IN rs)) ==> (arm_prog$reg r s = arm_prog$reg r s')) /\
	(!p. (~(p IN ns)) ==> (arm_prog$mem p s = arm_prog$mem p s')) /\
	((~st) ==> (status s = status s')) /\
	((~ud) ==> (s.undefined = s'.undefined)) /\
	((~rt) ==> (owrt_visible s = owrt_visible s'))``,
  SIMP_TAC std_ss [arm2set''_THM, EXTENSION, IN_UNION, IN_DIFF, IN_INSERT, 
    NOT_IN_EMPTY, GSPECIFICATION, 
    prove (``x IN (if c then S1 else S2) = if c then x IN S1 else x IN S2``, PROVE_TAC[])] 
  \\ REPEAT GEN_TAC \\ EQ_TAC << [
    REPEAT STRIP_TAC \\ CCONTR_TAC \\ Q.PAT_ASSUM `!x. P x` MP_TAC \\ SIMP_TAC std_ss [] << [
      Q_TAC EXISTS_TAC `Reg r (arm_prog$reg r s)` 
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q_TAC EXISTS_TAC `Mem p (arm_prog$mem p s)`
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q_TAC EXISTS_TAC `Status (status s)`
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q_TAC EXISTS_TAC `Undef s.undefined`
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct],
      Q_TAC EXISTS_TAC `Rest (owrt_visible s)` 
      \\ FULL_SIMP_TAC std_ss [ARMel_11, ARMel_distinct]],
    SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC 
    \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [ARMel_11, ARMel_distinct]]);


(* lemmas with SPLIT and STAR -------------------------------------------------- *)
 
val SPLIT_DIFF = prove(
  ``!s u. u SUBSET s ==> SPLIT s (u,s DIFF u)``,
  SRW_TAC [] [SPLIT_def,SUBSET_DEF,EXTENSION,IN_UNION,IN_DIFF,DISJOINT_DEF] 
  \\ METIS_TAC []);

val arm2set'_SUBSET_arm2set = prove(
  ``!x s. arm2set' x s SUBSET arm2set s``,
  REWRITE_TAC [SUBSET_DEF]
  \\ STRIP_TAC 
  \\ `?rs ms st ud rt. x = (rs,ms,st,ud,rt)` by METIS_TAC [PAIR]  
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [arm2set'_def,arm2set_def,SUBSET_DEF]);  
  
val SPLIT_arm2set = prove(
  ``!x s. SPLIT (arm2set s) (arm2set' x s, arm2set'' x s)``,
  METIS_TAC [arm2set''_def,SPLIT_DIFF,arm2set'_SUBSET_arm2set]);

val SUBSET_arm2set = prove(
  ``!u s. u SUBSET arm2set s = ?y. u = arm2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [arm2set'_SUBSET_arm2set]
  \\ Q.EXISTS_TAC `
       ({ a |a| ?x. Reg a x IN u },{ a |a| ?x. Mem a x IN u },
        (?x. Status x IN u),(?x. Undef x IN u),(?x. Rest x IN u))`
  \\ FULL_SIMP_TAC std_ss [arm2set'_def,arm2set_def,EXTENSION,SUBSET_DEF,
                           IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]  
  \\ STRIP_TAC
  \\ `!g y. x IN (if g then {y} else {}) = g /\ (x = y)` by METIS_TAC [NOT_IN_EMPTY,IN_INSERT]
  \\ ASM_REWRITE_TAC []
  \\ PAT_ASSUM ``!g y. x`` (fn th => ALL_TAC)
  \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a. b:bool`` (IMP_RES_TAC)
  \\ FULL_SIMP_TAC std_ss [ARMel_11,ARMel_distinct]);

val SPLIT_arm2set_EXISTS = prove(
  ``!s u v. SPLIT (arm2set s) (u,v) = ?y. (u = arm2set' y s) /\ (v = arm2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [SPLIT_arm2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,arm2set'_def,arm2set''_def]
  \\ `u SUBSET (arm2set s)` by 
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_arm2set]
  \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]  
  \\ METIS_TAC []);

val STAR_arm2set = prove(
  ``!P Q s. (P * Q) (arm2set s) = ?y. P (arm2set' y s) /\ Q (arm2set'' y s)``,
  SIMP_TAC std_ss [STAR_def,SPLIT_arm2set_EXISTS]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `y` \\ METIS_TAC [])
  \\ METIS_TAC []);


(* lemmas with equality -------------------------------------------------------- *)

val arm2set'_EQ_arm2set' = prove(
  ``!y y' s s'. (arm2set' y' s' = arm2set' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st ud rt. y = (r,m,st,ud,rt)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud' rt'. y' = (r',m',st',ud',rt')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] << [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Reg a x IN arm2set' y s) = (?x. Reg a x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Mem a x IN arm2set' y s) = (?x. Mem a x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `~((?x. Status x IN arm2set' y s) = (?x. Status x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `~((?x. Undef x IN arm2set' y s) = (?x. Undef x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC [],
    `~((?x. Rest x IN arm2set' y s) = (?x. Rest x IN arm2set' y' s'))` by
      (Q.PAT_ASSUM `arm2set' y' s' = arm2set' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set'])
    \\ METIS_TAC []]);

val arm2set''_EQ_arm2set'' = prove(
  ``!y y' s s'. (arm2set'' y' s' = arm2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r m st ud rt. y = (r,m,st,ud,rt)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud' rt'. y' = (r',m',st',ud',rt')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] << [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Reg a x IN arm2set'' y s) = (?x. Reg a x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ `~((?x. Mem a x IN arm2set'' y s) = (?x. Mem a x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `~((?x. Status x IN arm2set'' y s) = (?x. Status x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `~((?x. Undef x IN arm2set'' y s) = (?x. Undef x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC [],
    `~((?x. Rest x IN arm2set'' y s) = (?x. Rest x IN arm2set'' y' s'))` by
      (Q.PAT_ASSUM `arm2set'' y' s' = arm2set'' y s` (fn th => ALL_TAC)     
       \\ FULL_SIMP_TAC bool_ss [IN_arm2set''])
    \\ METIS_TAC []]);

val arm2set'_11 = prove(
  ``!x y s. (arm2set' x s = arm2set' y s) ==> (x = y)``,
  REPEAT STRIP_TAC
  \\ `?r m st ud rt. x = (r,m,st,ud,rt)` by METIS_TAC [PAIR]
  \\ `?r' m' st' ud' rt'. y = (r',m',st',ud',rt')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [arm2set'_def,PAIR_EQ,EXTENSION]  
  \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [] << [
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC `Reg x' (reg x' s)`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC `Mem x' (mem x' s)`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC `Status (status s)`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC `Undef (s.undefined)`),
    Q.PAT_ASSUM `!x:'a. b:bool` (ASSUME_TAC o Q.SPEC `Rest (owrt_visible s)`)]
  \\ FULL_SIMP_TAC (srw_ss()) [IN_UNION,GSPECIFICATION,NOT_IN_EMPTY,
       IN_INSERT,PUSH_IN_INTO_IF]);


(* ----------------------------------------------------------------------------- *)
(* Describe the subsets of arm2set                                               *)
(* ----------------------------------------------------------------------------- *)

val WD_Reg_def    = Define `WD_Reg s = !a x y. Reg a x IN s /\ Reg a y IN s ==> (x = y)`;
val WD_Mem_def    = Define `WD_Mem s = !a x y. Mem a x IN s /\ Mem a y IN s ==> (x = y)`;
val WD_Status_def = Define `WD_Status s = !x y. Status x IN s /\ Status y IN s ==> (x = y)`;
val WD_Undef_def  = Define `WD_Undef s = !x y. Undef x IN s /\ Undef y IN s ==> (x = y)`;
val WD_Rest_def   = Define `WD_Rest s = !x y. Rest x IN s /\ Rest y IN s ==> (x = y)`;
val WD_ARM_def = Define `WD_ARM s = WD_Reg s /\ WD_Mem s /\ WD_Status s /\ WD_Undef s /\ WD_Rest s`;

fun WD_TAC x y = 
  SRW_TAC [] [WD_ARM_def,arm2set_def,SUBSET_DEF,
              WD_Reg_def,WD_Mem_def,WD_Status_def,WD_Undef_def,WD_Rest_def]
  \\ PAT_ASSUM ``!x:'a. b`` 
     (fn th => (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC x) th \\ 
               (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC y) th)
  \\ SRW_TAC [] [];

val WD_Reg = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Reg t``, WD_TAC `Reg a x` `Reg a y`);

val WD_Mem = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Mem t``, WD_TAC `Mem a x` `Mem a y`);

val WD_Status = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Status t``, WD_TAC `Status x` `Status y`);

val WD_Undef = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Undef t``, WD_TAC `Undef x` `Undef y`);

val WD_Rest = prove(
  ``!t s. t SUBSET (arm2set s) ==> WD_Rest t``, WD_TAC `Rest x` `Rest y`);

val WD_ARM_THM = store_thm("WD_ARM_THM",
  ``!t s. t SUBSET (arm2set s) ==> WD_ARM t``,
  METIS_TAC [WD_Reg,WD_Mem,WD_Status,WD_Undef,WD_Rest,WD_ARM_def]);

val WD_ARM_SUBSET = store_thm("WD_ARM_SUBSET",
  ``!t s. (WD_ARM s /\ t SUBSET s) ==> WD_ARM t``,  
  SIMP_TAC std_ss [WD_ARM_def, WD_Reg_def, WD_Mem_def, WD_Status_def,
                   WD_Undef_def, WD_Rest_def, SUBSET_DEF] \\ METIS_TAC []);

val WD_ARM_DELETE = store_thm("WD_ARM_DELETE",
  ``!s e. WD_ARM s ==> WD_ARM (s DELETE e)``,
  REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC WD_ARM_SUBSET
  \\ Q_TAC EXISTS_TAC `s`
  \\ ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE]);

val WD_ARM_DIFF = store_thm("WD_ARM_DIFF",
  ``!s t. WD_ARM s ==> WD_ARM (s DIFF t)``,
  REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC WD_ARM_SUBSET 
  \\ Q_TAC EXISTS_TAC `s`
  \\ ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_DIFF]);

val arm2set'_SUBSET_arm2set = store_thm ("arm2set'_SUBSET_arm2set",
  ``!x s. arm2set' x s SUBSET arm2set s``,
  REPEAT STRIP_TAC
  \\ `?x1 x2 x3 x4 x5. x = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [arm2set'_def,arm2set_def,EXTENSION,GSPECIFICATION,IN_UNION,SUBSET_DEF]);

val WD_ARM_arm2set' = store_thm ("WD_ARM_arm2set'",
  ``!x s. WD_ARM (arm2set' x s)``,
  METIS_TAC [arm2set'_SUBSET_arm2set,WD_ARM_THM]);


(* ----------------------------------------------------------------------------- *)
(* Address operations                                                            *)
(* ----------------------------------------------------------------------------- *)

val addr32_def = Define `addr32 (x:word30) = (w2w x << 2):word32`;
val addr30_def = Define `addr30 (x:word32) = ((31 >< 2) x):word30`;

val w2n_mod = prove(
  ``!x. (w2n (x:word30)) MOD (2**30) = w2n x``,
  ASSUME_TAC (INST_TYPE [``:'a``|->``:i30``] w2n_lt)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []);

val addr32_eq_0 = store_thm("addr32_eq_0",
  ``!x. (1 >< 0) (addr32 x) = 0w:word2``,
  REWRITE_TAC [addr32_def]
  \\ REWRITE_TAC [w2w_def,word_lsl_n2w]
  \\ EVAL_TAC
  \\ REWRITE_TAC [BITS_def,MOD_2EXP_def,DIV_2EXP_def]
  \\ EVAL_TAC
  \\ ASSUME_TAC (EVAL ``0 MOD 4294967296 MOD 4``)
  \\ `0 < 4` by EVAL_TAC
  \\ METIS_TAC [DIV_1,MOD_EQ_0]);

val addr30_addr32_LEMMA = prove(
  ``!x. BITS 31 2 (w2n x * 4) = w2n (x:word30)``,
  STRIP_TAC
  \\ REWRITE_TAC [BITS_def,MOD_2EXP_def,DIV_2EXP_def]  
  \\ REWRITE_TAC [EVAL ``2**2``,EVAL ``SUC 31 - 2``]
  \\ `0 < 4` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [arithmeticTheory.MULT_DIV]
  \\ ONCE_REWRITE_TAC [GSYM w2n_mod]
  \\ `0 < 2**30` by EVAL_TAC
  \\ METIS_TAC [arithmeticTheory.MOD_MOD]);

val addr30_addr32 = store_thm("addr30_addr32",
  ``!x. addr30 (addr32 x) = x``,
  SIMP_TAC std_ss [addr30_def,addr32_def,word_extract_def,w2w_def]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_bits_n2w,word_lsl_n2w]
  \\ REWRITE_TAC [addr30_addr32_LEMMA]
  \\ ONCE_REWRITE_TAC [GSYM w2n_mod]
  \\ REWRITE_TAC [w2n_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `!n. n MOD 2**30 MOD 2**32 = n MOD 2**30` by ALL_TAC << [
    REPEAT STRIP_TAC
    \\ `0 < 2**30 /\ 2**30 < 2**32` by EVAL_TAC
    \\ `n MOD 2**30 < 2**32` by METIS_TAC [DIVISION,LESS_TRANS]
    \\ METIS_TAC [LESS_MOD],
    FULL_SIMP_TAC std_ss [SIMP_RULE std_ss [] w2n_mod,n2w_w2n]]);

val addr32_n2w = store_thm ("addr32_n2w", 
  ``!n. (addr32 (n2w n)  = n2w (4* n))``,
  REWRITE_TAC [addr32_def, DECIDE ``2 = 1 + 1``, GSYM LSL_ADD, 
               LSL_ONE,w2w_def, word_add_n2w, n2w_11, dimword_32]
  \\ `!n. n + n + (n + n) = 4*n` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [w2n_n2w, dimword_30, MOD_COMMON_FACTOR]);

val addr32_ADD = store_thm ("addr32_ADD", 
  ``!v w. (addr32 (v + w)  = addr32 v + addr32 w)``,
  SIMP_TAC std_ss [addr32_def]
  \\ wordsLib.WORDS_TAC
  \\ SIMP_TAC arith_ss 
       [word_add_def, w2n_n2w, dimword_30, bitTheory.TIMES_2EXP_def,
        GSYM LEFT_ADD_DISTRIB, MOD_COMMON_FACTOR]);

val addr32_NEG = store_thm("addr32_NEG",
  ``!w. addr32 ($- w) = $- (addr32 w)``,
  wordsLib.Cases_word \\ REWRITE_TAC [addr32_n2w] 
  \\ wordsLib.WORDS_TAC \\ REWRITE_TAC [addr32_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11,LEFT_SUB_DISTRIB,MOD_COMMON_FACTOR]);

val addr32_SUB = store_thm ("addr32_SUB", 
  ``!v w. (addr32 (v - w)  = addr32 v - addr32 w)``,
  REWRITE_TAC [word_sub_def,addr32_ADD,addr32_NEG]);
  
val addr32_SUC = store_thm("addr32_SUC",
  ``!p. addr32 (p + 1w) = addr32 p + 4w``,
  SRW_TAC [] [addr32_ADD,addr32_n2w]);

val LSL_ADD2 = store_thm ("LSL_ADD2",
  ``!v w n. (v + w) << n = (v << n) + (w << n)``,
  Induct_on `n` 
  \\ SIMP_TAC std_ss [SHIFT_ZERO,SUC_ONE_ADD,GSYM LSL_ADD,LSL_ONE]
  \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val addr32_11 = store_thm("addr32_11",
  ``!a b. (addr32 a = addr32 b) = (a = b)``,
  wordsLib.Cases_word \\ wordsLib.Cases_word 
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [addr32_n2w,n2w_11]
  \\ `4 * n < 4294967296 /\ 4 * n' < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,EQ_MULT_LCANCEL]);


(* ----------------------------------------------------------------------------- *)
(* Specialising processorTheory                                                  *)
(* ----------------------------------------------------------------------------- *)

val R_def = Define `R r x = one (Reg r x)`;
val M_def = Define `M a x = one (Mem a x)`;
val S_def = Define `S x = one (Status x)`;

val R30_def = Define `R30 r x = R r (addr32 x)`; 
val M30_def = Define `M30 r x = R r (addr32 x)`;

val ms_def = Define `
  (ms a [] = emp) /\ 
  (ms a (x::xs) = M a x * ms (a + 1w) xs)`;

val blank_ms_def = Define `
  (blank_ms a 0 = emp) /\ 
  (blank_ms a (SUC n) = ~M a * blank_ms (a + 1w) n)`;

val PASS_def = Define `PASS c x = (cond (CONDITION_PASSED2 x c)):ARMset->bool`;
val nPASS_def = Define `nPASS c x = (cond ~(CONDITION_PASSED2 x c)):ARMset->bool`;

val ARMnext_def = Define `ARMnext s = arm2set (NEXT_ARM_MEM (set2arm s))`;
val ARMi_def    = Define `ARMi (a,x) = M a x`;
val ARMpc_def   = Define `ARMpc p = R30 15w p * one (Undef F)`;
val ARMproc_def = Define `ARMproc = (ARMsets,ARMnext,ARMpc,ARMi)`;

val ARM_RUN_def   = Define `ARM_RUN   = RUN ARMproc`; 
val ARM_GPROG_def = Define `ARM_GPROG = GPROG ARMproc`;
val ARM_PROG_def  = Define `ARM_PROG  = PROG ARMproc`;
val ARM_PROC_def  = Define `ARM_PROC P Q C = PROC ARMproc (R30 14w) P (Q * ~R 14w) C`;
val ARM_CALL_def  = Define `ARM_CALL cs k = CALL ARMproc (R30 14w) (~(R 14w)) cs (pcADD k)`;

val ARM_NOP_def   = Define `ARM_NOP c cs = !x. ARM_PROG (S x * nPASS c x) cs {} (S x) {}`;
val ARM_PROG2_def = Define `ARM_PROG2 c P cs Q Z = ARM_PROG P cs {} Q Z /\ ARM_NOP c cs`;


(* lemmas about mpool and msequence -------------------------------------------- *)

val ARMi_ONE_TO_ONE = prove(
  ``!a b x y. (ARMi (a,x) = ARMi (b,y)) ==> (a = b)``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] 
  \\ SIMP_TAC std_ss [ARMi_def,M_def,one_def]
  \\ `!y z. (!x'. (y = x':ARMset) = (z = x')) ==> (y = z)` by ALL_TAC << [
    REPEAT STRIP_TAC \\ CCONTR_TAC
    \\ PAT_ASSUM ``!x':'a. b`` (ASSUME_TAC o Q.SPEC `z`) 
    \\ FULL_SIMP_TAC std_ss [],
    REPEAT STRIP_TAC \\ `{Mem a x} = {Mem b y}` by METIS_TAC []
    \\ `Mem a x = Mem b y` by METIS_TAC [EXTENSION,IN_INSERT,NOT_IN_EMPTY]
    \\ SRW_TAC [] []]);

val ARM_mpool_eq_msequence = 
  let
    val th = Q.INST_TYPE [`:'a`|->`:ARMel`,`:'b`|->`:i30`,`:'c`|->`:word32`] mpool_eq_msequence
    val th = Q.SPECL [`xs`,`f`,`a`,`ARMi`] th
    val th = SIMP_RULE (bool_ss++SIZES_ss) [GSYM AND_IMP_INTRO] (REWRITE_RULE [dimword_def] th)
    val th = MATCH_MP th ARMi_ONE_TO_ONE 
  in
    (Q.GEN `xs` o Q.GEN `f` o Q.GEN `a`) th 
  end;

val msequence_eq_ms = prove(
  ``!a xs. msequence ARMi a xs = ms a xs``,
  Induct_on `xs` \\ SRW_TAC [] [msequence_def,ms_def,ARMi_def]);

val mpool_eq_ms = store_thm("mpool_eq_ms",
  ``!xs (f:word30->word30) a. LENGTH xs <= 2**30 ==> (mpool ARMi a {(xs,f)} = ms (f a) xs)``,
  SIMP_TAC bool_ss [GSYM msequence_eq_ms,ARM_mpool_eq_msequence]);


(* various lemmas -------------------------------------------------------------- *)

val ARMproc_IN_PROCESSORS = prove(
  ``ARMproc IN PROCESSORS``,
  REWRITE_TAC [GSPECIFICATION,PROCESSORS_def]
  \\ Q.EXISTS_TAC `ARMproc`
  \\ SIMP_TAC std_ss [ARMproc_def]
  \\ SIMP_TAC bool_ss [ARMnext_def,RES_FORALL]
  \\ REPEAT STRIP_TAC  
  \\ SRW_TAC [] [ARMsets_def]
  \\ METIS_TAC []);

val PASS_CASES = store_thm("PASS_CASES",
  ``!n z c v.
      (PASS EQ (n,z,c,v) = cond z) /\
      (PASS CS (n,z,c,v) = cond c) /\
      (PASS MI (n,z,c,v) = cond n) /\
      (PASS VS (n,z,c,v) = cond v) /\
      (PASS HI (n,z,c,v) = cond (c /\ ~z)) /\
      (PASS GE (n,z,c,v) = cond (n = v)) /\
      (PASS GT (n,z,c,v) = cond (~z /\ (n = v))) /\
      (PASS AL (n,z,c,v) = emp) /\
      (PASS NE (n,z,c,v) = cond ~z) /\
      (PASS CC (n,z,c,v) = cond ~c) /\
      (PASS PL (n,z,c,v) = cond ~n) /\
      (PASS VC (n,z,c,v) = cond ~v) /\
      (PASS LS (n,z,c,v) = cond (~c \/ z)) /\
      (PASS LT (n,z,c,v) = cond ~(n = v)) /\
      (PASS LE (n,z,c,v) = cond (z \/ ~(n = v))) /\
      (PASS NV (n,z,c,v) = SEP_F) /\
      (nPASS EQ (n,z,c,v) = cond ~z) /\
      (nPASS CS (n,z,c,v) = cond ~c) /\
      (nPASS MI (n,z,c,v) = cond ~n) /\
      (nPASS VS (n,z,c,v) = cond ~v) /\
      (nPASS HI (n,z,c,v) = cond ~(c /\ ~z)) /\
      (nPASS GE (n,z,c,v) = cond ~(n = v)) /\
      (nPASS GT (n,z,c,v) = cond ~(~z /\ (n = v))) /\
      (nPASS AL (n,z,c,v) = SEP_F) /\
      (nPASS NE (n,z,c,v) = cond ~~z) /\
      (nPASS CC (n,z,c,v) = cond ~~c) /\
      (nPASS PL (n,z,c,v) = cond ~~n) /\
      (nPASS VC (n,z,c,v) = cond ~~v) /\
      (nPASS LS (n,z,c,v) = cond ~(~c \/ z)) /\
      (nPASS LT (n,z,c,v) = cond ~~(n = v)) /\
      (nPASS LE (n,z,c,v) = cond ~(z \/ ~(n = v))) /\
      (nPASS NV (n,z,c,v) = emp)``,
  SRW_TAC [] [CONDITION_PASSED2_def,nPASS_def,PASS_def,SEP_cond_CLAUSES]);

fun QGENL xs th = foldr (uncurry Q.GEN) th xs;
fun GENL_save_thm (name,vars,th) = save_thm(name,QGENL vars th);

val ARM_RUN_THM = GENL_save_thm("ARM_RUN_THM",[`P`,`Q`],  
  REWRITE_CONV [ARM_RUN_def,RUN_def,ARMproc_def] ``ARM_RUN P Q``);

val ARM_GPROG_THM = GENL_save_thm("ARM_GPROG_THM",[`Y`,`C`,`Z`],  
  (REWRITE_CONV [ARM_GPROG_def,ARMproc_def,GPROG_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_RUN_def]) ``ARM_GPROG Y C Z``);

val ARM_PROG_THM = GENL_save_thm("ARM_PROG_THM",[`P`,`cs`,`C`,`Q`,`Z`],  
  (REWRITE_CONV [ARM_PROG_def,ARMproc_def,PROG_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_GPROG_def]) ``ARM_PROG P cs C Q Z``);

val ARM_CALL_THM = GENL_save_thm("ARM_CALL_THM",[`cs`,`k`],
  (REWRITE_CONV [ARM_CALL_def,ARMproc_def,CALL_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_RUN_def]) ``ARM_CALL cs k``);

val ARM_PROC_THM = GENL_save_thm("ARM_PROC_THM",[`P`,`Q`,`C`],  
  (REWRITE_CONV [ARM_PROC_def,PROC_def,ARMproc_def] THENC 
   REWRITE_CONV [GSYM ARMproc_def,GSYM ARM_PROG_def]) ``ARM_PROC P Q C``);

val run_arm2set = prove(
  ``!k s. run ARMnext (k,arm2set s) = arm2set (STATE_ARM_MEM k s)``,
  Induct_on `k` \\ FULL_SIMP_TAC std_ss [run_def,STATE_ARM_MEM_def]
  \\ `!k s. run ARMnext (k,ARMnext s) = ARMnext (run ARMnext (k,s))` by
        (Induct \\ FULL_SIMP_TAC std_ss [run_def])
  \\ ASM_REWRITE_TAC [ARMnext_def,set2arm_arm2set]);


(* theorems for ARM_RUN -------------------------------------------------------- *)

fun ARM_RUN_INST th = 
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.ISPEC `ARMproc` th
    val th = MATCH_MP th ARMproc_IN_PROCESSORS
    val th = BETA_RULE th
  in
    REWRITE_RULE [GSYM ARM_RUN_def, GSYM ARM_PROG_def] th
  end;

fun save_ARM_RUN name rule = save_thm(name,ARM_RUN_INST rule);

val _ = save_ARM_RUN "ARM_RUN_FRAME" RUN_FRAME;
val _ = save_ARM_RUN "ARM_RUN_STRENGTHEN_PRE" RUN_STRENGTHEN_PRE;
val _ = save_ARM_RUN "ARM_RUN_WEAKEN_POST" RUN_WEAKEN_POST;
val _ = save_ARM_RUN "ARM_RUN_COMPOSE" RUN_COMPOSE;
val _ = save_ARM_RUN "ARM_RUN_HIDE_PRE" RUN_HIDE_PRE;
val _ = save_ARM_RUN "ARM_RUN_HIDE_POST" RUN_HIDE_POST;
val _ = save_ARM_RUN "ARM_RUN_LOOP" RUN_LOOP;

val ARM_RUN_SEMANTICS = store_thm("ARM_RUN_SEMANTICS",
  ``ARM_RUN P Q =
    !y s. P (arm2set' y s) ==>
          ?k. let s' = STATE_ARM_MEM k s in
              Q (arm2set' y s') /\ (arm2set'' y s = arm2set'' y s')``,
  SIMP_TAC std_ss [ARM_RUN_THM,RES_FORALL,ARMsets_def,GSPECIFICATION]
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    ASSUME_TAC (Q.EXISTS (`?s'. arm2set s = arm2set s'`,`s`) (REFL ``arm2set s``))
    \\ Q.PAT_ASSUM `!s. b` 
          (STRIP_ASSUME_TAC o Q.SPEC `\s'. s' = arm2set'' y s` o 
           UNDISCH o Q.SPEC `arm2set s`)   
    \\ FULL_SIMP_TAC std_ss [run_arm2set,STAR_arm2set,LET_DEF]
    \\ `?k y'. Q (arm2set' y' (STATE_ARM_MEM k s)) /\
               (arm2set'' y' (STATE_ARM_MEM k s) = arm2set'' y s)` by METIS_TAC []
    \\ Q.EXISTS_TAC `k` \\ METIS_TAC [arm2set''_EQ_arm2set''],
    PAT_ASSUM ``s = arm2set s'`` (fn th => FULL_SIMP_TAC bool_ss [th,STAR_arm2set])
    \\ PAT_ASSUM ``!y:'a. b:bool`` 
        (STRIP_ASSUME_TAC o SIMP_RULE std_ss [LET_DEF] o UNDISCH o Q.SPECL [`y`,`s'`])
    \\ Q.EXISTS_TAC `k` \\ REWRITE_TAC [run_arm2set,STAR_arm2set]
    \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC [] \\ METIS_TAC []]);

val IMP_ARM_RUN = store_thm ("IMP_ARM_RUN",
  ``!x P Q.
      (!t s. t SUBSET arm2set s /\ P t ==> (t = arm2set' x s)) /\     (* cond 1 *)
      (!s. ?k. (P (arm2set' x s) ==> 
           (arm2set'' x s = arm2set'' x (STATE_ARM_MEM k s)) /\       (* cond 2 *)
           Q (arm2set' x (STATE_ARM_MEM k s)))) ==>                   (* cond 3 *)
      ARM_RUN P Q``,
   REWRITE_TAC [ARM_RUN_SEMANTICS] \\ REPEAT STRIP_TAC
   \\ `x = y` by METIS_TAC [arm2set'_11,arm2set'_SUBSET_arm2set]
   \\ FULL_SIMP_TAC bool_ss []
   \\ Q.PAT_ASSUM `!s. ?k. b:bool` (STRIP_ASSUME_TAC o Q.SPEC `s`)  
   \\ Q.EXISTS_TAC `k` \\ FULL_SIMP_TAC std_ss [LET_DEF]);


(* theorems for ARM_GPROG ------------------------------------------------------ *)

fun ARM_GPROG_INST th = 
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.ISPEC `ARMproc` th
    val th = MATCH_MP th ARMproc_IN_PROCESSORS
    val th = BETA_RULE th
  in
    REWRITE_RULE [GSYM ARM_GPROG_def, GSYM ARM_GPROG_def] th
  end;

fun save_ARM_GPROG name rule = save_thm(name,ARM_GPROG_INST rule);

val _ = save_ARM_GPROG "ARM_GPROG_FRAME" GPROG_FRAME;
val _ = save_ARM_GPROG "ARM_GPROG_EMPTY_CODE" GPROG_EMPTY_CODE;
val _ = save_ARM_GPROG "ARM_GPROG_ADD_CODE" GPROG_ADD_CODE;
val _ = save_ARM_GPROG "ARM_GPROG_STRENGTHEN_PRE" GPROG_STRENGTHEN_PRE;
val _ = save_ARM_GPROG "ARM_GPROG_WEAKEN_POST" GPROG_WEAKEN_POST;
val _ = save_ARM_GPROG "ARM_GPROG_FALSE_PRE" GPROG_FALSE_PRE;
val _ = save_ARM_GPROG "ARM_GPROG_FALSE_POST" GPROG_FALSE_POST;
val _ = save_ARM_GPROG "ARM_GPROG_SHIFT" GPROG_SHIFT;
val _ = save_ARM_GPROG "ARM_GPROG_MERGE_CODE" GPROG_MERGE_CODE;
val _ = save_ARM_GPROG "ARM_GPROG_MERGE_PRE" GPROG_MERGE_PRE;
val _ = save_ARM_GPROG "ARM_GPROG_MERGE_POST" GPROG_MERGE_POST;
val _ = save_ARM_GPROG "ARM_GPROG_COMPOSE" GPROG_COMPOSE;
val _ = save_ARM_GPROG "ARM_GPROG_LOOP" GPROG_LOOP;


(* theorems for ARM_PROG ------------------------------------------------------- *)

fun ARM_PROG_INST th = 
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.ISPEC `ARMproc` th
    val th = MATCH_MP th ARMproc_IN_PROCESSORS
    val th = BETA_RULE th
  in
    REWRITE_RULE [GSYM ARM_PROG_def, GSYM ARM_PROG_def] th
  end;

fun save_ARM_PROG name rule = save_thm(name,ARM_PROG_INST rule);

val _ = save_ARM_PROG "ARM_PROG_FRAME" PROG_FRAME;
val _ = save_ARM_PROG "ARM_PROG_MERGE" PROG_MERGE;
val _ = save_ARM_PROG "ARM_PROG_MERGE_POST" PROG_MERGE_POST;
val _ = save_ARM_PROG "ARM_PROG_MERGE_CODE" PROG_MERGE_CODE;
val _ = save_ARM_PROG "ARM_PROG_ABSORB_POST" PROG_ABSORB_POST;
val _ = save_ARM_PROG "ARM_PROG_FALSE_POST" PROG_FALSE_POST;
val _ = save_ARM_PROG "ARM_PROG_STRENGTHEN_PRE" PROG_STRENGTHEN_PRE;
val _ = save_ARM_PROG "ARM_PROG_WEAKEN_POST" PROG_WEAKEN_POST;
val _ = save_ARM_PROG "ARM_PROG_WEAKEN_POST1" PROG_WEAKEN_POST1;
val _ = save_ARM_PROG "ARM_PROG_ADD_CODE" PROG_ADD_CODE;
val _ = save_ARM_PROG "ARM_PROG_APPEND_CODE" PROG_APPEND_CODE;
val _ = save_ARM_PROG "ARM_PROG_MOVE_COND" PROG_MOVE_COND;
val _ = save_ARM_PROG "ARM_PROG_HIDE_PRE" PROG_HIDE_PRE;
val _ = save_ARM_PROG "ARM_PROG_HIDE_POST1" PROG_HIDE_POST1;
val _ = save_ARM_PROG "ARM_PROG_HIDE_POST" PROG_HIDE_POST;
val _ = save_ARM_PROG "ARM_PROG_EXISTS_PRE" PROG_EXISTS_PRE;
val _ = save_ARM_PROG "ARM_PROG_COMPOSE" PROG_COMPOSE;
val _ = save_ARM_PROG "ARM_PROG_LOOP" PROG_LOOP;
val _ = save_ARM_PROG "ARM_PROG_EXTRACT_POST" PROG_EXTRACT_POST;
val _ = save_ARM_PROG "ARM_PROG_EXTRACT_CODE" PROG_EXTRACT_CODE;

val ARM_PROG_INTRO = save_thm("ARM_PROG_INTRO",
  let 
    val th = Q.ISPECL [`ARMsets`,`ARMnext`,`ARMpc`,`ARMi`] PROG_INTRO
    val th = REWRITE_RULE [GSYM ARM_RUN_def,GSYM ARM_PROG_def,GSYM ARMproc_def,dimword_def] th
    val th = SIMP_RULE (bool_ss++SIZES_ss) [GSYM AND_IMP_INTRO,msequence_eq_ms] th
    val th = MATCH_MP th ARMi_ONE_TO_ONE
  in
    th
  end);

val ARM_PROG_INTRO1 = save_thm("ARM_PROG_INTRO1",
  let 
    val th = Q.SPECL [`P`,`cs`,`Q`,`SEP_F`,`f`] ARM_PROG_INTRO
    val th = REWRITE_RULE [F_STAR,SEP_DISJ_CLAUSES,ARM_PROG_INST PROG_FALSE_POST] th
  in
    (Q.GEN `P` o Q.GEN `cs` o Q.GEN `Q`) th
  end);

val ARM_PROG_HIDE_STATUS = store_thm("ARM_PROG_HIDE_STATUS",
  ``!P cs C Q Z.
      (!n z c v. ARM_PROG (P * S (n,z,c,v)) cs C Q Z) = ARM_PROG (P * ~S) cs C Q Z``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM (ARM_PROG_INST PROG_HIDE_PRE)]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ ASM_REWRITE_TAC []);


(* theorems for ARM_PROC ------------------------------------------------------- *)

val ARM_PROC_CALL = store_thm("ARM_PROC_CALL",
  ``!cs P Q C k.
      ARM_CALL cs k /\ ARM_PROC P Q C ==>
      ARM_PROG (P * ~R 14w) cs (setADD k C) (Q * ~R 14w) {}``,
  REWRITE_TAC [ARM_CALL_def,setADD_def,ARM_PROG_def,ARM_PROC_def]
  \\ REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC (MATCH_MP (SIMP_RULE bool_ss [RES_FORALL] PROC_CALL) ARMproc_IN_PROCESSORS)
  \\ Q.EXISTS_TAC `R30 14w` \\ ASM_REWRITE_TAC []);

val _ = save_thm("ARM_PROC_RECURSION",PROC_RECURSION);


(* ----------------------------------------------------------------------------- *)
(* Theorems for collections of "R r x", "~R r" and "M a x"                       *)
(* ----------------------------------------------------------------------------- *)

val reg_spec_def = Define `
  reg_spec l = FOLDR (\(r, v) P. R r v * P) emp l`

val ereg_spec_def = Define `
  ereg_spec l = FOLDR (\r P. (SEP_EXISTS v. R r v) * P) emp l`

val reg_spec_thm = store_thm ("reg_spec_thm",
  ``!l P s. ALL_DISTINCT l ==>
            ((((reg_spec l) * P) s) =
             (((EVERY (\(r, v). ((Reg r v) IN s)) l)) /\
             (P (s DIFF (LIST_TO_SET (MAP (\(r, v). Reg r v) l))))))``,
  Induct_on `l` << [
    SIMP_TAC list_ss 
      [reg_spec_def, emp_STAR, containerTheory.LIST_TO_SET_THM, DIFF_EMPTY],
    REPEAT GEN_TAC THEN
    Cases_on `h` THEN
    SIMP_TAC list_ss [reg_spec_def, containerTheory.LIST_TO_SET_THM, GSYM STAR_ASSOC] THEN
    ASM_SIMP_TAC std_ss [GSYM reg_spec_def, R_def, one_STAR, IN_DELETE,
                         ARMel_11, DIFF_INSERT, GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (prove (``((a /\ c) ==> (b = b')) ==> ((a:bool /\ b /\ c) = (a /\ b' /\ c))``, PROVE_TAC[])) THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC std_ss [listTheory.EVERY_MEM] THEN 
    EQ_TAC THEN REPEAT STRIP_TAC THEN 
    RES_TAC THEN
    Cases_on `e` THEN
    FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC []]);

val ereg_spec_thm = store_thm ("ereg_spec_thm",
  ``!l P s. (ALL_DISTINCT l /\ WD_ARM s) ==>
            ((((ereg_spec l) * P) s) =
            (((EVERY (\r. ?v. ((Reg r v) IN s)) l)) /\
            (P (s DIFF (BIGUNION (LIST_TO_SET (MAP (\r. (\x. ?v. (x = Reg r v))) l)))))))``,
  Induct_on `l` THENL [
    SIMP_TAC list_ss [ereg_spec_def, emp_STAR, containerTheory.LIST_TO_SET_THM, DIFF_EMPTY, BIGUNION_EMPTY],
    SIMP_TAC list_ss [ereg_spec_def, containerTheory.LIST_TO_SET_THM, GSYM STAR_ASSOC] THEN
    ASM_SIMP_TAC std_ss [GSYM ereg_spec_def, R_def, one_STAR, IN_DELETE, WD_ARM_DELETE,
        ARMel_11, DIFF_INSERT, GSYM CONJ_ASSOC, SEP_EXISTS_ABSORB_STAR, SEP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC[],
    Q.PAT_ASSUM `EVERY X l` MP_TAC THEN
    MATCH_MP_TAC EVERY_MONOTONIC THEN
    SIMP_TAC std_ss [] THEN
    PROVE_TAC[],
    SIMP_TAC std_ss [BIGUNION_INSERT] THEN
    POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC (prove (``(s1 = s2) ==> (P s1 ==> P s2)``, SIMP_TAC std_ss [])) THEN
    MATCH_MP_TAC (prove (``(s DELETE x = s DIFF x') ==> (s DELETE x DIFF y = s DIFF (x' UNION y))``, SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, IN_UNION] THEN METIS_TAC[])) THEN
    FULL_SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, WD_ARM_def, WD_Reg_def] THEN
    GEN_TAC THEN
    Cases_on `x IN s` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC std_ss [IN_DEF] THEN
    METIS_TAC[],		
    Q_TAC EXISTS_TAC `v` THEN
    REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC[],
      FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
      REPEAT STRIP_TAC THEN
      METIS_TAC[],
      POP_ASSUM MP_TAC THEN
      SIMP_TAC std_ss [BIGUNION_INSERT] THEN
      MATCH_MP_TAC (prove (``(s2 = s1) ==> (P s1 ==> P s2)``, SIMP_TAC std_ss [])) THEN
      MATCH_MP_TAC (prove (``(s DELETE x = s DIFF x') ==> (s DELETE x DIFF y = s DIFF (x' UNION y))``, SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, IN_UNION] THEN METIS_TAC[])) THEN
      FULL_SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_DIFF, WD_ARM_def, WD_Reg_def] THEN
      GEN_TAC THEN
      Cases_on `x IN s` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [IN_DEF] THEN
      METIS_TAC[]]]]);

val ENUMERATE_def = Define `
  (ENUMERATE n [] = []) /\
  (ENUMERATE n (h::l) = (n, h)::(ENUMERATE (SUC n) l))`;

val ENUMERATE___MEM_FST_RANGE = store_thm ("ENUMERATE___MEM_FST_RANGE",
  ``!n e m l. MEM (n, e) (ENUMERATE m l) ==> (m <= n /\ n < m + LENGTH l)``,
  Induct_on `l` THENL [
    SIMP_TAC list_ss [ENUMERATE_def],
    ASM_SIMP_TAC list_ss [ENUMERATE_def, DISJ_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    RES_TAC THEN
    ASM_SIMP_TAC arith_ss []]);

val MEM_ENUMERATE = store_thm ("MEM_ENUMERATE",
  ``!x m l. MEM x (ENUMERATE m l) =
            ((m <= FST x) /\ (FST x < m + LENGTH l) /\
            (SND x = EL (FST x - m) l))``,
  Cases_on `x` THEN
  Induct_on `l` THENL [
    SIMP_TAC list_ss [ENUMERATE_def] THEN
    GEN_TAC THEN
    Cases_on `m <= q` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC arith_ss [],
    ASM_SIMP_TAC list_ss [ENUMERATE_def] THEN
    REPEAT GEN_TAC THEN
    Cases_on `(q = m) /\ (r = h)` THEN ASM_SIMP_TAC list_ss [] THEN
    Cases_on `q` THEN1 FULL_SIMP_TAC list_ss [] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC arith_ss [] THENL [
      FULL_SIMP_TAC list_ss [arithmeticTheory.SUB],
      CCONTR_TAC THEN
      `m = SUC n` by DECIDE_TAC THEN
      FULL_SIMP_TAC list_ss [],
      Cases_on `n < m` THEN 
      FULL_SIMP_TAC list_ss [arithmeticTheory.SUB]]]);

val ms_STAR = store_thm ("ms_STAR", 
  ``!n p l P s.
	(n + LENGTH l < 2**30) ==>
	((ms (p + n2w n) l * P)  s = ((LIST_TO_SET (MAP (\(n, i). Mem (p + n2w n) i) (ENUMERATE n l))) SUBSET s /\ P (s DIFF (LIST_TO_SET (MAP (\(n, i). Mem (p + n2w n) i) (ENUMERATE n l))))))``,
  Induct_on `l` THENL [
    SIMP_TAC list_ss 
      [ENUMERATE_def, ms_def, containerTheory.LIST_TO_SET_THM, LET_THM, 
       EMPTY_SUBSET,DIFF_EMPTY, emp_STAR],
    ASM_SIMP_TAC list_ss [ENUMERATE_def, ms_def, containerTheory.LIST_TO_SET_THM, LET_THM, M_def, GSYM STAR_ASSOC, one_STAR, GSYM WORD_ADD_ASSOC, word_add_n2w] THEN
    SIMP_TAC arith_ss [GSYM DIFF_INSERT, INSERT_SUBSET, SUBSET_DELETE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC arith_ss [SUC_ONE_ADD] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC list_ss [MEM_MAP] THEN
    Cases_on `y` THEN
    SIMP_TAC std_ss [ARMel_11, WORD_EQ_ADD_LCANCEL] THEN
    Cases_on `MEM (q,r) (ENUMERATE (n + 1) l)` THEN ASM_REWRITE_TAC[] THEN
    IMP_RES_TAC ENUMERATE___MEM_FST_RANGE THEN
    ASM_SIMP_TAC arith_ss [n2w_11, dimword_30]]);

val ms_STAR___ZERO = save_thm ("ms_STAR___ZERO",     
  REWRITE_RULE [ADD, WORD_ADD_0] (SPEC ``0:num`` ms_STAR));

val DELETE_EQ_ELIM = store_thm ("DELETE_EQ_ELIM",
  ``!X Y z. z IN Y ==> ((X = Y DELETE z) =
            ((z INSERT X = Y) /\ ~(z IN X)))``,
  SIMP_TAC std_ss [EXTENSION, IN_DELETE, IN_INSERT] \\ METIS_TAC []);

val DIFF_EQ_ELIM = store_thm ("DIFF_EQ_ELIM",
  ``!X Y Z. Z SUBSET Y ==> ((X = Y DIFF Z) =
            ((X UNION Z = Y) /\ (DISJOINT X Z)))``,
  SIMP_TAC std_ss [EXTENSION, IN_DIFF, IN_UNION, DISJOINT_DEF, IN_INTER, 
     NOT_IN_EMPTY, SUBSET_DEF] \\ METIS_TAC [])


val _ = export_theory();
