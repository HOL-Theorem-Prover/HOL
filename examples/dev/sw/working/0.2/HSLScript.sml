
(*---------------------------------------------------------------------------------*)

(*
quietdec := true;

app load ["arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory", "listTheory", "whileTheory", "finite_mapTheory", 
          "CFLTheory", "ACFTheory"];

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory listTheory whileTheory 
     finite_mapTheory CFLTheory ACFTheory;

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory listTheory whileTheory 
       finite_mapTheory CFLTheory ACFTheory;


(*---------------------------------------------------------------------------------*)

val _ = new_theory "HSL";

(*---------------------------------------------------------------------------------*)
(*      Logical registers and their mappings to physical registers                 *)
(*---------------------------------------------------------------------------------*)

(* Pointer registers *)

val _ = Hol_datatype `
    PTR = TTP | THP | TFP | TIP | TSP | TLR`;   (* temporary register, heap pointer, fp, ip, sp and lr *) 

val toPTR_def = Define `
    (toPTR TTP = tp) /\
    (toPTR THP = gp) /\
    (toPTR TFP = fp) /\
    (toPTR TIP = ip) /\
    (toPTR TSP = sp) /\
    (toPTR TLR = lr)`;

val toPTR_lem = Q.store_thm
  ("toPTR_lem",
   `!p. ~(toPTR p = 0) /\ ~(toPTR p = 1) /\ ~(toPTR p = 2) /\
        ~(toPTR p = 3) /\ ~(toPTR p = 4) /\ ~(toPTR p = 5) /\
        ~(toPTR p = 6) /\ ~(toPTR p = 7) /\ ~(toPTR p = 8)`,
    Cases_on `p` THEN
    RW_TAC arith_ss [toPTR_def, tp_def, gp_def, fp_def, ip_def, sp_def, lr_def]
  );

(* Data regisiters *)

val _ = Hol_datatype `
    TREG = r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8`;

val data_reg_index_def = Define `
    (data_reg_index r0 = 0) /\
    (data_reg_index r1 = 1) /\
    (data_reg_index r2 = 2) /\
    (data_reg_index r3 = 3) /\
    (data_reg_index r4 = 4) /\
    (data_reg_index r5 = 5) /\
    (data_reg_index r6 = 6) /\
    (data_reg_index r7 = 7) /\
    (data_reg_index r8 = 8)`;

val data_reg_name_lem = Q.store_thm
  ("data_reg_name_lem",
   `!r.((data_reg_index r = 0) = (r = r0)) /\
       ((data_reg_index r = 1) = (r = r1)) /\
       ((data_reg_index r = 2) = (r = r2)) /\
       ((data_reg_index r = 3) = (r = r3)) /\
       ((data_reg_index r = 4) = (r = r4)) /\
       ((data_reg_index r = 5) = (r = r5)) /\
       ((data_reg_index r = 6) = (r = r6)) /\
       ((data_reg_index r = 7) = (r = r7)) /\
       ((data_reg_index r = 8) = (r = r8))`,
    Cases_on `r` THEN
    RW_TAC std_ss [data_reg_index_def]
  );

val data_reg_name_def = Define `
    data_reg_name i =
      if i = 0 then r0
      else if i = 1 then r1
      else if i = 2 then r2
      else if i = 3 then r3
      else if i = 4 then r4
      else if i = 5 then r5
      else if i = 6 then r6
      else if i = 7 then r7
      else r8`;

val data_reg_name_thm = Q.store_thm
  ("data_reg_name_thm",
   `(data_reg_name 0 = r0) /\
    (data_reg_name 1 = r1) /\
    (data_reg_name 2 = r2) /\
    (data_reg_name 3 = r3) /\
    (data_reg_name 4 = r4) /\
    (data_reg_name 5 = r5) /\
    (data_reg_name 6 = r6) /\
    (data_reg_name 7 = r7) /\
    (data_reg_name 8 = r8)`,
   RW_TAC std_ss [data_reg_name_def]
  );

val toPTR_lem_2 = Q.store_thm
  ("toPTR_lem_2",
   `!p r. ~(toPTR p = data_reg_index r)`,
    Cases_on `p` THEN Cases_on `r` THEN
    RW_TAC arith_ss [toPTR_lem, data_reg_index_def]
  );

val conv_reg_def = Define `
    conv_reg = from_reg_index o data_reg_index`;


val conv_reg_thm = Q.store_thm (
  "conv_reg_thm",
  `(conv_reg r0 = R0) /\ (conv_reg r1 = R1) /\ (conv_reg r2 = R2) /\ (conv_reg r3 = R3) /\ (conv_reg r4 = R4) /\
   (conv_reg r5 = R5) /\ (conv_reg r6 = R6) /\ (conv_reg r7 = R7) /\ (conv_reg r8 = R8)`,
  SIMP_TAC std_ss [conv_reg_def, data_reg_index_def, from_reg_index_def]
  );

val CONV_REG_LEM = Q.store_thm (
  "CONV_REG_LEM",
  `!r r'. (data_reg_index r = index_of_reg (conv_reg r)) /\
        ((data_reg_index r = data_reg_index r') ==> (r = r'))`,
  SIMP_TAC std_ss [conv_reg_def] THEN
  Cases_on `r` THEN Cases_on `r'` THEN
  RW_TAC std_ss [data_reg_index_def, from_reg_index_def, index_of_reg_def]
  );

(*---------------------------------------------------------------------------------*)
(*      Data in memory, Expressions                                                *)
(*---------------------------------------------------------------------------------*)

val _ = type_abbrev("TSTATE", Type`:(TREG |-> bool ** i32) # (num |-> bool ** i32)`);

val FORALL_TSTATE = Q.store_thm (
    "FORALL_TSTATE",
    `(!s.P s) = (!rg sk. P ((rg,sk):TSTATE))`,
    RW_TAC std_ss [FORALL_PROD]
   );

val _ = type_abbrev("TMEM", Type`:PTR # OFFSET`);      (* memory in HSL *)

val _ = Hol_datatype `
    TEXP = inR of TREG            (* registers *)
         | inC of word32          (* constants *)
         | inE of num             (* stack variables, in environments *)
    `;

(* Register Or Constants *)

val _ = Hol_datatype `
    TROC = Rg of TREG           (* registers *)
         | Cn of word32         (* constants *)
    `;

val roc_2_exp_def = Define `
  (roc_2_exp (Rg r) = inR r) /\
  (roc_2_exp (Cn v) = inC v)
  `;

val tread_def = Define `
  (tread (rg,sk) (inE i) =  sk ' i) /\
  (tread (rg,sk) (inC v) =  v) /\
  (tread (rg,sk) (inR r) = rg ' r)
  `;

val twrite_def = Define `
  (twrite (rg,sk) (inE i) v =  (rg, sk |+ (i,v))) /\
  (twrite (rg,sk) (inR r) v = (rg |+ (r,v), sk)) /\
  (twrite (rg,sk) (inC _) v = (rg, sk))
  `;

val from_MEXP_def = Define `
  (from_MEXP (MR r) = inR (data_reg_name (index_of_reg r))) /\
  (from_MEXP (MC v) = inC v)
  `;

val _ = type_abbrev("TCND", Type`:TREG # COND # TROC`);

(*---------------------------------------------------------------------------------*)
(*      Syntax of HSL                                                              *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype `
    TOPER = TLDR of TREG => num |
            TSTR of num => TREG |
	    TMOV of TREG => TROC |
            TADD of TREG => TROC => TROC |
            TSUB of TREG => TROC => TROC |
            TRSB of TREG => TROC => TROC |
            TMUL of TREG => TROC => TROC |
            TAND of TREG => TROC => TROC |
            TORR of TREG => TROC => TROC |
            TEOR of TREG => TROC => TROC |
	    TLSL of TREG => TROC => word5 |
            TLSR of TREG => TROC => word5 |
            TASR of TREG => TROC => word5 |
            TROR of TREG => TROC => word5
(*
            TCPY of TEXP list => TEXP list   (* copy from a list to a list *)
*)
     `;

val _ = Hol_datatype `HSL_STRUCTURE =
    Blk of TOPER list |
    Sc of HSL_STRUCTURE => HSL_STRUCTURE |
    Cj of TCND => HSL_STRUCTURE => HSL_STRUCTURE |
    Tr of TCND => HSL_STRUCTURE |
    Fc of (TEXP list # TEXP list) => HSL_STRUCTURE => (TEXP list # TEXP list)
  `;

(*---------------------------------------------------------------------------------*)
(*      Eval the conditions                                                        *)
(*---------------------------------------------------------------------------------*)

val eval_TCND_def = Define `
    (eval_TCND (v1,EQ,v2) s = (tread s (inR v1) = tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,CS,v2) s = (tread s (inR v1) >=+ tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,MI,v2) s = (let (n,z,c,v) = nzcv (tread s (inR v1)) (tread s (roc_2_exp v2)) in n)) /\
    (eval_TCND (v1,VS,v2) s = (let (n,z,c,v) = nzcv (tread s (inR v1)) (tread s (roc_2_exp v2)) in v)) /\
    (eval_TCND (v1,HI,v2) s = (tread s (inR v1) >+ tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,GE,v2) s = (tread s (inR v1) >= tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,GT,v2) s = (tread s (inR v1) > tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,AL,v2) s = T) /\

    (eval_TCND (v1,NE,v2) s = ~(tread s (inR v1) = tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,CC,v2) s = (tread s (inR v1) <+ tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,PL,v2) s = (let (n,z,c,v) = nzcv (tread s (inR v1)) (tread s (roc_2_exp v2)) in ~n)) /\
    (eval_TCND (v1,VC,v2) s = (let (n,z,c,v) = nzcv (tread s (inR v1)) (tread s (roc_2_exp v2)) in ~v)) /\
    (eval_TCND (v1,LS,v2) s = (tread s (inR v1) <=+ tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,LT,v2) s = (tread s (inR v1) < tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,LE,v2) s = (tread s (inR v1) <= tread s (roc_2_exp v2))) /\
    (eval_TCND (v1,NV,v2) s = F)`;

(*---------------------------------------------------------------------------------*)
(*      Decode assignment statement                                                *)
(*---------------------------------------------------------------------------------*)

val transfer_def = Define `
    (transfer (s1,s0) ([],[]) = s1) /\
    (transfer (s1,s0) (dst::dstL, src::srcL) =
       transfer (twrite s1 dst (tread s0 src), s0) (dstL, srcL))`;

val tdecode_def = Define `
  (!dst src.tdecode hs (TLDR dst src) =
      twrite hs (inR dst) (tread hs (inE src))) /\
  (!dst src.tdecode hs (TSTR dst src) =
      twrite hs (inE dst) (tread hs (inR src))) /\
  (tdecode hs (TMOV dst src) =
      twrite hs (inR dst) (tread hs (roc_2_exp src))) /\
  (tdecode hs (TADD dst src1 src2) =
      twrite hs (inR dst) (tread hs (roc_2_exp src1) + tread hs (roc_2_exp src2))) /\
  (tdecode hs (TSUB dst src1 src2) =
      twrite hs (inR dst) (tread hs (roc_2_exp src1) - tread hs (roc_2_exp src2))) /\
  (tdecode hs (TRSB dst src1 src2) =
      twrite hs (inR dst) (tread hs (roc_2_exp src2) - tread hs (roc_2_exp src1))) /\
  (tdecode hs (TMUL dst src1 src2_reg) =
      twrite hs (inR dst) (tread hs (roc_2_exp src1) * tread hs (roc_2_exp src2_reg))) /\
  (tdecode hs (TAND dst src1 src2) =
      twrite hs (inR dst) (tread hs (roc_2_exp src1) && tread hs (roc_2_exp src2))) /\
  (tdecode hs (TORR dst src1 src2) =
      twrite hs (inR dst) (tread hs (roc_2_exp src1) !! tread hs (roc_2_exp src2))) /\
  (tdecode hs (TEOR dst src1 src2) =
      twrite hs (inR dst) (tread hs (roc_2_exp src1) ?? tread hs (roc_2_exp src2))) /\
  (tdecode hs (TLSL dst src2_reg src2_num) =
      twrite hs (inR dst) (tread hs (roc_2_exp src2_reg) << w2n src2_num)) /\
  (tdecode hs (TLSR dst src2_reg src2_num) =
      twrite hs (inR dst) (tread hs (roc_2_exp src2_reg) >>> w2n src2_num)) /\  
  (tdecode hs (TASR dst src2_reg src2_num) =
      twrite hs (inR dst) (tread hs (roc_2_exp src2_reg) >> w2n src2_num)) /\
  (tdecode hs (TROR dst src2_reg src2_num) =
      twrite hs (inR dst) (tread hs (roc_2_exp src2_reg) #>> w2n src2_num))
(*
  (tdecode hs (TCPY dstL srcL) =
      transfer (hs,hs) (dstL,srcL))
*)
  `;

(*---------------------------------------------------------------------------------*)
(*      Heap and Stack Level (HSL)                                                 *)
(*      Operational Semantics of HSL                                               *)
(*---------------------------------------------------------------------------------*)

val empty_s_def = Define `
    empty_s = (FEMPTY,FEMPTY):TSTATE`;


(* The semantics of HSL, defined on stacks *)

val run_hsl_def = Define `
    (run_hsl (Blk (stm::stmL)) s = 
       run_hsl (Blk stmL) (tdecode s stm)) /\
    (run_hsl (Blk []) s = s) /\
    (run_hsl (Sc S1 S2) s = 
       run_hsl S2 (run_hsl S1 s)) /\
    (run_hsl (Cj cond S1 S2) s =
       (if eval_TCND cond s then run_hsl S1 s else run_hsl S2 s)) /\
    (run_hsl (Tr cond S1) s =
       WHILE (\s'. ~eval_TCND cond s') (run_hsl S1) s) /\
    (run_hsl (Fc (caller_i,callee_i) S_hsl (caller_o,callee_o)) s =
       let s1 = transfer (empty_s, s) (callee_i, caller_i) in
       let s2 = run_hsl S_hsl s1 in
         transfer (s, s2) (caller_o, callee_o))
  `;

(*---------------------------------------------------------------------------------*)
(*      Valid HSL programs                                                         *)
(*      All heap and stack operations in each instruction should be within the     *)
(*        predefined domains                                                       *)
(*      The heap area and the stack area are separate                              *)
(*      Data registers include only r0-r8                                          *)
(*---------------------------------------------------------------------------------*)

val within_bound_def = Define `
  (within_bound (i:num) bound = i < bound)`;

val valid_TEXP_def = Define `
  (valid_TEXP (inE m) bound = within_bound m bound) /\
  (valid_TEXP (inR r) bound = T) /\
  (valid_TEXP (inC _) bound = T)`;

(* valid assignments *)

val valid_assgn_def = Define `
  (valid_assgn (TLDR r m) bound = within_bound m bound) /\
  (valid_assgn (TSTR m r) bound = within_bound m bound) /\
  (valid_assgn _ bound = T)`;

val valid_struct_def = Define `
  (valid_struct (Blk stmL) bound = EVERY (\stm. valid_assgn stm bound) stmL) /\
  (valid_struct (Sc S1 S2) bound = valid_struct S1 bound /\ valid_struct S2 bound) /\
  (valid_struct (Cj cond S_t S_f) bound =
       valid_struct S_t bound /\ valid_struct S_f bound) /\
  (valid_struct (Tr cond S_body) bound =
       valid_struct S_body bound)`;

(*---------------------------------------------------------------------------------*)
(*      Hoare Logic Style Specification                                            *)
(*      Connect combinator form to HSL programs                                    *)
(*---------------------------------------------------------------------------------*)

val CSPEC_def = Define `
    CSPEC S_hsl (in_f, acf, out_f) =
        !v s. (in_f s = v) ==> (out_f (run_hsl S_hsl s) = acf v)`;

(*---------------------------------------------------------------------------------*)
(*      Rules for reductions on basic structures                                   *)
(*      Sc, Cj and Tr rules are analogous to their peers in CFL                    *)
(*---------------------------------------------------------------------------------*)

val Sc_RULE = Q.store_thm (
   "Sc_RULE",
   `!S1 S2 in_f1 f1 f2 out_f1 out_f2.
     CSPEC S1 (in_f1,f1,out_f1) /\ CSPEC S2 (out_f1,f2,out_f2)
       ==>
       CSPEC (Sc S1 S2) (in_f1, sc f1 f2,out_f2)`,

     RW_TAC std_ss [CSPEC_def, run_hsl_def, sc_def]
   );

val Cj_RULE = Q.store_thm (
   "Cj_RULE",
   `!cond St Sf cond_f in_f f1 f2 out_f.
     CSPEC St (in_f,f1,out_f) /\ CSPEC Sf (in_f,f2,out_f) /\ 
     (!s. cond_f (in_f s) = eval_TCND cond s)
        ==>
       CSPEC (Cj cond St Sf) (in_f, cj cond_f f1 f2, out_f)`,

     RW_TAC std_ss [CSPEC_def, run_hsl_def, cj_def] THEN
     METIS_TAC []
   );

val WF_DEF_2 = Q.store_thm (
   "WF_DEF_2",
   `WF R = !P. (?w. P w) ==> ?min. P min /\ !b. R b min ==> ~P b`,
   RW_TAC std_ss [relationTheory.WF_DEF]
  );

val WF_HSL_TR_LEM_2 = Q.store_thm (
   "WF_HSL_TR_LEM_2",
    `!cond S_hsl prj_f f cond_f.
        (!s. cond_f (prj_f s) = eval_TCND cond s) /\ (!s. prj_f (run_hsl S_hsl s) = f (prj_f s)) /\
        WF (\t1 t0. ~cond_f t0 /\ (t1 = f t0)) ==>
           WF (\s1 s0. ~eval_TCND cond s0 /\ (s1 = run_hsl S_hsl s0))`,

   RW_TAC std_ss [WF_DEF_2] THEN
   Q.PAT_ASSUM `!P.p` (ASSUME_TAC o Q.SPEC `\t:'a. ?y:TSTATE. (prj_f y = t) /\ P y`) THEN
   FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
   RES_TAC THEN
   Q.EXISTS_TAC `y` THEN
   RW_TAC std_ss [] THEN
   `~cond_f (prj_f y)` by METIS_TAC [] THEN
   RES_TAC THEN
   Q.PAT_ASSUM `!t1.p` (ASSUME_TAC o Q.SPEC `prj_f (s1:TSTATE)`) THEN
   METIS_TAC []
  );

val WF_HSL_TR_LEM_3 = Q.store_thm (
   "WF_HSL_TR_LEM_3",
   `!cond_f f. (?R. WF R /\ !t0. ~cond_f t0 ==> R (f t0) t0) ==>
            WF (\t1 t0. ~cond_f t0 /\ (t1 = f t0))`,
   RW_TAC std_ss [] THEN
   MATCH_MP_TAC relationTheory.WF_SUBSET THEN
   Q.EXISTS_TAC `R` THEN
   RW_TAC std_ss []
   );

val WF_HSL_TR_THM = Q.store_thm (
   "WF_HSL_TR_THM",
    `!cond S_hsl prj_f f cond_f.
        (!s. cond_f (prj_f s) = eval_TCND cond s) /\ (!s. prj_f (run_hsl S_hsl s) = f (prj_f s)) /\
        (?R. WF R /\ !t0. ~cond_f t0 ==> R (f t0) t0) ==>
           WF (\s1 s0. ~eval_TCND cond s0 /\ (s1 = run_hsl S_hsl s0))`,

    RW_TAC std_ss [] THEN
    METIS_TAC [WF_HSL_TR_LEM_2, WF_HSL_TR_LEM_3]
  );   


val Tr_RULE = Q.store_thm (
   "Tr_RULE",
   `!cond S_hsl cond_f prj_f f.
        (?R. WF R /\ (!x. ~cond_f x ==> R (f x) x)) /\
        (!s. cond_f (prj_f s) = eval_TCND cond s) /\ 
        CSPEC S_hsl (prj_f,f,prj_f) ==>
          CSPEC (Tr cond S_hsl) (prj_f, tr cond_f f, prj_f)`,

    RW_TAC std_ss [CSPEC_def, run_hsl_def] THEN
    IMP_RES_TAC WF_HSL_TR_THM THEN
    IMP_RES_TAC  relationTheory.WF_INDUCTION_THM THEN
    POP_ASSUM (K ALL_TAC) THEN
    Q.ABBREV_TAC `g = run_hsl S_hsl` THEN
    Q.PAT_ASSUM `!P.k` (MATCH_MP_TAC o SIMP_RULE std_ss [] o 
          Q.SPEC `\s. (prj_f (WHILE (\s'. ~eval_TCND cond s') (\a. g a) s) = (tr cond_f f) (prj_f s))`) THEN
    REPEAT STRIP_TAC THEN

    RW_TAC std_ss [Once WHILE] THENL [
      IMP_RES_TAC (DISCH_ALL tr_def) THEN
        POP_ASSUM ((fn th => ONCE_REWRITE_TAC [th]) o Q.SPEC `prj_f (s:TSTATE)`) THEN
        RW_TAC std_ss [],
      METIS_TAC [DISCH_ALL tr_def]
    ]
  );

(*---------------------------------------------------------------------------------*)
(*      Properites of the "transfer" operation                                     *)
(*---------------------------------------------------------------------------------*)

val unique_list_def = Define `
    (unique_list (h::l) = EVERY (\x.~ (x = h)) l /\ unique_list l) /\
    (unique_list [] = T)`;

val notC_def = Define `
    (notC (inC c) = F) /\
    (notC _ = T)`;

val TRANSFER_LEM_1 = Q.store_thm (
   "TRANSFER_LEM_1",
    `!h dstL srcL s1 s0. unique_list (h::dstL) /\ (LENGTH dstL = LENGTH srcL) ==>
       (tread (transfer (s1,s0) (dstL,srcL)) h = tread s1 h)`,

     Induct_on `srcL` THEN Induct_on `dstL` THEN
     RW_TAC list_ss [unique_list_def, transfer_def] THEN
     `?rg sk. s1 = (rg,sk)` by METIS_TAC [ABS_PAIR_THM] THEN
     Cases_on `h` THEN  Cases_on `h''` THEN
     RW_TAC std_ss [tread_def, twrite_def] THEN
     METIS_TAC [FAPPLY_FUPDATE_THM]
   );

val TRANSFER_THM = Q.store_thm (
   "TRANSFER_THM",
   `!dstL srcL s1 s0. unique_list dstL /\ (LENGTH dstL = LENGTH srcL) /\ EVERY notC dstL
       ==>
        (MAP (tread (transfer (s1,s0) (dstL,srcL))) dstL = MAP (tread s0) srcL)`,

   Induct_on `srcL` THEN Induct_on `dstL` THEN
   RW_TAC list_ss [unique_list_def, transfer_def] THEN
   RW_TAC list_ss [SIMP_RULE list_ss [unique_list_def] TRANSFER_LEM_1] THEN
   `?rg sk. s1 = (rg,sk)` by METIS_TAC [ABS_PAIR_THM] THEN
   Cases_on `h` THEN
   FULL_SIMP_TAC std_ss [tread_def, twrite_def, notC_def] THEN
   METIS_TAC [FAPPLY_FUPDATE_THM]
  );

val TRANSFER_INTACT = Q.store_thm (
   "TRANSFER_INTACT",
   `!dstL srcL s1 s0 x. (LENGTH dstL = LENGTH srcL) /\  ~(MEM x dstL)
       ==>
        (tread (transfer (s1,s0) (dstL,srcL)) x = tread s1 x)`,

   Induct_on `srcL` THEN Induct_on `dstL` THEN
   RW_TAC list_ss [transfer_def] THEN
   `?rg sk. s1 = (rg,sk)` by METIS_TAC [ABS_PAIR_THM] THEN
   Cases_on `x` THEN  Cases_on `h` THEN
   FULL_SIMP_TAC std_ss [tread_def, twrite_def] THEN
   METIS_TAC [FAPPLY_FUPDATE_THM]
  );

(*---------------------------------------------------------------------------------*)
(*      Rules for function calls                                                   *)
(*---------------------------------------------------------------------------------*)

val match_def = Define `
    match f lst g = 
      !s:TSTATE. (f s = g (MAP (tread s) lst))`;

val valid_arg_list_def = Define `
    valid_arg_list (caller_i, caller_o, callee_i, callee_o) =
    unique_list caller_o /\ unique_list callee_i /\ 
    (LENGTH caller_i = LENGTH callee_i) /\ (LENGTH caller_o = LENGTH callee_o) /\
    EVERY notC callee_i /\ EVERY notC caller_o`;

val Fc_RULE = Q.store_thm (
   "Fc_RULE",
   `!S_hsl f caller_i caller_o callee_i callee_o caller_i_f caller_o_f callee_i_f callee_o_f g1 g2.
      valid_arg_list (caller_i, caller_o, callee_i, callee_o) /\
      (match caller_i_f caller_i g1 /\ match callee_i_f callee_i g1) /\
      (match caller_o_f caller_o g2 /\ match callee_o_f callee_o g2)
       ==>
        CSPEC S_hsl (callee_i_f,f,callee_o_f) ==>
          CSPEC (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o)) (caller_i_f, f, caller_o_f)`,

   RW_TAC std_ss [valid_arg_list_def, match_def, CSPEC_def, run_hsl_def] THEN
   `(MAP (tread (transfer (s,s2) (caller_o,callee_o))) caller_o = MAP (tread s2) callee_o) /\
    (MAP (tread s) caller_i = MAP (tread s1) callee_i)` by (Q.UNABBREV_TAC `s1` THEN METIS_TAC [TRANSFER_THM]) THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.UNABBREV_TAC `s2` THEN
   METIS_TAC []
  );

(*---------------------------------------------------------------------------------*)

val _ = export_theory();
