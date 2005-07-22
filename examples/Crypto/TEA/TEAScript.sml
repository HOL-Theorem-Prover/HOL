(*                              TEA, a Tiny Encryption Algorithm                                  *)
(* TEA routine is a Feistel type routine although addition and subtraction are used as the        *)
(* reversible operators rather than XOR. The routine relies on the alternate use of XOR and       *)
(* ADD to provide nonlinearity. A dual shift causes all bits of the key and data to be mixed      *)
(* repeatedly.The number of rounds before a single bit change of the data or key has spread       *)
(* very close to 32 is at most six, so that sixteen cycles may suffice and the authors suggest 32.*)
(* The key is set at 128 bits.                                                                    *)
(* See http://www.ftp.cl.cam.ac.uk/ftp/papers/djw-rmn/djw-rmn-tea.html for more information       *)

(* For interactive work
  quietdec := true;
  app load ["word32Theory"];
  open word32Theory pairTheory arithmeticTheory;
  quietdec := false;
 *)


open HolKernel Parse boolLib bossLib 
     pairTools numLib metisLib pairTheory word32Theory arithmeticTheory;


(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

(*---------------------------------------------------------------------------*)
(* Create the theory.                                                        *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "TEA";

(*---------------------------------------------------------------------------*)
(* Type Definition                                                           *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("block", ``:word32 # word32``);
val _ = type_abbrev("key",   ``:word32 # word32 # word32 # word32``);
val _ = type_abbrev("state", ``:block # key # word32``);

(*---------------------------------------------------------------------------*)
(* Case analysis on a block and a key and a state		             *)
(*---------------------------------------------------------------------------*)

val FORALL_BLOCK = Q.store_thm
  ("FORALL_BLOCK", 
    `(!b:block. P b) = !v0 v1. P (v0,v1)`,
    SIMP_TAC std_ss [FORALL_PROD]);

val FORALL_KEYS = Q.prove
  (`(!x:key. P x) = !k0 k1 k2 k3. P(k0,k1,k2,k3)`,
    METIS_TAC [PAIR]
  );

val FORALL_STATE = Q.prove
 (`(!x:state. P x) = !v0 v1 k0 k1 k2 k3 sum. P((v0,v1),(k0,k1,k2,k3),sum)`,
    METIS_TAC [PAIR]
 );

(* --------------------------------------------------------------------------*)
(*	One round forward computation and one round backward computation     *)
(* --------------------------------------------------------------------------*)

val DELTA_def = Define `DELTA = 0x9e3779b9w`;

val ShiftXor_def = 
 Define 
   `ShiftXor (x,s,k0,k1) = ((x << 4) + k0) # (x + s) # ((x >> 5) + k1)`;

val Round_def = Define
   `Round ((y,z),(k0,k1,k2,k3),sum):state  = 
      ((y + ShiftXor(z, sum+DELTA, k0, k1),
       z + ShiftXor(y + ShiftXor(z, sum+DELTA, k0, k1), sum+DELTA, k2, k3)),
      (k0,k1,k2,k3), sum+DELTA)`;

val InvRound_def = Define
   `InvRound((y,z),(k0,k1,k2,k3),sum)  =
        ((y - ShiftXor(z - ShiftXor(y, sum, k2, k3), sum, k0, k1),
          z - ShiftXor(y, sum, k2, k3)), 
	 (k0,k1,k2,k3), sum-DELTA)`;

val OneRound_Inversion = Q.store_thm
  ("OneRound_Inversion",
  `!s:state. InvRound (Round s) = s`,
  SIMP_TAC std_ss [FORALL_STATE] THEN
  RW_TAC list_ss [Round_def, InvRound_def,WORD_ADD_SUB] 
  );

(*-------------------------------------------------------------------------------*)
(* 32 rounds of computation							 *)
(*-------------------------------------------------------------------------------*)

val (Rounds_def, Rounds_ind) = Defn.tprove
 (Hol_defn
   "Rounds"
   `Rounds n (s:state) = if n=0 then s else Rounds (n-1) (Round s)`,
  WF_REL_TAC `measure FST`);

val (InvRounds_def,InvRounds_ind) = Defn.tprove
 (Hol_defn
   "InvRounds"
   `InvRounds n (s:state) = if n=0 then s else InvRounds (n-1) (InvRound s)`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("Rounds_def", Rounds_def);
val _ = save_thm ("InvRounds_def", InvRounds_def);

val _ = computeLib.add_persistent_funs 
           [("Rounds_def",Rounds_def), 
            ("InvRounds_def",InvRounds_def)];

(*---------------------------------------------------------------------------*)
(* Encrypt and Decrypt                                                       *)
(*---------------------------------------------------------------------------*)

val TEAEncrypt_def = Define `
    TEAEncrypt keys txt =
         FST (Rounds 32 (txt,keys,0w))`;

val TEADecrypt_def = Define `
    TEADecrypt keys txt = 
       FST (InvRounds 32 (txt,keys,DELTA << 5))`;

(*---------------------------------------------------------------------------*)
(* Main lemmas                                                               *)
(*---------------------------------------------------------------------------*)

val Rounds_LEM_1 = Q.prove (
  `!i sum b k. k = FST(SND(Rounds i (b,k,sum)))`,
    Induct_on `i` THENL [
	RW_TAC arith_ss [Ntimes Rounds_def 1],
	SIMP_TAC std_ss [FORALL_BLOCK, FORALL_KEYS] THEN
	RW_TAC arith_ss [Ntimes Rounds_def 1, Round_def] THEN
	METIS_TAC [FST, SND]]	
  );

val [Round] = decls "Round";
val [InvRound] = decls "InvRound";
val [DELTA] = decls "DELTA";

val Rounds_LEM_2 = Q.prove (
  `!sum b k. sum + (DELTA << 5) = SND(SND(Rounds 32 (b,k,sum)))`,
   SIMP_TAC std_ss [FORALL_BLOCK, FORALL_KEYS] THEN
   RESTR_EVAL_TAC [Round, DELTA] THEN
   `!s. SND(SND(Round(s))) = SND(SND(s)) + DELTA` by
  	(SIMP_TAC std_ss [FORALL_STATE] THEN RW_TAC arith_ss [Round_def]) THEN
   RW_TAC list_ss [] THEN
   Q.SUBGOAL_THEN `!i. i << 5 = i * (1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+
	1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w+1w)` (ASSUME_TAC o Q.SPEC `DELTA`) THENL [
     `~(HB < 5)` by RW_TAC arith_ss [HB_def] THEN
     ASSUME_TAC LSL_EVAL THEN FULL_SIMP_TAC arith_ss [ADD_EVAL],
     RW_TAC list_ss [WORD_LEFT_ADD_DISTRIB, WORD_MULT_CLAUSES, WORD_ADD_ASSOC]]   
  );

val TEA_LEMMA = Q.store_thm
("TEA_LEMMA",
 `!(plaintext:block) (keys:key).
     TEADecrypt keys (TEAEncrypt keys plaintext) = plaintext`,
   RW_TAC list_ss [TEAEncrypt_def, TEADecrypt_def] THEN
   ASSUME_TAC ((REWRITE_RULE [WORD_ADD_CLAUSES] o Q.SPECL [`0w`,`plaintext`,`keys`]) Rounds_LEM_2) THEN 
   ASSUME_TAC (Q.SPECL [`32`,`0w`,`plaintext`,`keys`] Rounds_LEM_1) THEN
   Q.ABBREV_TAC `x = Rounds 32 (plaintext,keys,0w)` THEN 
   ONCE_ASM_REWRITE_TAC [] THEN 
   RW_TAC list_ss [] THEN Q.UNABBREV_TAC `x` THEN 
   RESTR_EVAL_TAC [Round, InvRound, DELTA] THEN
   RW_TAC std_ss [OneRound_Inversion]
 );

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)
val TEA_def = Define
 `TEA keys =
    (TEAEncrypt keys, TEADecrypt keys)`;

val TEA_CORRECT = Q.store_thm
  ("TEA_CORRECT",
   `!key plaintext.
       ((encrypt,decrypt) = TEA key)
       ==>
       (decrypt (encrypt plaintext) = plaintext)`,
 RW_TAC std_ss [TEA_def, TEA_LEMMA]);

val _ = export_theory();

