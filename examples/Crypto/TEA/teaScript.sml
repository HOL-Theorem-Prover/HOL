(*---------------------------------------------------------------------------*)
(* TEA, a Tiny Encryption Algorithm                                          *)
(* TEA routine is a Feistel type routine although addition and subtraction   *)
(* are used as the reversible operators rather than XOR. The routine relies  *)
(* on the alternate use of XOR and ADD to provide nonlinearity. A dual shift *)
(* causes all bits of the key and data to be mixed repeatedly.The number of  *)
(* rounds before a single bit change of the data or key has spread very      *)
(* close to 32 is at most six, so that sixteen cycles may suffice and the    *)
(* authors suggest 32. The key is set at 128 bits.                           *)
(* See http://www.ftp.cl.cam.ac.uk/ftp/papers/djw-rmn/djw-rmn-tea.html       *)
(* for more information.                                                     *)
(*---------------------------------------------------------------------------*)

(* 
load "wordsLib";
quietdec := true;
*)
open HolKernel Parse boolLib bossLib;
open wordsTheory wordsLib pairTheory pairLib;
(*
quietdec := false;
*)

val _ = new_theory "tea";

val _ = Globals.priming := SOME"_";

val KMATCH_MP_TAC = 
  MATCH_MP_TAC o 
  Ho_Rewrite.REWRITE_RULE [AND_IMP_INTRO,
           METIS_PROVE [] ``(a ==> !x. b x) = !x. a ==> b x``]; 

val WORD_PRED_EXISTS = Q.prove
(`!w:'a word. ~(w = 0w) ==> ?u. w = u + 1w`,
  RW_TAC std_ss [] THEN 
  Q.EXISTS_TAC `w - 1w` THEN 
  RW_TAC std_ss [WORD_SUB_ADD,WORD_ADD_SUB,WORD_MULT_CLAUSES]);


(*---------------------------------------------------------------------------*)
(* Cipher types                                                              *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("block", ``:word32 # word32``);
val _ = type_abbrev("key",   ``:word32 # word32 # word32 # word32``);
val _ = type_abbrev("state", ``:block # key # word32``);

val DELTA_def = Define `DELTA = 0x9e3779b9w:word32`;

val ShiftXor_def = 
 Define 
   `ShiftXor (x:word32,s,k0,k1) = 
          ((x << 4) + k0) ?? (x + s) ?? ((x >> 5) + k1)`;

(* --------------------------------------------------------------------------*)
(*	One round forward computation    				     *)
(* --------------------------------------------------------------------------*)

val Round_def = 
 Define
   `Round ((y,z),(k0,k1,k2,k3),s):state = 
      let s' = s + DELTA in let 
          y' = y + ShiftXor(z, s', k0, k1) 
      in
	((y', z + ShiftXor(y', s', k2, k3)),
	 (k0,k1,k2,k3), s')`;

(*---------------------------------------------------------------------------*)
(* Arbitrary number of cipher rounds                                         *)
(*---------------------------------------------------------------------------*)

val Rounds_def = 
 Define
   `Rounds (n:word32,s:state) = 
      if n=0w then s else Rounds (n-1w, Round s)`;

val Rounds_ind = fetch "-" "Rounds_ind";

(*---------------------------------------------------------------------------*)
(* Encrypt  (32 rounds)                                                      *)
(*---------------------------------------------------------------------------*)

val teaEncrypt_def =
 Define
   `teaEncrypt (keys,txt) =
      let (cipheredtxt,keys,sum) = Rounds(32w,(txt,keys,0w)) in
      cipheredtxt`;

(*===========================================================================*)
(*      Decryption                                                           *)
(*      Analogous to the encryption case                                     *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(*     One round backward computation                                        *)
(*---------------------------------------------------------------------------*)

val InvRound_def =
 Define
   `InvRound((y,z),(k0,k1,k2,k3),sum)  =
        ((y - ShiftXor(z - ShiftXor(y, sum, k2, k3), sum, k0, k1),
          z - ShiftXor(y, sum, k2, k3)),
         (k0,k1,k2,k3),
         sum-DELTA)`;
   
(*---------------------------------------------------------------------------*)
(* Arbitrary number of decipher rounds                                       *)
(*---------------------------------------------------------------------------*)

val InvRounds_def = 
 Define
   `InvRounds (n:word32,s:state) = 
     if n=0w then s else InvRounds (n-1w, InvRound s)`;

(*---------------------------------------------------------------------------*)
(* Decrypt (32 rounds)                                                       *)
(*---------------------------------------------------------------------------*)

val teaDecrypt_def =
 Define
   `teaDecrypt (keys,txt) =
      let (plaintxt,keys,sum) = InvRounds(32w,(txt,keys,DELTA << 5)) 
      in
        plaintxt`;

(*===========================================================================*)
(* Correctness                                                               *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Case analysis on a state                                                  *)
(*---------------------------------------------------------------------------*)

val FORALL_STATE = Q.prove
 (`(!x:state. P x) = !v0 v1 k0 k1 k2 k3 sum. P((v0,v1),(k0,k1,k2,k3),sum)`,
    METIS_TAC [PAIR]
 );

(*---------------------------------------------------------------------------*)
(* Basic inversion lemma                                                     *)
(*---------------------------------------------------------------------------*)

val OneRound_Inversion = Q.store_thm("OneRound_Inversion",
 `!s:state. InvRound (Round s) = s`,
 SIMP_TAC std_ss [FORALL_STATE] THEN
 RW_TAC list_ss [Round_def, InvRound_def,WORD_ADD_SUB, LET_THM]);

(*---------------------------------------------------------------------------*)
(* Tweaked version of Rounds induction.                                      *)
(*---------------------------------------------------------------------------*)

val Rounds_ind' = Q.prove
(`!P. 
   (!(n:word32) b1 k1 s1. 
       (~(n = 0w) ==> P (n - 1w,Round(b1,k1,s1))) ==> P (n,(b1,k1,s1))) ==>
     !i b k s:word32. P (i,b,k,s)`,
 REPEAT STRIP_TAC THEN 
 MATCH_MP_TAC (DISCH_ALL(SPEC_ALL (UNDISCH (SPEC_ALL Rounds_ind)))) THEN
 METIS_TAC [ABS_PAIR_THM]);

(*---------------------------------------------------------------------------*)
(* Main lemmas                                                               *)
(*---------------------------------------------------------------------------*)

val lemma1 = Q.prove
(`!b k sum. ?b1. Round (b,k,sum) = (b1,k,sum+DELTA)`,
 SIMP_TAC std_ss [FORALL_PROD,Round_def,LET_THM]);

val lemma2 = Q.prove
(`!i b k s. ?b1. Rounds (i,b,k,s) = (b1,k,s + DELTA * i)`,
 recInduct Rounds_ind' THEN RW_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [Rounds_def] THEN 
  RW_TAC arith_ss [WORD_MULT_CLAUSES, WORD_ADD_0] THEN
  RES_TAC THEN RW_TAC std_ss [] THENL
  [METIS_TAC [lemma1,FST,SND],
   `?b2. Round(b1,k1,s1) = (b2,k1,s1+DELTA)` by METIS_TAC [lemma1] THEN
   RW_TAC arith_ss [WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC] THEN
   `?m. n = m + 1w` by METIS_TAC [WORD_PRED_EXISTS] THEN 
   RW_TAC std_ss [WORD_ADD_SUB,WORD_MULT_CLAUSES]]);

val delta_shift = Q.prove
(`DELTA << 5 = DELTA * 32w`, 
 REWRITE_TAC [DELTA_def] THEN WORD_EVAL_TAC);

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

val tea_correct = Q.store_thm
("tea_correct",
 `!plaintext keys.
     teaDecrypt (keys,teaEncrypt (keys,plaintext)) = plaintext`,
 RW_TAC list_ss [teaEncrypt_def, teaDecrypt_def, delta_shift] 
  THEN `(keys_1 = keys) /\ (sum = DELTA * 32w)` 
        by METIS_TAC [lemma2,WORD_ADD_0,PAIR_EQ] 
  THEN RW_TAC std_ss [] 
  THEN Q.PAT_ASSUM `Rounds x = y` (SUBST_ALL_TAC o SYM) 
  THEN POP_ASSUM MP_TAC 
  THEN computeLib.RESTR_EVAL_TAC 
           (flatten(map decls ["Round", "InvRound", "DELTA"])) 
  THEN RW_TAC std_ss [OneRound_Inversion]);

(*---------------------------------------------------------------------------*)
(* Generate code                                                             *)
(*---------------------------------------------------------------------------*)

val _ = 
 let open EmitML wordsTheory
     val RW = REWRITE_RULE[GSYM n2w_itself_def, GSYM w2w_itself_def,
           GSYM sw2sw_itself_def, GSYM word_concat_itself_def,
           GSYM word_extract_itself_def, word_T_def, word_L_def, word_H_def]
     val [DELTA_def, ShiftXor_def, Round_def, InvRound_def, 
          Rounds_def, InvRounds_def, teaEncrypt_def, teaDecrypt_def]
         = map RW [DELTA_def, ShiftXor_def, Round_def, InvRound_def, 
                   Rounds_def, InvRounds_def, teaEncrypt_def, teaDecrypt_def]
     val elems = 
     MLSIG "type num = numML.num"::
     MLSIG "type word32 = wordsML.word32"::
     MLSIG "type block = word32 * word32" ::
     MLSIG "type key   = word32 * (word32 * (word32 * word32))" ::
     MLSIG "type state = block * (key * word32)" ::
     MLSIG "val DELTA : word32" ::
     MLSIG "val ShiftXor : key -> word32" ::
     MLSIG "val Round : state -> state" ::
     MLSIG "val InvRound : state -> state" ::
     MLSIG "val Rounds : word32 * state -> state" ::
     MLSIG "val InvRounds : word32 * state -> state" ::
     MLSIG "val teaEncrypt : key * block -> block" ::
     MLSIG "val teaDecrypt : key * block -> block" ::
     OPEN ["num","words"] :: 
     MLSTRUCT "type word32 = wordsML.word32" ::
     MLSTRUCT "type block = word32 * word32" ::
     MLSTRUCT "type key   = word32 * (word32 * (word32 * word32))" ::
     MLSTRUCT "type state = block * (key * word32)" ::
      [DEFN_NOSIG DELTA_def, DEFN_NOSIG ShiftXor_def, 
       DEFN_NOSIG Round_def, DEFN_NOSIG InvRound_def, 
       DEFN_NOSIG Rounds_def, DEFN_NOSIG InvRounds_def, 
       DEFN_NOSIG teaEncrypt_def, DEFN_NOSIG teaDecrypt_def]
 in 
   emitML "./ML/" ("tea",elems)
 end
 handle _ => ();

val _ = export_theory();

