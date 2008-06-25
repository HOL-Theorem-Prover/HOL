(*===========================================================================*)
(* Lazy list version of TEA.                                                 *)
(*===========================================================================*)

(*
app load ["wordsLib","llistTheory","teaTheory"];
quietdec := true;
*)
open HolKernel Parse boolLib bossLib wordsLib
     wordsTheory pairTheory arithmeticTheory 
     llistTheory optionTheory teaTheory;
(*
quietdec := false;
*)

(*---------------------------------------------------------------------------*)
(* Create the theory.                                                        *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "lazy_tea";

(*---------------------------------------------------------------------------*)
(* Support for defining a stream of Round computations.                      *)
(*---------------------------------------------------------------------------*)

val RoundFun_def = 
 Define 
   `RoundFun (s: state) = SOME (Round s, FST (Round s))`;

val StreamG_def = new_specification 
 ("StreamG",
  ["StreamG"],
  ISPEC ``RoundFun`` llist_Axiom_1);

val FUNPOW_LEM = Q.prove
(`!n f x. FUNPOW f (SUC n) (f x) = f (FUNPOW f (SUC n) x)`,
 Induct THEN RW_TAC arith_ss [FUNPOW]);

val LNTH_FWD_UNROLL = Q.prove 
(`!n s. THE (LNTH n (StreamG s)) = FST (FUNPOW Round (SUC n) s)`,
 Induct_on `n` THENL 
 [SIMP_TAC std_ss [FORALL_STATE, LNTH, FUNPOW] THEN
  RW_TAC list_ss [Ntimes StreamG_def 1,RoundFun_def,LHD_THM,LTL_THM,LET_THM],
  SIMP_TAC list_ss [FORALL_STATE, Ntimes StreamG_def 1, Once FUNPOW_SUC] THEN
  RW_TAC list_ss [FUNPOW_LEM, RoundFun_def, LNTH_THM, LTL_THM]]);


(*---------------------------------------------------------------------------*)
(* Decryption                                                                *)
(*---------------------------------------------------------------------------*)

val InvRoundFun_def = 
 Define 
   `InvRoundFun (s: state) = SOME (InvRound s, FST (InvRound s))`;

val InvStreamG_def = new_specification 
 ("InvStreamG",
  ["InvStreamG"],
  ISPEC ``InvRoundFun`` llist_Axiom_1);

val LNTH_BWD_UNROLL = Q.prove 
(`!n s. THE (LNTH n (InvStreamG s)) = FST (FUNPOW InvRound (SUC n) s)`,
 Induct_on `n` THENL
 [SIMP_TAC std_ss [FORALL_STATE, LNTH, FUNPOW] THEN
  RW_TAC list_ss 
     [Ntimes InvStreamG_def 1, InvRoundFun_def,LHD_THM,LTL_THM,LET_THM],
  SIMP_TAC list_ss [FORALL_STATE, Once InvStreamG_def, Once FUNPOW_SUC] THEN
  RW_TAC list_ss [FUNPOW_LEM, InvRoundFun_def, LNTH_THM, LTL_THM]]);

(*---------------------------------------------------------------------------*)
(* Encrypt and Decrypt                                                       *)
(*---------------------------------------------------------------------------*)

val lazy_teaEncrypt_def = 
 Define 
   `lazy_teaEncrypt keys txt = THE(LNTH 31 (StreamG(txt,keys,0w)))`;

val lazy_teaDecrypt_def = 
 Define 
  `lazy_teaDecrypt keys txt = THE(LNTH 31 (InvStreamG(txt,keys,DELTA << 5)))`;

(*---------------------------------------------------------------------------*)
(* Main lemmas                                                               *)
(*---------------------------------------------------------------------------*)

val lemma1 = Q.prove
(`!a. FUNPOW Round 32 a = Rounds (32w,a)`, GEN_TAC THEN EVAL_TAC);

val lemma2 = Q.prove
(`!a. FUNPOW InvRound 32 a = InvRounds (32w,a)`, GEN_TAC THEN EVAL_TAC);

val teaEncrypt_lemma = Q.prove
(`teaEncrypt(k,t) = FST(FUNPOW Round 32 (t,k,0w))`,
 RW_TAC std_ss [teaEncrypt_def,lemma1] THEN RW_TAC std_ss []);

val teaDecrypt_lemma = Q.prove
(`teaDecrypt(k,t) = FST(FUNPOW InvRound 32 (t,k,DELTA << 5))`,
 RW_TAC std_ss [teaDecrypt_def,lemma2] THEN RW_TAC std_ss []);

val lazy_tea_correct = Q.store_thm
("lazy_tea_correct",
 `!plaintext keys.
   lazy_teaDecrypt keys (lazy_teaEncrypt keys plaintext) = plaintext`,
  RW_TAC list_ss 
    [lazy_teaEncrypt_def, lazy_teaDecrypt_def, 
     LNTH_FWD_UNROLL,LNTH_BWD_UNROLL,
     GSYM teaEncrypt_lemma,GSYM teaDecrypt_lemma] THEN
  METIS_TAC [tea_correct]);

val _ = export_theory();
