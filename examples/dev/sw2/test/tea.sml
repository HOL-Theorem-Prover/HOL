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

Lib.with_flag (quietdec,true) use "prelim";  

quietdec := true;
open wordsTheory wordsLib pairTheory pairLib;
quietdec := false;

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

val TEAEncrypt_def =
 Define
   `TEAEncrypt (keys,txt) =
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

val TEADecrypt_def =
 Define
   `TEADecrypt (keys,txt) =
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

val lemma = Q.prove
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
 REWRITE_TAC [DELTA_def] THEN WORDS_TAC);

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

val TEA_CORRECT = Q.store_thm
("TEA_CORRECT",
 `!plaintext keys.
     TEADecrypt (keys,TEAEncrypt (keys,plaintext)) = plaintext`,
 RW_TAC list_ss [TEAEncrypt_def, TEADecrypt_def, delta_shift] 
  THEN `(keys1 = keys) /\ (sum = DELTA * 32w)` 
        by METIS_TAC [lemma,WORD_ADD_0,PAIR_EQ] 
  THEN RW_TAC std_ss [] 
  THEN Q.PAT_ASSUM `Rounds x = y` (SUBST_ALL_TAC o SYM) 
  THEN POP_ASSUM MP_TAC 
  THEN computeLib.RESTR_EVAL_TAC 
           (flatten(map decls ["Round", "InvRound", "DELTA"])) 
  THEN RW_TAC std_ss [OneRound_Inversion]);


(*===========================================================================*)
(*  Compilation                                                              *)
(*===========================================================================*)

val teaFns = [ShiftXor_def,Round_def,Rounds_def,TEAEncrypt_def];

compile1 teaFns;

(* TEAEncrypt unwound a bit, but leaves some simplifications still possible *)

compile2 teaFns;

(*---------------------------------------------------------------------------*)
(* All previous, and closure conversion. Not needed for tea, but nevermind   *)
(*---------------------------------------------------------------------------*)

compile3 teaFns;

(*---------------------------------------------------------------------------*)
(* All previous, and register allocation.                                    *)
(*---------------------------------------------------------------------------*)

(* Fails on Rounds *)
compile4 teaFns;

(*---------------------------------------------------------------------------*)
(* Different pass4, in which some intermediate steps are skipped.            *)
(*---------------------------------------------------------------------------*)

fun pass4a (env,def) = 
  let val def1 = pass1 def
      val def2 = reg_alloc def1
  in 
    def2
  end;

val compile4a = complist pass4a;

compile4a teaFns;


(* results:
    |- ShiftXor =
       (\(r0,r1,r2,r3).
          (let r4 = r0 << 4 in
           let r2 = r4 + r2 in
           let r1 = r0 + r1 in
           let r0 = r0 >> 5 in
           let r0 = r0 + r3 in
           let r0 = r1 ?? r0 in
           let r0 = r2 ?? r0 in
             r0)) : thm

    |- Round =
       (\((r0,r1),(r2,r3,r4,r5),r6).
          (let r6 = r6 + DELTA in
           let r7 = ShiftXor (r1,r6,r2,r3) in
           let r0 = r0 + r7 in
           let r7 = ShiftXor (r0,r6,r4,r5) in
           let r1 = r1 + r7 in
             ((r0,r1),(r2,r3,r4,r5),r6))) : thm

    |- Rounds =
       (\(r0,(r1,r2),(r3,r4,r5,r6),r7).
          (let ((r0,r1),(r2,r3,r4,r5),r6) =
                 (if r0 = 0w then
                    ((r1,r2),(r3,r4,r5,r6),r7)
                  else
                    (let r0 = r0 - 1w in
                     let ((r1,r2),(r3,r4,r5,r6),r7) =
                           Round ((r1,r2),(r3,r4,r5,r6),r7)
                     in
                     let ((r0,r1),(r2,r3,r4,r5),r6) =
                           Rounds (r0,(r1,r2),(r3,r4,r5,r6),r7)
                     in
                       ((r0,r1),(r2,r3,r4,r5),r6)))
           in
             ((r0,r1),(r2,r3,r4,r5),r6))) : thm

 |- TEAEncrypt =
       (\((r0,r1,r2,r3),r4,r5).
          (let ((r0,r1),(r2,r3,r4,r5),r6) =
                 Rounds (2w,(r4,r5),(r0,r1,r2,r3),0w)
           in
             (r0,r1))) : thm

*)


(* --------------------------------------------------------------------*)
(* Another configuration:                                              *)
(* Suppose we have only 4 registers available                          *)
(* --------------------------------------------------------------------*)

numRegs := 4;
compile4a teaFns;

(*
Results:
    PASS [|- ShiftXor =
             (\(r0,r1,r2,r3).
                (let m1 = r3 in
                 let r3 = r0 << 4 in
                 let r2 = r3 + r2 in
                 let r1 = r0 + r1 in
                 let r0 = r0 >> 5 in
                 let r3 = m1 in
                 let r0 = r0 + r3 in
                 let r0 = r1 ?? r0 in
                 let r0 = r2 ?? r0 in
                   r0)),
          |- Round =
             (\((r0,r1),(r2,r3,m1,m2),m3).
                (let m4 = r2 in
                 let r2 = m3 in
                 let r2 = r2 + DELTA in
                 let m3 = r3 in
                 let r3 = ShiftXor (r1,r2,m4,m3) in
                 let r0 = r0 + r3 in
                 let r3 = ShiftXor (r0,r2,m1,m2) in
                 let r1 = r1 + r3 in
                   ((r0,r1),(m4,m3,m1,m2),r2))),
          |- Rounds =
             (\(r0,(r1,r2),(r3,m1,m2,m3),m4).
                (let ((r0,r1),(r2,r3,m1,m2),m3) =
                       (if r0 = 0w then
                          ((r1,r2),(r3,m1,m2,m3),m4)
                        else
                          (let r0 = r0 - 1w in
                           let ((r1,r2),(r3,m4,m5,m6),m7) =
                                 Round ((r1,r2),(r3,m1,m2,m3),m4)
                           in
                           let ((r0,r1),(r2,r3,m4,m5),m6) =
                                 Rounds (r0,(r1,r2),(r3,m4,m5,m6),m7)
                           in
                             ((r0,r1),(r2,r3,m4,m5),m6)))
                 in
                   ((r0,r1),(r2,r3,m1,m2),m3))),
          |- TEAEncrypt =
             (\((r0,r1,r2,r3),m1,m2).
                (let ((r0,r1),(r2,r3,m1,m1),m1) =
                       Rounds (2w,(m1,m2),(r0,r1,r2,r3),0w)
                 in
                   (r0,r1)))] : (thm list, thm list * thm list) verdict
*)

(* --------------------------------------------------------------------*)
(* An extreme configuration:                                           *)
(* Suppose we have only 2 registers available                          *)
(* We should have at least 2 registers when binary operations are      *)
(* presented in the program (e.g. add * * * needs 2-3 registers).      *)
(* --------------------------------------------------------------------*)

numRegs := 2;
compile4a teaFns;

(*
    PASS [|- ShiftXor =
             (\(r0,r1,m1,m2).
                (let m3 = r0 in
                 let r0 = m3 in
                 let r0 = r0 << 4 in
                 let m4 = r1 in
                 let r1 = m1 in
                 let r0 = r0 + r1 in
                 let r1 = m3 in
                 let m1 = r0 in
                 let r0 = m4 in
                 let r0 = r1 + r0 in
                 let r1 = m3 in
                 let r1 = r1 >> 5 in
                 let m3 = r0 in
                 let r0 = m2 in
                 let r0 = r1 + r0 in
                 let r1 = m3 in
                 let r0 = r1 ?? r0 in
                 let r1 = m1 in
                 let r0 = r1 ?? r0 in
                   r0)),
          |- Round =
             (\((r0,r1),(m1,m2,m3,m4),m5).
                (let m6 = r1 in
                 let r1 = m5 in
                 let r1 = r1 + DELTA in
                 let m5 = r1 in
                 let r1 = ShiftXor (m6,m5,m1,m2) in
                 let r0 = r0 + r1 in
                 let r1 = ShiftXor (r0,m5,m3,m4) in
                 let m7 = r0 in
                 let r0 = m6 in
                 let r0 = r0 + r1 in
                   ((m7,r0),(m1,m2,m3,m4),m5))),
          |- Rounds =
             (\(r0,(r1,m1),(m2,m3,m4,m5),m6).
                (let ((r0,r1),(m1,m2,m3,m4),m5) =
                       (if r0 = 0w then
                          ((r1,m1),(m2,m3,m4,m5),m6)
                        else
                          (let r0 = r0 - 1w in
                           let ((r1,m6),(m7,m8,m9,m10),m11) =
                                 Round ((r1,m1),(m2,m3,m4,m5),m6)
                           in
                           let ((r0,r1),(m6,m7,m8,m9),m10) =
                                 Rounds (r0,(r1,m6),(m7,m8,m9,m10),m11)
                           in
                             ((r0,r1),(m6,m7,m8,m9),m10)))
                 in
                   ((r0,r1),(m1,m2,m3,m4),m5))),
          |- TEAEncrypt =
             (\((r0,r1,m1,m2),m3,m4).
                (let ((r0,r1),(m1,m1,m1,m1),m1) =
                       Rounds (2w,(m3,m4),(r0,r1,m1,m2),0w)
                 in
                   (r0,r1)))] : (thm list, thm list * thm list) verdict

*)
