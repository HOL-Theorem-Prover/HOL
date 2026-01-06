(*---------------------------------------------------------------------------*)
(*             RC6 Block Cipher (RC6-w/r/b, w = 32, r = 20)                  *)
(*                                        -- implemented in HOL              *)
(*                                                                           *)
(* This is a HOL implementation of the RC6 encryption algorithm due to       *)
(* Ron Rivest and RSA Labs which was a candidate algorithm in the Advanced   *)
(* Encryption Standard. For detailed information about RC6, please refer to  *)
(*        http://www.rsasecurity.com/rsalabs/node.asp?id=2512                *)
(* in which algorithm specification, Security and performance evaluation,    *)
(* etc. can be found.                                                        *)
(*---------------------------------------------------------------------------*)
Theory RC6
Ancestors
  arithmetic pair list words
Libs
  wordsLib


(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

(*---------------------------------------------------------------------------*)
(* Create the theory.                                                        *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Type Definitions                                                          *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("block", ``:word32 # word32 # word32 # word32``);

val _ = type_abbrev("key",   ``:word32 # word32``);

val _ = type_abbrev("keysched",
        ``:word32 # word32 # word32 # word32 # word32 # word32 # word32 #
           word32 # word32 # word32 # word32 # word32 # word32 # word32 #
           word32 # word32 # word32 # word32 # word32 # word32 # word32 #
           word32 # word32 # word32 # word32 # word32 # word32 # word32 #
           word32 # word32 # word32 # word32 # word32 # word32 # word32 #
           word32 # word32 # word32 # word32 # word32 # word32 # word32 #
           word32 # word32``);

val _ = type_abbrev("state", ``:word32#word32#word32#word32#word32#word32``);

(*---------------------------------------------------------------------------*)
(* Case analysis on blocks and keys.                                         *)
(*---------------------------------------------------------------------------*)

Theorem FORALL_BLOCK:
     (!b:block. P b) = !v0 v1 v2 v3. P (v0,v1,v2,v3)
Proof
    SIMP_TAC std_ss [FORALL_PROD]
QED

val FORALL_KEYS = Q.prove
(`(!x:key. P x) = !k0 k1. P(k0,k1)`,
  SIMP_TAC std_ss [FORALL_PROD]);

(* --------------------------------------------------------------------------*)
(*      Rotation operators                                                   *)
(* --------------------------------------------------------------------------*)

Definition LeftShift_def:
    LeftShift (x:word32) (n:word32) = x #<< (w2n n)
End

Definition RightShift_def:
    RightShift (x:word32) (n:word32) = x #>> (w2n n)
End

val _ = augment_srw_ss [rewrites [LeftShift_def, RightShift_def]];

val _ = overload_on ("<<<",Term`$LeftShift`);
val _ = overload_on (">>>",Term`$RightShift`);
val _ = set_fixity "<<<" (Infixl 625);
val _ = set_fixity ">>>" (Infixl 625);

(*
val EX_Shift_Lemma = Q.store_thm
   ("EX_Shift_Lemma",
   `!n. w2n n MOD WL < WL`,
    ARW_TAC [WL_def, HB_def] THEN ARW_TAC [DIVISION]);

val EX_Shift_Inversion = Q.store_thm
  ("EX_Shift_Inversion",
  `!s n. (s >>> n <<< n = s) /\ (s <<< n >>> n = s)`,
  ASSUME_TAC EX_Shift_Lemma THEN
  REWRITE_TAC [LeftShift_def, RightShift_def] THEN ARW_TAC [SHIFT_Inversion]);
*)

(* --------------------------------------------------------------------------*)
(*      One round forward computation and one round backward computation     *)
(* --------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*  r is the number of rounds                                                *)
(*---------------------------------------------------------------------------*)

Definition r_def:   r = 20
End

Definition CompUT_def:
    CompUT (x:word32) = (x * (x + x + 1w)) #<< 5
End

Definition FwdRound_def:
   FwdRound ((a,b,c,d):block) ((k0,k1):key)  =
        (b,
         ((c ?? CompUT d) <<< CompUT b) + k1,  (*c = (c xor u <<< t) + k1*)
         d,
         ((a ?? CompUT b) <<< CompUT d) + k0)
End

Definition BwdRound_def:
   BwdRound ((a,b,c,d):block) ((k0,k1):key)  =  (* NB: (a,b,c,d) = (d,a,b,c) *)
        (((d - k0) >>> CompUT c) ?? CompUT a,   (* a = ((a-k0) >>> u) xor t  *)
         a,
         ((b - k1) >>> CompUT a) ?? CompUT c,   (* c = ((c-k1) >>> t) xor u  *)
         c)
End

Theorem OneRound_Inversion:
   !b:block k:key. BwdRound (FwdRound b k) k = b
Proof
  SIMP_TAC std_ss [FORALL_BLOCK, FORALL_KEYS]
    THEN SRW_TAC [] [FwdRound_def, BwdRound_def]
QED

(*---------------------------------------------------------------------------*)
(* Rotate keys and get a pair of keys from the head of the key schedule      *)
(*---------------------------------------------------------------------------*)

Definition ROTKEYS_def:
    ROTKEYS (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,
      k13,k14,k15,k16,k17,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27,
      k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39,k40,k41,k42,k43)
    =
     (k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,
      k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,
      k34,k35,k36,k37,k38,k39,k40,k41,k42,k43,k0,k1) : keysched
End

Definition GETKEYS_def:
    GETKEYS ((k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,
      k16,k17,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,
      k31,k32,k33,k34,k35,k36,k37,k38,k39,k40,k41,k42,k43) : keysched)
    = (k0,k1):key
End

(*---------------------------------------------------------------------------*)
(* Pre-Whitening and post-whitening in the encryption and the decryption     *)
(* Note the difference of the key schedules between Round and InvRound. We   *)
(* should make sure that corresponding Round and InvRound use the same keys  *)
(*---------------------------------------------------------------------------*)

Definition PreWhitening_def:
  PreWhitening (k:keysched) ((a,b,c,d):block)  =
            (a, b + FST(GETKEYS(k)), c, d + SND(GETKEYS(k))) : block
End

Definition PostWhitening_def:
  PostWhitening  (k:keysched) ((a,b,c,d):block)  =
            (a + SND(GETKEYS(k)), b, c + SND(GETKEYS(k)), d) : block
End

Definition InvPreWhitening_def:
  InvPreWhitening (k:keysched) ((a,b,c,d):block)  =
            (a - SND(GETKEYS(k)), b, c - SND(GETKEYS(k)), d) : block
End

Definition InvPostWhitening_def:
  InvPostWhitening (k:keysched) ((a,b,c,d):block)  =
            (a, b - FST(GETKEYS(k)), c, d - SND(GETKEYS(k))) : block
End

Theorem Whitening_Inversion:
   !b k. (InvPostWhitening k (PreWhitening k b) = b) /\
         (InvPreWhitening k (PostWhitening k b) = b)
Proof
  SIMP_TAC std_ss [FORALL_BLOCK]
    THEN SRW_TAC [] [InvPostWhitening_def, PreWhitening_def,
                     InvPreWhitening_def, PostWhitening_def]
QED

(*---------------------------------------------------------------------------*)
(* Round operations in the encryption and the decryption. Slow to define.    *)
(*---------------------------------------------------------------------------*)

val Round_def =
 tDefine
   "Round"
   `Round n (k:keysched) (b:block) =
     if n=0
      then PostWhitening k b
      else Round (n-1) (ROTKEYS k) (FwdRound b (GETKEYS k))`
  (WF_REL_TAC `measure FST` THEN RW_TAC arith_ss [ELIM_UNCURRY]);

val Round_ind = fetch "-" "Round_ind";

(*---------------------------------------------------------------------------*)
(* Note the difference between Round and InvRound -- we should make sure     *)
(* that PreWhitening and PostWhitening use the same key pair                 *)
(*---------------------------------------------------------------------------*)

val InvRound_def =
 tDefine
   "InvRound"
   `InvRound n k b =
      if n=0
       then InvPreWhitening k b
       else BwdRound (InvRound (n-1) (ROTKEYS k) b) (GETKEYS k)`
  (WF_REL_TAC `measure FST` THEN RW_TAC arith_ss [ELIM_UNCURRY]);


(*---------------------------------------------------------------------------*)
(* Encrypt and Decrypt                                                       *)
(* The number of rounds is 20. It is easy to change it into any value, but   *)
(* in this case you should redefine the type keysched                        *)
(*---------------------------------------------------------------------------*)

Definition RC6_FWD_def:
    RC6_FWD keys = Round r keys o PreWhitening keys
End

Definition RC6_BWD_def:
    RC6_BWD keys = InvPostWhitening keys o InvRound r keys
End

(*---------------------------------------------------------------------------*)
(* Main lemma                                                                *)
(*---------------------------------------------------------------------------*)

val [FwdRound] = decls "FwdRound";
val [BwdRound] = decls "BwdRound";

Theorem RC6_LEMMA:
  !(plaintext:block) (keys:keysched).
     RC6_BWD keys (RC6_FWD keys plaintext) = plaintext
Proof
   RESTR_EVAL_TAC [FwdRound, BwdRound] THEN
   RW_TAC std_ss [OneRound_Inversion, Whitening_Inversion]
QED

(*---------------------------------------------------------------------------*)
(* Build the keyschedule from a key. This definition is too specific, but    *)
(* works fine for 128 bit blocks.                                            *)
(*---------------------------------------------------------------------------*)

Definition LIST_TO_KEYS_def:
   (LIST_TO_KEYS [] acc = acc : keysched) /\
   (LIST_TO_KEYS (h::t)
      (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
       k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,
       k38,k39,k40,k41,k42,k43)
     =
      LIST_TO_KEYS t
       (h,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,
        k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,
        k37,k38,k39,k40,k41,k42,k43))
End

Definition DUMMY_KEYS_def:
   DUMMY_KEYS =
     (0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
      0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
      0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
      0w,0w,0w,0w,0w,0w,0w,0w,0w,0w,
      0w,0w,0w,0w) : keysched
End

Definition Pw_def:
    Pw = 0xB7E15163w:word32
End

Definition Qw_def:
    Qw = 0x9E3779B9w:word32
End

Definition init_S_def:
   (init_S 0 = [Pw]) /\
   (init_S (SUC n) = (HD (init_S n) + Qw) :: (init_S n))
End

Definition setKeys_def:
   (setKeys 0 S1 L a b = []) /\
   (setKeys (SUC n) S1 L a b =
     let a = (HD S1 + a + b) #<< 3 in
     let b = (HD L + a + b) <<< (a+b) in
         a::setKeys n (TL S1 ++ [a]) (TL L ++ [b]) a b)
End

Definition mk_keysched_def:
    mk_keysched(L) = setKeys (r*2+4) (REVERSE(init_S (2*r-3))) L 0w 0w
End

val setKeys_length = Q.prove
 (`!i S1 L a b. i>0 ==>
        (LENGTH (setKeys i S1 L a b) = SUC(LENGTH (setKeys (i-1) S1 L a b)))`,
  Induct_on `i` THENL [
    RW_TAC list_ss [],
    RW_TAC list_ss [Ntimes setKeys_def 1] THEN
    Cases_on `i=0` THENL [
        RW_TAC list_ss [setKeys_def],
        Q.SUBGOAL_THEN
         `!i S1 L1 a1 b1 S2 L2 a2 b2.
             LENGTH (setKeys i S1 L1 a1 b1) = LENGTH (setKeys i S2 L2 a2 b2)`
        ASSUME_TAC THENL [
            NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
            Induct_on `i` THENL [
                RW_TAC list_ss [setKeys_def],
                RW_TAC list_ss [setKeys_def] THEN RW_TAC list_ss [LENGTH]],
        RW_TAC list_ss []]]]
  );

(*---------------------------------------------------------------------------*)
(* Sanity check                                                              *)
(*---------------------------------------------------------------------------*)

val keysched_length = Q.prove
 (`!L. LENGTH (mk_keysched L) = r*2+4`,
    RW_TAC list_ss [mk_keysched_def, r_def] THEN
    RW_TAC list_ss [setKeys_length] THEN
    RW_TAC arith_ss [setKeys_def, LENGTH]
  );

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

Definition RC6_def:
  RC6 key =
   let keys = LIST_TO_KEYS (mk_keysched key) DUMMY_KEYS
   in (RC6_FWD keys, RC6_BWD keys)
End

Theorem RC6_CORRECT:
    !key plaintext.
       ((encrypt,decrypt) = RC6 key)
       ==>
       (decrypt (encrypt plaintext) = plaintext)
Proof
         RW_TAC std_ss [RC6_def,LET_THM,RC6_LEMMA]
QED
