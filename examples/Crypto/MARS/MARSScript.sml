(*                                   MARS Block Cipher
                                        -- implemented in HOL

 This is a HOL implementation of the encryption algorithm:
                        MARS by IBM
 which is a candidate algorithm in the Advanced Encryption Standard
 For detailed information about MARS, please refer to
        http://www.research.ibm.com/security/mars.html
 in which algorithm specification, Security and performance evaluation, 
 etc. could be found.
*)


(* For interactive work
  quietdec := true;
  app load ["wordsLib","MARS_SboxTheory","MARS_keyExpansionTheory"];
  open arithmeticTheory wordsLib pairTheory listTheory
       MARS_SboxTheory MARS_keyExpansionTheory MARS_DataTheory;
  quietdec := false;
*)

 open HolKernel Parse boolLib bossLib
      arithmeticTheory wordsTheory wordsLib pairTheory listTheory
      MARS_SboxTheory MARS_keyExpansionTheory MARS_DataTheory;

(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;
val ARW_TAC = RW_TAC arith_ss;

(*---------------------------------------------------------------------------*)
(* Create the theory.                                                        *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "MARS";

(*---------------------------------------------------------------------------*)
(*-------------Forward round used by the encrypting function-----------------*)
(*---------------------------------------------------------------------------*)

val E_function_def = Define
   `E_function(A, key1, key2) = 
     let R = ((A #<< 13) * key2) #<< 10  in
     let M = (A + key1) #<< w2n ((R #>> 5) ?? 0x1fw)  in
     let L = (Sbox(l9b(A+key1)) ?? (R #>> 5) ?? R) #<< w2n (R ?? 0x1fw)
     in (L,M,R)`;

val  en_f_rnd_def = Define
    `en_f_rnd ((A,B,C,D),i) =
        let B = (B ?? Sbox0(l8b(A))) + Sbox1(l8b(A #>> 8)) in
        let C = C + Sbox0(l8b(A #>> 16)) in
        let D = D ?? Sbox1(l8b(A #>> 24)) in
        let  A = (A #>> 24) +
        ((if (i=5) \/ (i=1) then B else 0w) + 
         (if (i=4) \/ (i=0) then D else 0w))
        in (B,C,D,A) : block`;

(*First add subkeys to data, then do eight rounds of forward mixing*)
val  (f_mix_def, f_mix_ind)  = Defn.tprove (
    Hol_defn "f_mix"
    `f_mix n (b:block) =
     if n=0 then  b
     else f_mix (n-1) (en_f_rnd(b,n))`,
  WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);

val  en_f_mix_def = Define `
    en_f_mix((A,B,C,D),k) = f_mix 8 (
        A+FST(GETKEYS(k)), B+SND(GETKEYS(k)), C+FST(GETKEYS(ROTKEYS(k))), 
        D+SND(GETKEYS(ROTKEYS(k))))`;

val  en_core_rnd_def = Define `
     en_core_rnd ((A,B,C,D):block, k:keysched, i) =
        let (out1,out2,out3) = E_function(A,FST(GETKEYS(k)),SND(GETKEYS(k))) in
        let A = A #<< 13 in
        let C = C + out2 in
        let B = if i<8 then B+out1 else B ?? out3 in
        let D = if i<8 then D ?? out3 else D + out1
        in (B, C, D, A):block`;

val  (core_def, core_ind) = Defn.tprove (
     Hol_defn "core" 
     `core i (b:block) (k:keysched) = 
     if i = 0 then b
     else core (i-1) (en_core_rnd(b,k,i)) (ROTKEYS(k))`,
   WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);

val  en_core_def = Define `
    en_core (b:block,k:keysched) = core 16 b k`;

val  en_b_rnd_def = Define `
  en_b_rnd ((A,B,C,D),i) =
      let A = if (i=2) \/ (i=6) then A - D else A in
      let A = if (i=3) \/ (i=7) then A - B else A in
      let B = B ?? Sbox1(l8b(A)) in
      let C = C - Sbox0(l8b(A #>> 24)) in
      let D = (D - Sbox1(l8b(A #>> 16))) ?? Sbox0(l8b(A #>> 8)) in
      let A = A #<< 24
      in (B,C,D,A) : block`;

(*Do eight rounds of backwards mixing*)
val  (b_mix_def, b_mix_ind) = Defn.tprove (
   Hol_defn "b_mix"
     `b_mix i (b:block) (k:keysched) = 
     if i = 0 then b
     else b_mix (i-1) (en_b_rnd(b,i)) k`,
   WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);

val  PostWhitening_def = Define `
     PostWhitening ((A,B,C,D),k) = (
        A-FST(GETKEYS(k)), B-SND(GETKEYS(k)), C-FST(GETKEYS(ROTKEYS(k))),
        D-SND(GETKEYS(ROTKEYS(k)))):block`;

val  en_b_mix_def = Define `
   en_b_mix(b:block,k:keysched) = PostWhitening(b_mix 8 b k,k)`;

val _ = save_thm ("f_mix_def", f_mix_def);
val _ = save_thm ("f_mix_ind", f_mix_ind);
val _ = save_thm ("core_def", core_def);
val _ = save_thm ("core_ind", core_ind);
val _ = save_thm ("b_mix_def", b_mix_def);
val _ = save_thm ("b_mix_ind", b_mix_ind);

(*---------------------------------------------------------------------------*)
(*-------------Backward round used by the decrypting function----------------*)
(*---------------------------------------------------------------------------*)
val  de_f_rnd_def = Define
    `de_f_rnd ((A,B,C,D),i) =
     let (A,B,C,D) = (D #>> 24, A, B, C) in
     let D = (D ?? Sbox0(l8b(A #>> 8))) + Sbox1(l8b(A #>> 16)) in
     let C = C + Sbox0(l8b(A #>> 24)) in
     let B = B ?? Sbox1(l8b(A)) in
     let A = if (i=2) \/ (i=6) then A + D else A in
     let A = if (i=3) \/ (i=7) then A + B else A in
     (A, B, C, D) : block`;

val  (inv_f_mix_def, inv_f_mix_ind)  = Defn.tprove (
    Hol_defn "inv_f_mix"
    `inv_f_mix n (b:block) =
     if n=0 then  b
     else de_f_rnd(inv_f_mix (n-1) b,n)`,
  WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);

val  PreWhitening_def = Define `
     PreWhitening ((A,B,C,D),k) = (
        A+FST(GETKEYS(k)), B+SND(GETKEYS(k)), C+FST(GETKEYS(ROTKEYS(k))),
        D+SND(GETKEYS(ROTKEYS(k)))):block`;

val  de_f_mix_def = Define `
    de_f_mix(b,k) = inv_f_mix 8 (PreWhitening(b,k))`;
                                                                                
val  de_core_rnd_def = Define `
     de_core_rnd ((A,B,C,D):block, k:keysched, i) =
        let (A,B,C,D) = (D #>> 13,A,B,C) in
        let (out1,out2,out3) = E_function(A,FST(GETKEYS(k)),SND(GETKEYS(k))) in
        let C = C - out2 in
        let B = if i<8 then B-out1 else B ?? out3 in
        let D = if i<8 then D ?? out3 else D - out1 
        in (A, B, C, D)`;

val  (inv_core_def, inv_core_ind) = Defn.tprove (
     Hol_defn "inv_core"
     `inv_core i (b:block) (k:keysched) =
     if i = 0 then b
     else de_core_rnd(inv_core (i-1) b (ROTKEYS(k)),k,i)`,
   WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);
                                                                                
val  de_core_def = Define `
    de_core (b:block,k:keysched) = inv_core 16 b k`;

val  de_b_rnd_def = Define `
  de_b_rnd ((A,B,C,D),i) =
    let (A,B,C,D) = (D,A,B,C) in
    let A = A - ((if (i=5) \/ (i=1) then B else 0w) + 
        (if (i=4) \/ (i=0) then D else 0w)) in
    let A = A #<< 24 in
    let D = D ?? Sbox1(l8b(A #>> 24)) in
    let C = C - Sbox0(l8b(A #>> 16)) in
    let B = (B - Sbox1(l8b(A #>> 8))) ?? Sbox0(l8b(A))
    in (A,B,C,D):block`;
                                                                                
(*Do eight rounds of backwards mixing*)
val  (inv_b_mix_def, inv_b_mix_ind) = Defn.tprove (
   Hol_defn "inv_b_mix"
     `inv_b_mix i (b:block) (k:keysched) =
     if i = 0 then b
     else de_b_rnd(inv_b_mix (i-1) b k,i)`,
   WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);

val  de_b_mix_def = Define `
   de_b_mix (b:block,k:keysched) = 
   let (A,B,C,D) = inv_b_mix 8 b k in
    (A-FST(GETKEYS(k)), B-SND(GETKEYS(k)),
     C-FST(GETKEYS(ROTKEYS(k))), D-SND(GETKEYS(ROTKEYS(k))))
  `;
                                                                                
val _ = save_thm ("inv_f_mix_def", inv_f_mix_def);
val _ = save_thm ("inv_f_mix_ind", inv_f_mix_ind);
val _ = save_thm ("inv_core_def", inv_core_def);
val _ = save_thm ("inv_core_ind", inv_core_ind);
val _ = save_thm ("inv_b_mix_def", inv_b_mix_def);
val _ = save_thm ("inv_b_mix_ind", inv_b_mix_ind);

(*---------------------------------------------------------------------------*)
(*-------------Forward and backward round operation inversion lemmas---------*)
(*---------------------------------------------------------------------------*)

(* -------------------First comes the foward mixing operations --------------*)
val Fwd_Mix_Inversion = Q.store_thm
  ("Fwd_Mix_Inversion",
  `!b i. de_b_rnd(en_f_rnd(b,i),i) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK, en_f_rnd_def, de_b_rnd_def, LET_THM]
    THEN SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val [en_f_rnd] = decls "en_f_rnd";
val [de_b_rnd] = decls "de_b_rnd";

val Fwd_Mix_LEMMA = Q.store_thm
("Fwd_Mix_LEMMA",
 `!b:block k:keysched. de_b_mix(en_f_mix(b,k),k) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK]
    THEN RESTR_EVAL_TAC [en_f_rnd, de_b_rnd]
    THEN SRW_TAC [] [Fwd_Mix_Inversion]);

(* ------------------Then the keyed transformation operations ---------------*)
val PBETA_ss = simpLib.conv_ss
  {name="PBETA",trace = 3,conv=K (K PairRules.PBETA_CONV),
   key = SOME([],``(\(x:'a,y:'b). s1) s2:'c``)};

val Core_Inversion = Q.store_thm
  ("Core_Inversion",
  `!b k i. de_core_rnd(en_core_rnd(b,k,i),k,i) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK]
    THEN SRW_TAC [PBETA_ss,boolSimps.LET_ss] [en_core_rnd_def,de_core_rnd_def]);

val [en_core_rnd] = decls "en_core_rnd";
val [de_core_rnd] = decls "de_core_rnd";
                                                                   
val Keyed_Trans_LEMMA = Q.store_thm
("Keyed_Trans_LEMMA",
 `!b:block k:keysched. de_core(en_core(b,k),k) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK]
    THEN RESTR_EVAL_TAC [en_core_rnd, de_core_rnd]
    THEN RW_TAC std_ss [Core_Inversion]);

(* -------------------Finally the backward mixing operations ----------------*)
val Bwd_Mix_Inversion = Q.store_thm
  ("Bwd_Mix_Inversion",
  `!b i. de_f_rnd(en_b_rnd(b,i),i) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK, en_b_rnd_def, de_f_rnd_def, LET_THM]
    THEN SRW_TAC [] []);

val Whitening_Inversion = Q.store_thm
  ("Whitening_Inversion",
  `!b k. PreWhitening(PostWhitening(b,k),k) = b`,
  SIMP_TAC std_ss [FORALL_BLOCK]
    THEN SRW_TAC [] [PreWhitening_def, PostWhitening_def]);

val [en_b_rnd] = decls "en_b_rnd";
val [de_f_rnd] = decls "de_f_rnd";
                                         
val Bwd_Mix_LEMMA = Q.store_thm
("Bwd_Mix_LEMMA",
 `!b:block k:keysched. de_f_mix(en_b_mix(b,k),k) = b`,
   SIMP_TAC std_ss [FORALL_BLOCK] THEN RESTR_EVAL_TAC [en_b_rnd, de_f_rnd]
     THEN RW_TAC std_ss [Whitening_Inversion, Bwd_Mix_Inversion]);

(*---------------------------------------------------------------------------*)
(* Encrypt and Decrypt                                                       *)
(*---------------------------------------------------------------------------*)
val MARSEncrypt_def  =  Define `
    MARSEncrypt k b = en_b_mix(
        en_core(en_f_mix(b,k),ROTKEYS(ROTKEYS(k))),
        ROTKEYS18(k))`;

val MARSDecrypt_def  =  Define `
    MARSDecrypt k b = de_b_mix(
        de_core(de_f_mix(b,ROTKEYS18(k)), ROTKEYS(ROTKEYS(k))), k)`;

(*---------------------------------------------------------------------------*)
(* Main lemma                                                                *)
(*---------------------------------------------------------------------------*)
val MARS_LEMMA = Q.store_thm
("MARS_LEMMA",
 `!(plaintext:block) (keys:keysched).
     MARSDecrypt keys (MARSEncrypt keys plaintext) = plaintext`,
   RW_TAC std_ss [MARSEncrypt_def,MARSDecrypt_def] THEN
   RW_TAC std_ss [Fwd_Mix_LEMMA, Keyed_Trans_LEMMA, Bwd_Mix_LEMMA]);

(*---------------------------------------------------------------------------*)
(* Sanity check                                                              *)
(*---------------------------------------------------------------------------*)
val keysched_length = Q.prove
  (`!k. LENGTH (key_expansion k) = 40`,
      SIMP_TAC std_ss [key_expansion_def, mul_def]
      THEN RW_TAC list_ss [INIT_K_LENGTH, MUL_RND_LENGTH]);

(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)
val MARS_def = Define
 `MARS (key) =
   let keys = LIST_TO_KEYS (key_expansion(key)) DUMMY_KEYS 
   in (MARSEncrypt keys,  MARSDecrypt keys)`;
                                          
val MARS_CORRECT = Q.store_thm
  ("MARS_CORRECT",
   `!key plaintext.
       ((encrypt,decrypt) = MARS key)
       ==>
       (decrypt (encrypt plaintext) = plaintext)`,
         RW_TAC std_ss [MARS_def,LET_THM,MARS_LEMMA]);
                               
val _ = export_theory();
