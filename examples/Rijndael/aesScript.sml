(*===========================================================================*)
(* Definition of the encryption and decryption algorithms plus               *)
(* proof of correctness.                                                     *)
(*===========================================================================*)

structure aesScript =
struct

open HolKernel boolLib bossLib RoundOpTheory pairTools;

(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

val BLOCK_VAR_TAC = PGEN_TAC (Term `(b0,b1,b2,b3,b4,b5,b6,b7,b8,
                                     b9,b10,b11,b12,b13,b14,b15):block`);

val _ = new_theory "aes";

(*---------------------------------------------------------------------------*)
(* Orchestrate the round computations.                                       *)
(* Similar to:                                                               *)
(*                                                                           *)
(* (Round 0 [key] state = AddRoundKey key (ShiftRows (SubBytes state))) /\   *)
(* (Round n (key::keys) state = Round (n-1) keys                             *)
(*                                (AddRoundKey key                           *)
(*                                  (MixColumns                              *)
(*                                    (ShiftRows (SubBytes state)))))`;      *)
(*---------------------------------------------------------------------------*)

val (Round_def, Round_ind) = Defn.tprove
 (Hol_defn 
   "Round"
   `Round n keys state = 
     if n=0 
      then (case keys 
             of [key] -> AddRoundKey key (ShiftRows (SubBytes state)))
      else (case keys
             of k::rst -> Round (n-1) rst
                             (AddRoundKey k (MixColumns 
                                 (ShiftRows (SubBytes state)))))`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("Round_def", Round_def);
val _ = save_thm ("Round_ind", Round_ind);

(*---------------------------------------------------------------------------*)
(*  (InvRound 0 [key] state = AddRoundKey key                                *)
(*                               (InvSubBytes(InvShiftRows state))) /\       *)
(*  (InvRound n (key::keys) state =                                          *)
(*      InvRound (n-1) keys                                                  *)
(*         (InvMixColumns (AddRoundKey key                                   *)
(*              (InvSubBytes (InvShiftRows state)))))`                       *)
(*---------------------------------------------------------------------------*)

val (InvRound_def,InvRound_ind) = Defn.tprove
 (Hol_defn 
   "InvRound"
   `InvRound n keys state =
      if n=0 
       then (case keys 
              of [key] -> AddRoundKey key 
                            (InvSubBytes
                               (InvShiftRows state)))
       else (case keys
              of k::rst -> InvRound (n-1) rst
                              (InvMixColumns 
                                 (AddRoundKey k 
                                   (InvSubBytes 
                                     (InvShiftRows state)))))`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("InvRound_def", InvRound_def);
val _ = save_thm ("InvRound_ind", InvRound_ind);

(*---------------------------------------------------------------------------*)
(* The following versions are better for computeLib                          *)
(*---------------------------------------------------------------------------*)

val Round_eqns = Q.store_thm
 ("Round_eqns",
  `Round n keys state = 
     if n=0 
      then if LENGTH keys = 1 
             then AddRoundKey (HD keys) (ShiftRows (SubBytes state))
             else ARB
      else if NULL keys then ARB
             else Round (n-1) (TL keys)
                   (AddRoundKey (HD keys) 
                     (MixColumns (ShiftRows (SubBytes state))))`,
 Cases_on `keys` 
   THEN CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [Round_def]))
   THEN RW_TAC list_ss [listTheory.LENGTH_NIL]
   THEN Cases_on `t` THEN FULL_SIMP_TAC list_ss []);


val InvRound_eqns = Q.store_thm
 ("InvRound_eqns",
  `InvRound n keys state =
      if n=0 
       then if LENGTH keys = 1
              then AddRoundKey (HD keys) (InvSubBytes (InvShiftRows state))
              else ARB
       else if NULL keys then ARB
              else InvRound (n-1) (TL keys)
                    (InvMixColumns 
                       (AddRoundKey (HD keys) 
                          (InvSubBytes (InvShiftRows state))))`,
 Cases_on `keys` 
   THEN CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [InvRound_def]))
   THEN RW_TAC list_ss [listTheory.LENGTH_NIL]
   THEN Cases_on `t` THEN FULL_SIMP_TAC list_ss []);

val _ = computeLib.add_persistent_funs [("Round_eqns",Round_eqns)];
val _ = computeLib.add_persistent_funs [("InvRound_eqns",InvRound_eqns)];


(*---------------------------------------------------------------------------
     Generate the key schedule from key. We work using 4-tuples of
     bytes. Unpacking moves from four contiguous 4-tuples to a 16-tuple,
     and also lays the bytes out in the top-to-bottom, left-to-right
     order that the state also has.
 ---------------------------------------------------------------------------*)

val XOR8x4_def = Define `(a,b,c,d) XOR8x4 (a1,b1,c1,d1) 
                                     = 
                                 (a XOR8 a1, 
                                  b XOR8 b1, 
                                  c XOR8 c1, 
                                  d XOR8 d1)`;

val SubWord_def = Define 
   `SubWord(b0,b1,b2,b3) = (Sbox b0, Sbox b1, Sbox b2, Sbox b3)`;

val RotWord_def = Define 
   `RotWord(b0,b1,b2,b3) = (b1,b2,b3,b0)`;

val Rcon_def = Define
   `Rcon i = (PolyExp TWO (i-1), ZERO,ZERO,ZERO)`;

val unpack_def = Define
  `(unpack [] A = A) /\
   (unpack ((a,b,c,d)::(e,f,g,h)::(i,j,k,l)::(m,n,o1,p)::rst) A 
        = unpack rst ((m,i,e,a,n,j,f,b,o1,k,g,c,p,l,h,d)::A))`;

(*---------------------------------------------------------------------------*)
(* Build the keyschedule from a key. This definition is too specific, but    *)
(* works fine for 128 bit blocks.                                            *)
(*---------------------------------------------------------------------------*)

val (expand_def,expand_ind) = 
Defn.tprove 
 (Hol_defn 
   "expand"
   `expand n sched = 
      if 43 < n then unpack sched []
      else let h = HD sched in 
           let h' = if ~(n MOD 4 = 0) then h
                       else SubWord(RotWord h) XOR8x4 Rcon(n DIV 4)
           in expand (n+1) ((h' XOR8x4 (HD(TL(TL(TL sched)))))::sched)`,
  WF_REL_TAC `measure ($- 44 o FST)`);


val _ = save_thm ("expand_def", expand_def);
val _ = save_thm ("expand_ind", expand_ind);
val _ = computeLib.add_persistent_funs [("expand_def", expand_def)];

val mk_keysched_def = Define
 `mk_keysched ((b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15):key)
    = 
  expand 4 [(b12,b13,b14,b15) ; (b8,b9,b10,b11) ;
            (b4,b5,b6,b7)     ; (b0,b1,b2,b3)]`;


(*---------------------------------------------------------------------------*)
(* Generate key schedule, and its inverse, then build the encryption and     *)
(* decryption functions. Called AES, since it wraps everything up into a     *)
(* single package.                                                           *)
(*---------------------------------------------------------------------------*)

val AES_def = Define
 `AES key =
   let sched = mk_keysched key in
   let isched = REVERSE sched 
   in
     ((from_state o Round 9 (TL sched) 
                  o AddRoundKey (HD sched) o to_state),
      (from_state o InvRound 9 (TL isched) 
                  o AddRoundKey (HD isched) o to_state))`;


(*---------------------------------------------------------------------------*)
(* Now let's show that it works for all inputs                               *)
(*---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*)
(* expand is tail recursive and adds a new element to its accumulator at     *)
(* each recursive call.                                                      *)
(*---------------------------------------------------------------------------*)

val lemma = Q.prove
(`!n t. 
    3 < n /\ n < 44 
      ==> 
    ?h. expand (n+1) (h::t) = expand n t`,
 RW_TAC std_ss []
   THEN GEN_REWRITE_TAC (BINDER_CONV o RHS_CONV) empty_rewrites [expand_def]
   THEN ZAP_TAC arith_ss []);


(*---------------------------------------------------------------------------*)
(* Build special purpose proof support for next lemma.                       *)
(*---------------------------------------------------------------------------*)

fun inst_lemma_tac i (asl,w) =
  let open numSyntax boolSyntax
      val j = term_of_int i
      val num_eq = DECIDE (Term `^j + 1 = ^(term_of_int (i+1))`)
      val ineq   = DECIDE (Term `3 < ^j /\ ^j < 44`)
      val lem = GSYM (simpLib.SIMP_RULE std_ss [num_eq,ineq] (SPEC j lemma))
      val pat = lhs(snd(dest_exists(snd(strip_forall (concl lem)))))
      val theta = match_term pat (find_term (can (match_term pat)) w)
  in
    CHOOSE_THEN (fn th => PURE_REWRITE_TAC [th]) 
                (INST (fst theta) (SPEC_ALL lem)) (asl,w)
  end;

val expand_4_lemma = Lib.with_flag(Globals.priming,SOME "")
Q.prove
 (`!a b c d.
   ?h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 
    h21 h22 h23 h24 h25 h26 h27 h28 h29 h30
    h31 h32 h33 h34 h35 h36 h37 h38 h39 h40. 
     expand 44 [h40;h39;h38;h37;h36;h35;h34;h33;h32;h31;h30;h29;h28;
                h27;h26;h25;h24;h23;h22;h21;h20;h19;h18;h17;h16;h15;
                h14;h13;h12;h11;h10;h9;h8;h7;h6;h5;h4;h3;h2;h1;a;b;c;d]
        = 
     expand 4 [a;b;c;d]`,
  REPEAT GEN_TAC 
    THEN EVERY (map inst_lemma_tac (upto 4 43)) 
    THEN PROVE_TAC []);

(*---------------------------------------------------------------------------*)
(* Surprisingly complicated to calculate the length of the list produced by  *)
(* mk_keysched.                                                              *)
(*---------------------------------------------------------------------------*)

val keysched_length = Q.prove
(`!key. LENGTH (mk_keysched key) = 11`,
 PGEN_TAC (Term `(b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15):key`) 
  THEN REWRITE_TAC [mk_keysched_def]
  THEN STRIP_ASSUME_TAC 
       (GSYM (Q.SPECL [`(b12,b13,b14,b15)`, `(b8,b9,b10,b11)`, 
                       `(b4,b5,b6,b7)`,     `(b0,b1,b2,b3)`] expand_4_lemma))
  THEN ASM_REWRITE_TAC[]
  THEN POP_ASSUM (K ALL_TAC)
  THEN EVAL_TAC
  THEN MAP_EVERY Q.ID_SPEC_TAC  
   [`h1`,  `h2`,  `h3`,  `h4`,  `h5`,  `h6`,  `h7`,  `h8`,  `h9`,  `h10`,
    `h11`, `h12`, `h13`, `h14`, `h15`, `h16`, `h17`, `h18`, `h19`, `h20`, 
    `h21`, `h22`, `h23`, `h24`, `h25`, `h26`, `h27`, `h28`, `h29`, `h30`,
    `h31`, `h32`, `h33`, `h34`, `h35`, `h36`, `h37`, `h38`, `h39`, `h40`]
  THEN PGEN_TAC (Term`(h1a,h1b,h1c,h1d):w8x4`)
  THEN PGEN_TAC (Term`(h2a,h2b,h2c,h2d):w8x4`)
  THEN PGEN_TAC (Term`(h3a,h3b,h3c,h3d):w8x4`)
  THEN PGEN_TAC (Term`(h4a,h4b,h4c,h4d):w8x4`)
  THEN PGEN_TAC (Term`(h5a,h5b,h5c,h5d):w8x4`)
  THEN PGEN_TAC (Term`(h6a,h6b,h6c,h6d):w8x4`)
  THEN PGEN_TAC (Term`(h7a,h7b,h7c,h7d):w8x4`)
  THEN PGEN_TAC (Term`(h8a,h8b,h8c,h8d):w8x4`)
  THEN PGEN_TAC (Term`(h9a,h9b,h9c,h9d):w8x4`)
  THEN PGEN_TAC (Term`(h10a,h10b,h10c,h10d):w8x4`)
  THEN PGEN_TAC (Term`(h11a,h11b,h11c,h11d):w8x4`)
  THEN PGEN_TAC (Term`(h12a,h12b,h12c,h12d):w8x4`)
  THEN PGEN_TAC (Term`(h13a,h13b,h13c,h13d):w8x4`)
  THEN PGEN_TAC (Term`(h14a,h14b,h14c,h14d):w8x4`)
  THEN PGEN_TAC (Term`(h15a,h15b,h15c,h15d):w8x4`)
  THEN PGEN_TAC (Term`(h16a,h16b,h16c,h16d):w8x4`)
  THEN PGEN_TAC (Term`(h17a,h17b,h17c,h17d):w8x4`)
  THEN PGEN_TAC (Term`(h18a,h18b,h18c,h18d):w8x4`)
  THEN PGEN_TAC (Term`(h19a,h19b,h19c,h19d):w8x4`)
  THEN PGEN_TAC (Term`(h20a,h20b,h20c,h20d):w8x4`)
  THEN PGEN_TAC (Term`(h21a,h21b,h21c,h21d):w8x4`)
  THEN PGEN_TAC (Term`(h22a,h22b,h22c,h22d):w8x4`)
  THEN PGEN_TAC (Term`(h23a,h23b,h23c,h23d):w8x4`)
  THEN PGEN_TAC (Term`(h24a,h24b,h24c,h24d):w8x4`)
  THEN PGEN_TAC (Term`(h25a,h25b,h25c,h25d):w8x4`)
  THEN PGEN_TAC (Term`(h26a,h26b,h26c,h26d):w8x4`)
  THEN PGEN_TAC (Term`(h27a,h27b,h27c,h27d):w8x4`)
  THEN PGEN_TAC (Term`(h28a,h28b,h28c,h28d):w8x4`)
  THEN PGEN_TAC (Term`(h29a,h29b,h29c,h29d):w8x4`)
  THEN PGEN_TAC (Term`(h30a,h30b,h30c,h30d):w8x4`)
  THEN PGEN_TAC (Term`(h31a,h31b,h31c,h31d):w8x4`)
  THEN PGEN_TAC (Term`(h32a,h32b,h32c,h32d):w8x4`)
  THEN PGEN_TAC (Term`(h33a,h33b,h33c,h33d):w8x4`)
  THEN PGEN_TAC (Term`(h34a,h34b,h34c,h34d):w8x4`)
  THEN PGEN_TAC (Term`(h35a,h35b,h35c,h35d):w8x4`)
  THEN PGEN_TAC (Term`(h36a,h36b,h36c,h36d):w8x4`)
  THEN PGEN_TAC (Term`(h37a,h37b,h37c,h37d):w8x4`)
  THEN PGEN_TAC (Term`(h38a,h38b,h38c,h38d):w8x4`)
  THEN PGEN_TAC (Term`(h39a,h39b,h39c,h39d):w8x4`)
  THEN PGEN_TAC (Term`(h40a,h40b,h40c,h40d):w8x4`)
  THEN EVAL_TAC);

val length_11 = 
 Lib.with_flag(Globals.priming,SOME "")
  Q.prove
 (`!l. (LENGTH l = 11) = 
       ?h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11.
         l = [h1;h2;h3;h4;h5;h6;h7;h8;h9;h10;h11]`,
 GEN_TAC THEN EQ_TAC THENL
 [Cases_on `l`  THEN EVAL_TAC THEN
  Cases_on `t`  THEN EVAL_TAC THEN
  Cases_on `t1` THEN EVAL_TAC THEN
  Cases_on `t`  THEN EVAL_TAC THEN
  Cases_on `t1` THEN EVAL_TAC THEN
  Cases_on `t`  THEN EVAL_TAC THEN
  Cases_on `t1` THEN EVAL_TAC THEN
  Cases_on `t`  THEN EVAL_TAC THEN
  Cases_on `t1` THEN EVAL_TAC THEN
  Cases_on `t`  THEN EVAL_TAC THEN
  Cases_on `t1` THEN EVAL_TAC THEN
  Cases_on `t`  THEN EVAL_TAC THENL [PROVE_TAC [], DECIDE_TAC],
 RW_TAC list_ss [] THEN EVAL_TAC]);


(*---------------------------------------------------------------------------*)
(* Main lemma                                                                *)
(*---------------------------------------------------------------------------*)

val [MultCol] = decls "MultCol";
val [InvMultCol] = decls "InvMultCol";
val [genMixColumns] = decls "genMixColumns";

val lemma = Q.prove
(`!plaintext : state. 
  !sched rsched:state list. 
    (LENGTH sched = 11) /\ (rsched = REVERSE sched)
        ==>
    ((from_state
       o InvRound 9 (TL rsched) 
       o AddRoundKey (HD rsched) 
       o to_state
       o from_state
       o Round 9 (TL sched) 
       o AddRoundKey (HD sched) 
       o to_state) plaintext = plaintext)`,
 BLOCK_VAR_TAC THEN RW_TAC std_ss [length_11]
   THEN RESTR_EVAL_TAC [MultCol,InvMultCol,genMixColumns]
   THEN RW_TAC std_ss [ShiftRows_Inversion,SubBytes_Inversion,
                       XOR_BLOCK_IDEM,MixColumns_Inversion,
                       from_state_Inversion,from_state_def]);


(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

val AES_Correct = Q.store_thm
  ("AES_Correct",
   `!key plaintext. 
       ((encrypt,decrypt) = AES key)
       ==>
       (decrypt (encrypt plaintext) = plaintext)`,
   RW_TAC std_ss [AES_def,GSYM combinTheory.o_ASSOC] THEN
   RW_TAC std_ss [combinTheory.o_THM] THEN
   PROVE_TAC [SIMP_RULE std_ss [combinTheory.o_THM] lemma, keysched_length]);



(*===========================================================================*)
(* Alternative decryption approach and its correctness                       *)
(*===========================================================================*)


(*---------------------------------------------------------------------------*)
(* Map InvMixColumns over the keyschedule before embarking on the            *)
(* alternative inverse round computation. However, do not alter the first or *)
(* last element of the keyschedule.                                          *)
(*---------------------------------------------------------------------------*)

val InvMix_def = Define 
   `(InvMix [x] = [x]) /\
    (InvMix (h::t) = InvMixColumns h::InvMix t)`;

val InvMixify_def = Define 
   `InvMixify (h::t) = h::InvMix t`;


(*---------------------------------------------------------------------------*)
(* Alternative inverse rounds                                                *)
(*                                                                           *)
(*  EqInvRound 0 [key] state = AddRoundKey key                               *)
(*                               (InvShiftRows                               *)
(*                                 (InvSubBytes state)))                     *)
(*  EqInvRound n (key::keys) state =                                         *)
(*      EqInvRound (n-1) keys                                                *)
(*         (AddRoundKey key                                                  *)
(*           (InvMixColumns                                                  *)
(*             (InvShiftRows                                                 *)
(*               (InvSubBytes state))))                                      *)
(*---------------------------------------------------------------------------*)

val (EqInvRound_def,EqInvRound_ind) = Defn.tprove
 (Hol_defn 
   "EqInvRound"
   `EqInvRound n keys state =
      if n=0 
       then (case keys 
              of [key] -> AddRoundKey key 
                            (InvShiftRows 
                               (InvSubBytes(state))))
       else (case keys
              of k::rst -> EqInvRound (n-1) rst
                              (AddRoundKey k 
                                (InvMixColumns 
                                  (InvShiftRows
                                     (InvSubBytes state)))))`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("EqInvRound_def",EqInvRound_def);
val _ = save_thm ("EqInvRound_ind",EqInvRound_ind);

val EqInvRound_eqns = Q.store_thm
("EqInvRound_eqns",
 `EqInvRound n keys state =
      if n=0 
       then if LENGTH keys = 1
               then AddRoundKey (HD keys) (InvShiftRows (InvSubBytes state))
               else ARB
       else if NULL keys then ARB
              else EqInvRound (n-1) (TL keys)
                     (AddRoundKey (HD keys)
                       (InvMixColumns (InvShiftRows (InvSubBytes state))))`,
 Cases_on `keys` 
   THEN CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [EqInvRound_def]))
   THEN RW_TAC list_ss [listTheory.LENGTH_NIL]
   THEN Cases_on `t` THEN FULL_SIMP_TAC list_ss []);

val _ = computeLib.add_persistent_funs [("EqInvRound_eqns",EqInvRound_eqns)];

(*---------------------------------------------------------------------------*)
(* Grab some constants (to help control symbolic evaluation)                 *)
(*---------------------------------------------------------------------------*)

val [InvMixColumns] = decls "InvMixColumns";
val [InvShiftRows]  = decls "InvShiftRows";
val [InvSubBytes]   = decls "InvSubBytes";
val [AddRoundKey]   = decls "AddRoundKey";

(*---------------------------------------------------------------------------*)
(* Prove the equivalence of the alternative scheme                           *)
(*---------------------------------------------------------------------------*)

val Equiv_lemma = Q.prove
(`!sched sched' : state list.
      (LENGTH sched = 11) /\ (sched' = InvMixify sched)
      ==> 
       (EqInvRound 9 (TL sched') o AddRoundKey (HD sched')
         =
        InvRound 9 (TL sched) o AddRoundKey (HD sched))`,
  RW_TAC std_ss [] THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC 
    THEN POP_ASSUM MP_TAC 
    THEN RW_TAC std_ss [length_11]
    THEN RW_TAC list_ss [InvMixify_def]
    THEN MATCH_MP_TAC (PROVE [combinTheory.o_THM] 
           (Term `(!s:state. f s = g s) ==> (f (h s) = g (h s))`))
    THEN RESTR_EVAL_TAC [InvMixColumns,InvShiftRows,AddRoundKey,InvSubBytes]
    THEN RW_TAC std_ss [InvShiftRows_InvSubBytes_Commute,
                        GSYM InvMixColumns_Distrib]);

val LENGTH_REVERSE = Q.prove
(`!l. LENGTH(REVERSE l) = LENGTH l`,
 Induct THEN RW_TAC list_ss []);

(*---------------------------------------------------------------------------*)
(* Encrypt as in AES, but use alternative decryptor.                         *)
(*---------------------------------------------------------------------------*)

val altAES_def = Define
 `altAES key =
   let sched = mk_keysched key in
   let isched = InvMixify (REVERSE sched)
   in
     ((from_state o Round 9 (TL sched) 
                  o AddRoundKey (HD sched) o to_state),
      (from_state o EqInvRound 9 (TL isched) 
                  o AddRoundKey (HD isched) o to_state))`;

(*---------------------------------------------------------------------------*)
(* Equality of AES and altAES                                                *)
(*---------------------------------------------------------------------------*)

val altAES_eq_AES = Q.prove
(`!k. altAES k = AES k`,
 RW_TAC std_ss [altAES_def, AES_def] THEN
 MATCH_MP_TAC (PROVE [combinTheory.o_THM] 
                     (Term `(f=g) ==> (h o f = h o g)`)) THEN
 REWRITE_TAC [combinTheory.o_ASSOC] THEN 
 MATCH_MP_TAC (PROVE [combinTheory.o_THM] (Term `(f=g) ==> (f o h = g o h)`))
 THEN RW_TAC std_ss [Equiv_lemma,LENGTH_REVERSE,keysched_length]);

(*---------------------------------------------------------------------------*)
(* Hence correctness of alternative decryptor                                *)
(*---------------------------------------------------------------------------*)

val altAES_Correct = Q.store_thm
 ("altAES_Correct",
  `!key plaintext. 
       ((encrypt,decrypt) = altAES key)
        ==>
        (decrypt (encrypt plaintext) = plaintext)`,
   PROVE_TAC [AES_Correct,altAES_eq_AES]);

val _ = export_theory();

end
