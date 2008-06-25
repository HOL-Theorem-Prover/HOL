(*===========================================================================*)
(* Definition of the encryption and decryption algorithms plus               *)
(* proof of correctness.                                                     *)
(*===========================================================================*)

structure aesScript =
struct
(*
  app load ["RoundOpTheory", "metisLib"];
*)
open HolKernel Parse boolLib bossLib RoundOpTheory pairTheory metisLib;

(*---------------------------------------------------------------------------*)
(* Make bindings to pre-existing stuff                                       *)
(*---------------------------------------------------------------------------*)

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

val _ = new_theory "aes";

(*---------------------------------------------------------------------------*)
(* The keyschedule can be represented as a circular buffer of fixed size.    *)
(* It has 11 keys (blocks) in it, and the buffer gets rotated each time      *)
(* a key is taken from it.                                                   *)
(*---------------------------------------------------------------------------*)

val _ = 
  type_abbrev ("keysched", Type`:key#key#key#key#key#key#key#key#key#key#key`);

val FORALL_KEYSCHED = Q.prove
(`(!x:keysched. P x) = !k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11. 
                        P(k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11)`,
 EQ_TAC THEN RW_TAC std_ss [] THEN
 `?a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11. 
     x = (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)`
   by METIS_TAC [ABS_PAIR_THM]
 THEN ASM_REWRITE_TAC[]);


val ROTKEYS_def = 
 Define
   `ROTKEYS (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10) =
            (k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k0) : keysched`;

val REVKEYS_def = 
 Define
   `REVKEYS (k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10) =
            (k10,k9,k8,k7,k6,k5,k4,k3,k2,k1,k0) : keysched`;

val LIST_TO_KEYS_def = 
 Define
  `(LIST_TO_KEYS [] acc = acc) /\
   (LIST_TO_KEYS (h::t) (k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11) =
         LIST_TO_KEYS t (h,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10))`;

val DUMMY_KEYS_def = 
 Define
  `DUMMY_KEYS = (ZERO_BLOCK,ZERO_BLOCK,ZERO_BLOCK,ZERO_BLOCK,
                 ZERO_BLOCK, ZERO_BLOCK,ZERO_BLOCK,ZERO_BLOCK,
                 ZERO_BLOCK,ZERO_BLOCK,ZERO_BLOCK)`;

(*---------------------------------------------------------------------------*)
(* Orchestrate the round computations.                                       *)
(*---------------------------------------------------------------------------*)


val (Round_def, Round_ind) = Defn.tprove
 (Hol_defn 
   "Round"
   `Round n (keys:keysched) (state:state) = 
     if n=0 
      then AddRoundKey (FST keys) (ShiftRows (SubBytes state))
      else Round (n-1) (ROTKEYS keys)
            (AddRoundKey (FST keys) 
              (MixColumns (ShiftRows (SubBytes state))))`,
  WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);


val (InvRound_def,InvRound_ind) = Defn.tprove
 (Hol_defn 
   "InvRound"
   `InvRound n keys state =
      if n=0 
       then AddRoundKey (FST keys) (InvSubBytes (InvShiftRows state))
       else InvRound (n-1) (ROTKEYS keys)
             (InvMixColumns 
               (AddRoundKey (FST keys) (InvSubBytes (InvShiftRows state))))`,
  WF_REL_TAC `measure FST` THEN REPEAT PairRules.PGEN_TAC THEN DECIDE_TAC);

val _ = save_thm ("Round_def", Round_def);
val _ = save_thm ("Round_ind", Round_ind);
val _ = save_thm ("InvRound_def", InvRound_def);
val _ = save_thm ("InvRound_ind", InvRound_ind);

(*---------------------------------------------------------------------------*)
(* Encrypt and Decrypt                                                       *)
(*---------------------------------------------------------------------------*)

val AES_FWD_def = 
 Define 
  `AES_FWD keys = 
    from_state o Round 9 (ROTKEYS keys) o AddRoundKey (FST keys) o to_state`;
     

val AES_BWD_def = 
 Define 
  `AES_BWD keys = 
    from_state o InvRound 9 (ROTKEYS keys) o AddRoundKey (FST keys) o to_state`;
     
(*---------------------------------------------------------------------------*)
(* Main lemma                                                                *)
(*---------------------------------------------------------------------------*)

val [MultCol] = decls "MultCol";
val [InvMultCol] = decls "InvMultCol";
val [genMixColumns] = decls "genMixColumns";

val AES_LEMMA = Q.store_thm
("AES_LEMMA",
 `!(plaintext:state) (keys:keysched). 
     AES_BWD (REVKEYS keys) (AES_FWD keys plaintext) = plaintext`,
 SIMP_TAC std_ss [FORALL_BLOCK] THEN 
 SIMP_TAC std_ss [FORALL_KEYSCHED]
   THEN RESTR_EVAL_TAC [MultCol,InvMultCol,genMixColumns]
   THEN RW_TAC std_ss [ShiftRows_Inversion,SubBytes_Inversion,
                       XOR_BLOCK_IDEM,MixColumns_Inversion,
                       from_state_Inversion,from_state_def]);


(*---------------------------------------------------------------------------
     Generate the key schedule from key. We work using 4-tuples of
     bytes. Unpacking moves from four contiguous 4-tuples to a 16-tuple,
     and also lays the bytes out in the top-to-bottom, left-to-right
     order that the state also has.
 ---------------------------------------------------------------------------*)

val XOR8x4_def = 
 Define 
   `(a,b,c,d) XOR8x4 (a1,b1,c1,d1) = (a # a1, b # b1, c # c1, d # d1)`;

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
(* Sanity check                                                              *)
(*---------------------------------------------------------------------------*)

val keysched_length = Count.apply Q.prove
(`!key. LENGTH (mk_keysched key) = 11`,
 SIMP_TAC std_ss [FORALL_BLOCK,mk_keysched_def]
  THEN REPEAT GEN_TAC 
  THEN EVAL_TAC);

(*---------------------------------------------------------------------------*)
(* Generate key schedule, and its inverse, then build the encryption and     *)
(* decryption functions. Called AES, since it wraps everything up into a     *)
(* single package.                                                           *)
(*---------------------------------------------------------------------------*)

val AES_def = Define
 `AES key = 
   let keys = LIST_TO_KEYS (mk_keysched key) DUMMY_KEYS 
   in (AES_FWD keys, AES_BWD (REVKEYS keys))`;


(*---------------------------------------------------------------------------*)
(* Basic theorem about encryption/decryption                                 *)
(*---------------------------------------------------------------------------*)

val AES_CORRECT = Q.store_thm
  ("AES_CORRECT",
   `!key plaintext. 
      ((encrypt,decrypt) = AES key) 
      ==> 
       (decrypt (encrypt plaintext) = plaintext)`,
 RW_TAC std_ss [AES_def,LET_THM,AES_LEMMA]);


val _ = export_theory();

end
