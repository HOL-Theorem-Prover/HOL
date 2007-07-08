(*---------------------------------------------------------------------------*)
(* A version of TEA, taken from examples/Crypto/TEA                          *)
(*---------------------------------------------------------------------------*)

use "prelim";

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
   `Round ((y,z),(k0,k1,k2,k3),s):state  = 
      let s' = s + DELTA in
      let y' = y + ShiftXor(z, s', k0, k1) 
      in
	((y', z + ShiftXor(y', s', k2, k3)),
	 (k0,k1,k2,k3), s')`;

(*---------------------------------------------------------------------------*)
(* Arbitrary number of cipher rounds                                         *)
(*---------------------------------------------------------------------------*)

(*
val Rounds_def = 
 Define
   `Rounds (n:word32,s:state) = if n=0w then s else Rounds (n-1w, Round s)`;
*)

val (Rounds_def, Rounds_ind) = Defn.tprove
 (Hol_defn
   "Rounds"
   `Rounds (n:word32,s:state) = if n=0w then s else Rounds (n-1w, Round s)`,
  WF_REL_TAC `measure (w2n o FST)` THEN
  METIS_TAC [wordsTheory.WORD_PRED_THM]);

(*---------------------------------------------------------------------------*)
(* Encrypt  (32 rounds)                                                      *)
(*---------------------------------------------------------------------------*)

val TEAEncrypt_def =
 Define
   `TEAEncrypt (keys,txt) =
      let (cipheredtxt,keys,sum) = Rounds(2w,(txt,keys,0w)) in
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

val (InvRounds_def, InvRounds_ind) = Defn.tprove
 (Hol_defn
   "InvRounds"
   `InvRounds (n:word32,s:state) = if n=0w then s else InvRounds (n-1w, InvRound s)`,
  WF_REL_TAC `measure (w2n o FST)` THEN
  METIS_TAC [wordsTheory.WORD_PRED_THM]);

(*
val InvRounds_def = 
  Define
   `InvRounds (n:word32,s:state) = 
     if n=0w then s else InvRounds (n-1w, InvRound s)`;
*)

(*---------------------------------------------------------------------------*)
(* Decrypt (32 rounds)                                                       *)
(*---------------------------------------------------------------------------*)

val TEADecrypt_def =
 Define
   `TEADecrypt (keys,txt) =
      let (plaintxt,keys,sum) = InvRounds(32w,(txt,keys,DELTA << 5)) in
      plaintxt`;

(*===========================================================================*)
(*  Compilation                                                              *)
(*===========================================================================*)


(*---------------------------------------------------------------------------*)
(* Basic flattening via CPS and unique names                                 *)
(*---------------------------------------------------------------------------*)

fun pass1 def = SSA_RULE (normalize def);

val sxor_def = pass1 ShiftXor_def;
val rnd_def  = pass1 Round_def;
val rnds_def = pass1 Rounds_def;

(*---------------------------------------------------------------------------*)
(* All previous, plus inlining and optimizations                             *)
(*---------------------------------------------------------------------------*)

fun pass2 (env,def) = 
  let val def1 = pass1 def
      val def2 = SSA_RULE (optimize_norm env def1)
  in 
   (def2::env,def2)
  end;

val (env,sxor_def2)  = pass2 ([],ShiftXor_def);
val (env1,rnd_def2)  = pass2 (env,Round_def);
val (env2,rnds_def2) = pass2 (env1,Rounds_def);

(*---------------------------------------------------------------------------*)
(* All previous, and closure conversion.                                     *)
(*---------------------------------------------------------------------------*)

(*
This phase is not neccessary for the given applications (cryptographic applications)

fun pass3 (env,def) = 
  let val (env1,def1) = pass2 (env,def)
  in case total closure_convert def1
      of SOME thm => 
           let val def2 = SSA_RULE (optimize_norm env thm)
           in (def2::env,def2)
           end
       | NONE => (env1,def1)
  end;

fun compile (env,[]) = PASS(rev env)
  | compile (env,h::t) =
     let val (env1,def1) = pass3 (env,h)
     in compile (env1,t)
     end
     handle HOL_ERR _ => FAIL(env,h::t);

val FAIL (env,notdone) = 
 compile ([],[ShiftXor_def,Round_def,Rounds_def]); 
*)

(*---------------------------------------------------------------------------*)
(* All previous, and register allocation.                                    *)
(*---------------------------------------------------------------------------*)

fun pass4 def = 
  let val def1 = pass1 def
      val def2 = reg_alloc def1
  in 
    def2
  end;

val sxor_fil  = pass4 ShiftXor_def;
val rnd_fil  = pass4 Round_def;
val rnds_fil = pass4 Rounds_def;

(* results:
val sxor_fil =
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

 val rnd_fil =
    |- Round =
       (\((r0,r1),(r2,r3,r4,r5),r6).
          (let r6 = r6 + DELTA in
           let r7 = ShiftXor (r1,r6,r2,r3) in
           let r0 = r0 + r7 in
           let r7 = ShiftXor (r0,r6,r4,r5) in
           let r1 = r1 + r7 in
             ((r0,r1),(r2,r3,r4,r5),r6))) : thm

val rnds_fil =
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
*)


(* --------------------------------------------------------------------*)
(* Another configuration:                                              *)
(* Suppose we have only 4 registers available                          *)
(* --------------------------------------------------------------------*)

numRegs := 4;
reset();

val rnd_fil  = pass4 Round_def;
val rnds_fil = pass4 Rounds_def;

Results:
|- Round =
       (\((r0,r1),(r2,r3,m1,m2),m3).
          (let m4 = r2 in
           let r2 = m3 in
           let r2 = r2 + DELTA in
           let m5 = r3 in
           let m6 = r2 in
           let r3 = ShiftXor (r1,r2,m4,m5) in
           let r0 = r0 + r3 in
           let r3 = ShiftXor (r0,r2,m1,m2) in
           let r1 = r1 + r3 in
             ((r0,r1),(m4,m5,m1,m2),r2))) : thm

val rnds_fil =
    |- Rounds =
       (\(r0,(r1,r2),(r3,m7,m8,m9),m10).
          (let ((r0,r1),(r2,r3,m18,m19),m20) =
                 (if r0 = 0w then
                    ((r1,r2),(r3,m7,m8,m9),m10)
                  else
                    (let r0 = r0 - 1w in
                     let ((r1,r2),(r3,m11,m12,m13),m14) =
                           Round ((r1,r2),(r3,m7,m8,m9),m10)
                     in
                     let ((r0,r1),(r2,r3,m15,m16),m17) =
                           Rounds (r0,(r1,r2),(r3,m11,m12,m13),m14)
                     in
                       ((r0,r1),(r2,r3,m15,m16),m17)))
           in
             ((r0,r1),(r2,r3,m18,m19),m20))) : thm

*)

