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

val Rounds_def = 
 Define
   `Rounds (n:word32,s:state) = if n=0w then s else Rounds (n-1w, Round s)`;

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

val (env,sxor_def)  = pass2 ([],ShiftXor_def);
val (env1,rnd_def)  = pass2 (env,Round_def);
val (env2,rnds_def) = pass2 (env1,Rounds_def);  (* fails *)

(*---------------------------------------------------------------------------*)
(* All previous, and closure conversion.                                     *)
(*---------------------------------------------------------------------------*)

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


(*---------------------------------------------------------------------------*)
(* All previous, and register allocation.                                    *)
(*---------------------------------------------------------------------------*)

fun pass4 (env,def) = 
  let val (env1,def1) = pass3 (env,def)
      val def2 = reg_alloc def1
  in 
    (env1,def2)
  end;

val (env,sxor_def)  = pass4 ([],ShiftXor_def);
val (env1,rnd_def)  = pass4 (env,Round_def);
val (env2,rnds_def) = pass4 (env1,Rounds_def);  (* fails *)


