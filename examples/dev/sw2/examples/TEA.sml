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

(* for interactive use  
fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
val _ = load_path_add "/examples/mc-logic";
val _ = load_path_add "/examples/ARM/v4";
val _ = load_path_add "/tools/mlyacc/mlyacclib";
val _ = load_path_add "/examples/dev/sw2";
*)

open compiler;

(*---------------------------------------------------------------------------*)
(* Cipher types                                                              *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("state", ``:word32 # word32 # word32 # word32 # word32 # word32 # word32``);

val DELTA_def = Define `DELTA = 1w`;  (* 0xe3779b9w:word32`; *)

val ShiftXor_def = 
 Define 
   `ShiftXor (x:word32,s,k0,k1) = 
          ((x << 4) + k0) ?? (x + s) ?? ((x >> 5) + k1)`;

(* --------------------------------------------------------------------------*)
(*	One round forward computation    				     *)
(* --------------------------------------------------------------------------*)

val Round_def = 
 Define
   `Round ((y,z,k0,k1,k2,k3,s):state) = 
      let s' = s + DELTA in let 
          y' = y + ShiftXor(z, s', k0, k1) 
      in
	(y', z + ShiftXor(y', s', k2, k3),
	 k0,k1,k2,k3,s')`;

val defs1 = [ShiftXor_def, SIMP_RULE std_ss [DELTA_def] Round_def];
val code1 = pp_compile defs1;

(*---------------------------------------------------------------------------*)
(* Arbitrary number of cipher rounds                                         *)
(*---------------------------------------------------------------------------*)

val Rounds_def = 
 Define
   `Rounds (n:word32,s:state) = 
      if n = 0w then s else 
         Rounds (n-1w, Round s)`;

(*
val defs2 = [ShiftXor_def, SIMP_RULE std_ss [DELTA_def] Round_def, Rounds_def];
*)

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
   `InvRound(y,z,k0,k1,k2,k3,sum)  =
        (y - ShiftXor(z - ShiftXor(y, sum, k2, k3), sum, k0, k1),
         z - ShiftXor(y, sum, k2, k3),
         k0,k1,k2,k3,
         sum-DELTA)`;

val inv_defs = [ShiftXor_def, SIMP_RULE std_ss [DELTA_def] InvRound_def];

(*---------------------------------------------------------------------------*)
(* Arbitrary number of decipher rounds                                       *)
(*---------------------------------------------------------------------------*)

val InvRounds_def = 
 Define
   `InvRounds (n:word32,s:state) = 
     if n=0w then s else InvRounds (n-1w, InvRound s)`;

(* val defs = [ShiftXor_def, SIMP_RULE std_ss [DELTA_def] InvRound_def]; *)

(*---------------------------------------------------------------------------*)
(* Decrypt (32 rounds)                                                       *)
(*---------------------------------------------------------------------------*)

val TEADecrypt_def =
 Define
   `TEADecrypt (keys,txt) =
      let (plaintxt,keys,sum) = InvRounds(32w,(txt,keys,DELTA << 5)) 
      in
        plaintxt`;
