(*---------------------------------------------------------------------------*)
(* Modes of operation (ECB, CBC, CFB, CFB, CTR) and padding                  *)
(* Currently only formalizes ECB and CBC modes.                              *)
(*---------------------------------------------------------------------------*)

(* Interactive:
   open combinTheory
*)
open HolKernel Parse boolLib bossLib combinTheory;

val _ = Defn.def_suffix := "_DEF";

val _ = new_theory "modes"

val MAP_MAP_COMPOSE = Q.prove
(`!l (f:'a->'b) (g:'b->'c). MAP g (MAP f l) = MAP (g o f) l`,
 Induct THEN RW_TAC list_ss []);

val MAP_I_THM = Q.prove
(`!l. MAP I l = l`,
 Induct THEN RW_TAC list_ss [combinTheory.I_THM]);

(*---------------------------------------------------------------------------*)
(* Electronic Code Book is just MAP.                                         *)
(*---------------------------------------------------------------------------*)

val ECB_DEF = Define `ECB = MAP`;

val ECB_Correct = Q.prove
(`!l cipher key encrypt decrypt.
     (cipher key = (encrypt,decrypt)) /\
     (decrypt o encrypt = I)
    ==>
     (ECB decrypt (ECB encrypt l) = l)`,
 Induct THEN
   RW_TAC list_ss [ECB_DEF,combinTheory.o_DEF,FUN_EQ_THM,MAP_MAP_COMPOSE] THEN
   METIS_TAC [combinTheory.I_DEF,MAP_I_THM]);;

(*---------------------------------------------------------------------------*)
(* Cipher Block Chaining.                                                    *)
(*---------------------------------------------------------------------------*)

val CBC_ENC_DEF =
 Define
  `(CBC_ENC (f:'a->'a->'a) (enc:'a->'a) v [] = []) /\
   (CBC_ENC f enc v (h::t) =
       let x = enc (f h v)
       in x::CBC_ENC f enc x t)`;

val CBC_DEC_DEF =
 Define
  `(CBC_DEC (f:'a->'a->'a) (dec:'a->'a) v [] = []) /\
   (CBC_DEC f dec v (h::t) = f (dec h) v :: CBC_DEC f dec h t)`;

(*
val CBC_DEF =
 Define
   `CBC j (e,d) k = (CBC_ENC j (e k), CBC_DEC j (d k))`;
*)

(*---------------------------------------------------------------------------*)
(* Provided decryption inverts encryption and f is idempotent, the CBC       *)
(* mode of operation is correct.                                             *)
(*---------------------------------------------------------------------------*)

val CBC_CORRECT = Q.store_thm
("CBC_CORRECT",
 `!(l:'a list) v (encrypt:'k->'a->'a) (decrypt:'k->'a->'a) f.
     (!k. decrypt k o encrypt k = I) /\
     (!x y. f (f x y) y = x)
     ==>
     !k. CBC_DEC f (decrypt k) v
        (CBC_ENC f (encrypt k) v l) = l`,
 SIMP_TAC list_ss [o_DEF,FUN_EQ_THM]
  THEN Induct
  THEN RW_TAC std_ss [CBC_ENC_DEF,CBC_DEC_DEF,LET_THM]
  THEN METIS_TAC []);


(*---------------------------------------------------------------------------*)
(* Encryption/decryption can be lifted to arbitrary encodable types.         *)
(*---------------------------------------------------------------------------*)

val DATA_CBC_CORRECT = Q.store_thm
("DATA_CBC_CORRECT",
 `!encode decode block unblock encrypt decrypt f.
    (decode o encode = I)   /\
    (!k. decrypt k o encrypt k = I) /\
    (unblock o block = I)   /\
    (!x y. f (f x y) y = x)
   ==>
    !(x:'a) v key.
      (decode o unblock o CBC_DEC f (decrypt key) v) o
      (CBC_ENC f (encrypt key) v o block o encode) = I`,
 RW_TAC list_ss [CBC_CORRECT,o_DEF,FUN_EQ_THM]);


val _ = export_theory();


