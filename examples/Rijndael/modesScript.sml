(*---------------------------------------------------------------------------*)
(* Modes of operation (ECB, CBC, CFB, CFB, CTR) and padding                  *)
(*---------------------------------------------------------------------------*)

(* Interactive:
   app load ["aesTheory", "metisLib"];
   val _ = quietdec := true;
   open aesTheory RoundOpTheory pairTools metisLib 
        listTheory arithmeticTheory combinTheory;
   val _ = quietdec := false;
*)
open HolKernel Parse boolLib numLib bossLib aesTheory RoundOpTheory 
     pairTools metisLib listTheory arithmeticTheory combinTheory;

val _ = new_theory "modes"


val _ = Defn.def_suffix := "_DEF";
val _ = Globals.priming := SOME "";  (* rename variables with number suffixes *)

(*---------------------------------------------------------------------------*)
(* Make list append into an infix recognized by the parser                   *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);

(*---------------------------------------------------------------------------*)
(* Electronic Code Book. We define it parameterized by an encoding function, *)
(* which can also be a decoding function.                                    *)
(*---------------------------------------------------------------------------*)

val ECB_DEF = TotalDefn.DefineSchema
   `(ECB [] = []) /\
    (ECB (h::t) = enc h::ECB t)`;

val ECB_Correct = Q.prove
(`!l key. ((encoder,decoder) = AES key) 
           ==> 
          (ECB decoder (ECB encoder l) = l)`,
 Induct THEN PROVE_TAC [AES_Correct,ECB_DEF]);

(*---------------------------------------------------------------------------*)
(* Cipher Block Chaining.                                                    *)
(*---------------------------------------------------------------------------*)

val (CBC_ENC_DEF,_) = Defn.tprove (Defn.Hol_defn 
    "CBC_ENC"
   `(CBC_ENC __ [] : state list = []) /\
    (CBC_ENC v (h::t) = let x = enc (XOR_BLOCK h v) in x::CBC_ENC x t)`,
 WF_REL_TAC `measure (LENGTH o SND)` THEN RW_TAC list_ss []);

val (CBC_DEC_DEF,_) = Defn.tprove (Defn.Hol_defn 
    "CBC_DEC"
   `(CBC_DEC __ [] : state list = []) /\
    (CBC_DEC v (h::t) = XOR_BLOCK (dec h) v :: CBC_DEC h t)`,
 WF_REL_TAC `measure (LENGTH o SND)` THEN RW_TAC list_ss []);

val _ = save_thm("CBC_ENC_DEF",CBC_ENC_DEF);
val _ = save_thm("CBC_DEC_DEF",CBC_DEC_DEF);
val _ = computeLib.add_persistent_funs [("CBC_ENC_DEF",CBC_ENC_DEF),
                                        ("CBC_DEC_DEF",CBC_DEC_DEF)];
val CBC_Correct = Q.store_thm
("CBC_Correct",
 `!l key v. ((encrypt,decrypt) = AES key) 
               ==> 
            (CBC_DEC decrypt v (CBC_ENC encrypt v l) = l)`,
 Induct THEN RW_TAC std_ss [CBC_ENC_DEF,CBC_DEC_DEF] THENL
 [PROVE_TAC [AES_Correct,XOR_BLOCK_IDEM],
  PROVE_TAC []]);


(*---------------------------------------------------------------------------*)
(* CFB, OFB, CTR still to come                                               *)
(*---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*)
(* Padding                                                                   *)
(*---------------------------------------------------------------------------*)

val BYTE_TO_LIST_DEF = Define
   `BYTE_TO_LIST (b7,b6,b5,b4,b3,b2,b1,b0) = [b7;b6;b5;b4;b3;b2;b1;b0]`;

val LENGTH_BYTE_TO_LIST = Q.store_thm
("LENGTH_BYTE_TO_LIST",
 `!b. LENGTH (BYTE_TO_LIST b) = 8`,
 METIS_TAC [EVAL (Term`LENGTH[b7;b6;b5;b4;b3;b2;b1;b0]`),
            BYTE_TO_LIST_DEF,pairTheory.ABS_PAIR_THM]);

(*---------------------------------------------------------------------------*)
(* Put n copies of x into a list                                             *)
(*---------------------------------------------------------------------------*)

val REPLICATE_DEF = Define
   `REPLICATE n x = if n = 0 then [] else x::REPLICATE (n-1) x`;

val LENGTH_REPLICATE = Q.store_thm
("LENGTH_REPLICATE",
 `!n x. LENGTH(REPLICATE n x) = n`,
 Induct THENL
 [EVAL_TAC THEN PROVE_TAC [],
  ONCE_REWRITE_TAC [REPLICATE_DEF] THEN RW_TAC list_ss []]);

(*---------------------------------------------------------------------------*)
(* Define a padding function and its inverse                                 *)
(*---------------------------------------------------------------------------*)

val PADDING_DEF = Define
   `PADDING l = let slop = (LENGTH l) MOD 128 in
            let to_drop = (if slop <= 120 then 128 else 256) - slop in
            let stuffing = to_drop - 8
            in
             REPLICATE stuffing F <> BYTE_TO_LIST (NUM_TO_BYTE to_drop)`;

val PAD_DEF = Define `PAD l = l <> PADDING l`;

(*---------------------------------------------------------------------------*)
(* Extract the length of the over-run from the last 8 bits of a padded list  *)
(*---------------------------------------------------------------------------*)

val PADLEN_DEF = Define
   `(PADLEN [b7;b6;b5;b4;b3;b2;b1;b0] = BYTE_TO_NUM (b7,b6,b5,b4,b3,b2,b1,b0))
/\  (PADLEN (b8::b7::b6::b5::b4::b3::b2::b1::b0::t) 
      = PADLEN (b7::b6::b5::b4::b3::b2::b1::b0::t))`;

(*---------------------------------------------------------------------------*)
(* The first n elements of a list                                            *)
(*---------------------------------------------------------------------------*)

val (FRONT_DEF,_) = Defn.tprove (Hol_defn "FRONT"
    `FRONT n l = if n = 0 then [] else HD(l)::FRONT (n-1) (TL l)`,
  WF_REL_TAC `measure FST`);

val _ = save_thm ("FRONT_DEF",FRONT_DEF);
val _ = computeLib.add_persistent_funs [("FRONT_DEF",FRONT_DEF)];

(*---------------------------------------------------------------------------*)
(* Inverse of padding function.                                              *)
(*---------------------------------------------------------------------------*)

val UNPAD_DEF = Define `UNPAD l = FRONT (LENGTH l - PADLEN l) l`;

(*---------------------------------------------------------------------------*)
(* Facts about padding                                                       *)
(*---------------------------------------------------------------------------*)

val LENGTH_PADDING_EQUALS_PADLEN = Q.store_thm
("LENGTH_PADDING_EQUALS_PADLEN",
 `!l. LENGTH (PADDING l) = PADLEN (PADDING l)`,
 REWRITE_TAC [PADDING_DEF] 
  THEN RW_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE] THENL
  [POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`LENGTH l MOD 128`, `x`) 
     THEN GEN_TAC THEN STRIP_TAC
     THEN `x < 121` by DECIDE_TAC
     THEN Q.PAT_ASSUM `x <= y` (K ALL_TAC)
     THEN POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `x`
     THEN NTAC 121 (CONV_TAC (BOUNDED_CONV EVAL))
     THEN PROVE_TAC [],
   `120 < LENGTH l MOD 128 /\ LENGTH l MOD 128 < 128` 
       by RW_TAC arith_ss [arithmeticTheory.DIVISION]
     THEN REPEAT (POP_ASSUM MP_TAC) 
     THEN Q.SPEC_TAC (`LENGTH l MOD 128`, `x`) 
     THEN GEN_TAC THEN REPEAT STRIP_TAC 
     THEN `(x = 121) \/ (x = 122) \/ (x = 123) \/ 
           (x = 124) \/ (x = 125) \/ (x = 126) \/ (x = 127)` 
          by RW_TAC arith_ss []
     THEN RW_TAC std_ss []
     THEN EVAL_TAC]);

val LENGTH8 = Q.prove
(`!l. (LENGTH l = 8) ==> 
      ?h0 h1 h2 h3 h4 h5 h6 h7. l = [h7; h6; h5; h4; h3; h2; h1; h0]`,
 Cases THENL [EVAL_TAC, ALL_TAC] THEN 
 NTAC 4 (Cases_on `t` THENL 
         [EVAL_TAC, Cases_on `t1` THENL [EVAL_TAC, ALL_TAC]]) THENL
 [PROVE_TAC [],RW_TAC list_ss []]);

val PADDING_APPEND_LEMMA = Q.prove
(`!l. ?l1 h0 h1 h2 h3 h4 h5 h6 h7. 
        PADDING l = l1 <> [h7;h6;h5;h4;h3;h2;h1;h0]`,
 RW_TAC std_ss [PADDING_DEF] 
  THENL [Q.EXISTS_TAC `(REPLICATE (128 - LENGTH l MOD 128 - 8) F)`,
         Q.EXISTS_TAC `(REPLICATE (256 - LENGTH l MOD 128 - 8) F)`]
  THEN RW_TAC std_ss [APPEND_11]
  THEN PROVE_TAC [LENGTH_BYTE_TO_LIST,LENGTH8]);

val lem = Q.prove
(`!l. ?l1 b0 b1 b2 b3 b4 b5 b6 b7 t. 
       l <> [h7; h6; h5; h4; h3; h2; h1; h0] = 
       b0::b1::b2::b3::b4::b5::b6::b7::t`,
 Induct THEN EVAL_TAC THEN PROVE_TAC []);

val PADLEN_EQUALS_BYTE_TO_NUM = Q.prove
(`!l. PADLEN (l <> [h7;h6;h5;h4;h3;h2;h1;h0]) = 
      BYTE_TO_NUM (h7,h6,h5,h4,h3,h2,h1,h0)`,
 Induct THENL
 [EVAL_TAC, RW_TAC list_ss [] THEN METIS_TAC [lem,PADLEN_DEF]]);

val PADLEN_APPEND = Q.store_thm
("PADLEN_APPEND",
 `!l. PADLEN (PAD l) = PADLEN (PADDING l)`,
 METIS_TAC [PAD_DEF,APPEND_ASSOC,PADLEN_EQUALS_BYTE_TO_NUM,
            PADDING_APPEND_LEMMA]);

val FRONT_LENGTH = Q.store_thm
("FRONT_LENGTH",
 `!l. FRONT (LENGTH l) l = l`,
 Induct THENL 
 [EVAL_TAC,
  ONCE_REWRITE_TAC [FRONT_DEF] THEN RW_TAC list_ss []]);

val FRONT_LENGTH_APPEND = Q.store_thm
("FRONT_LENGTH_APPEND",
 `!l l1. FRONT (LENGTH l) (l <> l1) = l`,
 Induct THENL
 [GEN_TAC THEN EVAL_TAC,
  ONCE_REWRITE_TAC [FRONT_DEF]
    THEN RW_TAC list_ss []]);

val lemma = Q.prove
(`!n l. (n = LENGTH l) ==> (FRONT n l = l)`,
 PROVE_TAC [FRONT_LENGTH]);

val lemma1 = Q.prove
(`!n l l1 l2. (n = LENGTH l1) /\ (l = l1 <> l2) ==> (FRONT n l = l1)`,
 PROVE_TAC [FRONT_LENGTH_APPEND]);

(*---------------------------------------------------------------------------*)
(* Correctness of padding then unpadding                                     *)
(*---------------------------------------------------------------------------*)

val UNPAD_PAD_THM = Q.store_thm
("UNPAD_PAD_THM",
 `!l. UNPAD (PAD l) = l`,
 RW_TAC std_ss [UNPAD_DEF,PAD_DEF] 
   THEN MATCH_MP_TAC lemma1
   THEN Q.EXISTS_TAC `PADDING l` THEN RW_TAC list_ss []
   THEN MATCH_MP_TAC (DECIDE (Term `(x = y) ==> (p + x - y = p)`))
   THEN PROVE_TAC [PADLEN_APPEND,LENGTH_PADDING_EQUALS_PADLEN,PAD_DEF]);

(*---------------------------------------------------------------------------*)
(* Padding always yields a multiple of 128                                   *)
(*---------------------------------------------------------------------------*)

val PADDED_LENGTH_THM = Q.store_thm
("PADDED_LENGTH_THM",
 `!l. LENGTH (PAD l) MOD 128 = 0`,
 RW_TAC std_ss [PAD_DEF,PADDING_DEF, listTheory.LENGTH_APPEND,
                LENGTH_REPLICATE, LENGTH_BYTE_TO_LIST]
  THEN ONCE_REWRITE_TAC [EVAL_RULE (Q.SPEC `128` (GSYM MOD_PLUS))] THENL
  [POP_ASSUM MP_TAC 
     THEN Q.SPEC_TAC (`LENGTH l MOD 128`, `x`) 
     THEN RW_TAC std_ss [] 
     THEN `(x = 0) \/ 0 < x` by DECIDE_TAC THEN RW_TAC arith_ss [LESS_MOD],
   `120 < LENGTH l MOD 128 /\ LENGTH l MOD 128 < 128` 
         by RW_TAC arith_ss [arithmeticTheory.DIVISION]
      THEN REPEAT (POP_ASSUM MP_TAC)
      THEN Q.SPEC_TAC (`LENGTH l MOD 128`, `x`) 
      THEN GEN_TAC THEN REPEAT STRIP_TAC 
      THEN `(x = 121) \/ (x = 122) \/ (x = 123) \/ 
            (x = 124) \/ (x = 125) \/ (x = 126) \/ (x = 127)` 
          by RW_TAC arith_ss []
      THEN RW_TAC arith_ss []]);


(*---------------------------------------------------------------------------*)
(* Trivial maps between a lists of bits and a 16-tuple of bytes              *)
(*---------------------------------------------------------------------------*)

val BYTE_DEF = Define 
  `(BYTE [] = []) /\
   (BYTE (a::b::c::d::e::f::g::h::t) = (a,b,c,d,e,f,g,h)::BYTE t)`;

val BLOCK_DEF = Define
 `(BLOCK [] = []) /\
  (BLOCK (a::b::c::d::e::f::g::h::i::j::k::l::m::n::p::q::t) 
       = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q)::BLOCK t)`;

val UNBYTE_DEF = Define 
   `(UNBYTE [] = []) /\
    (UNBYTE ((a,b,c,d,e,f,g,h)::t) = a::b::c::d::e::f::g::h::UNBYTE t)`;

val UNBLOCK_DEF = Define
 `(UNBLOCK [] = []) /\
  (UNBLOCK ((a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q)::t) = 
    a::b::c::d::e::f::g::h::i::j::k::l::m::n::p::q::UNBLOCK t)`;

(*---------------------------------------------------------------------------*)
(* Superfluous definitions, used for readability                             *)
(*---------------------------------------------------------------------------*)

val ENBLOCK_DEF = Define `ENBLOCK = BLOCK o BYTE`;
val DEBLOCK_DEF = Define `DEBLOCK = UNBYTE o UNBLOCK`;

val BYTE_THEN_UNBYTE = Q.store_thm
("BYTE_THEN_UNBYTE",
 `!l. (LENGTH l MOD 8 = 0) ==> (UNBYTE (BYTE l) = l)`,
 recInduct(fetch "-" "BYTE_ind") THEN EVAL_TAC
   THEN FULL_SIMP_TAC list_ss [ADD1,ADD_MODULUS]);

val BLOCK_THEN_UNBLOCK = Q.store_thm
("BLOCK_THEN_UNBLOCK",
 `!l k. (LENGTH (l) MOD 16 = 0) ==> (UNBLOCK (BLOCK l) = l)`,
 recInduct(fetch "-" "BLOCK_ind") THEN EVAL_TAC
   THEN FULL_SIMP_TAC list_ss [ADD1,ADD_MODULUS]);

(*---------------------------------------------------------------------------*)
(* Next proof requires 128 cases in the induction, so we get such an ind.    *)
(* thm by making an otherwise unused recursive definition with the right     *)
(* shape. Takes some time to process.                                        *)
(*---------------------------------------------------------------------------*)

val _ = Define
 `(foo(v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::v12::v13::v14::v15::v16::
       v17::v18::v19::v20::v21::v22::v23::v24::v25::v26::v27::v28::v29::v30::
       v31::v32::v33::v34::v35::v36::v37::v38::v39::v40::v41::v42::v43::v44::
       v45::v46::v47::v48::v49::v50::v51::v52::v53::v54::v55::v56::v57::v58::
       v59::v60::v61::v62::v63::v64::v65::v66::v67::v68::v69::v70::v71::v72::
       v73::v74::v75::v76::v77::v78::v79::v80::v81::v82::v83::v84::v85::v86::
       v87::v88::v89::v90::v91::v92::v93::v94::v95::v96::v97::v98::v99::v100::
       v101::v102::v103::v104::v105::v106::v107::v108::v109::v110::v111::v112::
       v113::v114::v115::v116::v117::v118::v119::v120::v121::v122::v123::v124::
       v125::v126::v127::v128::t) = foo t) /\
  (foo otherwise = T)`;

val listind128 = fetch "-" "foo_ind";

val LENGTH_BYTE_THM = Q.store_thm
("LENGTH_BYTE_THM",
 `!l. (LENGTH l MOD 128 = 0) ==> (LENGTH (BYTE l) MOD 16 = 0)`,
 HO_MATCH_MP_TAC listind128 
   THEN REPEAT (CONJ_TAC ORELSE GEN_TAC)
   THEN EVAL_TAC   (* Gets all cases except induction step *)
   THEN SIMP_TAC std_ss [ADD1] THEN RW_TAC arith_ss [ADD_MODULUS]);

val MOD_FACTOR = Q.prove
(`!n. (n MOD 128 = 0) ==> (n MOD 8 = 0)`,
  RW_TAC arith_ss [BETA_RULE (Q.ISPECL [`\x.x=0`] MOD_P)]
   THEN Q.EXISTS_TAC `16 * k` THEN DECIDE_TAC);

val ENBLOCK_THEN_DEBLOCK = Q.store_thm
("ENBLOCK_THEN_DEBLOCK",
 `!l. (LENGTH l MOD 128 = 0) ==> (DEBLOCK (ENBLOCK l) = l)`,
 METIS_TAC [DEBLOCK_DEF, ENBLOCK_DEF, LENGTH_BYTE_THM,o_THM,
            BYTE_THEN_UNBYTE,BLOCK_THEN_UNBLOCK,MOD_FACTOR]);

val PAD_TO_UNPAD_THM = Q.store_thm
("PAD_TO_UNPAD_THM",
 `!l. UNPAD (DEBLOCK(ENBLOCK(PAD l))) = l`,
 METIS_TAC [ENBLOCK_THEN_DEBLOCK,PADDED_LENGTH_THM,UNPAD_PAD_THM]);


(*---------------------------------------------------------------------------*)
(* Definition of CBC mode using AES, along with maps into and out of bool    *)
(* lists. Encode the data, pad it, block it, then encrypt it with AES.       *)
(* And the reverse.                                                          *)
(*---------------------------------------------------------------------------*)

val AES_CBC_DEF = Define
   `AES_CBC (encoder:'a -> bool list) 
            (decoder:bool list -> 'a) key init = 
    let (encrypt,decrypt) = AES key
    in 
     (CBC_ENC encrypt init o ENBLOCK o PAD o encoder,
      decoder o UNPAD o DEBLOCK o CBC_DEC decrypt init)`;

(*---------------------------------------------------------------------------*)
(* Encryption/decryption can be lifted to arbitrary types.                   *)
(*---------------------------------------------------------------------------*)

val AES_CBC_CORRECT = Q.store_thm
("AES_CBC_CORRECT",
 `!encode decode key iv E D.
    (decode o encode = I) /\  
    ((E,D) = AES_CBC encode decode key iv)
       ==> 
    (D o E = I)`,
 REWRITE_TAC [AES_CBC_DEF] 
  THEN REPEAT GEN_TAC
  THEN Cases_on `AES key`
  THEN RW_TAC std_ss [FUN_EQ_THM]
  THEN METIS_TAC [CBC_Correct, PAD_TO_UNPAD_THM]);

val _ = export_theory();
