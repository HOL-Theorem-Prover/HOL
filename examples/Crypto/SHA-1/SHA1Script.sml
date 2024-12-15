(*===========================================================================*)
(* Secure Hash Algorithm                                                     *)
(*                                                                           *)
(* HOL version of an ML implementation by Hiro Kuwahara                      *)
(*                                                                           *)
(*===========================================================================*)

(* interactive use
app load ["wordsLib", "stringLib", "numLib"];
*)

open HolKernel Parse boolLib bossLib
     stringTheory listTheory arithmeticTheory wordsLib wordsTheory;

val _ = new_theory "SHA1";

val _ = numLib.temp_prefer_num();

(*---------------------------------------------------------------------------*)
(* Some support stuff on lists, in particular a definition of TAKE.          *)
(*---------------------------------------------------------------------------*)

val (TAKE_def,TAKE_ind) = Defn.tprove(Hol_defn
     "TAKE"
     `TAKE n L acc =
        if n = 0 then SOME (REV acc [], L) else
        if NULL L then NONE
        else TAKE (n-1) (TL L) (HD L::acc)`,
 WF_REL_TAC `measure (LENGTH o FST o SND)`
  THEN Cases THEN RW_TAC list_ss []);

val _ = save_thm("TAKE_def",TAKE_def);

val TAKE_LEM = Q.prove
(`!n L L1 taken left.
      (SOME(taken,left) = TAKE n L L1) ==> (n=0) \/ LENGTH left < LENGTH L`,
 recInduct TAKE_ind THEN REPEAT GEN_TAC THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [TAKE_def]
   THEN RW_TAC list_ss []
   THEN FULL_SIMP_TAC list_ss [] THEN RES_TAC THENL
   [`n=1` by DECIDE_TAC THEN RW_TAC list_ss []
      THEN FULL_SIMP_TAC list_ss [Once TAKE_def]
      THEN Cases_on `L` THEN FULL_SIMP_TAC list_ss [],
      Cases_on `L` THEN FULL_SIMP_TAC list_ss []]);

(*---------------------------------------------------------------------------*)
(* Misc. support for 8 and 32 bit words.                                     *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* 64 copies of ZERO                                                         *)
(*---------------------------------------------------------------------------*)

val ZEROx64_def = Define
   `ZEROx64 = [0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w;
               0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w] : word32 list`;

(*---------------------------------------------------------------------------*)
(*    word32 <--> (word8 # word8 # word8 # word8)                            *)
(*---------------------------------------------------------------------------*)

val _ = wordsLib.guess_lengths();

val w8x4to32_def = Define`
  w8x4to32 (w1:word8) (w2:word8) (w3:word8) (w4:word8) = w1 @@ w2 @@ w3 @@ w4`;

val w32to8x4_def = Define`
  w32to8x4 (w:word32) = ((31 >< 24) w, (23 >< 16) w, (15 >< 8) w, (7 >< 0) w)`;

val w32List_def = Define`
  (w32List (b1::b2::b3::b4::t) = w8x4to32 b1 b2 b3 b4::w32List t) /\
  (w32List other = [])`;

val w8List_def = Define`
  (w8List [] = []) /\
  (w8List (h::t) = let (b1,b2,b3,b4) = w32to8x4 h in b1::b2::b3::b4::w8List t)`;

(*---------------------------------------------------------------------------*)
(* Translate 5 32 bit words to a 20-tuple of 8-bit words.                    *)
(*---------------------------------------------------------------------------*)

val w32x5to8_def =
 Define
   `w32x5to8 (w1,w2,w3,w4,w5) =
      let (w1b1,w1b2,w1b3,w1b4) = w32to8x4 w1 in
      let (w2b1,w2b2,w2b3,w2b4) = w32to8x4 w2 in
      let (w3b1,w3b2,w3b3,w3b4) = w32to8x4 w3 in
      let (w4b1,w4b2,w4b3,w4b4) = w32to8x4 w4 in
      let (w5b1,w5b2,w5b3,w5b4) = w32to8x4 w5
       in
        (w1b1,w1b2,w1b3,w1b4,w2b1,w2b2,w2b3,w2b4,
         w3b1,w3b2,w3b3,w3b4,w4b1,w4b2,w4b3,w4b4,w5b1,w5b2,w5b3,w5b4)`;

(*---------------------------------------------------------------------------*)
(*             Padding                                                       *)
(*---------------------------------------------------------------------------*)

val div64 = CONV_RULE EVAL (Q.SPEC `64n` arithmeticTheory.DIVISION);
val ndiv64 = Q.SPEC `n` div64;
val n1div64 = Q.SPEC `n+1` div64;

val swap_lem =
  DECIDE (Term `!a b c d : num. a < b /\ c < d ==> (b-a < d-c <=> b+c < d+a)`);

(*---------------------------------------------------------------------------*)
(* Gross termination proof. Would be better in the integers.                 *)
(*---------------------------------------------------------------------------*)

val (pBits_def, pBits_ind) =
 Defn.tprove
(Hol_defn
  "pBits"
  `pBits n : word8 list =
       if n MOD 64 = 56 then []
       else 0w::pBits (n+1)`,
 WF_REL_TAC
    `measure \n. if n MOD 64 <= 56 then 56 - n MOD 64 else 120 - n MOD 64`
   THEN RW_TAC std_ss [] THEN FULL_SIMP_TAC arith_ss [] THENL
   [`n MOD 64 < 56` by DECIDE_TAC
      THEN WEAKEN_TAC (aconv (Term `n MOD 64 <= 56`))
      THEN WEAKEN_TAC (aconv (Term `~(n MOD 64 = 56)`))
      THEN FULL_SIMP_TAC std_ss [LESS_OR_EQ] THENL
      [RW_TAC arith_ss [swap_lem]
        THEN Induct_on `n DIV 64` THEN RW_TAC std_ss [] THENL
        [MP_TAC ndiv64
           THEN Q.PAT_ASSUM `x = y` (SUBST_ALL_TAC o SYM)
           THEN RW_TAC arith_ss []
           THEN `(n=63) \/ n<63` by DECIDE_TAC THEN FULL_SIMP_TAC arith_ss [],
         Q.PAT_ASSUM `$!M` (MP_TAC o Q.SPEC `v * 64n + n MOD 64`)
           THEN RW_TAC arith_ss []
           THEN FULL_SIMP_TAC arith_ss [ADD_DIV_ADD_DIV]
           THEN `n MOD 64 DIV 64 = 0` by RW_TAC arith_ss [LESS_DIV_EQ_ZERO]
           THEN FULL_SIMP_TAC std_ss []
           THEN `(v * 64 + n MOD 64) MOD 64 = n MOD 64`
                by RW_TAC arith_ss [MOD_MULT]
           THEN FULL_SIMP_TAC arith_ss []
           THEN `(v * 64 + (n MOD 64 + 1)) MOD 64 = n MOD 64 + 1`
                by RW_TAC arith_ss [MOD_MULT]
           THEN `n MOD 64 + 1 = (n+1) MOD 64`
                by RW_TAC arith_ss [Once (GSYM MOD_PLUS)]
           THEN FULL_SIMP_TAC arith_ss []],
       DECIDE_TAC],
    ASSUME_TAC (CONJUNCT2 ndiv64) THEN DECIDE_TAC,
    ASSUME_TAC (CONJUNCT2 ndiv64) THEN DECIDE_TAC,
    FULL_SIMP_TAC arith_ss [Once (GSYM MOD_PLUS)],
    FULL_SIMP_TAC arith_ss [Once (GSYM MOD_PLUS)]
      THEN `56 < n MOD 64 /\ n MOD 64 < 64` by RW_TAC arith_ss [ndiv64]
      THEN Q.PAT_ASSUM `~(a = b)` (K ALL_TAC)
      THEN `(n MOD 64 = 57) \/ (n MOD 64 = 58) \/ (n MOD 64 = 59) \/
            (n MOD 64 = 60) \/ (n MOD 64 = 61) \/ (n MOD 64 = 62) \/
            (n MOD 64 = 63)` by DECIDE_TAC
      THEN FULL_SIMP_TAC arith_ss [],
    ASSUME_TAC (CONJUNCT2 ndiv64) THEN DECIDE_TAC]);

val _ = save_thm("pBits_def",pBits_def);

val PaddingBits =
 Define
   `PaddingBits len = 128w :: pBits (len+1n)`;

val lBits_def =
 Define
   `lBits(len,i) =
     if i = 0 then []
     else (7 >< 0) (n2w len : word32 >> ((i-1)*8)) :: lBits(len,i-1)`;

val LengthBits_def =
 Define
   `LengthBits len = lBits(len * 8n, 8)`;

(*---------------------------------------------------------------------------*)
(* Trickery needed to save stack. Note that input is the whole message to    *)
(* be digested, so it can be quite long compared to padding. So we append    *)
(* the (reversed) padding to the reversed input, then reverse the result.    *)
(* Non-obfuscated:                                                           *)
(*                                                                           *)
(*   Pad input =                                                             *)
(*      let len = LENGTH input                                               *)
(*      in input ++ PaddingBits(len) ++ LengthBits(len)                      *)
(*---------------------------------------------------------------------------*)

val Pad_def =
 Define
   `Pad input =
      let len = LEN input 0 in
      let padding = PaddingBits(len) ++ LengthBits(len)
      in REV (REV padding [] ++ REV input []) []`;

(*---------------------------------------------------------------------------*)
(* There are 4 highly similar rounds of computation, each consisting of 20   *)
(* highly similar steps. Higher order functions to the rescue!               *)
(*---------------------------------------------------------------------------*)

val C1_def = Define `C1 = 1518500249w:word32`;
val C2_def = Define `C2 = 1859775393w:word32`;
val C3_def = Define `C3 = 2400959708w:word32`;
val C4_def = Define `C4 = 3395469782w:word32`;

val f1_def = Define `f1(a,b,c) = (c ?? (a && (b ?? c))) + C1 : word32`;
val f2_def = Define `f2(a,b,c) = (a ?? b ?? c) + C2 : word32`;
val f3_def = Define `f3(a,b,c) = ((a && b) || (c && (a || b))) + C3 : word32`;
val f4_def = Define `f4(a,b,c) = (a ?? b ?? c) + C4 : word32`;


val Helper_def =
 Define
   `Helper (f:word32#word32#word32->word32) n (a,b,c,d,e) w =
      if n = 0 then (a,(b #<< 30n),c,d,e+(a #<< 5n)+f(b,c,d)+w) else
      if n = 1 then ((a #<< 30n),b,c,d+(e #<< 5n)+f(a,b,c)+w,e) else
      if n = 2 then (a,b,c+(d #<< 5n)+f(e,a,b)+w,d,e #<< 30n)   else
      if n = 3 then (a,b+(c #<< 5n)+f(d,e,a)+w,c,d #<< 30n,e)
               else (a+(b #<< 5n)+f(c,d,e)+w,b,c #<< 30n,d,e)`;

val Round_def =
 Define
  `(Round _ _ args [] = (args,[])) /\
   (Round helper i args (w::t) =
      if i<20 then Round helper (i+1) (helper (i MOD 5) args w) t
              else (args, w::t))`;

val (expand_def, expand_ind) = Defn.tprove
 (Hol_defn "expand"
  `(expand (w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::
            w10::w11::w12::w13::w14::w15::w16::t) =
      let j = (w0 ?? w2 ?? w8 ?? w13) : word32 #<< 1n
       in w0::expand(w1::w2::w3::w4::w5::w6::w7::w8::
                     w9::w10::w11::w12::w13::w14::w15::j::t)) /\
   (expand wlist = wlist)`,
   WF_REL_TAC `measure LENGTH` THEN RW_TAC list_ss []);

val _ = save_thm("expand_def",expand_def);

val _ = computeLib.add_persistent_funs ["expand_def"];

(*---------------------------------------------------------------------------*)
(* Digest a block                                                            *)
(*---------------------------------------------------------------------------*)

val digestBlock_def =
 Define
   `digestBlock (block:word8 list) (h0,h1,h2,h3,h4) =
      let wlist = expand (w32List block ++ ZEROx64) in
      let (hbar1,wlist1) = Round (Helper f1) 0 (h0,h1,h2,h3,h4) wlist in
      let (hbar2,wlist2) = Round (Helper f2) 0 hbar1 wlist1 in
      let (hbar3,wlist3) = Round (Helper f3) 0 hbar2 wlist2 in
      let (hbar4,wlist4) = Round (Helper f4) 0 hbar3 wlist3 in
      let (a,b,c,d,e) = hbar4
       in
         (h0+a, h1+b, h2+c, h3+d, h4+e)`;

(*---------------------------------------------------------------------------*)
(* Digest a whole message, one block at a time.                              *)
(*---------------------------------------------------------------------------*)

val (digest_def,digest_ind) = Defn.tprove
(Hol_defn
  "digest"
  `digest message Hbar =
    case TAKE 64 message []
     of NONE => Hbar
      | SOME(next,rest) => digest rest (digestBlock next Hbar)`,
 WF_REL_TAC `measure (LENGTH o FST)`
  THEN REPEAT PairRules.PGEN_TAC
  THEN RW_TAC list_ss []
  THEN IMP_RES_TAC (GSYM TAKE_LEM)
  THEN DECIDE_TAC);

val _ = save_thm("digest_def",digest_def);


(*---------------------------------------------------------------------------*)
(* Compute the message digest                                                *)
(*---------------------------------------------------------------------------*)

val H0_def = Define `H0 = 1732584193w:word32`;
val H1_def = Define `H1 = 4023233417w:word32`;
val H2_def = Define `H2 = 2562383102w:word32`;
val H3_def = Define `H3 = 271733878w:word32`;
val H4_def = Define `H4 = 3285377520w:word32`;

val computeMD_def =
 Define
   `computeMD input = w32x5to8 (digest (Pad input) (H0,H1,H2,H3,H4))`;

(*---------------------------------------------------------------------------*)
(* Mapping strings to word8 lists.                                           *)
(*---------------------------------------------------------------------------*)

val string_to_w8_list_def = Define
   `string_to_w8_list s = MAP (n2w o ORD) (EXPLODE s) : word8 list`;

(*---------------------------------------------------------------------------*)
(* Mapping strings to lists of 8 bit bytes.                                  *)
(*---------------------------------------------------------------------------*)

val stringMD_def =
 Define
   `stringMD s = computeMD (string_to_w8_list s)`;

(*---------------------------------------------------------------------------*)
(* Generate stand-alone ML code                                              *)
(*---------------------------------------------------------------------------*)

val _ = computeLib.add_persistent_funs
         ["TAKE_def",
          "pBits_def",
          "digest_def"];

val _ = type_pp.pp_num_types := false;
val _ = type_pp.pp_array_types := false;

(*
val _ =
  let open emitLib
      val string_to_w8_list = REWRITE_RULE [METIS_PROVE [combinTheory.o_THM]
                                ``(n2w o ORD) = (\x. n2w (ORD x))``]
                                string_to_w8_list_def
  in emitML (!Globals.emitMLDir) ("sha1",
     MLSIG "type num = numML.num" ::
     MLSIG "type word8 = wordsML.word8" ::
     MLSIG "type word32 = wordsML.word32" ::
     OPEN ["num", "list", "option", "words"] ::
     MLSTRUCT "type word8 = wordsML.word8" ::
     MLSTRUCT "type word32 = wordsML.word32"
     ::
     map DEFN
     [ TAKE_def, ZEROx64_def,
       w8x4to32_def, w32to8x4_def, w32List_def, w8List_def,
       w32x5to8_def, pBits_def, PaddingBits,
       lBits_def, LengthBits_def, Pad_def,
       C1_def,C2_def,C3_def,C4_def,
       f1_def, f2_def, f3_def, f4_def,
       H0_def,H1_def,H2_def,H3_def,H4_def,
       Helper_def, Round_def, expand_def,
       digestBlock_def, digest_def,
       computeMD_def, string_to_w8_list, stringMD_def ])
  end;
*)

val _ = export_theory();
