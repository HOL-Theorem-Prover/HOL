(*===========================================================================*)
(* Defining Decoders to be inverse Encoders                                  *)
(*===========================================================================*)

(* Interactive mode
app load
["bossLib", "rich_listTheory", "EncodeTheory", "normalForms", "metisLib"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools
     arithmeticTheory listTheory rich_listTheory EncodeTheory
     metisLib optionTheory normalForms combinTheory;

val _ = new_theory "Decode";

infixr 0 ++ || <<;
infix 1 >>;

val op ++ = op THEN;
val op >> = op THEN1;
val op << = op THENL;
val op || = op ORELSE;

val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;

val REVERSE = Tactical.REVERSE;

(*---------------------------------------------------------------------------
     Well-formed decoders: the definition is carefully chosen to be the
     dual of well-formed encoders.
 ---------------------------------------------------------------------------*)

val wf_decoder_def = Define
  `wf_decoder p (d : bool list -> ('a # bool list) option) =
   !x.
     if p x then (?a. !b c. (d b = SOME (x, c)) = (b = APPEND a c))
     else !a b. ~(d a = SOME (x, b))`;

(*---------------------------------------------------------------------------
     Functions to transform well-formed encoders to well-formed decoders,
     and vice versa.
 ---------------------------------------------------------------------------*)

val enc2dec_def = Define
  `enc2dec p e (l : bool list) =
   if ?x t. p (x : 'a) /\ (l = APPEND (e x) t)
   then SOME (@(x, t). p x /\ (l = APPEND (e x) t))
   else NONE`;

val dec2enc_def = Define
  `dec2enc (d : bool list -> ('a # bool list) option) x =
   @l. d l = SOME (x, [])`;

(*---------------------------------------------------------------------------
     Proofs that the transformation functions are mutually inverse.
 ---------------------------------------------------------------------------*)

val enc2dec_none = store_thm
  ("enc2dec_none",
   ``!p e l. (enc2dec p e l = NONE) = (!x t. p x ==> ~(l = APPEND (e x) t))``,
   RW_TAC std_ss [enc2dec_def] ++
   PROVE_TAC []);

val enc2dec_some = store_thm
  ("enc2dec_some",
   ``!p e l x t.
       wf_encoder p e ==>
       ((enc2dec p e l = SOME (x, t)) = p x /\ (l = APPEND (e x) t))``,
   REVERSE (RW_TAC std_ss [enc2dec_def]) >> PROVE_TAC [] ++
   ONCE_REWRITE_TAC [GSYM (ONCE_DEPTH_CONV ETA_CONV ``@p. q p``)] ++
   SELECT_TAC ++
   RW_TAC std_ss [UNCURRY] ++
   Cases_on `p'` ++
   EQ_TAC >>
   (DISCH_THEN (fn th => POP_ASSUM MP_TAC THEN SUBST1_TAC th) ++
    SIMP_TAC std_ss [] ++
    DISCH_THEN MATCH_MP_TAC ++
    PROVE_TAC [FST, SND]) ++
   POP_ASSUM MP_TAC ++
   MATCH_MP_TAC
   (PROVE [] ``(z ==> x) /\ (y ==> z ==> t) ==> (x ==> y) ==> z ==> t``) ++
   CONJ_TAC >> PROVE_TAC [FST, SND] ++
   SIMP_TAC std_ss [] ++
   REPEAT (DISCH_THEN STRIP_ASSUME_TAC) ++
   Suff `q = x` >> PROVE_TAC [APPEND_11] ++
   FULL_SIMP_TAC std_ss [wf_encoder_def] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2, IS_PREFIX_REFL]);

val enc2dec_some_alt = store_thm
  ("enc2dec_some_alt",
   ``!p e l x.
       wf_encoder p e ==>
       ((enc2dec p e l = SOME x) =
        p (FST x) /\ (l = APPEND (e (FST x)) (SND x)))``,
   RW_TAC std_ss []
   ++ Cases_on `x`
   ++ RW_TAC std_ss [FST, SND]
   ++ HO_METIS_TAC [enc2dec_some]);

val wf_enc2dec = store_thm
  ("wf_enc2dec",
   ``!p e. wf_encoder p e ==> wf_decoder p (enc2dec p e)``,
   RW_TAC std_ss [wf_decoder_def, enc2dec_some] ++
   PROVE_TAC [APPEND_NIL]);

val dec2enc_some = store_thm
  ("dec2enc_some",
   ``!p d x l.
       wf_decoder p d ==>
       ((dec2enc d x = l) /\ p x = (d l = SOME (x, [])))``,
   RW_TAC std_ss [dec2enc_def] ++
   SELECT_TAC ++
   RW_TAC std_ss [] ++
   EQ_TAC >>
   (RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X ==> Y` MATCH_MP_TAC ++
    FULL_SIMP_TAC std_ss [wf_decoder_def] ++
    PROVE_TAC [APPEND_NIL]) ++
   POP_ASSUM MP_TAC ++
   MATCH_MP_TAC
   (PROVE [] ``(z ==> x) /\ (y ==> z ==> t) ==> (x ==> y) ==> z ==> t``) ++
   CONJ_TAC >> PROVE_TAC [] ++
   POP_ASSUM MP_TAC ++
   SIMP_TAC std_ss [wf_decoder_def] ++
   DISCH_THEN (MP_TAC o Q.SPEC `x`) ++
   REVERSE (Cases_on `p x`) >> PROVE_TAC [] ++
   ASM_REWRITE_TAC [] ++
   DISCH_THEN (CHOOSE_THEN MP_TAC) ++
   RW_TAC std_ss []);

val decode_dec2enc = store_thm
  ("decode_dec2enc",
   ``!p d x.
       wf_decoder p d /\ p x ==> (d (dec2enc d x) = SOME (x, []))``,
   PROVE_TAC [dec2enc_some]);

val decode_dec2enc_append = store_thm
  ("decode_dec2enc_append",
   ``!p d x t.
       wf_decoder p d /\ p x ==>
       (d (APPEND (dec2enc d x) t) = SOME (x, t))``,
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`p`, `d`, `x`] decode_dec2enc) ++
   RW_TAC std_ss [] ++
   FULL_SIMP_TAC std_ss [wf_decoder_def] ++
   Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`) ++
   RW_TAC std_ss [] ++
   RW_TAC std_ss [] ++
   RES_TAC ++
   RW_TAC std_ss [APPEND_NIL]);

val wf_dec2enc = store_thm
  ("wf_dec2enc",
   ``!p d. wf_decoder p d ==> wf_encoder p (dec2enc d)``,
   RW_TAC std_ss [wf_encoder_def] ++
   MP_TAC (Q.SPECL [`p`, `d`] wf_decoder_def) ++
   ASM_REWRITE_TAC [] ++
   DISCH_THEN (fn th => MP_TAC (Q.SPEC `x` th) THEN MP_TAC (Q.SPEC `y` th)) ++
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`p`, `d`, `x`] decode_dec2enc) ++
   MP_TAC (Q.SPECL [`p`, `d`, `y`] decode_dec2enc) ++
   RW_TAC std_ss [APPEND_NIL] ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM (CHOOSE_THEN MP_TAC o REWRITE_RULE [IS_PREFIX_APPEND]) ++
   RW_TAC std_ss [GSYM APPEND_ASSOC] ++
   POP_ASSUM (MP_TAC o Q.SPECL [`APPEND (dec2enc d y) l`, `[]`]) ++
   POP_ASSUM (MP_TAC o Q.SPECL [`APPEND (dec2enc d y) l`, `l`]) ++
   RW_TAC std_ss [APPEND_NIL]);

val dec2enc_enc2dec = store_thm
  ("dec2enc_enc2dec",
   ``!p e x. wf_encoder p e /\ p x ==> (dec2enc (enc2dec p e) x = e x)``,
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`p`, `e`] wf_enc2dec) ++
   RW_TAC std_ss [dec2enc_some] ++
   MP_TAC (Q.SPECL [`p`, `enc2dec p e`, `x`, `e x`] dec2enc_some) ++
   RW_TAC std_ss [enc2dec_some, APPEND_NIL]);

val enc2dec_dec2enc = store_thm
  ("enc2dec_dec2enc",
   ``!p d. wf_decoder p d ==> (enc2dec p (dec2enc d) = d)``,
   RW_TAC std_ss [] ++
   MATCH_MP_TAC EQ_EXT ++
   Q.X_GEN_TAC `l` ++
   MP_TAC (Q.SPECL [`p`, `d`] wf_dec2enc) ++
   RW_TAC std_ss [] ++
   Cases_on `d l` <<
   [RW_TAC std_ss [enc2dec_none] ++
    STRIP_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X = Y` MP_TAC ++
    PROVE_TAC [NOT_SOME_NONE, decode_dec2enc_append],
    Cases_on `x` ++
    ASM_SIMP_TAC std_ss [enc2dec_some] ++
    MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``) ++
    RW_TAC std_ss [] >> PROVE_TAC [wf_decoder_def] ++
    MP_TAC (Q.SPECL [`p`, `d`] wf_decoder_def) ++
    ASM_REWRITE_TAC [] ++
    DISCH_THEN (MP_TAC o Q.SPEC `q`) ++
    RW_TAC std_ss [] ++
    RES_TAC ++
    RW_TAC std_ss [APPEND_11] ++
    Suff `d a = SOME (q, [])` >> PROVE_TAC [dec2enc_some] ++
    RW_TAC std_ss [APPEND_NIL]]);

(*---------------------------------------------------------------------------
     Unit decoders
 ---------------------------------------------------------------------------*)

val decode_unit_def = Define `decode_unit p = enc2dec p encode_unit`;

val wf_decode_unit = store_thm
  ("wf_decode_unit",
   ``wf_decoder p (decode_unit p)``,
   RW_TAC std_ss [decode_unit_def, wf_enc2dec, wf_encode_unit]);

val dec2enc_decode_unit = store_thm
  ("dec2enc_decode_unit",
   ``!p x. p x ==> (dec2enc (decode_unit p) x = encode_unit x)``,
   RW_TAC std_ss [decode_unit_def, dec2enc_enc2dec, wf_encode_unit]);

val decode_unit = store_thm
  ("decode_unit",
   ``decode_unit p l = if p () then SOME ((), l) else NONE``,
   RW_TAC std_ss
   [decode_unit_def, enc2dec_none, enc2dec_some, encode_unit_def,
    APPEND, wf_encode_unit, oneTheory.one]);

(*---------------------------------------------------------------------------
     Boolean decoders
 ---------------------------------------------------------------------------*)

val decode_bool_def = Define `decode_bool p = enc2dec p encode_bool`;

val wf_decode_bool = store_thm
  ("wf_decode_bool",
   ``!p. wf_decoder p (decode_bool p)``,
   RW_TAC std_ss [decode_bool_def, wf_enc2dec, wf_encode_bool]);

val dec2enc_decode_bool = store_thm
  ("dec2enc_decode_bool",
   ``!p x. p x ==> (dec2enc (decode_bool p) x = encode_bool x)``,
   RW_TAC std_ss [decode_bool_def, dec2enc_enc2dec, wf_encode_bool]);

val decode_bool = store_thm
  ("decode_bool",
   ``decode_bool p l =
     case l of [] -> NONE || (h :: t) -> if p h then SOME (h, t) else NONE``,
   REPEAT CASE_TAC ++
   RW_TAC std_ss
   [decode_bool_def, enc2dec_none, enc2dec_some, encode_bool_def,
    APPEND, wf_encode_bool]);

(*---------------------------------------------------------------------------
     Pair decoders
 ---------------------------------------------------------------------------*)

val decode_prod_def = Define
  `decode_prod p d1 d2 = enc2dec p (encode_prod (dec2enc d1) (dec2enc d2))`;

val wf_decode_prod = store_thm
  ("wf_decode_prod",
   ``!p1 p2 d1 d2.
       wf_decoder p1 d1 /\ wf_decoder p2 d2 ==>
       wf_decoder (lift_prod p1 p2) (decode_prod (lift_prod p1 p2) d1 d2)``,
   RW_TAC std_ss [decode_prod_def] ++
   PROVE_TAC [wf_dec2enc, wf_enc2dec, wf_encode_prod]);

val dec2enc_decode_prod = store_thm
  ("dec2enc_decode_prod",
   ``!p1 p2 d1 d2 x.
       wf_decoder p1 d1 /\ wf_decoder p2 d2 /\ lift_prod p1 p2 x ==>
       (dec2enc (decode_prod (lift_prod p1 p2) d1 d2) x =
        encode_prod (dec2enc d1) (dec2enc d2) x)``,
   RW_TAC std_ss
   [decode_prod_def, dec2enc_enc2dec, wf_encode_prod, wf_dec2enc]);

val encode_then_decode_prod = store_thm
  ("decode_encode_prod",
   ``!p1 p2 e1 e2 l t.
       wf_encoder p1 e1 /\ wf_encoder p2 e2 /\ lift_prod p1 p2 l ==>
       (decode_prod (lift_prod p1 p2) (enc2dec p1 e1) (enc2dec p2 e2)
        (APPEND (encode_prod e1 e2 l) t) = SOME (l, t))``,
   RW_TAC std_ss [decode_prod_def] ++
   MP_TAC
   (Q.SPECL
    [`lift_prod p1 p2`,
     `encode_prod (dec2enc (enc2dec p1 e1)) (dec2enc (enc2dec p2 e2))`,
     `APPEND (encode_prod e1 e2 l) t`, `l`, `t`]
    (INST_TYPE [alpha |-> ``:'a # 'b``] enc2dec_some)) ++
   MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) ++
   CONJ_TAC >> PROVE_TAC [wf_encode_prod, wf_dec2enc, wf_enc2dec] ++
   RW_TAC std_ss [APPEND_11] ++
   POP_ASSUM (K ALL_TAC) ++
   Cases_on `l` ++
   FULL_SIMP_TAC std_ss [lift_prod_def, encode_prod_def, APPEND_11] ++
   PROVE_TAC [dec2enc_enc2dec]);

val decode_prod = store_thm
  ("decode_prod",
   ``wf_decoder p1 d1 /\ wf_decoder p2 d2 ==>
     (decode_prod (lift_prod p1 p2) d1 d2 l =
      case d1 l of NONE -> NONE
      || SOME (x, t) ->
         (case d2 t of NONE -> NONE
          || SOME (y, t') -> SOME ((x, y), t')))``,
   (REPEAT CASE_TAC ++
    RW_TAC std_ss
    [decode_prod_def, enc2dec_none, GSYM APPEND_ASSOC, encode_prod_alt]) <<
   [STRIP_TAC
    ++ RW_TAC std_ss []
    ++ Cases_on `x`
    ++ FULL_SIMP_TAC std_ss [lift_prod_def]
    ++ PROVE_TAC [decode_dec2enc_append, NOT_SOME_NONE],
    STRIP_TAC
    ++ RW_TAC std_ss []
    ++ Cases_on `x`
    ++ FULL_SIMP_TAC std_ss [lift_prod_def]
    ++ Q.PAT_ASSUM `X = SOME Y` MP_TAC
    ++ MP_TAC (Q.SPECL [`p1`, `d1`, `q'`] decode_dec2enc_append)
    ++ ASM_SIMP_TAC std_ss []
    ++ DISCH_THEN (K ALL_TAC)
    ++ PURE_REWRITE_TAC [GSYM DE_MORGAN_THM]
    ++ STRIP_TAC
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `X = Y` MP_TAC
    ++ RW_TAC std_ss [decode_prod_def, enc2dec_none]
    ++ PROVE_TAC [decode_dec2enc_append, NOT_SOME_NONE],
    Know `wf_decoder (lift_prod p1 p2) (decode_prod (lift_prod p1 p2) d1 d2)`
    >> PROVE_TAC [wf_decode_prod]
    ++ STRIP_TAC
    ++ Know `wf_encoder p1 (dec2enc d1)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know `wf_encoder p2 (dec2enc d2)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know
       `wf_encoder (lift_prod p1 p2) (encode_prod (dec2enc d1) (dec2enc d2))`
    >> PROVE_TAC [wf_encode_prod]
    ++ STRIP_TAC
    ++ ASM_SIMP_TAC std_ss [enc2dec_some, encode_prod_def, APPEND]
    ++ MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``)
    ++ CONJ_TAC
    >> (RW_TAC std_ss [lift_prod_def]
        ++ PROVE_TAC [wf_decoder_def, wf_decode_prod])
    ++ RW_TAC std_ss [lift_prod_def]
    ++ MP_TAC (Q.SPECL [`p1`, `d1`] wf_decoder_def)
    ++ ASM_SIMP_TAC std_ss []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q`)
    ++ RW_TAC std_ss []
    ++ RES_TAC
    ++ RW_TAC std_ss [GSYM APPEND_ASSOC]
    ++ Know `dec2enc d1 q = a` >> PROVE_TAC [APPEND_NIL, dec2enc_some]
    ++ RW_TAC std_ss [APPEND_11]
    ++ Q.PAT_ASSUM `!x. P x` (K ALL_TAC)
    ++ MP_TAC (Q.SPECL [`p2`, `d2`] (INST_TYPE [alpha |-> beta] wf_decoder_def))
    ++ ASM_SIMP_TAC std_ss []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q'`)
    ++ RW_TAC std_ss []
    ++ RES_TAC
    ++ RW_TAC std_ss [GSYM APPEND_ASSOC]
    ++ Know `dec2enc d2 q' = a` >> PROVE_TAC [APPEND_NIL, dec2enc_some]
    ++ RW_TAC std_ss [APPEND_11]]);

(*---------------------------------------------------------------------------
     Sum decoders
 ---------------------------------------------------------------------------*)

val decode_sum_def = Define
  `decode_sum p d1 d2 = enc2dec p (encode_sum (dec2enc d1) (dec2enc d2))`;

val wf_decode_sum = store_thm
  ("wf_decode_sum",
   ``!p1 p2 d1 d2.
       wf_decoder p1 d1 /\ wf_decoder p2 d2 ==>
       wf_decoder (lift_sum p1 p2) (decode_sum (lift_sum p1 p2) d1 d2)``,
   RW_TAC std_ss [decode_sum_def] ++
   PROVE_TAC [wf_dec2enc, wf_enc2dec, wf_encode_sum]);

val dec2enc_decode_sum = store_thm
  ("dec2enc_decode_sum",
   ``!p1 p2 d1 d2 x.
       wf_decoder p1 d1 /\ wf_decoder p2 d2 /\ lift_sum p1 p2 x ==>
       (dec2enc (decode_sum (lift_sum p1 p2) d1 d2) x =
        encode_sum (dec2enc d1) (dec2enc d2) x)``,
   RW_TAC std_ss
   [decode_sum_def, dec2enc_enc2dec, wf_encode_sum, wf_dec2enc]);

val encode_then_decode_sum = store_thm
  ("decode_encode_sum",
   ``!p1 p2 e1 e2 l t.
       wf_encoder p1 e1 /\ wf_encoder p2 e2 /\ lift_sum p1 p2 l ==>
       (decode_sum (lift_sum p1 p2) (enc2dec p1 e1) (enc2dec p2 e2)
        (APPEND (encode_sum e1 e2 l) t) = SOME (l, t))``,
   RW_TAC std_ss [decode_sum_def] ++
   MP_TAC
   (Q.SPECL
    [`lift_sum p1 p2`,
     `encode_sum (dec2enc (enc2dec p1 e1)) (dec2enc (enc2dec p2 e2))`,
     `APPEND (encode_sum e1 e2 l) t`, `l`, `t`]
    (INST_TYPE [alpha |-> ``:'a + 'b``] enc2dec_some)) ++
   MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) ++
   CONJ_TAC >> PROVE_TAC [wf_encode_sum, wf_dec2enc, wf_enc2dec] ++
   RW_TAC std_ss [APPEND_11] ++
   POP_ASSUM (K ALL_TAC) ++
   Cases_on `l` ++
   FULL_SIMP_TAC std_ss [lift_sum_def, encode_sum_def, APPEND_11] ++
   PROVE_TAC [dec2enc_enc2dec]);

val decode_sum = store_thm
  ("decode_sum",
   ``wf_decoder p1 d1 /\ wf_decoder p2 d2 ==>
     (decode_sum (lift_sum p1 p2) d1 d2 l =
      case l of [] -> NONE
      || (T :: t) ->
         (case d1 t of NONE -> NONE
          || SOME (x, t') -> SOME (INL x, t'))
      || (F :: t) ->
         (case d2 t of NONE -> NONE
          || SOME (x, t') -> SOME (INR x, t')))``,
   (REPEAT CASE_TAC ++
    RW_TAC std_ss [decode_sum_def, enc2dec_none, GSYM APPEND_ASSOC]) <<
   [Cases_on `x`
    ++ RW_TAC std_ss [encode_sum_def, APPEND],
    (Cases_on `x` ++ RW_TAC std_ss [encode_sum_def, APPEND])
    ++ STRIP_TAC
    ++ RW_TAC std_ss []
    ++ FULL_SIMP_TAC std_ss [lift_sum_def]
    ++ PROVE_TAC [decode_dec2enc_append, NOT_SOME_NONE],
    Know `wf_decoder (lift_sum p1 p2) (decode_sum (lift_sum p1 p2) d1 d2)`
    >> PROVE_TAC [wf_decode_sum]
    ++ STRIP_TAC
    ++ Know `wf_encoder p1 (dec2enc d1)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know `wf_encoder p2 (dec2enc d2)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know
       `wf_encoder (lift_sum p1 p2) (encode_sum (dec2enc d1) (dec2enc d2))`
    >> PROVE_TAC [wf_encode_sum]
    ++ STRIP_TAC
    ++ ASM_SIMP_TAC std_ss [enc2dec_some, encode_sum_def, APPEND]
    ++ MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``)
    ++ CONJ_TAC
    >> (RW_TAC std_ss [lift_sum_def]
        ++ PROVE_TAC [wf_decoder_def, wf_decode_sum])
    ++ RW_TAC std_ss [lift_sum_def]
    ++ MP_TAC (Q.SPECL [`p1`, `d1`] wf_decoder_def)
    ++ ASM_SIMP_TAC std_ss []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q`)
    ++ RW_TAC std_ss []
    ++ RES_TAC
    ++ RW_TAC std_ss [GSYM APPEND_ASSOC]
    ++ Know `dec2enc d1 q = a` >> PROVE_TAC [APPEND_NIL, dec2enc_some]
    ++ RW_TAC std_ss [APPEND_11],
    (Cases_on `x` ++ RW_TAC std_ss [encode_sum_def, APPEND])
    ++ STRIP_TAC
    ++ RW_TAC std_ss []
    ++ FULL_SIMP_TAC std_ss [lift_sum_def]
    ++ PROVE_TAC [decode_dec2enc_append, NOT_SOME_NONE],
    Know `wf_decoder (lift_sum p1 p2) (decode_sum (lift_sum p1 p2) d1 d2)`
    >> PROVE_TAC [wf_decode_sum]
    ++ STRIP_TAC
    ++ Know `wf_encoder p1 (dec2enc d1)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know `wf_encoder p2 (dec2enc d2)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know
       `wf_encoder (lift_sum p1 p2) (encode_sum (dec2enc d1) (dec2enc d2))`
    >> PROVE_TAC [wf_encode_sum]
    ++ STRIP_TAC
    ++ ASM_SIMP_TAC std_ss [enc2dec_some, encode_sum_def, APPEND]
    ++ MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``)
    ++ CONJ_TAC
    >> (RW_TAC std_ss [lift_sum_def]
        ++ PROVE_TAC [wf_decoder_def, wf_decode_sum])
    ++ RW_TAC std_ss [lift_sum_def]
    ++ MP_TAC (Q.SPECL [`p2`, `d2`] wf_decoder_def)
    ++ ASM_SIMP_TAC std_ss []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q`)
    ++ RW_TAC std_ss []
    ++ RES_TAC
    ++ RW_TAC std_ss [GSYM APPEND_ASSOC]
    ++ Know `dec2enc d2 q = a` >> PROVE_TAC [APPEND_NIL, dec2enc_some]
    ++ RW_TAC std_ss [APPEND_11]]);

(*---------------------------------------------------------------------------
     Option decoders
 ---------------------------------------------------------------------------*)

val decode_option_def = Define
  `decode_option p d = enc2dec p (encode_option (dec2enc d))`;

val wf_decode_option = store_thm
  ("wf_decode_option",
   ``!p d.
       wf_decoder p d ==>
       wf_decoder (lift_option p) (decode_option (lift_option p) d)``,
   RW_TAC std_ss [decode_option_def] ++
   PROVE_TAC [wf_dec2enc, wf_enc2dec, wf_encode_option]);

val dec2enc_decode_option = store_thm
  ("dec2enc_decode_option",
   ``!p d x.
       wf_decoder p d /\ lift_option p x ==>
       (dec2enc (decode_option (lift_option p) d) x =
        encode_option (dec2enc d) x)``,
   RW_TAC std_ss
   [decode_option_def, dec2enc_enc2dec, wf_encode_option, wf_dec2enc]);

val encode_then_decode_option = store_thm
  ("decode_encode_option",
   ``!p e l t.
       wf_encoder p e /\ lift_option p l ==>
       (decode_option (lift_option p) (enc2dec p e)
        (APPEND (encode_option e l) t) = SOME (l, t))``,
   RW_TAC std_ss [decode_option_def] ++
   MP_TAC
   (Q.SPECL [`lift_option p`, `encode_option (dec2enc (enc2dec p e))`,
             `APPEND (encode_option e l) t`, `l`, `t`]
    (INST_TYPE [alpha |-> ``:'a option``] enc2dec_some)) ++
   MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) ++
   CONJ_TAC >> PROVE_TAC [wf_encode_option, wf_dec2enc, wf_enc2dec] ++
   RW_TAC std_ss [APPEND_11] ++
   POP_ASSUM (K ALL_TAC) ++
   Cases_on `l` ++
   FULL_SIMP_TAC std_ss [lift_option_def, encode_option_def, APPEND_11] ++
   RW_TAC std_ss [] ++
   PROVE_TAC [dec2enc_enc2dec]);

val decode_option = store_thm
  ("decode_option",
   ``wf_decoder p d ==>
     (decode_option (lift_option p) d l =
      case l of [] -> NONE
      || (T :: t) ->
         (case d t of NONE -> NONE
          || SOME (x, t') -> SOME (SOME x, t'))
      || (F :: t) -> SOME (NONE, t))``,
   (REPEAT CASE_TAC ++
    RW_TAC std_ss [decode_option_def, enc2dec_none]) <<
   [Cases_on `x`
    ++ RW_TAC std_ss [encode_option_def, APPEND],
    Cases_on `x`
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss
       [encode_option_def, APPEND, GSYM APPEND_ASSOC, lift_option_def]
    ++ STRIP_TAC
    ++ RW_TAC std_ss []
    ++ MP_TAC (Q.SPECL [`p`, `d`] wf_decoder_def)
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `x'`
    ++ RW_TAC std_ss []
    ++ PROVE_TAC [decode_dec2enc_append, NOT_SOME_NONE],
    Know `wf_decoder (lift_option p) (decode_option (lift_option p) d)`
    >> PROVE_TAC [wf_decode_option]
    ++ STRIP_TAC
    ++ Know `wf_encoder p (dec2enc d)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know `wf_encoder (lift_option p) (encode_option (dec2enc d))`
    >> PROVE_TAC [wf_encode_option]
    ++ STRIP_TAC
    ++ ASM_SIMP_TAC std_ss
       [enc2dec_some, encode_option_def, APPEND, lift_option_def]
    ++ MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``)
    ++ CONJ_TAC >> PROVE_TAC [wf_decoder_def, wf_decode_option]
    ++ RW_TAC std_ss []
    ++ MP_TAC (Q.SPECL [`p`, `d`] wf_decoder_def)
    ++ ASM_SIMP_TAC std_ss []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q`)
    ++ RW_TAC std_ss []
    ++ RES_TAC
    ++ RW_TAC std_ss [GSYM APPEND_ASSOC]
    ++ Know `dec2enc d q = a` >> PROVE_TAC [APPEND_NIL, dec2enc_some]
    ++ RW_TAC std_ss [APPEND_11],
    Know `wf_encoder p (dec2enc d)` >> PROVE_TAC [wf_dec2enc]
    ++ STRIP_TAC
    ++ Know `wf_encoder (lift_option p) (encode_option (dec2enc d))`
    >> PROVE_TAC [wf_encode_option]
    ++ STRIP_TAC
    ++ ASM_SIMP_TAC std_ss
       [enc2dec_some, encode_option_def, APPEND, lift_option_def]]);

(*---------------------------------------------------------------------------
     List decoders
 ---------------------------------------------------------------------------*)

val decode_list_def = Define
  `decode_list p d = enc2dec p (encode_list (dec2enc d))`;

val wf_decode_list = store_thm
  ("wf_decode_list",
   ``!p d.
       wf_decoder p d ==> wf_decoder (EVERY p) (decode_list (EVERY p) d)``,
   RW_TAC std_ss [decode_list_def] ++
   PROVE_TAC [wf_dec2enc, wf_enc2dec, wf_encode_list]);

val dec2enc_decode_list = store_thm
  ("dec2enc_decode_list",
   ``!p d x.
       wf_decoder p d /\ EVERY p x ==>
       (dec2enc (decode_list (EVERY p) d) x = encode_list (dec2enc d) x)``,
   RW_TAC std_ss
   [decode_list_def, dec2enc_enc2dec, wf_encode_list, wf_dec2enc]);

val encode_then_decode_list = store_thm
  ("decode_encode_list",
   ``!p e l t.
       wf_encoder p e /\ EVERY p l ==>
       (decode_list (EVERY p) (enc2dec p e) (APPEND (encode_list e l) t) =
        SOME (l, t))``,
   RW_TAC std_ss [decode_list_def] ++
   MP_TAC
   (Q.SPECL [`EVERY p`, `encode_list (dec2enc (enc2dec p e))`,
             `APPEND (encode_list e l) t`, `l`, `t`]
    (INST_TYPE [alpha |-> ``:'a list``] enc2dec_some)) ++
   MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) ++
   CONJ_TAC >> PROVE_TAC [wf_encode_list, wf_dec2enc, wf_enc2dec] ++
   RW_TAC std_ss [APPEND_11] ++
   POP_ASSUM (K ALL_TAC) ++
   Induct_on `l` ++
   RW_TAC std_ss [EVERY_DEF, encode_list_def, APPEND_11] ++
   PROVE_TAC [dec2enc_enc2dec]);

val decode_list = store_thm
  ("decode_list",
   ``wf_decoder p d ==>
     (decode_list (EVERY p) d l =
      case l of [] -> NONE
      || (T :: t) ->
         (case d t of NONE -> NONE
          || SOME (x, t') ->
             (case decode_list (EVERY p) d t' of NONE -> NONE
              || SOME (xs, t'') -> SOME (x :: xs, t'')))
      || (F :: t) -> SOME ([], t))``,
   (REPEAT CASE_TAC ++
    RW_TAC std_ss [decode_list_def, enc2dec_none]) <<
   [Cases_on `x` ++
    RW_TAC std_ss [encode_list_def, APPEND],
    Cases_on `x` ++
    POP_ASSUM MP_TAC ++
    RW_TAC std_ss [encode_list_def, APPEND, GSYM APPEND_ASSOC, EVERY_DEF] ++
    POP_ASSUM (K ALL_TAC) ++
    Q.SPEC_TAC (`APPEND (encode_list (dec2enc d) t'') t'`, `l`) ++
    REPEAT STRIP_TAC ++
    RW_TAC std_ss [] ++
    MP_TAC (Q.SPECL [`p`, `d`] wf_decoder_def) ++
    RW_TAC std_ss [] ++
    Q.EXISTS_TAC `h` ++
    RW_TAC std_ss [] ++
    PROVE_TAC [decode_dec2enc_append, NOT_SOME_NONE],
    Cases_on `x` ++
    POP_ASSUM MP_TAC ++
    RW_TAC std_ss [encode_list_def, APPEND, GSYM APPEND_ASSOC, EVERY_DEF] ++
    STRIP_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X = SOME Y` MP_TAC ++
    MP_TAC (Q.SPECL [`p`, `d`, `h`] decode_dec2enc_append) ++
    ASM_SIMP_TAC std_ss [] ++
    DISCH_THEN (K ALL_TAC) ++
    PURE_REWRITE_TAC [GSYM DE_MORGAN_THM] ++
    STRIP_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X = Y` MP_TAC ++
    RW_TAC std_ss [decode_list_def, enc2dec_none] ++
    PROVE_TAC [],
    Know `wf_decoder (EVERY p) (decode_list (EVERY p) d)` >>
    PROVE_TAC [wf_decode_list] ++
    STRIP_TAC ++
    Know `wf_encoder p (dec2enc d)` >> PROVE_TAC [wf_dec2enc] ++
    STRIP_TAC ++
    Know `wf_encoder (EVERY p) (encode_list (dec2enc d))` >>
    PROVE_TAC [wf_encode_list] ++
    STRIP_TAC ++
    ASM_SIMP_TAC std_ss [enc2dec_some, encode_list_def, APPEND] ++
    MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``) ++
    CONJ_TAC >> PROVE_TAC [EVERY_DEF, wf_decoder_def, wf_decode_list] ++
    RW_TAC std_ss [EVERY_DEF] ++
    MP_TAC (Q.SPECL [`p`, `d`] wf_decoder_def) ++
    ASM_SIMP_TAC std_ss [] ++
    DISCH_THEN (MP_TAC o Q.SPEC `q`) ++
    RW_TAC std_ss [] ++
    RES_TAC ++
    RW_TAC std_ss [GSYM APPEND_ASSOC] ++
    Know `dec2enc d q = a` >> PROVE_TAC [APPEND_NIL, dec2enc_some] ++
    RW_TAC std_ss [APPEND_11] ++
    Q.PAT_ASSUM `!x. P x` (K ALL_TAC) ++
    MP_TAC
    (Q.ISPECL [`EVERY (p : 'a -> bool)`, `decode_list (EVERY p) d`]
     wf_decoder_def) ++
    ASM_SIMP_TAC std_ss [] ++
    DISCH_THEN (MP_TAC o Q.SPEC `q'`) ++
    RW_TAC std_ss [] ++
    RES_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `!x. P x` (K ALL_TAC) ++
    Q.PAT_ASSUM `X = Y` MP_TAC ++
    ASM_SIMP_TAC std_ss [decode_list_def, enc2dec_some],
    Know `wf_decoder (EVERY p) (decode_list (EVERY p) d)` >>
    PROVE_TAC [wf_decode_list] ++
    STRIP_TAC ++
    Know `wf_encoder p (dec2enc d)` >> PROVE_TAC [wf_dec2enc] ++
    STRIP_TAC ++
    Know `wf_encoder (EVERY p) (encode_list (dec2enc d))` >>
    PROVE_TAC [wf_encode_list] ++
    STRIP_TAC ++
    ASM_SIMP_TAC std_ss [enc2dec_some, encode_list_def, APPEND, EVERY_DEF]]);

(*---------------------------------------------------------------------------
     Num decoders
 ---------------------------------------------------------------------------*)

val decode_num_def = Define `decode_num p = enc2dec p encode_num`;

val wf_decode_num = store_thm
  ("wf_decode_num",
   ``!p. wf_decoder p (decode_num p)``,
   RW_TAC std_ss [decode_num_def, wf_enc2dec, wf_encode_num]);

val dec2enc_decode_num = store_thm
  ("dec2enc_decode_num",
   ``!p x. p x ==> (dec2enc (decode_num p) x = encode_num x)``,
   RW_TAC std_ss [decode_num_def, dec2enc_enc2dec, wf_encode_num]);

(*
val decode_num = store_thm
  ("decode_num",
   ``decode_num p l =
     case l of
        (T :: T :: t) -> if p 0 then SOME (0, t) else NONE
     || (T :: F :: t) ->
        (case decode_num (K T) t of NONE -> NONE
         || SOME (v, t') ->
            if p (2 * v + 1) then SOME (2 * v + 1, t') else NONE)
     || (F :: t) ->
        (case decode_num (K T) t of NONE -> NONE
         || SOME (v, t') ->
            if p (2 * v + 2) then SOME (2 * v + 2, t') else NONE)
     || _ -> NONE``,
   (REPEAT CASE_TAC ++
    RW_TAC std_ss [decode_num_def, enc2dec_none]) <<
   [ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC std_ss [APPEND],
    ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC std_ss [APPEND],
    RW_TAC std_ss [enc2dec_some, wf_encode_num]
    ++ ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC std_ss [APPEND],
    ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC std_ss [APPEND]
    ++ METIS_TAC [],
    ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC std_ss [APPEND]
    ++ STRIP_TAC
    ++ RW_TAC std_ss []
    ++ Suff `encode_num = dec2enc (decode_num (K T))`
    >> (STRIP_TAC
        ++ Q.PAT_ASSUM `X = NONE` MP_TAC
        ++ RW_TAC std_ss []
        ++ MP_TAC (Q.SPEC `K T` wf_decode_num)
        ++ Q.SPEC_TAC (`decode_num (K T)`, `d`)
        ++ Q.SPEC_TAC (`(x - 1) DIV 2`, `x`)
        ++ POP_ASSUM_LIST (K ALL_TAC)
        ++ REPEAT STRIP_TAC
        ++ MP_TAC
           (Q.SPECL [`K T`, `d`, `x`, `t`]
            (INST_TYPE [alpha |-> ``:num``] decode_dec2enc_append))
        ++ RW_TAC std_ss [K_THM])
    ++ RW_TAC std_ss [decode_num_def]
    ++ MATCH_MP_TAC EQ_EXT
    ++ RW_TAC std_ss [dec2enc_enc2dec, K_THM, wf_encode_num],
    ASM_SIMP_TAC std_ss [enc2dec_some, wf_encode_num, APPEND]
    ++ ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC arith_ss [APPEND, GSYM ADD1, EVEN_ODD, ODD_DOUBLE]
    ++ ONCE_REWRITE_TAC [MULT_COMM]
    ++ RW_TAC std_ss [MULT_DIV]
    ++ MP_TAC
       (Q.SPECL [`K T`, `decode_num (K T)`]
        (INST_TYPE [alpha |-> ``:num``] wf_decoder_def))
    ++ ASM_SIMP_TAC std_ss [wf_decode_num]
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q`)
    ++ RW_TAC std_ss [K_THM]
    ++ RES_TAC
    ++ RW_TAC std_ss [APPEND_11]
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`a`, `[]`])
    ++ RW_TAC std_ss [APPEND_NIL, decode_num_def, enc2dec_some, wf_encode_num],
    ONCE_REWRITE_TAC [encode_num_def]
    ++ RW_TAC std_ss [APPEND]
    ++ STRIP_TAC
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `X = SOME Y` MP_TAC
    ++ MP_TAC
       (Q.SPECL [`K T`, `decode_num (K T)`]
        (INST_TYPE [alpha |-> ``:num``] wf_decoder_def))
    ++ ASM_SIMP_TAC std_ss [wf_decode_num]
    ++ DISCH_THEN (MP_TAC o Q.SPEC `q`)
    ++ RW_TAC std_ss [K_THM]
    ++ RW_TAC std_ss []
    ++ 
    ++ POP_ASSUM (MP_TAC o Q.SPECL [`a`, `[]`])
    ++ RW_TAC std_ss [APPEND_NIL, decode_num_def, enc2dec_some, wf_encode_num],



    ++ Know `decode_num (K T) q = a`
    >> PROVE_TAC [APPEND_NIL, dec2enc_some, wf_decode_num] ++
    RW_TAC std_ss [APPEND_11] ++
    Q.PAT_ASSUM `!x. P x` (K ALL_TAC) ++
    MP_TAC
    (Q.ISPECL [`EVERY (p : 'a -> bool)`, `decode_num (EVERY p) d`]
     wf_decoder_def) ++
    ASM_SIMP_TAC std_ss [] ++
    DISCH_THEN (MP_TAC o Q.SPEC `q'`) ++
    RW_TAC std_ss [] ++
    RES_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `!x. P x` (K ALL_TAC) ++
    Q.PAT_ASSUM `X = Y` MP_TAC ++
    ASM_SIMP_TAC std_ss [decode_num_def, enc2dec_some],
    Know `wf_decoder (EVERY p) (decode_num (EVERY p) d)` >>
    PROVE_TAC [wf_decode_num] ++
    STRIP_TAC ++
    Know `wf_encoder p (dec2enc d)` >> PROVE_TAC [wf_dec2enc] ++
    STRIP_TAC ++
    Know `wf_encoder (EVERY p) (encode_num (dec2enc d))` >>
    PROVE_TAC [wf_encode_num] ++
    STRIP_TAC ++
    ASM_SIMP_TAC std_ss [enc2dec_some, encode_num_def, APPEND, EVERY_DEF]]);
*)

(*---------------------------------------------------------------------------
     Trees
 ---------------------------------------------------------------------------*)

val decode_tree_def = Define
  `decode_tree p d = enc2dec p (encode_tree (dec2enc d))`;

val wf_decode_tree = store_thm
  ("wf_decode_tree",
   ``!p d.
       wf_decoder p d ==>
       wf_decoder (lift_tree p) (decode_tree (lift_tree p) d)``,
   RW_TAC std_ss [decode_tree_def] ++
   PROVE_TAC [wf_dec2enc, wf_enc2dec, wf_encode_tree]);

val decode_tree = store_thm
  ("decode_tree",
   ``wf_decoder p d ==>
     (decode_tree (lift_tree p) d l =
      case d l of NONE -> NONE
      || SOME (a, t) ->
         (case decode_list (EVERY (lift_tree p))
               (decode_tree (lift_tree p) d) t
          of NONE -> NONE
          || SOME (ts, t') -> SOME (Node a ts, t')))``,
   STRIP_TAC ++
   Know `wf_decoder (lift_tree p) (decode_tree (lift_tree p) d)` >>
   PROVE_TAC [wf_decode_tree] ++
   STRIP_TAC ++
   Know `wf_decoder (EVERY (lift_tree p))
         (decode_list (EVERY (lift_tree p)) (decode_tree (lift_tree p) d))` >>
   PROVE_TAC [wf_decode_list] ++
   STRIP_TAC ++
   REPEAT CASE_TAC <<
   [RW_TAC std_ss [decode_tree_def, enc2dec_none] ++
    STRIP_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X = Y` MP_TAC ++
    Cases_on `x` ++
    RW_TAC std_ss [encode_tree_def, GSYM APPEND_ASSOC] ++
    POP_ASSUM MP_TAC ++
    RW_TAC std_ss [lift_tree_def] ++
    MP_TAC (Q.SPECL [`p`, `d`, `a`] decode_dec2enc_append) ++
    RW_TAC std_ss [],
    RW_TAC std_ss [decode_tree_def, enc2dec_none] ++
    STRIP_TAC ++
    RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X = SOME Y` MP_TAC ++
    POP_ASSUM MP_TAC ++
    Cases_on `x` ++
    RW_TAC std_ss [lift_tree_def, encode_tree_def, GSYM APPEND_ASSOC] ++
    MP_TAC (Q.SPECL [`p`, `d`, `a`] decode_dec2enc_append) ++
    RW_TAC std_ss [] ++
    REVERSE (Cases_on `a = q`) >> RW_TAC std_ss [] ++
    RW_TAC std_ss [] ++
    STRIP_TAC ++
    RW_TAC std_ss [] ++
    POP_ASSUM (K ALL_TAC) ++
    Q.PAT_ASSUM `X = Y` MP_TAC ++
    POP_ASSUM MP_TAC ++
    POP_ASSUM (K ALL_TAC) ++
    CONV_TAC (DEPTH_CONV ETA_CONV) ++
    STRIP_TAC ++
    MP_TAC (Q.SPECL [`lift_tree p`, `encode_tree (dec2enc d)`, `l`, `t`]
            (INST_TYPE [alpha |-> ``:'a tree``] encode_then_decode_list)) ++
    MATCH_MP_TAC (PROVE [] ``(y ==> z) /\ x ==> (x ==> y) ==> z``) ++
    CONJ_TAC >> RW_TAC std_ss [decode_tree_def] ++
    PROVE_TAC [wf_encode_tree, wf_dec2enc],
    MP_TAC
    (Q.SPECL [`lift_tree p`, `encode_tree (dec2enc d)`, `l`, `Node q q'`, `r'`]
     (INST_TYPE [alpha |-> ``:'a tree``] enc2dec_some)) ++
    MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) ++
    CONJ_TAC >> PROVE_TAC [wf_encode_tree, wf_dec2enc] ++
    DISCH_THEN (fn th => SIMP_TAC std_ss [decode_tree_def, th]) ++
    SIMP_TAC std_ss [encode_tree_def, GSYM APPEND_ASSOC, lift_tree_def] ++
    CONV_TAC (DEPTH_CONV ETA_CONV) ++
    Suff
    `(p q /\ (l = APPEND (dec2enc d q) r)) /\
     (ALL_EL (lift_tree p) q' /\
      (r = APPEND (encode_list (encode_tree (dec2enc d)) q') r'))` >>
    RW_TAC std_ss [] ++
    CONJ_TAC <<
    [Know `enc2dec p (dec2enc d) l = SOME (q, r)` >>
     PROVE_TAC [enc2dec_dec2enc] ++
     RW_TAC std_ss [enc2dec_some, wf_dec2enc],
     POP_ASSUM MP_TAC ++
     SIMP_TAC std_ss [decode_list_def] ++
     RW_TAC std_ss [enc2dec_some, wf_dec2enc, wf_encode_list, APPEND_11] ++
     Q.PAT_ASSUM `X = Y` (K ALL_TAC) ++
     Induct_on `q'` ++
     RW_TAC std_ss [EVERY_DEF, encode_list_def, APPEND_11] ++
     RW_TAC std_ss
     [decode_tree_def, dec2enc_enc2dec, wf_dec2enc, wf_encode_tree]]]);

val _ = export_theory ();

