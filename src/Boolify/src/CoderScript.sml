(*===========================================================================*)
(* Pairs of encoder/decoders.                                                *)
(*===========================================================================*)

(* Interactive mode
app load
["bossLib", "rich_listTheory", "EncodeTheory", "DecodeTheory", "normalForms",
 "metisLib"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools
     arithmeticTheory listTheory rich_listTheory EncodeTheory DecodeTheory
     metisLib optionTheory normalForms combinTheory;

val _ = new_theory "Coder";

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
     Well-formed encoder/decoder pairs.
 ---------------------------------------------------------------------------*)

val wf_coder_def =
 Define
 `wf_coder p (e : 'a -> bool list) d = wf_encoder p e /\ (d = enc2dec p e)`;

(*---------------------------------------------------------------------------
     decode turns a decoding parser of type

       bool list -> ('a # bool list) option

     into a straight function of type

       bool list -> 'a
 ---------------------------------------------------------------------------*)

val decode_def = Define `decode f x = FST (THE (f x))`;

(*---------------------------------------------------------------------------
     Well-formed coders have nice properties for boolification.
 ---------------------------------------------------------------------------*)

val decode_encode = store_thm
  ("decode_encode",
   ``!p e x. wf_encoder p e /\ p x ==> (decode (enc2dec p e) (e x) = x)``,
   RW_TAC std_ss [] ++
   Cases_on `enc2dec p e (e x)` >>
   (POP_ASSUM MP_TAC ++
    RW_TAC std_ss [enc2dec_none] ++
    PROVE_TAC [APPEND_NIL]) ++
   POP_ASSUM MP_TAC ++
   Cases_on `x'` ++
   SIMP_TAC std_ss [decode_def] ++
   RW_TAC std_ss [enc2dec_some] ++
   MP_TAC (Q.SPECL [`p`, `e`] wf_encoder_def) ++
   RW_TAC std_ss [] ++
   Suff `IS_PREFIX (e x) (e q)` >> PROVE_TAC [] ++
   PROVE_TAC [IS_PREFIX_APPEND]);

val wf_coder = store_thm
  ("wf_coder",
   ``!p e d.
       wf_coder p (e : 'a -> bool list) d ==>
       !x. p x ==> (decode d (e x) = x)``,
   RW_TAC std_ss [wf_coder_def, decode_encode]);

val wf_coder_op = store_thm
  ("wf_coder_op",
   ``!p e f.
       wf_encoder p e /\ (!x. p x ==> (e x = f x)) ==>
       wf_coder p e (enc2dec p f)``,
   RW_TAC std_ss [wf_coder_def]
   ++ MATCH_MP_TAC EQ_EXT
   ++ RW_TAC std_ss []
   ++ Know `wf_encoder p f` >> HO_METIS_TAC [wf_encoder_eq]
   ++ STRIP_TAC
   ++ (Cases_on `enc2dec p e x`
       ++ Cases_on `enc2dec p f x`
       ++ POP_ASSUM MP_TAC
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [enc2dec_none, enc2dec_some_alt]) <<
   [PROVE_TAC [],
    PROVE_TAC [],
    Cases_on `x'`
    ++ Cases_on `x''`
    ++ FULL_SIMP_TAC std_ss []
    ++ Suff `q = q'` >> PROVE_TAC [APPEND_11]
    ++ PROVE_TAC [wf_encoder_alt, biprefix_append, biprefix_refl]]);

(*---------------------------------------------------------------------------
     Unit coders
 ---------------------------------------------------------------------------*)

val wf_coder_unit = store_thm
  ("wf_coder_unit",
   ``!p. wf_coder p encode_unit (decode_unit p)``,
   RW_TAC std_ss [wf_encode_unit, decode_unit_def, wf_coder_def]);

(*---------------------------------------------------------------------------
     Boolean coders
 ---------------------------------------------------------------------------*)

val wf_coder_bool = store_thm
  ("wf_coder_bool",
   ``!p. wf_coder p encode_bool (decode_bool p)``,
   RW_TAC std_ss [wf_encode_bool, decode_bool_def, wf_coder_def]);

(*---------------------------------------------------------------------------
     Pair coders
 ---------------------------------------------------------------------------*)

val wf_coder_prod = store_thm
  ("wf_coder_prod",
   ``!p1 p2 (e1 : 'a -> bool list) (e2 : 'b -> bool list) d1 d2.
       wf_coder p1 e1 d1 /\ wf_coder p2 e2 d2 ==>
       wf_coder (lift_prod p1 p2) (encode_prod e1 e2)
       (decode_prod (lift_prod p1 p2) d1 d2)``,
   RW_TAC std_ss [decode_prod_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_prod]
   ++ Cases
   ++ RW_TAC std_ss [encode_prod_def, lift_prod_def, dec2enc_enc2dec]);

(*---------------------------------------------------------------------------
     Sum coders
 ---------------------------------------------------------------------------*)

val wf_coder_sum = store_thm
  ("wf_coder_sum",
   ``!p1 p2 (e1 : 'a -> bool list) (e2 : 'b -> bool list) d1 d2.
       wf_coder p1 e1 d1 /\ wf_coder p2 e2 d2 ==>
       wf_coder (lift_sum p1 p2) (encode_sum e1 e2)
       (decode_sum (lift_sum p1 p2) d1 d2)``,
   RW_TAC std_ss [decode_sum_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_sum]
   ++ Cases
   ++ RW_TAC std_ss [encode_sum_def, lift_sum_def, dec2enc_enc2dec]);

(*---------------------------------------------------------------------------
     Option coders
 ---------------------------------------------------------------------------*)

val wf_coder_option = store_thm
  ("wf_coder_option",
   ``!p (e : 'a -> bool list) d.
       wf_coder p e d ==>
       wf_coder (lift_option p) (encode_option e)
       (decode_option (lift_option p) d)``,
   RW_TAC std_ss [decode_option_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_option]
   ++ Induct
   ++ RW_TAC std_ss [encode_option_def, lift_option_def, dec2enc_enc2dec]);

(*---------------------------------------------------------------------------
     List coders
 ---------------------------------------------------------------------------*)

val wf_coder_list = store_thm
  ("wf_coder_list",
   ``!p (e : 'a -> bool list) d.
       wf_coder p e d ==>
       wf_coder (EVERY p) (encode_list e) (decode_list (EVERY p) d)``,
   RW_TAC std_ss [decode_list_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_list]
   ++ Induct
   ++ RW_TAC std_ss [encode_list_def, EVERY_DEF, dec2enc_enc2dec]);

(*---------------------------------------------------------------------------
     Num coders (Norrish numerals)
 ---------------------------------------------------------------------------*)

val wf_coder_num = store_thm
  ("wf_coder_num",
   ``!p. wf_coder p encode_num (decode_num p)``,
   RW_TAC std_ss [wf_encode_num, decode_num_def, wf_coder_def]);

(*---------------------------------------------------------------------------
     Bounded number coders
 ---------------------------------------------------------------------------*)

val wf_coder_bnum = store_thm
  ("wf_coder_bnum",
   ``!m p. wf_pred_bnum m p ==> wf_coder p (encode_bnum m) (decode_bnum m p)``,
   RW_TAC std_ss [wf_encode_bnum, decode_bnum_def, wf_coder_def]);

(*---------------------------------------------------------------------------
     Tree coders
 ---------------------------------------------------------------------------*)

val wf_coder_tree = store_thm
  ("wf_coder_tree",
   ``!p (e : 'a -> bool list) d.
       wf_coder p e d ==>
       wf_coder (lift_tree p) (encode_tree e) (decode_tree (lift_tree p) d)``,
   RW_TAC std_ss [decode_tree_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_tree]
   ++ HO_MATCH_MP_TAC tree_ind
   ++ RW_TAC std_ss [encode_tree_def, lift_tree_def, dec2enc_enc2dec, APPEND_11]
   ++ Induct_on `ts`
   ++ RW_TAC std_ss [encode_list_def, EVERY_DEF, dec2enc_enc2dec, MEM]);

val _ = export_theory ();



