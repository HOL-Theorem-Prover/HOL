(*===========================================================================*)
(* Defining Decoders to be inverse Encoders                                  *)
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
 Define `wf_coder p (e : 'a -> bool list) d = (!x. p x ==> (d (e x) = x))`;

(*---------------------------------------------------------------------------
     Well-formed coders occur naturally from use of enc2dec.
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
   SIMP_TAC std_ss [decode_def, o_THM] ++
   RW_TAC std_ss [enc2dec_some] ++
   MP_TAC (Q.SPECL [`p`, `e`] wf_encoder_def) ++
   RW_TAC std_ss [] ++
   Suff `IS_PREFIX (e x) (e q)` >> PROVE_TAC [] ++
   PROVE_TAC [IS_PREFIX_APPEND]);

val wf_coder = store_thm
  ("wf_coder",
   ``!p e. wf_encoder p e ==> wf_coder p e (decode (enc2dec p e))``,
   RW_TAC std_ss [wf_coder_def, decode_encode]);

val wf_coder_op = store_thm
  ("wf_coder_op",
   ``!p e f.
       wf_encoder p e /\ (!x. p x ==> (e x = f x)) ==>
       wf_coder p e (decode (enc2dec p f))``,
   RW_TAC std_ss [wf_coder_def]
   ++ HO_METIS_TAC [decode_encode, wf_encoder_eq]);

(*---------------------------------------------------------------------------
     Boolean coders
 ---------------------------------------------------------------------------*)

val wf_coder_bool = store_thm
  ("wf_coder_bool",
   ``wf_coder total encode_bool decode_bool``,
   RW_TAC std_ss [wf_encode_bool, decode_bool_def, wf_coder, dec_bool_def]);

(*---------------------------------------------------------------------------
     List coders
 ---------------------------------------------------------------------------*)

val wf_coder_list = store_thm
  ("wf_coder_list",
   ``!p (e : 'a -> bool list).
       wf_encoder p e ==>
       wf_coder (EVERY p) (encode_list e)
       (decode_list (EVERY p) (enc2dec p e))``,
   RW_TAC std_ss [decode_list_def, dec_list_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ RW_TAC std_ss [wf_encode_list]
   ++ Induct_on `x`
   ++ RW_TAC std_ss [encode_list_def, EVERY_DEF, dec2enc_enc2dec]);

(*---------------------------------------------------------------------------
     Tree coders
 ---------------------------------------------------------------------------*)

val wf_coder_tree = store_thm
  ("wf_coder_tree",
   ``!p (e : 'a -> bool list).
       wf_encoder p e ==>
       wf_coder (lift_tree p) (encode_tree e)
       (decode_tree (lift_tree p) (enc2dec p e))``,
   RW_TAC std_ss [decode_tree_def, dec_tree_def]
   ++ MATCH_MP_TAC wf_coder_op
   ++ RW_TAC std_ss [wf_encode_tree]
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`x`, `t`)
   ++ HO_MATCH_MP_TAC tree_ind
   ++ RW_TAC std_ss [encode_tree_def, lift_tree_def, dec2enc_enc2dec, APPEND_11]
   ++ Induct_on `ts`
   ++ RW_TAC std_ss [MEM, encode_list_def, EVERY_DEF]);

val _ = export_theory ();

