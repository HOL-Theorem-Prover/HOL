(*===========================================================================*)
(* Pairs of encoder/decoders.                                                *)
(*===========================================================================*)

(* Interactive mode
app load
["bossLib", "rich_listTheory", "EncodeTheory", "DecodeTheory", "normalForms",
 "metisLib"];
*)
Theory Coder
Ancestors
  pair arithmetic list rich_list Encode Decode option combin
Libs
  pairTools metisLib normalForms


val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;

val REVERSE = Tactical.REVERSE;

val TOP_CASE_TAC = BasicProvers.TOP_CASE_TAC;

(*---------------------------------------------------------------------------
     decode turns a decoding parser of type

       bool list -> ('a # bool list) option

     into a straight function of type

       bool list -> 'a
 ---------------------------------------------------------------------------*)

Definition decode_def:
   decode (p : 'a -> bool) (d : bool list -> ('a # bool list) option) l =
   case d l of SOME (x, _) => x | NONE => @x. p x
End

(*---------------------------------------------------------------------------
     Well-formed (predicate,encoder,decoder) triples.
 ---------------------------------------------------------------------------*)

Definition wf_coder_def:
   wf_coder (p, e, d) <=> wf_pred p /\ wf_encoder p e /\ (d = enc2dec p e)
End

Definition domain_def:
   domain
   (p : 'a->bool, e : 'a->bool list, d : bool list->('a#bool list) option) = p
End

Definition encoder_def:
   encoder
   (p : 'a->bool, e : 'a->bool list, d : bool list->('a#bool list) option) = e
End

Definition decoder_def:
   decoder
   (p : 'a->bool, e : 'a->bool list, d : bool list->('a#bool list) option) =
   decode p d
End

(*---------------------------------------------------------------------------
     Well-formed coders have nice properties for boolification.
 ---------------------------------------------------------------------------*)

Theorem decode_encode:
     !p e x. wf_encoder p e /\ p x ==> (decode p (enc2dec p e) (e x) = x)
Proof
   RW_TAC std_ss [] >>
   Cases_on `enc2dec p e (e x)` >-
   (POP_ASSUM MP_TAC >>
    RW_TAC std_ss [enc2dec_none] >>
    PROVE_TAC [APPEND_NIL]) >>
   POP_ASSUM MP_TAC >>
   Cases_on `x'` >>
   SIMP_TAC std_ss [decode_def] >>
   RW_TAC std_ss [enc2dec_some] >>
   MP_TAC (Q.SPECL [`p`, `e`] wf_encoder_def) >>
   RW_TAC std_ss [] >>
   Suff `IS_PREFIX (e x) (e q)` >- PROVE_TAC [] >>
   PROVE_TAC [IS_PREFIX_APPEND]
QED

Theorem wf_coder:
     !c.
       wf_coder c ==>
       !x. domain c x ==> (decoder c (encoder c x) = x)
Proof
   Cases
   >> Cases_on `r`
   >> RW_TAC std_ss
      [wf_coder_def, decode_encode, encoder_def, decoder_def, domain_def]
QED

Theorem wf_coder_closed:
     !c. wf_coder c ==> !l. domain c (decoder c l)
Proof
   Cases
   >> Cases_on `r`
   >> RW_TAC std_ss
      [wf_coder_def, domain_def, decoder_def, decode_def, wf_pred_def]
   >> REPEAT TOP_CASE_TAC >- (HO_MATCH_MP_TAC SELECT_AX >> PROVE_TAC [])
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [enc2dec_some]
QED

Theorem wf_coder_op:
     !p e f.
       (?x. p x) /\ wf_encoder p e /\ (!x. p x ==> (e x = f x)) ==>
       wf_coder (p, e, enc2dec p f)
Proof
   RW_TAC std_ss [wf_coder_def, wf_pred_def]
   >> Q.UNDISCH_TAC `p x`
   >> DISCH_THEN (K ALL_TAC)
   >> MATCH_MP_TAC EQ_EXT
   >> RW_TAC std_ss []
   >> Know `wf_encoder p f` >- METIS_TAC [wf_encoder_eq]
   >> STRIP_TAC
   >> (Cases_on `enc2dec p e x`
       >> Cases_on `enc2dec p f x`
       >> POP_ASSUM MP_TAC
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [enc2dec_none, enc2dec_some_alt]) >|
   [PROVE_TAC [],
    PROVE_TAC [],
    Cases_on `x'`
    >> Cases_on `x''`
    >> FULL_SIMP_TAC std_ss []
    >> Suff `q = q'` >- PROVE_TAC [APPEND_11]
    >> PROVE_TAC [wf_encoder_alt, biprefix_append, biprefix_refl]]
QED

(*---------------------------------------------------------------------------
     Units
 ---------------------------------------------------------------------------*)

Definition unit_coder_def:   unit_coder p = (p, encode_unit, decode_unit p)
End

Theorem wf_coder_unit:
     !p. wf_pred p ==> wf_coder (unit_coder p)
Proof
   RW_TAC std_ss
   [unit_coder_def, wf_encode_unit, wf_coder_def, decode_unit_def]
QED

(*---------------------------------------------------------------------------
     Booleans
 ---------------------------------------------------------------------------*)

Definition bool_coder_def:   bool_coder p = (p, encode_bool, decode_bool p)
End

Theorem wf_coder_bool:
     !p. wf_pred p ==> wf_coder (bool_coder p)
Proof
   RW_TAC std_ss
   [bool_coder_def, wf_encode_bool, decode_bool_def, wf_coder_def]
QED

(*---------------------------------------------------------------------------
     Pairs
 ---------------------------------------------------------------------------*)

Definition prod_coder_def:
   prod_coder (p1, e1, d1) (p2, e2, d2) =
   (lift_prod p1 p2, encode_prod e1 e2, decode_prod (lift_prod p1 p2) d1 d2)
End

Theorem wf_coder_prod:
     !c1 c2. wf_coder c1 /\ wf_coder c2 ==> wf_coder (prod_coder c1 c2)
Proof
   REPEAT GEN_TAC
   >> Know `?p1 e1 d1. c1 = (p1, e1, d1)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> Know `?p2 e2 d2. c2 = (p2, e2, d2)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [decode_prod_def, prod_coder_def]
   >> MATCH_MP_TAC wf_coder_op
   >> FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_prod, wf_pred_def]
   >> CONJ_TAC >- (Q.EXISTS_TAC `(x, x')` >> RW_TAC std_ss [lift_prod_def])
   >> Cases
   >> RW_TAC std_ss [encode_prod_def, lift_prod_def, dec2enc_enc2dec]
QED

(*---------------------------------------------------------------------------
     Sums
 ---------------------------------------------------------------------------*)

Definition sum_coder_def:
   sum_coder (p1, e1, d1) (p2, e2, d2) =
   (lift_sum p1 p2, encode_sum e1 e2, decode_sum (lift_sum p1 p2) d1 d2)
End

Theorem wf_coder_sum:
     !c1 c2. wf_coder c1 /\ wf_coder c2 ==> wf_coder (sum_coder c1 c2)
Proof
   REPEAT GEN_TAC
   >> Know `?p1 e1 d1. c1 = (p1, e1, d1)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> Know `?p2 e2 d2. c2 = (p2, e2, d2)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [decode_sum_def, sum_coder_def]
   >> MATCH_MP_TAC wf_coder_op
   >> FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_sum, wf_pred_def]
   >> CONJ_TAC >- (Q.EXISTS_TAC `INL x` >> RW_TAC std_ss [lift_sum_def])
   >> Cases
   >> RW_TAC std_ss [encode_sum_def, lift_sum_def, dec2enc_enc2dec]
QED

(*---------------------------------------------------------------------------
     Options
 ---------------------------------------------------------------------------*)

Definition option_coder_def:
   option_coder (p, e, d) =
   (lift_option p, encode_option e, decode_option (lift_option p) d)
End

Theorem wf_coder_option:
     !c. wf_coder c ==> wf_coder (option_coder c)
Proof
   REPEAT GEN_TAC
   >> Know `?p e d. c = (p, e, d)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [decode_option_def, option_coder_def]
   >> MATCH_MP_TAC wf_coder_op
   >> FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_option, wf_pred_def]
   >> CONJ_TAC >- (Q.EXISTS_TAC `NONE` >> RW_TAC std_ss [lift_option_def])
   >> Induct
   >> RW_TAC std_ss [encode_option_def, lift_option_def, dec2enc_enc2dec]
QED

(*---------------------------------------------------------------------------
     Lists
 ---------------------------------------------------------------------------*)

Definition list_coder_def:
   list_coder (p, e, d) =
   (EVERY p, encode_list e, decode_list (EVERY p) d)
End

Theorem wf_coder_list:
     !c. wf_coder c ==> wf_coder (list_coder c)
Proof
   REPEAT GEN_TAC
   >> Know `?p e d. c = (p, e, d)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [decode_list_def, list_coder_def]
   >> MATCH_MP_TAC wf_coder_op
   >> FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_list, wf_pred_def]
   >> CONJ_TAC >- (Q.EXISTS_TAC `[]` >> RW_TAC std_ss [EVERY_DEF])
   >> Induct
   >> RW_TAC std_ss [encode_list_def, EVERY_DEF, dec2enc_enc2dec]
QED

(*---------------------------------------------------------------------------
     Bounded lists
 ---------------------------------------------------------------------------*)

Definition blist_coder_def:
   blist_coder m (p, e, d) =
   (lift_blist m p, encode_blist m e, decode_blist (lift_blist m p) m d)
End

Theorem wf_coder_blist:
     !m c. wf_coder c ==> wf_coder (blist_coder m c)
Proof
   REPEAT GEN_TAC
   >> Know `?p e d. c = (p, e, d)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [decode_blist_def, blist_coder_def]
   >> MATCH_MP_TAC wf_coder_op
   >> FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_blist, wf_pred_def]
   >> Induct_on `m`
   >- (REVERSE CONJ_TAC
       >- RW_TAC std_ss [encode_blist_def]
       >> Q.EXISTS_TAC `[]`
       >> RW_TAC std_ss [lift_blist_def, LENGTH, EVERY_DEF])
   >> POP_ASSUM STRIP_ASSUME_TAC
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `x :: x'` >> RW_TAC std_ss [lift_blist_suc])
   >> Cases >- RW_TAC std_ss [lift_blist_def, LENGTH]
   >> RW_TAC std_ss
      [lift_blist_suc, encode_blist_def, dec2enc_enc2dec, HD, TL]
QED

(*---------------------------------------------------------------------------
     Nums (Norrish numerals)
 ---------------------------------------------------------------------------*)

Definition num_coder_def:   num_coder p = (p, encode_num, decode_num p)
End

Theorem wf_coder_num:
     !p. wf_pred p ==> wf_coder (num_coder p)
Proof
   RW_TAC std_ss [num_coder_def, wf_encode_num, decode_num_def, wf_coder_def]
QED

(*---------------------------------------------------------------------------
     Bounded numbers
 ---------------------------------------------------------------------------*)

Definition bnum_coder_def:
   bnum_coder m p = (p, encode_bnum m, decode_bnum m p)
End

Theorem wf_coder_bnum:
     !m p. wf_pred_bnum m p ==> wf_coder (bnum_coder m p)
Proof
   RW_TAC std_ss [bnum_coder_def, wf_encode_bnum, decode_bnum_def, wf_coder_def]
   >> FULL_SIMP_TAC std_ss [wf_pred_bnum_def]
   >> PROVE_TAC []
QED

(*---------------------------------------------------------------------------
     Trees
 ---------------------------------------------------------------------------*)

Definition tree_coder_def:
   tree_coder (p, e, d) =
   (lift_tree p, encode_tree e, decode_tree (lift_tree p) d)
End

Theorem wf_coder_tree:
     !c. wf_coder c ==> wf_coder (tree_coder c)
Proof
   REPEAT GEN_TAC
   >> Know `?p e d. c = (p, e, d)` >- PROVE_TAC [pairTheory.ABS_PAIR_THM]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [decode_tree_def, tree_coder_def]
   >> MATCH_MP_TAC wf_coder_op
   >> FULL_SIMP_TAC std_ss [wf_coder_def, wf_encode_tree, wf_pred_def]
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `Node x []` >> RW_TAC std_ss [lift_tree_def, EVERY_DEF])
   >> HO_MATCH_MP_TAC tree_ind
   >> RW_TAC std_ss [encode_tree_def,lift_tree_def,dec2enc_enc2dec,APPEND_11]
   >> Induct_on `ts`
   >> RW_TAC std_ss [encode_list_def, EVERY_DEF, dec2enc_enc2dec, MEM]
QED

