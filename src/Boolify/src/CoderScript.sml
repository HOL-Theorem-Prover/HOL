(*===========================================================================*)
(* Showing Encoding and Decoding to be inverse operations.                   *)
(*===========================================================================*)

(* Interactive mode
app load ["rich_listTheory", "EncodeTheory", "normalForms"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools
     arithmeticTheory listTheory rich_listTheory EncodeTheory
     mesonLib optionTheory normalForms combinTheory;

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
     decode turns a decoding parser of type
       bool list -> ('a # bool list) option
     into a straight function of type
       bool list -> 'a

     domain parser identifies the set of bool lists where it is valid
     to apply decode parser (i.e., any bool list l such that parser l
     results in a successful parse with no bools remaining: SOME (t, []))
 ---------------------------------------------------------------------------*)

val decode_def = Define `decode f = FST o THE o f`;

local
  val th =prove
  (``?d. !f x. x IN d f = ?y. f x = SOME (y, [])``,
   Q.EXISTS_TAC `\f x. ?y. f x = SOME (y, [])` ++
   SIMP_TAC bool_ss [IN_DEF]);
in
  val domain_def =
    Definition.new_specification ("domain_def", ["domain"], th);
  val _ = add_const "domain";
end;

(*---------------------------------------------------------------------------
     Well-formed decoders.
 ---------------------------------------------------------------------------*)

val wf_pdecoder_def = Define
  `wf_pdecoder p (d : bool list -> ('a # bool list) option) =
   !x.
     if x IN p then (?a. !b c. (d b = SOME (x, c)) = (b = APPEND a c))
     else !a b. ~(d a = SOME (x, b))`;

(*---------------------------------------------------------------------------
     Functions to transform well-formed encoders to well-formed decoders,
     and vice versa.
 ---------------------------------------------------------------------------*)

val enc2dec_def = Define
  `enc2dec p e (l : bool list) =
   if ?x t. (x : 'a) IN p /\ (l = APPEND (e x) t)
   then SOME (@(x, t). x IN p /\ (l = APPEND (e x) t))
   else NONE`;

val dec2enc_def = Define
  `dec2enc (d : bool list -> ('a # bool list) option) x =
   @l. d l = SOME (x, [])`;

(*---------------------------------------------------------------------------
     Proofs that the transformation functions are mutually inverse.
 ---------------------------------------------------------------------------*)

val enc2dec_none = store_thm
  ("enc2dec_none",
   ``!p e l.
       (enc2dec p e l = NONE) = (!x t. x IN p ==> ~(l = APPEND (e x) t))``,
   RW_TAC std_ss [enc2dec_def] ++
   PROVE_TAC []);

val enc2dec_some = store_thm
  ("enc2dec_some",
   ``!p e l x t.
       wf_pencoder p e ==>
       ((enc2dec p e l = SOME (x, t)) = x IN p /\ (l = APPEND (e x) t))``,
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
   FULL_SIMP_TAC std_ss [wf_pencoder_def, RES_FORALL_DEF] ++
   PROVE_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND2, IS_PREFIX_REFL]);

val wf_enc2dec = store_thm
  ("wf_enc2dec",
   ``!p e. wf_pencoder p e ==> wf_pdecoder p (enc2dec p e)``,
   RW_TAC std_ss [wf_pdecoder_def, enc2dec_some, RES_FORALL_DEF] ++
   PROVE_TAC [APPEND_NIL]);

val dec2enc_some = store_thm
  ("dec2enc_some",
   ``!p d x l.
       wf_pdecoder p d ==>
       ((dec2enc d x = l) /\ x IN p = (d l = SOME (x, [])))``,
   RW_TAC std_ss [dec2enc_def] ++
   SELECT_TAC ++
   RW_TAC std_ss [] ++
   EQ_TAC >>
   (RW_TAC std_ss [] ++
    Q.PAT_ASSUM `X ==> Y` MATCH_MP_TAC ++
    FULL_SIMP_TAC std_ss [wf_pdecoder_def, RES_FORALL_DEF] ++
    PROVE_TAC [APPEND_NIL]) ++
   POP_ASSUM MP_TAC ++
   MATCH_MP_TAC
   (PROVE [] ``(z ==> x) /\ (y ==> z ==> t) ==> (x ==> y) ==> z ==> t``) ++
   CONJ_TAC >> PROVE_TAC [] ++
   POP_ASSUM MP_TAC ++
   SIMP_TAC std_ss [wf_pdecoder_def] ++
   DISCH_THEN (MP_TAC o Q.SPEC `x`) ++
   REVERSE (Cases_on `x IN p`) >> PROVE_TAC [] ++
   ASM_REWRITE_TAC [] ++
   DISCH_THEN (CHOOSE_THEN MP_TAC) ++
   RW_TAC std_ss []);

val decode_dec2enc = store_thm
  ("decode_dec2enc",
   ``!p d x.
       wf_pdecoder p d /\ x IN p ==> (d (dec2enc d x) = SOME (x, []))``,
   PROVE_TAC [dec2enc_some]);

val decode_dec2enc_append = store_thm
  ("decode_dec2enc_append",
   ``!p d x t.
       wf_pdecoder p d /\ x IN p ==>
       (d (APPEND (dec2enc d x) t) = SOME (x, t))``,
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`p`, `d`, `x`] decode_dec2enc) ++
   RW_TAC std_ss [] ++
   FULL_SIMP_TAC std_ss [wf_pdecoder_def] ++
   Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`) ++
   RW_TAC std_ss [] ++
   RW_TAC std_ss [] ++
   RES_TAC ++
   RW_TAC std_ss [APPEND_NIL]);

val wf_dec2enc = store_thm
  ("wf_dec2enc",
   ``!p d. wf_pdecoder p d ==> wf_pencoder p (dec2enc d)``,
   RW_TAC std_ss [wf_pencoder_def, RES_FORALL_DEF] ++
   MP_TAC (Q.SPECL [`p`, `d`] wf_pdecoder_def) ++
   ASM_REWRITE_TAC [] ++
   DISCH_THEN (fn th => MP_TAC (Q.SPEC `x` th) THEN MP_TAC (Q.SPEC `x'` th)) ++
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`p`, `d`, `x`] decode_dec2enc) ++
   MP_TAC (Q.SPECL [`p`, `d`, `x'`] decode_dec2enc) ++
   RW_TAC std_ss [APPEND_NIL] ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM MP_TAC ++
   POP_ASSUM (CHOOSE_THEN MP_TAC o REWRITE_RULE [IS_PREFIX_APPEND]) ++
   RW_TAC std_ss [GSYM APPEND_ASSOC] ++
   POP_ASSUM (MP_TAC o Q.SPECL [`APPEND (dec2enc d x') l`, `[]`]) ++
   POP_ASSUM (MP_TAC o Q.SPECL [`APPEND (dec2enc d x') l`, `l`]) ++
   RW_TAC std_ss [APPEND_NIL]);

val dec2enc_enc2dec = store_thm
  ("dec2enc_enc2dec",
   ``!p e x. wf_pencoder p e /\ x IN p ==> (dec2enc (enc2dec p e) x = e x)``,
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`p`, `e`] wf_enc2dec) ++
   RW_TAC std_ss [dec2enc_some] ++
   MP_TAC (Q.SPECL [`p`, `enc2dec p e`, `x`, `e x`] dec2enc_some) ++
   RW_TAC std_ss [enc2dec_some, APPEND_NIL]);

val enc2dec_dec2enc = store_thm
  ("enc2dec_dec2enc",
   ``!p d. wf_pdecoder p d ==> (enc2dec p (dec2enc d) = d)``,
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
    RW_TAC std_ss [] >> PROVE_TAC [wf_pdecoder_def] ++
    MP_TAC (Q.SPECL [`p`, `d`] wf_pdecoder_def) ++
    ASM_REWRITE_TAC [] ++
    DISCH_THEN (MP_TAC o Q.SPEC `q`) ++
    RW_TAC std_ss [] ++
    RES_TAC ++
    RW_TAC std_ss [APPEND_11] ++
    Suff `d a = SOME (q, [])` >> PROVE_TAC [dec2enc_some] ++
    RW_TAC std_ss [APPEND_NIL]]);

val decode_encode = store_thm
  ("decode_encode",
   ``!p e x. wf_pencoder p e /\ x IN p ==> (decode (enc2dec p e) (e x) = x)``,
   RW_TAC std_ss [] ++
   Cases_on `enc2dec p e (e x)` >>
   (POP_ASSUM MP_TAC ++
    RW_TAC std_ss [enc2dec_none] ++
    PROVE_TAC [APPEND_NIL]) ++
   POP_ASSUM MP_TAC ++
   Cases_on `x'` ++
   SIMP_TAC std_ss [decode_def, o_THM] ++
   RW_TAC std_ss [enc2dec_some] ++
   MP_TAC (Q.SPECL [`p`, `e`] wf_pencoder_def) ++
   RW_TAC std_ss [RES_FORALL_DEF] ++
   Suff `IS_PREFIX (e x) (e q)` >> PROVE_TAC [] ++
   PROVE_TAC [IS_PREFIX_APPEND]);

val encode_decode = store_thm
  ("encode_decode",
   ``!p e l.
       wf_pencoder p e /\ l IN domain (enc2dec p e) ==>
       (e (decode (enc2dec p e) l) = l)``,
   RW_TAC std_ss [domain_def, decode_def, o_THM] ++
   RW_TAC std_ss [] ++
   POP_ASSUM MP_TAC ++
   RW_TAC std_ss [enc2dec_some, APPEND_NIL]);

(* obsolete?
val enc2dec_11 = store_thm
  ("enc2dec_11",
  ``!e f.
       wf_encoder e /\ wf_encoder f /\ (enc2dec e = enc2dec f) ==> (e = f)``,
   RW_TAC std_ss [] ++
   MATCH_MP_TAC EQ_EXT ++
   RW_TAC std_ss [] ++
   MP_TAC (Q.SPECL [`e`, `e x`, `x`, `[]`] enc2dec_some) ++
   RW_TAC std_ss [APPEND_NIL] ++
   MP_TAC (Q.SPECL [`f`, `e x`, `x`, `[]`] enc2dec_some) ++
   RW_TAC std_ss [APPEND_NIL]);
*)

(*---------------------------------------------------------------------------
     We define decoders in terms of encoders.
 ---------------------------------------------------------------------------*)

val decode_bool_def = Define `decode_bool = enc2dec tot encode_bool`;

val decode_list_def = Define
  `decode_list d = enc2dec tot (encode_list (dec2enc d))`;

(*---------------------------------------------------------------------------
     decoders are well-formed and satisfy natural recursion equations.
 ---------------------------------------------------------------------------*)

val wf_decode_bool = store_thm
  ("wf_decode_bool",
   ``wf_pdecoder tot decode_bool``,
   RW_TAC std_ss [decode_bool_def, wf_enc2dec, wf_encoder, wf_encode_bool]);

val decode_encode_bool = store_thm
  ("decode_encode_bool",
   ``!x. decode decode_bool (encode_bool x) = x``,
   RW_TAC std_ss
   [decode_encode, decode_bool_def, wf_encoder, wf_encode_bool, tot_def]);

val encode_decode_bool = store_thm
  ("encode_decode_bool",
   ``!l :: domain decode_bool. encode_bool (decode decode_bool l) = l``,
   RW_TAC std_ss
   [RES_FORALL_DEF, encode_decode, decode_bool_def, wf_encoder,
    wf_encode_bool, tot_def]);

val decode_bool = store_thm
  ("decode_bool",
   ``decode_bool l = case l of [] -> NONE || (h :: t) -> SOME (h, t)``,
   REPEAT CASE_TAC ++
   RW_TAC std_ss
   [decode_bool_def, enc2dec_none, enc2dec_some, encode_bool_def,
    APPEND, wf_encode_bool, wf_encoder, tot_def]);

(* in progress
val decode_list = store_thm
  ("decode_list",
   ``(decode_list d l =
      case l of [] -> NONE
      || (T :: t) ->
         (case d t of NONE -> NONE
          || SOME (x, t') ->
             (case decode_list d t' of NONE -> NONE
              || SOME (xs, t'') -> SOME (x :: xs, t'')))
      || (F :: t) -> SOME ([], t))``,
   (REPEAT CASE_TAC ++
    RW_TAC std_ss [decode_list_def, enc2dec_none, tot_def]) <<
   [Cases_on `x` ++
    RW_TAC std_ss [encode_list_def, APPEND],
    Cases_on `x` ++
    RW_TAC std_ss [encode_list_def, APPEND, GSYM APPEND_ASSOC] ++
    STRIP_TAC ++
    RW_TAC std_ss []
    
); 
*)

val _ = export_theory ();
