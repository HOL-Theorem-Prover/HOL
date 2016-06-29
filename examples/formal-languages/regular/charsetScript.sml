open HolKernel Parse boolLib bossLib numLib lcsymtacs;
open arithmeticTheory listTheory optionTheory rich_listTheory
     pairTheory comparisonTheory stringTheory;

 
local open numSyntax Regexp_Type in end;

val _ = new_theory "charset";

(*---------------------------------------------------------------------------*)
(* Charsets are here represented by boolean vectors. Pinched from            *)
(*                                                                           *)
(*    ~/Projects/cakeml/translator/ml_translatorScript.sml                   *)
(*                                                                           *)
(* NB: for code generation, as done in regexpMLScript.sml, the above theory  *)
(* needs to be linked to in this script and the following four definitions   *)
(* commented out. References to ml_translatorTheory in descendant theories   *)
(* may also need to be edited.                                               *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `vector = Vector of 'a list`;
val fromList_def = Define `fromList l = Vector l`;
val sub_def      = Define `sub (Vector l) n = EL n l`;
val length_def   = Define `length (Vector l) = LENGTH l`;

val fromList_Vector = save_thm
("fromList_Vector",
 SIMP_RULE list_ss [GSYM FUN_EQ_THM] fromList_def);

val vector_cases = Q.store_thm
("vector_cases",
 `!v. ?l. v = Vector l`,
 Cases THEN METIS_TAC[]);

val vector_eq = Q.store_thm
("vector_eq",
 `!v1 v2. (v1 = v2) <=> 
    (length v1 = length v2) /\ 
    !i. i < length v1 ==> (sub v1 i = sub v2 i)`,
  Cases 
    >> Cases 
    >> rw [sub_def,length_def]
    >> metis_tac [LIST_EQ]);

val _ = type_abbrev("charset", ``:bool vector``);

(*---------------------------------------------------------------------------*)
(* Alphabet of regexps and DFAs (typically size 128 or 256). Set in          *)
(* Regexp_Type.sml.                                                          *)
(*---------------------------------------------------------------------------*)

val alphabet_size_def = 
 Define 
   `alphabet_size = ^(numSyntax.term_of_int Regexp_Type.alphabet_size)`;

val ALPHABET_def = 
 Define
  `ALPHABET = ^(rhs (concl (EVAL ``GENLIST I alphabet_size``)))`;

val mem_alphabet = Q.store_thm
("mem_alphabet",
 `!c. MEM c ALPHABET ==> c < alphabet_size`,
 rw_tac bool_ss [ALPHABET_def,alphabet_size_def,MEM] >> EVAL_TAC);

val alphabet_mem = Q.store_thm
("alphabet_mem",
 `!c. c < alphabet_size ==> MEM c ALPHABET`,
 simp_tac bool_ss [alphabet_size_def] 
  >> CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL))
  >> rw []);

val mem_alphabet_iff = Q.store_thm
("mem_alphabet_iff",
 `!c. MEM c ALPHABET <=> c < alphabet_size`,
 metis_tac [mem_alphabet,alphabet_mem]);

val ORD_CHR_lem = Q.store_thm
("ORD_CHR_lem",
 `!c. c < alphabet_size ==> (ORD(CHR c) = c)`,
 rw[alphabet_size_def,GSYM ORD_CHR] >> decide_tac);

(*---------------------------------------------------------------------------*)
(* Define tailrec genlist                                                    *)
(*---------------------------------------------------------------------------*)

val genlist_def = 
 Define
  `genlist f n acc = 
    if n = 0n then acc
     else genlist f (n-1) (f (n-1)::acc)`;

(*---------------------------------------------------------------------------*)
(* Define toList for vectors. Also map on vectors.                           *)
(*---------------------------------------------------------------------------*)

val toListAux_def = 
 tDefine
  "toListAux"
  `toListAux V i top = 
     if i<top
     then sub V i :: toListAux V (i+1) top
     else []`
 (WF_REL_TAC `measure \(x,y,z). z-y`)

val toListAux_ind = fetch "-" "toListAux_ind";

val toList_def = 
 Define
  `toList V = toListAux V 0 (length V)`;

val toListAux_append = Q.store_thm
("toListAux_append",
  `!V i top l1 l2. 
      (V = Vector (l1++l2)) /\ (i = LENGTH l1) /\ (top = LENGTH (l1++l2))
   ==>
     (toListAux V i top = l2)`,
recInduct toListAux_ind THEN 
 RW_TAC list_ss [] THEN 
 RW_TAC list_ss [Once toListAux_def] THEN
 Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] 
 THEN RW_TAC list_ss [] THENL
 [POP_ASSUM (K ALL_TAC) THEN 
   `LENGTH l1 <= LENGTH l1` by DECIDE_TAC THEN 
   RW_TAC list_ss [sub_def,rich_listTheory.EL_APPEND2],
  POP_ASSUM (MP_TAC o Q.SPECL [`l1++[h]`,`t`]) THEN 
  ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN 
  RW_TAC bool_ss [APPEND] THEN
  FULL_SIMP_TAC list_ss [] THEN 
  METIS_TAC [DECIDE ``X + SUC Y = X + (Y + 1)``]]);

val toList_Vector = Q.store_thm
("toList_Vector",
 `!list. toList(Vector list) = list`,
 RW_TAC list_ss [toList_def] THEN 
 MATCH_MP_TAC toListAux_append THEN 
 Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [] THEN 
 Induct_on `list` THEN RW_TAC list_ss [length_def]);

val toList_fromList = Q.store_thm
("toList_fromList",
 `!list. toList(fromList list) = list`,
 METIS_TAC [toList_Vector,fromList_def]);

(*---------------------------------------------------------------------------*)
(* compare vector slices.                                                    *)
(*---------------------------------------------------------------------------*)

val vector_slice_cmp_def = 
 tDefine
  "vector_slice_cmp"
  `vector_slice_cmp cmp v1 v2 i top = 
    if i >= top
     then Equal 
     else case cmp (sub v1 i) (sub v2 i)
           of Equal => vector_slice_cmp cmp v1 v2 (i+1) top
            | result => result`
 (WF_REL_TAC `measure \(u,w,x,y,z). z-y`);

val vector_slice_cmp_ind = fetch "-" "vector_slice_cmp_ind";

(*---------------------------------------------------------------------------*)
(* Character sets.                                                           *)
(*---------------------------------------------------------------------------*)

val all_unset_def = 
 Define
   `all_unset = ^(rhs (concl (EVAL ``GENLIST (K F) alphabet_size``)))`;

val all_set_def = 
 Define
   `all_set = ^(rhs (concl (EVAL ``GENLIST (K T) alphabet_size``)))`;

val charset_empty_def = 
 Define 
   `charset_empty:charset = Vector all_unset`;

val charset_full_def = 
 Define 
   `charset_full:charset = Vector all_set`;

val charset_mem_def = 
 Define 
  `charset_mem n cs = (n < alphabet_size /\ sub cs n)`;

val charset_sing_def = 
 Define 
  `charset_sing n:charset = Vector(genlist (\i. i=n) alphabet_size [])`;

val charset_union_def = 
 Define 
  `charset_union cs1 cs2 = 
    if cs1 = cs2 then cs1 else 
    if cs1 = charset_empty then cs2 else
    if cs2 = charset_empty then cs1 
    else Vector (genlist (\i. sub cs1 i \/ sub cs2 i) alphabet_size [])`;

val charset_insert_def =
 Define 
  `charset_insert ch cset = 
     if charset_mem ch cset then cset
     else charset_union (charset_sing ch) cset`;

val vector_cmp_def = 
 Define
   `vector_cmp cmp v1 v2 = 
     let len = length v1
     in case num_cmp len (length v2) 
         of Less => Less
          | Greater => Greater
          | Equal => vector_slice_cmp cmp v1 v2 0 len`;

val charset_cmp_def = 
 Define
  `charset_cmp (cs1:charset) cs2 = 
    if cs1 = cs2 then Equal
    else vector_cmp bool_cmp cs1 cs2`;


(*---------------------------------------------------------------------------*)
(* Charset theorems                                                          *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* genlist lemmas   (see also listTheory)                                    *)
(*---------------------------------------------------------------------------*)

val genlist_thm = Q.prove
(`(genlist f 0 acc = acc) /\
  (genlist f (SUC n) acc = genlist f n (f n :: acc))`,
  METIS_TAC [genlist_def, numTheory.NOT_SUC,SUC_SUB1]);

val genlist_append = Q.prove
(`!f n l1 l2. genlist f n l1 ++ l2 = genlist f n (l1++l2)`,
 Induct_on `n` >> RW_TAC list_ss [genlist_thm]);

val el_genlist = Q.prove
(`!n list i f. 
    i < n + LENGTH list ==> 
   (EL i (genlist f n list) = 
       if i < n then f i 
       else EL (i-n) list)`,
Induct_on `n` 
 >> RW_TAC list_ss [genlist_thm] 
    >- full_simp_tac arith_ss []
    >- (`i = n` by decide_tac >> RW_TAC list_ss [EL])
    >- (`i - n = SUC (i - SUC n)` by decide_tac 
         >> POP_ASSUM SUBST_ALL_TAC
         >> METIS_TAC [EL,TL]));

val el_genlist_thm = Q.prove
(`!i f. i < alphabet_size ==> (EL i (genlist f alphabet_size []) =  f i)`,
 rw [] >>
 mp_tac (Q.SPECL [`alphabet_size`, `[]`, `i`, `f`] el_genlist) >>
 rw_tac list_ss []);

val length_genlist = Q.prove
(`!f n list. LENGTH (genlist f n list) = n + LENGTH list`,
Induct_on `n` >> RW_TAC list_ss [genlist_thm]);

val length_genlist_thm = Q.prove
(`!f n. LENGTH (genlist f n []) = n`,
 rw_tac list_ss [length_genlist]);

val charset_mem_genlist = Q.prove
(`!c f. c < alphabet_size ==> 
       (charset_mem c (Vector(genlist f alphabet_size [])) <=> f c)`,
 REPEAT STRIP_TAC
  >> rw [charset_mem_def,length_def,sub_def,length_genlist_thm]
  >> metis_tac[el_genlist_thm])

val no_els = Q.prove
(`!list n. 0 < LENGTH list /\ n < LENGTH list /\ EVERY ($= F) list ==> ~EL n list`,
 Induct THEN RW_TAC list_ss [] THEN 
 Cases_on `n` THEN RW_TAC list_ss []);

val charset_mem_empty = Q.store_thm 
("charset_mem_empty",
 `!c. ~charset_mem c charset_empty`,
  simp_tac list_ss [charset_mem_def,charset_empty_def,
                    sub_def,all_unset_def,length_def, alphabet_size_def]
  >> simp_tac bool_ss [GSYM IMP_DISJ_THM]
  >> CONV_TAC (REPEATC (BOUNDED_FORALL_CONV EVAL)) >> metis_tac []);

val charset_mem_full = Q.store_thm 
("charset_mem_full",
 `!c. c < alphabet_size ==> charset_mem c charset_full`,
  SIMP_TAC list_ss [charset_mem_def,charset_full_def,
                    sub_def,all_set_def,length_def, alphabet_size_def]
  >> CONV_TAC (REPEATC (BOUNDED_FORALL_CONV EVAL)) >> metis_tac []);

val charset_mem_sing = Q.store_thm 
("charset_mem_sing",
 `!c1. c1 < alphabet_size ==> 
  !c2. c2 < alphabet_size ==> 
       (charset_mem c1 (charset_sing c2) ⇔ (c1 = c2))`,
 SIMP_TAC list_ss [charset_mem_def, charset_sing_def,alphabet_size_def,sub_def] >>
 CONV_TAC (REPEATC (BOUNDED_FORALL_CONV (EVAL THENC REWRITE_CONV[]))) THEN
 METIS_TAC[]);

val charset_sing_empty = Q.store_thm
("charset_sing_empty",
 `!c. (charset_sing c = charset_empty) <=> ~(c < alphabet_size)`,
 simp_tac list_ss [charset_sing_def,vector_eq,length_genlist_thm,length_def]
  >> `length charset_empty = alphabet_size` by EVAL_TAC
  >> rw [sub_def,el_genlist_thm,EQ_IMP_THM]
  >> fs[]
  >> metis_tac [charset_mem_empty,charset_mem_def]);

val charset_sing_not_empty = Q.store_thm 
("charset_sing_not_empty",
 `!c. c < alphabet_size ==> (charset_sing c ≠ charset_empty)`,
 rw [charset_sing_empty])

val charset_mem_union = Q.store_thm 
("charset_mem_union",
 `!c cs1 cs2.
   charset_mem c (charset_union cs1 cs2) ⇔ charset_mem c cs1 ∨ charset_mem c cs2`, 
 gen_tac >> ntac 2 Cases
  >> rw [charset_union_def,charset_mem_empty] 
  >> rw [charset_mem_def, sub_def,length_def,length_genlist_thm]
  >> rw [EQ_IMP_THM]
  >> MP_TAC (INST_TYPE [alpha |-> bool] el_genlist_thm)
  >> rw[]
  >> res_tac
  >> metis_tac[]);

(*---------------------------------------------------------------------------*)
(* Vector slice comparison                                                   *)
(*---------------------------------------------------------------------------*)

val vector_slice_cmp_eq = Q.prove
(`!cmp v1 v2 bot top. 
    top <= length v1 /\
    (length v1 = length v2) /\
    (!x y. (cmp x y = Equal) <=> (x=y))
    ==>
    ((vector_slice_cmp cmp v1 v2 bot top = Equal) 
     <=> 
    (!i. bot <= i /\ i < top ==> (sub v1 i = sub v2 i)))`,
recInduct vector_slice_cmp_ind 
  >> REPEAT STRIP_TAC
  >> RW_TAC list_ss [Once vector_slice_cmp_def]
  >> CASE_TAC >> fs[] >> rw[]
  >- (qexists_tac `i` >> rw[] >> metis_tac[totoTheory.cpn_distinct])
  >- (rev_full_simp_tac list_ss [] 
        >> `i < top` by decide_tac
        >> rw [EQ_IMP_THM]
        >> `(i=i') \/ i < i'` by decide_tac 
        >> rw[] )
   >- (qexists_tac `i` >> rw[] >> metis_tac[totoTheory.cpn_distinct]));

val charset_cmp_eq = Q.store_thm 
("charset_cmp_eq",
 `!cs1 cs2. (charset_cmp cs1 cs2 = Equal) <=> (cs1 = cs2)`,
 rw_tac std_ss [charset_cmp_def,vector_eq,vector_cmp_def,LET_THM,num_cmp_def]
  >> fs[]
  >> mp_tac (Q.SPECL [`bool_cmp`,`cs1`, `cs2`, `0n`,`length (cs2:bool vector)`] 
                    (INST_TYPE [alpha |-> bool] vector_slice_cmp_eq))
  >> rw[] >> metis_tac[]);

val vector_slice_cmp_less = Q.prove
(`!cmp v1 v2 bot top. 
    top <= length v1 /\ (length v1 = length v2) /\ good_cmp cmp
    ==>
    ((vector_slice_cmp cmp v1 v2 bot top = Less) 
     <=> 
    (?i. bot <= i /\ i < top /\ (cmp (sub v1 i) (sub v2 i) = Less)
         /\ !j. bot <= j /\ j < i ==> (cmp (sub v1 j) (sub v2 j) = Equal)))`,
recInduct vector_slice_cmp_ind 
  >> REPEAT STRIP_TAC
  >> RW_TAC list_ss [Once vector_slice_cmp_def]
  >> full_simp_tac list_ss [GSYM IMP_DISJ_THM]
  >> rw[]
  >> CASE_TAC 
  >> fs[] >> rw[]
  >- (qexists_tac `i` >> rw[])
  >- (rw [EQ_IMP_THM] 
       >- (qexists_tac `i'` >> rw[] 
           >- (`(i = j) \/ i < j` by decide_tac 
                >| [rw [], first_assum match_mp_tac >> decide_tac]))
       >- (`(i = i') \/ i < i'` by decide_tac 
            >- (rw [] >> metis_tac [good_cmp_thm,comparison_distinct])
            >- (qexists_tac `i'` >> rw[] 
                 >| [decide_tac,first_assum match_mp_tac >> decide_tac])))
  >- (full_simp_tac list_ss [GSYM IMP_DISJ_THM] >> rw []
      >> `(i = i') \/ i < i'` by decide_tac 
      >- (metis_tac [good_cmp_thm,comparison_distinct])
      >- (metis_tac [comparison_distinct,LESS_EQ_REFL]))
);

val vector_slice_cmp_greater = Q.prove
(`!cmp v1 v2 bot top. 
    top <= length v1 /\ (length v1 = length v2) /\ good_cmp cmp
    ==>
    ((vector_slice_cmp cmp v1 v2 bot top = Greater) 
     <=> 
    (?i. bot <= i /\ i < top /\ (cmp (sub v1 i) (sub v2 i) = Greater)
         /\ !j. bot <= j /\ j < i ==> (cmp (sub v1 j) (sub v2 j) = Equal)))`,
recInduct vector_slice_cmp_ind 
  >> REPEAT STRIP_TAC
  >> RW_TAC list_ss [Once vector_slice_cmp_def]
  >> full_simp_tac list_ss [GSYM IMP_DISJ_THM]
  >> rw[]
  >> CASE_TAC 
  >> fs[] >> rw[]
  >- (full_simp_tac list_ss [GSYM IMP_DISJ_THM] >> rw []
      >> `(i = i') \/ i < i'` by decide_tac 
      >- (metis_tac [good_cmp_thm,comparison_distinct])
      >- (metis_tac [comparison_distinct,LESS_EQ_REFL])
     )
  >- (rw [EQ_IMP_THM] 
       >- (qexists_tac `i'` >> rw[] 
            >- (`(i = j) \/ i < j` by decide_tac 
                 >| [rw [], first_assum match_mp_tac >> decide_tac]))
       >- (`(i = i') \/ i < i'` by decide_tac 
            >- (rw [] >> metis_tac [good_cmp_thm,comparison_distinct])
            >- (qexists_tac `i'` >> rw[] 
                 >| [decide_tac,first_assum match_mp_tac >> decide_tac]))
     )
  >- (qexists_tac `i` >> rw[])
);


val vector_slice_cmp_strict = Q.prove
(`!cmp v1 v2 bot top. 
    top <= length v1 /\ (length v1 = length v2) /\ good_cmp cmp
    ==>
    ((vector_slice_cmp cmp v1 v2 bot top = Less) 
     <=> 
    (vector_slice_cmp cmp v2 v1 bot top = Greater))`,
 rw [] >> mp_tac (SPEC_ALL vector_slice_cmp_less) >> rw[] >> pop_assum (K all_tac)
       >> mp_tac (Q.ISPECL [`cmp:'a comp`, `v2:'a vector`, 
                            `v1:'a vector`, `bot:num`, `top:num`]
                      vector_slice_cmp_greater)
       >> fs [] >> rw[] >> pop_assum (K ALL_TAC)
       >> rw [EQ_IMP_THM]
       >> (Q.EXISTS_TAC `i` >> rw[] 
           >- metis_tac [good_cmp_thm]
           >- metis_tac [good_cmp_def])
);

val bool_cmp_eq = Q.prove
(`!x y. (bool_cmp x y = Equal) <=> (x=y)`,
 Cases >> Cases >> rw_tac list_ss [bool_cmp_def]);

val charset_cmp_strict = Q.store_thm 
("charset_cmp_strict",
 `!cs1 cs2. (charset_cmp cs1 cs2 = Less) <=> (charset_cmp cs2 cs1 = Greater)`,
 rw_tac std_ss [charset_cmp_def]
  >> ONCE_REWRITE_TAC [vector_cmp_def]
  >> rw_tac list_ss [LET_THM]
  >> every_case_tac >> fs[vector_eq] 
  >> metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
);

val charset_cmp_trans = Q.store_thm 
("charset_cmp_trans",
 `!cs1 cs2 cs3. 
      (charset_cmp cs1 cs2 = Less) /\ 
      (charset_cmp cs2 cs3 = Less)
      ==> 
      (charset_cmp cs1 cs3 = Less)`,
 rw_tac std_ss [charset_cmp_def,vector_cmp_def,LET_THM]
  >> every_case_tac >> fs[] >> rw[]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- (mp_tac (Q.ISPECL [`bool_cmp`, `cs1:bool vector`, 
                        `cs2:bool vector`, `0n`, `length (cs1:bool vector)`]
                      vector_slice_cmp_less)
      >> rw_tac list_ss [bool_cmp_good]
      >> mp_tac (Q.ISPECL [`bool_cmp`, `cs2:bool vector`, 
                        `cs3:bool vector`, `0n`, `length (cs2:bool vector)`]
                      vector_slice_cmp_less)
      >> rw_tac list_ss [bool_cmp_good]
      >> mp_tac (Q.ISPECL [`bool_cmp`, `cs1:bool vector`, 
                          `cs3:bool vector`, `0n`, `length (cs2:bool vector)`]
                      vector_slice_cmp_less)
      >> rw_tac list_ss [bool_cmp_good]
      >> POP_ASSUM (K ALL_TAC)
      >> `i < i' \/ (i=i') \/ i' < i` by DECIDE_TAC
         >- (Q.EXISTS_TAC `i` >> rw[] 
              >- (`sub cs3 i = sub cs2  i` by METIS_TAC [bool_cmp_eq] >> rw[])
              >- metis_tac[LESS_TRANS,bool_cmp_eq])
         >- (rw[] >> NTAC 2 (Q.PAT_ASSUM `bool_cmp a b = Less` MP_TAC)
                 >> Cases_on `sub cs1 i`
                 >> Cases_on `sub cs2 i`
                 >> Cases_on `sub cs3 i`
                 >> rw_tac arith_ss [bool_cmp_def])
         >- (Q.EXISTS_TAC `i'` >> rw[] 
              >- (`sub cs1 i' = sub cs2 i'` by METIS_TAC [bool_cmp_eq] >> rw[])
              >- metis_tac[LESS_TRANS,bool_cmp_eq]))
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
  >- metis_tac [bool_cmp_good,num_cmp_good,good_cmp_thm,
       vector_slice_cmp_strict, comparison_distinct,LESS_EQ_REFL]
);

val _ = export_theory();
