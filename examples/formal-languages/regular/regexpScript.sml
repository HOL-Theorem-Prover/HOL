(*===========================================================================*)
(* Theory of regular expressions.                                            *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib lcsymtacs;
open arithmeticTheory listTheory optionTheory rich_listTheory
     pairTheory relationTheory sortingTheory stringTheory
     comparisonTheory bagTheory containerTheory pred_setTheory
     mergesortTheory charsetTheory FormalLangTheory;


local open numSyntax Regexp_Type wordsLib in end;

(* local open numSyntax Regexp_Type ml_translatorTheory in end; *)

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_case_def = TypeBase.case_def_of ``:ordering``

val _ = new_theory "regexp";

(*---------------------------------------------------------------------------*)
(* TODO: move this support stuff belonging in other theories                 *)
(*---------------------------------------------------------------------------*)

val SET_EQ_THM = Q.prove
(`!s1 s2. (s1 = s2) = !x. s1 x = s2 x`,
 METIS_TAC [EXTENSION,IN_DEF]);

val LENGTH_NIL_SYM =
   GEN_ALL (CONV_RULE (LHS_CONV SYM_CONV) (SPEC_ALL LENGTH_NIL));

val CONS_APPEND_11 = Q.prove
(`!h t list. (h::t = list ++ t) <=> (list = [h])`,
 SIMP_TAC list_ss [EQ_IMP_THM]
  THEN Induct_on `list`
  THEN RW_TAC list_ss [APPEND_EQ_SELF]);

val CONS_APPEND_11_SIMPS = Q.prove
(`(!h t list. (h::t = list ++ t) <=> (list = [h])) /\
  (!h t list. (list ++ t = h::t) <=> (list = [h]))`,
 METIS_TAC [CONS_APPEND_11]);

val list_ss = list_ss ++ rewrites
              [CONS_APPEND_11_SIMPS,APPEND_EQ_SELF,LENGTH_NIL, LENGTH_NIL_SYM];

val set_ss  = list_ss ++ pred_setLib.PRED_SET_ss ++ rewrites [SET_EQ_THM,IN_DEF]

val LIST_UNION_def =
 Define
  `(LIST_UNION [] = {}) /\
   (LIST_UNION (h::t) = h UNION LIST_UNION t)`;

val LIST_UNION_THM = Q.prove
(`(LIST_UNION [] x = F) /\
  (LIST_UNION (h::t) x = (h x \/ LIST_UNION t x))`,
 srw_tac [] [LIST_UNION_def,IN_DEF]);

val ZIP_ind  = Q.store_thm("ZIP_ind",
  `!P.
    (!l. P ([],l)) /\ (!v2 v3. P (v2::v3,[])) /\
     (!x xs y ys. P (xs,ys) ==> P (x::xs,y::ys)) ==>
     !v v1. P (v,v1)`,
  ntac 2 strip_tac
  \\ Induct \\ ASM_REWRITE_TAC[]
  \\ gen_tac \\ Cases \\ ASM_SIMP_TAC bool_ss []);

val MEM_ZIP_IMP = Q.store_thm("MEM_ZIP_IMP",
 `!l1 l2 a b. MEM (a,b) (ZIP (l1,l2)) ==> MEM a l1 /\ MEM b l2`,
 recInduct ZIP_ind THEN RW_TAC list_ss [ZIP_def] THEN METIS_TAC []);

val ZIP_eq_cons = Q.store_thm("ZIP_eq_cons",
 `!l1 l2 a b t.
     (ZIP (l1,l2) = (a,b)::t) ==> ?t1 t2. (l1 = a::t1) /\ (l2 = b::t2)`,
 recInduct ZIP_ind >> RW_TAC list_ss [ZIP_def]);

val cons_eq_ZIP = Q.prove
(`!l1 l2 a b t.
    ((a,b)::t = ZIP (l1,l2)) ==> ?t1 t2. (l1 = a::t1) /\ (l2 = b::t2)`,
 METIS_TAC [ZIP_eq_cons]);

val zip_append = Q.store_thm("zip_append",
 `!l1 l2 l3 l4.
   (LENGTH l1 = LENGTH l2) /\
   (LENGTH l3 = LENGTH l4)
   ==>
    (ZIP (l1 ++ l3, l2 ++ l4) = ZIP (l1,l2) ++ ZIP (l3,l4))`,
 recInduct ZIP_ind >> rw_tac list_ss [ZIP_def]);

val zip_append_id = Q.store_thm("zip_append_id",
 `!l1 l2. ZIP (l1,l1) ++ ZIP (l2,l2) = ZIP (l1 ++ l2, l1 ++ l2)`,
Induct_on `l1` THEN RW_TAC list_ss [ZIP_def] THEN
Induct_on `l2` THEN RW_TAC list_ss [ZIP_def]);

val ZIP_eq_nil = Q.store_thm("ZIP_eq_nil",
 `!l1 l2. (ZIP (l1,l2) = []) <=> ((l1=[]) \/ (l2=[]))`,
 recInduct ZIP_ind THEN RW_TAC list_ss [ZIP_def]);

(*---------------------------------------------------------------------------*)
(* Datatype of extended regular expressions                                  *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype
 `regexp
    = Chset of charset
    | Cat of regexp => regexp
    | Star of regexp
    | Or of regexp list
    | Neg of regexp`;

val regexp_induction = Q.store_thm
("regexp_induction",
 `!P Q.
     (!cs. P (Chset cs)) /\
     (!r r0. P r /\ P r0 ==> P (Cat r r0)) /\
     (!r. P r ==> P (Star r)) /\ (!l. Q l ==> P (Or l)) /\
     (!r. P r ==> P (Neg r)) /\ Q [] /\ (!r l. P r /\ Q l ==> Q (r::l)) ==>
     (!r. P r) /\ !l. Q l`,
 ACCEPT_TAC (fetch"regexp" "regexp_induction"));

val regexp_distinct = fetch "-" "regexp_distinct";

(*---------------------------------------------------------------------------*)
(* "And" on regexps is derived syntax                                        *)
(*---------------------------------------------------------------------------*)

val And_def =
 Define
  `And r s = Neg(Or[Neg r; Neg s])`;

(*---------------------------------------------------------------------------*)
(* Some standard regexps                                                     *)
(*---------------------------------------------------------------------------*)

val Empty_def   = Define `Empty = Chset charset_empty`;
val DOT_def   = Define `DOT = Chset charset_full`;
val Epsilon_def = Define `Epsilon = Star (Chset charset_empty)`;

(*---------------------------------------------------------------------------*)
(* Regexp of a string (currently unused).                                    *)
(*---------------------------------------------------------------------------*)

val catstring_def =
 Define
   `(catstring [] = Epsilon) /\
    (catstring (c::t) = Cat(Chset(charset_sing c)) (catstring t))`;

(*---------------------------------------------------------------------------*)
(* Size of a regular expression. The system-generated regexp_size goes       *)
(* "through" Chset and into its representation, but really the size          *)
(* computation should stop at Chset, as is done in rsize_def.                *)
(*---------------------------------------------------------------------------*)

val rsize_def =
  Define
   `(rsize (Chset a) = 1n) /\
    (rsize (Cat r s) = 1 + (rsize r + rsize s)) /\
    (rsize (Star a)  = 1 + rsize a) /\
    (rsize (Or a)    = 1 + rsizel a) /\
    (rsize (Neg a)   = 1 + rsize a)
    /\
    (rsizel []       = 0n) /\
    (rsizel (r::t)   = 1 + (rsize r + rsizel t))`;

val rsize_or_lem = Q.store_thm
("rsize_or_lem",
 `!l a. MEM a l ==> rsize a < rsize (Or l)`,
 SIMP_TAC list_ss [rsize_def] THEN
 Induct THEN RW_TAC list_ss [rsize_def] THENL
 [DECIDE_TAC, RES_TAC THEN POP_ASSUM MP_TAC THEN DECIDE_TAC]);

val rsizel_append = Q.store_thm
("rsizel_append",
 `!l1 l2. rsizel (l1 ++ l2) = rsizel (l1) + rsizel (l2)`,
 Induct THEN RW_TAC list_ss [rsize_def]);

(*---------------------------------------------------------------------------*)
(* If we were going to translate rsize_def, it would currently fail. The     *)
(* following would work. In fact, however, we only use regexp size defns to  *)
(* show termination of other functions, so it need not be translated.        *)
(*---------------------------------------------------------------------------*)

val regexp_list_size_def =
  tDefine
   "regexp_list_size"
   `(regexp_list_size [] (acc:num)     = acc) /\
    (regexp_list_size (Chset _::t) acc = regexp_list_size t (acc+1)) /\
    (regexp_list_size (Star r::t) acc  = regexp_list_size (r::t) (acc+1)) /\
    (regexp_list_size (Neg r::t) acc   = regexp_list_size (r::t) (acc+1)) /\
    (regexp_list_size (Cat r s::t) acc = regexp_list_size (r::s::t) (acc+1)) /\
    (regexp_list_size (Or rl::t) acc = regexp_list_size (rl ++ t) (acc + LENGTH rl + 1))`
(WF_REL_TAC `inv_image (mlt_list (measure rsize)) FST` THEN RW_TAC list_ss []
 THENL
  [METIS_TAC [rsize_or_lem],
   `r::s::t = [r;s] ++ t` by METIS_TAC [APPEND]
     THEN RW_TAC arith_ss [rsize_def,APPEND_11,MEM] THEN DECIDE_TAC,
   RW_TAC list_ss [rsize_def],
   RW_TAC list_ss [rsize_def]]);

(*---------------------------------------------------------------------------*)
(* Language of a regexp                                                      *)
(*---------------------------------------------------------------------------*)

val regexp_lang_def =
 tDefine
  "regexp_lang"
  `(regexp_lang (Chset ns) = {w:string | ?c. charset_mem c ns /\ (w = [CHR c])}) /\
   (regexp_lang (Cat r s)  = (regexp_lang r dot regexp_lang s)) /\
   (regexp_lang (Star r)   = KSTAR (regexp_lang r)) /\
   (regexp_lang (Neg r)    = COMPL (regexp_lang r)) /\
   (regexp_lang (Or rlist) = LIST_UNION (MAP regexp_lang rlist))`
(WF_REL_TAC `measure rsize`
  >> srw_tac [ARITH_ss] [rsize_or_lem]
  >> rw [rsize_def]
  >> decide_tac);

val regexp_lang_thm = Q.store_thm
("regexp_lang_thm",
  `(regexp_lang (Chset ns) w = ?c. charset_mem c ns /\ (w = [CHR c])) /\
   (regexp_lang (Cat r s) w  = ?w1 w2. regexp_lang r w1 /\
                                       regexp_lang s w2 /\ (w = w1++w2)) /\
   (regexp_lang (Star r) w   = ?ws. EVERY (regexp_lang r) ws /\ (w = FLAT ws)) /\
   (regexp_lang (Neg r) w    = ~regexp_lang r w) /\
   (regexp_lang (Or rlist) w = EXISTS (\r. regexp_lang r w) rlist)`,
 RW_TAC set_ss [regexp_lang_def,SET_EQ_THM] THENL
 [RW_TAC set_ss [SIMP_RULE std_ss [IN_DEF] IN_dot] THEN METIS_TAC[],
  RW_TAC set_ss [SIMP_RULE std_ss [IN_DEF] IN_KSTAR_LIST] THEN METIS_TAC[],
  Induct_on `rlist` THEN RW_TAC set_ss [LIST_UNION_THM]]);

val regexp_lang_epsilon = Q.store_thm
("regexp_lang_epsilon",
 `regexp_lang Epsilon = {""}`,
 rw [regexp_lang_def,Epsilon_def,charset_mem_empty,KSTAR_EMPTYSET,SET_EQ_THM]);

val regexp_lang_empty = Q.store_thm
("regexp_lang_empty",
 `regexp_lang Empty = EMPTY`,
 rw [regexp_lang_def,Empty_def,charset_mem_empty]);

val regexp_lang_epsilon_thm = Q.store_thm
("regexp_lang_epsilon_thm",
 `!s. regexp_lang Epsilon s <=> (s = "")`,
 rw [regexp_lang_epsilon,SET_EQ_THM]);

val regexp_lang_empty_thm = Q.store_thm
("regexp_lang_empty_thm",
 `!s. regexp_lang Empty s <=> F`,
 METIS_TAC [regexp_lang_empty,EMPTY_DEF]);

val regexp_lang_dot = Q.store_thm
("regexp_lang_dot",
 `regexp_lang DOT = \w. ?c. w = [c]`,
rw_tac set_ss [DOT_def, regexp_lang_def, EXTENSION, EQ_IMP_THM]
 >> Cases_on `c`
 >> qexists_tac `n`
 >> pop_assum mp_tac
 >> Q.ID_SPEC_TAC `n`
 >> REPEAT (CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL))
 >> rw_tac bool_ss []);

val regexp_lang_dot_star = Q.store_thm
("regexp_lang_dot_star",
 `regexp_lang (Star DOT) = \w. T`,
rw_tac set_ss [regexp_lang_def, regexp_lang_dot]
 >> Induct_on `w`
  >- metis_tac [IN_DEF,IN_KSTAR_THM]
  >- (rw_tac set_ss [Once (SIMP_RULE bool_ss [IN_DEF] IN_KSTAR_THM)]
      >> qexists_tac `[h]`
      >> qexists_tac `w`
      >> rw_tac set_ss []));

val union_compl = Q.prove
(`!s. s UNION COMPL s = UNIV`,
 rw_tac set_ss [EXTENSION]);

val regexp_lang_invol = Q.store_thm
("regexp_lang_invol",
 `!r. regexp_lang (Or [r ; Neg r]) = \w. T`,
rw_tac set_ss [regexp_lang_def]
 >> EVAL_TAC
 >> rw_tac set_ss [union_compl]);

val regexp_lang_invol_dot_star = Q.store_thm
("regexp_lang_invol_dot_star",
 `!r. regexp_lang (Or [r ; Neg r]) = regexp_lang (Star DOT)`,
 rw_tac bool_ss [regexp_lang_invol, GSYM regexp_lang_dot_star]);

val regexp_lang_dot_star_negempty = Q.store_thm
("regexp_lang_dot_star_negempty",
 `regexp_lang (Star DOT) = regexp_lang (Neg Empty)`,
 rw_tac set_ss [regexp_lang_dot_star,Empty_def]
  >> rw_tac set_ss [regexp_lang_def]
  >> metis_tac [charset_mem_empty]);

(*---------------------------------------------------------------------------*)
(* Compare lists by length. Used to speed up comparisons of Or regexps.      *)
(*---------------------------------------------------------------------------*)

val len_cmp_def =
 Define
  `(len_cmp [] [] = Equal) /\
   (len_cmp [] (_::_) = Less) /\
   (len_cmp (_::_) [] = Greater) /\
   (len_cmp (_::t1) (_::t2) = len_cmp t1 t2)`;

val len_cmp_ind = fetch "regexp" "len_cmp_ind";

val len_cmp_sym = Q.prove
(`!l1 l2. (len_cmp l1 l2 = Equal) <=> (len_cmp l2 l1 = Equal)`,
 recInduct len_cmp_ind >> rw[len_cmp_def]);

val len_cmp_thm = Q.prove
(`!l1 l2. len_cmp l1 l2 =
           if (LENGTH l1 = LENGTH l2) then Equal else
           if (LENGTH l1 < LENGTH l2) then Less else Greater`,
 recInduct len_cmp_ind >> rw[len_cmp_def]);

val len_cmp_neq = Q.prove
(`!l1 l2. (len_cmp l1 l2 <> Equal) ==> (l1 <> l2)`,
 recInduct len_cmp_ind >> rw[len_cmp_def]);

val len_cmp_length = Q.prove
(`!l1 l2.
    ((len_cmp l1 l2 = Equal) ==> (LENGTH l1 = LENGTH l2)) /\
    ((len_cmp l1 l2 = Less) ==> (LENGTH l1 < LENGTH l2)) /\
    ((len_cmp l1 l2 = Greater) ==> (LENGTH l2 < LENGTH l1))`,
 recInduct len_cmp_ind >> rw[len_cmp_def]);

val len_cmp_strict = Q.prove
(`!l1 l2. (len_cmp l1 l2 = Less) <=> (len_cmp l2 l1 = Greater)`,
 recInduct len_cmp_ind >> rw[len_cmp_def]);

val len_cmp_good_lem0 = Q.prove
(`!l1 l2. (len_cmp l1 l2 = Equal) <=> (len_cmp l2 l1 = Equal)`,
 recInduct len_cmp_ind THEN RW_TAC list_ss [len_cmp_def]);

val len_cmp_good_lem1 = Q.prove
(`!l1 l2. (l1 = l2) ==> (len_cmp l1 l2 = Equal)`,
 recInduct len_cmp_ind THEN RW_TAC list_ss [len_cmp_def]);

val len_cmp_good_lem2 = Q.prove
(`!l1 l2. (len_cmp l1 l2 = Greater) <=> (len_cmp l2 l1 = Less)`,
 recInduct len_cmp_ind THEN RW_TAC list_ss [len_cmp_def]);

val len_cmp_good_lem3 = Q.prove
(`!l1 l2 l3. (len_cmp l1 l2 = Less) /\ (len_cmp l2 l3 = Equal) ==> (len_cmp l1 l3 = Less)`,
 recInduct len_cmp_ind
  >> RW_TAC list_ss [len_cmp_def]
  >> Induct_on `l3`
  >> RW_TAC list_ss [len_cmp_def]);

val len_cmp_good_lem4 = Q.prove
(`!l1 l2 l3. (len_cmp l1 l2 = Less) /\ (len_cmp l2 l3 = Less) ==> (len_cmp l1 l3 = Less)`,
 recInduct len_cmp_ind
  >> RW_TAC list_ss [len_cmp_def]
  >> Induct_on `l3`
  >> RW_TAC list_ss [len_cmp_def]);

val len_cmp_good = Q.prove
(`good_cmp len_cmp`,
RW_TAC list_ss [good_cmp_thm] THEN
METIS_TAC [len_cmp_good_lem1,len_cmp_good_lem2,len_cmp_good_lem3,len_cmp_good_lem4]);

val len_cmp_zip = Q.prove
(`!l1 l2 l3 l4. (len_cmp l1 l2 = Equal) ==>
    (ZIP (l1,l2) ++ ZIP (l3,l4) = ZIP (l1++l3,l2++l4))`,
recInduct ZIP_ind THEN rw_tac list_ss [ZIP_def]
 >- (Cases_on `l` >> full_simp_tac list_ss [ZIP_def,len_cmp_def] >> rw_tac list_ss [])
 >- (full_simp_tac list_ss [ZIP_def,len_cmp_def] >> rw_tac list_ss [])
 >- (full_simp_tac list_ss [len_cmp_def]));


(*---------------------------------------------------------------------------*)
(* Regexp comparison                                                         *)
(*---------------------------------------------------------------------------*)

val regexp_compareW_def =
 tDefine
  "regexp_compareW"
  `(regexp_compareW [] = Equal) /\
   (regexp_compareW (pair::t) =
     case pair of
      | (Chset cs1, Chset cs2) =>
            (case charset_cmp cs1 cs2
              of Equal => regexp_compareW t
               | result => result)
      | (Chset _, __) => Less
      | (Cat _ _, Chset _) => Greater
      | (Cat r1 r2, Cat r3 r4) => regexp_compareW ((r1,r3)::(r2,r4)::t)
      | (Cat _ _, __) => Less
      | (Star _, Chset _) => Greater
      | (Star _, Cat _ _) => Greater
      | (Star r, Star s) => regexp_compareW ((r,s)::t)
      | (Star _, __) => Less
      | (Or _, Chset _) => Greater
      | (Or _, Cat _ _) => Greater
      | (Or _, Star _) => Greater
      | (Or rs1, Or rs2) =>
          (case len_cmp rs1 rs2
            of Equal => regexp_compareW (ZIP (rs1,rs2) ++ t)
             | verdict => verdict)
      | (Or _, __) => Less
      | (Neg r, Neg s) => regexp_compareW ((r,s)::t)
      | (Neg _, __) => Greater)`
(WF_REL_TAC `mlt_list (RPROD (measure rsize) (measure rsize))`
 THEN RW_TAC list_ss [rsize_def]
 THENL
  [METIS_TAC [SIMP_RULE list_ss [rsize_def] rsize_or_lem,MEM_ZIP_IMP],
   METIS_TAC [SIMP_RULE list_ss [rsize_def] rsize_or_lem,MEM_ZIP_IMP],
   Q.EXISTS_TAC `[(r1,r3) ; (r2,r4)]` THEN NTAC 2 (RW_TAC list_ss [rsize_def])
  ]);

val regexp_compare_def =
 Define
  `regexp_compare r s = regexp_compareW [(r,s)]`;

val regexp_leq_def = Define
`regexp_leq r1 r2 <=>
  case regexp_compare r1 r2 of
   | Less => T
   | Equal => T
   | Greater => F`;

val regexp_compareW_ind = fetch "-" "regexp_compareW_ind";

(*---------------------------------------------------------------------------*)
(* Comparison function. Implemented in worklist style, to accomodate cakeML. *)
(*---------------------------------------------------------------------------*)

val regexp_compareW_ind_thm =
  SIMP_RULE list_ss [FORALL_PROD] regexp_compareW_ind;

val regexp_compareW_thm = Q.prove
(`(regexp_compareW [] = Equal) /\
  (regexp_compareW ((Chset cs1, Chset cs2)::t) =
     (case charset_cmp cs1 cs2
       of Equal => regexp_compareW t
        | result => result)) /\
   (regexp_compareW ((Chset cs1,Cat v15 v16)::t) = Less) /\
   (regexp_compareW ((Chset cs1,Star v17)::t) = Less) /\
   (regexp_compareW ((Chset cs1,Or v18)::t) = Less) /\
   (regexp_compareW ((Chset cs1,Neg v19)::t) = Less) /\
   (regexp_compareW ((Cat r1 r2,Chset v26)::t) = Greater) /\
   (regexp_compareW ((Cat r1 r2,Cat r3 r4)::t) = regexp_compareW ((r1,r3)::(r2,r4)::t)) /\
   (regexp_compareW ((Cat r1 r2,Star v29)::t) = Less) /\
   (regexp_compareW ((Cat r1 r2,Or v30)::t) = Less) /\
   (regexp_compareW ((Cat r1 r2,Neg v31)::t) = Less) /\
   (regexp_compareW ((Star r,Chset v38)::t) = Greater) /\
   (regexp_compareW ((Star r,Cat v39 v40)::t) = Greater) /\
   (regexp_compareW ((Star r,Star s)::t) = regexp_compareW ((r,s)::t)) /\
   (regexp_compareW ((Star r,Or v42)::t) = Less) /\
   (regexp_compareW ((Star r,Neg v43)::t) = Less) /\
   (regexp_compareW ((Or rs1,Chset v50)::t) = Greater) /\
   (regexp_compareW ((Or rs1,Cat v51 v52)::t) = Greater) /\
   (regexp_compareW ((Or rs1,Star v53)::t) = Greater) /\
   (regexp_compareW ((Or rs1,Or rs2)::t) =
         (case len_cmp rs1 rs2 of
            Less => Less
          | Equal => regexp_compareW (ZIP (rs1,rs2) ++ t)
          | Greater => Greater)) /\
   (regexp_compareW ((Or rs1,Neg v55)::t) = Less) /\
   (regexp_compareW ((Neg r',Chset v62)::t) = Greater) /\
   (regexp_compareW ((Neg r',Cat v63 v64)::t) = Greater) /\
   (regexp_compareW ((Neg r',Star v65)::t) = Greater) /\
   (regexp_compareW ((Neg r',Or v66)::t) = Greater) /\
   (regexp_compareW ((Neg r',Neg s')::t) = regexp_compareW ((r',s')::t))`,
 REPEAT CONJ_TAC
  >> SIMP_TAC list_ss [SimpLHS, Once regexp_compareW_def]
  >> RW_TAC std_ss [])


val regexp_compareW_eq = Q.store_thm
("regexp_compareW_eq",
 `!plist l1 l2.
    (LENGTH l1 = LENGTH l2) /\ (ZIP (l1,l2) = plist)
    ==>
    ((regexp_compareW plist = Equal) <=> (l1 = l2))`,
 recInduct regexp_compareW_ind_thm
   >> rw[]
   >- (Cases_on `l1` >> Cases_on `l2` >> FULL_SIMP_TAC list_ss [ZIP_def,regexp_compareW_def])
   >- (Cases_on `p_1` >> Cases_on `p_2`
        >> full_simp_tac list_ss [] >> imp_res_tac ZIP_eq_cons
        >> fs [ZIP_def] >> rw_tac list_ss [regexp_compareW_thm]
        >- (every_case_tac >> fs []
            >| [ metis_tac[cpn_distinct,charset_cmp_eq],
                 full_simp_tac list_ss [charset_cmp_eq],
                 metis_tac[cpn_distinct,charset_cmp_eq]])
        >- (Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`r::r0::t1`, `r'::r0'::t2`])
            >> rw_tac list_ss [ZIP_def] >> metis_tac[])
        >- (Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`r::t1`, `r'::t2`])
            >> rw_tac list_ss [ZIP_def] >> metis_tac[])
        >- (CASE_TAC >> fs []
            >| [metis_tac[cpn_distinct,len_cmp_neq],
                imp_res_tac len_cmp_length
                  >> Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`l ++ t1`, `l' ++ t2`])
                  >> RW_TAC list_ss []
                  >> METIS_TAC [APPEND_LENGTH_EQ,zip_append],
                metis_tac[cpn_distinct,len_cmp_neq]])
        >- (Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`r::t1`, `r'::t2`])
            >> rw_tac list_ss [ZIP_def] >> metis_tac[])));

val regexp_compare_eq = Q.store_thm
("regexp_compare_eq",
 `!r s. (regexp_compare r s = Equal) <=> (r = s)`,
 rw_tac list_ss [regexp_compare_def]
  >> mp_tac (Q.SPECL [`[(r,s)]`, `[r]`, `[s]`] regexp_compareW_eq)
  >> rw_tac list_ss [ZIP_def]);

val regexp_compareW_antisym = Q.store_thm
("regexp_compareW_antisym",
  `!plist l1 l2.
    (LENGTH l1 = LENGTH l2) /\ (ZIP (l1,l2) = plist)
     ==>
     ((regexp_compareW plist = Greater) <=> (regexp_compareW (ZIP (l2,l1)) = Less))`,
 recInduct regexp_compareW_ind_thm
   >> rw[]
   >- (Cases_on `l1` >> Cases_on `l2`
         >> FULL_SIMP_TAC list_ss [ZIP_def,regexp_compareW_def]
         >> rw [])
   >- (Cases_on `p_1` >> Cases_on `p_2`
        >> full_simp_tac list_ss [] >> rw []
        >> imp_res_tac ZIP_eq_cons
        >> fs [ZIP_def] >> rw_tac list_ss [regexp_compareW_thm]
        >- (every_case_tac >> fs []
             >> metis_tac [charset_cmp_strict,cpn_distinct])
        >- (Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`r::r0::t1`, `r'::r0'::t2`])
            >> rw_tac list_ss [ZIP_def])
        >- (Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`r::t1`, `r'::t2`])
            >> rw_tac list_ss [ZIP_def])
        >- (CASE_TAC >> fs []
             >- (metis_tac [len_cmp_strict,cpn_case_def, cpn_distinct])
             >- (imp_res_tac len_cmp_length
                  >> fs [Once len_cmp_sym]
                  >> Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`l ++ t1`, `l' ++ t2`])
                  >> RW_TAC list_ss []
                  >> METIS_TAC [APPEND_LENGTH_EQ,zip_append])
             >- (metis_tac [len_cmp_strict,cpn_case_def, cpn_distinct]))
        >- (Q.PAT_X_ASSUM `$!M` (MP_TAC o Q.SPECL [`r::t1`, `r'::t2`])
            >> rw_tac list_ss [ZIP_def]))
);

val regexp_compare_antisym = Q.store_thm
("regexp_compare_antisym",
`!r s. (regexp_compare r s = Greater) <=> (regexp_compare s r = Less)`,
 rw_tac list_ss [regexp_compare_def]
  >> mp_tac (Q.SPECL [`[(r,s)]`, `[r]`, `[s]`] regexp_compareW_antisym)
  >> rw_tac list_ss [ZIP_def]);

val regexp_compareW_trans = Q.store_thm
("regexp_compareW_trans",
 `!plist l1 l2 l3.
   (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) /\
   (plist = ZIP (l1,l2)) /\
   (regexp_compareW plist = Less) /\
   (regexp_compareW (ZIP (l2,l3)) = Less)
    ==>
   (regexp_compareW (ZIP (l1,l3)) = Less)`,
 recInduct regexp_compareW_ind_thm
  >> rw_tac set_ss []
     >- metis_tac [ZIP_eq_nil,regexp_compareW_thm,cpn_distinct]
  >> imp_res_tac cons_eq_ZIP
  >> ntac 2 (pop_assum SUBST_ALL_TAC)
  >> Cases_on `p_1`
  >> Cases_on `p_2`
  >> full_simp_tac list_ss [regexp_distinct, fetch "-" "regexp_11"]
  >> Induct_on `l3`
  >> rw_tac list_ss []
  >> Cases_on `h`
  >> full_simp_tac set_ss [ZIP_def,regexp_compareW_thm]
  >> rw_tac std_ss []
     >- (every_case_tac
          >> rw_tac set_ss []
          >> metis_tac [charset_cmp_eq,charset_cmp_strict,charset_cmp_trans,
                       cpn_distinct])
     >- (qpat_x_assum `$!M`
          (mp_tac o Q.SPECL [`r::r0::t1`, `r'::r0'::t2`, `r''::r0''::l3`])
          >> rw_tac list_ss [ZIP_def])
     >- (qpat_x_assum `$!M`
           (mp_tac o Q.SPECL [`r::t1`, `r'::t2`, `r''::l3`])
           >> rw_tac list_ss [ZIP_def])
     >- (every_case_tac
          >> full_simp_tac list_ss []
          >> rw_tac list_ss []
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct]
             >- (imp_res_tac len_cmp_length
                  >> rw_tac list_ss [Once (GSYM zip_append)]
                  >> first_x_assum match_mp_tac
                  >> qexists_tac `l' ++ t2`
                  >> rw[LENGTH_APPEND]
                     >- full_simp_tac arith_ss []
                     >- full_simp_tac arith_ss [])
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct]
             >- (imp_res_tac len_cmp_length
                  >> rw_tac list_ss [Once (GSYM zip_append)]
                  >> first_x_assum match_mp_tac
                  >> qexists_tac `l' ++ t2`
                  >> rw[LENGTH_APPEND]
                  >> metis_tac[zip_append])
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct]
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct]
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct]
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct])
     >- (qpat_x_assum `$!M`
          (mp_tac o Q.SPECL [`r::t1`, `r'::t2`, `r''::l3`])
          >> rw_tac list_ss [ZIP_def])
);

val regexp_compare_trans = Q.store_thm
("regexp_compare_trans",
 `!r s u. (regexp_compare r s = Less) /\ (regexp_compare s u = Less)
         ==>
         (regexp_compare r u = Less)`,
 rw_tac std_ss [regexp_compare_def]
   >> `[(r,u)] = ZIP ([r],[u])` by rw[ZIP_def]
   >> pop_assum SUBST1_TAC
   >> match_mp_tac regexp_compareW_trans
   >> Q.EXISTS_TAC `[(r,s)]`
   >> Q.EXISTS_TAC `[s]`
   >> rw[ZIP_def]);

val regexp_compareW_trans_eq = Q.store_thm
("regexp_compareW_trans_eq",
 `!plist l1 l2 l3.
   (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) /\
   (plist = ZIP (l1,l2)) /\
   (regexp_compareW plist = Less) /\
   (regexp_compareW (ZIP (l2,l3)) = Equal)
    ==>
   (regexp_compareW (ZIP (l1,l3)) = Less)`,
 recInduct regexp_compareW_ind_thm
  >> rw_tac set_ss []
     >- metis_tac [ZIP_eq_nil,regexp_compareW_thm,cpn_distinct]
  >> imp_res_tac cons_eq_ZIP
  >> ntac 2 (pop_assum SUBST_ALL_TAC)
  >> Cases_on `p_1`
  >> Cases_on `p_2`
  >> full_simp_tac list_ss [regexp_distinct, fetch "-" "regexp_11"]
  >> Induct_on `l3`
  >> rw_tac list_ss []
  >> Cases_on `h`
  >> full_simp_tac set_ss [ZIP_def,regexp_compareW_thm]
  >> rw_tac std_ss []
     >- (every_case_tac >> rw[] >>
          metis_tac [charset_cmp_eq,charset_cmp_strict,cpn_distinct])
     >- (qpat_x_assum `$!M`
           (mp_tac o
               Q.SPECL [`r::r0::t1`, `r'::r0'::t2`, `r''::r0''::l3`])
           >> rw_tac list_ss [ZIP_def])
     >- (qpat_x_assum `$!M` (mp_tac o Q.SPECL [`r::t1`, `r'::t2`, `r''::l3`])
          >> rw_tac list_ss [ZIP_def])
     >- (every_case_tac
          >> full_simp_tac set_ss []
          >> rw_tac set_ss []
             >- (imp_res_tac len_cmp_length >> full_simp_tac arith_ss [])
             >- (imp_res_tac len_cmp_length
                  >> rw_tac list_ss [Once (GSYM zip_append)]
                  >> first_x_assum match_mp_tac
                  >> qexists_tac `l' ++ t2`
                  >> metis_tac [LENGTH_APPEND,zip_append])
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct]
             >- metis_tac [len_cmp_good,good_cmp_thm,cpn_distinct])
     >- (qpat_x_assum `$!M` (mp_tac o Q.SPECL [`r::t1`, `r'::t2`, `r''::l3`])
            >> rw_tac list_ss [ZIP_def])
);

val regexp_compare_trans_eq = Q.store_thm
("regexp_compare_trans_eq",
 `!r s u. (regexp_compare r s = Less) /\ (regexp_compare s u = Equal)
         ==>
         (regexp_compare r u = Less)`,
 rw_tac std_ss [regexp_compare_def]
   >> `[(r,u)] = ZIP([r],[u])` by rw[ZIP_def]
   >> pop_assum SUBST_ALL_TAC
   >> match_mp_tac regexp_compareW_trans_eq
   >> Q.EXISTS_TAC `[(r,s)]`
   >> Q.EXISTS_TAC `[s]`
   >> rw[ZIP_def]);

val regexp_compare_good = Q.store_thm
("regexp_compare_good",
 `good_cmp regexp_compare`,
 rw_tac std_ss [good_cmp_thm,regexp_compare_eq]
  >> metis_tac [regexp_compare_antisym,
                regexp_compare_trans,regexp_compare_trans_eq]);

val regexp_leq_total = Q.store_thm
("regexp_leq_total",
 `total regexp_leq`,
 rw [total_def, regexp_leq_def] >> every_case_tac >> fs [] >>
 metis_tac [regexp_compare_antisym, cpn_distinct]);

val regexp_leq_transitive = Q.store_thm
("regexp_leq_transitive",
 `transitive regexp_leq`,
 rw [transitive_def, regexp_leq_def]
   >> every_case_tac
   >> fs [regexp_compare_eq]
   >> metis_tac [regexp_compare_eq, regexp_compare_trans,cpn_distinct]);

val regexp_leq_antisym = Q.store_thm
("regexp_leq_antisym",
  `antisymmetric regexp_leq`,
  RW_TAC list_ss [antisymmetric_def, regexp_leq_def] >>
  every_case_tac >> full_simp_tac list_ss [] >>
  metis_tac [regexp_compare_antisym, cpn_distinct,regexp_compare_eq]);

val regexp_compare_id = Q.store_thm
("regexp_compare_id",
  `!r. regexp_compare r r = Equal`,
 metis_tac [regexp_compare_good, good_cmp_def])


(*---------------------------------------------------------------------------*)
(* Check if a regexp matches nothing, i.e., denotes the empty set.  Neg r    *)
(* should match nothing iff r matches every possible string; however, that   *)
(* is not easy to determine, so we're conservative here and just say that    *)
(* Neg r might always match something.                                       *)
(*---------------------------------------------------------------------------*)

val is_regexp_empty_def =
 tDefine
  "is_regexp_empty"
  `(is_regexp_empty (Chset cs) = (cs = charset_empty)) /\
   (is_regexp_empty (Cat r1 r2) = (is_regexp_empty r1 \/ is_regexp_empty r2)) /\
   (is_regexp_empty (Star _) = F) /\
   (is_regexp_empty (Or rs) = EVERY is_regexp_empty rs) /\
   (is_regexp_empty (Neg r) = F)`
(WF_REL_TAC `measure rsize`
  >> conj_tac
  >- metis_tac [rsize_or_lem]
  >- rw_tac arith_ss [rsize_def]);

val regexp_empty_thm = Q.store_thm
("regexp_empty_thm",
 `!r.  is_regexp_empty r ==> !w. ~regexp_lang r w`,
 recInduct (fetch "-" "is_regexp_empty_ind")
  >> rw [is_regexp_empty_def, regexp_lang_thm, EVERY_EL,charset_mem_empty]
  >> metis_tac[MEM_EL]);

(*---------------------------------------------------------------------------*)
(* Nullability.                                                              *)
(* Does a regexp list have a regexp that recognizes the empty string? The    *)
(* worklist-style algorithm is relatively efficient and gets around a        *)
(* limitation in the cakeML translator.                                      *)
(*---------------------------------------------------------------------------*)

val nullableW_def = (* the worklist represents a disjunction *)
 tDefine
  "nullableW"
 `(nullableW [] = F) /\
  (nullableW (Chset _ :: t) = nullableW t) /\
  (nullableW (Cat r s :: t) = ((nullableW [r] /\ nullableW [s]) \/ nullableW t)) /\
  (nullableW (Star _ :: t)  = T) /\
  (nullableW (Neg r :: t)   = (~nullableW [r] \/ nullableW t)) /\
  (nullableW (Or rs :: t)   = nullableW (rs ++ t))`
(WF_REL_TAC `measure rsizel` THEN RW_TAC list_ss [rsize_def,rsizel_append])

val nullable_def =
 Define
  `nullable r = nullableW [r]`;

val nullableW_thm = Q.store_thm
("nullableW_thm",
 `!rlist. nullableW rlist <=> EXISTS (\r. regexp_lang r "") rlist`,
  recInduct (fetch "-" "nullableW_ind")
    >> rw_tac list_ss [nullableW_def, regexp_lang_thm]
    >> metis_tac [EVERY_DEF,FLAT]);

val nullable_thm = Q.store_thm
("nullable_thm",
 `!r. nullable r <=> regexp_lang r ""`,
 RW_TAC list_ss [nullable_def,nullableW_thm]);

(*---------------------------------------------------------------------------*)
(* Brzozowski derivative                                                     *)
(*---------------------------------------------------------------------------*)

val deriv_def =
 tDefine
 "deriv"
 `(deriv c (Chset cs) = if charset_mem c cs then Epsilon else Empty) /\
  (deriv c (Neg r)    = Neg (deriv c r)) /\
  (deriv c (Star r)   = Cat (deriv c r) (Star r)) /\
  (deriv c (Cat r s) =
    let cat = Cat (deriv c r) s
    in if nullable r
          then Or [cat; deriv c s]
          else cat) /\
  (deriv c (Or rs) = Or (MAP (deriv c) rs))`
(WF_REL_TAC `measure (\(x,y). rsize y)`
  >> srw_tac [ARITH_ss] []
     >- metis_tac [rsize_or_lem]
     >- rw [rsize_def]
     >- rw [rsize_def]
     >- (rw [rsize_def] >> decide_tac)
     >- (rw [rsize_def] >> decide_tac));

(*---------------------------------------------------------------------------*)
(* Iterate deriv through a string. Check for nullable at the end. This is a  *)
(* basic matching algorithm.                                                 *)
(*---------------------------------------------------------------------------*)

val deriv_matches_def =
 Define
  `(deriv_matches r "" = nullable r) /\
   (deriv_matches r (c::s) = deriv_matches (deriv (ORD c) r) s)`;

(*---------------------------------------------------------------------------*)
(* Basic correctness lemma for derivative                                    *)
(*---------------------------------------------------------------------------*)

val split_concat = Q.prove
( `!ss c s.
   (c::s = CONCAT ss)
   ==>
   ?ss1 s2 ss3. EVERY (\s. s = "") ss1 /\ (ss = ss1++[c::s2]++ss3)`,
 Induct_on `ss` >> rw [] >> Cases_on `h` >> fs []
 >| [res_tac >> rw [] >> qexists_tac `""::ss1` >> rw [],
     qexists_tac `[]` >> rw []]);

val concat_empties = Q.prove
(`!ss1. EVERY (\s. s = []) ss1 ==> (CONCAT ss1 = [])`,
 Induct_on `ss1` >> rw []);

val deriv_thm = Q.store_thm
("deriv_thm",
`(!r c s. regexp_lang r (c::s) = regexp_lang (deriv (ORD c) r) s) /\
 (!rs c s. regexp_lang (Or rs) (c::s) = regexp_lang (deriv (ORD c) (Or rs)) s)`,
 ho_match_mp_tac regexp_induction >>
 rw [regexp_lang_thm, deriv_def, LET_THM, charset_mem_empty,Epsilon_def,Empty_def]
 >> simp_tac bool_ss [GSYM IMP_DISJ_THM]
 >- (rw [EQ_IMP_THM]
      >- (Q.EXISTS_TAC `[]` >> rw[])
      >- (Q.EXISTS_TAC `ORD c`
            >> rw[stringTheory.CHR_ORD]
            >> fs [regexp_lang_thm,EVERY_MEM,charset_mem_empty]
            >> Cases_on `ws`
            >> full_simp_tac list_ss[] >> metis_tac[]))
 >- (rw [EQ_IMP_THM,charset_mem_def]
      >> metis_tac[ORD_CHR_lem,charset_mem_def])
 >- (eq_tac >> rw [regexp_lang_thm, nullable_thm] >|
     [Cases_on `w1` >> fs []
        >- (metis_tac [])
        >- (rw[SIMP_RULE std_ss [IN_DEF] IN_dot] >> metis_tac[]),
      Cases_on `w1` >> fs [] >> rw[] >> metis_tac[],
      metis_tac [STRCAT_EQNS],
      metis_tac [STRCAT_EQNS],
      metis_tac [STRCAT_EQNS]])
 >- (rw [EQ_IMP_THM]
     >- (imp_res_tac split_concat
         >> fs [] >> rw []
         >> qexists_tac `s2`
         >> qexists_tac `CONCAT ss3`
         >> rw []
             >- metis_tac []
             >- metis_tac []
             >- (imp_res_tac concat_empties >> fs []))
     >- (qexists_tac `(c::w1) :: ws` >> rw [])));

(*---------------------------------------------------------------------------*)
(* Correctness of deriv                                                      *)
(*---------------------------------------------------------------------------*)

val regexp_lang_deriv = Q.store_thm
("regexp_lang_deriv",
 `!r s. regexp_lang r s = deriv_matches r s`,
 Induct_on `s` >> rw [deriv_matches_def, nullable_thm] >> metis_tac [deriv_thm]);

val regexp_lang_eqns = Q.store_thm
("regexp_lang_eqns",
`(!s. regexp_lang (Chset charset_empty) s = F) /\
 (!r1 r2 r3 s.
    regexp_lang (Cat (Cat r1 r2) r3) s = regexp_lang (Cat r1 (Cat r2 r3)) s) /\
 (!s. regexp_lang (Or []) s = F) /\
 (!s r. regexp_lang (Or [r]) s = regexp_lang r s) /\
 (!r. (!s. regexp_lang r s = F) ==>
      (!r' s. regexp_lang (Cat r' r) s = F) /\
      (!r' s. regexp_lang (Cat r r') s = F) /\
      (!s. regexp_lang (Star r) s = (s = ""))) /\
 (!r. (!s. regexp_lang r s = (s = "")) ==>
      (!r' s. regexp_lang (Cat r' r) s = regexp_lang r' s) /\
      (!r' s. regexp_lang (Cat r r') s = regexp_lang r' s) /\
      (!s. regexp_lang (Star r) s = (s = "")))`,
 rw [charset_mem_empty, regexp_lang_thm]
   >| [metis_tac [APPEND_ASSOC],
       rw [EQ_IMP_THM]
       >| [match_mp_tac concat_empties >> Induct_on `ws` >> rw_tac list_ss [],
           qexists_tac `[]` >> rw []],
       rw [EQ_IMP_THM]
       >| [match_mp_tac concat_empties >> Induct_on `ws` >> rw_tac list_ss [],
          qexists_tac `[""]` >> rw []]]);

val deriv_matches_eqns = save_thm
("deriv_matches_eqns",
 REWRITE_RULE [regexp_lang_deriv] regexp_lang_eqns);

val regexp_lang_ctxt_eqns = Q.store_thm ("regexp_lang_ctxt_eqns",
`!r1 r2.
  (!s. regexp_lang r1 s = regexp_lang r2 s)
  ==>
  (!r s. regexp_lang (Cat r1 r) s = regexp_lang (Cat r2 r) s) /\
  (!r s. regexp_lang (Cat r r1) s = regexp_lang (Cat r r2) s) /\
  (!s. regexp_lang (Star r1) s = regexp_lang (Star r2) s) /\
  (!s rs1 rs2. regexp_lang (Or (rs1++r1::rs2)) s =
               regexp_lang (Or (rs1++r2::rs2)) s) /\
  (!s. regexp_lang (Neg r1) s = regexp_lang (Neg r2) s)`,
rw [regexp_lang_thm] >> metis_tac [SET_EQ_THM]);

val deriv_matches_ctxt_eqns = save_thm
("deriv_matches_ctxt_eqns",
 REWRITE_RULE [regexp_lang_deriv] regexp_lang_ctxt_eqns);

(*---------------------------------------------------------------------------*)
(* Smart constructors for building normalized regexps                        *)
(*---------------------------------------------------------------------------*)

val is_charset_def =
 Define `
  (is_charset (Chset cs) = T) /\
  (is_charset _ = F)`;

val build_char_set_def =
 Define
   `build_char_set cs = Chset cs`;

val merge_charsets_def = (* requires all charsets to be adjacent *)
 tDefine
  "merge_charsets"
  `(merge_charsets (Chset cs1::Chset cs2::rs) =
       merge_charsets (Chset (charset_union cs1 cs2)::rs)) /\
   (merge_charsets rs = rs)`
 (WF_REL_TAC `measure LENGTH` THEN RW_TAC list_ss []);

val merge_charsets_ind = fetch "-" "merge_charsets_ind";

val assoc_cat_def =
 Define
  `(assoc_cat (Cat r1 r2) r3 = Cat r1 (assoc_cat r2 r3)) /\
   (assoc_cat r1 r2 = Cat r1 r2)`;

val assoc_cat_ind = fetch "-" "assoc_cat_ind";

val build_cat_def =
 Define `
   build_cat r1 r2 =
     if (r1 = Empty) \/ (r2 = Empty) then Empty
     else if r1 = Epsilon then r2
     else if r2 = Epsilon then r1
     else
       assoc_cat r1 r2`;

val build_neg_def =
 Define `
  (build_neg (Neg r) = r) /\
  (build_neg r = Neg r)`;

val build_star_def =
 Define `
  (build_star (Star r) = Star r) /\
  (build_star r = Star r)`;

val flatten_or_def =
 Define `
  (flatten_or [] = []) /\
  (flatten_or (Or rs::rs') = rs ++ flatten_or rs') /\
  (flatten_or (r::rs) = r :: flatten_or rs)`;

val flatten_or_ind = fetch"-" "flatten_or_ind";

val remove_dups_def = (* requires sorted input *)
 Define
 `(remove_dups [] = []) /\
  (remove_dups [r] = [r]) /\
  (remove_dups (r1::r2::rs) =
    if regexp_compare r1 r2 = Equal then
      remove_dups (r2::rs)
    else
      r1::remove_dups (r2::rs))`;

val remove_dups_ind = fetch"-" "remove_dups_ind";

val build_or_def =
 Define `
  build_or rs =
    let rs = remove_dups (merge_charsets (mergesort regexp_leq (flatten_or rs)))
    in
      if MEM (Neg Empty) rs then Neg Empty
      else
      case rs of
        | [] => Empty
        | [r] => r
        | [Chset cs; r] =>
            if cs = charset_empty then
              r
            else
              Or [Chset cs; r]
        | Chset cs :: rs =>
             if cs = charset_empty then
              Or rs
            else
              Or (Chset cs::rs)
        | ___ => Or rs`;


(*---------------------------------------------------------------------------*)
(* Correctness of smart constructors                                         *)
(*---------------------------------------------------------------------------*)

val regexp_smart_constructors_def = save_thm
("regexp_smart_constructors_def",
 LIST_CONJ [build_or_def, build_star_def,
            build_cat_def,build_char_set_def,
            assoc_cat_def, build_neg_def]);

val assoc_cat_correct = Q.prove
(`!r1 r2 s. regexp_lang (assoc_cat r1 r2) s = regexp_lang (Cat r1 r2) s`,
 Induct_on `r2`
   >> rw []
   >> rw [assoc_cat_def, regexp_lang_eqns, regexp_lang_thm]);

val Cat_Empty = Q.prove
(`(!r. regexp_lang (Cat r Empty) = regexp_lang Empty) /\
  (!r. regexp_lang (Cat Empty r) = regexp_lang Empty)`,
 rw_tac list_ss [SET_EQ_THM,Empty_def, regexp_lang_thm,charset_mem_empty]);

val EVERY_EMPTY = Q.prove
(`!wlist. EVERY EMPTY wlist ==> (CONCAT wlist = [])`,
 Induct THEN SRW_TAC [] []);

val regexp_lang_epsilon = Q.prove
(`regexp_lang Epsilon w = (w = "")`,
 rw_tac list_ss [Epsilon_def, regexp_lang_thm,EQ_IMP_THM]
 >- (full_simp_tac list_ss [charset_mem_empty,regexp_lang_def]
     >> POP_ASSUM MP_TAC >> SRW_TAC[][]
     >> metis_tac [EVERY_EMPTY])
 >- (Q.EXISTS_TAC `[]` >> rw[])
);;

val Cat_Epsilon = Q.prove
(`(!r. regexp_lang (Cat r Epsilon) = regexp_lang r) /\
  (!r. regexp_lang (Cat Epsilon r) = regexp_lang r)`,
 rw_tac list_ss [regexp_lang_thm,SET_EQ_THM,regexp_lang_epsilon]);

val build_cat_correct = Q.prove
(`!r1 r2 s. regexp_lang (build_cat r1 r2) s = regexp_lang (Cat r1 r2) s`,
 metis_tac [build_cat_def,Cat_Empty,Cat_Epsilon,assoc_cat_correct]);

val flatten_or_correct = Q.prove (
`!rs s.
  EXISTS (\r. regexp_lang r s) (flatten_or rs) =
  EXISTS (\r. regexp_lang r s) rs`,
 Induct_on `rs` >>
 rw [flatten_or_def] >>
 Cases_on `h` >>
 rw [flatten_or_def] >>
 rw [regexp_lang_thm]);

val sort_regexps_correct = Q.prove (
`!rs s.
  EXISTS (\r. regexp_lang r s) (mergesort regexp_leq rs) =
  EXISTS (\r. regexp_lang r s) rs`,
 rw [EXISTS_MEM, mergesort_mem]);

val merge_charsets_correct = Q.prove (
`!rs s.
  EXISTS (\r. regexp_lang r s) (merge_charsets rs) =
  EXISTS (\r. regexp_lang r s) rs`,
 ho_match_mp_tac merge_charsets_ind >>
 rw [merge_charsets_def] >>
 rw [charset_mem_union, regexp_lang_thm] >>
 metis_tac []);

val remove_dups_correct = Q.prove (
`!rs s.
  EXISTS (\r. regexp_lang r s) (remove_dups rs) =
  EXISTS (\r. regexp_lang r s) rs`,
 ho_match_mp_tac remove_dups_ind >>
 rw [remove_dups_def] >>
 fs [regexp_compare_eq] >>
 rw [] >>
 metis_tac []);

val build_or_init_correct = Q.prove (
`!rs s.
  EXISTS (\r. regexp_lang r s) rs
  <=>
  EXISTS (\r. regexp_lang r s)
         (remove_dups (merge_charsets (mergesort regexp_leq (flatten_or rs))))`,
 metis_tac [remove_dups_correct, merge_charsets_correct,
            sort_regexps_correct, flatten_or_correct]);

val build_or_correct = Q.prove (
`!rs s. regexp_lang (build_or rs) s = regexp_lang (Or rs) s`,
 rw [build_or_def, LET_THM, regexp_lang_thm,Empty_def,Epsilon_def]
 >- (rw [Once build_or_init_correct] >>
     pop_assum mp_tac >>
     Q.SPEC_TAC (`remove_dups (merge_charsets (mergesort regexp_leq (flatten_or rs)))`, `rs`) >>
     Induct_on `rs` >>
     rw [] >>
     fs [regexp_lang_thm, charset_mem_empty])
 >- (rw [Once build_or_init_correct] >>
     pop_assum mp_tac >>
     Q.SPEC_TAC (`remove_dups (merge_charsets (mergesort regexp_leq (flatten_or rs)))`, `rs`) >>
     Induct_on `rs` >>
     rw [] >>
     rw [charset_mem_empty, regexp_lang_thm] >>
     res_tac >>
     fs [] >>
     every_case_tac >>
     fs [regexp_lang_thm, combinTheory.o_DEF, charset_mem_empty] >>
     REWRITE_TAC [EXISTS_NOT_EVERY] >>
     metis_tac []));

val build_star_correct = Q.prove
(`!r s. regexp_lang (build_star r) s = regexp_lang (Star r) s`,
 rw [] >>
 Cases_on `r` >>
 rw [build_star_def] >>
 rw [regexp_lang_def] >>
 metis_tac [FormalLangTheory.KSTAR_KSTAR_EQ_KSTAR]);

val build_neg_correct = Q.prove (
`!r s. regexp_lang (build_neg r) s = regexp_lang (Neg r) s`,
 Cases_on `r` >>
 rw [build_neg_def, regexp_lang_def]);


(*---------------------------------------------------------------------------*)
(* Use smart constructors to normalize derivatives.                          *)
(*---------------------------------------------------------------------------*)

val smart_deriv_def =
 tDefine
  "smart_deriv"
  `(smart_deriv c (Chset cs) = if charset_mem c cs then Epsilon else Empty) /\
   (smart_deriv c (Cat r1 r2) =
     let d1 = build_cat (smart_deriv c r1) r2
     in if nullable r1
          then build_or [d1; smart_deriv c r2]
          else d1) /\
   (smart_deriv c (Star r) = build_cat (smart_deriv c r) (build_star r)) /\
   (smart_deriv c (Or rs) = build_or (MAP (smart_deriv c) rs)) /\
   (smart_deriv c (Neg r) = build_neg (smart_deriv c r))`
(WF_REL_TAC `measure (rsize o SND)`
  THEN RW_TAC list_ss [rsize_or_lem]
  THEN RW_TAC list_ss [rsize_def]);

val smart_deriv_ind = fetch "-" "smart_deriv_ind";


val smart_constructors_correct = Q.store_thm
("smart_constructors_correct",
 `(!r c s. regexp_lang (smart_deriv c r) s <=> regexp_lang (deriv c r) s) /\
  (!rs c s. EXISTS (\r. regexp_lang (smart_deriv c r) s) rs <=>
            EXISTS (\r. regexp_lang (deriv c r) s) rs)`,
 ho_match_mp_tac regexp_induction
 >> rw [regexp_lang_eqns, smart_deriv_def, deriv_def, build_cat_correct,Empty_def, Epsilon_def]
 >- (every_case_tac >>
     UNABBREV_ALL_TAC >>
     rw [build_cat_correct, build_or_correct]
     >- (rw [regexp_lang_thm, build_cat_correct])
     >- metis_tac [regexp_lang_ctxt_eqns])
 >- metis_tac [build_star_correct, regexp_lang_ctxt_eqns]
 >- rw [build_or_correct, regexp_lang_thm, EXISTS_MAP]
 >- metis_tac [build_neg_correct, regexp_lang_ctxt_eqns]);


val lem = Q.prove
(`smart_deriv c (Cat (Chset cs) r) = if charset_mem c cs then r else Empty`,
 rw_tac list_ss [smart_deriv_def,LET_THM]
  >- full_simp_tac list_ss [nullable_def,nullableW_def]
  >- full_simp_tac list_ss [nullable_def,nullableW_def]
  >- rw_tac list_ss [build_cat_def,Empty_def, Epsilon_def]
  >- rw_tac list_ss [build_cat_def]
);

val smart_deriv_thm = Q.store_thm
("smart_deriv_thm",
 `(smart_deriv c (Chset cs) = if charset_mem c cs then Epsilon else Empty) /\
  (smart_deriv c (Cat (Chset cs) r) = if charset_mem c cs then r else Empty) /\
  (smart_deriv c (Cat r1 r2) =
    let d1 = build_cat (smart_deriv c r1) r2
    in if nullable r1
         then build_or [d1; smart_deriv c r2]
         else d1) /\
  (smart_deriv c (Star r) = build_cat (smart_deriv c r) (build_star r)) /\
  (smart_deriv c (Or rs) = build_or (MAP (smart_deriv c) rs)) /\
  (smart_deriv c (Neg r) = build_neg (smart_deriv c r))`,
metis_tac [lem,smart_deriv_def]);

(*---------------------------------------------------------------------------*)
(* Matcher that uses smart constructor derivatives                           *)
(*---------------------------------------------------------------------------*)

val smart_deriv_matches_def =
 Define
  `(smart_deriv_matches r "" = nullable r) /\
   (smart_deriv_matches r (c::s) = smart_deriv_matches (smart_deriv (ORD c) r) s)`;

(*---------------------------------------------------------------------------*)
(* Correctness of matching with smart derivatives                            *)
(*---------------------------------------------------------------------------*)

val regexp_lang_smart_deriv = Q.store_thm
("regexp_lang_smart_deriv",
 `!r s. smart_deriv_matches r s <=> regexp_lang r s`,
  Induct_on `s` >>
  rw [smart_deriv_matches_def, nullable_thm, deriv_matches_def] >>
  rw [regexp_lang_deriv] >>
  rw [deriv_matches_def] >>
  rw [GSYM regexp_lang_deriv] >>
  metis_tac [smart_constructors_correct]);

(*---------------------------------------------------------------------------*)
(* Use smart constructors to normalize a regexp.                             *)
(*---------------------------------------------------------------------------*)

val normalize_def =
 tDefine
  "normalize"
  `(normalize (Chset cs) = build_char_set cs) /\
   (normalize (Cat r1 r2) = build_cat (normalize r1) (normalize r2)) /\
   (normalize (Star r) = build_star (normalize r)) /\
   (normalize (Or rs) = build_or (MAP normalize rs)) /\
   (normalize (Neg r) = build_neg (normalize r))`
(WF_REL_TAC `measure rsize`
  THEN RW_TAC list_ss [rsize_or_lem]
  THEN RW_TAC list_ss [rsize_def]);

val normalize_ind = fetch "-" "normalize_ind";

(*---------------------------------------------------------------------------*)
(* Language of a regexp does not change under normalization                  *)
(*---------------------------------------------------------------------------*)

val regexp_lang_normalize_help = Q.prove (
`(!r s. regexp_lang r s = regexp_lang (normalize r) s) /\
 (!rs s. EXISTS (\r. regexp_lang r s) rs =
         EXISTS (\r. regexp_lang (normalize r) s) rs)`,
 ho_match_mp_tac regexp_induction >>
 rw [] >>
 rw [normalize_def, build_star_correct, build_cat_correct, build_or_correct,
     build_neg_correct, build_char_set_def, regexp_lang_eqns]
 >- metis_tac [regexp_lang_ctxt_eqns]
 >- metis_tac [regexp_lang_ctxt_eqns]
 >- (rw [regexp_lang_thm] >>
     fs [EXISTS_MEM, MEM_MAP] >>
     metis_tac [regexp_lang_ctxt_eqns])
 >- metis_tac [regexp_lang_ctxt_eqns]);

val regexp_lang_normalize = Q.store_thm
("regexp_lang_normalize",
 `!r s. regexp_lang r s = regexp_lang (normalize r) s`,
 metis_tac [regexp_lang_normalize_help]);

val regexp_lang_normalize_eta = Q.store_thm
("regexp_lang_normalize_eta",
 `!r. regexp_lang r = regexp_lang (normalize r)`,
 metis_tac [regexp_lang_normalize]);

(*---------------------------------------------------------------------------*)
(* Is a regexp in normal form?                                               *)
(*---------------------------------------------------------------------------*)

val no_sub_or_def =
 Define `
  no_sub_or rs = EVERY (\r. case r of | Or _ => F | _ => T) rs`;

val is_normalized_def =
 tDefine
  "is_normalized"
  `(is_normalized (Chset cs) <=> T) /\
   (is_normalized (Cat r1 r2) <=>
     (r1 <> Chset charset_empty) /\
     (r2 <> Chset charset_empty) /\
     (r1 <> Star (Chset charset_empty)) /\
     (r2 <> Star (Chset charset_empty)) /\
     (case r1 of | Cat _ _ => F | _ => T) /\
     (is_normalized r1) /\
     (is_normalized r2)) /\
   (is_normalized (Star r) <=> is_normalized r /\ (case r of | Star _ => F | _ => T)) /\
   (is_normalized (Or rs) <=>
     LENGTH rs > 1 /\
     LENGTH (FILTER is_charset rs) <= 1 /\
     ALL_DISTINCT rs /\
     SORTED regexp_leq rs /\
     no_sub_or rs /\
     EVERY is_normalized rs /\
     ~MEM (Neg (Chset charset_empty)) rs /\
     ~MEM (Chset charset_empty) rs) /\
   (is_normalized (Neg r) <=> is_normalized r /\ (case r of | Neg _ => F | _ => T))
 `
(WF_REL_TAC `measure rsize`
  >> srw_tac [ARITH_ss] []
     >- metis_tac [rsize_or_lem]
     >- (rw [rsize_def] >> decide_tac)
     >- (rw [rsize_def] >> decide_tac)
     >- rw [rsize_def]
     >- rw [rsize_def]);

val is_normalized_ind = fetch "-" "is_normalized_ind";

(*---------------------------------------------------------------------------*)
(* Slightly more compact version.                                            *)
(*---------------------------------------------------------------------------*)

val is_normalized_eqns = Q.store_thm
("is_normalized_eqns",
 `(!cs. is_normalized (Chset cs) <=> T) /\
  (!r. is_normalized (Star r) <=> is_normalized r /\ (!s. r <> Star s)) /\
  (!r. is_normalized (Neg r) <=> is_normalized r /\ (!s. r <> Neg s)) /\
  (!r1 r2.
       is_normalized (Cat r1 r2) <=>
         r1 <> Chset charset_empty /\ r2 <> Chset charset_empty /\
         r1 <> Star (Chset charset_empty) /\ r2 <> Star (Chset charset_empty) /\
         (!x y. r1 <> Cat x y) /\
         is_normalized r1 /\ is_normalized r2) /\
  (!rs. is_normalized (Or rs) <=>
        LENGTH rs > 1 /\ LENGTH (FILTER is_charset rs) <= 1 /\
        ALL_DISTINCT rs /\ SORTED regexp_leq rs /\ no_sub_or rs /\
        EVERY is_normalized rs /\
        Neg (Chset charset_empty) NOTIN set rs /\
        Chset charset_empty NOTIN set rs)`,
 REPEAT CONJ_TAC THENL
  [METIS_TAC [is_normalized_def],
   RW_TAC list_ss [Once is_normalized_def] THEN CASE_TAC,
   RW_TAC list_ss [Once is_normalized_def] THEN CASE_TAC,
   RW_TAC list_ss [Once is_normalized_def] THEN CASE_TAC,
   RW_TAC list_ss [Once is_normalized_def] THEN METIS_TAC[]]);


(*---------------------------------------------------------------------------*)
(* Smart constructors do in fact normalize                                   *)
(*---------------------------------------------------------------------------*)

val norm_char_set = Q.prove
(`!cs. is_normalized (build_char_set cs)`,
 rw [is_normalized_def, regexp_smart_constructors_def]);

val norm_is_regexp_empty = Q.store_thm
("norm_is_regexp_empty",
 `!r. is_normalized r ==> (is_regexp_empty r = (r = Chset charset_empty))`,
 recInduct (fetch "-" "is_normalized_ind") >>
 rw [is_normalized_def, is_regexp_empty_def] >>
 fs [EXISTS_MEM, EVERY_MEM] >>
 rw [] >>
 Cases_on `rs` >>
 rw [] >>
 fs [] >>
 metis_tac []);

val assoc_cat_cat = Q.prove (
`!r1 r2. ?r1' r2'. assoc_cat r1 r2 = Cat r1' r2'`,
recInduct assoc_cat_ind >> rw [assoc_cat_def]);

val normalized_assoc_cat = Q.prove
(`!r1 r2.
  (r1 <> Chset charset_empty) /\
  (r2 <> Chset charset_empty) /\
  (r1 <> Star (Chset charset_empty)) /\
  (r2 <> Star (Chset charset_empty)) /\
  is_normalized r1 /\
  is_normalized r2
  ==>
  is_normalized (assoc_cat r1 r2)`,
recInduct assoc_cat_ind
  >> rw [is_normalized_def, regexp_smart_constructors_def]
  >> Cases_on `r1`
  >> fs [is_normalized_def]
  >> metis_tac [assoc_cat_cat, regexp_distinct]);

val norm_cat = Q.prove
(`!r1 r2. is_normalized r1 /\ is_normalized r2 ==> is_normalized (build_cat r1 r2)`,
rw [] >>
Cases_on `r1` >>
fs [is_normalized_def, regexp_smart_constructors_def,Empty_def,Epsilon_def] >>
rw [] >>
fs [is_normalized_def, regexp_smart_constructors_def] >>
rw [] >-
metis_tac [assoc_cat_cat, regexp_distinct] >-
metis_tac [assoc_cat_cat, regexp_distinct] >>
match_mp_tac normalized_assoc_cat >>
rw [is_normalized_def]);

val norm_star = Q.prove
(`!r. is_normalized r ==> is_normalized (build_star r)`,
 Cases_on `r` >>
 rw [is_normalized_def, regexp_smart_constructors_def]);

val norm_neg = Q.store_thm
("norm_neg",
`!r. is_normalized r ==> is_normalized (build_neg r)`,
Cases_on `r` >>
rw [is_normalized_def, regexp_smart_constructors_def]);

(*---------------------------------------------------------------------------*)
(* A normalised Or has only normalised subterms                              *)
(*---------------------------------------------------------------------------*)

val flatten_or_norm_pres = Q.store_thm
("flatten_or_norm_pres",
`!rs. EVERY is_normalized rs ==> EVERY is_normalized (flatten_or rs)`,
recInduct flatten_or_ind >>
rw [flatten_or_def] >>
fs [is_normalized_def, EVERY_MEM]);

val mergesort_norm_pres = Q.store_thm
("mergesort_norm_pres",
`!rs. EVERY is_normalized rs ==> EVERY is_normalized (mergesort regexp_leq rs)`,
 rw [EVERY_MEM, mergesort_mem]);

val merge_charsets_norm_pres = Q.store_thm
("merge_charsets_norm_pres",
`!rs. EVERY is_normalized rs ==> EVERY is_normalized (merge_charsets rs)`,
 ho_match_mp_tac merge_charsets_ind >>
 rw [merge_charsets_def] >>
 res_tac  >>
 fs [is_normalized_def]);

val remove_dups_norm_pres = Q.store_thm
("remove_dups_norm_pres",
`!rs. EVERY is_normalized rs ==> EVERY is_normalized (remove_dups rs)`,
 ho_match_mp_tac remove_dups_ind >>
 rw [remove_dups_def]);

(*---------------------------------------------------------------------------*)
(* A normalised Or contains no Or immediate subterms, flatten_or achieves    *)
(* this.                                                                     *)
(*---------------------------------------------------------------------------*)

val flatten_or_no_or = Q.store_thm
("flatten_or_no_or",
`!rs. EVERY is_normalized rs ==> no_sub_or (flatten_or rs)`,
 recInduct flatten_or_ind >>
 rw [flatten_or_def, no_sub_or_def] >>
 fs [is_normalized_def, EVERY_MEM, no_sub_or_def]);

val mergesort_no_or_pres = Q.store_thm
("mergesort_no_or_pres",
`!rs. no_sub_or rs ==> no_sub_or (mergesort regexp_leq rs)`,
 rw [no_sub_or_def, EVERY_MEM, mergesort_mem]);

val merge_charsets_no_or_pres = Q.store_thm
("merge_charsets_no_or_pres",
`!rs. no_sub_or rs ==> no_sub_or (merge_charsets rs)`,
 ho_match_mp_tac merge_charsets_ind >>
 rw [no_sub_or_def, merge_charsets_def]);

val remove_dups_no_or_pres = Q.store_thm
("remove_dups_no_or_pres",
`!rs. no_sub_or rs ==> no_sub_or (remove_dups rs)`,
 ho_match_mp_tac remove_dups_ind >>
 rw [no_sub_or_def, remove_dups_def]);

(*---------------------------------------------------------------------------*)
(* A normalised Or has sorted subterms.                                      *)
(*---------------------------------------------------------------------------*)

val charset_smallest = Q.prove
(`!r s. is_charset s /\ regexp_leq r s ==> is_charset r`,
 Cases_on `r` >> Cases_on `s`
 >> rw [is_charset_def, regexp_leq_def, regexp_compare_def]
 >> EVAL_TAC);

val SORTED_starts_charsets = Q.store_thm
("SORTED_starts_charsets",
`!rs. SORTED regexp_leq rs ==>
  ?rs1 rs2. (rs = rs1 ++ rs2) /\ EVERY is_charset rs1 /\ ~EXISTS is_charset rs2`,
 Induct_on `rs` >>
 rw [] >>
 assume_tac regexp_leq_transitive >>
 imp_res_tac SORTED_EQ >>
 res_tac >>
 rw [] >>
 Cases_on `rs1 = []` >>
 rw [] >>
 fs [] >>
 rw []
 >- (fs [EVERY_MEM] >>
     rename[`SORTED _ (h::(rs1 ++ rs2))`] >>
     Cases_on `rs1` >>
     fs [] >>
     Cases_on `is_charset h`
     >- (qexists_tac `[h]` >>
         rw [])
     >- (qexists_tac `[]` >>
         rw [] >>
         rw [])
     >- (qexists_tac `[h]` >>
         rw [])
     >- (qexists_tac `[]` >>
         rw [] >>
         rw []))
 >- (qexists_tac `h::rs1` >>
     qexists_tac `rs2` >>
     rw [] >>
     Cases_on `rs1` >>
     fs [SORTED_DEF] >>
     metis_tac [charset_smallest])
);

val merge_charsets_no_charsets = Q.store_thm
("merge_charsets_no_charsets",
`!rs. ~EXISTS is_charset rs ==> (merge_charsets rs = rs)`,
 ho_match_mp_tac merge_charsets_ind >>
 rw [merge_charsets_def] >>
 fs [is_charset_def]);

val merge_charsets_append = Q.store_thm
("merge_charsets_append",
 `!rs1 rs2.
  rs1 <> [] /\
  EVERY is_charset rs1 /\
  ~EXISTS is_charset rs2
  ==>
  ?c.
    is_charset c /\
    (merge_charsets rs1 = [c]) /\
    (merge_charsets (rs1 ++ rs2) = c :: rs2)`,
 ho_match_mp_tac merge_charsets_ind >>
 rw [merge_charsets_def, is_charset_def] >>
 Cases_on `rs2` >>
 fs [merge_charsets_def] >>
 Cases_on `h` >>
 fs [is_charset_def,merge_charsets_def]);


val merge_charsets_sorted_pres = Q.store_thm
("merge_charsets_sorted_pres",
`!rs. SORTED regexp_leq rs ==> SORTED regexp_leq (merge_charsets rs)`,
 rw [] >>
 imp_res_tac SORTED_starts_charsets >>
 rw [] >>
 Induct_on `rs1` >>
 rw [] >>
 fs [merge_charsets_no_charsets] >>
 `h::(rs1++rs2) = (h::rs1)++rs2` by rw [] >>
 `h::rs1 <> []` by rw [] >>
 `EVERY is_charset (h::rs1)` by rw [] >>
 imp_res_tac (SIMP_RULE (srw_ss()) [] merge_charsets_append) >>
 full_simp_tac std_ss [] >>
 `SORTED regexp_leq rs2` by metis_tac [SORTED_APPEND_IFF] >>
 rw [] >>
 fs [] >>
 assume_tac regexp_leq_transitive >>
 imp_res_tac SORTED_EQ >>
 rw [] >>
 first_x_assum match_mp_tac >>
 rw [] >>
 `~is_charset y` by fs [EVERY_MEM] >>
 Cases_on `c` >>
 fs [is_charset_def] >>
 rw [regexp_leq_def] >>
 Cases_on `y` >>
 fs [is_charset_def, regexp_compare_def,regexp_compareW_def]);

val remove_dups_mem = Q.store_thm
("remove_dups_mem",
`!rs r. MEM r (remove_dups rs) = MEM r rs`,
 ho_match_mp_tac remove_dups_ind >>
 rw [remove_dups_def, regexp_compare_eq] >>
 metis_tac []);

val remove_dups_sorted_pres = Q.store_thm
("remove_dups_sorted_pres",
`!rs. SORTED regexp_leq rs ==> SORTED regexp_leq (remove_dups rs)`,
 ho_match_mp_tac remove_dups_ind >>
 rw [remove_dups_def, SORTED_DEF] >>
 res_tac >>
 assume_tac regexp_leq_transitive >>
 imp_res_tac SORTED_EQ >>
 fs [] >>
 first_x_assum match_mp_tac >>
 rw [] >>
 fs [transitive_def, remove_dups_mem] >>
 metis_tac []);

(*---------------------------------------------------------------------------*)
(* A normalised Or has at most 1 Charset subterm. merge_charsets achieves    *)
(* this, but only on a sorted list of regexps.                               *)
(*---------------------------------------------------------------------------*)

val merge_charsets_only1 = Q.store_thm
("merge_charsets_only1",
`!rs. SORTED regexp_leq rs ==> LENGTH (FILTER is_charset (merge_charsets rs)) <= 1`,
 rw [] >>
 imp_res_tac SORTED_starts_charsets >>
 rw [] >>
 Cases_on `rs1 = []` >>
 rw [] >>
 imp_res_tac merge_charsets_append >>
 imp_res_tac merge_charsets_no_charsets >>
 fs [combinTheory.o_DEF, GSYM FILTER_EQ_NIL]);

val remove_dups_charset_only1_pres = Q.store_thm
("remove_dups_charset_only1_pres",
`!rs.
 LENGTH (FILTER is_charset rs) <= 1 ==>
 (LENGTH (FILTER is_charset (remove_dups rs)) = LENGTH (FILTER is_charset rs))`,
 ho_match_mp_tac remove_dups_ind >>
 rw [remove_dups_def] >>
 fs [regexp_compare_eq] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1]);

(*---------------------------------------------------------------------------*)
(* A normalised Or has no duplicate subterms. remove_dups achieves this,     *)
(* but only on a sorted list of regexps.                                     *)
(*---------------------------------------------------------------------------*)

val remove_dups_no_dups = Q.store_thm
("remove_dups_no_dups",
`!rs. SORTED regexp_leq rs ==> ALL_DISTINCT (remove_dups rs)`,
 ho_match_mp_tac remove_dups_ind >>
 rw [remove_dups_def, regexp_compare_eq] >>
 assume_tac regexp_leq_transitive
 >- (first_x_assum match_mp_tac >>
     imp_res_tac SORTED_EQ)
 >- (rw [remove_dups_mem] >>
     fs [SORTED_DEF] >>
     `!r. MEM r rs ==> regexp_leq r2 r` by metis_tac [SORTED_EQ] >>
     CCONTR_TAC >>
     fs [] >>
     fs [] >>
     res_tac >>
     fs [regexp_leq_def] >>
     every_case_tac >>
     fs [regexp_compare_antisym, regexp_compare_eq] >>
     metis_tac [regexp_compare_trans,regexp_compare_eq, cpn_distinct])
 >- (first_x_assum match_mp_tac >> imp_res_tac SORTED_EQ));

val norm_or = Q.store_thm
("norm_or",
 `!rs. EVERY is_normalized rs ==> is_normalized (build_or rs)`,
 rw_tac list_ss [build_or_def, is_normalized_def,Empty_def]
 >> Cases_on `MEM (Neg (Chset charset_empty)) rs'`
 >> rw [is_normalized_def]
 >> `LENGTH (FILTER is_charset rs') <= 1`
           by metis_tac [regexp_leq_total, regexp_leq_transitive,
                         mergesort_sorted, merge_charsets_only1,
                         remove_dups_charset_only1_pres]
 >> `ALL_DISTINCT rs'`
           by metis_tac [regexp_leq_total, regexp_leq_transitive,
                         merge_charsets_sorted_pres,
                         mergesort_sorted, remove_dups_no_dups]
 >> `EVERY is_normalized rs'`
           by metis_tac [flatten_or_norm_pres, remove_dups_norm_pres,
                         merge_charsets_norm_pres, mergesort_norm_pres]
 >> `SORTED regexp_leq rs'`
           by metis_tac [regexp_leq_total, regexp_leq_transitive,
                         mergesort_sorted, remove_dups_sorted_pres,
                         merge_charsets_sorted_pres]
 >> `no_sub_or rs'`
           by metis_tac [flatten_or_no_or, remove_dups_no_or_pres,
                         merge_charsets_no_or_pres, mergesort_no_or_pres]
 >> Cases_on `rs'`
 >> rw [is_normalized_def]
 >> Cases_on `t`
    >- fs[EVERY_DEF]
    >- (imp_res_tac SORTED_starts_charsets
        >> `(rs1 = []) \/ (rs1 = [h])`
            by (rw [] >> CCONTR_TAC >> fs []
                >> Cases_on `rs1`
                >> fs [] >> rw []
                >> Cases_on `t` >> full_simp_tac (srw_ss()++ARITH_ss) [])
       >> fs []
       >- (Cases_on `h` >> rw []
            >> fs [is_charset_def]
            >> `h' <> Chset charset_empty` by (Cases_on `h'` >> fs [is_charset_def])
            >> `~MEM (Chset charset_empty) t'`
                 by (fs [FILTER_EQ_NIL, EVERY_MEM]
                     >> metis_tac [is_charset_def])
            >> srw_tac [ARITH_ss] [is_normalized_def, ETA_THM, SORTED_DEF]
            >> fs [SORTED_DEF, combinTheory.o_DEF, GSYM FILTER_EQ_NIL, no_sub_or_def])
       >- (Cases_on `h` >> rw []
           >> fs [is_charset_def]
           >> Cases_on `t'`
           >> srw_tac [ARITH_ss] [is_normalized_def, ETA_THM, SORTED_DEF]
           >> fs [SORTED_DEF, combinTheory.o_DEF, GSYM FILTER_EQ_NIL, no_sub_or_def]
              >- (Cases_on `h'` >> fs [is_charset_def])
              >- (Cases_on `h'` >> fs [is_charset_def])
              >- (Cases_on `h'` >> fs [is_charset_def])
              >- (Cases_on `h` >> fs [is_charset_def])
              >- (fs [FILTER_EQ_NIL, EVERY_MEM] >> metis_tac [is_charset_def])
              >- (Cases_on `h'` >> fs [is_charset_def])
              >- (Cases_on `h` >> fs [is_charset_def])
              >- (fs [FILTER_EQ_NIL, EVERY_MEM] >> metis_tac [is_charset_def])))
);

(*---------------------------------------------------------------------------*)
(* Normalization delivers normal form                                        *)
(*---------------------------------------------------------------------------*)

val normalize_thm = Q.store_thm
("normalize_thm",
 `!r. is_normalized (normalize r)`,
recInduct normalize_ind >>
rw [normalize_def, norm_char_set, norm_cat, norm_neg, norm_star] >>
metis_tac [norm_or, EVERY_MEM, MEM_MAP]);

val map_id_lem = Q.prove
(`!L f. (!x. MEM x L ==> (f x = x)) ==> (MAP f L = L)`,
 Induct THEN RW_TAC list_ss []);

val flatten_or_id = Q.prove
(`!L. no_sub_or L ==> (flatten_or L = L)`,
Induct THEN RW_TAC list_ss [] THENL
 [RW_TAC list_ss [flatten_or_def],
  Cases_on `h` THEN RW_TAC list_ss [flatten_or_def] THEN
  FULL_SIMP_TAC list_ss [no_sub_or_def] THEN
  BasicProvers.FULL_CASE_TAC THEN RW_TAC list_ss []]);

(*---------------------------------------------------------------------------*)
(* Could drop one of the properties on R (see similar theorem in             *)
(* sortingTheory)                                                            *)
(*---------------------------------------------------------------------------*)

val PERM_SORTED_LIST_EQ = Q.prove
(`!L1 L2.
     PERM L1 L2 /\ antisymmetric R /\ total R /\ transitive R /\
     SORTED R L1 /\ SORTED R L2 ==> (L1 = L2)`,
Induct THEN RW_TAC list_ss [PERM_NIL] THEN
Induct_on `L2` THENL [RW_TAC bool_ss [PERM_NIL],REPEAT STRIP_TAC] THEN
`SORTED R L1 /\ SORTED R L2 /\
  (!a. MEM a L1 ==> R h a) /\
  (!b. MEM b L2 ==> R h' b)` by METIS_TAC [SORTED_EQ] THEN
Cases_on `h = h'` THEN RW_TAC list_ss [] THENL
[METIS_TAC [PERM_CONS_IFF],
 `R h h' /\ ~R h' h \/  R h' h /\ ~R h h'`
  by METIS_TAC [total_def,transitive_def,antisymmetric_def] THENL
 [`MEM h L2`
     by (Q.PAT_X_ASSUM `PERM x y` MP_TAC THEN
         RW_TAC list_ss [PERM_CONS_EQ_APPEND] THEN
         Cases_on `M` THEN FULL_SIMP_TAC list_ss [])
    THEN METIS_TAC [],
  `MEM h' L1`
     by (Q.PAT_X_ASSUM `PERM x y` (MP_TAC o SIMP_RULE bool_ss [Once PERM_SYM])
         THEN RW_TAC list_ss [PERM_CONS_EQ_APPEND] THEN
         Cases_on `M` THEN FULL_SIMP_TAC list_ss [])
    THEN METIS_TAC []]]);

val sorted_sort_id = Q.prove
(`!L. SORTED regexp_leq L ==> (mergesort regexp_leq L = L)`,
 RW_TAC list_ss [] THEN
 `PERM L (mergesort regexp_leq L)`
     by METIS_TAC [mergesort_perm] THEN
 `antisymmetric regexp_leq /\ total regexp_leq /\ transitive regexp_leq`
     by METIS_TAC [regexp_leq_total,regexp_leq_antisym,regexp_leq_transitive] THEN
 `SORTED regexp_leq (mergesort regexp_leq L)`
     by METIS_TAC [mergesort_sorted]
  THEN METIS_TAC [PERM_SORTED_LIST_EQ]);

val merge_charsets_id = Q.prove
(`!L. LENGTH (FILTER is_charset L) <= 1 ==> (merge_charsets L = L)`,
 recInduct merge_charsets_ind THEN RW_TAC list_ss [merge_charsets_def,is_charset_def]);

val remove_dups_id = Q.prove
(`!L. ALL_DISTINCT L ==> (remove_dups L = L)`,
 recInduct remove_dups_ind THEN RW_TAC list_ss [remove_dups_def,regexp_compare_eq]);

(*---------------------------------------------------------------------------*)
(* Normalization as identity function                                        *)
(*---------------------------------------------------------------------------*)

val FULL_CASE_TAC = BasicProvers.FULL_CASE_TAC;

val normalize_id = Q.store_thm
("normalize_id",
 `!r. is_normalized r ==> (normalize r = r)`,
recInduct is_normalized_ind
 THEN SIMP_TAC list_ss [is_normalized_def, normalize_def]
 THEN RW_TAC list_ss [] THENL
 [METIS_TAC [build_char_set_def],
  FULL_CASE_TAC THEN FULL_SIMP_TAC list_ss [is_normalized_def]
    THEN RW_TAC list_ss [build_cat_def,assoc_cat_def,Empty_def,Epsilon_def],
  FULL_CASE_TAC THEN FULL_SIMP_TAC list_ss [is_normalized_def]
    THEN RW_TAC list_ss [build_star_def],
  FULL_SIMP_TAC list_ss [EVERY_MEM] THEN RW_TAC list_ss [map_id_lem]
    THEN RW_TAC list_ss [build_or_def,LET_THM,flatten_or_id,Empty_def,
                 sorted_sort_id,merge_charsets_id,remove_dups_id]
    THEN CASE_TAC THENL [FULL_SIMP_TAC arith_ss [LENGTH],ALL_TAC]
    THEN Cases_on`t` THENL [FULL_SIMP_TAC arith_ss [LENGTH],ALL_TAC]
    THEN CASE_TAC THEN RW_TAC list_ss []
    THEN Cases_on `t'` THEN FULL_SIMP_TAC arith_ss []
    THEN CASE_TAC THEN FULL_SIMP_TAC list_ss [],
  FULL_CASE_TAC THEN FULL_SIMP_TAC list_ss [is_normalized_def]
    THEN RW_TAC list_ss [build_neg_def]]);

(*---------------------------------------------------------------------------*)
(* Normalization is idempotent                                               *)
(*---------------------------------------------------------------------------*)

val normalize_idempotent = Q.store_thm
("normalize_idempotent",
 `!r. normalize (normalize r) = normalize r`,
 METIS_TAC [normalize_id,normalize_thm]);


(*---------------------------------------------------------------------------*)
(* Smart derivative yields a regexp in normal form                           *)
(*---------------------------------------------------------------------------*)

val smart_deriv_normalized = Q.store_thm
("smart_deriv_normalized",
 `!c r. is_normalized r ==> is_normalized (smart_deriv c r)`,
 recInduct smart_deriv_ind
 >> rw [is_normalized_def, smart_deriv_def, normalize_def,
        norm_char_set, norm_cat, norm_neg, norm_star,Empty_def,Epsilon_def]
 >> match_mp_tac norm_or
 >> rw []
    >- metis_tac[norm_cat]
    >- (fs [EVERY_MAP] >> fs [EVERY_MEM])
);

(*---------------------------------------------------------------------------*)
(* smart_deriv is ordinary deriv followed by normalization                   *)
(*---------------------------------------------------------------------------*)

val smart_deriv_normalize_deriv = Q.store_thm
("smart_deriv_normalize_deriv",
 `!r c. is_normalized r ==> (smart_deriv c r = normalize (deriv c r))`,
 recInduct normalize_ind THEN
 RW_TAC list_ss [is_normalized_def, smart_deriv_def, normalize_def, deriv_def,
        LET_THM, Epsilon_def, Empty_def]
 THENL
  [rw [build_char_set_def, build_star_def],
   rw [build_char_set_def],
   RW_TAC list_ss [normalize_def,LET_THM] THEN METIS_TAC [normalize_id],
   METIS_TAC [normalize_id],
   RW_TAC list_ss [MAP_MAP_o,combinTheory.o_DEF] THEN
     AP_TERM_TAC THEN RW_TAC std_ss [MAP_EQ_f] THEN
     METIS_TAC [EVERY_MEM,MAP_EQ_f]]);


(*---------------------------------------------------------------------------*)
(* We can use the following theorem as a quick regexp matcher in the         *)
(* rewriter, but it doesn't handle Neg and diverges on (Star r) where        *)
(* (regexp_lang r "")                                                        *)
(*---------------------------------------------------------------------------*)

val regexp_lang_algorithm = Q.store_thm
("regexp_lang_algorithm",
 `(!cs r. regexp_lang (Cat (Chset cs) r) [] = F) /\
  (!cs r c s.
   regexp_lang (Cat (Chset cs) r) (c::s) =
     (charset_mem (ORD c) cs /\ regexp_lang r s)) /\
  (!r1 r2 r3 s.
   regexp_lang (Cat (Cat r1 r2) r3) s =
     regexp_lang (Cat r1 (Cat r2 r3)) s) /\
  (!r1 r2 s.
   regexp_lang (Cat (Star r1) r2) s =
     (regexp_lang r2 s \/
     regexp_lang (Cat r1 (Cat (Star r1) r2)) s)) /\
  (!rs r s.
   regexp_lang (Cat (Or rs) r) s =
     EXISTS (\r'. regexp_lang (Cat r' r) s) rs)`,
REPEAT CONJ_TAC
 >- rw [regexp_lang_thm]
 >- (rw_tac list_ss [regexp_lang_thm,EQ_IMP_THM,charset_mem_def]
     >> fs[]
        >- metis_tac [ORD_CHR_lem]
        >- metis_tac [ORD_CHR_lem]
        >- (qexists_tac `[c]` >> qexists_tac `s`
             >> rw []
             >> metis_tac [CHR_ORD]))
 >- (rw [regexp_lang_def] >> metis_tac [DOT_ASSOC])
 >- (rw [regexp_lang_def]
     >> rw_tac list_ss [SimpLHS,Once KSTAR_EQ_EPSILON_UNION_DOT,
                        DOT_UNION_RDISTRIB,DOT_EMPTYSTRING]
     >> metis_tac [DOT_ASSOC,IN_UNION,IN_DEF])
 >- (simp_tac list_ss [regexp_lang_def]
      >> Induct
      >> rw [EQ_IMP_THM,LIST_UNION_def,
             DOT_EMPTYSET,DOT_UNION_RDISTRIB,IN_DEF]));


val _ = export_theory();

(*
g `!cs1 cs2 cs3. regexp_lang (Cat (Or [Chset cs1 ; Chset cs2]) (Chset cs3))
                  = regexp_lang (Cat (Chset (charset_union cs1 cs2)) (Charset cs3))`;

val regexp_lang_or2 = Q.prove
(`!cs1 cs2 cs3.
     regexp_lang (Or [Chset cs1 ; Chset cs2]) =
     regexp_lang (Chset (charset_union cs1 cs2))`,
 rw_tac set_ss [SET_EQ_THM, regexp_lang_thm,charset_mem_union,EQ_IMP_THM]
 >> metis_tac[]);

*)
