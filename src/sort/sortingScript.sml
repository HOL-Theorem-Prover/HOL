(*---------------------------------------------------------------------------*
 *  General specification of sorting and correctness of quicksort            *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;
open combinTheory pairTheory relationTheory listTheory
     markerLib metisLib BasicProvers
     arithmeticTheory pred_setTheory rich_listTheory

val _ = new_theory "sorting";
val _ = set_grammar_ancestry ["rich_list"]

val _ = Defn.def_suffix := "_DEF";
val _ = Defn.ind_suffix := "_IND";

(*---------------------------------------------------------------------------*
 * What's a permutation? This definition uses universal quantification to    *
 * define it. There are other ways, which could be compared to this, e.g.    *
 * as an inductive definition, or as a particular kind of function.          *
 *---------------------------------------------------------------------------*)

Definition PERM_DEF:  PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2
End

Theorem PERM_REFL[simp]:  !L. PERM L L
Proof PROVE_TAC[PERM_DEF]
QED

Theorem PERM_INTRO:
  !x y. (x=y) ==> PERM x y
Proof PROVE_TAC[PERM_REFL]
QED

Theorem PERM_transitive:
  transitive PERM
Proof
 RW_TAC list_ss [relationTheory.transitive_def] THEN PROVE_TAC[PERM_DEF]
QED

Theorem PERM_TRANS:
  !x y z. PERM x y /\ PERM y z ==> PERM x z
Proof
 METIS_TAC [relationTheory.transitive_def, PERM_transitive]
QED

Theorem PERM_SYM:
  !l1 l2. PERM l1 l2 = PERM l2 l1
Proof PROVE_TAC [PERM_DEF]
QED

Theorem PERM_CONG:
  !(L1:'a list) L2 L3 L4.
     PERM L1 L3 /\ PERM L2 L4 ==>
     PERM (APPEND L1 L2) (APPEND L3 L4)
Proof PROVE_TAC [PERM_DEF,FILTER_APPEND_DISTRIB]
QED

Theorem CONS_APPEND[local] = PROVE [APPEND] “!L h. h::L = APPEND [h] L”

Theorem PERM_MONO:
  !l1 l2 x. PERM l1 l2 ==> PERM (x::l1) (x::l2)
Proof PROVE_TAC [CONS_APPEND,PERM_CONG, PERM_REFL]
QED

Theorem PERM_MONO_CONVERSE[local]:
  PERM (x::l1) (x::l2) ==> PERM l1 l2
Proof
  RW_TAC list_ss [PERM_DEF,FILTER]
  THEN POP_ASSUM (MP_TAC o Q.SPEC‘x'’)
  THEN RW_TAC list_ss []
QED

(* PERM (x::l1) (x::l2) <=> PERM l1 l2 *)
Theorem PERM_CONS_IFF[simp] =
  GEN_ALL(IMP_ANTISYM_RULE PERM_MONO_CONVERSE (SPEC_ALL PERM_MONO))

Theorem PERM_NIL[simp]:
  !L. (PERM L [] = (L=[])) /\ (PERM [] L = (L=[]))
Proof
  Cases THEN RW_TAC list_ss [PERM_DEF,FILTER]
  THEN Q.EXISTS_TAC ‘h’
  THEN RW_TAC list_ss []
QED

Theorem PERM_SING[simp]:
  (PERM L [x] <=> L = [x]) /\ (PERM [x] L <=> L = [x])
Proof
 Q_TAC SUFF_TAC ‘PERM L [x] = (L = [x])’
       THEN1 METIS_TAC [PERM_SYM] THEN
 Cases_on ‘L’ THEN SIMP_TAC (srw_ss()) [PERM_DEF, EQ_IMP_THM] THEN
 Q_TAC SUFF_TAC
       ‘(!y. (if y = h then h :: FILTER ($= h) t else FILTER ($= y) t) =
             (if y = x then [x] else [])) ==>
        (h = x) /\ (t = [])’
       THEN1 METIS_TAC [] THEN
 STRIP_TAC THEN
 ‘h = x’ by (POP_ASSUM (Q.SPEC_THEN ‘h’ MP_TAC) THEN SRW_TAC [][]) THEN
 SRW_TAC [][] THEN
 ‘!y. FILTER ($= y) t = []’ by METIS_TAC [CONS_11] THEN
 Cases_on ‘t’ THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [NOT_CONS_NIL]
QED

val MEM_FILTER_EQ = Q.prove
(‘!l x. MEM x l = ~(FILTER ($= x) l = [])’,
 Induct THEN SRW_TAC [][]);

val MEM_APPEND_SPLIT = Q.prove
(‘!L x. MEM x L ==> ?M N. L = M ++ x::N’,
 Induct THEN SRW_TAC [][] THENL [
   Q.EXISTS_TAC ‘[]’ THEN SRW_TAC [][],
   ‘?M N. L = M ++ x::N’ by METIS_TAC [] THEN
   Q.EXISTS_TAC ‘h::M’ THEN SRW_TAC [][]
 ]);

val FILTER_EQ_CONS_APPEND = Q.prove
(‘!M N x. FILTER ($= x) M ++ x::N = x::FILTER ($= x) M ++ N’,
 Induct THEN SRW_TAC [][])

val PERM_CONS_EQ_APPEND = Q.store_thm
("PERM_CONS_EQ_APPEND",
 ‘!L h. PERM (h::t) L = ?M N. (L = M ++ h::N) /\ PERM t (M ++ N)’,
 SRW_TAC [][PERM_DEF, FILTER_APPEND_DISTRIB, EQ_IMP_THM] THENL [
   ‘MEM h L’ by METIS_TAC [NOT_CONS_NIL, MEM_FILTER_EQ] THEN
   ‘?M N. L = M ++ h::N’ by METIS_TAC [MEM_APPEND_SPLIT] THEN
   MAP_EVERY Q.EXISTS_TAC [‘M’, ‘N’] THEN
   SRW_TAC [][] THEN Cases_on ‘x = h’ THEN
   FIRST_X_ASSUM (Q.SPEC_THEN ‘x’ MP_TAC) THEN
   SRW_TAC [][FILTER_APPEND_DISTRIB, FILTER_EQ_CONS_APPEND],
   SRW_TAC [][FILTER_APPEND_DISTRIB, FILTER_EQ_CONS_APPEND]
 ]);

val PERM_APPEND = Q.store_thm
("PERM_APPEND",
 ‘!l1 l2. PERM (APPEND l1 l2) (APPEND l2 l1)’,
 Induct THEN SRW_TAC [][PERM_CONS_EQ_APPEND] THEN METIS_TAC [])

val CONS_PERM = Q.store_thm
("CONS_PERM",
 ‘!x L M N. PERM L (APPEND M N)
            ==>
           PERM (x::L) (APPEND M (x::N))’,
METIS_TAC [PERM_CONS_EQ_APPEND]);


val APPEND_PERM_SYM = Q.store_thm
("APPEND_PERM_SYM",
 ‘!A B C. PERM (APPEND A B) C ==> PERM (APPEND B A) C’,
PROVE_TAC [PERM_TRANS, PERM_APPEND]);

val PERM_SPLIT_IF = Q.store_thm
("PERM_SPLIT_IF",
 ‘!P Q l. EVERY (\x. P x = ~ Q x) l ==>
   PERM l (APPEND (FILTER P l) (FILTER Q l))’,
 Induct_on ‘l’
 THEN RW_TAC list_ss [FILTER,PERM_REFL]
 THEN RES_TAC
 THEN ASM_SIMP_TAC std_ss [PERM_MONO, CONS_PERM]) ;

val PERM_SPLIT = Q.store_thm
("PERM_SPLIT",
 ‘!P l. PERM l (APPEND (FILTER P l) (FILTER ($~ o P) l))’,
 REPEAT GEN_TAC
 THEN irule PERM_SPLIT_IF
 THEN SIMP_TAC list_ss []) ;

(* ----------------------------------------------------------------------
    Alternative definition of PERM
   ---------------------------------------------------------------------- *)

Theorem FILTER_EQ_REP:
  FILTER ($= x) l = REPLICATE (LENGTH (FILTER ($= x) l)) x
Proof
  EVERY [Induct_on ‘l’,
         SIMP_TAC list_ss [rich_listTheory.REPLICATE], GEN_TAC,
         COND_CASES_TAC THENL [ BasicProvers.VAR_EQ_TAC, ALL_TAC],
         ASM_SIMP_TAC list_ss [rich_listTheory.REPLICATE] ]
QED

Theorem FILTER_EQ_LENGTHS_EQ:
  (LENGTH (FILTER ($= x) l1) = LENGTH (FILTER ($= x) l2)) ==>
    (FILTER ($= x) l1 = FILTER ($= x) l2)
Proof
  EVERY [ DISCH_TAC, ONCE_REWRITE_TAC [FILTER_EQ_REP],
          ASM_SIMP_TAC bool_ss [] ]
QED

Theorem PERM_alt:
  !L1 L2. PERM L1 L2 <=>
          !x. LENGTH (FILTER ($= x) L1) = LENGTH (FILTER ($= x) L2)
Proof
  EVERY [REWRITE_TAC [PERM_DEF], REPEAT GEN_TAC,
         EQ_TAC, REPEAT STRIP_TAC ]
  THENL [
    ASM_SIMP_TAC bool_ss [],
    irule FILTER_EQ_LENGTHS_EQ THEN ASM_REWRITE_TAC []
  ]
QED

(* ----------------------------------------------------------------------
    Inductive characterisation of PERM
   ---------------------------------------------------------------------- *)

(* things become slightly awkward because I avoid actually defining an
   inductive version of the permutation constant.  Instead, I do a bunch
   of proofs subject to an assumption "defining" perm to be the
   appropriate RHS; an alernative would be to define the constant, work
   with it, and then to delete it, so that it didn't get exported. *)

(* the definition assumption is 'backwards' so that it will be OK as an
   assumption and not cause perm to get rewritten out *)
val perm_t =
  “permdef :- !l1 l2:'a list.
                  perm l1 l2 =
                    (!P. P [] [] /\
                         (!x l1 l2. P l1 l2 ==> P (x::l1) (x::l2)) /\
                         (!x y l1 l2. P l1 l2 ==> P (x::y::l1) (y::x::l2)) /\
                         (!l1 l2 l3. P l1 l2 /\ P l2 l3 ==> P l1 l3) ==>
                         P l1 l2)”

(* perm's induction principle *)
val _ = print "Proving perm induction principle\n"
Theorem perm_ind[local]:
  ^perm_t ==> !P. P [] [] /\
                    (!x l1 l2. P l1 l2 ==> P (x::l1) (x::l2)) /\
                    (!x y l1 l2. P l1 l2 ==> P (x::y::l1) (y::x::l2)) /\
                    (!l1 l2 l3. P l1 l2 /\ P l2 l3 ==> P l1 l3) ==>
                    !l1 l2. perm l1 l2 ==> P l1 l2
Proof
  STRIP_TAC THEN LABEL_X_ASSUM "permdef" (REWRITE_TAC o C cons nil) THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []
QED
val perm_ind = UNDISCH perm_ind

val _ = print "Proving perm rules\n"
Theorem perm_rules:
  ^perm_t ==> perm [] [] /\
              (!x l1 l2. perm l1 l2 ==> perm (x::l1) (x::l2)) /\
              (!x y l1 l2. perm l1 l2 ==> perm (x::y::l1) (y::x::l2)) /\
              (!l1 l2 l3. perm l1 l2 /\ perm l2 l3 ==> perm l1 l3)
Proof
  STRIP_TAC THEN LABEL_X_ASSUM "permdef" (REWRITE_TAC o C cons nil) THEN
  REPEAT STRIP_TAC THEN
  REPEAT
    (FIRST_X_ASSUM (MP_TAC o SPEC “P : 'a list -> 'a list -> bool”)) THEN
  ASM_REWRITE_TAC [] THEN METIS_TAC []
QED

val perm_rules = UNDISCH perm_rules;

val _ = print "Proving perm symmetric, reflexive & transitive\n"

val perm_sym = prove(
  “^perm_t ==> (perm l1 l2 = perm l2 l1)”,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC
        ‘!l1 l2. perm l1 l2 ==> perm l2 l1’
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC perm_ind THEN
  SRW_TAC [][perm_rules] THEN METIS_TAC [perm_rules]);
val perm_sym = UNDISCH perm_sym

val perm_refl = prove(
  “^perm_t ==> !l. perm l l”,
  STRIP_TAC THEN Induct THEN SRW_TAC [][perm_rules]);
val perm_refl = UNDISCH perm_refl

val perm_trans = last (CONJUNCTS perm_rules)

val _ = print "Proving perm ==> PERM\n"

val perm_PERM = prove(
  “^perm_t ==> !l1 l2. perm l1 l2 ==> PERM l1 l2”,
  STRIP_TAC THEN HO_MATCH_MP_TAC perm_ind THEN SRW_TAC [][] THENL [
    SRW_TAC [][PERM_CONS_EQ_APPEND] THEN
    MAP_EVERY Q.EXISTS_TAC [‘[y]’, ‘l2’] THEN SRW_TAC [][] THEN
    MAP_EVERY Q.EXISTS_TAC [‘[]’, ‘l2’] THEN SRW_TAC [][],
    METIS_TAC [PERM_TRANS]
  ]);
val perm_PERM = UNDISCH perm_PERM

val _ = print "Proving perm has primitive recursive characterisation\n"

val perm_cons_append' = Q.prove
  (‘^perm_t ==> !M. perm (h::M ++ N) (M ++ [h] ++ N)’,
  STRIP_TAC >> ASSUME_TAC perm_rules >> ASSUME_TAC perm_refl >>
    RULE_L_ASSUM_TAC CONJUNCTS >>
    Induct >> ASM_SIMP_TAC list_ss [] >> GEN_TAC >>
    MATCH_MP_TAC perm_trans >> Q.EXISTS_TAC ‘h'::h::(M ++ N)’ >>
    RES_TAC >> ASM_SIMP_TAC list_ss []) ;

val perm_cons_append = prove(
  “^perm_t ==> !l1 l2. perm l1 l2 ==>
                        !M N. (l2 = M ++ N) ==>
                              !h. perm (h::l1) (M ++ [h] ++ N)”,
  REPEAT STRIP_TAC >> MATCH_MP_TAC perm_trans >>
    Q.EXISTS_TAC ‘h :: l2’ >> CONJ_TAC
  THENL [ ASSUME_TAC perm_rules >> ASM_SIMP_TAC list_ss [],
    BasicProvers.VAR_EQ_TAC >>
    MATCH_ACCEPT_TAC (REWRITE_RULE [APPEND] (UNDISCH perm_cons_append')) ]) ;

val perm_cons_append =
    SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [] (UNDISCH perm_cons_append)

val _ = print "Proving PERM ==> perm\n"

val PERM_perm = prove(
  “^perm_t ==> !l1 l2. PERM l1 l2 ==> perm l1 l2”,
  STRIP_TAC THEN Induct THEN SRW_TAC [][perm_rules, PERM_CONS_EQ_APPEND] THEN
  METIS_TAC [perm_cons_append])
val PERM_perm = UNDISCH PERM_perm

val perm_elim = GEN_ALL
                  (IMP_ANTISYM_RULE (SPEC_ALL perm_PERM) (SPEC_ALL PERM_perm))
fun remove_eq_asm th = let
  val th0 =
      CONV_RULE (LAND_CONV
                   (SIMP_CONV (bool_ss ++ boolSimps.ETA_ss)
                              [GSYM FUN_EQ_THM, markerTheory.label_def]))
                (DISCH_ALL (REWRITE_RULE [perm_elim] th))
in
  CONV_RULE Unwind.UNWIND_FORALL_CONV
            (GEN “perm : 'a list -> 'a list -> bool” th0)
end

val PERM_IND = save_thm("PERM_IND", remove_eq_asm perm_ind)

val PERM_MONO' = PERM_MONO |> SPEC_ALL |> Q.GENL [‘x’, ‘l1’, ‘l2’]

val PERM_SWAP_AT_FRONT = store_thm(
  "PERM_SWAP_AT_FRONT",
  “PERM (x::y::l1) (y::x::l2) = PERM l1 l2”,
  METIS_TAC [remove_eq_asm (List.nth(CONJUNCTS perm_rules, 2)),
             PERM_REFL, PERM_TRANS, PERM_CONS_IFF]);

val PERM_SWAP_L_AT_FRONT = store_thm(
  "PERM_SWAP_L_AT_FRONT",
  “!x y. PERM (x++y++l1) (y++x++l2) = PERM l1 l2”,
  SIMP_TAC list_ss [PERM_alt, FILTER_APPEND_DISTRIB]) ;

(* alternative proof of PERM_SWAP_AT_FRONT
val PERM_SWAP_AT_FRONT' = SPECL [``[x]``, ``[y]``] PERM_SWAP_L_AT_FRONT ;

val PERM_SWAP_AT_FRONT = save_thm( "PERM_SWAP_AT_FRONT",
  SIMP_RULE list_ss [] PERM_SWAP_AT_FRONT') ;
*)

val PERM_SWAP = PERM_SWAP_AT_FRONT |> EQ_IMP_RULE |> #2
                                   |> Q.GENL [‘x’, ‘y’, ‘l1’, ‘l2’]

val PERM_NILNIL = prove(“PERM [][]”, SRW_TAC[][])

val PERM_STRONG_IND = save_thm(
  "PERM_STRONG_IND",
  IndDefLib.derive_strong_induction(
    LIST_CONJ [PERM_NILNIL, PERM_MONO', PERM_SWAP, PERM_TRANS],
    PERM_IND))
val _ = IndDefLib.export_rule_induction "PERM_STRONG_IND"

val PERM_LENGTH = Q.store_thm(
  "PERM_LENGTH",
  ‘!l1 l2. PERM l1 l2 ==> (LENGTH l1 = LENGTH l2)’,
  HO_MATCH_MP_TAC PERM_IND THEN SRW_TAC [][]);

val PERM_MEM_EQ = Q.store_thm(
  "PERM_MEM_EQ",
  ‘!l1 l2. PERM l1 l2 ==> !x. MEM x l1 = MEM x l2’,
  HO_MATCH_MP_TAC PERM_IND THEN SRW_TAC [][AC DISJ_ASSOC DISJ_COMM]);

Theorem PERM_LIST_TO_SET:
  !l1 l2. PERM l1 l2 ==> (set l1 = set l2)
Proof SRW_TAC[][EXTENSION,PERM_MEM_EQ]
QED

Theorem PERM_BIJ:
  !l1 l2. PERM l1 l2 ==>
          ?f. (BIJ f (count(LENGTH l1)) (count(LENGTH l1)) /\
              (l2 = GENLIST (\i. EL (f i) l1) (LENGTH l1)))
Proof
  Induct_on ‘PERM’ >> simp[BIJ_EMPTY] >> conj_tac
  >- (
    simp[GENLIST_CONS] >>
    srw_tac[][combinTheory.o_DEF] >>
    qexists_tac‘\i. case i of 0 => 0 | SUC i => SUC(f i)’ >>
    fs[BIJ_IFF_INV, EL_CONS, PRE_SUB1] >>
    conj_tac >- (Cases >> simp[]) >>
    qexists_tac ‘\i. case i of 0 => 0 | SUC i => SUC(g i)’ >>
    conj_tac >- (Cases >> simp[]) >>
    conj_tac >- (Cases >> simp[]) >>
    (Cases >> simp[])
  ) >> conj_tac >- (
    simp[GENLIST_CONS] >>
    srw_tac[][combinTheory.o_DEF] >>
    qexists_tac
      ‘\i. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(f n))’ >>
    simp[PRE_SUB1,EL_CONS] >>
    REWRITE_TAC[ONE] >> simp[] >> fs[BIJ_IFF_INV] >>
    conj_tac >- (Cases >> simp[]>> Cases_on‘n’>>simp[]) >>
    qexists_tac
      ‘\i. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(g n))’ >>
    simp[] >>
    conj_tac >- (Cases >> simp[]>> Cases_on‘n’>>simp[]) >>
    conj_tac >- (Cases >> simp[]>> TRY(Cases_on‘n’)>>simp[] >>
                 REWRITE_TAC[ONE]>>simp[]) >>
    (Cases >> simp[]>> TRY(Cases_on‘n’)>>simp[] >> REWRITE_TAC[ONE]>>simp[])
  ) >>
  ntac 2 (srw_tac[][LENGTH_GENLIST]) >>
  simp[LIST_EQ_REWRITE,EL_GENLIST] >>
  full_simp_tac(srw_ss())[LENGTH_GENLIST] >>
  qexists_tac‘f o f'’ >>
  simp[combinTheory.o_DEF] >>
  full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
  qexists_tac‘g' o g’ >>
  simp[combinTheory.o_DEF]
QED

Theorem PERM_BIJ_IFF:
  PERM l1 l2 <=>
  ?p. p PERMUTES count (LENGTH l1) /\
      l2 = GENLIST (\i. EL (p i) l1) (LENGTH l1)
Proof
  eq_tac
  >- metis_tac[PERM_BIJ]
  \\ rw[] \\ fs[]
  \\ pop_assum mp_tac
  \\ qid_spec_tac‘p’
  \\ qid_spec_tac‘l1’
  \\ Induct
  \\ rw[]
  \\ simp[PERM_CONS_EQ_APPEND]
  \\ pop_assum mp_tac
  \\ rw[BIJ_IFF_INV]
  \\ qexists_tac‘GENLIST (\i. EL (p i - 1) l1) (g 0)’
  \\ qexists_tac‘GENLIST (\i. EL (p (g 0 + i + 1) - 1) l1)
                         (LENGTH l1 - g 0)’
  \\ simp[LIST_EQ_REWRITE, GSYM CONJ_ASSOC]
  \\ conj_tac
  >- ( rpt(first_x_assum(qspec_then‘0’mp_tac)) \\ simp[] )
  \\ conj_tac
  >- (
    simp[EL_APPEND_EQN]
    \\ rpt strip_tac
    \\ Cases_on‘x < g 0’ \\ gs[]
    >- (
      Cases_on‘p x’ \\ gs[]
      \\ Cases_on‘g 0’ \\ gs[]
      \\ metis_tac[prim_recTheory.LESS_REFL] )
    \\ Cases_on‘x = g 0’ \\ gs[]
    \\ Cases_on‘p x’ \\ gs[]
    \\ metis_tac[prim_recTheory.LESS_0])
  \\ qspecl_then[‘\i. EL (p (if i < g 0 then i else i + 1) - 1) l1’,
                 ‘LENGTH l1 - g 0’, ‘g 0’] (mp_tac o SYM) GENLIST_APPEND
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac‘l2 ++ l3’
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac‘l4 ++ l3’
  \\ ‘l4 = l2’ by ( simp[Abbr‘l4’, Abbr‘l2’, LIST_EQ_REWRITE] )
  \\ ‘g 0 < SUC (LENGTH l1)’ by gs[]
  \\ ‘g 0 <= LENGTH l1’ by simp[]
  \\ simp[Abbr‘l4’, Abbr‘l2’]
  \\ qho_match_abbrev_tac‘PERM _ (GENLIST (\i. EL (q i) l1) _)’
  \\ first_x_assum irule
  \\ simp[BIJ_DEF, SURJ_DEF, INJ_DEF, GSYM CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    simp[Abbr‘q’]
    \\ rpt strip_tac
    \\ ‘p x < SUC (LENGTH l1)’ by gs[]
    \\ ‘p (x + 1) < SUC (LENGTH l1)’ by gs[]
    \\ rw[] )
  \\ simp[]
  \\ reverse conj_tac
  >- (
    simp[Abbr‘q’]
    \\ rpt strip_tac
    \\ qexists_tac‘if g (x + 1) < g 0 then g (x + 1) else g (x + 1) - 1’
    \\ IF_CASES_TAC \\ simp[]
    \\ ‘g (x + 1) < SUC (LENGTH l1)’by gs[]
    \\ simp[]
    \\ Cases_on‘g (x + 1) = g 0’ \\ gs[]
    \\ ‘(0 < SUC (LENGTH l1)) /\ x + 1 < SUC (LENGTH l1)’ by gs[]
    \\ ‘0 = x + 1’ by metis_tac[]
    \\ fs[] )
  \\ simp[Abbr‘q’]
  \\ rpt strip_tac
  \\ ‘(x + 1 < SUC (LENGTH l1)) /\ y + 1 < SUC (LENGTH l1)’ by gs[]
  \\ wlog_tac ‘x < y’ [‘x’, ‘y’]
  >- (
    CCONTR_TAC
    \\ first_x_assum(qspecl_then[‘y’,‘x’]mp_tac)
    \\ simp[] )
  \\ ‘x < SUC (LENGTH l1)’ by gs[]
  \\ ‘y < SUC (LENGTH l1)’ by gs[]
  \\ Cases_on‘y < g 0’
  >- (
    fs[]
    \\ Cases_on‘p x’ \\ fs[]
    >- ( ‘y < x’ by metis_tac[] \\ fs[] )
    \\ Cases_on‘p y’ \\ fs[]
    >- ( ‘y < y’ by metis_tac[] \\ fs[] )
    \\ ‘x = y’ by metis_tac[] \\ fs[] )
  \\ qpat_x_assum‘p _ - _ = _’mp_tac
  \\ Cases_on‘x < g 0’ \\ simp[]
  >- (
    Cases_on‘p x’ \\ simp[]
    >- ( ‘x < x’ by metis_tac[] \\ fs[] )
    \\ Cases_on‘p (y + 1)’ \\ simp[]
    >- ( ‘g 0 = y + 1’ by metis_tac[] \\ gs[] )
    \\ strip_tac
    \\ ‘x = y + 1’ by metis_tac[] \\ fs[] )
  \\ Cases_on‘p (x + 1)’ \\ simp[]
  >- ( ‘g 0 = x + 1’ by metis_tac[] \\ gs[] )
  \\ Cases_on‘p (y + 1)’ \\ simp[]
  >- ( ‘g 0 = y + 1’ by metis_tac[] \\ gs[] )
  \\ strip_tac
  \\ ‘x + 1 = y + 1’ by metis_tac[]
  \\ fs[]
QED

Theorem PERM_EVERY:
  !ls ls'. PERM ls ls' ==> (EVERY P ls <=> EVERY P ls')
Proof Induct_on ‘PERM’ >> srw_tac[][] >> metis_tac[]
QED


(*---------------------------------------------------------------------------*
 * The idea of sortedness requires a "permutation" relation for lists, and   *
 * a "chain" predicate that holds just when the relation R holds between     *
 * all adjacent elements of the list.                                        *
 *---------------------------------------------------------------------------*)

Definition SORTED_DEF[simp]:
   (SORTED R [] = T) /\
   (SORTED R [x] = T) /\
   (SORTED R (x::y::rst) <=> R x y /\ SORTED R (y::rst))
End

Definition SORTS_DEF:
  SORTS f R <=> !l. PERM l (f R l) /\ SORTED R (f R l)
End

Theorem SORTED_adjacent:
  SORTED R L <=> adjacent L RSUBSET R
Proof
  Induct_on ‘L’ >> simp[relationTheory.RSUBSET] >>
  rename [‘SORTED R L’] >> Cases_on ‘L’ >>
  simp[adjacent_iff, DISJ_IMP_THM, FORALL_AND_THM,
       relationTheory.RSUBSET]
QED


(*---------------------------------------------------------------------------*
 *    When consing onto a sorted list yields a sorted list                   *
 *---------------------------------------------------------------------------*)

Theorem SORTED_EQ:
  !R L x.
    transitive R ==> (SORTED R (x::L) <=> SORTED R L /\ !y. MEM y L ==> R x y)
Proof
Induct_on ‘L’
 THEN RW_TAC list_ss [SORTED_DEF,MEM]
 THEN PROVE_TAC [relationTheory.transitive_def]
QED


(*---------------------------------------------------------------------------*
 *       When appending sorted lists gives a sorted list.                    *
 *---------------------------------------------------------------------------*)

Theorem SORTED_APPEND:
 !R L1 L2.
 transitive R ==>
 (SORTED R (L1 ++ L2) <=> SORTED R L1 /\ SORTED R L2 /\
                          (!x y. MEM x L1 ==> MEM y L2 ==> R x y))
Proof
 Induct_on ‘L1’ \\ fs [SORTED_EQ] \\ metis_tac []
QED

Theorem SORTED_APPEND_IMP:
 !R L1 L2.
     transitive R
 /\  SORTED R L1
 /\  SORTED R L2
 /\ (!x y. MEM x L1 /\ MEM y L2 ==> R x y)
  ==>
    SORTED R (L1 ++ L2)
Proof
Induct_on ‘L1’
  THEN SRW_TAC [boolSimps.CONJ_ss][SORTED_EQ]
  THEN PROVE_TAC []
QED

Theorem SORTED_APPEND_GEN:
  !R L1 L2. SORTED R (L1 ++ L2) <=>
              SORTED R L1 /\ SORTED R L2 /\
                ((L1 = []) \/ (L2 = []) \/ (R (LAST L1) (HD L2)))
Proof
  REPEAT STRIP_TAC >> Induct_on ‘L1’ >>
    ASM_SIMP_TAC list_ss [SORTED_DEF] >> GEN_TAC >>
    Cases_on ‘L1’ >> Cases_on ‘L2’ >>
    FULL_SIMP_TAC list_ss [SORTED_DEF]
  THENL [
    SIMP_TAC bool_ss [CONJ_COMM],
    SIMP_TAC bool_ss [CONJ_ASSOC] ]
QED

(*---------------------------------------------------------------------------
                 Partition a list by a predicate.
 ---------------------------------------------------------------------------*)

Definition PART_DEF:
      (PART P [] l1 l2 = (l1,l2))
  /\  (PART P (h::rst) l1 l2 =
          if P h then PART P rst (h::l1) l2
                 else PART P rst  l1  (h::l2))
End

(*---------------------------------------------------------------------------
              Theorems about "PART"
 ---------------------------------------------------------------------------*)

val PART_LENGTH = Q.store_thm
("PART_LENGTH",
 ‘!P L l1 l2 p q.
    ((p,q) = PART P L l1 l2)
    ==> (LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q)’,
Induct_on ‘L’
  THEN RW_TAC list_ss [PART_DEF]
  THEN RES_THEN MP_TAC
  THEN RW_TAC list_ss []);


val PART_LENGTH_LEM = Q.store_thm
("PART_LENGTH_LEM",
‘!P L l1 l2 p q.
    ((p,q) = PART P L l1 l2)
    ==>  LENGTH p <= LENGTH L + LENGTH l1 + LENGTH l2 /\
         LENGTH q <= LENGTH L + LENGTH l1 + LENGTH l2’,
RW_TAC bool_ss []
 THEN IMP_RES_THEN MP_TAC PART_LENGTH
 THEN RW_TAC list_ss []);


(*---------------------------------------------------------------------------
       Each element in the positive and negative partitions has
       the desired property. The simplifier loops on some of the
       subgoals here, so we have to take round-about measures.
 ---------------------------------------------------------------------------*)

val PARTs_HAVE_PROP = Q.store_thm
("PARTs_HAVE_PROP",
 ‘!P L A B l1 l2.
   ((A,B) = PART P L l1 l2) /\
   (!x. MEM x l1 ==> P x) /\ (!x. MEM x l2 ==> ~P x)
    ==>
      (!z. MEM z A ==>  P z) /\ (!z. MEM z B ==> ~P z)’,
Induct_on ‘L’
 THEN REWRITE_TAC [PART_DEF,CLOSED_PAIR_EQ] THENL
 [PROVE_TAC[],
  POP_ASSUM (fn th => REPEAT GEN_TAC THEN
     COND_CASES_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th)
   THENL [MAP_EVERY Q.EXISTS_TAC [‘h::l1’, ‘l2’],
          MAP_EVERY Q.EXISTS_TAC [‘l1’, ‘h::l2’]]
  THEN RW_TAC list_ss [MEM] THEN RW_TAC bool_ss []]);


(*---------------------------------------------------------------------------*)
(* Appending the two partitions of the original list is a permutation of the *)
(* original list.                                                            *)
(*---------------------------------------------------------------------------*)

val PART_PERM = Q.prove
(‘!P L a1 a2 l1 l2.
   ((a1,a2) = PART P L l1 l2)
      ==>
   PERM (L ++ (l1 ++ l2)) (a1 ++ a2)’,
Induct_on ‘L’
  THEN RW_TAC list_ss [PART_DEF, PERM_REFL]
  THEN RES_TAC THEN MATCH_MP_TAC PERM_TRANS THENL
  [Q.EXISTS_TAC ‘APPEND L (APPEND (h::l1) l2)’,
   Q.EXISTS_TAC ‘APPEND L (APPEND l1 (h::l2))’]
  THEN PROVE_TAC [APPEND,APPEND_ASSOC,CONS_PERM,PERM_REFL]);

(*---------------------------------------------------------------------------
     Everything in the partitions occurs in the original list, and
     vice-versa. The goal has been generalized.
 ---------------------------------------------------------------------------*)

val PART_MEM = Q.store_thm
("PART_MEM",
 ‘!P L a1 a2 l1 l2.
     ((a1,a2) = PART P L l1 l2)
       ==>
      !x. MEM x (L ++ (l1 ++ l2)) = MEM x (a1 ++ a2)’,
  METIS_TAC [PART_PERM, PERM_MEM_EQ]);

(*---------------------------------------------------------------------------
     A packaged version of PART. Most theorems about PARTITION
     will be instances of theorems about PART.
 ---------------------------------------------------------------------------*)

Definition PARTITION_DEF: PARTITION P l = PART P l [] []
End

(*---------------------------------------------------------------------------*
 *      Quicksort                                                            *
 *---------------------------------------------------------------------------*)

Definition QSORT_DEF:
  (QSORT ord [] = []) /\
  (QSORT ord (h::t) =
       let (l1,l2) = PARTITION (\y. ord y h) t
       in
         QSORT ord l1 ++ [h] ++ QSORT ord l2)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’
     THEN RW_TAC list_ss [o_DEF,PARTITION_DEF]
     THEN IMP_RES_THEN MP_TAC PART_LENGTH_LEM
     THEN RW_TAC list_ss []
End

(*---------------------------------------------------------------------------*
 *           Properties of QSORT                                            *
 *---------------------------------------------------------------------------*)

val QSORT_MEM = Q.store_thm
("QSORT_MEM",
 ‘!R L x. MEM x (QSORT R L) = MEM x L’,
recInduct QSORT_IND
 THEN RW_TAC bool_ss [QSORT_DEF,PARTITION_DEF]
 THEN RW_TAC list_ss []
 THEN Q.PAT_X_ASSUM ‘_ = _’ (MP_TAC o MATCH_MP PART_MEM o SYM)
 THEN RW_TAC list_ss [] THEN PROVE_TAC []);

(*---------------------------------------------------------------------------*)
(* The result list is a permutation of the input list.                       *)
(*---------------------------------------------------------------------------*)


val QSORT_PERM = Q.store_thm
("QSORT_PERM",
 ‘!R L. PERM L (QSORT R L)’,
 recInduct QSORT_IND
  THEN RW_TAC list_ss [QSORT_DEF,PERM_REFL,PARTITION_DEF]
  THEN REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
  THEN MATCH_MP_TAC CONS_PERM
  THEN MATCH_MP_TAC PERM_TRANS
  THEN Q.EXISTS_TAC ‘l1 ++ l2’
  THEN RW_TAC std_ss [] THENL
  [METIS_TAC [APPEND,APPEND_NIL,PART_PERM],
   METIS_TAC [PERM_CONG]]);


Theorem LENGTH_QSORT[simp]:
  LENGTH (QSORT R l) = LENGTH l
Proof
  metis_tac[QSORT_PERM, PERM_LENGTH]
QED

(*---------------------------------------------------------------------------
 * The result list is sorted.
 *---------------------------------------------------------------------------*)

Theorem QSORT_SORTED:
  !R L. transitive R /\ total R ==> SORTED R (QSORT R L)
Proof
 recInduct QSORT_IND
  THEN RW_TAC bool_ss [QSORT_DEF, SORTED_DEF, PARTITION_DEF]
  THEN REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
  THEN MATCH_MP_TAC SORTED_APPEND_IMP
  THEN POP_ASSUM (ASSUME_TAC o SYM)
  THEN IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) SORTED_EQ
  THEN RW_TAC list_ss [MEM_FILTER,MEM,QSORT_MEM]
  THEN ((RES_TAC THEN NO_TAC) ORELSE ALL_TAC)
  THEN Q.PAT_X_ASSUM ‘_ = _’ (MP_TAC o MATCH_MP
        (REWRITE_RULE[PROVE [] (Term ‘x/\y/\z ==> w <=> x ==> y/\z ==> w’)]
            PARTs_HAVE_PROP))
  THEN RW_TAC std_ss [MEM]
  THEN PROVE_TAC [transitive_def,total_def]
QED


(*---------------------------------------------------------------------------
 * Bring everything together.
 *---------------------------------------------------------------------------*)

val QSORT_SORTS = Q.store_thm
("QSORT_SORTS",
 ‘!R. transitive R /\ total R ==> SORTS QSORT R’,
  PROVE_TAC [SORTS_DEF, QSORT_PERM, QSORT_SORTED]);


(*---------------------------------------------------------------------------
 * Theorems about Permutations. Added by Thomas Tuerk. 19 March 2009
 *---------------------------------------------------------------------------*)

val PERM_APPEND_IFF = store_thm ("PERM_APPEND_IFF",
“(!l:'a list l1 l2. PERM (l++l1) (l++l2) = PERM l1 l2) /\
  (!l:'a list l1 l2. PERM (l1++l) (l2++l) = PERM l1 l2)”,
  SIMP_TAC list_ss [PERM_alt, FILTER_APPEND_DISTRIB]) ;

val PERM_SINGLE_SWAP_DEF = Define ‘PERM_SINGLE_SWAP l1 l2 =
    ?x1 x2 x3. (l1 = x1 ++ x2 ++ x3) /\ (l2 = x1 ++ x3 ++ x2)’;

val PERM_SINGLE_SWAP_SYM = store_thm ("PERM_SINGLE_SWAP_SYM",
“!l1 l2. PERM_SINGLE_SWAP l1 l2 = PERM_SINGLE_SWAP l2 l1”,
  PROVE_TAC[PERM_SINGLE_SWAP_DEF]);

val PERM_SINGLE_SWAP_I = Q.store_thm ("PERM_SINGLE_SWAP_I",
  ‘PERM_SINGLE_SWAP (x1 ++ x2 ++ x3) (x1 ++ x3 ++ x2)’,
  PROVE_TAC [PERM_SINGLE_SWAP_DEF]) ;

val PERM_SINGLE_SWAP_APPEND = save_thm ("PERM_SINGLE_SWAP_APPEND",
  REWRITE_RULE [APPEND] (Q.INST [‘x1’ |-> ‘NIL’] PERM_SINGLE_SWAP_I)) ;

val PERM_SINGLE_SWAP_REFL = save_thm ("PERM_SINGLE_SWAP_REFL",
  GEN_ALL (REWRITE_RULE [APPEND, APPEND_NIL]
    (Q.INST [‘x2’ |-> ‘NIL’, ‘x3’ |-> ‘l’] PERM_SINGLE_SWAP_APPEND))) ;

val [_, TC_TRANS] = CONJUNCTS (SPEC_ALL TC_RULES) ;

val PERM_SINGLE_SWAP_CONS = Q.store_thm ("PERM_SINGLE_SWAP_CONS",
  ‘PERM_SINGLE_SWAP M N ==> PERM_SINGLE_SWAP (x :: M) (x :: N)’,
  SIMP_TAC list_ss [PERM_SINGLE_SWAP_DEF] >> REPEAT STRIP_TAC >>
    Q.EXISTS_TAC ‘x :: x1’ >> Q.EXISTS_TAC ‘x2’ >> Q.EXISTS_TAC ‘x3’ >>
    ASM_SIMP_TAC list_ss [] ) ;

Theorem PERM_SINGLE_SWAP_TC_CONS:
  !M N. TC PERM_SINGLE_SWAP M N ==> TC PERM_SINGLE_SWAP (x :: M) (x :: N)
Proof
  HO_MATCH_MP_TAC TC_INDUCT >> reverse CONJ_TAC >- MATCH_ACCEPT_TAC TC_TRANS >>
  rpt strip_tac >> irule TC_SUBSET >>
  irule PERM_SINGLE_SWAP_CONS >> FIRST_ASSUM ACCEPT_TAC
QED

val PERM_is_TC_PSS = Q.prove (
  ‘!l1 l2. PERM l1 l2 ==> TC PERM_SINGLE_SWAP l1 l2’,
  Induct THEN1 (SIMP_TAC list_ss [PERM_NIL] >>
      irule TC_SUBSET >> irule PERM_SINGLE_SWAP_REFL) >>
    REPEAT STRIP_TAC >> IMP_RES_TAC PERM_CONS_EQ_APPEND >>
    BasicProvers.VAR_EQ_TAC >> irule TC_TRANS >>
    Q.EXISTS_TAC ‘(h :: N) ++ M’ >> CONJ_TAC
  THENL [
    SIMP_TAC list_ss [] >> irule PERM_SINGLE_SWAP_TC_CONS >>
      RES_TAC >> irule TC_TRANS >> Q.EXISTS_TAC ‘M ++ N’ >>
      CONJ_TAC THEN1 POP_ASSUM ACCEPT_TAC >>
      irule TC_SUBSET >> irule PERM_SINGLE_SWAP_APPEND,
    irule TC_SUBSET >> irule PERM_SINGLE_SWAP_APPEND ] ) ;

val PSS_is_PERM = Q.prove (
  ‘!l1 l2. PERM_SINGLE_SWAP l1 l2 ==> PERM l1 l2’,
  SIMP_TAC list_ss [PERM_SINGLE_SWAP_DEF, PERM_alt] >>
    REPEAT STRIP_TAC >>
    ASM_SIMP_TAC list_ss [FILTER_APPEND_DISTRIB]) ;

val TC_PSS_is_PERM =
  REWRITE_RULE [MATCH_MP transitive_TC_identity PERM_transitive]
  (MATCH_MP TC_MONOTONE PSS_is_PERM) ;

val PERM_TC = Q.store_thm ("PERM_TC",
  ‘PERM = TC PERM_SINGLE_SWAP’,
  SIMP_TAC std_ss [FUN_EQ_THM] >> REPEAT STRIP_TAC >> EQ_TAC
  THENL [ MATCH_ACCEPT_TAC PERM_is_TC_PSS,
    MATCH_ACCEPT_TAC TC_PSS_is_PERM ]) ;

val PERM_RTC = store_thm ("PERM_RTC",
    “PERM = RTC PERM_SINGLE_SWAP”,

REWRITE_TAC[GSYM (CONJUNCT2 (SIMP_RULE std_ss [FORALL_AND_THM] TC_RC_EQNS)),
            PERM_TC] THEN
AP_TERM_TAC THEN
SIMP_TAC std_ss [RC_DEF, FUN_EQ_THM] THEN
PROVE_TAC[PERM_SINGLE_SWAP_REFL]);


val PERM_EQC = store_thm ("PERM_EQC",
    “PERM = EQC PERM_SINGLE_SWAP”,

‘SC PERM_SINGLE_SWAP = PERM_SINGLE_SWAP’ by (
   SIMP_TAC std_ss [FUN_EQ_THM, SC_DEF, PERM_SINGLE_SWAP_SYM]
) THEN
ASM_REWRITE_TAC[EQC_DEF, GSYM PERM_TC] THEN
SIMP_TAC std_ss [RC_DEF, FUN_EQ_THM] THEN
PROVE_TAC[PERM_REFL]);



val PERM_lift_TC_RULE =
  (GEN_ALL o
   SIMP_RULE std_ss [GSYM PERM_TC, PERM_SINGLE_SWAP_DEF,
                     GSYM LEFT_FORALL_IMP_THM,
                     GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] o
   Q.ISPEC ‘PERM_SINGLE_SWAP’ o
   Q.GEN ‘R’);


val PERM_lifts_transitive_relations = save_thm (
"PERM_lifts_transitive_relations",
PERM_lift_TC_RULE TC_lifts_transitive_relations);

val PERM_lifts_equalities = save_thm (
"PERM_lifts_equalities",
PERM_lift_TC_RULE TC_lifts_equalities);

val PERM_lifts_invariants = save_thm (
"PERM_lifts_invariants",
PERM_lift_TC_RULE TC_lifts_invariants);


val PERM_lifts_monotonicities = store_thm (
"PERM_lifts_monotonicities",
“!f. (!x1:'a list x2 x3. ?x1':'b list x2' x3'.
       (f (x1 ++ x2 ++ x3) = x1' ++ x2' ++ x3') /\
       (f (x1 ++ x3 ++ x2) = x1' ++ x3' ++ x2')) ==>
      !x y. PERM x y ==> PERM (f x) (f y)”,
GEN_TAC THEN STRIP_TAC THEN
MATCH_MP_TAC PERM_lifts_transitive_relations THEN
REWRITE_TAC[PERM_transitive] THEN
REPEAT GEN_TAC THEN
POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x1’,‘x2’,‘x3’])) THEN
ASM_REWRITE_TAC[PERM_APPEND, PERM_APPEND_IFF, GSYM APPEND_ASSOC]);


val PERM_EQUIVALENCE = store_thm (
"PERM_EQUIVALENCE",
“equivalence PERM”,
REWRITE_TAC [PERM_EQC, EQC_EQUIVALENCE]);

val PERM_EQUIVALENCE_ALT_DEF = store_thm(
"PERM_EQUIVALENCE_ALT_DEF",
“!x y. PERM x y = (PERM x = PERM y)”,
SIMP_TAC std_ss [GSYM ALT_equivalence,
                 PERM_EQUIVALENCE]);

val ALL_DISTINCT_PERM = store_thm ("ALL_DISTINCT_PERM",
   “!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)”,
   MATCH_MP_TAC PERM_lifts_equalities THEN
   SIMP_TAC list_ss [ALL_DISTINCT_APPEND] THEN
   PROVE_TAC[]);


val PERM_ALL_DISTINCT = store_thm ("PERM_ALL_DISTINCT",
“!l1 l2. (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ (!x. MEM x l1 = MEM x l2)) ==>
           PERM l1 l2”,

SIMP_TAC std_ss [ALL_DISTINCT_FILTER, PERM_DEF, MEM_FILTER_EQ] THEN
METIS_TAC[]);

val ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST = store_thm(
"ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST",
“!ls. ALL_DISTINCT ls = PERM ls (SET_TO_LIST (set ls))”,
SRW_TAC[][EQ_IMP_THM] THEN1 (
  MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  SRW_TAC[][] ) THEN
IMP_RES_TAC ALL_DISTINCT_PERM THEN
FULL_SIMP_TAC (srw_ss()) [])

Theorem PERM_SET_TO_LIST_INSERT:
  FINITE s ==>
    PERM (SET_TO_LIST (x INSERT s))
         (if x IN s then SET_TO_LIST s else x :: SET_TO_LIST s)
Proof
  SRW_TAC[][] THEN1 (‘x INSERT s = s’ by (SRW_TAC[][EXTENSION] \\ METIS_TAC[])
                     THEN SRW_TAC[][])
  THEN Cases_on ‘CHOICE (x INSERT s) = x’
  THEN1 (
    SRW_TAC[][Once SET_TO_LIST_THM]
    THEN ‘REST (x INSERT s) = s’ by (
      Q.SPEC_THEN‘x INSERT s’MP_TAC CHOICE_INSERT_REST
      THEN ASM_SIMP_TAC(srw_ss())[]
      THEN Q.SPEC_THEN‘x INSERT s’MP_TAC (CONV_RULE SWAP_FORALL_CONV IN_REST)
      THEN SRW_TAC[][EXTENSION]
      THEN METIS_TAC[])
    THEN SRW_TAC[][])
  THEN SRW_TAC[][Once SET_TO_LIST_THM]
  THEN MATCH_MP_TAC PERM_ALL_DISTINCT
  THEN SRW_TAC[][CHOICE_NOT_IN_REST]
  THEN METIS_TAC[CHOICE_INSERT_REST, NOT_EMPTY_INSERT, IN_INSERT]
QED

val PERM_MAP = store_thm ("PERM_MAP",
“!f l1 l2. PERM l1 l2 ==> PERM (MAP f l1) (MAP f l2)”,
   GEN_TAC THEN
   MATCH_MP_TAC PERM_lifts_monotonicities THEN
   REWRITE_TAC[MAP_APPEND] THEN
   PROVE_TAC[]);

val PERM_SUM = Q.store_thm(
"PERM_SUM",
‘!l1 l2. PERM l1 l2 ==> (SUM l1 = SUM l2)’,
HO_MATCH_MP_TAC PERM_IND THEN
SRW_TAC [][] THEN DECIDE_TAC);

val PERM_FILTER = store_thm ("PERM_FILTER",
“!P l1 l2. PERM l1 l2 ==> (PERM (FILTER P l1) (FILTER P l2))”,
   GEN_TAC THEN
   MATCH_MP_TAC PERM_lifts_monotonicities THEN
   REWRITE_TAC[FILTER_APPEND_DISTRIB] THEN
   PROVE_TAC []);

val PERM_REVERSE = Q.store_thm(
  "PERM_REVERSE",
  ‘PERM ls (REVERSE ls)’,
  SIMP_TAC list_ss [PERM_alt, FILTER_REVERSE]) ;

val PERM_REVERSE_EQ = store_thm(
  "PERM_REVERSE_EQ",
  “(PERM (REVERSE l1) l2 = PERM l1 l2) /\
    (PERM l1 (REVERSE l2) = PERM l1 l2)”,
  METIS_TAC [PERM_TRANS, PERM_SYM, PERM_REVERSE]);
val _ = export_rewrites ["PERM_REVERSE_EQ"]

val FOLDR_PERM = store_thm ("FOLDR_PERM",
“!f l1 l2 e.
(ASSOC f /\ COMM f) ==>
((PERM l1 l2) ==>
(FOLDR f e l1 = FOLDR f e l2))”,

SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC PERM_IND THEN
SIMP_TAC list_ss [] THEN
PROVE_TAC[ASSOC_DEF, COMM_DEF]);

Theorem PERM_SET_TO_LIST_count_COUNT_LIST:
  PERM (SET_TO_LIST (count n)) (COUNT_LIST n)
Proof
  MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  CONJ_TAC
  >- (MATCH_MP_TAC ALL_DISTINCT_SET_TO_LIST THEN
      MATCH_ACCEPT_TAC pred_setTheory.FINITE_COUNT ) THEN
  SRW_TAC [][rich_listTheory.COUNT_LIST_GENLIST,ALL_DISTINCT_GENLIST,
             MEM_GENLIST]
QED

Theorem SORTED_NIL:     !R. SORTED R []
Proof SRW_TAC[][]
QED

Theorem SORTED_SING:    !R x. SORTED R [x]
Proof SRW_TAC[][]
QED

val SORTED_TL = store_thm ("SORTED_TL",
  “SORTED R (x :: xs) ==> SORTED R xs”,
    Cases_on ‘xs’ THEN (SIMP_TAC list_ss [SORTED_DEF])) ;

val SORTED_EL_SUC = store_thm(
"SORTED_EL_SUC",
“!R ls. SORTED R ls =
        !n. (SUC n) < LENGTH ls ==>
            R (EL n ls) (EL (SUC n) ls)”,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
Cases_on ‘ls’ THEN SRW_TAC[][SORTED_DEF] THEN
SRW_TAC[][EQ_IMP_THM] THEN1 (
  Cases_on ‘n’ THEN SRW_TAC[][] THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  POP_ASSUM (Q.SPEC_THEN ‘0’ MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN ‘SUC n’ MP_TAC) THEN
SRW_TAC [][])

val SORTED_EL_LESS = store_thm(
"SORTED_EL_LESS",
“!R. transitive R ==>
  !ls. SORTED R ls =
       !m n. m < n /\ n < LENGTH ls ==>
             R (EL m ls) (EL n ls)”,
GEN_TAC THEN STRIP_TAC THEN
Induct THEN SRW_TAC[][] THEN
SRW_TAC[][SORTED_EQ,EQ_IMP_THM] THEN1 (
  Cases_on ‘n’ THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on ‘m’ THEN SRW_TAC[][] THEN1
    METIS_TAC[MEM_EL] THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  FIRST_X_ASSUM (Q.SPECL_THEN [‘SUC m’,‘SUC n’] MP_TAC) THEN
  SRW_TAC [][] ) THEN
FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [‘0’,‘SUC n’] MP_TAC) THEN
SRW_TAC [][])

val MEM_PERM =
  store_thm(
    "MEM_PERM",
    “!l1 l2. PERM l1 l2 ==> (!a. MEM a l1 = MEM a l2)”,
    METIS_TAC [Q.SPEC ‘$= a’ MEM_FILTER, PERM_DEF]);


val SORTED_PERM_EQ = Q.store_thm ("SORTED_PERM_EQ",
  ‘!R. transitive R /\ antisymmetric R ==>
    !l1 l2. SORTED R l1 /\ SORTED R l2 /\ PERM l1 l2 ==> (l1 = l2)’,
  GEN_TAC >> STRIP_TAC >>
    Induct THEN1 SIMP_TAC list_ss [PERM_NIL] >>
    REPEAT STRIP_TAC >>
    Cases_on ‘l2’ THEN1 FULL_SIMP_TAC list_ss [PERM_NIL] >>
    SIMP_TAC list_ss [] >> CONJ_ASM1_TAC
  THENL [
    IMP_RES_TAC SORTED_EQ >> IMP_RES_TAC MEM_PERM >>
      POP_ASSUM (ASSUME_TAC o Q.SPEC ‘h'’) >>
      FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC ‘h’) >>
      FULL_SIMP_TAC list_ss [relationTheory.antisymmetric_def],
    FIRST_X_ASSUM MATCH_MP_TAC >>
      BasicProvers.VAR_EQ_TAC >> IMP_RES_TAC SORTED_TL >>
      FULL_SIMP_TAC list_ss [PERM_CONS_IFF] ]) ;

val QSORT_eq_if_PERM = store_thm(
"QSORT_eq_if_PERM",
“!R. total R /\ transitive R /\ antisymmetric R ==>
  !l1 l2. (QSORT R l1 = QSORT R l2) = PERM l1 l2”,
PROVE_TAC[QSORT_PERM,QSORT_SORTED,SORTED_PERM_EQ,PERM_TRANS,PERM_SYM])

(* generalisation of the above *)
Theorem SORTS_PERM_EQ:
  !R. transitive R /\ antisymmetric R /\ SORTS f R ==>
  !l1 l2. (f R l1 = f R l2) = PERM l1 l2
Proof
  PROVE_TAC[SORTED_PERM_EQ, PERM_SYM, PERM_TRANS, SORTS_DEF]
QED

Theorem SORTED_FILTER:
  !R ls P. transitive R /\ SORTED R ls ==> SORTED R (FILTER P ls)
Proof
  Induct_on ‘ls’ >> csimp[SORTED_EQ] >> rw[SORTED_EQ] >> fs[MEM_FILTER]
QED

val ALL_DISTINCT_SORTED_WEAKEN = Q.store_thm("ALL_DISTINCT_SORTED_WEAKEN",
  ‘!R R' ls. (!x y. MEM x ls /\ MEM y ls /\ x <> y ==> (R x y <=> R' x y)) /\
        ALL_DISTINCT ls /\ SORTED R ls ==> SORTED R' ls’,
  gen_tac \\ ho_match_mp_tac SORTED_IND \\ rw[]
  \\ pop_assum mp_tac
  \\ simp_tac(srw_ss())[SORTED_DEF]
  \\ metis_tac[]);

(*Perm theorems for the simplication*)

(* was PERM_FUN_APPEND but this name is used again lower down *)
val PERM_FUN_APPEND_C = store_thm (
"PERM_FUN_APPEND_C",
“!l1 l1' l2 l2'.
(PERM l1 = PERM l1') ==>
(PERM l2 = PERM l2') ==>
(PERM (l1 ++ l2) = PERM (l1' ++ l2'))”,
SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_CONG]);


val PERM_FUN_CONS = store_thm (
"PERM_FUN_CONS",
“!x l1 l1'.
(PERM l1 = PERM l1') ==>
(PERM (x::l1) = PERM (x::l1'))”,
SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_CONS_IFF]);


val PERM_FUN_APPEND_CONS = store_thm (
"PERM_FUN_APPEND_CONS",
“!x l1 l2. PERM (l1 ++ x::l2) = PERM (x::l1++l2)”,
METIS_TAC[PERM_EQUIVALENCE_ALT_DEF,
          PERM_APPEND, PERM_CONS_IFF,
          APPEND])


val PERM_FUN_SWAP_AT_FRONT = store_thm (
"PERM_FUN_SWAP_AT_FRONT",
“!x y l. PERM (x::y::l) = PERM (y::x::l)”,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF,
            PERM_SWAP_AT_FRONT, PERM_REFL]);

val PERM_FUN_CONS_11_SWAP_AT_FRONT = store_thm (
"PERM_FUN_CONS_11_SWAP_AT_FRONT",
“!y l1 x l2.
(PERM l1 = PERM (x::l2)) ==>
(PERM (y::l1) = PERM (x::y::l2))”,
REPEAT STRIP_TAC THEN
ASSUME_TAC (Q.SPECL [‘x’, ‘y’,‘l2’] PERM_FUN_SWAP_AT_FRONT) THEN
ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_CONS_IFF]);


val PERM_FUN_CONS_11_APPEND = store_thm (
"PERM_FUN_CONS_11_APPEND",
“!y l1 l2 l3.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (y::l1) = PERM (l2++(y::l3)))”,
EVERY [SIMP_TAC list_ss
    [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_alt, FILTER_APPEND_DISTRIB],
  REPEAT STRIP_TAC, COND_CASES_TAC, ASM_SIMP_TAC list_ss [] ]) ;

val PERM_FUN_CONS_APPEND_1 = store_thm (
"PERM_FUN_CONS_APPEND_1",
“!l l1 x l2.
(PERM l1 = PERM (x::l2)) ==>
(PERM (l1 ++ l) = PERM (x::(l2++l)))”,
EVERY [SIMP_TAC list_ss
    [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_alt, FILTER_APPEND_DISTRIB],
  REPEAT STRIP_TAC, COND_CASES_TAC, ASM_SIMP_TAC list_ss [] ]) ;

val PERM_FUN_CONS_APPEND_2 = store_thm (
"PERM_FUN_CONS_APPEND_2",
“!l l1 x l2.
(PERM l1 = PERM (x::l2)) ==>
(PERM (l ++ l1) = PERM (x::(l ++ l2)))”,
EVERY [SIMP_TAC list_ss
    [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_alt, FILTER_APPEND_DISTRIB],
  REPEAT STRIP_TAC, COND_CASES_TAC, ASM_SIMP_TAC list_ss [] ]) ;

val PERM_FUN_APPEND_APPEND_1 = store_thm (
"PERM_FUN_APPEND_APPEND_1",
“!l1 l2 l3 l4.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (l1 ++ l4) = PERM (l2++(l3++l4)))”,
SIMP_TAC list_ss
    [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_alt, FILTER_APPEND_DISTRIB]) ;

val PERM_FUN_APPEND_APPEND_2 = store_thm (
"PERM_FUN_APPEND_APPEND_2",
“!l1 l2 l3 l4.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (l4 ++ l1) = PERM (l2++(l4++l3)))”,
SIMP_TAC list_ss
    [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_alt, FILTER_APPEND_DISTRIB]) ;

val PERM_FUN_APPEND = store_thm (
"PERM_FUN_APPEND",
“!l1 l2. PERM (l1 ++ l2) = PERM (l2 ++ l1)”,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND])


val PERM_FUN_CONS_IFF = store_thm (
"PERM_FUN_CONS_IFF",
“!x l1 l2. (PERM l1 = PERM l2) ==> (PERM (x::l1) = PERM (x::l2))”,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_CONS_IFF]);



val PERM_FUN_APPEND_IFF = store_thm (
"PERM_FUN_APPEND_IFF",
“!l l1 l2. (PERM l1 = PERM l2) ==> (PERM (l++l1) = PERM (l++l2))”,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);



val PERM_FUN_CONG = store_thm (
"PERM_FUN_CONG",
“!l1 l1' l2 l2'.
(PERM l1 = PERM l1') ==>
(PERM l2 = PERM l2') ==>
(PERM l1 l2 = PERM l1' l2')”,
METIS_TAC[PERM_EQUIVALENCE_ALT_DEF])


val PERM_CONG_2 = store_thm (
"PERM_CONG_2",
“!l1 l1' l2 l2'.
(PERM l1 l1') ==>
(PERM l2 l2') ==>
(PERM l1 l2 = PERM l1' l2')”,
METIS_TAC[PERM_EQUIVALENCE_ALT_DEF])


val PERM_CONG_APPEND_IFF = store_thm (
"PERM_CONG_APPEND_IFF",
“!l l1 l1' l2 l2'.
(PERM l1 (l++l1')) ==>
(PERM l2 (l++l2')) ==>
(PERM l1 l2 = PERM l1' l2')”,
METIS_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);


val PERM_CONG_APPEND_IFF2 = store_thm (
"PERM_CONG_APPEND_IFF2",
“!l1 l1' l1'' l2 l2' l2''.
(PERM l1 (l1'++l1'')) ==>
(PERM l2 (l2'++l2'')) ==>
(PERM l1' l2') ==>
(PERM l1 l2 = PERM l1'' l2'')”,
METIS_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);


val PERM_FUN_SPLIT = store_thm (
"PERM_FUN_SPLIT",
“!l l1 l1' l2.
(PERM l (l1++l2)) ==>
(PERM l1' l1) ==>
(PERM l (l1'++l2))”,
METIS_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);


val PERM_REWR = store_thm (
"PERM_REWR",
“!l r l1 l2.
(PERM l r) ==>
(PERM (l++l1) l2 = PERM (r++l1) l2)”,
PROVE_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);


val PERM_CENTRE1 = prove (
“(PERM (xs ++ l) (r1 ++ xs ++ r2) = PERM l (r1 ++ r2))”,
METIS_TAC [APPEND_ASSOC, PERM_APPEND_IFF,
    PERM_APPEND, PERM_EQUIVALENCE_ALT_DEF]);
val PERM_CENTRE2 = PERM_CENTRE1 |> Q.GEN ‘xs’ |> Q.SPEC ‘[x]’
  |> SIMP_RULE bool_ss [APPEND, GSYM APPEND_ASSOC]

val PERM_TO_APPEND_SIMPS = store_thm (
"PERM_TO_APPEND_SIMPS",
“(PERM (x::l) ((x::r1) ++ r2) = PERM l (r1 ++ r2)) /\
(PERM (x::l) (r1 ++ (x::r2)) = PERM l (r1 ++ r2)) /\
(PERM ((xs ++ ys) ++ zs) r = PERM (xs ++ (ys ++ zs)) r) /\
(PERM ((x :: ys) ++ zs) r = PERM (x :: (ys ++ zs)) r) /\
(PERM ([] ++ l) r = PERM l r) /\
(PERM (xs ++ l) ((xs ++ r1) ++ r2) = PERM l (r1 ++ r2)) /\
(PERM (xs ++ l) (r1 ++ (xs ++ r2)) = PERM l (r1 ++ r2)) /\
(PERM [] ([] ++ []) = T) /\
(PERM xs ((xs ++ []) ++ []) = T) /\
(PERM xs ([] ++ (xs ++ [])) = T)”,
SIMP_TAC list_ss [PERM_REFL, PERM_CONS_IFF, PERM_CENTRE1, PERM_CENTRE2]
  \\ SIMP_TAC bool_ss [GSYM APPEND_ASSOC, PERM_APPEND_IFF]);

Theorem PERM_FLAT:
  !l1 l2. PERM l1 l2 ==> PERM (FLAT l1) (FLAT l2)
Proof
  ho_match_mp_tac PERM_IND
  \\ rw[PERM_APPEND_IFF, PERM_SWAP_L_AT_FRONT]
  \\ metis_tac[PERM_TRANS]
QED

Theorem PERM_FLAT_MAP_CONS:
  !h t ls. PERM (FLAT (MAP (\x. h x :: t x) ls)) (MAP h ls ++ FLAT (MAP t ls))
Proof
  ntac 2 gen_tac
  \\ Induct
  \\ rw[]
  \\ irule PERM_TRANS
  \\ qmatch_goalsub_abbrev_tac`PERM _ (a ++ b ++ c)`
  \\ qexists_tac`b ++ (a ++ c)`
  \\ simp[PERM_APPEND_IFF, PERM_APPEND]
QED

Theorem PERM_FLAT_MAP_SWAP:
  !f l1 l2.
    PERM (FLAT (MAP (\x. MAP (f x) l2) l1))
         (FLAT (MAP (\x. MAP (flip f x) l1) l2))
Proof
  gen_tac
  \\ Induct
  \\ rw[]
  >- (
    qmatch_goalsub_abbrev_tac`MAP g l2`
    \\ `g = K []` by simp[Abbr`g`, FUN_EQ_THM]
    \\ rw[FLAT_MAP_K_NIL] )
  \\ irule PERM_TRANS
  \\ qexists_tac`MAP (f h) l2 ++ FLAT (MAP (\x. MAP (flip f x) l1) l2)`
  \\ simp[PERM_APPEND_IFF]
  \\ simp[Once PERM_SYM]
  \\ qho_match_abbrev_tac`PERM (FLAT (MAP (\x. hf x :: ht x) l2)) _`
  \\ `MAP (f h) l2 = MAP hf l2`
  by ( simp[Abbr`hf`, MAP_EQ_f] \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ simp[PERM_FLAT_MAP_CONS]
QED

Theorem PERM_MAP_SET_TO_LIST_IMAGE:
  !s. FINITE s ==> !f. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) ==>
  PERM (MAP f (SET_TO_LIST s)) (SET_TO_LIST (IMAGE f s))
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  \\ rw[Once PERM_SYM]
  \\ irule PERM_TRANS
  \\ qexists_tac`f e :: SET_TO_LIST (IMAGE f s)`
  \\ conj_tac
  >- (
    `FINITE (IMAGE f s)` by simp[]
    \\ drule PERM_SET_TO_LIST_INSERT
    \\ disch_then(qspec_then`f e`mp_tac)
    \\ simp[]
    \\ metis_tac[])
  \\ irule PERM_TRANS
  \\ qexists_tac`f e :: MAP f (SET_TO_LIST s)`
  \\ conj_tac >- metis_tac[PERM_SYM, PERM_CONS_IFF]
  \\ rewrite_tac[GSYM MAP]
  \\ irule PERM_MAP
  \\ rw[Once PERM_SYM]
  \\ drule PERM_SET_TO_LIST_INSERT
  \\ metis_tac[]
QED

Theorem PERM_BIJ_SET_TO_LIST:
  !f s1 s2. FINITE s1 /\ FINITE s2 /\ BIJ f s1 s2 ==>
  PERM (MAP f (SET_TO_LIST s1)) (SET_TO_LIST s2)
Proof
  rw[]
  \\ irule PERM_TRANS
  \\ qexists_tac`SET_TO_LIST (IMAGE f s1)`
  \\ conj_tac
  >- (
    irule PERM_MAP_SET_TO_LIST_IMAGE
    \\ fs[BIJ_DEF, INJ_DEF] )
  \\ imp_res_tac BIJ_IMAGE
  \\ rw[]
QED

Theorem PERM_SET_TO_LIST_DISJOINT_UNION_APPEND:
  !s1 s2. FINITE s1 /\ FINITE s2 /\ DISJOINT s1 s2 ==>
  PERM (SET_TO_LIST (s1 UNION s2)) (SET_TO_LIST s1 ++ SET_TO_LIST s2)
Proof
  rpt strip_tac
  \\ irule PERM_ALL_DISTINCT
  \\ simp[ALL_DISTINCT_APPEND]
  \\ fs[IN_DISJOINT]
  \\ PROVE_TAC[]
QED

Theorem LIST_REL_PERM:
  !l1 l2 l3. LIST_REL P l1 l2 /\ PERM l2 l3 ==>
             ?l4. PERM l1 l4 /\ LIST_REL P l4 l3
Proof
  Induct_on ‘LIST_REL’
  \\ rw[PERM_CONS_EQ_APPEND, PULL_EXISTS]
  \\ ntac 2 (irule_at Any listTheory.LIST_REL_APPEND_suff)
  \\ simp[]
  \\ first_x_assum $ drule_then strip_assume_tac
  \\ gs[LIST_REL_SPLIT2, SF SFY_ss]
QED

(*---------------------------------------------------------------------------*)
(* QSORT3 - A stable version of QSORT (James Reynolds - 10/2010)             *)
(*    Lists are stable if filtering using any predicate that implies two     *)
(*    elements are unordered is unaffected by sorting.                       *)
(*---------------------------------------------------------------------------*)

val STABLE_DEF = Define ‘
    STABLE sort r <=>
      SORTS sort r /\
      !p. (!x y. p x /\ p y ==> r x y) ==>
          (!l. FILTER p l = FILTER p (sort r l))’;

(*---------------------------------------------------------------------------*)
(* PART3 - Split a list into < h, = h and > h                                *)
(*---------------------------------------------------------------------------*)

val PART3_DEF = Define ‘
    (PART3 R h [] = ([],[],[])) /\
    (PART3 R h (hd::tl) =
         if R h hd /\ R hd h
            then (I ## CONS hd ## I) (PART3 R h tl)
            else if R hd h
                    then (CONS hd ## I ## I) (PART3 R h tl)
                    else (I ## I ## CONS hd) (PART3 R h tl))’;

val LENGTH_FILTER =
  prove(“!a. LENGTH (FILTER P a) <= LENGTH a”,
    Induct THEN RW_TAC arith_ss [FILTER, LENGTH]);

val length_lem =
  prove(“!a h. LENGTH (FILTER P a) < LENGTH (h::a)”,
    REPEAT STRIP_TAC THEN REWRITE_TAC [LENGTH] THEN
    MATCH_MP_TAC (DECIDE “!a b. a <= b ==> a < SUC b”) THEN
    MATCH_ACCEPT_TAC LENGTH_FILTER);

(*---------------------------------------------------------------------------*)
(* PART3_FILTER - Partition is the same as filtering.                        *)
(*---------------------------------------------------------------------------*)

val PART3_FILTER =
  store_thm("PART3_FILTER",
    “!tl hd. PART3 R hd tl = (FILTER (\x. R x hd /\ ~R hd x) tl,
                            FILTER (\x. R x hd /\ R hd x) tl,
                            FILTER (\x. ~R x hd) tl)”,
    Induct THEN RW_TAC std_ss [PART3_DEF, PAIR_MAP, FILTER] THEN
    FULL_SIMP_TAC std_ss []);

(*---------------------------------------------------------------------------*)
(* QSORT3 - Partition three ways but only recurse on < and >                 *)
(*---------------------------------------------------------------------------*)

Definition QSORT3_DEF:
    (QSORT3 R [] = []) /\
    (QSORT3 R (hd::tl) =
        let (lo,eq,hi) = PART3 R hd tl
        in QSORT3 R lo ++ (hd::eq) ++ QSORT3 R hi)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ THEN
  RW_TAC arith_ss [PART3_FILTER, length_lem]
End

val PERM3 =
  store_thm(
    "PERM3",
    “!x a a' b b' c c'.
      (PERM a a' /\ PERM b b' /\ PERM c c') /\ PERM x (a ++ b ++ c)
      ==> PERM x (a' ++ b' ++ c')”,
    RW_TAC std_ss [PERM_DEF, FILTER_APPEND_DISTRIB]);

val PULL_CONV =
  REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV))
val PULL_RULE = CONV_RULE PULL_CONV;

val IND_STEP_TAC = PAT_X_ASSUM “!y. P ==> Q” (MATCH_MP_TAC o PULL_RULE);

val tospec =
    Q.GEN ‘P’
      (MATCH_MP (SPEC_ALL
        (REWRITE_RULE [GSYM AND_IMP_INTRO] PERM_TRANS)) (SPEC_ALL PERM_SPLIT));

val filter_filter =
  prove(
    “!l P Q. FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l”,
    Induct THEN NTAC 2 (RW_TAC std_ss [FILTER]) THEN PROVE_TAC []);

Theorem PERM3_FILTER:
  !l h.
    PERM l
         (FILTER (\x. R x h /\ ~R h x) l ++ FILTER (\x. R x h /\ R h x) l ++
          FILTER (\x. ~R x h) l)
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (SPEC “\x. (R:'a -> 'a -> bool) x h” tospec) THEN
  REWRITE_TAC [APPEND_ASSOC] THEN MATCH_MP_TAC PERM_CONG THEN
  RW_TAC std_ss [combinTheory.o_DEF, PERM_REFL] THEN
  MATCH_MP_TAC (SPEC “(R :'a -> 'a -> bool) h” tospec) THEN
  RW_TAC std_ss [o_DEF, PERM_REFL, filter_filter, FILTER_APPEND_DISTRIB] THEN
  MATCH_MP_TAC
    (PROVE [PERM_APPEND] “(A = C) /\ (B = D) ==> (PERM (A ++ B) (D ++ C))”) THEN
  REPEAT CONJ_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  PROVE_TAC []
QED

Theorem PERM_QSORT3:
  !l R. PERM l (QSORT3 R l)
Proof
  completeInduct_on ‘LENGTH l’ THEN Cases THEN
  RW_TAC std_ss [PERM_CONS_EQ_APPEND, QSORT3_DEF, PERM_NIL, PART3_FILTER] THEN
  Q.EXISTS_TAC ‘QSORT3 R (FILTER (\x. R x h /\ ~R h x) t)’ THEN
  Q.EXISTS_TAC
   ‘FILTER (\x. R x h /\ R h x) t ++ QSORT3 R (FILTER (\x. ~R x h) t) ’ THEN
  RW_TAC std_ss [APPEND_ASSOC, GSYM APPEND] THEN
  MATCH_MP_TAC PERM3 THEN
  MAP_EVERY Q.EXISTS_TAC [
      ‘FILTER (\x. R x h /\ ~R h x) t’,
      ‘FILTER (\x. R x h /\ R h x) t’,
      ‘FILTER (\x. ~R x h) t’] THEN
  RW_TAC std_ss [PERM_REFL] THEN TRY IND_STEP_TAC THEN
  RW_TAC arith_ss [length_lem] THEN METIS_TAC [PERM3_FILTER]
QED

val SORTED_EQ_PART =
  store_thm(
    "SORTED_EQ_PART",
    “!l R. transitive R ==> SORTED R (FILTER (\x. R x hd /\ R hd x) l)”,
    Induct THEN REPEAT STRIP_TAC THEN
    RW_TAC std_ss [SORTED_DEF, FILTER, SORTED_EQ, MEM_FILTER] THEN
    PROVE_TAC [relationTheory.transitive_def]);

Theorem QSORT3_SORTS:
  !R. transitive R /\ total R ==> SORTS QSORT3 R
Proof
  RW_TAC std_ss [SORTS_DEF, PERM_QSORT3] THEN
  completeInduct_on ‘LENGTH l’ THEN
  Cases_on ‘l’ THEN
  RW_TAC std_ss [QSORT3_DEF, SORTED_DEF, PART3_FILTER] THEN
  REPEAT (MATCH_MP_TAC SORTED_APPEND_IMP THEN REPEAT CONJ_TAC) THEN
  ASM_REWRITE_TAC [] THEN
  TRY IND_STEP_TAC THEN
  RW_TAC std_ss [length_lem, SORTED_EQ, MEM_FILTER, SORTED_EQ_PART, MEM,
                 MEM_FILTER, MEM_APPEND] THEN
  IMP_RES_TAC (PROVE[MEM_PERM, PERM_QSORT3] “MEM x (QSORT3 R b) ==> MEM x b”) >>
  FULL_SIMP_TAC std_ss [MEM_FILTER] THEN
  PROVE_TAC [relationTheory.total_def,relationTheory.transitive_def]
QED

Theorem LENGTH_QSORT3[local] =
   PROVE [PERM_LENGTH, PERM_QSORT3] “!l R. LENGTH (QSORT3 R l) = LENGTH l”

fun SPLIT_APPEND_TAC x =
    MATCH_MP_TAC
      (prove(x, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [APPEND_ASSOC])) THEN
    REPEAT CONJ_TAC

fun LIND_STEP (a,goal) =
  FIRST_ASSUM
    (CONV_TAC o LAND_CONV o REWR_CONV o
     SIMP_RULE std_ss [length_lem,LENGTH_QSORT3] o
     SPEC (mk_comb(“LENGTH:'a list -> num”,lhs goal)) o
     Q.GEN ‘m’ o C (PART_MATCH (lhs o rand)) (lhs goal) o PULL_RULE) (a,goal)

val FILTER_P =
  prove(
    “!R h. p h /\ transitive R /\ total R /\ (!x y. p x /\ p y ==> R x y) ==>
             !l. (FILTER (\x. p x /\ R x h /\ R h x) l = FILTER p l) /\
                 (FILTER p (FILTER (\x. R x h /\ ~R h x) l) = []) /\
                 (FILTER p (FILTER (\x. ~R x h) l) = [])”,
    NTAC 3 STRIP_TAC THEN Induct THEN RW_TAC std_ss [FILTER] THEN
    PROVE_TAC [relationTheory.transitive_def, relationTheory.total_def]);

Theorem QSORT3_SPLIT:
  !R. transitive R /\ total R ==>
      !l e.
        QSORT3 R l = QSORT3 R (FILTER (\x. R x e /\ ~R e x) l) ++
                     FILTER (\x. R x e /\ R e x) l ++
                     QSORT3 R (FILTER (\x. ~R x e) l)
Proof
  NTAC 2 STRIP_TAC THEN completeInduct_on ‘LENGTH l’ THEN Cases THEN
  RW_TAC std_ss [FILTER, QSORT3_DEF, PART3_FILTER, APPEND, APPEND_ASSOC] THEN
  RW_TAC std_ss [filter_filter, QSORT3_DEF, PART3_FILTER] THEN
  FULL_SIMP_TAC bool_ss [APPEND_ASSOC] THENL [
    SPLIT_APPEND_TAC “(a = d) /\ (b = e) /\ (c = f ++ g ++ h) ==>
                      (a ++ b ++ c = d ++ e ++ f ++ g ++ h)”,
    SPLIT_APPEND_TAC “(a = d) /\ (b = e) /\ (c = f) ==>
                      (a ++ b ++ c = d ++ e ++ f)”,
    SPLIT_APPEND_TAC “(a = d ++ e ++ f) /\ (b = g) /\ (c = h) ==>
                      (a ++ b ++ c = d ++ e ++ f ++ g ++ h)”
  ] THEN
  TRY (LIND_STEP THEN
       SPLIT_APPEND_TAC “(a = d) /\ (b = e) /\ (c = f) ==>
                         (a ++ b ++ c = d ++ e ++ f)”) THEN
  RW_TAC std_ss [filter_filter] THEN
  REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  PROVE_TAC [relationTheory.total_def,relationTheory.transitive_def]
QED

(*---------------------------------------------------------------------------*)
(* Final proof: QSORT3 is a stable sort.                                     *)
(*---------------------------------------------------------------------------*)

Theorem QSORT3_STABLE:
  !R. transitive R /\ total R ==> STABLE QSORT3 R
Proof
  RW_TAC std_ss [STABLE_DEF, QSORT3_SORTS] >>
  completeInduct_on ‘LENGTH l’ >> Cases_on ‘l’ >>
  RW_TAC std_ss [QSORT3_DEF, FILTER, PART3_FILTER] >>
  RW_TAC std_ss [FILTER_APPEND_DISTRIB, filter_filter, GSYM APPEND, FILTER]
  >- METIS_TAC [FILTER_P, APPEND_NIL, length_lem, CONJUNCT1 APPEND] >>
  MATCH_MP_TAC EQ_TRANS >> Q.EXISTS_TAC ‘FILTER p (QSORT3 R t)’ >> CONJ_TAC
  >- (IND_STEP_TAC >> RW_TAC arith_ss [LENGTH]) >>
  METIS_TAC [FILTER_APPEND_DISTRIB, filter_filter, QSORT3_SPLIT]
QED


(*---------------------------------------------------------------------------*)
(* Various useful theorems from the CakeML project https://cakeml.org.       *)
(*---------------------------------------------------------------------------*)

local open rich_listTheory in

Theorem QSORT3_MEM:
  !R L x. MEM x (QSORT3 R L) <=> MEM x L
Proof
 ho_match_mp_tac QSORT3_IND >>
 rw [QSORT3_DEF] >>
 fs [] >>
 eq_tac >>
 rw [] >>
 fs [PART3_FILTER] >>
 rw [] >>
 fs [MEM_FILTER] >>
 metis_tac []
QED

val QSORT3_SORTED = Q.store_thm ("QSORT3_SORTED",
‘!R L. transitive R /\ total R ==> SORTED R (QSORT3 R L)’,
 rw [] >>
 imp_res_tac QSORT3_SORTS >>
 fs [SORTS_DEF]);

val sorted_lt_count_list = Q.store_thm ("sorted_lt_count_list",
‘!n. SORTED $< (COUNT_LIST n)’,
 Induct_on ‘n’
 >- rw [COUNT_LIST_def] >>
 rw [COUNT_LIST_SNOC, SNOC_APPEND] >>
 match_mp_tac SORTED_APPEND_IMP >>
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [transitive_def, MEM_COUNT_LIST] >>
 decide_tac);

val SORTED_weaken = store_thm("SORTED_weaken",
  “!R R' ls. SORTED R ls /\ (!x y. MEM x ls /\ MEM y ls /\ R x y ==> R' x y)
      ==> SORTED R' ls”,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][] THEN
  Cases_on‘ls’ THEN
  FULL_SIMP_TAC(srw_ss())[SORTED_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  METIS_TAC[])

val sorted_count_list = Q.store_thm ("sorted_count_list",
‘!n. SORTED $<= (COUNT_LIST n)’,
 gen_tac \\ irule SORTED_weaken \\ qexists_tac‘$<’
 \\ simp[sorted_lt_count_list]);

val sorted_map = Q.store_thm ("sorted_map",
‘!R f l. (SORTED R (MAP f l) <=> SORTED (inv_image R f) l)’,
 Induct_on ‘l’ >> rw [SORTED_EL_SUC, EL_MAP]);

val sorted_perm_count_list = Q.store_thm ("sorted_perm_count_list",
‘!y f l n.
  SORTED (inv_image $<= f) l /\
  PERM (MAP f l) (COUNT_LIST n)
  ==>
  (MAP f l = COUNT_LIST n)’,
 rw [] >>
 ‘transitive $<= /\ antisymmetric $<=’
          by srw_tac [ARITH_ss] [transitive_def,antisymmetric_def] >>
 metis_tac [sorted_map, SORTED_PERM_EQ, sorted_count_list]);

val less_sorted_eq = MATCH_MP SORTED_EQ arithmeticTheory.transitive_LESS
  |> curry save_thm"less_sorted_eq";

val SORTED_GENLIST_PLUS = store_thm("SORTED_GENLIST_PLUS",
  “!n k. SORTED $< (GENLIST ($+ k) n)”,
  Induct >> simp[GENLIST_CONS,less_sorted_eq,MEM_GENLIST] >> gen_tac >>
  ‘$+ k o SUC = $+ (k+1)’ by (
    simp[FUN_EQ_THM] ) >>
  metis_tac[])

val SORTED_ALL_DISTINCT = store_thm("SORTED_ALL_DISTINCT",
  “irreflexive R /\ transitive R ==> !ls. SORTED R ls ==> ALL_DISTINCT ls”,
  STRIP_TAC THEN Induct THEN SRW_TAC[][] THEN
  IMP_RES_TAC SORTED_EQ THEN
  FULL_SIMP_TAC (srw_ss()) [SORTED_DEF] THEN
  METIS_TAC[relationTheory.irreflexive_def])

val sorted_filter = Q.store_thm("sorted_filter",
  ‘!R ls. transitive R ==> SORTED R ls ==> SORTED R (FILTER P ls)’,
  HO_MATCH_MP_TAC SORTED_IND >>
  rw[SORTED_DEF] >> fs[] >>
  rfs[SORTED_EQ,MEM_FILTER] >>
  rw[] >> metis_tac[transitive_def])

end

Theorem SORTED_ALL_DISTINCT_LIST_TO_SET_EQ:
  !R. transitive R /\ antisymmetric R ==>
      !l1 l2. SORTED R l1 /\ SORTED R l2 /\ ALL_DISTINCT l1 /\
              ALL_DISTINCT l2 /\ set l1 = set l2 ==>
              l1 = l2
Proof
  gen_tac \\ strip_tac
  \\ Induct \\ simp[]
  \\ gen_tac \\ Cases \\ simp[]
  \\ simp[SORTED_EQ]
  \\ strip_tac
  \\ fs[EXTENSION]
  \\ metis_tac[antisymmetric_def]
QED

Theorem EL_FILTER_COUNT_LIST_LEAST:
!n i.
  (i < LENGTH (FILTER P (COUNT_LIST n))) ==>
    EL i (FILTER P (COUNT_LIST n))
    = LEAST j.
        ((0 < i) ==> EL (i-1) (FILTER P (COUNT_LIST n)) < j) /\
        (j < n) /\ P j
Proof
  rw[]
  \\ ‘SORTED $< (FILTER P (COUNT_LIST n))’
    by ( irule SORTED_FILTER \\ rw[sorted_lt_count_list] )
  \\ qmatch_abbrev_tac‘x = _’
  \\ ‘MEM x (FILTER P (COUNT_LIST n))’ by metis_tac[MEM_EL]
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac
  >- (
    qexists_tac‘x’
    \\ fs[MEM_FILTER, MEM_COUNT_LIST]
    \\ strip_tac
    \\ fs[SORTED_EL_LESS, Abbr‘x’] )
  \\ qx_gen_tac‘y’
  \\ strip_tac
  \\ ‘MEM y (FILTER P (COUNT_LIST n))’ by simp[MEM_FILTER, MEM_COUNT_LIST]
  \\ pop_assum mp_tac \\ simp[MEM_EL]
  \\ disch_then(qx_choose_then‘j’strip_assume_tac)
  \\ Cases_on‘i = j’ >- fs[]
  \\ Cases_on‘i < j’ >- (
    ‘x < y’ by fs[SORTED_EL_LESS, Abbr‘x’]
    \\ first_x_assum drule
    \\ fs[SORTED_EL_LESS, MEM_FILTER]
    \\ simp[Abbr‘x’]
    \\ Cases_on‘i = 0’ \\ simp[] )
  \\ ‘j < i’ by simp[]
  \\ ‘0 < i’ by simp[]
  \\ Cases_on ‘j = i-1’ \\ fs[]
  \\ ‘j < i-1’ by fs[]
  \\ fs[SORTED_EL_LESS]
  \\ last_x_assum drule
  \\ simp[]
QED

Theorem SORTED_FILTER_COUNT_LIST:
  SORTED R (FILTER P (COUNT_LIST m)) <=>
  !i j. (i < j) /\ (j < m) /\ P i /\ P j /\ (!k. (i < k) /\ (k < j) ==> ~P k)
        ==> R i j
Proof
  ‘SORTED $< (FILTER P (COUNT_LIST m))’
  by ( irule SORTED_FILTER \\ simp[sorted_lt_count_list] )
  \\ rw[SORTED_EL_SUC, EQ_IMP_THM]
  >- (
    ‘MEM i (FILTER P (COUNT_LIST m))’ by simp[MEM_FILTER, MEM_COUNT_LIST]
    \\ ‘MEM j (FILTER P (COUNT_LIST m))’ by simp[MEM_FILTER, MEM_COUNT_LIST]
    \\ fs[MEM_EL]
    \\ qmatch_assum_rename_tac‘i = EL ni _’
    \\ qmatch_assum_rename_tac‘j = EL nj _’
    \\ ‘ni < nj’
    by (
      CCONTR_TAC \\ gs[NOT_LESS, LESS_OR_EQ]
      \\ fs[SORTED_EL_LESS]
      \\ res_tac \\ fs[] )
    \\ last_x_assum(qspec_then‘nj-1’mp_tac)
    \\ simp[ADD1]
    \\ ‘ni = nj - 1’ suffices_by rw[]
    \\ CCONTR_TAC
    \\ first_x_assum(qspec_then‘EL (nj-1) (FILTER P (COUNT_LIST m))’mp_tac)
    \\ fs[SORTED_EL_LESS]
    \\ qmatch_abbrev_tac‘P x’
    \\ ‘nj - 1 < LENGTH (FILTER P (COUNT_LIST m))’ by simp[]
    \\ ‘MEM x (FILTER P (COUNT_LIST m))’ by metis_tac[MEM_EL]
    \\ fs[MEM_FILTER] )
  \\ first_x_assum irule
  \\ qmatch_abbrev_tac‘P x /\ P y /\ _’
  \\ ‘n < LENGTH (FILTER P (COUNT_LIST m))’ by simp[]
  \\ ‘MEM x (FILTER P (COUNT_LIST m))’ by metis_tac[MEM_EL]
  \\ ‘MEM y (FILTER P (COUNT_LIST m))’ by metis_tac[MEM_EL]
  \\ fs[MEM_FILTER, MEM_COUNT_LIST]
  \\ fs[SORTED_EL_LESS]
  \\ reverse conj_asm2_tac >- metis_tac[prim_recTheory.LESS_SUC_REFL]
  \\ simp[Abbr‘y’, Once EL_FILTER_COUNT_LIST_LEAST]
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ first_x_assum(qspec_then‘k’mp_tac)
  \\ simp[]
QED

Theorem SORTED_nub:
  transitive R /\ SORTED R ls ==> SORTED R (nub ls)
Proof
  qspec_then‘ls’(SUBST1_TAC o Q.AP_TERM‘nub’ o SYM)GENLIST_ID
  \\ simp[nub_GENLIST, sorted_map]
  \\ qmatch_goalsub_abbrev_tac‘FILTER P’
  \\ qmatch_goalsub_abbrev_tac‘COUNT_LIST m’
  \\ simp[SORTED_FILTER_COUNT_LIST]
  \\ rw[]
  \\ gs[SORTED_EL_LESS]
QED

Theorem QSORT_nub:
  transitive R /\ antisymmetric R /\ total R ==>
  QSORT R (nub ls) = nub (QSORT R ls)
Proof
  rw[]
  \\ irule SORTED_ALL_DISTINCT_LIST_TO_SET_EQ
  \\ simp[]
  \\ conj_tac >- metis_tac[ALL_DISTINCT_PERM, QSORT_PERM, all_distinct_nub]
  \\ conj_tac >- simp[EXTENSION, QSORT_MEM]
  \\ qexists_tac‘R’
  \\ simp[QSORT_SORTED]
  \\ irule SORTED_nub
  \\ simp[QSORT_SORTED]
QED

Theorem SORTED_FST_ZIP:
  !R ls rs.
  SORTED R ls /\ LENGTH ls = LENGTH rs ==>
  SORTED (\x y. R (FST x) (FST y)) (ZIP (ls,rs))
Proof
  ho_match_mp_tac SORTED_IND>>rw[]
  >- (Cases_on`rs`>>fs[])>>
  `?a b rss. rs = a::b::rss` by
    (Cases_on`rs` \\ fs[] \\
     metis_tac[list_CASES,LENGTH_NIL,SUC_NOT]) >>
  fs[]>>
  first_x_assum(qspec_then`b::rss` mp_tac)>>
  simp[]
QED

val _ = export_theory();
