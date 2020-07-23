open HolKernel boolLib Parse BasicProvers simpLib numLib metisLib markerLib;
open pred_setTheory pairTheory arithmeticTheory open optionTheory relationTheory;

val Define = TotalDefn.Define;
val Hol_reln = IndDefLib.Hol_reln;

val _ = new_theory "set_relation";

local open OpenTheoryMap
  val ns = ["Relation"]
in
  fun ot0 x y = OpenTheory_const_name{const={Thy="set_relation",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end

(* ------------------------------------------------------------------------ *)
(*  Basic concepts                                                          *)
(* ------------------------------------------------------------------------ *)

val _ = type_abbrev  ("reln", ``:'a # 'a -> bool``);

Theorem rextension:
  !s t. (s = t) <=> !x y. (x,y) IN s <=> (x,y) IN t
Proof
SRW_TAC [] [] THEN
EQ_TAC THEN
SRW_TAC [] [EXTENSION] THEN
Cases_on `x` THEN
SRW_TAC [] []
QED

val domain_def = Define `
  domain r = {x | ?y. (x, y) IN r}`;
val _ = ot "domain"

val range_def = Define `range r = {y | ?x. (x, y) IN r}`;
val _ = ot "range"

Theorem in_domain:
  !x r. x IN domain r <=> ?y. (x,y) IN r
Proof SRW_TAC [] [domain_def]
QED

Theorem in_range:
  !y r. y IN range r <=> ?x. (x,y) IN r
Proof SRW_TAC [] [range_def]
QED

val in_dom_rg = Q.store_thm ("in_dom_rg",
  `(x, y) IN r ==> x IN domain r /\ y IN range r`,
  REWRITE_TAC [in_domain, in_range] THEN PROVE_TAC []) ;

val domain_mono = Q.store_thm ("domain_mono",
  `r SUBSET r' ==> domain r SUBSET domain r'`,
  REWRITE_TAC [in_domain, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `y` THEN RES_TAC) ;

val range_mono = Q.store_thm ("range_mono",
  `r SUBSET r' ==> range r SUBSET range r'`,
  REWRITE_TAC [in_range, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `x'` THEN RES_TAC) ;

val rrestrict_def = Define `
  rrestrict r s = {(x, y) | (x, y) IN r /\ x IN s /\ y IN s}`;
val _ = ot0 "rrestrict" "restrict"

Theorem in_rrestrict:
  !x y r s. (x, y) IN rrestrict r s <=> (x, y) IN r /\ x IN s /\ y IN s
Proof SRW_TAC [] [rrestrict_def]
QED

val in_rrestrict_alt = Q.store_thm ("in_rrestrict_alt",
  `x IN rrestrict r s <=> x IN r /\ FST x IN s /\ SND x IN s`,
  Cases_on `x` THEN REWRITE_TAC [in_rrestrict, FST, SND]) ;

val rrestrict_SUBSET = Q.store_thm ("rrestrict_SUBSET",
  `rrestrict r s SUBSET r`,
  REWRITE_TAC [in_rrestrict_alt, SUBSET_DEF] THEN REPEAT STRIP_TAC) ;

val rrestrict_union = Q.store_thm ("rrestrict_union",
`!r1 r2 s. rrestrict (r1 UNION r2) s = (rrestrict r1 s) UNION (rrestrict r2 s)`,
SRW_TAC [] [rrestrict_def, EXTENSION] THEN
METIS_TAC []);

val rrestrict_rrestrict = Q.store_thm ("rrestrict_rrestrict",
`!r x y. rrestrict (rrestrict r x) y = rrestrict r (x INTER y)`,
SRW_TAC [] [rrestrict_def, EXTENSION] THEN
EQ_TAC THEN
SRW_TAC [] []);

val domain_rrestrict_SUBSET = Q.store_thm ("domain_rrestrict_SUBSET",
  `domain (rrestrict r s) SUBSET s`,
  REWRITE_TAC [in_domain, SUBSET_DEF, in_rrestrict] THEN REPEAT STRIP_TAC) ;

val range_rrestrict_SUBSET = Q.store_thm ("range_rrestrict_SUBSET",
  `range (rrestrict r s) SUBSET s`,
  REWRITE_TAC [in_range, SUBSET_DEF, in_rrestrict] THEN REPEAT STRIP_TAC) ;

val rcomp_def = Define `
  rcomp r1 r2 = { (x, y) | ?z. (x, z) IN r1 /\ (z, y) IN r2}`;

val _ = overload_on ("OO", ``rcomp``);
val _ = set_fixity "OO" (Infixr 800);

val strict_def = Define `
  strict r = {(x, y) | (x, y) IN r /\ x <> y}`;

val strict_rrestrict = Q.store_thm ("strict_rrestrict",
`!r s. strict (rrestrict r s) = rrestrict (strict r) s`,
SRW_TAC [] [strict_def, rrestrict_def, EXTENSION] THEN
METIS_TAC []);

val univ_reln_def = Define `
  univ_reln xs = {(x1, x2) | x1 IN xs /\ x2 IN xs}`;

val finite_prefixes_def = Define `
  finite_prefixes r s = !e. e IN s ==> FINITE {e' | (e', e) IN r}`;
val _ = ot0 "finite_prefixes" "finitePrefixes"

val finite_prefixes_subset_s = Q.store_thm ("finite_prefixes_subset_s",
`!r s s'. finite_prefixes r s /\ s' SUBSET s ==> finite_prefixes r s'`,
SRW_TAC [] [finite_prefixes_def, SUBSET_DEF]);

val finite_prefixes_subset_r = Q.store_thm ("finite_prefixes_subset_r",
`!r r' s. finite_prefixes r s /\ r' SUBSET r ==> finite_prefixes r' s`,
  SRW_TAC [] [finite_prefixes_def, SUBSET_DEF] THEN
  RES_TAC THEN IMP_RES_THEN MATCH_MP_TAC SUBSET_FINITE THEN
  SRW_TAC [] [SUBSET_DEF]);

val finite_prefixes_subset_rs = Q.store_thm ("finite_prefixes_subset_rs",
`!r s r' s'. finite_prefixes r s ==> r' SUBSET r ==> s' SUBSET s ==>
  finite_prefixes r' s'`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC finite_prefixes_subset_r THEN
  IMP_RES_TAC finite_prefixes_subset_s) ;

val finite_prefixes_subset = Q.store_thm ("finite_prefixes_subset",
`!r s s'.
  finite_prefixes r s /\ s' SUBSET s
  ==>
  finite_prefixes r s' /\ finite_prefixes (rrestrict r s') s'`,
SRW_TAC [] [finite_prefixes_def, SUBSET_DEF, rrestrict_def, GSPEC_AND] THEN
METIS_TAC [INTER_FINITE, INTER_COMM]);

val finite_prefixes_union = Q.store_thm ("finite_prefixes_union",
`!r1 r2 s1 s2.
  finite_prefixes r1 s1 /\ finite_prefixes r2 s2
  ==>
  finite_prefixes (r1 UNION r2) (s1 INTER s2)`,
SRW_TAC [] [finite_prefixes_def, GSPEC_OR]);

val finite_prefixes_comp = Q.store_thm ("finite_prefixes_comp",
`!r1 r2 s1 s2.
  finite_prefixes r1 s1 /\ finite_prefixes r2 s2 /\
  { x | ?y. y IN s2 /\ (x, y) IN r2 } SUBSET s1
  ==>
  finite_prefixes (rcomp r1 r2) s2`,
SRW_TAC [] [finite_prefixes_def, SUBSET_DEF, rcomp_def] THEN
`{ e' | ?z. (e', z) IN r1 /\ (z, e) IN r2 } =
 BIGUNION (IMAGE (\z. { e' | (e', z) IN r1}) { z | (z, e) IN r2 })`
        by (SRW_TAC [] [EXTENSION] THEN
            EQ_TAC THEN
            SRW_TAC [] [] THENL
            [Q.EXISTS_TAC `{ x | (x, z) IN r1 }` THEN
                 SRW_TAC [] [] THEN
                 METIS_TAC [],
             METIS_TAC []]) THEN
SRW_TAC [] [] THEN
METIS_TAC []);

val finite_prefixes_inj_image = Q.store_thm ("finite_prefixes_inj_image",
`!f r s.
  (!x y. (f x = f y) ==> (x = y)) /\
  finite_prefixes r s
  ==>
  finite_prefixes { (f x, f y) | (x, y) IN r } (IMAGE f s)`,
SRW_TAC [] [finite_prefixes_def] THEN
`{e' | ?x' y. ((e' = f x') /\ (f x = f y)) /\ (x',y) IN r}
 SUBSET
 IMAGE f { e' | (e', x) IN r }`
        by (SRW_TAC [] [SUBSET_DEF] THEN
            METIS_TAC []) THEN
METIS_TAC [SUBSET_FINITE, IMAGE_FINITE]);

val finite_prefixes_range = Q.store_thm ("finite_prefixes_range",
`!r s t. finite_prefixes r s /\ DISJOINT t (range r) ==>
  finite_prefixes r (s UNION t)`,
SRW_TAC [] [finite_prefixes_def, DISJOINT_DEF, range_def, INTER_DEF, EXTENSION] THEN1
METIS_TAC [] THEN
`{e' | (e', e) IN r} = {}`
        by (SRW_TAC [] [EXTENSION] THEN
            METIS_TAC []) THEN
METIS_TAC [FINITE_EMPTY]);

(* ------------------------------------------------------------------------ *)
(* Transitive closure                                                       *)
(* ------------------------------------------------------------------------ *)

val (tc_rules, tc_ind, tc_cases) = Hol_reln `
(!x y. r (x, y) ==> tc r (x, y)) /\
(!x y. (?z. tc r (x, z) /\ tc r (z, y)) ==> tc r (x, y))`;

val tc_rules = Q.store_thm ("tc_rules",
`!r.
  (!x y. (x,y) IN r ==> (x, y) IN tc r) /\
  (!x y. (?z. (x, z) IN tc r /\ (z, y) IN tc r) ==> (x, y) IN tc r)`,
SRW_TAC [] [SPECIFICATION, tc_rules]);

Theorem tc_cases:
  !r x y.
    (x, y) IN tc r <=>
      (x, y) IN r \/
      ?z. (x, z) IN tc r /\ (z, y) IN tc r
Proof
SRW_TAC [] [SPECIFICATION] THEN
SRW_TAC [] [Once (Q.SPECL [`r`, `(x, y)`] tc_cases)]
QED

val tc_ind = Q.store_thm ("tc_ind",
`!r tc'.
  (!x y. (x, y) IN r ==> tc' x y) /\
  (!x y. (?z. tc' x z /\ tc' z y) ==> tc' x y) ==>
  !x y. (x, y) IN tc r ==> tc' x y`,
SRW_TAC [] [SPECIFICATION] THEN
IMP_RES_TAC (SIMP_RULE (srw_ss()) [LAMBDA_PROD, GSYM PFORALL_THM]
             (Q.SPECL [`r`, `\(x, y). tc' x y`] tc_ind)));

val [tc_rule1', tc_rule2] = CONJUNCTS (SPEC_ALL tc_rules) ;
val tc_rule1 = Ho_Rewrite.REWRITE_RULE [GSYM FORALL_PROD] tc_rule1' ;

(** closure rules for tc **)

val tc_closure = Q.store_thm ("tc_closure",
  `r SUBSET tc s ==> tc r SUBSET tc s`,
  Ho_Rewrite.REWRITE_TAC [SUBSET_DEF, FORALL_PROD] THEN DISCH_TAC THEN
  HO_MATCH_MP_TAC tc_ind THEN CONJ_TAC
  THENL [ POP_ASSUM ACCEPT_TAC, MATCH_ACCEPT_TAC tc_rule2]) ;

val subset_tc = Q.store_thm ("subset_tc",
  `r SUBSET tc r`,
  Ho_Rewrite.REWRITE_TAC [SUBSET_DEF, FORALL_PROD] THEN
  MATCH_ACCEPT_TAC tc_rule1) ;

val tc_idemp = Q.store_thm ("tc_idemp",
  `tc (tc r) = tc r`,
  REWRITE_TAC [SET_EQ_SUBSET] THEN CONJ_TAC
  THENL [irule tc_closure THEN irule SUBSET_REFL, irule subset_tc]) ;

val tc_mono = Q.store_thm ("tc_mono",
  `r SUBSET s ==> tc r SUBSET tc s`,
  DISCH_TAC THEN irule tc_closure THEN
  irule SUBSET_TRANS THEN Q.EXISTS_TAC `s` THEN
  ASM_REWRITE_TAC [subset_tc]) ;

val tc_strongind = Q.store_thm ("tc_strongind",
`!r tc'.
  (!x y. (x, y) IN r ==> tc' x y) /\
  (!x y. (?z. (x,z) IN tc r /\ tc' x z /\ (z,y) IN tc r /\ tc' z y) ==> tc' x y) ==>
  !x y. (x, y) IN tc r ==> tc' x y`,
SRW_TAC [] [SPECIFICATION] THEN
IMP_RES_TAC (SIMP_RULE (srw_ss()) [LAMBDA_PROD, GSYM PFORALL_THM]
             (Q.SPECL [`r`, `\(x, y). tc' x y`] (fetch "-" "tc_strongind"))));

val tc_cases_lem = Q.prove (
`!x y.
  (x, y) IN tc r
  ==>
  (x, y) IN r \/
  ((?z. (x, z) IN tc r /\ (z, y) IN r) /\
   (?z. (x, z) IN r /\ (z, y) IN tc r))`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
METIS_TAC [tc_rules]);

Theorem tc_cases_right:
  !r x y.
    (x, y) IN tc r <=>
      (x, y) IN r \/
      ?z. (x, z) IN tc r /\ (z, y) IN r
Proof METIS_TAC [tc_cases_lem, tc_rules]
QED

Theorem tc_cases_left:
  !r x y.
    (x, y) IN tc r <=>
      (x, y) IN r \/
      ?z. (x, z) IN r /\ (z, y) IN tc r
Proof METIS_TAC [tc_cases_lem, tc_rules]
QED

val tc_ind_left_lem = Q.prove (
`!r P.
  (!x y. (x, y) IN r ==> P x y) /\
  (!x y. (?z. (x, z) IN r /\ P z y) ==> P x y)
  ==>
  (!x y. (x, y) IN tc r ==> (!z. P x y /\ P y z ==> P x z) /\ P x y)`,
NTAC 3 STRIP_TAC THEN
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
METIS_TAC []);

val tc_ind_left = Q.store_thm ("tc_ind_left",
`!r tc'.
  (!x y. (x, y) IN r ==> tc' x y) /\
  (!x y. (?z. (x, z) IN r /\ tc' z y) ==> tc' x y)
  ==>
  (!x y. (x, y) IN tc r ==> tc' x y)`,
METIS_TAC [tc_ind_left_lem]);

val tc_strongind_left_lem = Q.prove (
`!r P.
  (!x y. (x, y) IN r ==> P x y) /\
  (!x y. (?z. (x, z) IN r /\ (z,y) IN tc r /\ P z y) ==> P x y)
  ==>
  (!x y. (x, y) IN tc r ==>
         (!z. P x y /\ P y z /\ (y,z) IN tc r ==> P x z) /\ P x y)`,
NTAC 3 STRIP_TAC THEN
HO_MATCH_MP_TAC tc_strongind THEN
SRW_TAC [] [] THEN
METIS_TAC [tc_rules]);

val tc_strongind_left = Q.store_thm ("tc_strongind_left",
`!r tc'.
  (!x y. (x, y) IN r ==> tc' x y) /\
  (!x y. (?z. (x, z) IN r /\ (z,y) IN tc r /\ tc' z y) ==> tc' x y)
  ==>
  (!x y. (x, y) IN tc r ==> tc' x y)`,
METIS_TAC [tc_strongind_left_lem]);

val tc_ind_right_lem = Q.prove (
`!r P.
  (!x y. (x, y) IN r ==> P x y) /\
  (!x y. (?z. P x z /\ (z, y) IN r) ==> P x y)
  ==>
  (!x y. (x, y) IN tc r ==> (!z. P z x /\ P x y ==> P z y) /\ P x y)`,
NTAC 3 STRIP_TAC THEN
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
METIS_TAC []);

val tc_ind_right = Q.store_thm ("tc_ind_right",
`!r tc'.
  (!x y. (x, y) IN r ==> tc' x y) /\
  (!x y. (?z. tc' x z /\ (z, y) IN r) ==> tc' x y)
  ==>
  (!x y. (x, y) IN tc r ==> tc' x y)`,
METIS_TAC [tc_ind_right_lem]);

val rtc_ind_right = Q.store_thm ("rtc_ind_right",
`!r tc'.
  (!x. x IN domain r \/ x IN range r ==> tc' x x) /\
  (!x y. (?z. tc' x z /\ (z,y) IN r) ==> tc' x y)
  ==>
  (!x y. (x,y) IN tc r ==> tc' x y)`,
NTAC 3 STRIP_TAC THEN
HO_MATCH_MP_TAC tc_ind_right THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [domain_def, range_def] THEN
METIS_TAC []);

val tc_strongind_right_lem = Q.prove (
`!r P.
  (!x y. (x, y) IN r ==> P x y) /\
  (!x y. (?z. (x,z) IN tc r /\ P x z /\ (z, y) IN r) ==> P x y)
  ==>
  (!x y. (x, y) IN tc r ==>
         (!z. (z,x) IN tc r /\ P z x /\ P x y ==> P z y) /\ P x y)`,
NTAC 3 STRIP_TAC THEN
HO_MATCH_MP_TAC tc_strongind THEN
SRW_TAC [] [] THEN
METIS_TAC [tc_rules]);

val tc_strongind_right = Q.store_thm ("tc_strongind_right",
`!r tc'.
  (!x y. (x, y) IN r ==> tc' x y) /\
  (!x y. (?z. (x,z) IN tc r /\ tc' x z /\ (z, y) IN r) ==> tc' x y)
  ==>
  (!x y. (x, y) IN tc r ==> tc' x y)`,
METIS_TAC [tc_strongind_right_lem]);

val tc_union = Q.store_thm ("tc_union",
`!x y. (x, y) IN tc r1 ==> !r2. (x, y) IN tc (r1 UNION r2)`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THENL
[SRW_TAC [] [Once tc_cases],
 METIS_TAC [tc_rules]]);

val tc_implication_lem = Q.prove (
`!x y. (x, y) IN tc r1 ==>
       !r2. (!x y. (x, y) IN r1 ==> (x, y) IN r2) ==> (x, y) IN tc r2`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
METIS_TAC [tc_rules]);

val tc_implication = Q.store_thm ("tc_implication",
`!r1 r2. (!x y. (x, y) IN r1 ==> (x, y) IN r2) ==>
         (!x y. (x, y) IN tc r1 ==> (x, y) IN tc r2)`,
METIS_TAC [tc_implication_lem]);

val tc_empty = Q.prove (
`!x y. (x, y) IN tc {} ==> F`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] []);

val _ = save_thm ("tc_empty", SIMP_RULE (srw_ss()) [] tc_empty);

val tc_empty_eqn = Q.store_thm(
  "tc_empty_eqn[simp]",
  `tc {} = {}`,
  asm_simp_tac(srw_ss())[EXTENSION, pairTheory.FORALL_PROD, tc_empty])

val tc_domain_range = Q.store_thm ("tc_domain_range",
`!x y. (x, y) IN tc r ==> x IN domain r /\ y IN range r`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [domain_def, range_def] THEN
METIS_TAC []);

val rrestrict_tc = Q.store_thm ("rrestrict_tc",
`!e e'. (e, e') IN tc (rrestrict r x) ==> (e, e') IN tc r`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [rrestrict_def] THEN
METIS_TAC [tc_rules]);

val pair_in_IMAGE_SWAP = Q.prove (
  `((a, b) IN IMAGE SWAP r) = ((b, a) IN r)`,
  Ho_Rewrite.REWRITE_TAC [IN_IMAGE, EXISTS_PROD, SWAP_def,
    FST, SND, PAIR_EQ] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN PROVE_TAC []) ;

val tc_ind' = Ho_Rewrite.REWRITE_RULE [PULL_FORALL] tc_ind ;

val tc_SWAP = Q.store_thm ("tc_SWAP",
  `tc (IMAGE SWAP r) = IMAGE SWAP (tc r)`,
  Ho_Rewrite.REWRITE_TAC [SET_EQ_SUBSET, SUBSET_DEF,
    FORALL_PROD, pair_in_IMAGE_SWAP] THEN CONJ_TAC
  THENL [
    HO_MATCH_MP_TAC tc_ind THEN
    REWRITE_TAC [pair_in_IMAGE_SWAP] THEN REPEAT STRIP_TAC
    THENL [IMP_RES_TAC tc_rule1, IMP_RES_TAC tc_rule2],
    REPEAT GEN_TAC THEN HO_MATCH_MP_TAC tc_ind' THEN REPEAT STRIP_TAC
    THENL [irule tc_rule1 THEN ASM_REWRITE_TAC [pair_in_IMAGE_SWAP],
      IMP_RES_TAC tc_rule2]]) ;

(* ------------------------------------------------------------------------ *)
(* Acyclic relations                                                        *)
(* ------------------------------------------------------------------------ *)

val acyclic_def = Define `
  acyclic r = !x. (x, x) NOTIN tc r`;

val acyclic_subset = Q.store_thm ("acyclic_subset",
`!r1 r2. acyclic r1 /\ r2 SUBSET r1 ==> acyclic r2`,
SRW_TAC [] [acyclic_def, SUBSET_DEF] THEN
METIS_TAC [tc_implication_lem]);

val acyclic_union = Q.store_thm ("acyclic_union",
`!r1 r2. acyclic (r1 UNION r2) ==> acyclic r1 /\ acyclic r2`,
SRW_TAC [] [acyclic_def] THEN
METIS_TAC [tc_union, UNION_COMM]);

val acyclic_rrestrict = Q.store_thm ("acyclic_rrestrict",
`!r s. acyclic r ==> acyclic (rrestrict r s)`,
SRW_TAC [] [rrestrict_def] THEN
`r = {(x,y) | (x,y) IN r /\ x IN s /\ y IN s} UNION r`
        by SRW_TAC [] [UNION_DEF, rextension, EQ_IMP_THM] THEN
METIS_TAC [acyclic_union]);

val acyclic_irreflexive = Q.store_thm ("acyclic_irreflexive",
`!r x. acyclic r ==> (x, x) NOTIN r`,
SRW_TAC [] [acyclic_def] THEN
METIS_TAC [tc_cases]);

val acyclic_SWAP = Q.store_thm ("acyclic_SWAP",
  `acyclic (IMAGE SWAP r) = acyclic r`,
  REWRITE_TAC [acyclic_def, tc_SWAP, pair_in_IMAGE_SWAP]) ;

val tc_BIGUNION_lem = Q.prove (
`!x y. (x, y) IN tc (BIGUNION rs) ==>
(!r r'.
  r IN rs /\ r' IN rs /\ r <> r'
  ==>
  DISJOINT (domain r UNION range r) (domain r' UNION range r')) ==>
?r. r IN rs /\ (x, y) IN tc r`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN1
METIS_TAC [tc_rules] THEN
RES_TAC THEN
IMP_RES_TAC tc_domain_range THEN
FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
`r = r'`
        by (SRW_TAC [] [EXTENSION] THEN
            METIS_TAC []) THEN
METIS_TAC [tc_rules]);

val acyclic_bigunion = Q.store_thm ("acyclic_bigunion",
`!rs.
  (!r r'.
    r IN rs /\ r' IN rs /\ r <> r'
    ==>
    DISJOINT (domain r UNION range r) (domain r' UNION range r')) /\
  (!r. r IN rs ==> acyclic r)
  ==>
  acyclic (BIGUNION rs)`,
SRW_TAC [] [acyclic_def] THEN
CCONTR_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC tc_BIGUNION_lem THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);

val acyclic_union = Q.store_thm ("acyclic_union",
`!r r'.
  DISJOINT (domain r UNION range r) (domain r' UNION range r') /\
  acyclic r /\
  acyclic r'
  ==>
  acyclic (r UNION r')`,
SRW_TAC [] [] THEN
MATCH_MP_TAC (SIMP_RULE (srw_ss()) [] (Q.SPEC `{r; r'}` acyclic_bigunion)) THEN
SRW_TAC [] [] THEN
METIS_TAC [DISJOINT_SYM]);

(* ------------------------------------------------------------------------ *)
(*  Orders                                                                  *)
(* ------------------------------------------------------------------------ *)

val reflexive_def = Define `
  reflexive r s = !x. x IN s ==> (x, x) IN r`;

val irreflexive_def = Define `
  irreflexive r s = !x. x IN s ==> (x, x) NOTIN r`;

val transitive_def = Define `
  transitive r =
    !x y z.  (x, y) IN r /\ (y, z) IN r ==> (x, z) IN r`;
val _ = ot "transitive"

val transitive_tc_lem = Q.prove (
`!x y. (x, y) IN tc r ==> transitive r ==> (x, y) IN r`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [transitive_def] THEN
METIS_TAC []);

val transitive_tc = Q.store_thm ("transitive_tc",
`!r. transitive r ==> (tc r = r)`,
SRW_TAC [] [EXTENSION] THEN
EQ_TAC THEN
SRW_TAC [] [] THEN
Cases_on `x` THEN1
METIS_TAC [transitive_tc_lem] THEN
FULL_SIMP_TAC (srw_ss()) [transitive_def] THEN
METIS_TAC [tc_rules]);

val tc_transitive = Q.store_thm ("tc_transitive",
`!r. transitive (tc r)`,
SRW_TAC [] [transitive_def] THEN
METIS_TAC [tc_rules]);

val antisym_def = Define `
  antisym r = !x y. (x, y) IN r /\ (y, x) IN r ==> (x = y)`;
val _ = ot0 "antisym" "antisymmetric"

val partial_order_def = Define `
  partial_order r s <=>
       domain r SUBSET s /\ range r SUBSET s /\
       transitive r /\ reflexive r s /\ antisym r`;

val antisym_subset = Q.store_thm ("antisym_subset",
  `antisym t ==> s SUBSET t ==> antisym s`,
  REWRITE_TAC [antisym_def, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []) ;

val partial_order_dom_rng = Q.store_thm ("partial_order_dom_rng",
`!r s x y. (x, y) IN r /\ partial_order r s ==> x IN s /\ y IN s`,
SRW_TAC [] [partial_order_def, domain_def, range_def, SUBSET_DEF] THEN
METIS_TAC []);

val partial_order_subset = Q.store_thm ("partial_order_subset",
`!r s s'.
  partial_order r s /\ s' SUBSET s ==> partial_order (rrestrict r s') s'`,
SRW_TAC [] [partial_order_def, SUBSET_DEF, reflexive_def, transitive_def,
       antisym_def, domain_def, range_def, rrestrict_def] THEN
METIS_TAC []);

val strict_partial_order = Q.store_thm ("strict_partial_order",
`!r s.
  partial_order r s
  ==>
  domain (strict r) SUBSET s /\ range (strict r) SUBSET s /\
  transitive (strict r) /\ antisym (strict r)`,
SRW_TAC [] [domain_def, SUBSET_DEF, range_def, partial_order_def, strict_def]
THENL
[METIS_TAC [],
 METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [transitive_def, strict_def, antisym_def] THEN
     METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [antisym_def] THEN
     METIS_TAC []]);

val strict_partial_order_acyclic = Q.store_thm ("strict_partial_order_acyclic",
`!r s. partial_order r s ==> acyclic (strict r)`,
SRW_TAC [] [acyclic_def] THEN
IMP_RES_TAC strict_partial_order THEN
SRW_TAC [] [transitive_tc, strict_def]);

val linear_order_def = Define `
  linear_order r s <=>
    domain r SUBSET s /\ range r SUBSET s /\
    transitive r /\ antisym r /\
    (!x y. x IN s /\ y IN s ==> (x, y) IN r \/ (y, x) IN r)`;
val _ = ot0 "linear_order" "linearOrder"

val linear_order_subset = Q.store_thm ("linear_order_subset",
`!r s s'.
  linear_order r s /\ s' SUBSET s ==> linear_order (rrestrict r s') s'`,
SRW_TAC [] [linear_order_def, SUBSET_DEF, transitive_def,
       antisym_def, domain_def, range_def, rrestrict_def] THEN
METIS_TAC []);

val partial_order_linear_order = Q.store_thm ("partial_order_linear_order",
`!r s. linear_order r s ==> partial_order r s`,
SRW_TAC [] [linear_order_def, partial_order_def, reflexive_def] THEN
METIS_TAC []);

val strict_linear_order_def = Define `
  strict_linear_order r s <=>
    domain r SUBSET s /\ range r SUBSET s /\
    transitive r /\
    (!x. (x, x) NOTIN r) /\
    (!x y. x IN s /\ y IN s /\ x <> y ==> (x, y) IN r \/ (y, x) IN r)`;

val strict_linear_order_dom_rng = Q.store_thm ("strict_linear_order_dom_rng",
`!r s x y. (x, y) IN r /\ strict_linear_order r s ==> x IN s /\ y IN s`,
SRW_TAC [] [strict_linear_order_def, domain_def, range_def, SUBSET_DEF] THEN
METIS_TAC []);

val linear_order_dom_rng = Q.store_thm ("linear_order_dom_rng",
`!r s x y. (x, y) IN r /\ linear_order r s ==> x IN s /\ y IN s`,
SRW_TAC [] [linear_order_def, domain_def, range_def, SUBSET_DEF] THEN
METIS_TAC []);

(* ------------------------------------------------------------------------ *)
(*  Link to relation theory                                                 *)
(* ------------------------------------------------------------------------ *)
val reln_to_rel_def = Define `reln_to_rel r = (\x y. (x,y) IN r)`
val rel_to_reln_def = Define `rel_to_reln R = {(x, y) | x, y | R x y}`
val RRUNIV_def = Define `RRUNIV s = (\x y. x IN s /\ y IN s)`
val RREFL_EXP_def = Define `RREFL_EXP R s = (R RUNION (\x y. (x = y) /\ ~(x IN s) ))`

val RREFL_EXP_RSUBSET = Q.store_thm ("RREFL_EXP_RSUBSET",
`R RSUBSET (RREFL_EXP R s)`,
SRW_TAC [] [RSUBSET, RREFL_EXP_def, RUNION]);

val RREFL_EXP_UNIV = Q.store_thm ("RREFL_EXP_UNIV",
`RREFL_EXP R UNIV = R`,
SRW_TAC [] [FUN_EQ_THM, RREFL_EXP_def, RUNION]);

val REL_RESTRICT_UNIV = Q.store_thm ("REL_RESTRICT_UNIV",
`REL_RESTRICT R UNIV = R`,
SRW_TAC [] [FUN_EQ_THM, REL_RESTRICT_DEF, RINTER, RRUNIV_def]);

Theorem in_rel_to_reln:
  xy IN (rel_to_reln R) <=> R (FST xy) (SND xy)
Proof
  Cases_on `xy` THEN SRW_TAC [] [rel_to_reln_def]
QED

Theorem reln_to_rel_app:
  (reln_to_rel r) x y <=> (x, y) IN r
Proof
  SRW_TAC [] [reln_to_rel_def]
QED

val rel_to_reln_IS_UNCURRY = Q.store_thm ("rel_to_reln_IS_UNCURRY",
  `rel_to_reln = UNCURRY`,
  REWRITE_TAC [FUN_EQ_THM,
    REWRITE_RULE [IN_APP] in_rel_to_reln, UNCURRY_VAR]) ;

val reln_to_rel_IS_CURRY = Q.store_thm ("reln_to_rel_IS_CURRY",
  `reln_to_rel = CURRY`,
  REWRITE_TAC [FUN_EQ_THM, CURRY_DEF, reln_to_rel_app, IN_APP]) ;

val rel_to_reln_inv = Q.store_thm ("rel_to_reln_inv",
`reln_to_rel (rel_to_reln R) = R`,
SRW_TAC [] [reln_to_rel_def, rel_to_reln_def, FUN_EQ_THM])

val reln_to_rel_inv = Q.store_thm ("reln_to_rel_inv",
`rel_to_reln (reln_to_rel r) = r`,
SRW_TAC [] [reln_to_rel_app, EXTENSION, in_rel_to_reln]);

val reln_to_rel_11 = Q.store_thm ("reln_to_rel_11",
`(reln_to_rel r1 = reln_to_rel r2) <=> (r1 = r2)`,
SRW_TAC [] [reln_to_rel_app, FUN_EQ_THM, FORALL_PROD, IN_DEF])

val rel_to_reln_11 = Q.store_thm ("rel_to_reln_11",
`(rel_to_reln R1 = rel_to_reln R2) <=> (R1 = R2)`,
SRW_TAC [] [in_rel_to_reln, EXTENSION, FORALL_PROD] THEN
SRW_TAC [] [FUN_EQ_THM]);

val reln_rel_conv_props =
LIST_CONJ [in_rel_to_reln, reln_to_rel_app, rel_to_reln_inv, reln_to_rel_inv,
reln_to_rel_11, rel_to_reln_11]

val rel_to_reln_swap = Q.store_thm("rel_to_reln_swap",
`(r = rel_to_reln R) <=> (reln_to_rel r = R)`,
METIS_TAC [rel_to_reln_inv, reln_to_rel_inv]);

val domain_to_rel_conv = Q.store_thm ("domain_to_rel_conv",
  `domain r = RDOM (reln_to_rel r)`,
SRW_TAC [] [domain_def, EXTENSION, IN_RDOM, reln_rel_conv_props])

val range_to_rel_conv = Q.store_thm ("range_to_rel_conv",
  `range r = RRANGE (reln_to_rel r)`,
SRW_TAC [] [range_def, EXTENSION, IN_RRANGE, reln_rel_conv_props])

val strict_to_rel_conv = Q.store_thm ("strict_to_rel_conv",
  `strict r = rel_to_reln (STRORD (reln_to_rel r))`,
SRW_TAC [] [strict_def, rextension, reln_rel_conv_props, STRORD]);

val rrestrict_to_rel_conv = Q.store_thm ("rrestrict_to_rel_conv",
  `rrestrict r s = rel_to_reln (REL_RESTRICT (reln_to_rel r) s)`,
SRW_TAC [boolSimps.EQUIV_EXTRACT_ss] [rrestrict_def, rextension, reln_rel_conv_props, REL_RESTRICT_DEF, RINTER, RRUNIV_def])

val rcomp_to_rel_conv = Q.store_thm ("rcomp_to_rel_conv",
  `r1 OO r2 = rel_to_reln ((reln_to_rel r2) O (reln_to_rel r1))`,
SRW_TAC [] [rcomp_def, rextension, reln_rel_conv_props, relationTheory.O_DEF])

val univ_reln_to_rel_conv = Q.store_thm ("univ_reln_to_rel_conv",
  `univ_reln s = rel_to_reln (RRUNIV s)`,
SRW_TAC [] [univ_reln_def, rextension, reln_rel_conv_props, RRUNIV_def])

val tc_to_rel_conv = Q.store_thm ("tc_to_rel_conv",
`tc r = rel_to_reln ((reln_to_rel r)^+)`,
SRW_TAC [] [rextension, reln_rel_conv_props] THEN
EQ_TAC THENL [
  MATCH_MP_TAC tc_ind THEN
  METIS_TAC [TC_RULES, reln_to_rel_app],

  Q.SPEC_TAC (`y`, `y`) THEN
  Q.SPEC_TAC (`x`, `x`) THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN
  METIS_TAC [tc_rules, reln_to_rel_app]
])

val acyclic_reln_to_rel_conv = Q.store_thm ("acyclic_reln_to_rel_conv",
`acyclic r = irreflexive ((reln_to_rel r)^+)`,
SRW_TAC [] [acyclic_def, tc_to_rel_conv, reln_rel_conv_props] THEN
SRW_TAC [] [FUN_EQ_THM, relationTheory.irreflexive_def])

val irreflexive_reln_to_rel_conv = Q.store_thm ("irreflexive_reln_to_rel_conv",
`(set_relation$irreflexive) r s = (relation$irreflexive) (REL_RESTRICT (reln_to_rel r) s)`,
SRW_TAC [] [irreflexive_def, relationTheory.irreflexive_def, REL_RESTRICT_DEF, RINTER, RRUNIV_def, reln_rel_conv_props] THEN
PROVE_TAC[])

val irreflexive_reln_to_rel_conv_UNIV = Q.store_thm ("irreflexive_reln_to_rel_conv_UNIV",
`(set_relation$irreflexive) r UNIV = (relation$irreflexive) (reln_to_rel r)`,
SIMP_TAC std_ss [irreflexive_reln_to_rel_conv, REL_RESTRICT_UNIV])

val reflexive_reln_to_rel_conv = Q.store_thm ("reflexive_reln_to_rel_conv",
`(set_relation$reflexive) r s = (relation$reflexive) (RREFL_EXP (reln_to_rel r) s)`,
SRW_TAC [] [reflexive_def, relationTheory.reflexive_def, reln_rel_conv_props, RREFL_EXP_def, RUNION, RRUNIV_def] THEN
PROVE_TAC[])

val reflexive_reln_to_rel_conv_UNIV = Q.store_thm ("reflexive_reln_to_rel_conv_UNIV",
`(set_relation$reflexive) r UNIV = (relation$reflexive) (reln_to_rel r)`,
REWRITE_TAC[reflexive_reln_to_rel_conv, RREFL_EXP_UNIV])

val transitive_reln_to_rel_conv = Q.store_thm ("transitive_reln_to_rel_conv",
`(set_relation$transitive) r = (relation$transitive) (reln_to_rel r)`,
SRW_TAC [] [transitive_def, relationTheory.transitive_def, reln_rel_conv_props])

val antisym_reln_to_rel_conv = Q.store_thm ("antisym_reln_to_rel_conv",
`(set_relation$antisym) r = (relation$antisymmetric) (reln_to_rel r)`,
SRW_TAC [] [antisym_def, relationTheory.antisymmetric_def, reln_rel_conv_props])

local

val aux1 = prove(``((reln_to_rel r) RSUBSET RRUNIV s) =
  (domain r SUBSET s /\ range r SUBSET s)``,
SRW_TAC [] [RSUBSET, RRUNIV_def, domain_def, range_def, reln_to_rel_app, SUBSET_DEF] THEN
PROVE_TAC[])

val aux2 = prove(``(domain r SUBSET s /\ range r SUBSET s) ==>
   (transitive (RREFL_EXP (reln_to_rel r) s) =
    transitive (reln_to_rel r))``,
SRW_TAC [] [relationTheory.transitive_def, RREFL_EXP_def, RUNION, reln_to_rel_app, SUBSET_DEF, in_range, in_domain,
  GSYM LEFT_FORALL_IMP_THM] THEN
PROVE_TAC[])

val aux3 = prove(``(domain r SUBSET s /\ range r SUBSET s) ==>
   (antisymmetric (RREFL_EXP (reln_to_rel r) s) =
    antisymmetric (reln_to_rel r))``,
SRW_TAC [] [relationTheory.antisymmetric_def, RREFL_EXP_def, RUNION, reln_to_rel_app, SUBSET_DEF, in_range, in_domain,
  GSYM LEFT_FORALL_IMP_THM] THEN
PROVE_TAC[])

in

Theorem partial_order_reln_to_rel_conv:
  partial_order r s <=> reln_to_rel r RSUBSET RRUNIV s /\
                        WeakOrder (RREFL_EXP (reln_to_rel r) s)
Proof
SRW_TAC [boolSimps.EQUIV_EXTRACT_ss] [partial_order_def, WeakOrder, reflexive_reln_to_rel_conv,
  transitive_reln_to_rel_conv, antisym_reln_to_rel_conv,
  aux1, aux2, aux3]
QED

val partial_order_reln_to_rel_conv_UNIV = Q.store_thm ("partial_order_reln_to_rel_conv_UNIV",
`partial_order r UNIV = WeakOrder (reln_to_rel r)`,
SRW_TAC [] [partial_order_reln_to_rel_conv, RREFL_EXP_UNIV, RSUBSET, RRUNIV_def]);

end

val linear_order_reln_to_rel_conv_UNIV = Q.store_thm ("linear_order_reln_to_rel_conv_UNIV",
`linear_order r UNIV = WeakLinearOrder (reln_to_rel r)`,
SRW_TAC [] [linear_order_def, WeakLinearOrder_dichotomy, reflexive_reln_to_rel_conv_UNIV,
  transitive_reln_to_rel_conv, antisym_reln_to_rel_conv, WeakOrder,
  relationTheory.reflexive_def, reln_to_rel_app] THEN
PROVE_TAC[]);

val strict_linear_order_reln_to_rel_conv_UNIV = Q.store_thm ("strict_linear_order_reln_to_rel_conv_UNIV",
`strict_linear_order r UNIV = StrongLinearOrder (reln_to_rel r)`,
SRW_TAC [] [strict_linear_order_def, StrongLinearOrder, reflexive_reln_to_rel_conv_UNIV,
  transitive_reln_to_rel_conv, antisym_reln_to_rel_conv, StrongOrder,
  relationTheory.irreflexive_def, reln_to_rel_app, trichotomous] THEN
PROVE_TAC[]);

val reln_rel_conv_thms = save_thm ("reln_rel_conv_thms", LIST_CONJ [
  reln_rel_conv_props,
  RREFL_EXP_UNIV,
  REL_RESTRICT_UNIV,
  domain_to_rel_conv,
  range_to_rel_conv,
  strict_to_rel_conv,
  rrestrict_to_rel_conv,
  rcomp_to_rel_conv,
  univ_reln_to_rel_conv,
  tc_to_rel_conv,
  acyclic_reln_to_rel_conv,
  irreflexive_reln_to_rel_conv,
  reflexive_reln_to_rel_conv,
  transitive_reln_to_rel_conv,
  antisym_reln_to_rel_conv,
  partial_order_reln_to_rel_conv_UNIV,
  linear_order_reln_to_rel_conv_UNIV,
  strict_linear_order_reln_to_rel_conv_UNIV])


val acyclic_WF = Q.store_thm ("acyclic_WF",
`FINITE s /\ acyclic r /\ domain r SUBSET s /\ range r SUBSET s ==>
 WF (reln_to_rel r)`,
REPEAT STRIP_TAC THEN
`(REL_RESTRICT (reln_to_rel r) s) = (reln_to_rel r)` by (
  FULL_SIMP_TAC std_ss [SUBSET_DEF, in_domain, in_range,
                        GSYM LEFT_FORALL_IMP_THM, FUN_EQ_THM,
                        REL_RESTRICT_DEF, reln_to_rel_app] THEN
  PROVE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [acyclic_reln_to_rel_conv] THEN
PROVE_TAC[FINITE_WF_noloops]);

(* ------------------------------------------------------------------------ *)
(* Minimal and maximal elements                                             *)
(* ------------------------------------------------------------------------ *)

val maximal_elements_def = Define `
  maximal_elements xs r =
    {x | x IN xs /\ !x'. x' IN xs /\ (x, x') IN r ==> (x = x')}`;

val minimal_elements_def = Define `
  minimal_elements xs r =
    {x | x IN xs /\ !x'. x' IN xs /\ (x', x) IN r ==> (x = x')}`;
val _ = ot0 "minimal_elements" "minimalElements"

val minimal_elements_subset = Q.store_thm ("minimal_elements_subset",
  `minimal_elements s lo SUBSET s`,
  SRW_TAC [] [SUBSET_DEF, minimal_elements_def]) ;

val minimal_elements_SWAP = Q.store_thm ("minimal_elements_SWAP",
  `minimal_elements xs (IMAGE SWAP r) = maximal_elements xs r`,
  REWRITE_TAC [minimal_elements_def, maximal_elements_def,
    EXTENSION, pair_in_IMAGE_SWAP]) ;

val maximal_union = Q.store_thm ("maximal_union",
`!e s r1 r2.
  e IN maximal_elements s (r1 UNION r2)
  ==>
  e IN maximal_elements s r1 /\
  e IN maximal_elements s r2`,
SRW_TAC [] [maximal_elements_def]);

val minimal_union = Q.store_thm ("minimal_union",
`!e s r1 r2.
  e IN minimal_elements s (r1 UNION r2)
  ==>
  e IN minimal_elements s r1 /\
  e IN minimal_elements s r2`,
SRW_TAC [] [minimal_elements_def]);

val minimal_elements_mono = Q.store_thm ("minimal_elements_mono",
  `r SUBSET r' ==> minimal_elements xs r' SUBSET minimal_elements xs r`,
  Ho_Rewrite.REWRITE_TAC [minimal_elements_def, SUBSET_DEF, IN_GSPEC_IFF] THEN
  REPEAT STRIP_TAC THENL [FIRST_ASSUM ACCEPT_TAC, REPEAT RES_TAC]) ;

val minimal_elements_rrestrict = Q.store_thm ("minimal_elements_rrestrict",
  `minimal_elements xs (rrestrict r xs) = minimal_elements xs r`,
  Ho_Rewrite.REWRITE_TAC [minimal_elements_def,
    in_rrestrict, EXTENSION, IN_GSPEC_IFF] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE RES_TAC)) ;

val WF_has_minimal_path = Q.store_thm ("WF_has_minimal_path",
  `WF (reln_to_rel r) ==> x IN s ==>
    ?y. y IN minimal_elements s r /\ ((y,x) IN tc r \/ (y = x))`,
  Ho_Rewrite.REWRITE_TAC
    [WF_DEF, reln_to_rel_app, minimal_elements_def, IN_GSPEC_IFF] THEN
  REPEAT STRIP_TAC THEN
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH o
    Q.SPEC `\z. z IN s /\ ((z, x) IN tc r \/ (z = x))`))
  THENL [
    Q.EXISTS_TAC `x` THEN BETA_TAC THEN
    ASM_REWRITE_TAC [],
    POP_ASSUM CHOOSE_TAC THEN
    Q.EXISTS_TAC `min` THEN
    RULE_L_ASSUM_TAC (CONJUNCTS o BETA_RULE) THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN
    IMP_RES_TAC tc_rule1 THEN
    FIRST_ASSUM DISJ_CASES_TAC
    THENL [
      IMP_RES_TAC tc_rule2,
      BasicProvers.VAR_EQ_TAC] THEN
    RES_TAC]) ;

val tc_path_max_lem = Q.prove (
`!s. FINITE s ==>
     s <> {} ==> !r. acyclic r ==> ?x. x IN maximal_elements s (tc r)`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THEN
Cases_on `s={}` THEN1
SRW_TAC [] [maximal_elements_def] THEN
RES_TAC THEN
Cases_on `(x, e) IN (tc r)` THENL
[Q.EXISTS_TAC `e` THEN
     SRW_TAC [] [maximal_elements_def] THEN
     `(x, x'') IN (tc r)` by METIS_TAC [tc_rules] THEN
     FULL_SIMP_TAC (srw_ss()) [acyclic_def, maximal_elements_def] THEN
     METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [maximal_elements_def] THEN
     METIS_TAC []]);

val tc_path_min_lem = Q.prove (
`!s. FINITE s ==>
     s <> {} ==> !r. acyclic r ==> ?x. x IN minimal_elements s (tc r)`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THEN
Cases_on `s={}` THEN1
SRW_TAC [] [minimal_elements_def] THEN
RES_TAC THEN
Cases_on `(e, x) IN (tc r)` THENL
[Q.EXISTS_TAC `e` THEN
     SRW_TAC [] [minimal_elements_def] THEN
     `(x'', x) IN (tc r)` by METIS_TAC [tc_rules] THEN
     FULL_SIMP_TAC (srw_ss()) [acyclic_def, minimal_elements_def] THEN
     METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [minimal_elements_def] THEN
     METIS_TAC []]);

val finite_acyclic_has_maximal = Q.store_thm ("finite_acyclic_has_maximal",
`!s. FINITE s ==> s <> {} ==> !r. acyclic r ==> ?x. x IN maximal_elements s r`,
SRW_TAC [] [] THEN
IMP_RES_TAC tc_path_max_lem THEN
FULL_SIMP_TAC (srw_ss()) [maximal_elements_def] THEN
METIS_TAC [tc_rules]);

val finite_acyclic_has_minimal = Q.store_thm ("finite_acyclic_has_minimal",
`!s. FINITE s ==> s <> {} ==> !r. acyclic r ==> ?x. x IN minimal_elements s r`,
SRW_TAC [] [] THEN
IMP_RES_TAC tc_path_min_lem THEN
FULL_SIMP_TAC (srw_ss()) [minimal_elements_def] THEN
METIS_TAC [tc_rules]);

local

val lemma1 = Q.prove (
`!x y. (x, y) IN tc r ==> ?z. (x, z) IN r /\ (x <> y ==> x <> z)`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
METIS_TAC []);

in

val maximal_TC = Q.store_thm ("maximal_TC",
`!s r.
  domain r SUBSET s /\ range r SUBSET s
  ==>
  (maximal_elements s (tc r) = maximal_elements s r)`,
SRW_TAC [] [EXTENSION, maximal_elements_def, domain_def, range_def,
            SUBSET_DEF] THEN
EQ_TAC THEN
SRW_TAC [] [] THEN
METIS_TAC [lemma1, tc_rules]);

end;

local

val lemma1 = Q.prove (
`!y x. (y, x) IN tc r ==> ?z. (z, x) IN r /\ (x <> y ==> x <> z)`,
HO_MATCH_MP_TAC tc_ind THEN
SRW_TAC [] [] THEN
METIS_TAC []);

in

val minimal_TC = Q.store_thm ("minimal_TC",
`!s r.
  domain r SUBSET s /\ range r SUBSET s
  ==>
  (minimal_elements s (tc r) = minimal_elements s r)`,
SRW_TAC [] [EXTENSION, minimal_elements_def, domain_def, range_def,
            SUBSET_DEF] THEN
EQ_TAC THEN
SRW_TAC [] [] THEN
METIS_TAC [lemma1, tc_rules]);

end;

val rr_acyclic_WF = Q.INST [`r` |-> `rrestrict r s`] acyclic_WF ;
val rme = MATCH_MP WF_has_minimal_path (UNDISCH_ALL rr_acyclic_WF) ;
val irme = Q.INST [`s'` |-> `s`] rme ;
val urme = REWRITE_RULE [domain_rrestrict_SUBSET, range_rrestrict_SUBSET,
  minimal_elements_rrestrict] (DISCH_ALL irme) ;

val tcrr = REWRITE_RULE [SUBSET_DEF] (MATCH_MP tc_mono rrestrict_SUBSET) ;

val finite_acyclic_has_minimal_path = Q.store_thm
("finite_acyclic_has_minimal_path",
`!s r x.
  FINITE s /\
  acyclic r /\
  x IN s /\
  x NOTIN minimal_elements s r
  ==>
  ?y. y IN minimal_elements s r /\ (y, x) IN tc r`,
  REPEAT STRIP_TAC THEN
  IMP_RES_THEN (ASSUME_TAC o Q.SPEC `s`) acyclic_rrestrict THEN
  IMP_RES_TAC urme THEN
  TRY (BasicProvers.VAR_EQ_TAC THEN RES_TAC) THEN
  Q.EXISTS_TAC `y'` THEN
  ASM_REWRITE_TAC [] THEN
  IMP_RES_TAC tcrr) ;

val tc_SWAP' = REWRITE_RULE [rextension, pair_in_IMAGE_SWAP] tc_SWAP ;

val finite_acyclic_has_maximal_path = Q.store_thm
("finite_acyclic_has_maximal_path",
`!s r x.
  FINITE s /\
  acyclic r /\
  x IN s /\
  x NOTIN maximal_elements s r
  ==>
  ?y. y IN maximal_elements s r /\ (x, y) IN tc r`,
  ONCE_REWRITE_TAC [GSYM tc_SWAP', GSYM minimal_elements_SWAP,
    GSYM acyclic_SWAP] THEN REPEAT STRIP_TAC THEN
  irule finite_acyclic_has_minimal_path THEN rpt conj_tac THEN
  FIRST_ASSUM ACCEPT_TAC) ;

val finite_prefix_po_has_minimal_path = Q.store_thm
("finite_prefix_po_has_minimal_path",
`!r s x s'.
  partial_order r s /\
  finite_prefixes r s /\
  x NOTIN minimal_elements s' r /\
  x IN s' /\
  s' SUBSET s
  ==>
  ?x'. x' IN minimal_elements s' r /\ (x', x) IN r`,
SRW_TAC [] [finite_prefixes_def] THEN
IMP_RES_TAC strict_partial_order_acyclic THEN
`?x'. x' IN minimal_elements (s' INTER {x' | (x', x) IN r})
                             (strict r) /\
      (x', x) IN tc (strict r)`
        by (MATCH_MP_TAC finite_acyclic_has_minimal_path THEN
            SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, strict_def,
                                      SUBSET_DEF, partial_order_def,
                                      reflexive_def] THEN
            METIS_TAC [INTER_FINITE, INTER_COMM]) THEN
Q.EXISTS_TAC `x'` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [minimal_elements_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [partial_order_def, domain_def, SUBSET_DEF,
       transitive_def, strict_def] THEN
METIS_TAC []);

val empty_strict_linear_order = Q.store_thm ("empty_strict_linear_order",
`!r. strict_linear_order r {} = (r = {})`,
SRW_TAC [] [strict_linear_order_def, RES_FORALL_THM, domain_def, range_def,
            transitive_def, EXTENSION] THEN
EQ_TAC THEN
SRW_TAC [] [] THEN
Cases_on `x` THEN
SRW_TAC [] []);

val empty_linear_order = Q.store_thm ("empty_linear_order",
`!r. linear_order r {} = (r = {})`,
SRW_TAC [] [linear_order_def, RES_FORALL_THM, domain_def, range_def,
            transitive_def, antisym_def, EXTENSION] THEN
EQ_TAC THEN
SRW_TAC [] [] THEN
Cases_on `x` THEN
SRW_TAC [] []);

val linear_order_restrict = Q.store_thm ("linear_order_restrict",
`!s r s'. linear_order r s ==> linear_order (rrestrict r s') (s INTER s')`,
  Ho_Rewrite.REWRITE_TAC
    [linear_order_def, rrestrict_def, domain_def, range_def,
              SUBSET_DEF, transitive_def, antisym_def,
               IN_GSPEC_IFF, PAIR_IN_GSPEC_IFF, IN_INTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN_LT
  LASTGOAL (FIRST_X_ASSUM irule THEN rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  RES_TAC) ;

val strict_linear_order_restrict = Q.store_thm ("strict_linear_order_restrict",
`!s r s'.
  strict_linear_order r s
  ==>
  strict_linear_order (rrestrict r s') (s INTER s')`,
  Ho_Rewrite.REWRITE_TAC
    [strict_linear_order_def, rrestrict_def, domain_def, range_def,
              SUBSET_DEF, transitive_def, antisym_def,
               IN_GSPEC_IFF, PAIR_IN_GSPEC_IFF, IN_INTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN_LT
  LASTGOAL (FIRST_X_ASSUM irule >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) THEN
  RES_TAC) ;

val linear_order_dom_rg = Q.store_thm ("linear_order_dom_rg",
  `linear_order lo X ==> (domain lo UNION range lo = X)`,
  REWRITE_TAC [linear_order_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [SET_EQ_SUBSET, UNION_SUBSET] THEN
  REWRITE_TAC [SUBSET_DEF, IN_UNION, in_domain] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN DISJ1_TAC THEN
  Q.EXISTS_TAC `x` THEN POP_ASSUM ACCEPT_TAC ) ;

val linear_order_refl = Q.store_thm ("linear_order_refl",
  `linear_order lo X ==> x IN X ==> (x, x) IN lo`,
  REWRITE_TAC [linear_order_def] THEN REPEAT STRIP_TAC THEN RES_TAC) ;

val linear_order_in_set = Q.store_thm ("linear_order_in_set",
  `linear_order lo X ==> (x, y) IN lo ==> x IN X /\ y IN X`,
  REPEAT DISCH_TAC THEN IMP_RES_TAC linear_order_dom_rg THEN
  VAR_EQ_TAC THEN
  IMP_RES_TAC in_dom_rg THEN ASM_REWRITE_TAC [IN_UNION]) ;

val IN_MIN_LO = Q.store_thm ("IN_MIN_LO",
  `x IN X ==> linear_order lo X ==> y IN minimal_elements X lo ==>
    (y, x) IN lo`,
  Ho_Rewrite.REWRITE_TAC [minimal_elements_def, linear_order_def,
      EXTENSION, IN_GSPEC_IFF] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPECL [`x`, `y`]) THEN
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `x`) THEN
  RES_TAC THEN RES_TAC THEN FULL_SIMP_TAC std_ss []) ;

val extend_linear_order = Q.store_thm ("extend_linear_order",
`!r s x.
  x NOTIN s /\
  linear_order r s
  ==>
  linear_order (r UNION {(y, x) | y | y IN (s UNION {x})}) (s UNION {x})`,
  Ho_Rewrite.REWRITE_TAC [linear_order_def, domain_def, range_def,
      transitive_def, antisym_def, SUBSET_DEF,
      IN_UNION, IN_SING, PAIR_IN_GSPEC_1, PAIR_IN_GSPEC_2, IN_GSPEC_IFF] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN METIS_TAC []) ;

val strict_linear_order_acyclic = Q.store_thm ("strict_linear_order_acyclic",
`!r s. strict_linear_order r s ==> acyclic r`,
SRW_TAC [] [acyclic_def, strict_linear_order_def] THEN
IMP_RES_TAC transitive_tc THEN
FULL_SIMP_TAC (srw_ss()) [strict_linear_order_def, transitive_def]);

val acyclic_union = Q.prove (
  `acyclic (r1 UNION r2) ==> (q, r) IN r2 ==> (r, q) NOTIN r1`,
  REWRITE_TAC [acyclic_def] THEN
  REPEAT STRIP_TAC THEN
  VALIDATE (FIRST_ASSUM (CONTR_TAC o UNDISCH o
    MATCH_MP F_IMP o Q.SPEC `q`)) THEN
  irule tc_rule2 THEN Q.EXISTS_TAC `r` THEN
  CONJ_TAC THEN irule tc_rule1 THEN ASM_REWRITE_TAC [IN_UNION]) ;

Theorem strict_linear_order_union_acyclic:
  !r1 r2 s.
    strict_linear_order r1 s /\
    (domain r2 UNION range r2) SUBSET s
    ==>
    (acyclic (r1 UNION r2) <=> r2 SUBSET r1)
Proof
  SRW_TAC [] [] THEN
  EQ_TAC THEN
  SRW_TAC [] [] THENL
  [ FULL_SIMP_TAC (srw_ss()) [strict_linear_order_def, domain_def,
                             transitive_def, range_def, SUBSET_DEF] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `x` THEN
      RES_TAC THEN RES_TAC THEN
      IMP_RES_TAC acyclic_union THEN
      IMP_RES_TAC acyclic_irreflexive THEN
      CCONTR_TAC THEN FULL_SIMP_TAC std_ss [IN_UNION],
   `r1 UNION r2 = r1`
           by (FULL_SIMP_TAC (srw_ss()) [domain_def, range_def, SUBSET_DEF,
                                         EXTENSION] THEN
               METIS_TAC []) THEN
       SRW_TAC [] [] THEN
       METIS_TAC [strict_linear_order_acyclic]]
QED

val strict_linear_order = Q.store_thm ("strict_linear_order",
`!r s. linear_order r s ==> strict_linear_order (strict r) s`,
  Ho_Rewrite.REWRITE_TAC [linear_order_def, strict_linear_order_def,
    strict_def, domain_def, range_def, SUBSET_DEF, transitive_def,
     antisym_def, IN_GSPEC_IFF, PAIR_IN_GSPEC_IFF] THEN
  REPEAT STRIP_TAC THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  ASM_REWRITE_TAC [] THEN METIS_TAC []) ;

val linear_order = Q.store_thm ("linear_order",
`!r s. strict_linear_order r s ==> linear_order (r UNION {(x, x) | x IN s}) s`,
  Ho_Rewrite.REWRITE_TAC [linear_order_def, strict_linear_order_def,
     domain_def, range_def, SUBSET_DEF, transitive_def, antisym_def,
      IN_UNION, IN_GSPEC_IFF, PAIR_IN_GSPEC_IFF, PAIR_IN_GSPEC_same] THEN
  REPEAT STRIP_TAC THEN
  REPEAT BasicProvers.VAR_EQ_TAC THEN
  ASM_REWRITE_TAC [] THEN METIS_TAC []) ;

val finite_strict_linear_order_has_maximal = Q.store_thm
("finite_strict_linear_order_has_maximal",
`!s r.
  FINITE s /\ strict_linear_order r s /\ s <> {}
  ==>
  ?x. x IN maximal_elements s r`,
METIS_TAC [strict_linear_order_acyclic, finite_acyclic_has_maximal]);

val finite_strict_linear_order_has_minimal = Q.store_thm
("finite_strict_linear_order_has_minimal",
`!s r.
  FINITE s /\ strict_linear_order r s /\ s <> {}
  ==>
  ?x. x IN minimal_elements s r`,
METIS_TAC [strict_linear_order_acyclic, finite_acyclic_has_minimal]);

val finite_linear_order_has_maximal = Q.store_thm
("finite_linear_order_has_maximal",
`!s r.
   FINITE s /\ linear_order r s /\ s <> {} ==> ?x. x IN maximal_elements s r`,
SRW_TAC [] [] THEN
IMP_RES_TAC strict_linear_order THEN
IMP_RES_TAC finite_strict_linear_order_has_maximal THEN
Q.EXISTS_TAC `x` THEN
FULL_SIMP_TAC (srw_ss()) [maximal_elements_def, strict_def] THEN
METIS_TAC []);

val finite_linear_order_has_minimal = Q.store_thm
("finite_linear_order_has_minimal",
`!s r.
   FINITE s /\ linear_order r s /\ s <> {} ==> ?x. x IN minimal_elements s r`,
SRW_TAC [] [] THEN
IMP_RES_TAC strict_linear_order THEN
IMP_RES_TAC finite_strict_linear_order_has_minimal THEN
Q.EXISTS_TAC `x` THEN
FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, strict_def] THEN
METIS_TAC []);

val maximal_linear_order = Q.store_thm ("maximal_linear_order",
`!s r x y.
  y IN s /\ linear_order r s /\ x IN maximal_elements s r ==> (y, x) IN r`,
SRW_TAC [] [linear_order_def, maximal_elements_def] THEN
METIS_TAC []);

val minimal_linear_order = Q.store_thm ("minimal_linear_order",
`!s r x y.
   y IN s /\ linear_order r s /\ x IN minimal_elements s r ==> (x, y) IN r`,
SRW_TAC [] [linear_order_def, minimal_elements_def] THEN
METIS_TAC []);

val minimal_linear_order_unique = Q.store_thm ("minimal_linear_order_unique",
`!r s s' x y.
  linear_order r s /\
  x IN minimal_elements s' r /\
  y IN minimal_elements s' r /\
  s' SUBSET s
  ==>
  (x = y)`,
SRW_TAC [] [minimal_elements_def, linear_order_def, antisym_def,
            SUBSET_DEF] THEN
METIS_TAC []);

val finite_prefix_linear_order_has_unique_minimal = Q.store_thm
("finite_prefix_linear_order_has_unique_minimal",
`!r s s'.
  linear_order r s /\
  finite_prefixes r s /\
  x IN s' /\
  s' SUBSET s
  ==>
  SING (minimal_elements s' r)`,
SRW_TAC [] [SING_DEF] THEN
Cases_on `?y. y IN minimal_elements s' r` THEN1
METIS_TAC [UNIQUE_MEMBER_SING, minimal_linear_order_unique] THEN
METIS_TAC [partial_order_linear_order, finite_prefix_po_has_minimal_path]);

val nat_order_iso_thm = Q.store_thm ("nat_order_iso_thm",
`!(f: num -> 'a option) (s : 'a set).
  (!n m. (f m = f n) /\ f m <> NONE ==> (m = n)) /\
  (!x. x IN s ==> ?m. (f m = SOME x)) /\
  (!m x. (f m = SOME x) ==> x IN s)
  ==>
  linear_order {(x, y) | ?m n. m <= n /\ (f m = SOME x) /\ (f n = SOME y)} s /\
  finite_prefixes {(x, y) | ?m n. m <= n /\ (f m = SOME x) /\ (f n = SOME y)} s`,
SRW_TAC [] [linear_order_def, domain_def, range_def, SUBSET_DEF,
            transitive_def, antisym_def, finite_prefixes_def] THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [LESS_EQ_TRANS, SOME_11, NOT_SOME_NONE],
 METIS_TAC [LESS_EQUAL_ANTISYM, SOME_11, NOT_SOME_NONE],
 METIS_TAC [NOT_LESS_EQUAL, LESS_IMP_LESS_OR_EQ],
 `?n. SOME e = f n` by METIS_TAC [] THEN
     SRW_TAC [] [] THEN
     `{SOME x | ?m n'. m <= n' /\ (f m = SOME x) /\ (f n' = f n)} SUBSET
      IMAGE f (count (SUC n))`
             by (SRW_TAC [] [SUBSET_DEF, count_def,
                             DECIDE ``!x:num y. x < SUC y <=> x <= y``] THEN
                 METIS_TAC [NOT_SOME_NONE]) THEN
     `{x | ?m n'. m <= n' /\ (f m = SOME x) /\ (f n' = f n)} =
      IMAGE THE {SOME x | ?m n'. m <= n' /\ (f m = SOME x) /\ (f n' = f n)}`
             by (SRW_TAC [] [EXTENSION] THEN
                 METIS_TAC [THE_DEF]) THEN
     METIS_TAC [IMAGE_FINITE, SUBSET_FINITE, FINITE_COUNT]]);

val chain_def = Define `
  chain s r =
    !x y. x IN s /\ y IN s ==> (x,y) IN r \/ (y,x) IN r`;

val upper_bounds_def = Define `
  upper_bounds s r = {x | x IN range r /\ !y. y IN s ==> (y,x) IN r}`;

val upper_bounds_lem = Q.store_thm ("upper_bounds_lem",
`!r s x1 x2.
   transitive r /\ x1 IN upper_bounds s r /\ (x1,x2) IN r
   ==>
   x2 IN upper_bounds s r`,
SRW_TAC [] [transitive_def, upper_bounds_def, range_def] THEN
METIS_TAC []);

(* ----------------- Zorn's lemma ---------------- *)
(* Following "A short proof of Zorn's Lemma" by J.D. Weston, Archiv der
* Mathematik, 1957 *)

(* Chains that are built by transfinite repetition of adding an arbitrary
* minimal upper bound  *)
val fchains_def = Define `
  fchains r =
    { k | chain k r /\ k <> {} /\
          !C. chain C r /\ C SUBSET k /\
              (upper_bounds C r DIFF C) INTER k <> {} ==>
              (CHOICE (upper_bounds C r DIFF C) IN
               minimal_elements ((upper_bounds C r DIFF C) INTER k) r) }`;

local

val lemma1 = Q.prove (
`!x s r. chain s r /\ x IN s ==> x IN domain r /\ x IN range r`,
SRW_TAC [] [chain_def, in_domain, in_range] THEN
METIS_TAC []);

val lemma2 = Q.prove (
`!r k1 k2 x x'.
  transitive r /\
  k1 IN fchains r /\
  k2 IN fchains r /\
  x IN k1 /\
  x' IN k2 /\
  x' NOTIN k1
  ==>
  (x,x') IN r`,
SRW_TAC [] [] THEN
`x IN range r /\ x' IN range r`
        by (FULL_SIMP_TAC (srw_ss()) [fchains_def] THEN
            METIS_TAC [lemma1]) THEN
Q.ABBREV_TAC `C = {x | x IN k1 /\ x IN k2 /\ (x,x') IN r}` THEN
`x' IN upper_bounds C r DIFF C`
        by (Q.UNABBREV_TAC `C` THEN
            FULL_SIMP_TAC (srw_ss()) [upper_bounds_def]) THEN
`chain C r /\ C SUBSET k2 /\ C SUBSET k1`
        by (Q.UNABBREV_TAC `C` THEN
            FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, chain_def, fchains_def]) THEN
`CHOICE (upper_bounds C r DIFF C) IN
   minimal_elements ((upper_bounds C r DIFF C) INTER k2) r`
        by (FULL_SIMP_TAC (srw_ss()) [fchains_def] THEN
            METIS_TAC [NOT_IN_EMPTY, IN_DIFF, IN_INTER]) THEN
`CHOICE (upper_bounds C r DIFF C) IN k2 /\
 (CHOICE (upper_bounds C r DIFF C), x') IN r`
        by (FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, chain_def,
                                      fchains_def] THEN
            METIS_TAC []) THEN
`(upper_bounds C r DIFF C) INTER k1 = {}`
        by (SRW_TAC [] [EXTENSION] THEN
            CCONTR_TAC THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
            `CHOICE (upper_bounds C r DIFF C) IN k1`
                    by (FULL_SIMP_TAC (srw_ss()) [minimal_elements_def,
                                                  chain_def, fchains_def] THEN
                        METIS_TAC [NOT_IN_EMPTY, IN_DIFF, IN_INTER]) THEN
            `CHOICE (upper_bounds C r DIFF C) IN C`
                    by (Q.UNABBREV_TAC `C` THEN
                        FULL_SIMP_TAC (srw_ss()) []) THEN
            METIS_TAC [CHOICE_DEF, MEMBER_NOT_EMPTY, IN_DIFF]) THEN
`?x''. x'' IN C /\ (x,x'') IN r`
        by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, upper_bounds_def, fchains_def,
                                      SUBSET_DEF, chain_def] THEN
               METIS_TAC []) THEN
`(x'',x') IN r`
        by (Q.UNABBREV_TAC `C` THEN
            FULL_SIMP_TAC (srw_ss()) []) THEN
METIS_TAC [transitive_def]);

val lemma3 = Q.prove (
`!r k1 k2.
   transitive r /\ antisym r /\ k1 IN fchains r /\ k2 IN fchains r
   ==>
   k1 SUBSET k2 \/ k2 SUBSET k1`,
SRW_TAC [] [antisym_def, SUBSET_DEF] THEN
CCONTR_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(x,x') IN r` by METIS_TAC [lemma2] THEN
METIS_TAC [lemma2]);

val lemma4 = Q.prove (
`!r. antisym r /\ transitive r ==>
    chain (BIGUNION (fchains r)) r /\
    (!x x' k.
      (x',x) IN r /\
      x' IN BIGUNION (fchains r) /\
      x IN BIGUNION (fchains r) /\
      k IN fchains r /\
      x IN k
      ==>
      x' IN k)`,
SRW_TAC [] [chain_def] THENL
[Cases_on `y IN s` THENL
     [FULL_SIMP_TAC (srw_ss()) [fchains_def, chain_def] THEN
          METIS_TAC [],
      METIS_TAC [lemma2]],
 METIS_TAC [lemma2, antisym_def]]);

val lemma5 = Q.prove (
`!r s. range r SUBSET s /\ (range r <> {}) /\ reflexive r s ==>
       { CHOICE (range r) } IN fchains r`,
SRW_TAC [] [fchains_def] THENL
[FULL_SIMP_TAC (srw_ss()) [chain_def, reflexive_def, SUBSET_DEF] THEN
     METIS_TAC [CHOICE_DEF, MEMBER_NOT_EMPTY],
 FULL_SIMP_TAC (srw_ss()) [GSYM DISJOINT_DEF, IN_DISJOINT] THEN
     SRW_TAC [] [minimal_elements_def, upper_bounds_def] THEN
     METIS_TAC [CHOICE_DEF, MEMBER_NOT_EMPTY]]);

val lemma6 = Q.prove (
`!r k x C.
  transitive r /\
  antisym r /\
  k IN fchains r /\
  x IN k /\
  chain C r /\
  x IN upper_bounds C r DIFF C /\
  C SUBSET BIGUNION (fchains r)
  ==>
  CHOICE (upper_bounds C r DIFF C) IN k /\ (CHOICE (upper_bounds C r DIFF C),x) IN r`,
SRW_TAC [] [] THEN
`!x'. x' IN C ==> (x',x) IN r /\ (x' <> x)`
        by FULL_SIMP_TAC (srw_ss()) [upper_bounds_def] THEN
`C SUBSET k`
        by (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
            SRW_TAC [] [] THEN
            RES_TAC THEN
            IMP_RES_TAC lemma4 THEN
            METIS_TAC [IN_BIGUNION]) THEN
FULL_SIMP_TAC (srw_ss()) [fchains_def, minimal_elements_def, chain_def] THEN
`(upper_bounds C r DIFF C) INTER k <> {}`
        by (FULL_SIMP_TAC (srw_ss()) [GSYM DISJOINT_DEF, IN_DISJOINT,
                                      IN_DIFF] THEN
            METIS_TAC []) THEN
METIS_TAC []);

val lemma7 = Q.prove (
`!r s.
   range r SUBSET s /\ (range r <> {}) /\ antisym r /\ reflexive r s /\
   transitive r
   ==>
   BIGUNION (fchains r) IN fchains r`,
SRW_TAC [] [fchains_def] THEN
FULL_SIMP_TAC (srw_ss()) [GSYM fchains_def] THEN1
METIS_TAC [lemma4] THEN1
METIS_TAC [lemma5, NOT_IN_EMPTY] THENL
[`{ CHOICE (range r) } IN fchains r` by METIS_TAC [lemma5] THEN
     CCONTR_TAC THEN
     FULL_SIMP_TAC (srw_ss()) [],
 `?x k. x IN (upper_bounds C r DIFF C) /\ x IN k /\ k IN fchains r`
         by METIS_TAC [GSYM DISJOINT_DEF, IN_DISJOINT, IN_BIGUNION] THEN
     `CHOICE (upper_bounds C r DIFF C) IN k /\
      (CHOICE (upper_bounds C r DIFF C),x) IN r`
         by METIS_TAC [lemma6] THEN
     SRW_TAC [] [minimal_elements_def] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN1
     METIS_TAC [CHOICE_DEF, IN_DIFF] THEN1
     METIS_TAC [CHOICE_DEF, IN_DIFF] THEN1
     METIS_TAC [] THEN
     `(CHOICE (upper_bounds C r DIFF C),x'') IN r`
         by METIS_TAC [lemma6, IN_DIFF] THEN
     METIS_TAC [antisym_def]]);

val lemma8 = Q.prove (
`!r s k.
   range r SUBSET s /\
   (range r <> {}) /\
   reflexive r s /\ antisym r /\ transitive r /\
   k IN fchains r /\
   (upper_bounds k r DIFF k <> {})
   ==>
  (CHOICE (upper_bounds k r DIFF k) INSERT k IN fchains r)`,
SRW_TAC [] [fchains_def] THEN
`CHOICE (upper_bounds k r DIFF k) IN upper_bounds k r DIFF k`
        by METIS_TAC [IN_DIFF, IN_DISJOINT, DISJOINT_DEF, CHOICE_DEF] THENL
[FULL_SIMP_TAC (srw_ss()) [chain_def, upper_bounds_def] THEN
     SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [reflexive_def, SUBSET_DEF],
 `CHOICE (upper_bounds C r DIFF C) IN upper_bounds C r DIFF C`
         by METIS_TAC [IN_DIFF, IN_DISJOINT, DISJOINT_DEF, CHOICE_DEF] THEN
     `C SUBSET k`
             by (FULL_SIMP_TAC (srw_ss()) [IN_DISJOINT, GSYM DISJOINT_DEF,
                                           SUBSET_DEF, upper_bounds_def] THEN
                 SRW_TAC [] [] THEN
                 METIS_TAC [antisym_def]) THEN
     Cases_on `(upper_bounds C r DIFF C) INTER k <> {}` THENL
     [SRW_TAC [] [minimal_elements_def] THEN1
          METIS_TAC [IN_DIFF] THEN1
          METIS_TAC [IN_DIFF] THEN
          FULL_SIMP_TAC (srw_ss()) [minimal_elements_def] THEN
          FULL_SIMP_TAC (srw_ss()) [IN_DISJOINT, GSYM DISJOINT_DEF, SUBSET_DEF,
                                    upper_bounds_def] THEN
          SRW_TAC [] [] THEN
          METIS_TAC [antisym_def],
      Q_TAC SUFF_TAC `(upper_bounds C r DIFF C = upper_bounds k r DIFF k)` THENL
          [FULL_SIMP_TAC (srw_ss()) [minimal_elements_def,
                                     upper_bounds_def] THEN
               SRW_TAC [] [] THEN1
               METIS_TAC [] THEN1
               METIS_TAC [] THEN
               FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
               METIS_TAC [],
           SRW_TAC [] [EXTENSION] THEN
               EQ_TAC THEN
               SRW_TAC [] [] THEN
               FULL_SIMP_TAC (srw_ss()) [transitive_def, reflexive_def,
                                         chain_def, SUBSET_DEF,
                                         upper_bounds_def, range_def] THEN
               METIS_TAC []]]]);

val lemma9 = Q.prove (
`!r s.
   range r SUBSET s /\
   (range r <> {}) /\
   antisym r /\ reflexive r s /\ transitive r
   ==>
   upper_bounds (BIGUNION (fchains r)) r SUBSET maximal_elements s r`,
SRW_TAC [] [] THEN
`BIGUNION (fchains r) IN fchains r` by METIS_TAC [lemma7] THEN
Cases_on `upper_bounds (BIGUNION (fchains r)) r DIFF (BIGUNION (fchains r)) <>
          {}`
THENL [
  `(CHOICE (upper_bounds (BIGUNION (fchains r)) r DIFF
     (BIGUNION (fchains r))) INSERT (BIGUNION (fchains r))
   IN fchains r)`
         by METIS_TAC [lemma8] THEN
  METIS_TAC [MEMBER_NOT_EMPTY, CHOICE_DEF, IN_BIGUNION, IN_DIFF, IN_INSERT],
  SIMP_TAC (srw_ss()) [SUBSET_DEF, maximal_elements_def] THEN
  Q.X_GEN_TAC `u` THEN STRIP_TAC THEN CONJ_TAC THENL [
    ALL_TAC,
    Q.X_GEN_TAC `e` THEN STRIP_TAC
  ] THEN
  `?k. k IN fchains r /\ u IN k`
             by METIS_TAC [IN_DIFF, MEMBER_NOT_EMPTY, IN_BIGUNION]
  THENL [
    FULL_SIMP_TAC (srw_ss()) [fchains_def, chain_def, range_def, SUBSET_DEF] THEN
    METIS_TAC [],
    `e IN upper_bounds (BIGUNION (fchains r)) r` by METIS_TAC [upper_bounds_lem] THEN
    `u IN (BIGUNION (fchains r)) /\ e IN (BIGUNION (fchains r))`
                  by METIS_TAC [IN_BIGUNION, IN_DIFF, MEMBER_NOT_EMPTY] THEN
    FULL_SIMP_TAC (srw_ss()) [upper_bounds_def, antisym_def] THEN
    METIS_TAC []
   ]
]);

in

val zorns_lemma = Q.store_thm ("zorns_lemma",
`!r s. (s <> {}) /\ partial_order r s /\
  (!t. chain t r ==> upper_bounds t r <> {})
  ==>
  (?x. x IN maximal_elements s r)`,
SRW_TAC [] [partial_order_def] THEN
Q.EXISTS_TAC `CHOICE (upper_bounds (BIGUNION (fchains r)) r)` THEN
SRW_TAC [] [] THEN
`range r <> {}`
        by (FULL_SIMP_TAC (srw_ss()) [range_def, reflexive_def,
                                      GSYM MEMBER_NOT_EMPTY] THEN
            METIS_TAC []) THEN
METIS_TAC [SUBSET_DEF, lemma9, MEMBER_NOT_EMPTY, CHOICE_DEF, lemma4]);

end

(* ------------------------------------------------------------------------ *)
(*  Equivalences                                                            *)
(* ------------------------------------------------------------------------ *)

val per_def = Define `
  per xs xss <=>
    (BIGUNION xss) SUBSET xs /\ {} NOTIN xss /\
    !xs1 xs2. xs1 IN xss /\ xs2 IN xss /\ xs1 <> xs2 ==> DISJOINT xs1 xs2`;

val per_restrict_def = Define `
  per_restrict xss xs = {xs' INTER xs | xs' IN xss} DELETE {}`;

val per_delete = Q.store_thm ("per_delete",
`!xs xss e. per xs xss ==>
            per (xs DELETE e)
                {es | es IN (IMAGE (\es. es DELETE e) xss) /\ es <> {}}`,
SRW_TAC [] [per_def, SUBSET_DEF, RES_FORALL_THM] THENL
[FULL_SIMP_TAC (srw_ss()) [IN_DELETE] THEN
     METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [IN_DELETE] THEN
     METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [EXTENSION, DISJOINT_DEF] THEN
     METIS_TAC []]);

val per_restrict_per = Q.store_thm ("per_restrict_per",
`!r s s'. per s r ==> per s' (per_restrict r s')`,
SRW_TAC [] [per_def, per_restrict_def, RES_FORALL_THM, SUBSET_DEF,
            DISJOINT_DEF] THENL
[FULL_SIMP_TAC (srw_ss()) [],
 FULL_SIMP_TAC (srw_ss()) [EXTENSION, SPECIFICATION] THEN
     METIS_TAC []]);

val countable_per = Q.store_thm ("countable_per",
`!xs xss. countable xs /\ per xs xss ==> countable xss`,
SRW_TAC [] [per_def, SUBSET_DEF, DISJOINT_DEF, EXTENSION] THEN
MATCH_MP_TAC (METIS_PROVE [inj_countable]
                  ``countable xs /\ INJ CHOICE xss xs ==> countable xss``) THEN
SRW_TAC [] [INJ_DEF, EXTENSION] THEN
METIS_TAC [CHOICE_DEF]);



(* ------------------------------------------------------------------------ *)
(*  Misc                                                                    *)
(* ------------------------------------------------------------------------ *)

val all_choices_def = Define `
  all_choices xss =
    {IMAGE choice xss | choice | !xs. xs IN xss ==> choice xs IN xs}`;

val all_choices_thm = Q.store_thm ("all_choices_thm",
`!x s y. x IN all_choices s /\ y IN x ==> ?z. z IN s /\ y IN z`,
SRW_TAC [] [all_choices_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [SPECIFICATION]);


val num_order_def = Define `
  num_order (f:'a -> num) s = {(x, y) | x IN s /\ y IN s /\ f x <= f y}`;

val linear_order_num_order = Q.store_thm ("linear_order_num_order",
`!f s t. INJ f s t ==> linear_order (num_order f s) s`,
SRW_TAC [] [linear_order_def, transitive_def, antisym_def, num_order_def,
       domain_def, range_def, SUBSET_DEF, INJ_DEF] THEN1
DECIDE_TAC THEN1
METIS_TAC [EQ_LESS_EQ] THEN1
DECIDE_TAC);

val num_order_finite_prefix = Q.store_thm ("num_order_finite_prefix",
`!f s t. INJ f s t ==> finite_prefixes (num_order f s) s`,
SRW_TAC [] [finite_prefixes_def, num_order_def] THEN
`INJ f {e' | e' IN s /\ f e' <= f e} (count (SUC (f e)))`
        by (FULL_SIMP_TAC (srw_ss()) [count_def, INJ_DEF] THEN
            SRW_TAC [] [] THEN
            DECIDE_TAC) THEN
METIS_TAC [FINITE_INJ, FINITE_COUNT]);

(* ------------------------------------------------------------------------ *)
(*  A big theorem that a partial order with finite prefixes over a countable*)
(*  set can be extended to a linear order with finite prefixes.             *)
(* ------------------------------------------------------------------------ *)

val po2lolem1= Q.prove (
`!(f: num -> 'a option) (s : 'a set).
  (!n m. (f m = f n) /\ ~(f m = NONE) ==> (m = n)) /\
  (!x. x IN s ==> ?m. (f m = SOME x)) /\
  (!m x. (f m = SOME x) ==> x IN s)
  ==>
  linear_order {(x, y) | ?m n. m <= n /\ (f m = SOME x) /\ (f n = SOME y)} s /\
  finite_prefixes {(x, y) | ?m n. m <= n /\ (f m = SOME x) /\ (f n = SOME y)} s`,
SRW_TAC [] [] THEN
IMP_RES_TAC nat_order_iso_thm THEN
SRW_TAC [] [finite_prefixes_def]);

val get_min_def = Define `
  get_min r' (s, r) =
    let mins = minimal_elements (minimal_elements s r) r' in
      if SING mins then
        SOME (CHOICE mins)
      else
        NONE`;

Definition nth_min_def:
  (nth_min r' (s, r) 0 = get_min r' (s, r)) /\
  (nth_min r' (s, r) (SUC n) =
    let min = get_min r' (s, r) in
      if min = NONE then
        NONE
      else
        nth_min r' (s DELETE (THE min), r) n)
End


Triviality nth_min_surj_lem1:
  !r' s' x s r.
    linear_order r' s /\
    finite_prefixes r' s /\
    partial_order r s /\
    x IN minimal_elements s' r /\
    s' SUBSET s
   ==>
    ?m. nth_min r' (s', r) m = SOME x
Proof
rpt gen_tac THEN
Induct_on `CARD {x' | x' IN s' /\ (x', x) IN r'}` THEN
SRW_TAC [] [] THEN
`FINITE {x' | x' IN s' /\ (x', x) IN r'}`
        by (FULL_SIMP_TAC (srw_ss()) [finite_prefixes_def, minimal_elements_def,
                                      SUBSET_DEF, GSPEC_AND] THEN
            METIS_TAC [INTER_COMM, INTER_FINITE])
THENL [
  Q.EXISTS_TAC `0` THEN
  SRW_TAC [] [nth_min_def, get_min_def] THEN
  `{x' | x' IN s' /\ (x', x) IN r'} = {}` by METIS_TAC [CARD_EQ_0] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `mins = {x}` suffices_by SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [minimal_elements_def] THEN
  Q.UNABBREV_TAC `mins` THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION, linear_order_def, SUBSET_DEF] THEN
  METIS_TAC [],

  first_x_assum (Q.SPECL_THEN [‘s' DELETE THE (get_min r' (s',r))’, ‘x’, ‘r'’]
                             strip_assume_tac) >>
  `SING (minimal_elements (minimal_elements s' r) r')`
    by (MATCH_MP_TAC finite_prefix_linear_order_has_unique_minimal THEN
        Q.EXISTS_TAC `s` THEN
        SRW_TAC [] [SUBSET_DEF, minimal_elements_def] THEN
        FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]) THEN
  FULL_SIMP_TAC (srw_ss()) [get_min_def, LET_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [SING_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.RENAME_TAC [‘minimal_elements (minimal_elements _ _) _ = {X}’] >>
  Cases_on `x = X` THENL [
    Q.EXISTS_TAC `0` THEN
    SRW_TAC [] [nth_min_def, get_min_def, LET_THM],
    `x IN s' /\ X IN s'`
      by (FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, EXTENSION] THEN
          METIS_TAC []) THEN
    `v = CARD ({x' | x' IN s' /\ (x',x) IN r'} DELETE X)`
      by (SRW_TAC [] [] THEN1 DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, EXTENSION,
                                    linear_order_def,
                                    SUBSET_DEF] THEN
          METIS_TAC []) THEN
    `{x' | x' IN s' /\ (x',x) IN r'} DELETE X =
     {x'' | (x'' IN s' /\ x'' <> X) /\ (x'',x) IN r'}`
      by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, linear_order_def,
                                    domain_def, SUBSET_DEF] THEN
          METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `?m. nth_min r' (s' DELETE X, r) m = SOME x`
      by (Q.PAT_ASSUM `P ==> ?m. Q m` MATCH_MP_TAC THEN
          FULL_SIMP_TAC (srw_ss()) [minimal_elements_def,
                                    rrestrict_def,
                                    SUBSET_DEF]) THEN
    Q.EXISTS_TAC `SUC m` THEN
    SRW_TAC [] [nth_min_def] THEN
    Q.UNABBREV_TAC `min` THEN
    SRW_TAC [] [] THEN
    Cases_on `get_min r' (s', r)` THEN
    FULL_SIMP_TAC (srw_ss()) [get_min_def, LET_THM, SING_DEF] THEN
    METIS_TAC [NOT_SOME_NONE, CHOICE_SING, SOME_11]
  ]
]
QED

Triviality nth_min_surj_lem2:
  !r' s r m m' x x'.
    nth_min r' (s, r) m = SOME x /\
    nth_min r' (s DIFF {x | ?n. n <= m /\ (nth_min r' (s,r) n = SOME x)}, r) m'
    =
    SOME x'
    ==>
    (nth_min r' (s, r) (SUC (m + m')) = SOME x')
Proof
  Induct_on `m` THEN
  SRW_TAC [] [nth_min_def, LET_THM] THEN
  SRW_TAC [] [DELETE_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
  REV_FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.RENAME_TAC [‘get_min R (s,r) <> NONE’,
                ‘nth_min R (s DELETE _, _) m1 = SOME x1’,
                ‘nth_min R _ (SUC m1 + m2) = SOME x2’] >>
  Cases_on `get_min R (s, r)` THEN
  FULL_SIMP_TAC (srw_ss()) [DELETE_DEF] THEN
  SRW_TAC [] [arithmeticTheory.ADD] THEN
  first_assum irule THEN
  SRW_TAC [] [] THEN
  Q.RENAME_TAC [‘get_min R _ = SOME x0’, ‘s DIFF {x0} DIFF _’] >>
  ‘s DIFF {x0} DIFF
   {x | ?n. n <= m1 /\ (nth_min R (s DIFF {x0}, r) n = SOME x)} =
   s DIFF {x | ?n.  n <= SUC m1 /\ (nth_min R (s,r) n = SOME x)}’
    by (SRW_TAC [] [EXTENSION] THEN EQ_TAC THEN SRW_TAC [] [] THENL [
           Cases_on `n` THEN SRW_TAC [] [nth_min_def, LET_THM]
           >- REV_FULL_SIMP_TAC (srw_ss()) [nth_min_def] >>
           Q.RENAME_TAC [‘SUC m1 <= N’] >>
           first_x_assum (Q.SPEC_THEN ‘N’ mp_tac) >>
           SRW_TAC [] [] >>
           Q.PAT_X_ASSUM ‘nth_min _ _ (SUC _) = SOME _’ mp_tac >>
           ASM_SIMP_TAC (srw_ss()) [LET_THM, nth_min_def] >> strip_tac >>
           FULL_SIMP_TAC (srw_ss()) [DELETE_DEF] >> DECIDE_TAC,
           DISCH_THEN SUBST_ALL_TAC >> POP_ASSUM (Q.SPEC_THEN ‘0’ MP_TAC) THEN
           SRW_TAC [] [nth_min_def],
           Q.RENAME_TAC [‘~(N <= m1)’, ‘nth_min _ _ N = SOME _’] >>
           first_x_assum (Q.SPEC_THEN ‘SUC N’ MP_TAC) >>
           ASM_SIMP_TAC (srw_ss()) [nth_min_def, LET_THM, DELETE_DEF] >>
           DECIDE_TAC
         ]) THEN
  SRW_TAC [] []
QED

val nth_min_surj_lem3 = Q.prove (
`!r' s r s' x.
  linear_order r' s /\
  finite_prefixes r' s /\
  partial_order r s /\
  finite_prefixes r s /\
  s' SUBSET s /\
  x IN s'
  ==>
  ?m. nth_min r' (s', r) m = SOME x`,
NTAC 5 STRIP_TAC THEN
completeInduct_on `CARD {x' | x' IN s' /\ (x', x) IN r}` THEN
SRW_TAC [] [] THEN
Cases_on `x IN minimal_elements s' r` THEN1
METIS_TAC [nth_min_surj_lem1] THEN
`?x'. x' IN minimal_elements s' r /\ (x', x) IN r`
        by METIS_TAC [finite_prefix_po_has_minimal_path] THEN
`?m. nth_min r' (s', r) m = SOME x'` by METIS_TAC [nth_min_surj_lem1] THEN
Q.ABBREV_TAC `s'' = {x | ?n. n <= m /\ (nth_min r' (s', r) n = SOME x)}` THEN
`{x''' | (x''' IN s' /\ x''' NOTIN s'') /\ (x''',x) IN r} PSUBSET
 {x' | x' IN s' /\ (x',x) IN r}`
        by (SRW_TAC [] [PSUBSET_DEF, SUBSET_DEF, EXTENSION] THEN
            Q.EXISTS_TAC `x'` THEN
            SRW_TAC [] [] THEN
            Q.UNABBREV_TAC `s''` THEN
            FULL_SIMP_TAC (srw_ss()) [minimal_elements_def] THEN
            METIS_TAC [LESS_EQ_REFL]) THEN
`FINITE {x' | x' IN s' /\ (x',x) IN r}`
        by (FULL_SIMP_TAC (srw_ss()) [finite_prefixes_def, SUBSET_DEF,
                                      minimal_elements_def, GSPEC_AND] THEN
               METIS_TAC [INTER_FINITE, INTER_COMM]) THEN
Cases_on `x IN s' DIFF s''` THENL
[FULL_SIMP_TAC (srw_ss()) [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] THEN
     `?m. nth_min r' (s' DIFF s'', r) m = SOME x`
             by (Q.PAT_ASSUM `!s''' x'' r''. P s''' x'' r''` MATCH_MP_TAC THEN
                 FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
                 METIS_TAC [CARD_PSUBSET]) THEN
     Q.EXISTS_TAC `SUC (m + m')` THEN
     METIS_TAC [nth_min_surj_lem2],
 FULL_SIMP_TAC (srw_ss()) [] THEN1
     METIS_TAC [] THEN
     Q.UNABBREV_TAC `s''` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC []]);

val get_min_lem1 = Q.prove (
`!r' s r x. (get_min r' (s, r) = SOME x) ==> x IN s`,
SRW_TAC [] [get_min_def, LET_THM, SING_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, minimal_elements_def] THEN
METIS_TAC []);

val nth_min_lem1 = Q.prove (
`!r' s r m x. (nth_min r' (s, r) m = SOME x) ==> x IN s`,
Induct_on `m` THEN
SRW_TAC [] [nth_min_def, LET_DEF] THEN1
METIS_TAC [get_min_lem1] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []);

val nth_min_lem2 = Q.prove (
`!r' s r n m.
  nth_min r' (s, r) m <> NONE
  ==>
  nth_min r' (s, r) m <> nth_min r' (s, r) (SUC (m + n))`,
Induct_on `m` THEN
SRW_TAC [] [nth_min_def, LET_THM] THEN
Cases_on `get_min r' (s, r)` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL
[CCONTR_TAC THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     `x IN s DELETE x` by METIS_TAC [nth_min_lem1] THEN
     FULL_SIMP_TAC (srw_ss()) [],
 `SUC m + n = SUC (m + n)` by DECIDE_TAC THEN
     METIS_TAC [NOT_IS_SOME_EQ_NONE]]);

val nth_min_inj_lem = Q.prove (
`!r' s r.
  (nth_min r' (s, r) m = nth_min r' (s, r) n) /\ nth_min r' (s, r) m <> NONE
  ==>
  (m = n)`,
STRIP_ASSUME_TAC (DECIDE ``m:num < n \/ n < m \/ (m = n)``) THEN
SRW_TAC [] [] THENL
[`SUC (m + (n - m - 1)) = n` by DECIDE_TAC THEN
     METIS_TAC [nth_min_lem2],
 Cases_on `nth_min r' (s, r) n = NONE` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     `SUC (n + (m - n - 1)) = m` by DECIDE_TAC THEN
     METIS_TAC [nth_min_lem2]]);

val nth_min_subset_lem1 = Q.prove (
`!m n x y s r r'.
  m < n /\ x <> y /\
  (nth_min r' (s, r) n = SOME x) /\ (nth_min r' (s, r) m = SOME y)
  ==>
  (x, y) NOTIN r`,
Induct THEN
SRW_TAC [] [nth_min_def] THENL
[IMP_RES_TAC get_min_lem1 THEN
     IMP_RES_TAC nth_min_lem1 THEN
     FULL_SIMP_TAC (srw_ss()) [get_min_def, LET_THM] THEN
     Cases_on `SING (minimal_elements (minimal_elements s r) r')` THEN
     FULL_SIMP_TAC (srw_ss()) [SING_DEF] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, EXTENSION] THEN
     METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
     Cases_on `get_min r' (s, r)` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     Cases_on `n` THEN
     FULL_SIMP_TAC (srw_ss()) [nth_min_def, LET_THM] THEN
     RES_TAC THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     FULL_SIMP_TAC (srw_ss()) [Q.prove (`(x, y) IN {(x, y) | P x y} <=> P x y`,
                                        SRW_TAC [] [])] THEN
     IMP_RES_TAC nth_min_lem1 THEN
     FULL_SIMP_TAC (srw_ss()) []]);

val nth_min_subset_lem2 = Q.prove (
`!r' r s.
  linear_order {(x, y) | ?m n. m <= n /\ (nth_min r' (s, r) m = SOME x) /\
                               (nth_min r' (s, r) n = SOME y)} s /\
  domain r SUBSET s /\
  range r SUBSET s
  ==>
  r SUBSET {(x, y) | ?m n. m <= n /\ (nth_min r' (s, r) m = SOME x) /\
                           (nth_min r' (s, r) n = SOME y)}`,
SRW_TAC [] [SUBSET_DEF] THEN
Cases_on `x` THEN
SRW_TAC [] [] THEN
`?m n. m <= n /\ (((nth_min r' (s, r) m = SOME q) /\
                   (nth_min r' (s, r) n = SOME r'')) \/
                  ((nth_min r' (s, r) n = SOME q) /\
                   (nth_min r' (s, r) m = SOME r'')))`
        by (FULL_SIMP_TAC (srw_ss()) [linear_order_def, domain_def,
                                      range_def] THEN
            METIS_TAC []) THEN1
METIS_TAC [] THEN
Cases_on `m = n` THEN1
METIS_TAC [] THEN
`m < n` by DECIDE_TAC THEN
`~(q = r'')`
        by (CCONTR_TAC THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
            METIS_TAC [nth_min_inj_lem, NOT_SOME_NONE]) THEN
METIS_TAC [nth_min_subset_lem1]);

val linear_order_of_countable_po = Q.store_thm ("linear_order_of_countable_po",
`!r s.
  countable s /\ partial_order r s /\ finite_prefixes r s
  ==>
  ?r'. linear_order r' s /\ finite_prefixes r' s /\ r SUBSET r'`,
SRW_TAC [] [countable_def] THEN
Q.ABBREV_TAC `f' = nth_min (num_order f s) (s, r)` THEN
`!n m. (f' m = f' n) /\ f' m <> NONE ==> (m = n)`
        by METIS_TAC [nth_min_inj_lem] THEN
`!x. x IN s ==> ?m. f' m = SOME x`
        by METIS_TAC [nth_min_surj_lem3, linear_order_num_order, SUBSET_REFL,
                      num_order_finite_prefix] THEN
`!m x. (f' m = SOME x) ==> x IN s` by METIS_TAC [nth_min_lem1] THEN
Q.EXISTS_TAC `{(x,y) | ?m n. m <= n /\ (f' m = SOME x) /\ (f' n = SOME y)}` THEN
IMP_RES_TAC po2lolem1 THEN
SRW_TAC [] [] THEN
METIS_TAC [partial_order_def, nth_min_subset_lem2]);

val _ = export_theory ();
