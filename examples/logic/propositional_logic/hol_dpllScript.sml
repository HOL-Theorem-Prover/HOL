open HolKernel boolLib Parse bossLib

open finite_mapTheory
open boolSimps

val _ = new_theory "hol_dpll"

val _ = set_fixity "satisfies_clause" (Infixl 500)
Definition satisfies_clause_def:
  sigma satisfies_clause (c:('a # bool) list) =
    EXISTS (\ (a,v). FLOOKUP sigma a = SOME v) c
End

Theorem satisfies_clause_thm:
  (s satisfies_clause [] <=> F) /\
  (s satisfies_clause (h :: t) <=>
   FLOOKUP s (FST h) = SOME (SND h) \/
   s satisfies_clause t)
Proof
  SRW_TAC [][satisfies_clause_def] THEN Cases_on `h` THEN
  SRW_TAC [][]
QED

val _ = set_fixity "satisfies" (Infixl 500)
Definition satisfies_def:
  sigma satisfies (cset : ('a # bool) list list) =
    EVERY (\c. sigma satisfies_clause c) cset
End

Theorem satisfies_thm:
  (s satisfies [] = T) /\
  (s satisfies (c::cs) ⇔ s satisfies_clause c /\ s satisfies cs)
Proof
  SRW_TAC [][satisfies_def]
QED

Definition binds_def:
  binds a p = (a = FST p)
End

Definition rewrite_def:
  (rewrite a v [] = []) /\
  (rewrite a v (c::cs) = if MEM (a,v) c then
                             rewrite a v cs
                         else
                             FILTER ($~ o binds a) c :: rewrite a v cs)
End

Definition catom_def:
  (catom a [] <=> F) /\
  (catom a (h :: t) <=> (a = FST h) \/ catom a t)
End

Definition atom_appears_def:
  atom_appears a cset = EXISTS (catom a) cset
End

val LENGTH_FILTER_1 = prove(
  ``LENGTH (FILTER P l) <= LENGTH l``,
  Induct_on `l` THEN SRW_TAC [][] THEN DECIDE_TAC);

Theorem rewrite_noincrease:
  list_size LENGTH (rewrite a v cset) <= list_size LENGTH cset
Proof
  Induct_on `cset` THEN
  SRW_TAC [][rewrite_def, listTheory.list_size_def] THENL [
    DECIDE_TAC,
    Q_TAC SUFF_TAC `LENGTH (FILTER ($~ o binds a) h) <= LENGTH h`
          THEN1 DECIDE_TAC THEN
    SRW_TAC [][LENGTH_FILTER_1]
  ]
QED

val lemma = prove(
  ``catom a h ==> LENGTH (FILTER ($~ o binds a) h) < LENGTH h``,
  Induct_on `h` THEN
  SRW_TAC [][catom_def, binds_def, DECIDE “x < SUC y ⇔ x <= y”,
             LENGTH_FILTER_1] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

Theorem rewrite_reduces_size:
  atom_appears a cset ==>
  list_size LENGTH (rewrite a v cset) < list_size LENGTH cset
Proof
  Induct_on `cset` THEN SRW_TAC [][atom_appears_def] THENL [
    SRW_TAC [][listTheory.list_size_def, rewrite_def] THENL [
      ASSUME_TAC rewrite_noincrease THEN DECIDE_TAC,
      ASSUME_TAC rewrite_noincrease THEN
      Q_TAC SUFF_TAC `LENGTH (FILTER ($~ o binds a) h) < LENGTH h`
            THEN1 DECIDE_TAC THEN
      SRW_TAC [][lemma]
    ],

    SRW_TAC [][listTheory.list_size_def, rewrite_def] THENL [
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [atom_appears_def],
      Q_TAC SUFF_TAC `LENGTH (FILTER ($~ o binds a) h) <= LENGTH h`
            THEN1 FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [atom_appears_def] THEN
      SRW_TAC [][LENGTH_FILTER_1]
    ]
  ]
QED

Definition find_uprop_def:
  (find_uprop [] = NONE) /\
  (find_uprop (c::cs) = if LENGTH c = 1 then SOME (HD c)
                        else find_uprop cs)
End

Theorem find_uprop_works:
  find_uprop cset = SOME (v',b) ==> atom_appears v' cset
Proof
  Induct_on `cset` THEN SRW_TAC [][find_uprop_def] THENL [
    SRW_TAC [][atom_appears_def] THEN Cases_on `h` THEN
    FULL_SIMP_TAC (srw_ss()) [catom_def],
    FULL_SIMP_TAC (srw_ss()) [atom_appears_def]
  ]
QED

Definition choose_def:
  choose cset = FST (HD (HD cset))
End

Theorem choose_works:
  cset ≠ [] /\ ~MEM [] cset ==> atom_appears (choose cset) cset
Proof
  Cases_on `cset` THEN SRW_TAC [][] THEN
  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [choose_def] THEN
  SRW_TAC [][atom_appears_def, catom_def]
QED

Definition dpll_def:
  dpll cset =
    if cset = [] then SOME FEMPTY
    else if MEM [] cset then NONE
    else
      case find_uprop cset of
        NONE => (let splitv = choose cset
                 in
                   case dpll (rewrite splitv T cset) of
                     NONE => (case dpll (rewrite splitv F cset) of
                                NONE => NONE
                              | SOME fm => SOME (fm |+ (splitv,F)))
                   | SOME fm => SOME (fm |+ (splitv,T)))
      | SOME (v,b) =>
          case dpll (rewrite v b cset) of
            NONE => NONE
          | SOME fm => SOME (fm |+ (v,b))
Termination
  WF_REL_TAC `measure (\cset. list_size LENGTH cset)` THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][rewrite_reduces_size, choose_works],
    SRW_TAC [][rewrite_reduces_size, choose_works],
    METIS_TAC [find_uprop_works, rewrite_reduces_size]
  ]
End

Theorem induct[local] =
    (SIMP_RULE (srw_ss()) [prim_recTheory.WF_measure,
                           prim_recTheory.measure_thm] o
     Q.ISPEC `measure (\cset. list_size LENGTH cset)`)
             relationTheory.WF_INDUCTION_THM

val exrwt_lemma = prove(
  ``!c v b fm. fm satisfies_clause FILTER ($~ o binds v) c ==>
               fm |+ (v,b) satisfies_clause c``,
  Induct THEN1 SRW_TAC [][satisfies_clause_thm] THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
               [pairTheory.FORALL_PROD, satisfies_clause_thm,
                binds_def, finite_mapTheory.FLOOKUP_DEF,
                finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF,
             finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][]);

Theorem extend_rewrite:
  !fm v b.
    fm satisfies rewrite v b cset ==> (fm |+ (v,b)) satisfies cset
Proof
  Induct_on `cset` THEN SRW_TAC [][satisfies_thm, rewrite_def] THENL [
    Induct_on `h` THEN1 SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                 [pairTheory.FORALL_PROD, satisfies_clause_thm] THEN
    SRW_TAC [][finite_mapTheory.FLOOKUP_DEF],
    SRW_TAC [][exrwt_lemma]
  ]
QED

Theorem dpll_satisfies:
  !cset fm. (dpll cset = SOME fm) ==> fm satisfies cset
Proof
  HO_MATCH_MP_TAC dpll_ind THEN SRW_TAC [][] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [dpll_def] THEN
  SRW_TAC [][] THEN1 SRW_TAC [][satisfies_def] THEN
  Cases_on `find_uprop cset` THENL [
    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    Cases_on `dpll (rewrite (choose cset) T cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THENL [
      Cases_on `dpll (rewrite (choose cset) F cset)` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN SRW_TAC [][extend_rewrite],
      SRW_TAC [][extend_rewrite]
    ],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite q r cset)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][extend_rewrite]
  ]
QED

val empty_clause_unsatisfiable = prove(
  ``!cset. MEM [] cset ==> !fm. ~(fm satisfies cset)``,
  Induct THEN SRW_TAC [][satisfies_thm] THEN
  SRW_TAC [][satisfies_clause_thm]);

val option_cond = prove(
  ``((if p then SOME x else NONE) = SOME y) ⇔ p /\ (x = y)``,
  SRW_TAC [][]);

val fm_gives_value = prove(
  ``!cset fm v.
       fm satisfies cset /\ v IN FDOM fm ==>
       fm satisfies (rewrite v (fm ' v) cset)``,
  Induct THEN SRW_TAC [][satisfies_thm, rewrite_def] THEN
  Induct_on `h` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
               [pairTheory.FORALL_PROD, binds_def, option_cond,
                satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  METIS_TAC []);

val cpos_fm_gives_value = prove(
  ``v IN FDOM fm /\ ~(fm satisfies (rewrite v (fm ' v) cset)) ==>
    ~(fm satisfies cset)``,
  METIS_TAC [fm_gives_value]);

Theorem novbind_lemma[local]:
  ~MEM (v,T) h /\ ~MEM (v,F) h ==> (FILTER ($~ o binds v) h = h)
Proof
  Induct_on `h` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
               [pairTheory.FORALL_PROD, binds_def, AllCaseEqs()]
QED

val partial_clause_1 = prove(
  ``!h. fm satisfies_clause h /\
        ~(fm satisfies_clause FILTER ($~ o binds v) h) ==>
        ?b. MEM (v,b) h``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, binds_def] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  METIS_TAC []);

val partial_clause_sat = prove(
  ``!h v b fm.
       fm satisfies_clause h /\
       ~(fm satisfies_clause FILTER ($~ o binds v) h) /\
       MEM (v,b) h /\ ~MEM (v,~b) h ==>
       v IN FDOM fm /\ (fm ' v = b)``,
  Induct_on `h` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss())
               [pairTheory.FORALL_PROD, binds_def, satisfies_clause_thm,
                finite_mapTheory.FLOOKUP_DEF] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  TRY (METIS_TAC []) THEN
  IMP_RES_TAC partial_clause_1 THEN
  `b = b'` by (Cases_on `b` THEN SRW_TAC [][] THEN
               Cases_on `b'` THEN SRW_TAC [][] THEN
               FULL_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][] THEN METIS_TAC []);

val not_sat_case_split = prove(
  ``!cset fm. ~(fm satisfies (rewrite v T cset)) /\
              ~(fm satisfies (rewrite v F cset)) ==>
              ~(fm satisfies cset)``,
  Induct THEN SRW_TAC [][rewrite_def, satisfies_thm] THEN
  TRY (METIS_TAC [novbind_lemma]) THEN
  Cases_on `fm satisfies_clause h` THEN SRW_TAC [][] THENL [
    `v IN FDOM fm /\ (fm ' v = T)`
       by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][],
    `v IN FDOM fm /\ (fm ' v = F)`
       by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][]
  ]);

val case_split_unsat = prove(
  ``!cset. (!fm. ~(fm satisfies rewrite v F cset)) /\
           (!fm. ~(fm satisfies rewrite v T cset)) ==>
           !fm. ~(fm satisfies cset)``,
  Induct THEN SRW_TAC [][rewrite_def, satisfies_thm] THEN
  Cases_on `fm satisfies_clause h` THEN SRW_TAC [][] THENL [
    Cases_on `fm satisfies_clause FILTER ($~ o binds v) h` THENL [
      `~(fm satisfies rewrite v T cset)` by METIS_TAC [] THEN
      MATCH_MP_TAC not_sat_case_split THEN SRW_TAC [][],
      `v IN FDOM fm /\ (fm ' v = F)`
         by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
             METIS_TAC []) THEN
      MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][]
    ],
    Cases_on `fm satisfies_clause FILTER ($~ o binds v) h` THENL [
      `~(fm satisfies rewrite v F cset)` by METIS_TAC [] THEN
      MATCH_MP_TAC not_sat_case_split THEN SRW_TAC [][],
      `v IN FDOM fm /\ (fm ' v = T)`
         by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
             METIS_TAC []) THEN
      MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][]
    ],
    `FILTER ($~ o binds v) h = h` by METIS_TAC [novbind_lemma] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [not_sat_case_split]
  ]);

val find_uprop_forces = prove(
  ``!cset. (find_uprop cset = SOME (q, r)) ==>
           !fm. ~(fm satisfies rewrite q (~r) cset)``,
  Induct THEN SRW_TAC [][find_uprop_def, satisfies_thm, rewrite_def] THENL [
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      METIS_TAC [],
      gvs[]
    ],
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][binds_def] THEN
    simp[satisfies_clause_thm]
  ]);

Theorem dpll_unsatisfied:
  !cset. (dpll cset = NONE) ==> !fm. ~(fm satisfies cset)
Proof
  HO_MATCH_MP_TAC dpll_ind THEN GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [dpll_def] THEN
  SRW_TAC [][empty_clause_unsatisfiable] THEN
  Cases_on `find_uprop cset` THENL [
    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    Cases_on `dpll (rewrite (choose cset) T cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite (choose cset) F cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [case_split_unsat],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite q r cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC find_uprop_forces THEN
    Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [case_split_unsat]
  ]
QED

val _ = EVAL ``dpll [[(1,T); (2,F); (3,T)]; [(1,F); (2,T)]]``

(* using the DPLL algorithm on HOL's boolean formula's via "reflection" *)
(* it seems necessary to push the variable type through a substitution,  mapping
   into a type that will allow the "variables" of the original formula to be
   compared with each other without worrying about their semantic content *)
Definition interpret_clause_def[simp]:
  (interpret_clause f [] = F) /\
  (interpret_clause f ((h : 'a # bool) :: t) ⇔
     (f (FST h) = SND h) \/ interpret_clause f t)
End

Definition interpret_def[simp]:
  (interpret f [] = T) /\
  (interpret f (c::cs) ⇔ interpret_clause f c /\ interpret f cs)
End

val empty_clause_interpret = store_thm(
  "empty_clause_interpret",
  ``!cs. MEM [] cs ==> ~interpret f cs``,
  Induct THEN SRW_TAC [][] THEN SRW_TAC [][]);

val iclause_rewrite = store_thm(
  "iclause_rewrite",
  ``!c v. ~MEM (v,f v) c /\ interpret_clause f c ==>
          interpret_clause f (FILTER ($~ o binds v) c)``,
  Induct THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [pairTheory.FORALL_PROD, binds_def] THEN
  SRW_TAC [][] THEN METIS_TAC []);

val interpret_rewrite = store_thm(
  "interpret_rewrite",
  ``!cs v b. (f v = b) /\ interpret f cs ==>
             interpret f (rewrite v b cs)``,
  Induct THEN SRW_TAC [][rewrite_def] THEN METIS_TAC [iclause_rewrite]);

val interpret_uprop = store_thm(
  "interpret_uprop",
  ``(find_uprop cs = SOME (q,r)) ==> ~interpret f (rewrite q (~r) cs)``,
  Induct_on `cs` THEN SRW_TAC [][find_uprop_def, rewrite_def] THENL [
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [],
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
    ],
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [binds_def] THEN
    Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [binds_def]
  ]);

(* might equally be able to get conclusion from !fm. ~(fm satisfies cs) *)
val dpll_interpret = store_thm(
  "dpll_interpret",
  ``!cs f. (dpll cs = NONE) ==> (interpret f cs = F)``,
  HO_MATCH_MP_TAC dpll_ind THEN GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [dpll_def] THEN SRW_TAC [][empty_clause_interpret] THEN
  Cases_on `find_uprop cs` THENL [
    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    Cases_on `dpll (rewrite (choose cs) T cs)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite (choose cs) F cs)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [interpret_rewrite],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite q r cs)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `~interpret f (rewrite q (~r) cs)` by METIS_TAC [interpret_uprop] THEN
    Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [interpret_rewrite]
  ]);

val t0 = `` (((~a \/ p /\ ~q \/ ~p /\ q) /\
                    (~(p /\ ~q \/ ~p /\ q) \/ a)) /\
                   (~c \/ p /\ q) /\ (~(p /\ q) \/ c)) /\
                 ~(~(p /\ q) \/ c /\ ~a)``
val t = rhs (concl
                 (SIMP_CONV bool_ss [LEFT_OR_OVER_AND, RIGHT_OR_OVER_AND,
                                     GSYM CONJ_ASSOC, GSYM DISJ_ASSOC,
                                     DE_MORGAN_THM] t0))

(* t must not only be in CNF, but with boolean operators right associated *)
fun prove_cnf_unsat t = let
  val cs = strip_conj t
  val vars = free_vars t
  val f = ``\n. EL n ^(listSyntax.mk_list(vars, bool))``
  fun var2n v = numSyntax.mk_numeral (Arbnum.fromInt (index (aconv v) vars))
  fun mk_clause c = let
    val ds = strip_disj c
    fun mkatom t = if is_neg t then ``(^(var2n (dest_neg t)), F)``
                   else ``(^(var2n t), T)``
  in
    listSyntax.mk_list(map mkatom ds, ``:num # bool``)
  end
  val clauses = listSyntax.mk_list (map mk_clause cs, ``:(num # bool) list``)
  val th1 = SIMP_CONV (srw_ss()) [] ``interpret ^f ^clauses``
  val _ = aconv t (rhs (concl th1)) orelse raise Fail "translation failed"
  val th2 = EVAL ``dpll ^clauses``
in
  if is_const (rhs (concl th2)) then
    TRANS (SYM th1) (ISPEC f (MATCH_MP dpll_interpret th2))
  else raise Fail "formula is propositionally satisfiable"
end

(* 0.018s seconds [Poly/ML, 22 Jan 2024, Apple M1 Macbook Pro] *)
Theorem example = time prove_cnf_unsat t

val _ = export_theory();
