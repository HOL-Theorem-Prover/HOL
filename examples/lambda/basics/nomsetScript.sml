(* ========================================================================== *)
(* FILE    : nomsetScript.sml                                                 *)
(* TITLE   : Nominal sets and the permutation operations on them              *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open BasicProvers boolSimps pairTheory pred_setTheory listTheory rich_listTheory
     finite_mapTheory hurdUtils stringTheory;

open basic_swapTheory NEWLib;

val _ = new_theory "nomset";

(* permutations are represented as lists of pairs of strings.  These
   can be lifted to bijections on strings that only move finitely many
   strings with the perm_of function *)

val _ = overload_on ("perm_of", ``raw_lswapstr``);
val _ = overload_on ("raw_lswapstr", ``raw_lswapstr``);

val perm_of_decompose = raw_lswapstr_APPEND
val perm_of_swapstr = store_thm(
  "perm_of_swapstr",
  ``perm_of p (swapstr x y s) =
    swapstr (perm_of p x) (perm_of p y) (perm_of p s)``,
  Induct_on `p` THEN SRW_TAC [][]);

val permeq_def = Define`
  permeq l1 l2 = (perm_of l1 = perm_of l2)
`;
val _ = set_fixity "==" (Infix(NONASSOC, 450));
val _ = overload_on ("==", ``permeq``)

val permeq_permeq_cong = store_thm(
  "permeq_permeq_cong",
  ``((==) p1 = (==) p1') ==> ((==) p2 = (==) p2') ==>
    ((p1 == p2) = (p1' == p2'))``,
  SRW_TAC [][permeq_def, FUN_EQ_THM] THEN METIS_TAC []);

Theorem permeq_refl[simp] :
    x == x
Proof
  SRW_TAC [][permeq_def]
QED

val permeq_sym = store_thm(
  "permeq_sym",
  ``(x == y) ==> (y == x)``,
  SRW_TAC [][permeq_def]);

val permeq_trans = store_thm(
  "permeq_trans",
  ``(x == y) /\ (y == z) ==> (x == z)``,
  SRW_TAC [][permeq_def]);

val app_permeq_monotone = store_thm(
  "app_permeq_monotone",
  ``!p1 p1' p2 p2'.
       (p1 == p1') /\ (p2 == p2') ==> (p1 ++ p2 == p1' ++ p2')``,
  ASM_SIMP_TAC (srw_ss()) [raw_lswapstr_APPEND, permeq_def, FUN_EQ_THM]);

val halfpermeq_eliminate = prove(
  ``((==) x = (==)y) = (x == y)``,
  SRW_TAC [][FUN_EQ_THM, EQ_IMP_THM, permeq_def]);

val app_permeq_cong = store_thm(
  "app_permeq_cong",
  ``((==) p1 = (==) p1') ==> ((==) p2 = (==) p2') ==>
    ((==) (p1 ++ p2) = (==) (p1' ++ p2'))``,
  SRW_TAC [][halfpermeq_eliminate, app_permeq_monotone]);

val permof_inverse_lemma = prove(
  ``!p. p ++ REVERSE p == []``,
  ASM_SIMP_TAC (srw_ss()) [FUN_EQ_THM, permeq_def] THEN Induct THEN
  SRW_TAC [][] THEN ONCE_REWRITE_TAC [raw_lswapstr_APPEND] THEN SRW_TAC [][]);

val permof_inverse = store_thm(
  "permof_inverse",
 ``(p ++ REVERSE p == []) /\ (REVERSE p ++ p == [])``,
  METIS_TAC [permof_inverse_lemma, REVERSE_REVERSE]);

val permof_inverse_append = store_thm (
  "permof_inverse_append",
  ``(p ++ q) ++ REVERSE q == p ∧ (p ++ REVERSE q) ++ q == p``,
  SIMP_TAC bool_ss [GSYM APPEND_ASSOC] THEN
  CONJ_TAC THEN
  SIMP_TAC bool_ss [Once (GSYM APPEND_NIL), SimpR ``(==)``] THEN
  MATCH_MP_TAC app_permeq_monotone THEN SRW_TAC [][permof_inverse]);

val permof_inverse_applied = raw_lswapstr_inverse

val permof_dups = store_thm(
  "permof_dups",
  ``h::h::t == t``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val permof_dups_rwt = store_thm(
  "permof_dups_rwt",
  ``(==) (h::h::t) = (==) t``,
  SRW_TAC [][halfpermeq_eliminate, permof_dups]);

val permof_idfront = store_thm(
  "permof_idfront",
  ``(x,x) :: t == t``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val permof_REVERSE_monotone = store_thm(
  "permof_REVERSE_monotone",
  ``(x == y) ==> (REVERSE x == REVERSE y)``,
  STRIP_TAC THEN
  `REVERSE x ++ x == REVERSE x ++ y`
    by METIS_TAC [app_permeq_monotone, permeq_refl] THEN
  `REVERSE x ++ y == []`
    by METIS_TAC [permof_inverse, permeq_trans, permeq_sym] THEN
  `REVERSE x ++ (y ++ REVERSE y) == REVERSE y`
    by METIS_TAC [APPEND, APPEND_ASSOC,
                  app_permeq_monotone, permeq_refl] THEN
  METIS_TAC [permof_inverse, APPEND_NIL,
             app_permeq_monotone, permeq_refl, permeq_trans, permeq_sym]);

val permeq_cons_monotone = store_thm(
  "permeq_cons_monotone",
  ``(p1 == p2) ==> (h::p1 == h::p2)``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val permeq_swap_ends0 = store_thm(
  "permeq_swap_ends0",
  ``!p x y. p ++ [(x,y)] == (perm_of p x, perm_of p y)::p``,
  Induct THEN SRW_TAC [][permeq_refl] THEN
  Q_TAC SUFF_TAC `h::(perm_of p x, perm_of p y)::p ==
                  (swapstr (FST h) (SND h) (perm_of p x),
                   swapstr (FST h) (SND h) (perm_of p y))::h::p`
        THEN1 METIS_TAC [permeq_trans, permeq_cons_monotone] THEN
  SRW_TAC [][FUN_EQ_THM, permeq_def]);

val app_permeq_left_cancel = store_thm(
  "app_permeq_left_cancel",
  ``!p1 p1' p2 p2'. p1 == p1' /\ p1 ++ p2 == p1' ++ p2' ==> p2 == p2'``,
  REPEAT STRIP_TAC THEN
  `REVERSE p1 == REVERSE p1'` by METIS_TAC [permof_REVERSE_monotone] THEN
  `(REVERSE p1) ++ p1 ++ p2 == (REVERSE p1') ++ p1' ++ p2'`
    by (METIS_TAC [app_permeq_monotone, APPEND_ASSOC]) THEN
  `[] ++ p2 == (REVERSE p1) ++ p1 ++ p2 /\
   [] ++ p2' == (REVERSE p1') ++ p1' ++ p2'`
    by (METIS_TAC [app_permeq_monotone, permeq_refl, permeq_sym, permof_inverse]) THEN
  METIS_TAC [APPEND, permeq_refl, permeq_sym, permeq_trans]);

val app_permeq_right_cancel = store_thm(
  "app_permeq_right_cancel",
  ``!p1 p1' p2 p2'. p1 == p1' /\ p2 ++ p1 == p2' ++ p1' ==> p2 == p2'``,
  REPEAT STRIP_TAC THEN
  `REVERSE p1 == REVERSE p1'` by METIS_TAC [permof_REVERSE_monotone] THEN
  `p2 ++ (p1 ++ (REVERSE p1)) == p2' ++ (p1' ++ (REVERSE p1'))`
    by (METIS_TAC [app_permeq_monotone, APPEND_ASSOC]) THEN
  `p2 ++ [] == p2 ++ (p1 ++ (REVERSE p1)) /\
   p2' ++ [] == p2' ++ (p1' ++ (REVERSE p1'))`
    by (METIS_TAC [app_permeq_monotone, permeq_refl, permeq_sym, permof_inverse]) THEN
  METIS_TAC [APPEND_NIL, permeq_refl, permeq_trans, permeq_sym]);

(* ----------------------------------------------------------------------
    Define what it is to be a permutation action on a type (pmact)
   ---------------------------------------------------------------------- *)

val _ = type_abbrev("pm",``:(string # string) list``);

val _ = add_rule {fixity = Suffix 2100,
                  term_name = "⁻¹",
                  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⁻¹"]}
val _ = overload_on ("⁻¹", ``REVERSE : pm -> pm``)
val _ = TeX_notation {hol="⁻¹", TeX= ("\\HOLTokenInverse{}", 1)}

val is_pmact_def = Define`
  is_pmact (f:pm -> 'a -> 'a) <=>
      (!x. f [] x = x) /\
      (!p1 p2 x. f (p1 ++ p2) x = f p1 (f p2 x)) /\
      (!p1 p2. (p1 == p2) ==> (f p1 = f p2))`;

val existence = prove(
``?p. is_pmact p``,
  Q.EXISTS_TAC `K I` THEN
  SRW_TAC [][is_pmact_def]);

val pmact_TY_DEF = new_type_definition ("pmact", existence);
val pmact_bijections = define_new_type_bijections
  {name="pmact_bijections",tyax=pmact_TY_DEF,ABS="mk_pmact",REP="pmact"};
val pmact_onto = prove_rep_fn_onto pmact_bijections;

Theorem is_pmact_pmact[simp] :
    !pm. is_pmact (pmact pm)
Proof
  METIS_TAC [pmact_onto]
QED

Theorem pmact_nil[simp] :
    !pm x. (pmact pm [] x = x)
Proof
  MP_TAC is_pmact_pmact THEN
  simp_tac std_ss [is_pmact_def]
QED

Theorem pmact_permeq[simp] :
    p1 == p2 ==> (pmact pm p1 = pmact pm p2)
Proof
  METIS_TAC [is_pmact_pmact,is_pmact_def]
QED

val pmact_decompose = store_thm(
  "pmact_decompose",
  ``!pm x y a. pmact pm (x ++ y) a = pmact pm x (pmact pm y a)``,
  MP_TAC is_pmact_pmact THEN
  simp_tac std_ss [is_pmact_def]);

Theorem pmact_dups[simp] :
    !f h t a. pmact f (h::h::t) a = pmact f t a
Proof
  MP_TAC is_pmact_pmact THEN
  SRW_TAC [][is_pmact_def] THEN
  Q_TAC SUFF_TAC `h::h::t == t` THEN1 METIS_TAC [pmact_permeq] THEN
  SRW_TAC [][permof_dups]
QED

Theorem pmact_id[simp] :
    !f x a t. pmact f ((x,x)::t) a = pmact f t a
Proof
  MP_TAC is_pmact_pmact THEN
  rpt strip_tac >>
  Q_TAC SUFF_TAC `((x,x)::t) == t`
        THEN1 METIS_TAC [is_pmact_def] THEN
  SRW_TAC [][permof_idfront]
QED

Theorem pmact_inverse[simp] :
    (pmact f p (pmact f p⁻¹ a) = a) /\
    (pmact f p⁻¹ (pmact f p a) = a)
Proof
  MP_TAC is_pmact_pmact THEN
  METIS_TAC [is_pmact_def, permof_inverse]
QED

Theorem pmact_sing_inv[simp] :
    pmact pm [h] (pmact pm [h] x) = x
Proof
  METIS_TAC [REVERSE_DEF, APPEND, pmact_inverse]
QED

val pmact_eql = store_thm(
  "pmact_eql",
  ``(pmact pm p x = y) = (x = pmact pm p⁻¹ y)``,
  MP_TAC is_pmact_pmact THEN
  SRW_TAC [][is_pmact_def, EQ_IMP_THM] THEN
  SRW_TAC [][pmact_decompose]);

(* |- x = pmact pm p y <=> pmact pm (REVERSE p) x = y *)
val pmact_eqr = save_thm(
  "pmact_eqr",
  pmact_eql |> Q.INST [`y` |-> `pmact pm p y`,
                       `x` |-> `pmact pm p⁻¹ x`]
            |> REWRITE_RULE [pmact_inverse]);

Theorem pmact_injective[simp] :
    (pmact pm p x = pmact pm p y) = (x = y)
Proof
  METIS_TAC [pmact_inverse]
QED

val permeq_flip_args = store_thm(
  "permeq_flip_args",
  ``(x,y)::t == (y,x)::t``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val pmact_flip_args = store_thm(
  "pmact_flip_args",
  ``pmact pm ((x,y)::t) a = pmact pm ((y,x)::t) a``,
  METIS_TAC [is_pmact_pmact, is_pmact_def, permeq_flip_args]);

Theorem pmact_append :
    !f p1 p2 x. pmact f (p1 ++ p2) x = pmact f p1 (pmact f p2 x)
Proof
    rpt GEN_TAC
 >> MP_TAC (Q.SPEC ‘f’ is_pmact_pmact)
 >> METIS_TAC [is_pmact_def]
QED

Theorem pmact_flip_args_all :
    !pm xs ys a. LENGTH xs = LENGTH ys ==>
                 pmact pm (ZIP (xs,ys)) a = pmact pm (ZIP (ys,xs)) a
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> qabbrev_tac ‘pi = ZIP (xs,ys)’
 >> ‘xs = MAP FST pi /\ ys = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> NTAC 2 POP_ORW
 >> Q.ID_SPEC_TAC ‘a’
 >> Q.ID_SPEC_TAC ‘pi’
 >> KILL_TAC
 >> Induct_on ‘pi’ >- rw []
 >> simp [FORALL_PROD]
 >> rpt GEN_TAC
 >> qabbrev_tac ‘pi' = ZIP (MAP SND pi,MAP FST pi)’
 >> ‘!(a :string) (b :string) ls. (a,b)::ls = [(a,b)] ++ ls’ by rw []
 >> POP_ORW
 >> simp [pmact_append, Once pmact_flip_args]
QED

(* ----------------------------------------------------------------------
   define (possibly parameterised) permutation actions on standard
   builtin types: functions, sets, lists, pairs, etc
  ----------------------------------------------------------------------  *)

(* two simple permutation actions: strings, and "everything else" *)
Theorem perm_of_is_pmact[simp] :
    is_pmact raw_lswapstr
Proof
  SRW_TAC [][is_pmact_def, raw_lswapstr_APPEND, permeq_def]
QED

Theorem discrete_is_pmact[simp] :
    is_pmact (K I)
Proof
  SRW_TAC [][is_pmact_def]
QED

val _ = overload_on("string_pmact", ``mk_pmact perm_of``);
val _ = overload_on("stringpm",``pmact string_pmact``);
val _ = overload_on("lswapstr", ``stringpm``);
val _ = overload_on("discrete_pmact",``(mk_pmact (K I))``);
val _ = overload_on("discretepm",``pmact discrete_pmact``);

val stringpm_raw = store_thm(
"stringpm_raw",
``stringpm = perm_of``,
srw_tac [][GSYM pmact_bijections]);

val permeq_swap_ends = save_thm(
  "permeq_swap_ends",
  SUBS [GSYM stringpm_raw] permeq_swap_ends0);

val lswapstr_swapstr = save_thm(
  "lswapstr_swapstr",
  ONCE_REWRITE_RULE [GSYM stringpm_raw] perm_of_swapstr);

val _ = remove_ovl_mapping "perm_of" {Thy="basic_swap", Name = "raw_lswapstr"}

(* l1 == l2 <=> !x. lswapstr l1 x = lswapstr l2 x *)
val permeq_thm = save_thm(
  "permeq_thm",
  permeq_def |> ONCE_REWRITE_RULE [GSYM stringpm_raw]
             |> REWRITE_RULE [FUN_EQ_THM])

(* |- (!s. lswapstr [] s = s) /\
      !h t s. lswapstr (h::t) s = swapstr (FST h) (SND h) (lswapstr t s)
 *)
Theorem stringpm_thm[simp] = SUBS [GSYM stringpm_raw] raw_lswapstr_def

val discretepm_raw = store_thm(
"discretepm_raw",
``discretepm = K I``,
srw_tac [][GSYM pmact_bijections]);

Theorem discretepm_thm[simp] :
    discretepm pi x = x
Proof
  srw_tac [][discretepm_raw]
QED

val pmact_sing_to_back = store_thm(
  "pmact_sing_to_back",
  ``pmact pm [(lswapstr pi a, lswapstr pi b)] (pmact pm pi v) =
      pmact pm pi (pmact pm [(a,b)] v)``,
  SRW_TAC [][GSYM pmact_decompose] THEN
  Q_TAC SUFF_TAC `(lswapstr pi a,lswapstr pi b)::pi == pi ++ [(a,b)]`
        THEN1 METIS_TAC [is_pmact_def,is_pmact_pmact] THEN
  METIS_TAC [permeq_swap_ends, permeq_sym, stringpm_raw]);

(* cf. lswapstr_unchanged *)
Theorem lswapstr_unchanged' :
    !pi e. ~MEM e (MAP FST pi) /\ ~MEM e (MAP SND pi) ==> lswapstr pi e = e
Proof
    Induct_on ‘pi’ >> rw []
QED

Theorem lswapstr_apply_EL :
    !vs vs' i. LENGTH vs = LENGTH vs' /\
               DISJOINT (set vs) (set vs') /\
               ALL_DISTINCT vs /\
               ALL_DISTINCT vs' /\
               i < LENGTH vs ==>
               lswapstr (ZIP (vs,vs')) (EL i vs) = EL i vs'
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘pi = ZIP (vs,vs')’
 >> ‘vs  = MAP FST pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> ‘vs' = MAP SND pi’ by rw [Abbr ‘pi’, MAP_ZIP]
 >> Q.PAT_X_ASSUM ‘i < LENGTH vs’               MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set vs) (set vs')’ MP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT vs'’            MP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT vs’             MP_TAC
 (* rewrite vs and vs' by pi *)
 >> NTAC 2 POP_ORW
 >> KILL_TAC
 >> simp [LENGTH_MAP]
 >> Q.ID_SPEC_TAC ‘i’
 >> Induct_on ‘pi’ >> rw [FORALL_PROD]
 >> Cases_on ‘i’
 >- (Cases_on ‘h’ >> fs [] \\
     Suff ‘lswapstr pi q = q’ >- rw [] \\
     MATCH_MP_TAC lswapstr_unchanged' >> art [])
 >> Cases_on ‘h’ >> fs []
 >> Q.PAT_X_ASSUM ‘!i. i < LENGTH pi ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> rw []
 >> qabbrev_tac ‘vs  = MAP FST pi’
 >> qabbrev_tac ‘vs' = MAP SND pi’
 >> ‘LENGTH vs = LENGTH pi /\ LENGTH vs' = LENGTH pi’
      by rw [Abbr ‘vs’, Abbr ‘vs'’]
 >> Suff ‘swapstr q r (EL n vs') = EL n vs'’ >- rw []
 >> Suff ‘q <> EL n vs' /\ r <> EL n vs'’
 >- PROVE_TAC [swapstr_thm]
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> CCONTR_TAC
 >> FULL_SIMP_TAC std_ss [MEM_EL]
 >> METIS_TAC []
QED

Theorem MEM_lswapstr :
    !vs vs' x. LENGTH vs = LENGTH vs' /\
               DISJOINT (set vs) (set vs') /\
               ALL_DISTINCT vs /\ ALL_DISTINCT vs' /\
               MEM x vs ==> MEM (lswapstr (ZIP (vs,vs')) x) vs'
Proof
    rw [MEM_EL]
 >> Q.EXISTS_TAC ‘n’ >> rw []
 >> MATCH_MP_TAC lswapstr_apply_EL >> rw []
QED

Theorem MEM_lswapstr' :
    !vs vs' x. LENGTH vs = LENGTH vs' /\
               DISJOINT (set vs) (set vs') /\
               ALL_DISTINCT vs /\ ALL_DISTINCT vs' /\
               MEM x vs' ==> MEM (lswapstr (ZIP (vs,vs')) x) vs
Proof
    rpt STRIP_TAC
 >> Know ‘lswapstr (ZIP (vs,vs')) x = lswapstr (ZIP (vs',vs)) x’
 >- (MATCH_MP_TAC pmact_flip_args_all >> art [])
 >> Rewr'
 >> MATCH_MP_TAC MEM_lswapstr
 >> simp [Once DISJOINT_SYM]
QED

(* |- !p1 p2 x. lswapstr (p1 ++ p2) x = lswapstr p1 (lswapstr p2 x) *)
Theorem lswapstr_append = ISPEC “string_pmact” pmact_append

(*---------------------------------------------------------------------------*
 *  Permutation of a function call (fnpm)
 *---------------------------------------------------------------------------*)

val raw_fnpm_def = Define`
  raw_fnpm (dpm: α pmact) (rpm: β pmact) p f x = pmact rpm p (f (pmact dpm p⁻¹ x))
`;
val _ = export_rewrites["raw_fnpm_def"];

val _ = overload_on ("fn_pmact", ``λdpm rpm. mk_pmact (raw_fnpm dpm rpm)``);
val _ = overload_on ("fnpm", ``λdpm rpm. pmact (fn_pmact dpm rpm)``);

val fnpm_raw = store_thm(
"fnpm_raw",
``fnpm dpm rpm = raw_fnpm dpm rpm``,
srw_tac [][GSYM pmact_bijections] >>
SRW_TAC [][is_pmact_def, FUN_EQ_THM, REVERSE_APPEND, pmact_decompose] THEN
METIS_TAC [permof_REVERSE_monotone,pmact_permeq]);

(* |- !dpm rpm p f x.
        fnpm dpm rpm p f x = pmact rpm p (f (pmact dpm (REVERSE p) x))
 *)
Theorem fnpm_def =
    SUBS [GSYM fnpm_raw] (SPEC_ALL raw_fnpm_def)
 |> Q.GENL [`dpm`,`rpm`,`p`,`f`,`x`]

(*---------------------------------------------------------------------------*
 *  Permutation of a set of names (setpm)
 *---------------------------------------------------------------------------*)

Overload set_pmact = ``λpm. mk_pmact (fnpm pm discrete_pmact) : α set pmact``
Overload setpm = ``λpm. pmact (set_pmact pm)``
Overload sset_pmact = ``set_pmact string_pmact``
Overload ssetpm = ``pmact sset_pmact``

Theorem pmact_IN[simp]:
  (x IN (setpm pm π s) ⇔ pmact pm π⁻¹ x IN s)
Proof
  SRW_TAC [][fnpm_raw, SPECIFICATION] THEN
  let open combinTheory in
    METIS_TAC [pmact_bijections, K_THM, I_THM, discrete_is_pmact]
  end
QED

Theorem pmact_UNIV[simp] :
    setpm pm π UNIV = UNIV
Proof
  SRW_TAC [][EXTENSION, SPECIFICATION, fnpm_def] THEN
  SRW_TAC [][UNIV_DEF]
QED

Theorem pmact_EMPTY[simp] :
    setpm pm π {} = {}
Proof
  SRW_TAC [][EXTENSION, SPECIFICATION, fnpm_def] THEN
  SRW_TAC [][EMPTY_DEF]
QED

val pmact_INSERT = store_thm(
  "pmact_INSERT",
  ``setpm pm π (e INSERT s) = pmact pm π e INSERT setpm pm π s``,
  SRW_TAC [][EXTENSION, pmact_IN, pmact_eql]);

val pmact_UNION = store_thm(
  "pmact_UNION",
  ``setpm pm π (s1 UNION s2) = setpm pm π s1 UNION setpm pm π s2``,
  SRW_TAC [][EXTENSION, pmact_IN]);

val pmact_DIFF = store_thm(
  "pmact_DIFF",
  ``setpm pm pi (s DIFF t) = setpm pm pi s DIFF setpm pm pi t``,
  SRW_TAC [][EXTENSION, pmact_IN]);

val pmact_DELETE = store_thm(
  "pmact_DELETE",
  ``setpm pm p (s DELETE e) = setpm pm p s DELETE pmact pm p e``,
  SRW_TAC [][EXTENSION, pmact_IN, pmact_eql]);

Theorem pmact_FINITE[simp] :
    FINITE (setpm pm p s) = FINITE s
Proof
  Q_TAC SUFF_TAC `(!s. FINITE s ==> FINITE (setpm pm p s)) /\
                  (!s. FINITE s ==> !t p. (setpm pm p t = s) ==> FINITE t)`
        THEN1 METIS_TAC [] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][pmact_INSERT],
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    SRW_TAC [][pmact_eql, pmact_INSERT]
  ]
QED

(* |- !pi x s. x IN ssetpm pi s <=> lswapstr (REVERSE pi) x IN s *)
Theorem ssetpm_IN =
         pmact_IN |> GEN_ALL |> INST_TYPE [“:'a” |-> “:string”]
                  |> Q.SPECL [‘pi’, ‘x’, ‘s’, ‘string_pmact’]
                  |> Q.GENL [‘pi’, ‘x’, ‘s’]

Theorem ssetpm_unchanged_lemma[local] :
    !s. FINITE s ==> !pi. DISJOINT (set (MAP FST pi)) s /\
                          DISJOINT (set (MAP SND pi)) s ==>
                          ssetpm pi s = s
Proof
    HO_MATCH_MP_TAC FINITE_INDUCT
 >> rw [pmact_INSERT]
 >> Suff ‘lswapstr pi e = e’ >- rw []
 >> MATCH_MP_TAC lswapstr_unchanged' >> art []
QED

Theorem ssetpm_unchanged :
    !pi s. FINITE s /\ DISJOINT (set (MAP FST pi)) s /\
                       DISJOINT (set (MAP SND pi)) s ==>
                       ssetpm pi s = s
Proof
    rpt STRIP_TAC
 >> irule ssetpm_unchanged_lemma >> art []
QED

(*---------------------------------------------------------------------------*
 *  Permutation of optional values (optpm)
 *---------------------------------------------------------------------------*)

val raw_optpm_def = Define`
  (raw_optpm pm pi NONE = NONE) /\
  (raw_optpm pm pi (SOME x) = SOME (pmact pm pi x))`;
val _ = export_rewrites ["raw_optpm_def"];

val _ = overload_on("opt_pmact",``λpm. mk_pmact (raw_optpm pm)``);
val _ = overload_on("optpm",``λpm. pmact (opt_pmact pm)``);

val optpm_raw = store_thm(
"optpm_raw",
``optpm pm = raw_optpm pm``,
srw_tac [][GSYM pmact_bijections] >>
srw_tac [][is_pmact_def] THENL [
  Cases_on `x` THEN SRW_TAC [][],
  Cases_on `x` THEN SRW_TAC [][pmact_decompose],
  srw_tac [][FUN_EQ_THM] >>
  Cases_on `x` THEN SRW_TAC [][] THEN
  AP_THM_TAC >> srw_tac [][]
]);

(* |- optpm pm pi NONE = NONE /\ optpm pm pi (SOME x) = SOME (pmact pm pi x) *)
Theorem optpm_thm[simp] =
    raw_optpm_def |> CONJUNCTS |> map SPEC_ALL |> map (SUBS [GSYM optpm_raw])
 |> LIST_CONJ

(*---------------------------------------------------------------------------*
 *  Permutation of a pair of values (pairpm)
 *---------------------------------------------------------------------------*)

val raw_pairpm_def = Define`
  raw_pairpm apm bpm pi (a,b) = (pmact apm pi a, pmact bpm pi b)
`;
val _ = export_rewrites ["raw_pairpm_def"]

val _ = overload_on("pair_pmact",``λapm bpm. mk_pmact (raw_pairpm apm bpm)``);
val _ = overload_on("pairpm",``λapm bpm. pmact (pair_pmact apm bpm)``);

val pairpm_raw = store_thm(
  "pairpm_raw",
  ``pairpm apm bpm = raw_pairpm apm bpm``,
  srw_tac [][GSYM pmact_bijections] >>
  SIMP_TAC (srw_ss()) [is_pmact_def, pairTheory.FORALL_PROD,
                       FUN_EQ_THM, pmact_decompose] >>
  metis_tac [pmact_permeq]);

(* |- !b a pi bpm apm.
        pairpm apm bpm pi (a,b) = (pmact apm pi a,pmact bpm pi b)
 *)
Theorem pairpm_thm[simp] =
    raw_pairpm_def |> SPEC_ALL |> SUBS [GSYM pairpm_raw]
 |> (rev_itlist Q.GEN) [`apm`,`bpm`,`pi`,`a`,`b`]

Theorem FST_pairpm[simp] :
    FST (pairpm pm1 pm2 pi v) = pmact pm1 pi (FST v)
Proof
  Cases_on `v` THEN SRW_TAC [][]
QED

Theorem SND_pairpm[simp] :
    SND (pairpm pm1 pm2 pi v) = pmact pm2 pi (SND v)
Proof
  Cases_on `v` THEN SRW_TAC [][]
QED

(*---------------------------------------------------------------------------*
 *  Permutation of values of sum types (sumpm)
 *---------------------------------------------------------------------------*)

val raw_sumpm_def = Define`
  (raw_sumpm pm1 pm2 pi (INL x) = INL (pmact pm1 pi x)) /\
  (raw_sumpm pm1 pm2 pi (INR y) = INR (pmact pm2 pi y))
`;
val _ = export_rewrites ["raw_sumpm_def"]

val _ = overload_on("sum_pmact",``λpm1 pm2. mk_pmact (raw_sumpm pm1 pm2)``);
val _ = overload_on("sumpm",``λpm1 pm2. pmact (sum_pmact pm1 pm2)``);

val sumpm_raw = store_thm(
  "sumpm_raw",
  ``sumpm pm1 pm2 = raw_sumpm pm1 pm2``,
  srw_tac [][GSYM pmact_bijections] >>
  SRW_TAC [][is_pmact_def, FUN_EQ_THM] THEN Cases_on `x` THEN
  SRW_TAC [][pmact_decompose] >> AP_THM_TAC >> srw_tac [][pmact_permeq]);

(* |- (!pm1 pm2 pi x. sumpm pm1 pm2 pi (INL x) = INL (pmact pm1 pi x)) /\
      !pm1 pm2 pi y. sumpm pm1 pm2 pi (INR y) = INR (pmact pm2 pi y)
 *)
Theorem sumpm_thm[simp] =
    raw_sumpm_def |> CONJUNCTS
|> map (fn th => th |> Q.SPECL [`pm1`,`pm2`]
                    |> SUBS [GSYM sumpm_raw]
                    |> (itlist Q.GEN [`pm1`,`pm2`]))
|> LIST_CONJ

(*---------------------------------------------------------------------------*
 *  Permutation of list of values (listpm)
 *---------------------------------------------------------------------------*)

val raw_listpm_def = Define`
  (raw_listpm apm pi [] = []) /\
  (raw_listpm apm pi (h::t) = pmact apm pi h :: raw_listpm apm pi t)
`;
val _ = export_rewrites ["raw_listpm_def"]

val _ = overload_on("list_pmact",``λapm. mk_pmact (raw_listpm apm)``);
val _ = overload_on("listpm",``λapm. pmact (list_pmact apm)``)

val listpm_raw = store_thm(
  "listpm_raw",
  ``listpm apm = raw_listpm apm``,
  srw_tac [][GSYM pmact_bijections] >>
  SIMP_TAC (srw_ss()) [is_pmact_def, FUN_EQ_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL [
    Induct THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][pmact_decompose],
    REPEAT GEN_TAC THEN STRIP_TAC THEN Induct THEN SRW_TAC [][] >>
    AP_THM_TAC >> srw_tac [][pmact_permeq]
  ]);

(* |- (!apm pi. listpm apm pi [] = []) /\
      !apm pi h t. listpm apm pi (h::t) = pmact apm pi h::listpm apm pi t
 *)
Theorem listpm_thm[simp] =
   raw_listpm_def |> CONJUNCTS
|> map (fn th => th |> Q.SPEC `apm` |> SUBS [GSYM listpm_raw] |> Q.GEN `apm`)
|> LIST_CONJ

val listpm_MAP = store_thm(
  "listpm_MAP",
  ``!l. listpm pm pi l = MAP (pmact pm pi) l``,
  Induct THEN fsrw_tac [][]);

val listpm_APPENDlist = store_thm(
  "listpm_APPENDlist",
  ``listpm pm pi (l1 ++ l2) = listpm pm pi l1 ++ listpm pm pi l2``,
  Induct_on `l1` THEN fsrw_tac [][]);

Theorem LENGTH_listpm[simp] :
    LENGTH (listpm pm pi l) = LENGTH l
Proof
  Induct_on `l` >> fsrw_tac [][]
QED

Theorem EL_listpm[simp] :
    ∀l n. n < LENGTH l ==> (EL n (listpm pm pi l) = pmact pm pi (EL n l))
Proof
  Induct >> srw_tac [][] >> Cases_on `n` >> srw_tac [][] >>
  fsrw_tac [][]
QED

val MEM_listpm = store_thm(
  "MEM_listpm",
  ``MEM x (listpm pm pi l) ⇔ MEM (pmact pm pi⁻¹ x) l``,
  Induct_on `l` >> fsrw_tac [][pmact_eql]);

val MEM_listpm_EXISTS = store_thm(
  "MEM_listpm_EXISTS",
  ``MEM x (listpm pm pi l) ⇔ ∃y. MEM y l ∧ (x = pmact pm pi y)``,
  Induct_on `l` >> fsrw_tac [][] >> metis_tac []);

(* lists of pairs of strings, (concrete rep for permutations) *)
val _ = overload_on("cpm_pmact", ``list_pmact (pair_pmact string_pmact string_pmact)``);
val _ = overload_on ("cpmpm", ``pmact cpm_pmact``);

(* moved here from sttScript.sml *)
Theorem ALL_DISTINCT_listpm[simp]:
  ALL_DISTINCT (listpm act π xs) = ALL_DISTINCT xs
Proof
  Induct_on ‘xs’ >> simp[MEM_listpm]
QED

(* ----------------------------------------------------------------------
    Notion of support, and calculating the smallest set of support
   ---------------------------------------------------------------------- *)

val support_def = Define`
  support (pm : α pmact) (a:α) (supp:string set) =
     ∀x y. x ∉ supp /\ y ∉ supp ⇒ (pmact pm [(x,y)] a = a)
`;

val pmact_support = store_thm(
  "pmact_support",
  ``(support pm (pmact pm π x) s =
     support pm x (setpm string_pmact π⁻¹ s))``,
  ASM_SIMP_TAC (srw_ss()) [EQ_IMP_THM, support_def, pmact_IN] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MAP_EVERY Q.X_GEN_TAC [`a`,`b`] THEN STRIP_TAC THENL [
    `pmact pm [(stringpm π a, stringpm π b)] (pmact pm π x) = pmact pm π x`
       by METIS_TAC [] THEN
    `pmact pm ([(stringpm π a, stringpm π b)] ++ π) x = pmact pm π x`
       by METIS_TAC [pmact_decompose] THEN
    `[(stringpm π a, stringpm π b)] ++ π == π ++ [(a,b)]`
       by METIS_TAC [permeq_swap_ends, permeq_sym, APPEND] THEN
    `pmact pm (π ++ [(a,b)]) x = pmact pm π x`
       by METIS_TAC [pmact_permeq] THEN
    METIS_TAC [pmact_injective, pmact_decompose],
    `pmact pm [(a,b)] (pmact pm π x) = pmact pm ([(a,b)] ++ π) x`
       by METIS_TAC [pmact_decompose] THEN
    `[(a,b)] ++ π == π ++ [(stringpm π⁻¹ a, stringpm π⁻¹ b)]`
       by (SRW_TAC [][] THEN
           Q.SPECL_THEN [`π`, `lswapstr π⁻¹ a`, `lswapstr π⁻¹ b`]
                        (ASSUME_TAC o REWRITE_RULE [pmact_inverse])
                        permeq_swap_ends THEN
           METIS_TAC [permeq_sym]) THEN
    `pmact pm [(a,b)] (pmact pm π x) =
          pmact pm (π ++ [(stringpm π⁻¹ a, stringpm π⁻¹ b)]) x`
       by METIS_TAC [pmact_permeq] THEN
    ` _ = pmact pm π (pmact pm [(stringpm π⁻¹ a, stringpm π⁻¹ b)] x)`
       by METIS_TAC [pmact_decompose] THEN
    ASM_SIMP_TAC (srw_ss()) [pmact_injective]
  ]);

val support_dwards_directed = store_thm(
  "support_dwards_directed",
  ``support pm e s1 /\ support pm e s2 /\
    FINITE s1 /\ FINITE s2 ==>
    support pm e (s1 INTER s2)``,
  SIMP_TAC bool_ss [support_def] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `x = y` THEN1 METIS_TAC [pmact_id, pmact_nil] THEN
  Q_TAC (NEW_TAC "z") `{x;y} UNION s1 UNION s2` THEN
  `[(x,y)] == [(x,z); (y,z); (x,z)]`
     by (SRW_TAC [][FUN_EQ_THM, permeq_def] THEN
         CONV_TAC (RAND_CONV
                    (ONCE_REWRITE_CONV [GSYM swapstr_swapstr])) THEN
         SIMP_TAC bool_ss [swapstr_inverse] THEN
         SRW_TAC [][]) THEN
  `pmact pm [(x,y)] e = pmact pm [(x,z); (y,z); (x,z)] e`
     by METIS_TAC [pmact_permeq] THEN
  ` _ = pmact pm [(x,z)] (pmact pm [(y,z)] (pmact pm [(x,z)] e))`
     by METIS_TAC [pmact_decompose, APPEND] THEN
  METIS_TAC [IN_INTER]);

val supp_def = Define`
  supp pm x = { (a:string) | INFINITE { (b:string) | pmact pm [(a,b)] x ≠ x}}
`;

val supp_supports = store_thm(
  "supp_supports",
  ``support pm x (supp pm x)``,
  ASM_SIMP_TAC (srw_ss()) [support_def, supp_def, pmact_decompose] THEN
  MAP_EVERY Q.X_GEN_TAC [`a`, `b`] THEN STRIP_TAC THEN
  Q.ABBREV_TAC `aset = {b | ~(pmact pm [(a,b)] x = x)}` THEN
  Q.ABBREV_TAC `bset = {c | ~(pmact pm [(b,c)] x = x)}` THEN
  Cases_on `a = b` THEN1 SRW_TAC [][pmact_id, pmact_nil] THEN
  `?c. ~(c IN aset) /\ ~(c IN bset) /\ ~(c = a) /\ ~(c = b)`
      by (Q.SPEC_THEN `{a;b} UNION aset UNION bset` MP_TAC NEW_def THEN
          SRW_TAC [][] THEN METIS_TAC []) THEN
  `(pmact pm [(a,c)] x = x) /\ (pmact pm [(b,c)] x = x)`
      by FULL_SIMP_TAC (srw_ss()) [Abbr`aset`, Abbr`bset`] THEN
  `pmact pm ([(a,c)] ++ [(b,c)] ++ [(a,c)]) x = x`
      by SRW_TAC [][pmact_decompose] THEN
  Q_TAC SUFF_TAC `[(a,c)] ++ [(b,c)] ++ [(a,c)] == [(a,b)]`
        THEN1 METIS_TAC [pmact_permeq] THEN
  SIMP_TAC (srw_ss()) [permeq_def, FUN_EQ_THM] THEN
  ONCE_REWRITE_TAC [GSYM swapstr_swapstr] THEN
  `(swapstr a c b = b) /\ (swapstr a c c = a)` by SRW_TAC [][swapstr_def] THEN
  ASM_REWRITE_TAC [] THEN SRW_TAC [][]);

val supp_fresh = store_thm(
  "supp_fresh",
  ``x ∉ supp apm v /\ y ∉ supp apm v ⇒ (pmact apm [(x,y)] v = v)``,
  METIS_TAC [support_def, supp_supports]);

val setpm_postcompose = store_thm(
  "setpm_postcompose",
  ``!P pm p. is_pmact pm ==> ({x | P (pm p x)} = setpm (mk_pmact pm) p⁻¹ {x | P x})``,
  SRW_TAC [][EXTENSION, pmact_IN] >> metis_tac [pmact_bijections]);

val perm_supp = store_thm(
  "perm_supp",
  ``supp pm (pmact pm p x) = setpm string_pmact p (supp pm x)``,
  SIMP_TAC (srw_ss()) [EXTENSION, pmact_IN, supp_def, pmact_eql] THEN
  Q.X_GEN_TAC `a` THEN
  `!e x y. pmact pm (REVERSE p) (pmact pm [(x,y)] e) =
           pmact pm [(stringpm (REVERSE p) x, stringpm (REVERSE p) y)]
              (pmact pm (REVERSE p) e)`
      by METIS_TAC [stringpm_raw, pmact_decompose, pmact_permeq, permeq_swap_ends, APPEND] THEN
  SRW_TAC [][pmact_inverse] THEN
  Q.MATCH_ABBREV_TAC `FINITE s1 = FINITE s2` THEN
  `s1 = { b | (\s. ~(x = pmact pm [(stringpm (REVERSE p) a, s)] x))
                (stringpm (REVERSE p ) b)}`
     by SRW_TAC [][Abbr`s1`] THEN
  ` _ = setpm (mk_pmact stringpm) (REVERSE (REVERSE p))
              {b | (\s. ~(x = pmact pm [(stringpm (REVERSE p) a, s)] x)) b}`
     by (MATCH_MP_TAC setpm_postcompose THEN SRW_TAC [][]) THEN
  Q.UNABBREV_TAC `s2` THEN SRW_TAC [][]);

val supp_apart = store_thm(
  "supp_apart",
  ``a ∈ supp pm x /\ b ∉ supp pm x ⇒ pmact pm [(a,b)] x ≠ x``,
  STRIP_TAC THEN
  `a ≠ b` by METIS_TAC [] THEN
  `b ∈ setpm string_pmact [(a,b)] (supp pm x)`
     by SRW_TAC[][pmact_IN, swapstr_def] THEN
  `b ∈ supp pm (pmact pm [(a,b)] x)`
     by metis_tac [perm_supp] THEN
  `supp pm x ≠ supp pm (pmact pm [(a,b)] x)` by METIS_TAC [] THEN
  METIS_TAC []);

val supp_finite_or_UNIV = store_thm(
  "supp_finite_or_UNIV",
  ``INFINITE (supp pm x) ⇒ (supp pm x = UNIV)``,
  STRIP_TAC THEN
  SPOSE_NOT_THEN (Q.X_CHOOSE_THEN `a` MP_TAC o
                  SIMP_RULE (srw_ss()) [EXTENSION]) THEN
  DISCH_THEN (fn th => ASSUME_TAC th THEN MP_TAC th THEN
                       SIMP_TAC (srw_ss()) [supp_def]) THEN
  STRIP_TAC THEN
  `∃b. b ∉ {b | pmact pm [(a,b)] x ≠ x} ∧ b ∈ supp pm x`
    by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [supp_apart, pmact_flip_args]);

val supp_absence_FINITE = store_thm(
  "supp_absence_FINITE",
  ``a ∉ supp pm x ⇒ FINITE (supp pm x)``,
  METIS_TAC [IN_UNIV, supp_finite_or_UNIV]);

(* lemma3_4_i from Pitts & Gabbay - New Approach to Abstract Syntax *)
val supp_smallest = store_thm(
  "supp_smallest",
  ``support pm x s /\ FINITE s ==> supp pm x SUBSET s``,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SUBSET_DEF] THEN
  Q.X_GEN_TAC `a` THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `!b. ~(b IN s) ==> (pmact pm [(a,b)] x = x)`
     by METIS_TAC [support_def] THEN
  `{b | ~(pmact pm [(a,b)] x = x)} SUBSET s`
     by (SRW_TAC [][SUBSET_DEF] THEN METIS_TAC []) THEN
  `FINITE {b | ~(pmact pm [(a,b)] x = x)}` by METIS_TAC [SUBSET_FINITE] THEN
  FULL_SIMP_TAC (srw_ss()) [supp_def]);

val notinsupp_I = store_thm(
  "notinsupp_I",
  ``∀A apm e x. FINITE A ∧ support apm x A ∧ e ∉ A ==> e ∉ supp apm x``,
  metis_tac [supp_smallest, SUBSET_DEF]);

val lemma0 = prove(
  ``COMPL (e INSERT s) = COMPL s DELETE e``,
  SRW_TAC [][EXTENSION] THEN METIS_TAC []);
val lemma = prove(
  ``!s: string set. FINITE s ==> ~FINITE (COMPL s)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][lemma0] THEN
  SRW_TAC [][INFINITE_STR_UNIV]);

val supp_unique = store_thm(
  "supp_unique",
  ``support pm x s /\ FINITE s /\
    (!s'. support pm x s' /\ FINITE s' ==> s SUBSET s') ==>
    (supp pm x = s)``,
  SRW_TAC [][] THEN
  `FINITE (supp pm x)` by METIS_TAC [supp_smallest, SUBSET_FINITE] THEN
  `support pm x (supp pm x)` by METIS_TAC [supp_supports] THEN
  `!s'. support pm x s' /\ FINITE s' ==> supp pm x SUBSET s'`
     by METIS_TAC [supp_smallest] THEN
  METIS_TAC [SUBSET_ANTISYM]);

val supp_unique_apart = store_thm(
  "supp_unique_apart",
  ``support pm x s /\ FINITE s /\
    (!a b. a IN s /\ ~(b IN s) ==> ~(pmact pm [(a,b)] x = x)) ==>
    (supp pm x = s)``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][SUBSET_DEF] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `?z. ~(z IN s') /\ ~(z IN s)`
      by (Q.SPEC_THEN `s UNION s'` MP_TAC NEW_def THEN
          SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC [support_def]);

(* some examples of supp *)
Theorem supp_string[simp] :
    supp string_pmact s = {s}
Proof
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def]
QED

Theorem supp_discrete[simp] :
    supp discrete_pmact x = {}
Proof
  SRW_TAC [][supp_def]
QED

val supp_unitfn = store_thm(
  "supp_unitfn",
  ``(supp (fn_pmact discrete_pmact apm) (λu:unit. a) = supp apm a)``,
  Cases_on `∃x. x ∉ supp apm a` >| [
    fsrw_tac [][] >>
    match_mp_tac (GEN_ALL supp_unique_apart) >>
    srw_tac [][support_def, FUN_EQ_THM, fnpm_def, supp_fresh] >-
      metis_tac [supp_absence_FINITE] >>
    metis_tac [supp_apart],
    fsrw_tac [][] >>
    `supp apm a = univ(:string)` by srw_tac [][EXTENSION] >>
    fsrw_tac [][EXTENSION, supp_def, FUN_EQ_THM, fnpm_def]
  ])

(* options *)
val supp_optpm = store_thm(
  "supp_optpm",
  ``(supp (opt_pmact pm) NONE = {}) /\
    (supp (opt_pmact pm) (SOME x) = supp pm x)``,
  SRW_TAC [][supp_def]);
val _ = export_rewrites ["supp_optpm"]

(* pairs *)
Theorem supp_pairpm[simp]:
  (supp (pair_pmact pm1 pm2) (x,y) = supp pm1 x UNION supp pm2 y)
Proof
  SRW_TAC [][supp_def, GSPEC_OR, Excl "lift_disj_eq"]
QED

(* lists *)
Theorem supp_listpm[simp]:
    (supp (list_pmact apm) [] = {}) /\
    (supp (list_pmact apm) (h::t) = supp apm h UNION supp (list_pmact apm) t)
Proof
  SRW_TAC [][supp_def, GSPEC_OR, Excl "lift_disj_eq"]
QED

Theorem listsupp_APPEND[simp] :
    supp (list_pmact p) (l1 ++ l2) = supp (list_pmact p) l1 ∪ supp (list_pmact p) l2
Proof
  Induct_on `l1` THEN SRW_TAC [][AC UNION_ASSOC UNION_COMM]
QED

Theorem listsupp_REVERSE[simp] :
    supp (list_pmact p) (REVERSE l) = supp (list_pmact p) l
Proof
  Induct_on `l` THEN SRW_TAC [][UNION_COMM]
QED

val IN_supp_listpm = store_thm(
  "IN_supp_listpm",
  ``a ∈ supp (list_pmact pm) l ⇔ ∃e. MEM e l ∧ a ∈ supp pm e``,
  Induct_on `l` >> srw_tac [DNF_ss][]);

val NOT_IN_supp_listpm = store_thm(
  "NOT_IN_supp_listpm",
  ``a ∉ supp (list_pmact pm) l ⇔ ∀e. MEM e l ⇒ a ∉ supp pm e``,
  metis_tac [IN_supp_listpm])

(* concrete permutations, which get their own overload for calculating their
   support *)
Overload patoms = ``supp (list_pmact (pair_pmact string_pmact string_pmact))``

Theorem FINITE_patoms[simp] :
    !l. FINITE (patoms l)
Proof
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]
QED

Theorem patoms_fresh[simp] :
    !p. x ∉ patoms p ∧ y ∉ patoms p ⇒ (cpmpm [(x,y)] p = p)
Proof
  METIS_TAC [supp_supports, support_def]
QED

val lswapstr_unchanged = store_thm(
  "lswapstr_unchanged",
  ``!p. s ∉ patoms p ⇒ (lswapstr p s = s)``,
  Induct THEN SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][swapstr_def]);

val IN_patoms_MEM = store_thm(
  "IN_patoms_MEM",
  ``a ∈ patoms π ⇔ (∃b. MEM (a,b) π) ∨ (∃b. MEM (b,a) π)``,
  Induct_on `π` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN METIS_TAC []);

val pm_cpmpm_cancel = prove(
  ``pmact pm [(x,y)] (pmact pm (cpmpm [(x,y)] pi) (pmact pm [(x,y)] t)) = pmact pm pi t``,
  Induct_on `pi` THEN
  fsrw_tac [][pairTheory.FORALL_PROD, pmact_nil,
              pmact_sing_inv] THEN
  `!p q pi t. pmact pm ((swapstr x y p, swapstr x y q)::pi) t =
              pmact pm [(swapstr x y p, swapstr x y q)] (pmact pm pi t)`
     by SRW_TAC [][GSYM pmact_decompose] THEN
  REPEAT GEN_TAC THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
  fsrw_tac [][GSYM pmact_decompose] >>
  metis_tac [pmact_decompose, APPEND]);

val pmact_supp_empty = store_thm(
  "pmact_supp_empty",
  ``(supp (fn_pmact cpm_pmact (fn_pmact pm pm)) (pmact pm) = {})``,
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][] THEN
  SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, pm_cpmpm_cancel]);

val supp_pm_fresh = store_thm(
  "supp_pm_fresh",
  ``(supp pm x = {}) ==> (pmact pm pi x = x)``,
  Induct_on `pi` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pmact_nil] THEN
  REPEAT STRIP_TAC THEN
  `pmact pm ((p_1,p_2)::pi) x = pmact pm [(p_1,p_2)] (pmact pm pi x)`
     by SIMP_TAC (srw_ss()) [GSYM pmact_decompose] THEN
  SRW_TAC [][supp_fresh]);

val pm_pm_cpmpm = store_thm(
  "pm_pm_cpmpm",
  ``pmact pm pi1 (pmact pm pi2 s) = pmact pm (cpmpm pi1 pi2) (pmact pm pi1 s)``,
  Q.MATCH_ABBREV_TAC `L = R` THEN
  `L = fnpm pm pm pi1 (pmact pm pi2) (pmact pm pi1 s)`
     by SRW_TAC [][fnpm_def, pmact_inverse] THEN
  `_ = fnpm cpm_pmact
            (fn_pmact pm pm)
            pi1
            (pmact pm)
            (cpmpm pi1 pi2)
            (pmact pm pi1 s)`
     by (ONCE_REWRITE_TAC [fnpm_def] THEN
         SRW_TAC [][pmact_inverse]) THEN
  `fnpm cpm_pmact (fn_pmact pm pm) pi1 (pmact pm) = (pmact pm)`
     by SRW_TAC [][supp_pm_fresh, pmact_supp_empty] THEN
  METIS_TAC []);

val stringpm_stringpm_cpmpm = save_thm(
  "stringpm_stringpm_cpmpm",
  (SIMP_RULE std_ss []  o Q.INST [`pm` |-> `string_pmact`] o
   INST_TYPE [alpha |-> ``:string``]) pm_pm_cpmpm);

val patoms_cpmpm = store_thm(
  "patoms_cpmpm",
  ``patoms (cpmpm pi1 pi2) = setpm string_pmact pi1 (patoms pi2)``,
  SRW_TAC [][perm_supp]);

(* support for honest to goodness permutations, not just their
   representations *)
val perm_supp_SUBSET_plistvars = prove(
  ``!p. {s | ~(lswapstr p s = s)} SUBSET
        FOLDR (\p a. {FST p; SND p} UNION a) {} p``,
  ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN Induct THEN
  SRW_TAC [][] THEN
  Cases_on `x = FST h` THEN SRW_TAC [][] THEN
  Cases_on `x = SND h` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [swapstr_def, swapstr_eq_left]);

val FINITE_plistvars = prove(
  ``FINITE (FOLDR (\p a. {FST p; SND p} UNION a) {} p)``,
  Induct_on `p` THEN SRW_TAC [][]);
val lemma = MATCH_MP SUBSET_FINITE FINITE_plistvars

val perm_supp_finite = store_thm(
  "perm_supp_finite",
  ``FINITE {s | ~(lswapstr p s = s)}``,
  MATCH_MP_TAC lemma THEN SRW_TAC [][perm_supp_SUBSET_plistvars]);

val supp_perm_of = store_thm(
  "supp_perm_of",
  ``supp (fn_pmact string_pmact string_pmact) (lswapstr p) =
    { s | ~(lswapstr p s = s) }``,
  HO_MATCH_MP_TAC supp_unique THEN
  ASM_SIMP_TAC (srw_ss()) [perm_supp_finite] THEN CONJ_TAC THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, lswapstr_swapstr],

    Q.X_GEN_TAC `s` THEN
    SRW_TAC [][SUBSET_DEF] THEN
    SPOSE_NOT_THEN ASSUME_TAC THEN
    Q_TAC (NEW_TAC "y") `{x; lswapstr p⁻¹ x} UNION s` THEN
    `!a. fnpm string_pmact string_pmact [(x,y)] (lswapstr p) a = lswapstr p a`
       by METIS_TAC [support_def] THEN
    `p ++ [(x,y)] == [(x,y)] ++ p`
       by (POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [fnpm_def]) THEN
           SRW_TAC [][permeq_thm, pmact_decompose, GSYM swapstr_eq_left]) THEN
    `(x,y) :: p == (lswapstr p x, lswapstr p y) :: p`
       by METIS_TAC [permeq_swap_ends, permeq_trans, permeq_sym, APPEND] THEN
    `(x,y) :: (p ++ p⁻¹) == (lswapstr p x, lswapstr p y) :: (p ++ p⁻¹)`
       by METIS_TAC [app_permeq_monotone, APPEND, permeq_refl] THEN
    `!h. [h] == h :: (p ++ p⁻¹)`
       by METIS_TAC [permeq_cons_monotone, permof_inverse, permeq_sym] THEN
    `[(x,y)] == [(lswapstr p x, lswapstr p y)]`
       by METIS_TAC [permeq_trans, permeq_sym] THEN
    `lswapstr [(x,y)] x = lswapstr [(lswapstr p x, lswapstr p y)] x`
       by METIS_TAC [permeq_thm] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC (srw_ss()) [] THEN
    `x ≠ lswapstr p y` by METIS_TAC [pmact_inverse] THEN
    SRW_TAC [][swapstr_def]
  ]);

val support_FINITE_supp = store_thm(
  "support_FINITE_supp",
  ``support pm v A /\ FINITE A ==> FINITE (supp pm v)``,
  METIS_TAC [supp_smallest, SUBSET_FINITE]);

val support_fnapp = store_thm(
  "support_fnapp",
  ``support (fn_pmact dpm rpm) f A /\ support dpm d B ==>
    support rpm (f d) (A UNION B)``,
  SRW_TAC [][support_def] THEN
  fsrw_tac [][fnpm_def,FUN_EQ_THM] >>
  metis_tac []);

val supp_fnapp = store_thm(
  "supp_fnapp",
  ``supp rpm (f x) SUBSET supp (fn_pmact dpm rpm) f UNION supp dpm x``,
  METIS_TAC [supp_smallest, FINITE_UNION, supp_supports, support_fnapp,
             supp_finite_or_UNIV, SUBSET_UNIV, UNION_UNIV]);

val notinsupp_fnapp = store_thm(
  "notinsupp_fnapp",
  ``v ∉ supp (fn_pmact dpm rpm) f ∧ v ∉ supp dpm x ==>
    v ∉ supp rpm (f x)``,
  prove_tac [supp_fnapp, SUBSET_DEF, IN_UNION]);

val raw_fmpm_def = Define`
  raw_fmpm (dpm : 'd pmact) (rpm : 'r pmact) pi fmap =
    pmact rpm pi o_f fmap f_o pmact dpm (REVERSE pi)
`;
val _ = export_rewrites["raw_fmpm_def"];

val _ = overload_on("fm_pmact",``λdpm rpm. mk_pmact (raw_fmpm dpm rpm)``);
val _ = overload_on("fmpm",``λdpm rpm. pmact (fm_pmact dpm rpm)``);

val lemma0 = prove(
  ``(pmact pm pi x ∈ X ⇔ x ∈ setpm pm (REVERSE pi) X)``,
  SRW_TAC [][pmact_IN])
val lemma1 = prove(``{x | x ∈ X} = X``, SRW_TAC [][EXTENSION])
val lemma = prove(
  ``FINITE { x | pmact pm pi x ∈ FDOM f}``,
  SIMP_TAC bool_ss [lemma0, lemma1, pmact_FINITE, FDOM_FINITE]);

val fmpm_def = store_thm(
  "fmpm_def",
  ``fmpm dpm rpm = raw_fmpm dpm rpm``,
  srw_tac [][GSYM pmact_bijections] >>
  SRW_TAC [][is_pmact_def] THENL [
    `(!d. pmact dpm [] d = d) ∧ (!r. pmact rpm [] r = r)` by METIS_TAC [pmact_nil] THEN
    SRW_TAC [][fmap_EXT, EXTENSION, FDOM_f_o, lemma,
               FAPPLY_f_o, o_f_FAPPLY],

    `(!d pi1 pi2. pmact dpm (pi1 ++ pi2) d = pmact dpm pi1 (pmact dpm pi2 d)) ∧
     (!r pi1 pi2. pmact rpm (pi1 ++ pi2) r = pmact rpm pi1 (pmact rpm pi2 r))`
      by METIS_TAC [pmact_decompose] THEN
    SRW_TAC [][fmap_EXT, FDOM_f_o, lemma, o_f_FAPPLY,
               REVERSE_APPEND, FAPPLY_f_o],

    `REVERSE p1 == REVERSE p2` by METIS_TAC [permof_REVERSE_monotone] THEN
    `(pmact rpm p1 = pmact rpm p2) ∧ (pmact dpm (REVERSE p1) = pmact dpm (REVERSE p2))`
       by METIS_TAC [pmact_permeq] THEN
    SRW_TAC [][fmap_EXT, FUN_EQ_THM, FDOM_f_o, lemma]
  ]);

val fmpm_applied = store_thm(
  "fmpm_applied",
  ``pmact dpm (REVERSE pi) x ∈ FDOM fm ==>
    (fmpm dpm rpm pi fm ' x = pmact rpm pi (fm ' (pmact dpm (REVERSE pi) x)))``,
  SRW_TAC [][fmpm_def, FAPPLY_f_o, FDOM_f_o, lemma, o_f_FAPPLY]);

Theorem fmpm_FDOM:
  x IN FDOM (fmpm dpm rpm pi fmap) ⇔ pmact dpm (REVERSE pi) x IN FDOM fmap
Proof
  SRW_TAC [][fmpm_def, lemma, FDOM_f_o]
QED

val supp_setpm = store_thm(
  "supp_setpm",
  ``FINITE s ∧ (∀x. x ∈ s ⇒ FINITE (supp pm x)) ⇒
    (supp (set_pmact pm) s = BIGUNION (IMAGE (supp pm) s))``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][] THENL [
    SRW_TAC [][support_def] THEN
    SRW_TAC [][EXTENSION] THEN
    Cases_on `x ∈ supp pm x'` THENL [
      `x' ∉ s` by METIS_TAC [] THEN
      `y ∈ supp pm (pmact pm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN Cases_on `y ∈ supp pm x'` THENL [
      `x' ∉ s` by METIS_TAC [] THEN
      `x ∈ supp pm (pmact pm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN SRW_TAC [][supp_fresh],

    METIS_TAC [],

    SRW_TAC [][EXTENSION] THEN
    `∀x. b ∈ supp pm x ==> ¬(x ∈ s)` by METIS_TAC [] THEN
    `¬(b ∈ supp pm x)` by METIS_TAC [] THEN
    `b ∈ supp pm (pmact pm [(a,b)] x)` by SRW_TAC [][perm_supp] THEN
    METIS_TAC []
  ]);

val supp_FINITE_strings = store_thm(
  "supp_FINITE_strings",
  ``FINITE s ⇒ (supp (set_pmact string_pmact) s = s)``,
  SRW_TAC [][supp_setpm, EXTENSION] THEN EQ_TAC THEN
  STRIP_TAC THENL [
    METIS_TAC [],
    Q.EXISTS_TAC `{x}` THEN SRW_TAC [][] THEN METIS_TAC []
  ]);
val _ = export_rewrites ["supp_FINITE_strings"]

val rwt = prove(
  ``(!x. ~P x \/ Q x) = (!x. P x ==> Q x)``,
  METIS_TAC []);

Theorem fmap_supp:
    (∀d. FINITE (supp dpm d)) ∧ (∀r. FINITE (supp rpm r)) ==>
    (supp (fm_pmact dpm rpm) fmap =
        supp (set_pmact dpm) (FDOM fmap) ∪
        supp (set_pmact rpm) (FRANGE fmap))
Proof
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][FINITE_FRANGE, supp_setpm, rwt,
             GSYM RIGHT_FORALL_IMP_THM]
  THENL [
    SRW_TAC [][support_def, fmap_EXT, rwt, GSYM RIGHT_FORALL_IMP_THM,
               fmpm_FDOM]
    THENL [
      SRW_TAC [][EXTENSION, fmpm_FDOM] THEN
      Cases_on `x ∈ supp dpm x'` THEN1
        (`y ∈ supp dpm (pmact dpm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
         METIS_TAC []) THEN
      Cases_on `y ∈ supp dpm x'` THEN1
        (`x ∈ supp dpm (pmact dpm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
         METIS_TAC []) THEN
      METIS_TAC [supp_fresh],
      SRW_TAC [][fmpm_def, FAPPLY_f_o, lemma, FDOM_f_o, o_f_FAPPLY] THEN
      `¬(x ∈ supp dpm (pmact dpm [(x,y)] x')) ∧ ¬(y ∈ supp dpm (pmact dpm [(x,y)] x'))`
          by METIS_TAC [] THEN
      NTAC 2 (POP_ASSUM MP_TAC) THEN
      SRW_TAC [][perm_supp] THEN
      SRW_TAC [][supp_fresh] THEN
      `x' ∈ FDOM fmap` by METIS_TAC [supp_fresh] THEN
      `fmap ' x' ∈ FRANGE fmap`
         by (SRW_TAC [][FRANGE_DEF] THEN METIS_TAC []) THEN
      METIS_TAC [supp_fresh]
    ],

    SRW_TAC [][],
    SRW_TAC [][],

    rename [‘fmpm _ _ [(a,b)] fmap = fmap’, ‘a ∈ supp dpm x’] >>
    `b ∉ supp dpm x` by METIS_TAC [] THEN
    SRW_TAC [][fmap_EXT, fmpm_FDOM] THEN
    fs[EXTENSION, fmpm_FDOM] THEN
    `b ∈ supp dpm (pmact dpm [(a,b)] x)` by SRW_TAC [][perm_supp] THEN
    METIS_TAC [],

    rename [‘fmpm dpm rpm [(a,b)] fmap = fmap’, ‘a ∈ supp rpm x’] >>
    `b ∉ supp rpm x` by METIS_TAC [] THEN
    `∃y. y ∈ FDOM fmap ∧ (fmap ' y = x)`
        by (FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF] THEN METIS_TAC []) THEN
    `b ∉ supp dpm y` by METIS_TAC [] THEN
    Cases_on `a ∈ supp dpm y` THENL [
      `b ∈ supp dpm (pmact dpm [(a,b)] y)` by SRW_TAC [][perm_supp] THEN
      SRW_TAC [][fmap_EXT, fmpm_FDOM, EXTENSION] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN
    SRW_TAC [][fmap_EXT, fmpm_FDOM] THEN Q.EXISTS_TAC `y` THEN
    SRW_TAC [][supp_fresh, fmpm_def, FAPPLY_f_o, o_f_FAPPLY, lemma,
               FDOM_f_o] THEN
    METIS_TAC [supp_apart]
  ]
QED

val FAPPLY_eqv_lswapstr = store_thm(
  "FAPPLY_eqv_lswapstr",
  ``d ∈ FDOM fm ⇒ (pmact rpm pi (fm ' d) = fmpm string_pmact rpm pi fm ' (lswapstr pi d))``,
  srw_tac [][fmpm_def] >>
  qmatch_abbrev_tac `z = (f o_f g) ' x` >>
  `FDOM g = { x | lswapstr pi⁻¹ x ∈ FDOM fm }`
    by simp[FINITE_PRED_11, FDOM_f_o, Abbr`g`] >>
  simp[Abbr`g`, FAPPLY_f_o, FINITE_PRED_11, Abbr`x`]);

val fmpm_FEMPTY = store_thm(
  "fmpm_FEMPTY",
  ``fmpm dpm rpm pi FEMPTY = FEMPTY``,
  SRW_TAC [][fmap_EXT, fmpm_applied, fmpm_FDOM, EXTENSION]);
val _ = export_rewrites ["fmpm_FEMPTY"]

val fmpm_FUPDATE = store_thm(
  "fmpm_FUPDATE",
  ``fmpm dpm rpm pi (fm |+ (k,v)) =
    fmpm dpm rpm pi fm |+ (pmact dpm pi k, pmact rpm pi v)``,
  SRW_TAC [][fmap_EXT, fmpm_applied, fmpm_FDOM, EXTENSION]
  THENL [
    SRW_TAC [][pmact_eql],
    SRW_TAC [][pmact_inverse],
    Cases_on `k = pmact dpm (REVERSE pi) x` THENL [
      SRW_TAC [][pmact_inverse],
      SRW_TAC [][FAPPLY_FUPDATE_THM, fmpm_applied] THEN
      METIS_TAC [pmact_inverse]
    ]
  ]);
val _ = export_rewrites ["fmpm_FUPDATE"]

val fmpm_DOMSUB = store_thm(
  "fmpm_DOMSUB",
  ``fmpm dpm rpm pi (fm \\ k) = fmpm dpm rpm pi fm \\ (pmact dpm pi k)``,
  SRW_TAC [][fmap_EXT,fmpm_FDOM,EXTENSION] THEN1
    METIS_TAC [pmact_eql] THEN
  SRW_TAC [][fmpm_applied,DOMSUB_FAPPLY_THM] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][pmact_inverse] )
val _ = export_rewrites ["fmpm_DOMSUB"];

val fcond_def = Define`
  fcond pm f ⇔
     FINITE (supp (fn_pmact string_pmact pm) f) ∧
     (∃a. a ∉ supp (fn_pmact string_pmact pm) f /\ a ∉ supp pm (f a))
`;

Theorem fcond_equivariant[simp] :
    fcond pm (fnpm string_pmact pm pi f) = fcond pm f
Proof
  SIMP_TAC (srw_ss() ++ CONJ_ss) [fcond_def, EQ_IMP_THM, perm_supp, fnpm_def,
                                  pmact_IN, pmact_FINITE] THEN
  METIS_TAC [pmact_inverse]
QED

val fresh_def = Define`
  fresh apm f = let z = NEW (supp (fn_pmact string_pmact apm) f)
                in
                  f z
`;

val fresh_thm = store_thm(
  "fresh_thm",
  ``fcond apm f ==>
    ∀a. a ∉ supp (fn_pmact string_pmact apm) f ⇒ (f a = fresh apm f)``,
  SIMP_TAC (srw_ss()) [fcond_def, fresh_def] THEN STRIP_TAC THEN
  Q.X_GEN_TAC `b` THEN
  SRW_TAC [][fcond_def, fresh_def] THEN
  Q.UNABBREV_TAC `z` THEN
  NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `!c. ~(c IN supp (fn_pmact string_pmact apm) f) ==> (f c = f a)`
        THEN1 SRW_TAC [][] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `c = a` THEN1 SRW_TAC [][] THEN
  `~(c IN supp string_pmact a)` by SRW_TAC [][] THEN
  `~(c IN supp apm (f a))`
      by (`supp apm (f a) SUBSET
             supp (fn_pmact string_pmact apm) f UNION supp string_pmact a`
            by SRW_TAC [][supp_fnapp] THEN
          FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC []) THEN
  `pmact apm [(a,c)] (f a) = f a` by METIS_TAC [supp_supports, support_def] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  `pmact apm [(a,c)] (f a) = fnpm string_pmact apm [(a,c)] f (lswapstr [(a,c)] a)`
     by SRW_TAC [][fnpm_def] THEN
  SRW_TAC [][supp_fresh])

val fresh_equivariant = store_thm(
  "fresh_equivariant",
  ``fcond pm f ==>
    (pmact pm pi (fresh pm f) = fresh pm (fnpm string_pmact pm pi f))``,
  STRIP_TAC THEN
  `fcond pm (fnpm string_pmact pm pi f)` by SRW_TAC [][fcond_equivariant] THEN
  `∃b. b ∉ supp (fn_pmact string_pmact pm) (fnpm string_pmact pm pi f)`
     by (Q.SPEC_THEN `supp (fn_pmact string_pmact pm) (fnpm string_pmact pm pi f)`
                     MP_TAC NEW_def THEN METIS_TAC [fcond_def]) THEN
  `stringpm pi⁻¹ b ∉ supp (fn_pmact string_pmact pm) f`
     by (POP_ASSUM MP_TAC THEN SRW_TAC [][perm_supp, pmact_IN]) THEN
  `fresh pm (fnpm string_pmact pm pi f) = fnpm string_pmact pm pi f b`
     by METIS_TAC [fresh_thm] THEN
  SRW_TAC [][fnpm_def, pmact_injective, GSYM fresh_thm]);

(*
   given a finite set of atoms and some other set to avoid, we can
   exhibit a pi that maps the original set away from the avoid set, and
   doesn't itself contain any atoms apart from those present in the
   original set and its image.
*)
val gen_avoidance_lemma = store_thm(
  "gen_avoidance_lemma",
  ``FINITE atoms ∧ FINITE s  ⇒
    ∃π. (∀a. a ∈ atoms ⇒ lswapstr π a ∉ s) ∧
        ∀x y. MEM (x,y) π ⇒ x ∈ atoms ∧ y ∈ ssetpm π atoms``,
  Q_TAC SUFF_TAC
    `FINITE s ⇒
     ∀limit. FINITE limit ⇒
        ∀atoms. FINITE atoms ⇒
                atoms ⊆ limit ⇒
                ∃π. (∀a. a ∈ atoms ⇒ lswapstr π a ∉ s ∧ lswapstr π a ∉ limit) ∧
                    ∀x y. MEM (x,y) π ⇒ x ∈ atoms ∧ y ∈ ssetpm π atoms`
    THEN1 METIS_TAC [SUBSET_REFL] THEN
  NTAC 3 STRIP_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN1
    (Q.EXISTS_TAC `[]` THEN SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss () ++ DNF_ss) [] THEN
  `lswapstr π e = e`
    by (MATCH_MP_TAC lswapstr_unchanged THEN
        DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [IN_patoms_MEM]) THEN1
          METIS_TAC [] THEN
        `lswapstr π⁻¹ e ∈ atoms` by METIS_TAC [] THEN
        `lswapstr π (lswapstr π⁻¹ e) ∉ limit` by METIS_TAC [] THEN
        FULL_SIMP_TAC (srw_ss()) []) THEN

  Q_TAC (NEW_TAC "e'") `s ∪ patoms π ∪ limit ∪ {e}` THEN
  `∀a. a ∈ atoms ⇒ lswapstr π a ≠ e` by METIS_TAC [] THEN
  `∀a. a ∈ atoms ⇒ lswapstr π a ≠ e'`
      by (REPEAT STRIP_TAC THEN
          `lswapstr π⁻¹ e' = a` by SRW_TAC [][pmact_eql] THEN
          METIS_TAC [lswapstr_unchanged, listsupp_REVERSE, SUBSET_DEF]) THEN
  Q.EXISTS_TAC `(e,e')::π` THEN SRW_TAC [][] THENL [
    METIS_TAC [],

    SRW_TAC [][pmact_decompose] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM) THEN SRW_TAC [][],

    FULL_SIMP_TAC (srw_ss()) [pmact_decompose] THEN
    `y ∈ patoms π` by METIS_TAC [IN_patoms_MEM] THEN
    `y ≠ e'` by METIS_TAC [] THEN
    Cases_on `y = e` THENL [
      SRW_TAC [][swapstr_def] THEN
      `lswapstr π⁻¹ e ∈ atoms` by METIS_TAC [] THEN
      POP_ASSUM MP_TAC THEN
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
      SRW_TAC [][],
      SRW_TAC [][] THEN METIS_TAC []
    ]
  ]);

Theorem lswapstr_IN_RANK :
    !x ys zs r. LENGTH ys = LENGTH zs /\
                DISJOINT (set ys) (set zs) /\
                ALL_DISTINCT ys /\ ALL_DISTINCT zs /\
                set ys SUBSET RANK r /\
                set zs SUBSET RANK r /\
                x IN RANK r /\ ~MEM x zs ==>
                lswapstr (ZIP (ys,zs)) x IN RANK r
Proof
    rpt STRIP_TAC
 >> Cases_on ‘MEM x ys’
 >- (Know ‘MEM (lswapstr (ZIP (ys,zs)) x) zs’
     >- (MATCH_MP_TAC MEM_lswapstr >> art []) \\
     METIS_TAC [SUBSET_DEF])
 >> Suff ‘lswapstr (ZIP (ys,zs)) x = x’ >- rw []
 >> MATCH_MP_TAC lswapstr_unchanged
 >> rw [IN_patoms_MEM, MEM_ZIP]
 >> CCONTR_TAC >> gs [EL_MEM]
QED

val _ = export_theory();
val _ = html_theory "nomset";
