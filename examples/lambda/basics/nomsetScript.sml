open HolKernel Parse boolLib bossLib BasicProvers boolSimps

local open stringTheory in end;

open pred_setTheory

open basic_swapTheory NEWLib lcsymtacs

val _ = new_theory "nomset";

fun Store_thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

fun Save_thm(s, t) = (save_thm(s,t) before export_rewrites [s])

(* permutations are represented as lists of pairs of atoms.  These
   can be lifted to bijections on atoms that only move finitely many
   atoms with the perm_of function *)

val _ = overload_on ("perm_of", ``lswap``);
val _ = overload_on ("lswap", ``lswap``);

val perm_of_decompose = lswap_APPEND
val perm_of_swap = store_thm(
  "perm_of_swap",
  ``perm_of p (swap x y s) =
    swap (perm_of p x) (perm_of p y) (perm_of p s)``,
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

val permeq_refl = Store_thm("permeq_refl", ``x == x``, SRW_TAC [][permeq_def]);

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
  ASM_SIMP_TAC (srw_ss()) [lswap_APPEND, permeq_def, FUN_EQ_THM]);

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
  SRW_TAC [][] THEN ONCE_REWRITE_TAC [lswap_APPEND] THEN SRW_TAC [][]);

val permof_inverse = store_thm(
  "permof_inverse",
 ``(p ++ REVERSE p == []) /\ (REVERSE p ++ p == [])``,
  METIS_TAC [permof_inverse_lemma, listTheory.REVERSE_REVERSE]);

val permof_inverse_append = store_thm (
  "permof_inverse_append",
  ``(p ++ q) ++ REVERSE q == p ∧ (p ++ REVERSE q) ++ q == p``,
  SIMP_TAC bool_ss [GSYM listTheory.APPEND_ASSOC] THEN
  CONJ_TAC THEN
  SIMP_TAC bool_ss [Once (GSYM listTheory.APPEND_NIL), SimpR ``(==)``] THEN
  MATCH_MP_TAC app_permeq_monotone THEN SRW_TAC [][permof_inverse]);

val permof_inverse_applied = lswap_inverse

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

val permof_sorts_differ = store_thm(
  "permof_sorts_differ",
  ``~(atom_sort x = atom_sort y) ==> (x,y) :: t == t``,
  SRW_TAC [][permeq_def,FUN_EQ_THM])

val permof_REVERSE_monotone = store_thm(
  "permof_REVERSE_monotone",
  ``(x == y) ==> (REVERSE x == REVERSE y)``,
  STRIP_TAC THEN
  `REVERSE x ++ x == REVERSE x ++ y`
    by METIS_TAC [app_permeq_monotone, permeq_refl] THEN
  `REVERSE x ++ y == []`
    by METIS_TAC [permof_inverse, permeq_trans, permeq_sym] THEN
  `REVERSE x ++ (y ++ REVERSE y) == REVERSE y`
    by METIS_TAC [listTheory.APPEND, listTheory.APPEND_ASSOC,
                  app_permeq_monotone, permeq_refl] THEN
  METIS_TAC [permof_inverse, listTheory.APPEND_NIL,
             app_permeq_monotone, permeq_refl, permeq_trans, permeq_sym]);

val permeq_cons_monotone = store_thm(
  "permeq_cons_monotone",
  ``(p1 == p2) ==> (h::p1 == h::p2)``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val permeq_swap_ends = store_thm(
  "permeq_swap_ends",
  ``!p x y. p ++ [(x,y)] == (perm_of p x, perm_of p y)::p``,
  Induct THEN SRW_TAC [][permeq_refl] THEN
  Q_TAC SUFF_TAC `h::(perm_of p x, perm_of p y)::p ==
                  (swap (FST h) (SND h) (perm_of p x),
                   swap (FST h) (SND h) (perm_of p y))::h::p`
        THEN1 METIS_TAC [permeq_trans, permeq_cons_monotone] THEN
  SRW_TAC [][FUN_EQ_THM, permeq_def]);

val app_permeq_left_cancel = store_thm(
  "app_permeq_left_cancel",
  ``!p1 p1' p2 p2'. p1 == p1' /\ p1 ++ p2 == p1' ++ p2' ==> p2 == p2'``,
  REPEAT STRIP_TAC THEN
  `REVERSE p1 == REVERSE p1'` by METIS_TAC [permof_REVERSE_monotone] THEN
  `(REVERSE p1) ++ p1 ++ p2 == (REVERSE p1') ++ p1' ++ p2'`
    by (METIS_TAC [app_permeq_monotone, listTheory.APPEND_ASSOC]) THEN
  `[] ++ p2 == (REVERSE p1) ++ p1 ++ p2 /\
   [] ++ p2' == (REVERSE p1') ++ p1' ++ p2'`
    by (METIS_TAC [app_permeq_monotone, permeq_refl, permeq_sym, permof_inverse]) THEN
  METIS_TAC [listTheory.APPEND, permeq_refl, permeq_sym, permeq_trans]);

val app_permeq_right_cancel = store_thm(
  "app_permeq_right_cancel",
  ``!p1 p1' p2 p2'. p1 == p1' /\ p2 ++ p1 == p2' ++ p1' ==> p2 == p2'``,
  REPEAT STRIP_TAC THEN
  `REVERSE p1 == REVERSE p1'` by METIS_TAC [permof_REVERSE_monotone] THEN
  `p2 ++ (p1 ++ (REVERSE p1)) == p2' ++ (p1' ++ (REVERSE p1'))`
    by (METIS_TAC [app_permeq_monotone, listTheory.APPEND_ASSOC]) THEN
  `p2 ++ [] == p2 ++ (p1 ++ (REVERSE p1)) /\
   p2' ++ [] == p2' ++ (p1' ++ (REVERSE p1'))`
    by (METIS_TAC [app_permeq_monotone, permeq_refl, permeq_sym, permof_inverse]) THEN
  METIS_TAC [listTheory.APPEND_NIL, permeq_refl, permeq_trans, permeq_sym]);

(* ----------------------------------------------------------------------
    Define what it is to be a permutation action on a type
   ---------------------------------------------------------------------- *)

val _ = type_abbrev("pm",``:(atom # atom) list``);

val _ = add_rule {fixity = Suffix 2100,
                  term_name = "⁻¹",
                  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⁻¹"]}
val _ = overload_on ("⁻¹", ``REVERSE : pm -> pm``)
val _ = TeX_notation {hol="⁻¹", TeX= ("\\ensuremath{\\sp{-1}}", 1)}

val is_pmact_def = Define`
  is_pmact (f:pm -> 'a -> 'a) =
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

val is_pmact_pmact = Store_thm(
"is_pmact_pmact",
``!pm. is_pmact (pmact pm)``,
METIS_TAC [pmact_onto]);

val pmact_nil = Store_thm(
  "pmact_nil",
  ``!pm x. (pmact pm [] x = x)``,
  MP_TAC is_pmact_pmact THEN
  simp_tac std_ss [is_pmact_def])

val pmact_permeq = Store_thm(
  "pmact_permeq",
  ``p1 == p2 ==> (pmact pm p1 = pmact pm p2)``,
  METIS_TAC [is_pmact_pmact,is_pmact_def]);

val pmact_decompose = store_thm(
  "pmact_decompose",
  ``!pm x y a. pmact pm (x ++ y) a = pmact pm x (pmact pm y a)``,
  MP_TAC is_pmact_pmact THEN
  simp_tac std_ss [is_pmact_def]);

val pmact_dups = Store_thm(
  "pmact_dups",
  ``!f h t a. pmact f (h::h::t) a = pmact f t a``,
  MP_TAC is_pmact_pmact THEN
  SRW_TAC [][is_pmact_def] THEN
  Q_TAC SUFF_TAC `h::h::t == t` THEN1 METIS_TAC [pmact_permeq] THEN
  SRW_TAC [][permof_dups]);

val pmact_id = Store_thm(
  "pmact_id",
  ``!f x a t. pmact f ((x,x)::t) a = pmact f t a``,
  MP_TAC is_pmact_pmact THEN
  rpt strip_tac >>
  Q_TAC SUFF_TAC `((x,x)::t) == t`
        THEN1 METIS_TAC [is_pmact_def] THEN
  SRW_TAC [][permof_idfront]);

val pmact_sorts_differ = Store_thm(
  "pmact_sorts_differ",
  ``!f x y t a. ~(atom_sort x = atom_sort y) ==> (pmact f ((x,y)::t) a = pmact f t a)``,
  MP_TAC is_pmact_pmact THEN
  rpt strip_tac THEN
  Q_TAC SUFF_TAC `((x,y)::t) == t`
        THEN1 METIS_TAC [is_pmact_def] THEN
  SRW_TAC [][permof_sorts_differ])

val pmact_inverse = Store_thm(
  "pmact_inverse",
  ``(pmact f p (pmact f p⁻¹ a) = a) /\
    (pmact f p⁻¹ (pmact f p a) = a)``,
  MP_TAC is_pmact_pmact THEN
  METIS_TAC [is_pmact_def, permof_inverse])

val pmact_sing_inv = Store_thm(
  "pmact_sing_inv",
  ``pmact pm [h] (pmact pm [h] x) = x``,
  METIS_TAC [listTheory.REVERSE_DEF, listTheory.APPEND, pmact_inverse]);

val pmact_eql = store_thm(
  "pmact_eql",
  ``(pmact pm p x = y) = (x = pmact pm p⁻¹ y)``,
  MP_TAC is_pmact_pmact THEN
  SRW_TAC [][is_pmact_def, EQ_IMP_THM] THEN
  SRW_TAC [][pmact_decompose]);

val pmact_injective = store_thm(
  "pmact_injective",
  ``(pmact pm p x = pmact pm p y) = (x = y)``,
  METIS_TAC [pmact_inverse]);

val permeq_flip_args = store_thm(
  "permeq_flip_args",
  ``(x,y)::t == (y,x)::t``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val pmact_flip_args = store_thm(
  "pmact_flip_args",
  ``pmact pm ((x,y)::t) a = pmact pm ((y,x)::t) a``,
  METIS_TAC [is_pmact_pmact, is_pmact_def, permeq_flip_args]);

val pmact_sing_to_back = store_thm(
  "pmact_sing_to_back",
  ``pmact pm [(lswap pi a, lswap pi b)] (pmact pm pi v) = pmact pm pi (pmact pm [(a,b)] v)``,
  SRW_TAC [][GSYM pmact_decompose] THEN
  Q_TAC SUFF_TAC `(lswap pi a,lswap pi b)::pi == pi ++ [(a,b)]`
        THEN1 METIS_TAC [is_pmact_def,is_pmact_pmact] THEN
  METIS_TAC [permeq_swap_ends, permeq_sym]);

(* ----------------------------------------------------------------------
   define (possibly parameterised) permutation actions on standard
   builtin types: functions, sets, lists, pairs, etc
  ----------------------------------------------------------------------  *)

(* two simple permutation actions: atoms, and "everything else" *)
val perm_of_is_pmact = Store_thm(
  "perm_of_is_pmact",
  ``is_pmact perm_of``,
  SRW_TAC [][is_pmact_def, lswap_APPEND, permeq_def]);

val _ = overload_on("atom_pmact", ``mk_pmact perm_of``);
val _ = overload_on("atompm",``pmact atom_pmact``);

val atompm_raw = store_thm(
"atompm_raw",
``atompm = perm_of``,
srw_tac [][GSYM pmact_bijections]);

val atompm_thm = Save_thm(
"atompm_thm",
SUBS [GSYM atompm_raw] lswap_def);

val discrete_is_pmact = Store_thm(
  "discrete_is_pmact",
  ``is_pmact (K I)``,
  SRW_TAC [][is_pmact_def]);

val _ = overload_on("discrete_pmact",``(mk_pmact (K I))``);
val _ = overload_on("discretepm",``pmact discrete_pmact``);

val discretepm_raw = store_thm(
"discretepm_raw",
``discretepm = K I``,
srw_tac [][GSYM pmact_bijections]);

val discretepm_thm = Store_thm(
"discretepm_thm",
``discretepm pi x = x``,
srw_tac [][discretepm_raw]);

val atompm_sort = Store_thm(
"atompm_sort",
``!pi a. atom_sort (atompm pi a) = atom_sort a``,
Induct >> srw_tac [][atompm_thm,swap_def] THEN METIS_TAC [])

val lswap_sort = Save_thm(
"lswap_sort",
atompm_sort |> SUBS [atompm_raw]);

val swap_sort = Store_thm(
"swap_sort",
``atom_sort (swap x y s) = atom_sort s``,
srw_tac [][swap_def] >> srw_tac [][])

(* functions *)
val raw_fnpm_def = Define`
  raw_fnpm (dpm: α pmact) (rpm: β pmact) p f x = pmact rpm p (f (pmact dpm  p⁻¹ x))
`;
val _ = export_rewrites["raw_fnpm_def"];

val _ = overload_on ("fn_pmact", ``λdpm rpm. mk_pmact (raw_fnpm dpm rpm)``);
val _ = overload_on ("fnpm", ``λdpm rpm. pmact (fn_pmact dpm rpm)``);

val fnpm_raw = store_thm(
"fnpm_raw",
``fnpm dpm rpm = raw_fnpm dpm rpm``,
srw_tac [][GSYM pmact_bijections] >>
SRW_TAC [][is_pmact_def, FUN_EQ_THM, listTheory.REVERSE_APPEND, pmact_decompose] THEN
METIS_TAC [permof_REVERSE_monotone,pmact_permeq]);

val fnpm_def = save_thm(
"fnpm_def",
foldr (uncurry Q.GEN) (SUBS [GSYM fnpm_raw] (SPEC_ALL raw_fnpm_def))
[`dpm`,`rpm`,`p`,`f`,`x`])

(* sets *)
val _ = overload_on ("set_pmact", ``λpm. mk_pmact (fnpm pm discrete_pmact) : α set pmact``);
val _ = overload_on ("setpm", ``λpm. pmact (set_pmact pm)``);

val pmact_IN = Store_thm(
  "pmact_IN",
  ``(x IN (setpm pm π s) = pmact pm π⁻¹ x IN s)``,
  SRW_TAC [][fnpm_raw, SPECIFICATION] THEN
  let open combinTheory in
    METIS_TAC [pmact_bijections, K_THM, I_THM, discrete_is_pmact]
  end);

val pmact_UNIV = Store_thm(
  "pmact_UNIV",
  ``setpm pm π UNIV = UNIV``,
  SRW_TAC [][EXTENSION, SPECIFICATION, fnpm_def] THEN
  SRW_TAC [][UNIV_DEF]);

val pmact_EMPTY = Store_thm(
  "pmact_EMPTY",
  ``setpm pm π {} = {}``,
  SRW_TAC [][EXTENSION, SPECIFICATION, fnpm_def] THEN
  SRW_TAC [][EMPTY_DEF]);

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

val pmact_FINITE = Store_thm(
  "pmact_FINITE",
  ``FINITE (setpm pm p s) = FINITE s``,
  Q_TAC SUFF_TAC `(!s. FINITE s ==> FINITE (setpm pm p s)) /\
                  (!s. FINITE s ==> !t p. (setpm pm p t = s) ==> FINITE t)`
        THEN1 METIS_TAC [] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][pmact_INSERT],
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    SRW_TAC [][pmact_eql, pmact_INSERT]
  ]);

(* options *)

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

val optpm_thm = Save_thm(
"optpm_thm",
raw_optpm_def |> CONJUNCTS |> map SPEC_ALL |> map (SUBS [GSYM optpm_raw]) |> LIST_CONJ)

(* pairs *)
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

val pairpm_thm = Save_thm(
"pairpm_thm",
raw_pairpm_def |> SPEC_ALL |> SUBS [GSYM pairpm_raw] |>
(rev_itlist Q.GEN) [`apm`,`bpm`,`pi`,`a`,`b`]);

val FST_pairpm = Store_thm(
  "FST_pairpm",
  ``FST (pairpm pm1 pm2 pi v) = pmact pm1 pi (FST v)``,
  Cases_on `v` THEN SRW_TAC [][]);

val SND_pairpm = Store_thm(
  "SND_pairpm",
  ``SND (pairpm pm1 pm2 pi v) = pmact pm2 pi (SND v)``,
  Cases_on `v` THEN SRW_TAC [][]);

(* sums *)
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

val sumpm_thm = Save_thm(
"sumpm_thm",
raw_sumpm_def |> CONJUNCTS
|> map (fn th => th |> Q.SPECL [`pm1`,`pm2`]
                    |> SUBS [GSYM sumpm_raw]
                    |> (itlist Q.GEN [`pm1`,`pm2`]))
|> LIST_CONJ);

(* lists *)
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

val listpm_thm = Save_thm(
"listpm_thm",
raw_listpm_def |> CONJUNCTS
|> map (fn th => th |> Q.SPEC `apm` |> SUBS [GSYM listpm_raw] |> Q.GEN `apm`)
|> LIST_CONJ)

val listpm_MAP = store_thm(
  "listpm_MAP",
  ``!l. listpm pm pi l = MAP (pmact pm pi) l``,
  Induct THEN fsrw_tac [][]);

val listpm_APPENDlist = store_thm(
  "listpm_APPENDlist",
  ``listpm pm pi (l1 ++ l2) = listpm pm pi l1 ++ listpm pm pi l2``,
  Induct_on `l1` THEN fsrw_tac [][]);

val LENGTH_listpm = Store_thm(
  "LENGTH_listpm",
  ``LENGTH (listpm pm pi l) = LENGTH l``,
  Induct_on `l` >> fsrw_tac [][])

val EL_listpm = Store_thm(
  "EL_listpm",
  ``∀l n. n < LENGTH l ==> (EL n (listpm pm pi l) = pmact pm pi (EL n l))``,
  Induct >> srw_tac [][] >> Cases_on `n` >> srw_tac [][] >>
  fsrw_tac [][]);

val MEM_listpm = store_thm(
  "MEM_listpm",
  ``MEM x (listpm pm pi l) ⇔ MEM (pmact pm pi⁻¹ x) l``,
  Induct_on `l` >> fsrw_tac [][pmact_eql]);

val MEM_listpm_EXISTS = store_thm(
  "MEM_listpm_EXISTS",
  ``MEM x (listpm pm pi l) ⇔ ∃y. MEM y l ∧ (x = pmact pm pi y)``,
  Induct_on `l` >> fsrw_tac [][] >> metis_tac []);

(* lists of pairs of strings, (concrete rep for permutations) *)
val _ = overload_on("cpm_pmact", ``list_pmact (pair_pmact atom_pmact atom_pmact)``);
val _ = overload_on ("cpmpm", ``pmact cpm_pmact``);

(* ----------------------------------------------------------------------
    Notion of support, and calculating the smallest set of support
   ---------------------------------------------------------------------- *)

val support_def = Define`
  support (pm : α pmact) (a:α) (supp:atom set) =
     ∀x y. x ∉ supp /\ y ∉ supp ⇒ (pmact pm [(x,y)] a = a)
`;

val pmact_support = store_thm(
  "pmact_support",
  ``(support pm (pmact pm π x) s =
     support pm x (setpm atom_pmact π⁻¹ s))``,
  ASM_SIMP_TAC (srw_ss()) [EQ_IMP_THM, support_def, pmact_IN] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MAP_EVERY Q.X_GEN_TAC [`a`,`b`] THEN STRIP_TAC THENL [
    `pmact pm [(atompm π a, atompm π b)] (pmact pm π x) = pmact pm π x`
       by METIS_TAC [] THEN
    `pmact pm ([(atompm π a, atompm π b)] ++ π) x = pmact pm π x`
       by METIS_TAC [pmact_decompose] THEN
    `[(atompm π a, atompm π b)] ++ π == π ++ [(a,b)]`
       by METIS_TAC [atompm_raw, permeq_swap_ends, permeq_sym, listTheory.APPEND] THEN
    `pmact pm (π ++ [(a,b)]) x = pmact pm π x`
       by METIS_TAC [pmact_permeq] THEN
    METIS_TAC [pmact_injective, pmact_decompose],
    `pmact pm [(a,b)] (pmact pm π x) = pmact pm ([(a,b)] ++ π) x` by METIS_TAC [pmact_decompose] THEN
    `[(a,b)] ++ π == π ++ [(atompm π⁻¹ a, atompm π⁻¹ b)]`
       by (SRW_TAC [][atompm_raw] THEN
           Q.SPECL_THEN [`π`, `perm_of π⁻¹ a`, `perm_of π⁻¹ b`]
                        (ASSUME_TAC o REWRITE_RULE [permof_inverse_applied])
                        permeq_swap_ends THEN
           METIS_TAC [permeq_sym]) THEN
    `pmact pm [(a,b)] (pmact pm π x) = pmact pm (π ++ [(atompm π⁻¹ a, atompm π⁻¹ b)]) x`
       by METIS_TAC [pmact_permeq] THEN
    ` _ = pmact pm π (pmact pm [(atompm π⁻¹ a, atompm π⁻¹ b)] x)`
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
  Q_TAC (NEW_TAC "z") `(atom_sort x,{x;y} UNION s1 UNION s2)` THEN
  `[(x,y)] == [(x,z); (y,z); (x,z)]`
     by (SRW_TAC [][FUN_EQ_THM, permeq_def] THEN
         CONV_TAC (RAND_CONV
                    (ONCE_REWRITE_CONV [GSYM swap_swap])) THEN
         SIMP_TAC bool_ss [swap_inverse] THEN
         SRW_TAC [][]) THEN
  `pmact pm [(x,y)] e = pmact pm [(x,z); (y,z); (x,z)] e`
     by METIS_TAC [pmact_permeq] THEN
  ` _ = pmact pm [(x,z)] (pmact pm [(y,z)] (pmact pm [(x,z)] e))`
     by METIS_TAC [pmact_decompose, listTheory.APPEND] THEN
  METIS_TAC [IN_INTER]);

val supp_def = Define`
  supp pm x = { (a:atom) | INFINITE { (b:atom) | pmact pm [(a,b)] x ≠ x}}
`;

val supp_supports = store_thm(
  "supp_supports",
  ``support pm x (supp pm x)``,
  ASM_SIMP_TAC (srw_ss()) [support_def, supp_def, pmact_decompose,
                           INFINITE_DEF] THEN
  MAP_EVERY Q.X_GEN_TAC [`a`, `b`] THEN STRIP_TAC THEN
  Q.ABBREV_TAC `aset = {b | ~(pmact pm [(a,b)] x = x)}` THEN
  Q.ABBREV_TAC `bset = {c | ~(pmact pm [(b,c)] x = x)}` THEN
  Cases_on `a = b` THEN1 SRW_TAC [][pmact_id, pmact_nil] THEN
  REVERSE (Cases_on `atom_sort a = atom_sort b`) THEN1 SRW_TAC [][] THEN
  `?c. ~(c IN aset) /\ ~(c IN bset) /\ ~(c = a) /\ ~(c = b) /\ (atom_sort c = atom_sort a)`
      by (Q.SPEC_THEN `{a;b} UNION aset UNION bset` MP_TAC NEW_def THEN
          SRW_TAC [][] THEN METIS_TAC []) THEN
  `(pmact pm [(a,c)] x = x) /\ (pmact pm [(b,c)] x = x)`
      by FULL_SIMP_TAC (srw_ss()) [Abbr`aset`, Abbr`bset`] THEN
  `pmact pm ([(a,c)] ++ [(b,c)] ++ [(a,c)]) x = x`
      by SRW_TAC [][pmact_decompose] THEN
  Q_TAC SUFF_TAC `[(a,c)] ++ [(b,c)] ++ [(a,c)] == [(a,b)]`
        THEN1 METIS_TAC [pmact_permeq] THEN
  SIMP_TAC (srw_ss()) [permeq_def, FUN_EQ_THM] THEN
  ONCE_REWRITE_TAC [GSYM swap_swap] THEN
  `(swap a c b = b) /\ (swap a c c = a)` by SRW_TAC [][swap_def] THEN
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
  ``supp pm (pmact pm p x) = setpm atom_pmact p (supp pm x)``,
  SIMP_TAC (srw_ss()) [EXTENSION, pmact_IN, supp_def, pmact_eql,
                       INFINITE_DEF] THEN
  Q.X_GEN_TAC `a` THEN
  `!e x y. pmact pm (REVERSE p) (pmact pm [(x,y)] e) =
           pmact pm [(atompm (REVERSE p) x, atompm (REVERSE p) y)]
              (pmact pm (REVERSE p) e)`
      by METIS_TAC [atompm_raw, pmact_decompose, pmact_permeq, permeq_swap_ends, listTheory.APPEND] THEN
  SRW_TAC [][pmact_inverse] THEN
  Q.MATCH_ABBREV_TAC `FINITE s1 = FINITE s2` THEN
  `s1 = { b | (\s. ~(x = pmact pm [(atompm (REVERSE p) a, s)] x))
                (atompm (REVERSE p ) b)}`
     by SRW_TAC [][Abbr`s1`] THEN
  ` _ = setpm (mk_pmact atompm) (REVERSE (REVERSE p))
              {b | (\s. ~(x = pmact pm [(atompm (REVERSE p) a, s)] x)) b}`
     by (MATCH_MP_TAC setpm_postcompose THEN SRW_TAC [][]) THEN
  Q.UNABBREV_TAC `s2` THEN SRW_TAC [][]);

val supp_apart = store_thm(
  "supp_apart",
  ``(atom_sort a = atom_sort b) ∧ a ∈ supp pm x ∧ b ∉ supp pm x ⇒ pmact pm [(a,b)] x ≠ x``,
  STRIP_TAC THEN
  `a ≠ b` by METIS_TAC [] THEN
  `b ∈ setpm atom_pmact [(a,b)] (supp pm x)`
     by SRW_TAC[][pmact_IN, swap_def] THEN
  `b ∈ supp pm (pmact pm [(a,b)] x)`
     by metis_tac [perm_supp] THEN
  `supp pm x ≠ supp pm (pmact pm [(a,b)] x)` by METIS_TAC [] THEN
  METIS_TAC []);

(*
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
*)

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
  FULL_SIMP_TAC (srw_ss()) [supp_def, INFINITE_DEF]);

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
  SRW_TAC [][INFINITE_STR_UNIV, GSYM INFINITE_DEF]);

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
    (!a b. (atom_sort a = atom_sort b) /\ a IN s /\ ~(b IN s)
                ==> ~(pmact pm [(a,b)] x = x)) ==>
    (supp pm x = s)``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][SUBSET_DEF] THEN
  Q.MATCH_RENAME_TAC `y IN s2` [] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `?z. ~(z IN s2) /\ ~(z IN s) /\ (atom_sort y = atom_sort z)`
      by (Q.SPEC_THEN `s UNION s2` MP_TAC NEW_def THEN
          SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC [support_def]);

(* some examples of supp *)
val supp_atom = Store_thm(
  "supp_atom",
  ``supp atom_pmact s = {s}``,
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def,swap_def]);

val supp_discrete = Store_thm(
  "supp_discrete",
  ``supp discrete_pmact x = {}``,
  SRW_TAC [][supp_def, INFINITE_DEF]);

(*
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
*)

(* options *)
val supp_optpm = store_thm(
  "supp_optpm",
  ``(supp (opt_pmact pm) NONE = {}) /\
    (supp (opt_pmact pm) (SOME x) = supp pm x)``,
  SRW_TAC [][supp_def, pred_setTheory.INFINITE_DEF]);
val _ = export_rewrites ["supp_optpm"]

(* pairs *)
val supp_pairpm = Store_thm(
  "supp_pairpm",
  ``(supp (pair_pmact pm1 pm2) (x,y) = supp pm1 x UNION supp pm2 y)``,
  SRW_TAC [][supp_def, GSPEC_OR, INFINITE_DEF]);

(* lists *)
val supp_listpm = Store_thm(
  "supp_listpm",
  ``(supp (list_pmact apm) [] = {}) /\
    (supp (list_pmact apm) (h::t) = supp apm h UNION supp (list_pmact apm) t)``,
  SRW_TAC [][supp_def, INFINITE_DEF, GSPEC_OR]);

val listsupp_APPEND = Store_thm(
  "listsupp_APPEND",
  ``supp (list_pmact p) (l1 ++ l2) = supp (list_pmact p) l1 ∪ supp (list_pmact p) l2``,
  Induct_on `l1` THEN SRW_TAC [][AC UNION_ASSOC UNION_COMM]);

val listsupp_REVERSE = Store_thm(
  "listsupp_REVERSE",
  ``supp (list_pmact p) (REVERSE l) = supp (list_pmact p) l``,
  Induct_on `l` THEN SRW_TAC [][UNION_COMM]);

val IN_supp_listpm = store_thm(
  "IN_supp_listpm",
  ``a ∈ supp (list_pmact pm) l ⇔ ∃e. MEM e l ∧ a ∈ supp pm e``,
  Induct_on `l` >> srw_tac [DNF_ss][]);

val NOT_IN_supp_listpm = store_thm(
  "NOT_IN_supp_listpm",
  ``a ∉ supp (list_pmact pm) l ⇔ ∀e. MEM e l ⇒ a ∉ supp pm e``,
  metis_tac [IN_supp_listpm])


(* concrete permutations, which get their own overload for calculating their support *)
val _ = overload_on ("patoms", ``supp (list_pmact (pair_pmact atom_pmact atom_pmact))``)

val FINITE_patoms = Store_thm(
  "FINITE_patoms",
  ``!l. FINITE (patoms l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

val patoms_fresh = Store_thm(
  "patoms_fresh",
  ``!p. x ∉ patoms p ∧ y ∉ patoms p ⇒ (cpmpm [(x,y)] p = p)``,
  METIS_TAC [supp_supports, support_def]);

val perm_of_unchanged = store_thm(
  "perm_of_unchanged",
  ``!p. s ∉ patoms p ⇒ (perm_of p s = s)``,
  Induct THEN SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][swap_def]);

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
  `!p q pi t. pmact pm ((swap x y p, swap x y q)::pi) t =
              pmact pm [(swap x y p, swap x y q)] (pmact pm pi t)`
     by SRW_TAC [][GSYM pmact_decompose] THEN
  REPEAT GEN_TAC THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
  fsrw_tac [][GSYM pmact_decompose] >>
  metis_tac [pmact_decompose,listTheory.APPEND]);

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

val atompm_atompm_cpmpm = save_thm(
  "atompm_atompm_cpmpm",
  (SIMP_RULE std_ss []  o Q.INST [`pm` |-> `atom_pmact`] o
   INST_TYPE [alpha |-> ``:atom``]) pm_pm_cpmpm);

val patoms_cpmpm = store_thm(
  "patoms_cpmpm",
  ``patoms (cpmpm pi1 pi2) = setpm atom_pmact pi1 (patoms pi2)``,
  SRW_TAC [][perm_supp]);

(* support for honest to goodness permutations, not just their
   representations *)
val perm_supp_SUBSET_plistvars = prove(
  ``!p. {s | ~(perm_of p s = s)} SUBSET
        FOLDR (\p a. {FST p; SND p} UNION a) {} p``,
  ASM_SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF] THEN Induct THEN
  SRW_TAC [][] THEN
  Cases_on `x = FST h` THEN SRW_TAC [][] THEN
  Cases_on `x = SND h` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [swap_def, swap_eq_left]);

val FINITE_plistvars = prove(
  ``FINITE (FOLDR (\p a. {FST p; SND p} UNION a) {} p)``,
  Induct_on `p` THEN SRW_TAC [][]);
val lemma = MATCH_MP pred_setTheory.SUBSET_FINITE FINITE_plistvars

val perm_supp_finite = store_thm(
  "perm_supp_finite",
  ``FINITE {s | ~(perm_of p s = s)}``,
  MATCH_MP_TAC lemma THEN SRW_TAC [][perm_supp_SUBSET_plistvars]);

val supp_perm_of = store_thm(
  "supp_perm_of",
  ``supp (fn_pmact atom_pmact atom_pmact) (perm_of p) = { s | ~(perm_of p s = s) }``,
  HO_MATCH_MP_TAC supp_unique THEN
  SRW_TAC [][perm_supp_finite] THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, perm_of_swap],

    SRW_TAC [][pred_setTheory.SUBSET_DEF] THEN
    SPOSE_NOT_THEN ASSUME_TAC THEN
    Q_TAC (NEW_TAC "y") `(atom_sort x, {x; perm_of (REVERSE p) x} UNION s')` THEN
    `!a. fnpm atom_pmact atom_pmact [(x,y)] (perm_of p) a = perm_of p a`
       by METIS_TAC [support_def] THEN
    `p ++ [(x,y)] == [(x,y)] ++ p`
       by (POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [fnpm_def]) THEN
           SRW_TAC [][permeq_def, FUN_EQ_THM, perm_of_decompose,
                      GSYM swap_eq_left]) THEN
    `(x,y) :: p == (perm_of p x, perm_of p y) :: p`
       by METIS_TAC [permeq_swap_ends, permeq_trans, permeq_sym,
                     listTheory.APPEND] THEN
    `(x,y) :: (p ++ REVERSE p) ==
        (perm_of p x, perm_of p y) :: (p ++ REVERSE p)`
       by METIS_TAC [app_permeq_monotone, listTheory.APPEND, permeq_refl] THEN
    `!h. [h] == h :: (p ++ REVERSE p)`
       by METIS_TAC [permeq_cons_monotone, permof_inverse, permeq_sym] THEN
    `[(x,y)] == [(perm_of p x, perm_of p y)]`
       by METIS_TAC [permeq_trans, permeq_sym] THEN
    `perm_of [(x,y)] x = perm_of [(perm_of p x, perm_of p y)] x`
       by METIS_TAC [permeq_def] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC (srw_ss()) [] THEN
    `~(x = perm_of p y)` by METIS_TAC [permof_inverse_applied] THEN
    SRW_TAC [][swap_def]
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
  ``FINITE (supp (fn_pmact dpm rpm) f) ∧
    FINITE (supp dpm x) ⇒
  supp rpm (f x) SUBSET supp (fn_pmact dpm rpm) f UNION supp dpm x``,
  METIS_TAC [supp_smallest, FINITE_UNION, supp_supports, support_fnapp]);

val notinsupp_fnapp = store_thm(
  "notinsupp_fnapp",
  ``FINITE (supp (fn_pmact dpm rpm) f) ∧ FINITE (supp dpm x) ∧
    v ∉ supp (fn_pmact dpm rpm) f ∧ v ∉ supp dpm x ==>
    v ∉ supp rpm (f x)``,
  prove_tac [supp_fnapp, SUBSET_DEF, IN_UNION]);

open finite_mapTheory
val raw_fmpm_def = Define`
  raw_fmpm (dpm : 'd pmact) (rpm : 'r pmact) pi fmap =
    pmact rpm pi o_f fmap f_o pmact dpm (REVERSE pi)
`;
val _ = export_rewrites["raw_fmpm_def"];

val _ = overload_on("fm_pmact",``λdpm rpm. mk_pmact (raw_fmpm dpm rpm)``);
val _ = overload_on("fmpm",``λdpm rpm. pmact (fm_pmact dpm rpm)``);

val lemma0 = prove(
  ``(pmact pm pi x ∈ X = x ∈ setpm pm (REVERSE pi) X)``,
  SRW_TAC [][pmact_IN])
val lemma1 = prove(``{x | x ∈ X} = X``, SRW_TAC [][pred_setTheory.EXTENSION])
val lemma = prove(
  ``FINITE { x | pmact pm pi x ∈ FDOM f}``,
  SIMP_TAC bool_ss [lemma0, lemma1, pmact_FINITE,
                    finite_mapTheory.FDOM_FINITE]);

val fmpm_def = store_thm(
  "fmpm_def",
  ``fmpm dpm rpm = raw_fmpm dpm rpm``,
  srw_tac [][GSYM pmact_bijections] >>
  SRW_TAC [][is_pmact_def] THENL [
    `(!d. pmact dpm [] d = d) ∧ (!r. pmact rpm [] r = r)` by METIS_TAC [pmact_nil] THEN
    SRW_TAC [][fmap_EXT, pred_setTheory.EXTENSION, FDOM_f_o, lemma,
               FAPPLY_f_o, o_f_FAPPLY],

    `(!d pi1 pi2. pmact dpm (pi1 ++ pi2) d = pmact dpm pi1 (pmact dpm pi2 d)) ∧
     (!r pi1 pi2. pmact rpm (pi1 ++ pi2) r = pmact rpm pi1 (pmact rpm pi2 r))`
      by METIS_TAC [pmact_decompose] THEN
    SRW_TAC [][fmap_EXT, FDOM_f_o, lemma, o_f_FAPPLY,
               listTheory.REVERSE_APPEND, FAPPLY_f_o],

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

val fmpm_FDOM = store_thm(
  "fmpm_FDOM",
  ``x IN FDOM (fmpm dpm rpm pi fmap) = pmact dpm (REVERSE pi) x IN FDOM fmap``,
  SRW_TAC [][fmpm_def, lemma, FDOM_f_o])

val supp_setpm = store_thm(
  "supp_setpm",
  ``FINITE s ∧ (∀x. x ∈ s ⇒ FINITE (supp pm x)) ⇒
    (supp (set_pmact pm) s = BIGUNION (IMAGE (supp pm) s))``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][] THENL [
    SRW_TAC [][support_def] THEN
    SRW_TAC [][pred_setTheory.EXTENSION] THEN
    REVERSE (Cases_on `atom_sort x = atom_sort y`) THEN1 (
      SRW_TAC [][] ) THEN
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

    SRW_TAC [][pred_setTheory.EXTENSION] THEN
    `∀x. b ∈ supp pm x ==> ¬(x ∈ s)` by METIS_TAC [] THEN
    `¬(b ∈ supp pm x)` by METIS_TAC [] THEN
    `b ∈ supp pm (pmact pm [(a,b)] x)` by SRW_TAC [][perm_supp] THEN
    METIS_TAC []
  ]);

val supp_FINITE_atoms = store_thm(
  "supp_FINITE_atoms",
  ``FINITE s ⇒ (supp (set_pmact atom_pmact) s = s)``,
  SRW_TAC [][supp_setpm, pred_setTheory.EXTENSION] THEN EQ_TAC THEN
  STRIP_TAC THENL [
    METIS_TAC [],
    Q.EXISTS_TAC `{x}` THEN SRW_TAC [][] THEN METIS_TAC []
  ]);
val _ = export_rewrites ["supp_FINITE_atoms"]

val rwt = prove(
  ``(!x. ~P x \/ Q x) = (!x. P x ==> Q x)``,
  METIS_TAC []);

val fmap_supp = store_thm(
  "fmap_supp",
  ``(∀d. FINITE (supp dpm d)) ∧ (∀r. FINITE (supp rpm r)) ==>
    (supp (fm_pmact dpm rpm) fmap =
        supp (set_pmact dpm) (FDOM fmap) ∪
        supp (set_pmact rpm) (FRANGE fmap))``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][FINITE_FRANGE, supp_setpm, rwt,
             GSYM RIGHT_FORALL_IMP_THM]
  THENL [
    SRW_TAC [][support_def, fmap_EXT, rwt, GSYM RIGHT_FORALL_IMP_THM,
               fmpm_FDOM]
    THENL [
      SRW_TAC [][pred_setTheory.EXTENSION, fmpm_FDOM] THEN
      REVERSE (Cases_on `atom_sort x = atom_sort y`) THEN1 (
        SRW_TAC [][] ) THEN
      Cases_on `x ∈ supp dpm x'` THEN1
        (`y ∈ supp dpm (pmact dpm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
         METIS_TAC []) THEN
      Cases_on `y ∈ supp dpm x'` THEN1
        (`x ∈ supp dpm (pmact dpm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
         METIS_TAC []) THEN
      METIS_TAC [supp_fresh],
      SRW_TAC [][fmpm_def, FAPPLY_f_o, lemma, FDOM_f_o, o_f_FAPPLY] THEN
      REVERSE (Cases_on `atom_sort x = atom_sort y`) THEN1 (
        SRW_TAC [][] ) THEN
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

    `¬(b ∈ supp dpm x)` by METIS_TAC [] THEN
    SRW_TAC [][fmap_EXT, fmpm_FDOM] THEN DISJ1_TAC THEN
    SRW_TAC [][pred_setTheory.EXTENSION, fmpm_FDOM] THEN
    `b ∈ supp dpm (pmact dpm [(a,b)] x)` by SRW_TAC [][perm_supp] THEN
    METIS_TAC [],

    `¬(b ∈ supp rpm x)` by METIS_TAC [] THEN
    `∃y. y ∈ FDOM fmap ∧ (fmap ' y = x)`
        by (FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF] THEN METIS_TAC []) THEN
    `¬(b ∈ supp dpm y)` by METIS_TAC [] THEN
    Cases_on `a ∈ supp dpm y` THENL [
      `b ∈ supp dpm (pmact dpm [(a,b)] y)` by SRW_TAC [][perm_supp] THEN
      SRW_TAC [][fmap_EXT, fmpm_FDOM, pred_setTheory.EXTENSION] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN
    SRW_TAC [][fmap_EXT, fmpm_FDOM] THEN DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN
    SRW_TAC [][supp_fresh, fmpm_def, FAPPLY_f_o, o_f_FAPPLY, lemma,
               FDOM_f_o] THEN
    METIS_TAC [supp_apart]
  ]);

val FAPPLY_eqv_lswap = store_thm(
  "FAPPLY_eqv_lswap",
  ``d ∈ FDOM fm ⇒ (pmact rpm pi (fm ' d) = fmpm atom_pmact rpm pi fm ' (lswap pi d))``,
  srw_tac [][fmpm_def] >>
  qmatch_abbrev_tac `z = (f f_o g) ' x` >>
  `FINITE {x | g x ∈ FDOM f}` by metis_tac [lemma] >>
  `FDOM (f f_o g) = {x | g x ∈ FDOM f}` by metis_tac [FDOM_f_o] >>
  `x ∈ FDOM (f f_o g)` by ( unabbrev_all_tac >> srw_tac [][atompm_raw] ) >>
  unabbrev_all_tac >>
  srw_tac [][FAPPLY_f_o, atompm_raw]);

val fmpm_FEMPTY = store_thm(
  "fmpm_FEMPTY",
  ``fmpm dpm rpm pi FEMPTY = FEMPTY``,
  SRW_TAC [][fmap_EXT, fmpm_applied, fmpm_FDOM, pred_setTheory.EXTENSION]);
val _ = export_rewrites ["fmpm_FEMPTY"]

val fmpm_FUPDATE = store_thm(
  "fmpm_FUPDATE",
  ``fmpm dpm rpm pi (fm |+ (k,v)) =
    fmpm dpm rpm pi fm |+ (pmact dpm pi k, pmact rpm pi v)``,
  SRW_TAC [][fmap_EXT, fmpm_applied, fmpm_FDOM, pred_setTheory.EXTENSION]
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
  fcond pm s f = FINITE (supp (fn_pmact atom_pmact pm) f) ∧
                 (∃a. a ∉ supp (fn_pmact atom_pmact pm) f /\ a ∉ supp pm (f a) /\ (atom_sort a = s))
`;

val fcond_equivariant = Store_thm(
  "fcond_equivariant",
  ``fcond pm s (fnpm atom_pmact pm pi f) = fcond pm s f``,
  SIMP_TAC (srw_ss() ++ CONJ_ss) [fcond_def, EQ_IMP_THM, perm_supp, fnpm_def,
                                  pmact_IN, pmact_FINITE] THEN
  METIS_TAC [pmact_inverse, atompm_sort]);

val fresh_def = Define`fresh apm s f = let z = NEW (supp (fn_pmact atom_pmact apm) f) s
                                     in
                                       f z`

val fresh_thm = store_thm(
  "fresh_thm",
  ``!a. fcond apm (atom_sort a) f /\
    a ∉ supp (fn_pmact atom_pmact apm) f ⇒ (f a = fresh apm (atom_sort a) f)``,
  SIMP_TAC (srw_ss()) [fcond_def, fresh_def] THEN
  Q.X_GEN_TAC `b` THEN
  SRW_TAC [][fcond_def, fresh_def] THEN
  qmatch_assum_rename_tac `a NOTIN supp apm (f a)` [] THEN
  Q.UNABBREV_TAC `z` THEN
  NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `!c. ~(c IN supp (fn_pmact atom_pmact apm) f) /\ (atom_sort c = atom_sort a) ==> (f c = f a)`
        THEN1 SRW_TAC [][] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `c = a` THEN1 SRW_TAC [][] THEN
  `~(c IN supp atom_pmact a)` by SRW_TAC [][] THEN
  `~(c IN supp apm (f a))`
      by (`supp apm (f a) SUBSET
             supp (fn_pmact atom_pmact apm) f UNION supp atom_pmact a`
            by SRW_TAC [][supp_fnapp] THEN
          FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC []) THEN
  `pmact apm [(a,c)] (f a) = f a` by METIS_TAC [supp_supports, support_def] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  `pmact apm [(a,c)] (f a) = fnpm atom_pmact apm [(a,c)] f (lswap [(a,c)] a)`
     by SRW_TAC [][fnpm_def] THEN
  SRW_TAC [][supp_fresh])

val fresh_equivariant = store_thm(
  "fresh_equivariant",
  ``fcond pm s f ==>
    (pmact pm pi (fresh pm s f) = fresh pm s (fnpm atom_pmact pm pi f))``,
  STRIP_TAC THEN
  `fcond pm s (fnpm atom_pmact pm pi f)` by SRW_TAC [][fcond_equivariant] THEN
  `∃b. b ∉ supp (fn_pmact atom_pmact pm) (fnpm atom_pmact pm pi f) /\ (atom_sort b = s)`
     by (Q.SPEC_THEN `supp (fn_pmact atom_pmact pm) (fnpm atom_pmact pm pi f)`
                     MP_TAC NEW_def THEN METIS_TAC [fcond_def]) THEN
  `atompm pi⁻¹ b ∉ supp (fn_pmact atom_pmact pm) f`
     by (Q.PAT_ASSUM `b NOTIN X` MP_TAC THEN SRW_TAC [][perm_supp, pmact_IN]) THEN
  `fresh pm s (fnpm atom_pmact pm pi f) = fnpm atom_pmact pm pi f b`
     by METIS_TAC [fresh_thm] THEN
  SRW_TAC [][fnpm_def, pmact_injective] THEN
  METIS_TAC [fresh_thm, atompm_sort]);

val _ = overload_on ("aset_pmact",``set_pmact atom_pmact``);
val _ = overload_on ("asetpm", ``pmact aset_pmact``)

val cpmsupp_avoids = perm_of_unchanged
(*
   given a finite set of atoms and some other set to avoid, we can
   exhibit a pi that maps the original set away from the avoid set, and
   doesn't itself contain any atoms apart from those present in the
   original set and its image.
*)
val gen_avoidance_lemma = store_thm(
  "gen_avoidance_lemma",
  ``FINITE atoms ∧ FINITE s  ⇒
    ∃π. (∀a. a ∈ atoms ⇒ lswap π a ∉ s) ∧
        ∀x y. MEM (x,y) π ⇒ x ∈ atoms ∧ y ∈ asetpm π atoms``,
  Q_TAC SUFF_TAC
    `FINITE s ⇒
     ∀limit. FINITE limit ⇒
        ∀atoms. FINITE atoms ⇒
                atoms ⊆ limit ⇒
                ∃π. (∀a. a ∈ atoms ⇒ lswap π a ∉ s ∧ lswap π a ∉ limit) ∧
                    ∀x y. MEM (x,y) π ⇒ x ∈ atoms ∧ y ∈ asetpm π atoms`
    THEN1 METIS_TAC [SUBSET_REFL] THEN
  NTAC 3 STRIP_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN1
    (Q.EXISTS_TAC `[]` THEN SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss () ++ DNF_ss) [atompm_raw] THEN
  `lswap π e = e`
    by (MATCH_MP_TAC cpmsupp_avoids THEN
        DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [IN_patoms_MEM]) THEN1
          METIS_TAC [] THEN
        `lswap π⁻¹ e ∈ atoms` by METIS_TAC [] THEN
        `lswap π (lswap π⁻¹ e) ∉ limit` by METIS_TAC [] THEN
        FULL_SIMP_TAC (srw_ss()) []) THEN

  Q_TAC (NEW_TAC "e'") `(atom_sort e,s ∪ patoms π ∪ limit ∪ {e})` THEN
  `∀a. a ∈ atoms ⇒ lswap π a ≠ e` by METIS_TAC [] THEN
  `∀a. a ∈ atoms ⇒ lswap π a ≠ e'`
      by (REPEAT STRIP_TAC THEN
          `lswap π⁻¹ e' = a` by SRW_TAC [][lswap_eqr] THEN
          METIS_TAC [cpmsupp_avoids, listsupp_REVERSE, SUBSET_DEF]) THEN
  Q.EXISTS_TAC `(e,e')::π` THEN SRW_TAC [][] THENL [
    METIS_TAC [],

    SRW_TAC [][lswap_APPEND] THEN
    `e = lswap π e` by SRW_TAC [][] THEN
    POP_ASSUM SUBST1_TAC THEN SRW_TAC [][],

    FULL_SIMP_TAC (srw_ss()) [lswap_APPEND] THEN
    `y ∈ patoms π` by METIS_TAC [IN_patoms_MEM] THEN
    `y ≠ e'` by METIS_TAC [] THEN
    Cases_on `y = e` THENL [
      SRW_TAC [][swap_def] THEN
      `lswap π⁻¹ e ∈ atoms` by METIS_TAC [] THEN
      POP_ASSUM MP_TAC THEN
      `e = lswap π e` by SRW_TAC [][] THEN
      POP_ASSUM SUBST1_TAC THEN SRW_TAC [][],
      SRW_TAC [][] THEN METIS_TAC []
    ]
  ]);

val _ = export_theory();
