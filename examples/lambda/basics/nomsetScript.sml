open HolKernel Parse boolLib bossLib BasicProvers boolSimps

local open stringTheory in end;

open pred_setTheory

open basic_swapTheory NEWLib

val _ = new_theory "nomset";

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

(* permutations are represented as lists of pairs of strings.  These
   can be lifted to bijections on strings that only move finitely many
   strings with the perm_of function *)

val _ = overload_on ("perm_of", ``lswapstr``);
val _ = overload_on ("lswapstr", ``lswapstr``);

val perm_of_decompose = lswapstr_APPEND
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

val permeq_refl = store_thm(
  "permeq_refl",
  ``x == x``,
  SRW_TAC [][permeq_def]);

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
  ASM_SIMP_TAC (srw_ss()) [lswapstr_APPEND, permeq_def, FUN_EQ_THM]);

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
  SRW_TAC [][] THEN ONCE_REWRITE_TAC [lswapstr_APPEND] THEN SRW_TAC [][]);

val permof_inverse = store_thm(
  "permof_inverse",
 ``(p ++ REVERSE p == []) /\ (REVERSE p ++ p == [])``,
  METIS_TAC [permof_inverse_lemma, listTheory.REVERSE_REVERSE]);

val permof_inverse_applied = lswapstr_inverse

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
                  (swapstr (FST h) (SND h) (perm_of p x),
                   swapstr (FST h) (SND h) (perm_of p y))::h::p`
        THEN1 METIS_TAC [permeq_trans, permeq_cons_monotone] THEN
  SRW_TAC [][FUN_EQ_THM, permeq_def]);


(* ----------------------------------------------------------------------
    Define what it is to be a permutation action on a type
   ---------------------------------------------------------------------- *)

val is_perm_def = Define`
  is_perm (f:(string # string) list -> 'a -> 'a) =
      (!x. f [] x = x) /\
      (!p1 p2 x. f (p1 ++ p2) x = f p1 (f p2 x)) /\
      (!p1 p2. (p1 == p2) ==> (f p1 = f p2))
`;

val _ = type_abbrev ("pm", ``:(string # string) list -> 'a -> 'a``)

val is_perm_nil = store_thm(
  "is_perm_nil",
  ``is_perm pm ==> (pm [] x = x)``,
  SRW_TAC [][is_perm_def])


val is_perm_decompose = store_thm(
  "is_perm_decompose",
  ``is_perm pm ==> (!a. pm (x ++ y) a = pm x (pm y a))``,
  SRW_TAC [][is_perm_def]);

val is_perm_dups = store_thm(
  "is_perm_dups",
  ``is_perm f ==> !t a. f (h::h::t) a = f t a``,
  SRW_TAC [][is_perm_def] THEN
  Q_TAC SUFF_TAC `h::h::t == t` THEN1 METIS_TAC [is_perm_def] THEN
  SRW_TAC [][permof_dups]);

val is_perm_id = store_thm(
  "is_perm_id",
  ``is_perm f ==> !x a t. f ((x,x)::t) a = f t a``,
  SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `((x,x)::t) == t`
        THEN1 METIS_TAC [is_perm_def] THEN
  SRW_TAC [][permof_idfront]);

val is_perm_inverse = store_thm(
  "is_perm_inverse",
  ``is_perm f ==> (f p (f (REVERSE p) a) = a) /\
                  (f (REVERSE p) (f p a) = a)``,
  METIS_TAC [is_perm_def, permof_inverse])

val is_perm_sing_inv = store_thm(
  "is_perm_sing_inv",
  ``is_perm pm ==> (pm [h] (pm [h] x) = x)``,
  METIS_TAC [listTheory.REVERSE_DEF, listTheory.APPEND, is_perm_inverse]);

val is_perm_eql = store_thm(
  "is_perm_eql",
  ``is_perm pm ==> ((pm p x = y) = (x = pm (REVERSE p) y))``,
  SRW_TAC [][is_perm_def, EQ_IMP_THM] THEN METIS_TAC [permof_inverse]);

val is_perm_injective = store_thm(
  "is_perm_injective",
  ``is_perm pm ==> ((pm p x = pm p y) = (x = y))``,
  METIS_TAC [is_perm_inverse]);

val permeq_flip_args = store_thm(
  "permeq_flip_args",
  ``(x,y)::t == (y,x)::t``,
  SRW_TAC [][permeq_def, FUN_EQ_THM]);

val is_perm_flip_args = store_thm(
  "is_perm_flip_args",
  ``is_perm pm ==> (pm ((x,y)::t) a = pm ((y,x)::t) a)``,
  METIS_TAC [is_perm_def, permeq_flip_args]);

val is_perm_sing_to_back = store_thm(
  "is_perm_sing_to_back",
  ``is_perm pm ==>
    (pm [(lswapstr pi a, lswapstr pi b)] (pm pi v) = pm pi (pm [(a,b)] v))``,
  SRW_TAC [][GSYM is_perm_decompose] THEN
  Q_TAC SUFF_TAC `(lswapstr pi a,lswapstr pi b)::pi == pi ++ [(a,b)]`
        THEN1 METIS_TAC [is_perm_def] THEN
  METIS_TAC [permeq_swap_ends, permeq_sym]);

(* ----------------------------------------------------------------------
   define (possibly parameterised) permutation actions on standard
   builtin types: functions, sets, lists, pairs, etc
  ----------------------------------------------------------------------  *)

(* two simple permutation actions: strings, and "everything else" *)
val perm_of_is_perm = Store_Thm(
  "perm_of_is_perm",
  ``is_perm perm_of``,
  SRW_TAC [][is_perm_def, lswapstr_APPEND, permeq_def]);

val discrete_is_perm = Store_Thm(
  "discrete_is_perm",
  ``is_perm (K I)``,
  SRW_TAC [][is_perm_def]);

(* functions *)
val fnpm_def = Define`
  fnpm (dpm:'a pm) (rpm: 'b pm) p f x = rpm p (f (dpm (REVERSE p) x))
`;

val fnpm_is_perm = Store_Thm(
  "fnpm_is_perm",
  ``is_perm dpm /\ is_perm rpm ==> is_perm (fnpm dpm rpm)``,
  SRW_TAC [][is_perm_def, fnpm_def, FUN_EQ_THM, listTheory.REVERSE_APPEND] THEN
  METIS_TAC [permof_REVERSE_monotone]);

(* sets *)
val setpm_def = Define`
  setpm pm = fnpm pm (K I) : ('a -> bool) pm
`;

val perm_IN = Store_Thm(
  "perm_IN",
  ``is_perm pm ==> (x IN (setpm pm p s) = pm (REVERSE p) x IN s)``,
  SRW_TAC [][fnpm_def, SPECIFICATION, setpm_def]);

val setpm_is_perm = Store_Thm(
  "setpm_is_perm",
  ``is_perm pm ==> is_perm (setpm pm)``,
  SRW_TAC [][setpm_def, discrete_is_perm]);

val perm_UNIV = Store_Thm(
  "perm_UNIV",
  ``setpm pm p UNIV = UNIV``,
  SRW_TAC [][EXTENSION, setpm_def, SPECIFICATION, fnpm_def] THEN
  SRW_TAC [][UNIV_DEF]);

val perm_EMPTY = Store_Thm(
  "perm_EMPTY",
  ``setpm pm p {} = {}``,
  SRW_TAC [][EXTENSION, SPECIFICATION, setpm_def, fnpm_def] THEN
  SRW_TAC [][EMPTY_DEF]);

val perm_INSERT = store_thm(
  "perm_INSERT",
  ``is_perm pm ==> (setpm pm p (e INSERT s) = pm p e INSERT setpm pm p s)``,
  SRW_TAC [][EXTENSION, perm_IN, is_perm_eql]);

val perm_UNION = store_thm(
  "perm_UNION",
  ``is_perm pm ==>
    (setpm pm p (s1 UNION s2) = setpm pm p s1 UNION setpm pm p s2)``,
  SRW_TAC [][EXTENSION, perm_IN]);

val perm_DIFF = store_thm(
  "perm_DIFF",
  ``is_perm pm ==> (setpm pm pi (s DIFF t) =
                    setpm pm pi s DIFF setpm pm pi t)``,
  SRW_TAC [][EXTENSION, perm_IN]);

val perm_DELETE = store_thm(
  "perm_DELETE",
  ``is_perm pm ==> (setpm pm p (s DELETE e) = setpm pm p s DELETE pm p e)``,
  SRW_TAC [][EXTENSION, perm_IN, is_perm_eql]);

val perm_FINITE = Store_Thm(
  "perm_FINITE",
  ``is_perm pm ==> (FINITE (setpm pm p s) = FINITE s)``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC `(!s. FINITE s ==> FINITE (setpm pm p s)) /\
                  (!s. FINITE s ==> !t p. (setpm pm p t = s) ==> FINITE t)`
        THEN1 METIS_TAC [] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][perm_INSERT],
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    SRW_TAC [][is_perm_eql, setpm_is_perm, perm_INSERT]
  ]);

(* options *)
val optpm_def = Define`
  (optpm pm pi NONE = NONE) /\
  (optpm pm pi (SOME x) = SOME (pm pi x))
`;
val _ = export_rewrites ["optpm_def"]

val optpm_is_perm = store_thm(
  "optpm_is_perm",
  ``is_perm pm ==> is_perm (optpm pm)``,
  SRW_TAC [][is_perm_def] THENL [
    Cases_on `x` THEN SRW_TAC [][optpm_def],
    Cases_on `x` THEN SRW_TAC [][optpm_def],
    FULL_SIMP_TAC (srw_ss()) [permeq_def, FUN_EQ_THM] THEN GEN_TAC THEN
    Cases_on `x` THEN SRW_TAC [][optpm_def]
  ]);
val _ = export_rewrites ["optpm_is_perm"]

(* pairs *)
val pairpm_def = Define`
  pairpm (apm:'a pm) (bpm:'b pm) pi (a,b) = (apm pi a, bpm pi b)
`;
val _ = export_rewrites ["pairpm_def"]

val pairpm_is_perm = Store_Thm(
  "pairpm_is_perm",
  ``is_perm pm1 /\ is_perm pm2 ==> is_perm (pairpm pm1 pm2)``,
  SIMP_TAC (srw_ss()) [is_perm_def, pairpm_def, pairTheory.FORALL_PROD,
                       FUN_EQ_THM]);

val FST_pairpm = Store_Thm(
  "FST_pairpm",
  ``FST (pairpm pm1 pm2 pi v) = pm1 pi (FST v)``,
  Cases_on `v` THEN SRW_TAC [][]);

val SND_pairpm = Store_Thm(
  "SND_pairpm",
  ``SND (pairpm pm1 pm2 pi v) = pm2 pi (SND v)``,
  Cases_on `v` THEN SRW_TAC [][]);

(* sums *)
val sumpm_def = Define`
  (sumpm (pm1:'a pm) (pm2:'b pm) pi (INL x) = INL (pm1 pi x)) /\
  (sumpm pm1 pm2 pi (INR y) = INR (pm2 pi y))
`;
val _ = export_rewrites ["sumpm_def"]

val sumpm_is_perm = Store_Thm(
  "sumpm_is_perm",
  ``is_perm pm1 /\ is_perm pm2 ==> is_perm (sumpm pm1 pm2)``,
  SRW_TAC [][is_perm_def, FUN_EQ_THM, permeq_def] THEN Cases_on `x` THEN
  SRW_TAC [][sumpm_def]);

(* lists *)
val listpm_def = Define`
  (listpm (apm: 'a pm) pi [] = []) /\
  (listpm apm pi (h::t) = apm pi h :: listpm apm pi t)
`;
val _ = export_rewrites ["listpm_def"]

val listpm_MAP = store_thm(
  "listpm_MAP",
  ``!l. listpm pm pi l = MAP (pm pi) l``,
  Induct THEN SRW_TAC [][listpm_def]);

val listpm_is_perm = Store_Thm(
  "listpm_is_perm",
  ``is_perm pm ==> is_perm (listpm pm)``,
  SIMP_TAC (srw_ss()) [is_perm_def, FUN_EQ_THM, permeq_def] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL [
    Induct THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][],
    REPEAT GEN_TAC THEN STRIP_TAC THEN Induct THEN SRW_TAC [][]
  ]);

val listpm_APPENDlist = store_thm(
  "listpm_APPENDlist",
  ``listpm pm pi (l1 ++ l2) = listpm pm pi l1 ++ listpm pm pi l2``,
  Induct_on `l1` THEN SRW_TAC [][]);

val listpm_APPEND = store_thm(
  "listpm_APPEND",
  ``is_perm pm ==> (listpm pm (p1 ++ p2) x = listpm pm p1 (listpm pm p2 x))``,
  METIS_TAC [listpm_is_perm, is_perm_decompose]);

(* lists of pairs of strings, (concrete rep for permutations) *)
val cpmpm_def = Define`
  cpmpm = listpm (pairpm lswapstr lswapstr)
`;

val cpmpm_thm = Store_Thm(
  "cpmpm_thm",
  ``(cpmpm pi [] = []) /\
    (cpmpm pi ((x,y)::t) = (lswapstr pi x, lswapstr pi y) :: cpmpm pi t)``,
  SRW_TAC [][cpmpm_def]);

val cpmpm_is_perm = Store_Thm(
  "cpmpm_is_perm",
  ``is_perm cpmpm``,
  SRW_TAC [][cpmpm_def]);

val cpmpm_APPENDlist = store_thm(
  "cpmpm_APPENDlist",
  ``cpmpm pi (l1 ++ l2) = cpmpm pi l1 ++ cpmpm pi l2``,
  SRW_TAC [][cpmpm_def, listpm_APPENDlist]);

val cpmpm_APPEND = store_thm(
  "cpmpm_APPEND",
  ``cpmpm (p1 ++ p2) p = cpmpm p1 (cpmpm p2 p)``,
  SRW_TAC [][cpmpm_def, listpm_APPEND]);

val cpmpm_sing_inv = Store_Thm(
  "cpmpm_sing_inv",
  ``cpmpm [h] (cpmpm (h::t) p) = cpmpm t p``,
  `!p1 p2 v. cpmpm p1 (cpmpm p2 v) = cpmpm (p1 ++ p2) v`
      by METIS_TAC [cpmpm_is_perm, is_perm_def] THEN
  SRW_TAC [][is_perm_dups])

val cpmpm_nil = Store_Thm(
  "cpmpm_nil",
  ``cpmpm [] v = v``,
  METIS_TAC [cpmpm_is_perm, is_perm_def]);

(* ----------------------------------------------------------------------
    Notion of support, and calculating the smallest set of support
   ---------------------------------------------------------------------- *)

val support_def = Define`
  support (pm : (string # string) list -> 'a -> 'a) (a:'a) (supp: string set) =
     !x y. ~(x IN supp) /\ ~(y IN supp) ==> (pm [(x,y)] a = a)
`;

val perm_support = store_thm(
  "perm_support",
  ``is_perm pm ==> (support pm (pm p x) s =
                    support pm x (setpm perm_of (REVERSE p) s))``,
  ASM_SIMP_TAC (srw_ss()) [EQ_IMP_THM, support_def, perm_IN] THEN
  STRIP_TAC THEN CONJ_TAC THEN STRIP_TAC THEN
  MAP_EVERY Q.X_GEN_TAC [`a`,`b`] THEN STRIP_TAC THENL [
    `pm [(perm_of p a, perm_of p b)] (pm p x) = pm p x`
       by METIS_TAC [] THEN
    `pm ([(perm_of p a, perm_of p b)] ++ p) x = pm p x`
       by METIS_TAC [is_perm_def] THEN
    `[(perm_of p a, perm_of p b)] ++ p == p ++ [(a,b)]`
       by METIS_TAC [permeq_swap_ends, permeq_sym, listTheory.APPEND] THEN
    `pm (p ++ [(a,b)]) x = pm p x`
       by METIS_TAC [is_perm_def] THEN
    METIS_TAC [is_perm_injective, is_perm_def],
    `pm [(a,b)] (pm p x) = pm ([(a,b)] ++ p) x` by METIS_TAC [is_perm_def] THEN
    Q.ABBREV_TAC `pi = REVERSE p` THEN
    `[(a,b)] ++ p == p ++ [(perm_of pi a, perm_of pi b)]`
       by (SRW_TAC [][Abbr`pi`] THEN
           Q.SPECL_THEN [`p`, `perm_of (REVERSE p) a`, `perm_of (REVERSE p) b`]
                        (ASSUME_TAC o REWRITE_RULE [permof_inverse_applied])
                        permeq_swap_ends THEN
           METIS_TAC [permeq_sym]) THEN
    `pm [(a,b)] (pm p x) = pm (p ++ [(perm_of pi a, perm_of pi b)]) x`
       by METIS_TAC [is_perm_def] THEN
    ` _ = pm p (pm [(perm_of pi a, perm_of pi b)] x)`
       by METIS_TAC [is_perm_def] THEN
    ASM_SIMP_TAC (srw_ss()) [is_perm_injective] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [Abbr`pi`]
  ]);


val support_dwards_directed = store_thm(
  "support_dwards_directed",
  ``support pm e s1 /\ support pm e s2 /\ is_perm pm /\
    FINITE s1 /\ FINITE s2 ==>
    support pm e (s1 INTER s2)``,
  SIMP_TAC bool_ss [support_def] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `x = y` THEN1 METIS_TAC [is_perm_id, is_perm_def] THEN
  Q_TAC (NEW_TAC "z") `{x;y} UNION s1 UNION s2` THEN
  `[(x,y)] == [(x,z); (y,z); (x,z)]`
     by (SRW_TAC [][FUN_EQ_THM, permeq_def] THEN
         CONV_TAC (RAND_CONV
                    (ONCE_REWRITE_CONV [GSYM swapstr_swapstr])) THEN
         SIMP_TAC bool_ss [swapstr_inverse] THEN
         SRW_TAC [][]) THEN
  `pm [(x,y)] e = pm [(x,z); (y,z); (x,z)] e`
     by METIS_TAC [is_perm_def] THEN
  ` _ = pm [(x,z)] (pm [(y,z)] (pm [(x,z)] e))`
     by METIS_TAC [is_perm_def, listTheory.APPEND] THEN
  METIS_TAC [IN_INTER]);

val supp_def = Define`
  supp pm x = { (a:string) | INFINITE { (b:string) | ~(pm [(a,b)] x = x)}}
`;

val supp_supports = store_thm(
  "supp_supports",
  ``is_perm pm ==> support pm x (supp pm x)``,
  ASM_SIMP_TAC (srw_ss()) [support_def, supp_def, is_perm_decompose,
                           INFINITE_DEF] THEN STRIP_TAC THEN
  MAP_EVERY Q.X_GEN_TAC [`a`, `b`] THEN STRIP_TAC THEN
  Q.ABBREV_TAC `aset = {b | ~(pm [(a,b)] x = x)}` THEN
  Q.ABBREV_TAC `bset = {c | ~(pm [(b,c)] x = x)}` THEN
  Cases_on `a = b` THEN1 SRW_TAC [][is_perm_id, is_perm_nil] THEN
  `?c. ~(c IN aset) /\ ~(c IN bset) /\ ~(c = a) /\ ~(c = b)`
      by (Q.SPEC_THEN `{a;b} UNION aset UNION bset` MP_TAC NEW_def THEN
          SRW_TAC [][] THEN METIS_TAC []) THEN
  `(pm [(a,c)] x = x) /\ (pm [(b,c)] x = x)`
      by FULL_SIMP_TAC (srw_ss()) [Abbr`aset`, Abbr`bset`] THEN
  `pm ([(a,c)] ++ [(b,c)] ++ [(a,c)]) x = x`
      by SRW_TAC [][is_perm_decompose] THEN
  Q_TAC SUFF_TAC `[(a,c)] ++ [(b,c)] ++ [(a,c)] == [(a,b)]`
        THEN1 METIS_TAC [is_perm_def] THEN
  SIMP_TAC (srw_ss()) [permeq_def, FUN_EQ_THM] THEN
  ONCE_REWRITE_TAC [GSYM swapstr_swapstr] THEN
  `(swapstr a c b = b) /\ (swapstr a c c = a)` by SRW_TAC [][swapstr_def] THEN
  ASM_REWRITE_TAC [] THEN SRW_TAC [][]);

val supp_fresh = store_thm(
  "supp_fresh",
  ``is_perm apm /\ ~(x IN supp apm v) /\ ~(y IN supp apm v) ==>
    (apm [(x,y)] v = v)``,
  METIS_TAC [support_def, supp_supports]);


val setpm_postcompose = store_thm(
  "setpm_postcompose",
  ``!P pm p. is_perm pm ==>
             ({x | P (pm p x)} = setpm pm (REVERSE p) {x | P x})``,
  SRW_TAC [][EXTENSION, perm_IN]);

val perm_supp = store_thm(
  "perm_supp",
  ``is_perm pm ==> (supp pm (pm p x) = setpm perm_of p (supp pm x))``,
  SIMP_TAC (srw_ss()) [EXTENSION, perm_IN, supp_def, is_perm_eql,
                       INFINITE_DEF] THEN STRIP_TAC THEN
  Q.X_GEN_TAC `a` THEN
  `!e x y. pm (REVERSE p) (pm [(x,y)] e) =
           pm [(perm_of (REVERSE p) x, perm_of (REVERSE p) y)]
              (pm (REVERSE p) e)`
      by METIS_TAC [is_perm_def, permeq_swap_ends, listTheory.APPEND] THEN
  SRW_TAC [][is_perm_inverse] THEN
  Q.MATCH_ABBREV_TAC `FINITE s1 = FINITE s2` THEN
  `s1 = { b | (\s. ~(x = pm [(perm_of (REVERSE p) a, s)] x))
                (perm_of (REVERSE p ) b)}`
     by SRW_TAC [][Abbr`s1`] THEN
  ` _ = setpm perm_of (REVERSE (REVERSE p))
              {b | (\s. ~(x = pm [(perm_of (REVERSE p) a, s)] x)) b}`
     by (MATCH_MP_TAC setpm_postcompose THEN SRW_TAC [][]) THEN
  Q.UNABBREV_TAC `s2` THEN SRW_TAC [][]);

val supp_apart = store_thm(
  "supp_apart",
  ``is_perm pm /\ a IN supp pm x /\ ~(b IN supp pm x) ==>
    ~(pm [(a,b)] x = x)``,
  STRIP_TAC THEN
  `~(a = b)` by METIS_TAC [] THEN
  `b IN setpm perm_of [(a,b)] (supp pm x)`
     by SRW_TAC[][perm_IN, swapstr_def] THEN
  `b IN supp pm (pm [(a,b)] x)`
     by SRW_TAC [][perm_supp] THEN
  `~(supp pm x = supp pm (pm [(a,b)] x))` by METIS_TAC [] THEN
  METIS_TAC []);

(* lemma3_4_i from Pitts & Gabbay - New Approach to Abstract Syntax *)
val supp_smallest = store_thm(
  "supp_smallest",
  ``is_perm pm /\ support pm x s /\ FINITE s ==> supp pm x SUBSET s``,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SUBSET_DEF] THEN
  Q.X_GEN_TAC `a` THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `!b. ~(b IN s) ==> (pm [(a,b)] x = x)`
     by METIS_TAC [support_def] THEN
  `{b | ~(pm [(a,b)] x = x)} SUBSET s`
     by (SRW_TAC [][SUBSET_DEF] THEN METIS_TAC []) THEN
  `FINITE {b | ~(pm [(a,b)] x = x)}` by METIS_TAC [SUBSET_FINITE] THEN
  FULL_SIMP_TAC (srw_ss()) [supp_def, INFINITE_DEF]);

val lemma0 = prove(
  ``COMPL (e INSERT s) = COMPL s DELETE e``,
  SRW_TAC [][EXTENSION] THEN METIS_TAC []);
val lemma = prove(
  ``!s: string set. FINITE s ==> ~FINITE (COMPL s)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][lemma0] THEN
  SRW_TAC [][INFINITE_STR_UNIV, GSYM INFINITE_DEF]);

val supp_unique = store_thm(
  "supp_unique",
  ``is_perm pm /\ support pm x s /\ FINITE s /\
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
  ``is_perm pm /\ support pm x s /\ FINITE s /\
    (!a b. a IN s /\ ~(b IN s) ==> ~(pm [(a,b)] x = x)) ==>
    (supp pm x = s)``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][SUBSET_DEF] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `?z. ~(z IN s') /\ ~(z IN s)`
      by (Q.SPEC_THEN `s UNION s'` MP_TAC NEW_def THEN
          SRW_TAC [][] THEN METIS_TAC []) THEN
  METIS_TAC [support_def]);

(* some examples of supp *)
val supp_string = Store_Thm(
  "supp_string",
  ``supp perm_of s = {s}``,
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def]);

val supp_discrete = Store_Thm(
  "supp_discrete",
  ``supp (K I) x = {}``,
  SRW_TAC [][supp_def, INFINITE_DEF]);

(* options *)
val supp_optpm = store_thm(
  "supp_optpm",
  ``(supp (optpm pm) NONE = {}) /\
    (supp (optpm pm) (SOME x) = supp pm x)``,
  SRW_TAC [][supp_def, optpm_def, pred_setTheory.INFINITE_DEF]);
val _ = export_rewrites ["supp_optpm"]

(* pairs *)
val supp_pairpm = Store_Thm(
  "supp_pairpm",
  ``(supp (pairpm pm1 pm2) (x,y) = supp pm1 x UNION supp pm2 y)``,
  SRW_TAC [][supp_def, GSPEC_OR, INFINITE_DEF]);

(* lists *)
val supp_listpm = Store_Thm(
  "supp_listpm",
  ``(supp (listpm apm) [] = {}) /\
    (supp (listpm apm) (h::t) = supp apm h UNION supp (listpm apm) t)``,
  SRW_TAC [][supp_def, INFINITE_DEF, GSPEC_OR]);

(* concrete permutations, which get their own constant for calculating their
   support *)
val patoms_def = Define`
  (patoms [] = {}) /\
  (patoms (h::t) = {FST h:string; SND h} UNION patoms t)
`;
val _ = export_rewrites ["patoms_def"]

val FINITE_patoms = Store_Thm(
  "FINITE_patoms",
  ``!l. FINITE (patoms l)``,
  Induct THEN SRW_TAC [][patoms_def]);

val supp_cpmpm = Store_Thm(
  "supp_cpmpm",
  ``!p. supp cpmpm p = patoms p``,
  SIMP_TAC (srw_ss()) [cpmpm_def] THEN
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, INSERT_UNION_EQ]);

val patoms_fresh = Store_Thm(
  "patoms_fresh",
  ``!p. ~(x IN patoms p) /\ ~(y IN patoms p) ==> (cpmpm [(x,y)] p = p)``,
  METIS_TAC [supp_cpmpm, supp_supports, support_def, cpmpm_is_perm]);

val perm_of_unchanged = store_thm(
  "perm_of_unchanged",
  ``!p. ~(s IN patoms p) ==> (perm_of p s = s)``,
  Induct THEN SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][swapstr_def]);

val patoms_APPEND = store_thm(
  "patoms_APPEND",
  ``patoms (x ++ y) = patoms x UNION patoms y``,
  Induct_on `x` THEN
  ASM_SIMP_TAC (srw_ss()) [EXTENSION,
                           pairTheory.FORALL_PROD] THEN
  METIS_TAC []);

val patoms_REVERSE = store_thm(
  "patoms_REVERSE",
  ``patoms (REVERSE pi) = patoms pi``,
  Induct_on `pi` THEN
  ASM_SIMP_TAC (srw_ss()) [EXTENSION, pairTheory.FORALL_PROD,
                           patoms_APPEND] THEN METIS_TAC []);


val pm_cpmpm_cancel = prove(
  ``is_perm pm ==>
     (pm [(x,y)] (pm (cpmpm [(x,y)] pi) (pm [(x,y)] t)) = pm pi t)``,
  STRIP_TAC THEN Induct_on `pi` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, is_perm_nil,
                           is_perm_sing_inv] THEN
  `!p q pi t. pm ((swapstr x y p, swapstr x y q)::pi) t =
              pm [(swapstr x y p, swapstr x y q)] (pm pi t)`
     by SRW_TAC [][GSYM is_perm_decompose] THEN
  REPEAT GEN_TAC THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  ONCE_REWRITE_TAC [MP (GSYM is_perm_sing_to_back)
                       (ASSUME ``is_perm pm``)] THEN
  SRW_TAC [][] THEN
  SRW_TAC [][GSYM is_perm_decompose]);

val is_perm_supp_empty = store_thm(
  "is_perm_supp_empty",
  ``is_perm pm ==> (supp (fnpm cpmpm (fnpm pm pm)) pm = {})``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][] THEN
  SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, pm_cpmpm_cancel]);

val supp_pm_fresh = store_thm(
  "supp_pm_fresh",
  ``is_perm pm /\ (supp pm x = {}) ==> (pm pi x = x)``,
  Induct_on `pi` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, is_perm_nil] THEN
  REPEAT STRIP_TAC THEN
  `pm ((p_1,p_2)::pi) x = pm [(p_1,p_2)] (pm pi x)`
     by SIMP_TAC (srw_ss()) [GSYM is_perm_decompose,
                             ASSUME ``is_perm pm``] THEN
  SRW_TAC [][supp_fresh]);

val pm_pm_cpmpm = store_thm(
  "pm_pm_cpmpm",
  ``is_perm pm ==>
        (pm pi1 (pm pi2 s) = pm (cpmpm pi1 pi2) (pm pi1 s))``,
  STRIP_TAC THEN Q.MATCH_ABBREV_TAC `L = R` THEN
  `L = fnpm pm pm pi1 (pm pi2) (pm pi1 s)`
     by SRW_TAC [][fnpm_def, is_perm_inverse] THEN
  `_ = fnpm cpmpm
            (fnpm pm pm)
            pi1
            pm
            (cpmpm pi1 pi2)
            (pm pi1 s)`
     by (ONCE_REWRITE_TAC [fnpm_def] THEN
         ONCE_REWRITE_TAC [fnpm_def] THEN
         SRW_TAC [][is_perm_inverse]) THEN
  `fnpm cpmpm (fnpm pm pm) pi1 pm = pm`
     by SRW_TAC [][supp_pm_fresh, is_perm_supp_empty] THEN
  METIS_TAC []);

val lswapstr_lswapstr_cpmpm = save_thm(
  "lswapstr_lswapstr_cpmpm",
  (SIMP_RULE (srw_ss()) []  o Q.INST [`pm` |-> `lswapstr`] o
   INST_TYPE [alpha |-> ``:string``]) pm_pm_cpmpm);

val patoms_cpmpm = store_thm(
  "patoms_cpmpm",
  ``patoms (cpmpm pi1 pi2) = setpm lswapstr pi1 (patoms pi2)``,
  SIMP_TAC bool_ss [GSYM supp_cpmpm] THEN MATCH_MP_TAC perm_supp THEN
  SRW_TAC [][]);

(* support for honest to goodness permutations, not just their
   representations *)
val perm_supp_SUBSET_plistvars = prove(
  ``!p. {s | ~(perm_of p s = s)} SUBSET
        FOLDR (\p a. {FST p; SND p} UNION a) {} p``,
  ASM_SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF] THEN Induct THEN
  SRW_TAC [][] THEN
  Cases_on `x = FST h` THEN SRW_TAC [][] THEN
  Cases_on `x = SND h` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [swapstr_def, swapstr_eq_left]);

val FINITE_plistvars = prove(
  ``FINITE (FOLDR (\p a. {FST p; SND p} UNION a) {} p)``,
  Induct_on `p` THEN SRW_TAC [][]);
val lemma = MATCH_MP pred_setTheory.SUBSET_FINITE FINITE_plistvars

val perm_supp_finite = store_thm(
  "perm_supp_finite",
  ``FINITE {s | ~(perm_of p s = s)}``,
  MATCH_MP_TAC lemma THEN SRW_TAC [][perm_supp_SUBSET_plistvars]);

val lemma = prove(
  ``(perm_of p x = x) /\ (perm_of p y = y) ==>
    (fnpm perm_of perm_of [(x,y)] (perm_of p) = perm_of p)``,
  STRIP_TAC THEN
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, fnpm_def] THEN
  Q.X_GEN_TAC `a` THEN
  `perm_of p (swapstr x y a) = perm_of p (perm_of [(x,y)] a)`
     by SRW_TAC [][] THEN
  `_ = perm_of (p ++ [(x,y)]) a`
     by SIMP_TAC (srw_ss())[lswapstr_APPEND] THEN
  `_ = perm_of ([(x,y)] ++ p) a`
     by (Q_TAC SUFF_TAC `p ++ [(x,y)] == [(x,y)] ++ p`
               THEN1 SRW_TAC [][permeq_def] THEN
         METIS_TAC [permeq_swap_ends, listTheory.APPEND]) THEN
  SRW_TAC [][]);

val supp_perm_of = store_thm(
  "supp_perm_of",
  ``supp (fnpm perm_of perm_of) (perm_of p) = { s | ~(perm_of p s = s) }``,
  HO_MATCH_MP_TAC supp_unique THEN
  SRW_TAC [][perm_supp_finite] THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, perm_of_swapstr],

    SRW_TAC [][pred_setTheory.SUBSET_DEF] THEN
    SPOSE_NOT_THEN ASSUME_TAC THEN
    Q_TAC (NEW_TAC "y") `{x; perm_of (REVERSE p) x} UNION s'` THEN
    `!a. fnpm perm_of perm_of [(x,y)] (perm_of p) a = perm_of p a`
       by METIS_TAC [support_def] THEN
    `p ++ [(x,y)] == [(x,y)] ++ p`
       by (POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [fnpm_def]) THEN
           SRW_TAC [][permeq_def, FUN_EQ_THM, perm_of_decompose,
                      GSYM swapstr_eq_left]) THEN
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
    SRW_TAC [][swapstr_def]
  ]);

val support_FINITE_supp = store_thm(
  "support_FINITE_supp",
  ``is_perm pm /\ support pm v A /\ FINITE A ==> FINITE (supp pm v)``,
  METIS_TAC [supp_smallest, SUBSET_FINITE]);

val support_fnapp = store_thm(
  "support_fnapp",
  ``is_perm dpm /\ is_perm rpm /\
    support (fnpm dpm rpm) f A /\ support dpm d B ==>
    support rpm (f d) (A UNION B)``,
  SRW_TAC [][support_def] THEN
  `rpm [(x,y)] (f d) = fnpm dpm rpm [(x,y)] f (dpm [(x,y)] d)`
     by SRW_TAC [][fnpm_def] THEN
  SRW_TAC [][]);

val supp_fnapp = store_thm(
  "supp_fnapp",
  ``is_perm dpm /\ is_perm rpm /\ FINITE (supp (fnpm dpm rpm) f) /\
    FINITE (supp dpm x) ==>
    supp rpm (f x) SUBSET supp (fnpm dpm rpm) f UNION supp dpm x``,
  METIS_TAC [supp_smallest, FINITE_UNION, supp_supports, fnpm_is_perm,
             support_fnapp]);

open finite_mapTheory
val _ = set_trace "Unicode" 1
val fmpm_def = Define`
  fmpm (dpm : 'd pm) (rpm : 'r pm) pi fmap =
    rpm pi o_f fmap f_o dpm (REVERSE pi)
`;

val lemma0 = prove(
  ``is_perm pm ==> (pm pi x ∈ X = x ∈ setpm pm (REVERSE pi) X)``,
  SRW_TAC [][perm_IN])
val lemma1 = prove(``{x | x ∈ X} = X``, SRW_TAC [][pred_setTheory.EXTENSION])
val lemma = prove(
  ``is_perm pm ==> FINITE { x | pm pi x ∈ FDOM f}``,
  SIMP_TAC bool_ss [lemma0, lemma1, perm_FINITE,
                    finite_mapTheory.FDOM_FINITE]);

val fmpm_applied = store_thm(
  "fmpm_applied",
  ``is_perm dpm ∧ dpm (REVERSE pi) x ∈ FDOM fm ==>
    (fmpm dpm rpm pi fm ' x = rpm pi (fm ' (dpm (REVERSE pi) x)))``,
  SRW_TAC [][fmpm_def, FAPPLY_f_o, FDOM_f_o, lemma, o_f_FAPPLY]);

val fmpm_FDOM = store_thm(
  "fmpm_FDOM",
  ``is_perm dpm ==>
     (x IN FDOM (fmpm dpm rpm pi fmap) = dpm (REVERSE pi) x IN FDOM fmap)``,
  SRW_TAC [][fmpm_def, lemma, FDOM_f_o])

val fmpm_is_perm = store_thm(
  "fmpm_is_perm",
  ``is_perm dpm /\ is_perm rpm ==> is_perm (fmpm dpm rpm)``,
  STRIP_TAC THEN SRW_TAC [][is_perm_def] THENL [
    `(!d. dpm [] d = d) ∧ (!r. rpm [] r = r)` by METIS_TAC [is_perm_def] THEN
    SRW_TAC [][fmap_EXT, fmpm_def, pred_setTheory.EXTENSION, FDOM_f_o, lemma,
               FAPPLY_f_o, o_f_FAPPLY],

    `(!d pi1 pi2. dpm (pi1 ++ pi2) d = dpm pi1 (dpm pi2 d)) ∧
     (!r pi1 pi2. rpm (pi1 ++ pi2) r = rpm pi1 (rpm pi2 r))`
      by METIS_TAC [is_perm_def] THEN
    SRW_TAC [][fmap_EXT, fmpm_def, FDOM_f_o, lemma, o_f_FAPPLY,
               listTheory.REVERSE_APPEND, FAPPLY_f_o],

    `REVERSE p1 == REVERSE p2` by METIS_TAC [permof_REVERSE_monotone] THEN
    `(rpm p1 = rpm p2) ∧ (dpm (REVERSE p1) = dpm (REVERSE p2))`
       by METIS_TAC [is_perm_def] THEN
    SRW_TAC [][fmpm_def, fmap_EXT, FUN_EQ_THM, FDOM_f_o, lemma]
  ]);
val _ = export_rewrites ["fmpm_is_perm"]

val supp_setpm = store_thm(
  "supp_setpm",
  ``is_perm pm /\ FINITE s /\ (!x. x∈s ==> FINITE (supp pm x)) ==>
    (supp (setpm pm) s = BIGUNION (IMAGE (supp pm) s))``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][] THENL [
    SRW_TAC [][support_def] THEN
    SRW_TAC [][pred_setTheory.EXTENSION] THEN
    Cases_on `x ∈ supp pm x'` THENL [
      `¬(x'∈s)` by METIS_TAC [] THEN
      `y ∈ supp pm (pm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN Cases_on `y ∈ supp pm x'` THENL [
      `¬(x' ∈ s)` by METIS_TAC [] THEN
      `x ∈ supp pm (pm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN SRW_TAC [][supp_fresh],

    METIS_TAC [],

    SRW_TAC [][pred_setTheory.EXTENSION] THEN
    `∀x. b ∈ supp pm x ==> ¬(x ∈ s)` by METIS_TAC [] THEN
    `¬(b ∈ supp pm x)` by METIS_TAC [] THEN
    `b ∈ supp pm (pm [(a,b)] x)` by SRW_TAC [][perm_supp] THEN
    METIS_TAC []
  ]);

val supp_FINITE_strings = store_thm(
  "supp_FINITE_strings",
  ``FINITE s ==> (supp (setpm lswapstr) s = s)``,
  SRW_TAC [][supp_setpm, pred_setTheory.EXTENSION] THEN EQ_TAC THEN
  STRIP_TAC THENL [
    METIS_TAC [],
    Q.EXISTS_TAC `{x}` THEN SRW_TAC [][] THEN METIS_TAC []
  ]);
val _ = export_rewrites ["supp_FINITE_strings"]



val rwt = prove(
  ``(!x. ~P x \/ Q x) = (!x. P x ==> Q x)``,
  METIS_TAC []);

val fmap_supp = store_thm(
  "fmap_supp",
  ``is_perm dpm /\ is_perm rpm /\ (!d. FINITE (supp dpm d)) /\
    (!r. FINITE (supp rpm r)) ==>
    (supp (fmpm dpm rpm) fmap =
        supp (setpm dpm) (FDOM fmap) ∪
        supp (setpm rpm) (FRANGE fmap))``,
  STRIP_TAC THEN MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][FINITE_FRANGE, fmpm_is_perm, supp_setpm, rwt,
             GSYM RIGHT_FORALL_IMP_THM]
  THENL [
    SRW_TAC [][support_def, fmap_EXT, rwt, GSYM RIGHT_FORALL_IMP_THM,
               fmpm_FDOM]
    THENL [
      SRW_TAC [][pred_setTheory.EXTENSION, fmpm_FDOM] THEN
      Cases_on `x ∈ supp dpm x'` THEN1
        (`y ∈ supp dpm (dpm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
         METIS_TAC []) THEN
      Cases_on `y ∈ supp dpm x'` THEN1
        (`x ∈ supp dpm (dpm [(x,y)] x')` by SRW_TAC [][perm_supp] THEN
         METIS_TAC []) THEN
      METIS_TAC [supp_fresh],
      SRW_TAC [][fmpm_def, FAPPLY_f_o, lemma, FDOM_f_o, o_f_FAPPLY] THEN
      `¬(x ∈ supp dpm (dpm [(x,y)] x')) ∧ ¬(y ∈ supp dpm (dpm [(x,y)] x'))`
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
    `b ∈ supp dpm (dpm [(a,b)] x)` by SRW_TAC [][perm_supp] THEN
    METIS_TAC [],

    `¬(b ∈ supp rpm x)` by METIS_TAC [] THEN
    `∃y. y ∈ FDOM fmap ∧ (fmap ' y = x)`
        by (FULL_SIMP_TAC (srw_ss()) [FRANGE_DEF] THEN METIS_TAC []) THEN
    `¬(b ∈ supp dpm y)` by METIS_TAC [] THEN
    Cases_on `a ∈ supp dpm y` THENL [
      `b ∈ supp dpm (dpm [(a,b)] y)` by SRW_TAC [][perm_supp] THEN
      SRW_TAC [][fmap_EXT, fmpm_FDOM, pred_setTheory.EXTENSION] THEN
      METIS_TAC [],
      ALL_TAC
    ] THEN
    SRW_TAC [][fmap_EXT, fmpm_FDOM] THEN DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN
    SRW_TAC [][supp_fresh, fmpm_def, FAPPLY_f_o, o_f_FAPPLY, lemma,
               FDOM_f_o] THEN
    METIS_TAC [supp_apart]
  ]);

val FAPPLY_eqv_lswapstr = store_thm(
  "FAPPLY_eqv_lswapstr",
  ``is_perm rpm ∧ d ∈ FDOM fm ==>
    (rpm pi (fm ' d) = fmpm lswapstr rpm pi fm ' (lswapstr pi d))``,
  SRW_TAC [][fmpm_def, FAPPLY_f_o, FDOM_f_o, lemma, o_f_FAPPLY]);
  (* feels as if it should be possible to prove this for the case where d is
     not in the domain *)

val fmpm_FEMPTY = store_thm(
  "fmpm_FEMPTY",
  ``is_perm dpm ==> (fmpm dpm rpm pi FEMPTY = FEMPTY)``,
  SRW_TAC [][fmap_EXT, fmpm_applied, fmpm_FDOM, pred_setTheory.EXTENSION]);
val _ = export_rewrites ["fmpm_FEMPTY"]

val fmpm_FUPDATE = store_thm(
  "fmpm_FUPDATE",
  ``is_perm dpm ∧ is_perm rpm ==>
    (fmpm dpm rpm pi (fm |+ (k,v)) =
       fmpm dpm rpm pi fm |+ (dpm pi k, rpm pi v))``,
  SRW_TAC [][fmap_EXT, fmpm_applied, fmpm_FDOM, pred_setTheory.EXTENSION]
  THENL [
    SRW_TAC [][is_perm_eql],
    SRW_TAC [][is_perm_inverse],
    Cases_on `k = dpm (REVERSE pi) x` THENL [
      SRW_TAC [][is_perm_inverse],
      SRW_TAC [][FAPPLY_FUPDATE_THM, fmpm_applied] THEN
      METIS_TAC [is_perm_inverse]
    ]
  ]);
val _ = export_rewrites ["fmpm_FUPDATE"]




val fcond_def = Define`
  fcond pm f = is_perm pm /\ FINITE (supp (fnpm perm_of pm) f) /\
               (?a. ~(a IN supp (fnpm perm_of pm) f) /\ ~(a IN supp pm (f a)))
`;

val fcond_equivariant = Store_Thm(
  "fcond_equivariant",
  ``fcond pm (fnpm perm_of pm pi f) = fcond pm f``,
  SIMP_TAC (srw_ss() ++ CONJ_ss) [fcond_def, EQ_IMP_THM, perm_supp, fnpm_def,
                                  perm_IN, perm_FINITE] THEN
  METIS_TAC [is_perm_inverse, perm_of_is_perm]);


val fresh_def = Define`fresh apm f = let z = NEW (supp (fnpm lswapstr apm) f)
                                     in
                                       f z`

val fresh_thm = store_thm(
  "fresh_thm",
  ``fcond apm f ==>
    !a. ~(a IN supp (fnpm perm_of apm) f) ==> (f a = fresh apm f)``,
  SIMP_TAC (srw_ss()) [fcond_def, fresh_def] THEN STRIP_TAC THEN
  Q.X_GEN_TAC `b` THEN
  SRW_TAC [][fcond_def, fresh_def] THEN
  Q.UNABBREV_TAC `z` THEN
  NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `!c. ~(c IN supp (fnpm lswapstr apm) f) ==> (f c = f a)`
        THEN1 SRW_TAC [][] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `c = a` THEN1 SRW_TAC [][] THEN
  `~(c IN supp lswapstr a)` by SRW_TAC [][] THEN
  `~(c IN supp apm (f a))`
      by (`supp apm (f a) SUBSET
             supp (fnpm lswapstr apm) f UNION supp lswapstr a`
            by SRW_TAC [][supp_fnapp] THEN
          FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC []) THEN
  `apm [(a,c)] (f a) = f a` by METIS_TAC [supp_supports, support_def] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  `apm [(a,c)] (f a) = fnpm lswapstr apm [(a,c)] f (lswapstr [(a,c)] a)`
     by SRW_TAC [][fnpm_def] THEN
  SRW_TAC [][supp_fresh])

val fresh_equivariant = store_thm(
  "fresh_equivariant",
  ``fcond pm f ==>
    (pm pi (fresh pm f) = fresh pm (fnpm perm_of pm pi f))``,
  STRIP_TAC THEN
  `is_perm pm` by METIS_TAC [fcond_def] THEN
  `fcond pm (fnpm perm_of pm pi f)` by SRW_TAC [][fcond_equivariant] THEN
  `?b. ~(b IN supp (fnpm perm_of pm) (fnpm perm_of pm pi f))`
     by (Q.SPEC_THEN `supp (fnpm perm_of pm) (fnpm perm_of pm pi f)`
                     MP_TAC NEW_def THEN METIS_TAC [fcond_def]) THEN
  `~(perm_of (REVERSE pi) b IN supp (fnpm perm_of pm) f)`
     by (POP_ASSUM MP_TAC THEN SRW_TAC [][perm_supp, perm_IN]) THEN
  `fresh pm (fnpm perm_of pm pi f) = fnpm perm_of pm pi f b`
     by METIS_TAC [fresh_thm] THEN
  SRW_TAC [][fnpm_def, is_perm_injective, GSYM fresh_thm]);

val _ = export_theory();
