(* This is an -*- sml -*- file *)

(* could perform quotient now *)

(* First show connection with nomset concepts *)
open HolKernel boolLib Parse bossLib BasicProvers
open pred_setTheory

open binderLib
open basic_swapTheory nomsetTheory termTheory preltermTheory

val _ = new_theory "labelledTerms"

fun Store_Thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]
fun Save_Thm(n,th) = save_thm(n,th) before export_rewrites [n]


val _ = print "Proving recursion theorem\n"

val lamf = ``lamf : string -> 'a -> 'a``
val h = ``\a':string. ^lamf a' ((s:(string # string) list->'a)
                                 (pi ++ [(a',a)]))``

val limf = ``limf : num -> string -> 'a -> 'a -> 'a``
val i = ``\a':string.
             ^limf n a' ((s:(string # string) list -> 'a) (pi ++ [(a',a)]))``
val limf_pm = ``fnpm (K I : num pm) (fnpm perm_of (fnpm apm (fnpm apm apm)))``

val lamf_supp_t = ``supp (fnpm perm_of (fnpm apm apm)) ^lamf``
val limf_supp_t = ``supp ^limf_pm ^limf``

val finite_supp = prove(
  ``is_perm pm /\ support pm a X /\ FINITE X ==> FINITE(supp pm a)``,
  METIS_TAC [supp_smallest, SUBSET_FINITE]);

val perm_fnapp = prove(
  ``is_perm pm1 /\ is_perm pm2 ==>
    (pm2 pi (f x) = (fnpm pm1 pm2 pi f) (pm1 pi x))``,
  SRW_TAC [][fnpm_def, is_perm_inverse]);

val supp_fresh = prove(
  ``is_perm pm /\ ~(x IN supp pm a) /\ ~(y IN supp pm a) ==>
    (pm [(x,y)] a = a)``,
  METIS_TAC [supp_supports, support_def]);

val supp_freshf = prove(
  ``is_perm pm1 /\ is_perm pm2 /\
    ~(x IN supp (fnpm pm1 pm2) f) /\ ~(y IN supp (fnpm pm1 pm2) f) ==>
    !a. pm2 [(x,y)] (f a) = f (pm1 [(x,y)] a)``,
  REPEAT STRIP_TAC THEN
  `pm2 [(x,y)] (f a) = fnpm pm1 pm2 [(x,y)] f (pm1 [(x,y)] a)`
     by SRW_TAC [][GSYM perm_fnapp] THEN
  SRW_TAC [][supp_fresh]);

val support_freshf = prove(
  ``is_perm pm1 /\ is_perm pm2 /\ ~(x IN A) /\ ~(y IN A) /\
    support (fnpm pm1 pm2) f A ==>
    !a. pm2 [(x,y)] (f a) = f (pm1 [(x,y)] a)``,
  SRW_TAC [][support_def] THEN
  `pm2 [(x,y)] (f a) = fnpm pm1 pm2 [(x,y)] f (pm1 [(x,y)] a)`
     by SRW_TAC [][GSYM perm_fnapp] THEN
  SRW_TAC [][]);

val lamf_support_t = ``support (fnpm perm_of (fnpm apm apm)) lamf A``
val app_support_t = ``support (fnpm apm (fnpm apm apm)) ap A``
val var_support_t = ``support (fnpm perm_of apm) vr A``
val limf_support_t = ``support ^limf_pm limf A``

val lamf_support_fresh = UNDISCH (UNDISCH (prove(
  ``^lamf_support_t ==> is_perm apm ==>
    !x y v a.
      ~(x IN A) /\ ~(y IN A) ==>
        (apm [(x,y)] (lamf v a) = lamf (swapstr x y v) (apm [(x,y)] a))``,
  REPEAT STRIP_TAC THEN
  `apm [(x,y)] (lamf v a) =
       fnpm apm apm [(x,y)] (lamf v) (apm [(x,y)] a)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `swapstr x y v = perm_of [(x,y)] v` by SRW_TAC [][] THEN
  POP_ASSUM SUBST1_TAC THEN MATCH_MP_TAC support_freshf THEN
  SRW_TAC [][])))

val limf_support_fresh = UNDISCH (UNDISCH (prove(
  ``^limf_support_t ==> is_perm apm ==>
    !x y v n a1 a2.
       ~(x IN A) /\ ~(y IN A) ==>
       (apm [(x,y)] (limf n v a1 a2) =
          limf n (swapstr x y v) (apm [(x,y)] a1) (apm [(x,y)] a2))``,
  REPEAT STRIP_TAC THEN
  `apm [(x,y)] (limf n v a1 a2) =
       fnpm apm apm [(x,y)] (limf n v a1) (apm [(x,y)] a2)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `fnpm apm apm [(x,y)] (limf n v a1) =
       fnpm apm (fnpm apm apm) [(x,y)] (limf n v) (apm [(x,y)] a1)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `fnpm apm (fnpm apm apm) [(x,y)] (limf n v) =
       fnpm perm_of (fnpm apm (fnpm apm apm)) [(x,y)] (limf n)
            (swapstr x y v)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  `fnpm perm_of (fnpm apm (fnpm apm apm)) [(x,y)] (limf n) =
     ^limf_pm [(x,y)] limf n`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  METIS_TAC [support_def])));

val h_supp_t = ``supp (fnpm perm_of apm) ^h``
val i_supp_t = ``supp (fnpm perm_of (fnpm apm apm)) ^i``

val ctxt00 = ``^lamf_support_t /\ ^limf_support_t /\ FINITE A /\ is_perm apm``
val ctxt_s_supp =
    ``support (fnpm (cpmpm) apm) s sS /\ FINITE sS``
val ctxt_s12_supp =
    ``support (fnpm (cpmpm) apm) s1 sS1 /\
      FINITE sS1 /\
      support (fnpm (cpmpm) apm) s2 sS2 /\
      FINITE sS2``

val ssupport_fresh = UNDISCH (UNDISCH (prove(
  ``support (fnpm (cpmpm) apm) s sS ==>
    is_perm apm ==>
    !x y p.
      ~(x IN sS) /\ ~(y IN sS) ==>
      (apm [(x,y)] (s p) = s (cpmpm [(x,y)] p))``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (Q.GEN `A` support_freshf) THEN Q.EXISTS_TAC `sS` THEN
  SRW_TAC [][])));

val s1support_fresh = Q.INST [`s` |-> `s1`, `sS` |-> `sS1`] ssupport_fresh
val s2support_fresh = Q.INST [`s` |-> `s2`, `sS` |-> `sS2`] ssupport_fresh

val h_supported_by = prove(
  ``!a s sS pi.
       ^ctxt00 /\ ^ctxt_s_supp ==>
       support (fnpm perm_of apm) ^h (a INSERT (A UNION patoms pi UNION sS))``,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASSUME_TAC [lamf_support_fresh, ssupport_fresh] THEN
  SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, listpm_APPENDlist]);
val i_supported_by = prove(
  ``!a s1 s2 sS1 sS2 pi.
       ^ctxt00 /\ ^ctxt_s_supp ==>
       support (fnpm perm_of (fnpm apm apm)) ^i
               (a INSERT A UNION patoms pi UNION sS)``,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASSUME_TAC [limf_support_fresh, ssupport_fresh] THEN
  SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, listpm_APPENDlist,
             is_perm_sing_inv]);

val _ = print "Proving cond16 implies freshness ok... "
val cond16 = ``?a'. ~(a' IN A) /\ !x. ~(a' IN supp apm (^lamf a' x))``
val cond16i = ``?a'. ~(a' IN A) /\
                      !n x. ~(a' IN supp (fnpm apm apm) (^limf n a' x))``

val cond16_implies_freshness_ok = prove(
  ``!a s A sS.
       ^ctxt00 /\ ^ctxt_s_supp /\ ^cond16 ==>
       ?a'. ~(a' IN ^h_supp_t) /\ ~(a' IN supp apm (^h a'))``,
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `h = ^h` THEN
  `!a'' x. ~(a'' IN A) /\ ~(a' = a'') ==>
           ~(a'' IN supp apm (lamf a'' (apm [(a',a'')] x)))`
      by (REPEAT GEN_TAC THEN STRIP_TAC THEN
          `lamf a'' = fnpm apm apm [(a',a'')] (lamf a')`
              by SRW_TAC [][fnpm_def, FUN_EQ_THM, is_perm_sing_inv,
                            lamf_support_fresh] THEN
          SRW_TAC [][fnpm_def, is_perm_sing_inv, perm_supp]) THEN
  Q_TAC (NEW_TAC "a''") `{a;a'} UNION A UNION sS UNION patoms pi` THEN
  `support (fnpm perm_of apm) h (a INSERT A UNION patoms pi UNION sS)`
     by (UNABBREV_ALL_TAC THEN MATCH_MP_TAC h_supported_by THEN
         SRW_TAC [][]) THEN
  Q.EXISTS_TAC `a''` THEN SRW_TAC [][] THENL [
    `~(a'' IN a INSERT A UNION patoms pi UNION sS)` by SRW_TAC [][] THEN
    `FINITE (a INSERT A UNION patoms pi UNION sS)` by SRW_TAC [][] THEN
    METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm, perm_of_is_perm],
    Q.UNABBREV_TAC `h` THEN
    FIRST_X_ASSUM
      (Q.SPECL_THEN [`a''`, `apm [(a',a'')] (s (pi ++ [(a'',a)]))`]
         MP_TAC) THEN
    SRW_TAC [][is_perm_sing_inv]
  ]);

val cond16i_implies_freshness_ok = prove(
  ``!a s sS A.
       ^ctxt00 /\ ^ctxt_s_supp /\ ^cond16i ==>
       ?a'. ~(a' IN ^i_supp_t) /\ ~(a' IN supp (fnpm apm apm) (^i a'))``,
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `i = ^i` THEN
  `!a'' n x. ~(a'' IN A) /\ ~(a' = a'') ==>
             ~(a'' IN supp (fnpm apm apm) (limf n a'' (apm [(a',a'')] x)))`
      by (REPEAT GEN_TAC THEN STRIP_TAC THEN
          `limf n' a'' = fnpm apm (fnpm apm apm) [(a',a'')] (limf n' a')`
              by SRW_TAC [][fnpm_def, FUN_EQ_THM, is_perm_sing_inv,
                            limf_support_fresh] THEN
          SRW_TAC [][fnpm_def, is_perm_sing_inv, perm_supp]) THEN
  Q_TAC (NEW_TAC "a''") `{a;a'} UNION A UNION sS UNION patoms pi` THEN
  `support (fnpm perm_of (fnpm apm apm)) i
           (a INSERT A UNION patoms pi UNION sS)`
     by (UNABBREV_ALL_TAC THEN MATCH_MP_TAC i_supported_by THEN
         SRW_TAC [][]) THEN
  Q.EXISTS_TAC `a''` THEN SRW_TAC [][] THENL [
    `~(a'' IN a INSERT A UNION patoms pi UNION sS)`
       by SRW_TAC [][] THEN
    `FINITE (a INSERT A UNION patoms pi UNION sS)`
       by SRW_TAC [][] THEN
    METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm, perm_of_is_perm],
    Q.UNABBREV_TAC `i` THEN
    FIRST_X_ASSUM
      (Q.SPECL_THEN [`a''`, `n`, `apm [(a',a'')] (s (pi ++ [(a'',a)]))`]
         MP_TAC) THEN
    SRW_TAC [][is_perm_sing_inv]
  ]);
val _ = print "done\n"

val base =
    SPECL [``\(s:string) p. vr (perm_of p s) : 'a``]
          (INST_TYPE [alpha |-> ``:(string # string) list -> 'a``]
                     (TypeBase.axiom_of ``:prelterm$l0term``))
val full0 = Q.SPECL [`\t u r1 r2 p. ap (r1 p) (r2 p)`,
                    `\a t s pi. fresh apm ^h`,
                    `\n a t1 t2 s s2 pi. fresh (fnpm apm apm) ^i (s2 pi)`] base

val full = SIMP_RULE (srw_ss()) [FUN_EQ_THM] full0

val fndefn = #2 (dest_exists (concl full))

val swapstr_perm_of = store_thm(
  "swapstr_perm_of",
  ``swapstr x y (perm_of pi s) =
    perm_of (cpmpm [(x,y)] pi) (swapstr x y s)``,
  Induct_on `pi` THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, listpm_def, pairpm_def] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN SRW_TAC [][]);

val _ = print "Proving function is supported by set A... "
val rawfinite_support = prove(
  ``^fndefn /\ ^ctxt00 /\ ^cond16 /\ ^cond16i /\ ^var_support_t /\
    ^app_support_t ==>
    support (fnpm ptpm (fnpm (cpmpm) apm)) fn A``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] THEN
  Q_TAC SUFF_TAC
        `!t pi x y.  ~(x IN A) /\ ~(y IN A) ==>
                     (apm [(x,y)] (fn (ptpm [(x,y)] t) (cpmpm [(x,y)] pi)) =
                      fn t pi)`
        THEN1 PROVE_TAC [] THEN
  Induct THENL [
    SRW_TAC [][fnpm_def] THEN
    `(!s. apm [(x,y)] (vr s) = vr (perm_of [(x,y)] s))`
        by (MATCH_MP_TAC support_freshf THEN SRW_TAC [][]) THEN
    SRW_TAC [][swapstr_perm_of, is_perm_sing_inv],

    SRW_TAC [][fnpm_def] THEN
    `!a b pi. apm pi (ap a b) =
              fnpm apm apm pi (ap a) (apm pi b)`
        by SRW_TAC [][fnpm_def, is_perm_inverse] THEN
    SRW_TAC [][] THEN
    `!t. fnpm apm apm [(x,y)] (ap t) = ap (apm [(x,y)] t)`
        by (MATCH_MP_TAC support_freshf THEN SRW_TAC [][]) THEN
    SRW_TAC [][],

    ASM_SIMP_TAC (srw_ss()) [fnpm_def] THEN
    Q.X_GEN_TAC `s` THEN SRW_TAC [][] THEN
    Q.MATCH_ABBREV_TAC `apm [(x,y)] (fresh apm g) = fresh apm h` THEN
    `h = fnpm perm_of apm [(x,y)] g`
       by (MAP_EVERY Q.UNABBREV_TAC [`g`, `h`] THEN
           SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `a` THEN
           SRW_TAC [][fnpm_def, lamf_support_fresh] THEN
           `cpmpm [(x,y)] pi ++ [(swapstr x y a, swapstr x y s)] =
                cpmpm [(x,y)] (pi ++ [(a,s)])`
              by SRW_TAC [][listpm_APPENDlist] THEN
           SRW_TAC [][]) THEN
    POP_ASSUM (fn th =>
                  Q_TAC SUFF_TAC `fcond apm h` THEN1
                        SRW_TAC [][fresh_equivariant, is_perm_eql,
                                   is_perm_sing_inv, th]) THEN
    UNABBREV_ALL_TAC THEN
    `support (fnpm (cpmpm) apm) (fn t) (A UNION allatoms t)`
       by (SIMP_TAC (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] THEN
           MAP_EVERY Q.X_GEN_TAC [`c`, `d`] THEN REPEAT STRIP_TAC THEN
           `!x. apm [(c,d)] (fn t x) =
                fnpm (cpmpm) apm [(c,d)] (fn t) (cpmpm [(c,d)] x)`
             by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
           SRW_TAC [][is_perm_sing_inv] THEN
           `fnpm (cpmpm) apm [(c,d)] (fn t) =
            fnpm ptpm (fnpm (cpmpm) apm) [(c,d)] fn
                 (ptpm [(c,d)] t)`
             by SRW_TAC [][fnpm_def] THEN
           `ptpm [(c,d)] t = t`
             by PROVE_TAC [allatoms_supports, support_def] THEN
           SRW_TAC [][] THEN
           NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN SRW_TAC [][fnpm_def]) THEN
    Q.ABBREV_TAC `bigA = A UNION allatoms t UNION patoms pi` THEN
    `support (fnpm perm_of (fnpm apm apm)) lamf bigA /\
     support (fnpm (cpmpm) apm) (fn t) bigA /\
     support (cpmpm) pi bigA`
       by FULL_SIMP_TAC (srw_ss()) [support_def, Abbr`bigA`] THEN
    SRW_TAC [][fcond_def] THENL [
      Q.MATCH_ABBREV_TAC `FINITE (supp pm h)` THEN
      Q_TAC SUFF_TAC `?X. FINITE X /\ support pm h X`
            THEN1 METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                             perm_of_is_perm] THEN
      Q.EXISTS_TAC `s INSERT A UNION patoms pi UNION (A UNION allatoms t)` THEN
      SRW_TAC [][Abbr`bigA`, Abbr`h`, Abbr`pm`] THEN
      MATCH_MP_TAC h_supported_by THEN
      SRW_TAC [][],

      MATCH_MP_TAC (BETA_RULE cond16_implies_freshness_ok) THEN
      MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t`] THEN
      SRW_TAC [][] THEN METIS_TAC []
    ],

    Q.X_GEN_TAC `s` THEN SRW_TAC [][fnpm_def] THEN
    Q.MATCH_ABBREV_TAC
      `apm [(x,y)] (fresh (fnpm apm apm) g arg1) =
       fresh (fnpm apm apm) h arg2` THEN
    `h = fnpm perm_of (fnpm apm apm) [(x,y)] g`
       by (MAP_EVERY Q.UNABBREV_TAC [`g`, `h`] THEN
           SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `a` THEN
           SRW_TAC [][fnpm_def, limf_support_fresh, is_perm_sing_inv] THEN
           `cpmpm [(x,y)] pi ++ [(swapstr x y a, swapstr x y s)] =
                cpmpm [(x,y)] (pi ++ [(a,s)])`
              by SRW_TAC [][listpm_APPENDlist, listpm_def, pairpm_def] THEN
           SRW_TAC [][]) THEN
    `arg2 = apm [(x,y)] arg1` by SRW_TAC [][Abbr`arg1`, Abbr`arg2`,
                                            is_perm_sing_inv] THEN
    Q.PAT_ASSUM `h = foo` (fn th =>
                  Q_TAC SUFF_TAC `fcond (fnpm apm apm) h` THEN1
                        (`apm [(x,y)] (fresh (fnpm apm apm) g arg1) =
                          fnpm apm apm [(x,y)] (fresh (fnpm apm apm) g)
                                               (apm [(x,y)] arg1)`
                             by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN

                         SRW_TAC [][fresh_equivariant, th])) THEN
    UNABBREV_ALL_TAC THEN
    `support (fnpm (cpmpm) apm) (fn t)
             (A UNION allatoms t)`
       by (SIMP_TAC (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def] THEN
           MAP_EVERY Q.X_GEN_TAC [`c`, `d`] THEN REPEAT STRIP_TAC THEN
           `!x. apm [(c,d)] (fn t x) =
                fnpm (cpmpm) apm [(c,d)] (fn t)
                     (cpmpm [(c,d)] x)`
             by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
           SRW_TAC [][is_perm_sing_inv] THEN
           `fnpm (cpmpm) apm [(c,d)] (fn t) =
            fnpm ptpm (fnpm (cpmpm) apm) [(c,d)] fn
                 (ptpm [(c,d)] t)`
             by SRW_TAC [][fnpm_def] THEN
           `ptpm [(c,d)] t = t`
             by PROVE_TAC [allatoms_supports, support_def] THEN
           SRW_TAC [][] THEN
           NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN SRW_TAC [][fnpm_def]) THEN
    Q.ABBREV_TAC `bigA = A UNION allatoms t UNION patoms pi` THEN
    `support (fnpm perm_of (fnpm apm apm)) lamf bigA /\
     support (fnpm (cpmpm) apm) (fn t) bigA /\
     support (cpmpm) pi bigA`
       by FULL_SIMP_TAC (srw_ss()) [support_def, Abbr`bigA`] THEN
    SRW_TAC [][fcond_def] THENL [
      Q.MATCH_ABBREV_TAC `FINITE (supp pm h)` THEN
      Q_TAC SUFF_TAC `?X. FINITE X /\ support pm h X`
            THEN1 METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                             perm_of_is_perm] THEN
      Q.EXISTS_TAC
        `s INSERT A UNION patoms pi UNION (A UNION allatoms t)` THEN
      SRW_TAC [][Abbr`bigA`, Abbr`h`, Abbr`pm`] THEN
      MATCH_MP_TAC i_supported_by THEN
      SRW_TAC [][],

      MATCH_MP_TAC (BETA_RULE cond16i_implies_freshness_ok) THEN
      MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms t`, `A`] THEN
      SRW_TAC [][] THEN METIS_TAC []
    ]
  ]);
val _ = print "done\n"

val eqperms_ok = prove(
  ``^fndefn ==>
    !t p1 p2. (p1 == p2) ==> (fn t p1 = fn t p2)``,
  STRIP_TAC THEN Induct THENL [
    FULL_SIMP_TAC (srw_ss()) [permeq_def],
    METIS_TAC [],
    MAP_EVERY Q.X_GEN_TAC [`s`, `p1`, `p2`] THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `!a. fn t (p1 ++ [(a,s)]) = fn t (p2 ++ [(a,s)])` THEN1
          SRW_TAC [][] THEN
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC app_permeq_monotone THEN
    SRW_TAC [][permeq_refl],
    MAP_EVERY Q.X_GEN_TAC [`s`, `n`, `p1`, `p2`] THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `(!a. fn t (p1 ++ [(a,s)]) = fn t (p2 ++ [(a,s)])) /\
                    (fn t' p1 = fn t' p2)` THEN1 SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC app_permeq_monotone THEN SRW_TAC [][permeq_refl]
  ]);

val fn_support_fresh = UNDISCH (UNDISCH (prove(
  ``support (fnpm ptpm (fnpm (cpmpm) apm)) fn A ==>
    is_perm apm ==>
    !x y M p.
       ~(x IN A) /\ ~(y IN A) ==>
       (apm [(x,y)] (fn M p) =
          fn (ptpm [(x,y)] M) (cpmpm [(x,y)] p))``,
  REPEAT STRIP_TAC THEN
  `apm [(x,y)] (fn M p) =
       fnpm (cpmpm) apm [(x,y)] (fn M)
            (cpmpm [(x,y)] p)`
     by SRW_TAC [][fnpm_def, is_perm_sing_inv] THEN
  SRW_TAC [][] THEN AP_THM_TAC THEN
  MATCH_MP_TAC support_freshf THEN SRW_TAC [][])))

val _ = print "Proving that permutations can be re-arranged... "
val perms_move = prove(
  ``^fndefn /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\ ^cond16i /\
    ^ctxt00 ==>
    !t p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)``,
  STRIP_TAC THEN Induct THEN
  TRY (SRW_TAC [][lswapstr_APPEND] THEN
       SRW_TAC [][GSYM lswapstr_APPEND] THEN NO_TAC)
  THENL [
    MAP_EVERY Q.X_GEN_TAC [`s`, `p1`, `p2`] THEN SRW_TAC [][] THEN
    Q.MATCH_ABBREV_TAC `fresh apm f = fresh apm g` THEN
    `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
       by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    ASSUME_TAC fn_support_fresh THEN
    Q.ABBREV_TAC
      `bigS = s INSERT A UNION allatoms t UNION patoms p1 UNION patoms p2` THEN
    ASSUME_TAC allatoms_fresh THEN
    ASSUME_TAC lamf_support_fresh THEN
    Q.PAT_ASSUM `!p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)` (K ALL_TAC) THEN
    `support (fnpm perm_of apm) f bigS /\ support (fnpm perm_of apm) g bigS`
       by (SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, Abbr`f`, Abbr`g`,
                      Abbr`bigS`, listpm_APPENDlist, listpm_def, pairpm_def] THEN
           SRW_TAC [][swapstr_perm_of, swapstr_def]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `?b. ~(b IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(b IN supp (fnpm perm_of apm) f) /\ ~(b IN supp (fnpm perm_of apm) g)`
        by METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `FINITE (supp (fnpm perm_of apm) f) /\ FINITE (supp (fnpm perm_of apm) g)`
        by METIS_TAC [supp_smallest, SUBSET_FINITE, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `fcond apm f /\ fcond apm g`
        by (SRW_TAC [][fcond_def] THENL [
              `f = \c. lamf c ((\p. fn t (p ++ p2)) (p1 ++ [(c, perm_of p2 s)]))`
                 by SRW_TAC [][Abbr`f`] THEN
              POP_ASSUM SUBST1_TAC THEN
              MATCH_MP_TAC cond16_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC
                        [`A`, `A UNION allatoms t UNION patoms p2`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, listpm_APPENDlist,
                           is_perm_sing_inv],
                METIS_TAC []
              ],
              Q.UNABBREV_TAC `g` THEN
              MATCH_MP_TAC cond16_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def,
                           is_perm_sing_inv],
                METIS_TAC []
              ]
            ]) THEN
    `(fresh apm f = f b) /\ (fresh apm g = g b)` by METIS_TAC [fresh_thm] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`] THEN
    Q_TAC SUFF_TAC `p1 ++ [(b,perm_of p2 s)] ++ p2 == p1 ++ p2 ++ [(b,s)]`
          THEN1 (STRIP_TAC THEN
                 Q_TAC SUFF_TAC
                       `fn t (p1 ++ [(b,perm_of p2 s)] ++ p2) =
                        fn t (p1 ++ p2 ++ [(b,s)])` THEN1 SRW_TAC [][] THEN
                 MP_TAC eqperms_ok THEN SRW_TAC [][]) THEN
    REWRITE_TAC [GSYM listTheory.APPEND_ASSOC] THEN
    MATCH_MP_TAC app_permeq_monotone THEN
    SRW_TAC [][permeq_refl] THEN
    `(perm_of p2 b, perm_of p2 s) :: p2 == p2 ++ [(b,s)]`
        by METIS_TAC [permeq_swap_ends, permeq_sym] THEN
    Q_TAC SUFF_TAC `perm_of p2 b = b` THEN1 METIS_TAC [] THEN
    `~(b IN patoms p2)` by FULL_SIMP_TAC (srw_ss()) [Abbr`bigS`] THEN
    SRW_TAC [][perm_of_unchanged],

    MAP_EVERY Q.X_GEN_TAC [`s`, `n`, `p1`, `p2`] THEN SRW_TAC [][] THEN
    AP_THM_TAC THEN
    Q.MATCH_ABBREV_TAC `fresh (fnpm apm apm) f = fresh (fnpm apm apm) g` THEN
    `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
       by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    ASSUME_TAC fn_support_fresh THEN
    Q.ABBREV_TAC
      `bigS = s INSERT A UNION allatoms t UNION patoms p1 UNION patoms p2` THEN
    ASSUME_TAC limf_support_fresh THEN
    Q.PAT_ASSUM `!p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)` (K ALL_TAC) THEN
    Q.PAT_ASSUM `!p1 p2. fn (ptpm p2 t') p1 = fn t' (p1 ++ p2)`
                (K ALL_TAC) THEN
    `support (fnpm perm_of (fnpm apm apm)) f bigS /\
     support (fnpm perm_of (fnpm apm apm)) g bigS`
       by (SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, Abbr`f`, Abbr`g`,
                      Abbr`bigS`, listpm_APPENDlist, listpm_def, pairpm_def,
                      allatoms_fresh] THEN
           SRW_TAC [][swapstr_perm_of, swapstr_def, is_perm_sing_inv]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `?b. ~(b IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(b IN supp (fnpm perm_of (fnpm apm apm)) f) /\
     ~(b IN supp (fnpm perm_of (fnpm apm apm)) g)`
        by METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `FINITE (supp (fnpm perm_of (fnpm apm apm)) f) /\
     FINITE (supp (fnpm perm_of (fnpm apm apm)) g)`
        by METIS_TAC [supp_smallest, SUBSET_FINITE, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `fcond (fnpm apm apm) f /\ fcond (fnpm apm apm) g`
        by (SRW_TAC [][fcond_def] THENL [
              `f = \c. limf n c
                          ((\p. fn t (p ++ p2)) (p1 ++ [(c, perm_of p2 s)]))`
                 by SRW_TAC [][Abbr`f`] THEN
              POP_ASSUM SUBST1_TAC THEN
              MATCH_MP_TAC cond16i_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC
                        [`A UNION allatoms t UNION patoms p2`, `A`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, listpm_APPENDlist,
                           is_perm_sing_inv, allatoms_fresh],
                METIS_TAC []
              ],
              Q.UNABBREV_TAC `g` THEN
              MATCH_MP_TAC cond16i_implies_freshness_ok THEN
              MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms t`, `A`] THEN
              SRW_TAC [][] THENL [
                SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def,
                           is_perm_sing_inv, allatoms_fresh],
                METIS_TAC []
              ]
            ]) THEN
    `(fresh (fnpm apm apm) f = f b) /\ (fresh (fnpm apm apm) g = g b)`
       by METIS_TAC [fresh_thm] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`] THEN
    Q_TAC SUFF_TAC `p1 ++ [(b,perm_of p2 s)] ++ p2 == p1 ++ p2 ++ [(b,s)]`
          THEN1 (STRIP_TAC THEN
                 Q_TAC SUFF_TAC
                       `fn t (p1 ++ [(b,perm_of p2 s)] ++ p2) =
                        fn t (p1 ++ p2 ++ [(b,s)])` THEN1 SRW_TAC [][] THEN
                 MP_TAC eqperms_ok THEN SRW_TAC [][]) THEN
    REWRITE_TAC [GSYM listTheory.APPEND_ASSOC] THEN
    MATCH_MP_TAC app_permeq_monotone THEN
    SRW_TAC [][permeq_refl] THEN
    `(perm_of p2 b, perm_of p2 s) :: p2 == p2 ++ [(b,s)]`
        by METIS_TAC [permeq_swap_ends, permeq_sym] THEN
    Q_TAC SUFF_TAC `perm_of p2 b = b` THEN1 METIS_TAC [] THEN
    `~(b IN patoms p2)` by FULL_SIMP_TAC (srw_ss()) [Abbr`bigS`] THEN
    SRW_TAC [][perm_of_unchanged]
  ]);
val _ = print "done\n"

val _ = print "Proving that the function respects alpha-equivalence... "
val fn_respectful = prove(
  ``^fndefn /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\ ^cond16i /\
    ^ctxt00 /\
    aeq t1 t2 ==> !p. fn t1 p = fn t2 p``,
  STRIP_TAC THEN
  Q.UNDISCH_THEN `aeq t1 t2` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`t2`, `t1`] THEN
  HO_MATCH_MP_TAC alt_aeq_ind THEN SRW_TAC [][] THEN
  `!t p1 p2. fn (ptpm p1 t) p2 = fn t (p2 ++ p1)`
      by (MATCH_MP_TAC perms_move THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM (ASSUME_TAC o GSYM) THEN SRW_TAC [][] THENL [
    ALL_TAC,
    AP_THM_TAC
  ] THEN
  Q.MATCH_ABBREV_TAC `fresh somepm f = fresh somepm g` THEN
  `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
     by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
         METIS_TAC [])
  THENL [
    Q.UNABBREV_TAC `somepm` THEN
    Q.ABBREV_TAC
      `bigS = {u;v} UNION A UNION patoms p UNION allatoms t1 UNION
              allatoms t2` THEN
    `support (fnpm perm_of apm) f bigS /\ support (fnpm perm_of apm) g bigS`
       by (SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, Abbr`f`, Abbr`bigS`,
                      lamf_support_fresh, fn_support_fresh, Abbr`g`] THEN
           ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
           SRW_TAC [][] THEN SRW_TAC [][swapstr_def, allatoms_fresh]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `FINITE (supp (fnpm perm_of apm) f) /\ FINITE (supp (fnpm perm_of apm) g)`
       by METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                     perm_of_is_perm] THEN
    `fcond apm f /\ fcond apm g`
       by (SRW_TAC [][fcond_def] THENL [
             Q.UNABBREV_TAC `f`,
             Q.UNABBREV_TAC `g`
           ] THEN
           FIRST_X_ASSUM (ASSUME_TAC o GSYM o assert (is_forall o concl)) THEN
           POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
           MATCH_MP_TAC cond16_implies_freshness_ok THENL [
             MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t1`],
             MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t2`]
           ] THEN SRW_TAC [][] THEN
           SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, fn_support_fresh,
                      allatoms_fresh, is_perm_sing_inv] THEN
           METIS_TAC []) THEN
    `?z. ~(z IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(z IN supp (fnpm perm_of apm) f) /\ ~(z IN supp (fnpm perm_of apm) g)`
        by METIS_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `(fresh apm f = f z) /\ (fresh apm g = g z)` by METIS_TAC [fresh_thm] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`, is_perm_flip_args, Abbr`bigS`] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    Q.ABBREV_TAC
      `bigS = {u;v} UNION A UNION patoms p UNION allatoms M1 UNION
              allatoms M2` THEN
    `support (fnpm perm_of somepm) f bigS /\
     support (fnpm perm_of somepm) g bigS`
       by (SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, Abbr`f`, Abbr`bigS`,
                      limf_support_fresh, fn_support_fresh, Abbr`g`,
                      Abbr`somepm`, is_perm_sing_inv] THEN
           ONCE_REWRITE_TAC [GSYM ptpm_sing_to_back] THEN
           SRW_TAC [][] THEN SRW_TAC [][swapstr_def, allatoms_fresh]) THEN
    `FINITE bigS` by SRW_TAC [][Abbr`bigS`] THEN
    `FINITE (supp (fnpm perm_of somepm) f) /\
     FINITE (supp (fnpm perm_of somepm) g)`
       by METIS_TAC [SUBSET_FINITE, supp_smallest, fnpm_is_perm,
                     perm_of_is_perm] THEN
    `is_perm somepm` by SRW_TAC [][Abbr`somepm`] THEN
    `fcond somepm f /\ fcond somepm g`
       by (SRW_TAC [][fcond_def] THENL [
             Q.UNABBREV_TAC `f`,
             Q.UNABBREV_TAC `g`
           ] THEN
           FIRST_X_ASSUM (ASSUME_TAC o GSYM o assert (is_forall o concl)) THEN
           POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
           Q.UNABBREV_TAC `somepm` THEN
           MATCH_MP_TAC cond16i_implies_freshness_ok THENL [
             MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms M1`,`A`],
             MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms M2`,`A`]
           ] THEN SRW_TAC [][] THEN
           SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM, fn_support_fresh,
                      allatoms_fresh, is_perm_sing_inv] THEN
           METIS_TAC []) THEN
    `?z. ~(z IN bigS)` by METIS_TAC [NEW_def] THEN
    `~(z IN supp (fnpm perm_of somepm) f) /\
     ~(z IN supp (fnpm perm_of somepm) g)`
        by PROVE_TAC [supp_smallest, SUBSET_DEF, fnpm_is_perm,
                      perm_of_is_perm] THEN
    `(fresh somepm f = f z) /\ (fresh somepm g = g z)`
       by METIS_TAC [fresh_thm] THEN
    SRW_TAC [][Abbr`f`, Abbr`g`, is_perm_flip_args, Abbr`bigS`] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);
val _ = print "done\n"

val better_lam_clause0 = prove(
  ``^fndefn /\ ^ctxt00 /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\
    ^cond16i /\
    ~(z = v) /\ ~(z IN A) /\ ~(z IN allatoms t) ==>
    (fn (lam z (ptpm [(z,v)] t)) [] = lamf z (fn (ptpm [(z,v)] t) []))``,
  REPEAT STRIP_TAC THEN
  `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
  `aeq (lam z (ptpm [(z,v)] t)) (lam v t)` by SRW_TAC [][lam_aeq_thm] THEN
  `fn (lam z (ptpm [(z,v)] t)) [] = fn (lam v t) []`
     by (MATCH_MP_TAC fn_respectful THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THEN
  `!t p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)`
     by (MATCH_MP_TAC perms_move THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM (fn th => SIMP_TAC (srw_ss()) [th]) THEN
  Q.MATCH_ABBREV_TAC `fresh apm f = lamf z (fn t [(z,v)])` THEN
  `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
     by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
         METIS_TAC []) THEN
  Q.ABBREV_TAC `bigS = v INSERT A UNION allatoms t` THEN
  `support (fnpm perm_of apm) f bigS`
     by (SRW_TAC [][lamf_support_fresh, fn_support_fresh, support_def,
                    fnpm_def, FUN_EQ_THM, Abbr`f`, listpm_def, pairpm_def,
                    allatoms_fresh, Abbr`bigS`] THEN
         SRW_TAC [][swapstr_def]) THEN
  `FINITE bigS /\ ~(z IN bigS)` by SRW_TAC [][Abbr`bigS`] THEN
  `~(z IN supp (fnpm perm_of apm) f) /\ FINITE (supp (fnpm perm_of apm) f)`
      by METIS_TAC [supp_smallest, SUBSET_FINITE, SUBSET_DEF, fnpm_is_perm,
                    perm_of_is_perm] THEN
  Q_TAC SUFF_TAC `fcond apm f`
        THEN1 (STRIP_TAC THEN
               `fresh apm f = f z` by METIS_TAC [fresh_thm] THEN
               SRW_TAC [][Abbr`f`]) THEN
  SRW_TAC [][fcond_def] THEN
  Q.UNABBREV_TAC `f` THEN
  MATCH_MP_TAC ((REWRITE_RULE [listTheory.APPEND] o
                 Q.INST [`pi` |-> `[]`]) cond16_implies_freshness_ok) THEN
  MAP_EVERY Q.EXISTS_TAC [`A`, `A UNION allatoms t`] THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, fn_support_fresh,
               allatoms_fresh, is_perm_sing_inv],
    METIS_TAC []
  ]);

val silly_new_lemma = prove(
  ``~(x = NEW (x INSERT allatoms t)) /\
    ~(NEW (x INSERT allatoms t) IN allatoms t)``,
  Q.SPEC_THEN `x INSERT allatoms t` MP_TAC NEW_def THEN
  SRW_TAC [][]);

val better_lam_clause =
    (REWRITE_RULE [silly_new_lemma] o
     Q.INST [`v` |-> `NEW (z INSERT allatoms t)`] o
     REWRITE_RULE [] o
     SIMP_RULE pure_ss [ptpm_sing_inv, allatoms_perm, perm_IN,
                        perm_of_is_perm, listTheory.REVERSE_DEF,
                        listTheory.APPEND, lswapstr_def, pairTheory.FST,
                        pairTheory.SND, swapstr_def] o
     Q.INST [`t` |-> `ptpm [(z,v)] t`]) better_lam_clause0

val better_lami_clause0 = prove(
  ``^fndefn /\ ^ctxt00 /\ ^var_support_t /\ ^app_support_t /\ ^cond16 /\
    ^cond16i /\
    ~(z = v) /\ ~(z IN A) /\ ~(z IN allatoms t) ==>
    (fn (lami n z (ptpm [(z,v)] t) t') [] =
       limf n z (fn (ptpm [(z,v)] t) []) (fn t' []))``,
  REPEAT STRIP_TAC THEN
  `~(z IN fv t)` by METIS_TAC [SUBSET_DEF, fv_SUBSET_allatoms] THEN
  `aeq (lami n z (ptpm [(z,v)] t) t') (lami n v t t')`
     by SRW_TAC [][lami_aeq_thm] THEN
  `fn (lami n z (ptpm [(z,v)] t) t') [] = fn (lami n v t t') []`
     by (MATCH_MP_TAC fn_respectful THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THEN
  `!t p1 p2. fn (ptpm p2 t) p1 = fn t (p1 ++ p2)`
     by (MATCH_MP_TAC perms_move THEN SRW_TAC [][] THEN METIS_TAC []) THEN
  POP_ASSUM (fn th => SIMP_TAC (srw_ss()) [th]) THEN
  AP_THM_TAC THEN
  Q.MATCH_ABBREV_TAC `fresh spm f = limf n z (fn t [(z,v)])` THEN
  `support (fnpm ptpm (fnpm (cpmpm) apm)) fn A`
     by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
         METIS_TAC []) THEN
  Q.ABBREV_TAC `bigS = v INSERT A UNION allatoms t` THEN
  `support (fnpm perm_of spm) f bigS`
     by (SRW_TAC [][limf_support_fresh, fn_support_fresh, support_def,
                    fnpm_def, FUN_EQ_THM, Abbr`f`, listpm_def, pairpm_def,
                    allatoms_fresh, Abbr`bigS`, Abbr`spm`,
                    is_perm_sing_inv] THEN
         SRW_TAC [][swapstr_def]) THEN
  `FINITE bigS /\ ~(z IN bigS)` by SRW_TAC [][Abbr`bigS`] THEN
  `~(z IN supp (fnpm perm_of spm) f) /\ FINITE (supp (fnpm perm_of spm) f)`
      by PROVE_TAC [supp_smallest, SUBSET_FINITE, SUBSET_DEF, fnpm_is_perm,
                    perm_of_is_perm] THEN
  Q_TAC SUFF_TAC `fcond spm f`
        THEN1 (STRIP_TAC THEN
               `fresh spm f = f z` by METIS_TAC [fresh_thm] THEN
               SRW_TAC [][Abbr`f`]) THEN
  SRW_TAC [][fcond_def, Abbr`spm`] THEN
  Q.UNABBREV_TAC `f` THEN
  MATCH_MP_TAC ((REWRITE_RULE [listTheory.APPEND] o
                 Q.INST [`pi` |-> `[]`]) cond16i_implies_freshness_ok) THEN
  MAP_EVERY Q.EXISTS_TAC [`A UNION allatoms t`, `A`] THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][support_def, FUN_EQ_THM, fnpm_def, fn_support_fresh,
               allatoms_fresh, is_perm_sing_inv],
    METIS_TAC []
  ]);

val better_lami_clause =
    (REWRITE_RULE [silly_new_lemma] o
     Q.INST [`v` |-> `NEW (z INSERT allatoms t)`] o
     REWRITE_RULE [] o
     SIMP_RULE pure_ss [ptpm_sing_inv, allatoms_perm, perm_IN,
                        perm_of_is_perm, listTheory.REVERSE_DEF,
                        listTheory.APPEND, lswapstr_def, pairTheory.FST,
                        pairTheory.SND, swapstr_def] o
     Q.INST [`t` |-> `ptpm [(z,v)] t`]) better_lami_clause0

val recursion0 = prove(
  ``^cond16 /\ ^cond16i /\ ^ctxt00 /\ ^var_support_t /\ ^app_support_t ==>
    ?f :: respects (aeq ===> (=)).
        ((!s. f (var s) = vr s) /\
         (!t1 t2. f (app t1 t2) = ap (f t1) (f t2)) /\
         (!v t. ~(v IN A) ==> (f (lam v t) = lamf v (f t))) /\
         (!n v t1 t2. ~(v IN A) ==>
                      (f (lami n v t1 t2) = limf n v (f t1) (f t2)))) /\
        (!x y t. ~(x IN A) /\ ~(y IN A) ==>
                 (f (ptpm [(x,y)] t) = apm [(x,y)] (f t)))``,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC full THEN
  SRW_TAC [][RES_EXISTS_THM, quotientTheory.IN_RESPECTS,
             quotientTheory.FUN_REL] THEN
  Q.EXISTS_TAC `\t. fn t []` THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][] THEN MATCH_MP_TAC fn_respectful THEN
    SRW_TAC [][] THEN METIS_TAC [],
    SRW_TAC [][],
    SRW_TAC [][],
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC better_lam_clause THEN SRW_TAC [][] THEN METIS_TAC [],
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC better_lami_clause THEN SRW_TAC [][] THEN METIS_TAC [],
    `support (fnpm ptpm (fnpm cpmpm apm)) fn A`
       by (MATCH_MP_TAC rawfinite_support THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    ASSUME_TAC fn_support_fresh THEN
    SRW_TAC [][]
  ]);

fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = NONE, fname = s, func = t};

(* some trivialities that are either needed for the lifting, or which are
   wanted to be part of it *)
val lam_respects_aeq = prove(
  ``!v t1 t2. aeq t1 t2 ==> aeq (lam v t1) (lam v t2)``,
  SRW_TAC [][lam_aeq_thm]);

val app_respects_aeq = prove(
  ``!M1 M2 N1 N2. aeq M1 M2 /\ aeq N1 N2 ==> aeq (app M1 N1) (app M2 N2)``,
  SRW_TAC [][aeq_rules]);

val var_respects_aeq = prove(
  ``!s1 s2. (s1 = s2) ==> aeq (var s1) (var s2)``,
  SRW_TAC [][]);

val lami_respects_aeq = prove(
  ``!n v M1 M2 N1 N2. aeq M1 M2 /\ aeq N1 N2 ==>
                      aeq (lami n v M1 N1) (lami n v M2 N2)``,
  SRW_TAC [][lami_aeq_thm]);
val aeq_app_11 = SIMP_RULE (srw_ss()) []
                           (Q.INST [`v` |-> `app t' u'`] aeq_app_inversion)
val aeq_var_11 = prove(
  ``aeq (var s1) (var s2) = (s1 = s2)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][] THEN METIS_TAC []);






val [FV_thm, simple_lterm_induction, ltpm_thm, LAM_distinct, lterm_11,
     LAM_eq_thm, LAMi_eq_thm, FRESH_swap0,
     (* tpm_is_perm,*) ltm_recursion, FINITE_FV,
     ltpm_sing_inv, ltpm_NIL, ltpm_flip_args, ltpm_id_front, ltpm_FV,
     ltpm_inverse] =
    quotient.define_equivalence_type
    {
     name = "lterm", equiv = aeq_equiv,
     defs = map mk_def [("LAM", ``prelterm$lam``),
                        ("APP", ``prelterm$app``),
                        ("VAR", ``prelterm$var``),
                        ("LAMi", ``prelterm$lami``),
                        ("FV",  ``prelterm$fv``),
                        ("ltpm", ``prelterm$ptpm``)],
     welldefs = [lam_respects_aeq, app_respects_aeq, var_respects_aeq,
                 lami_respects_aeq, aeq_fv,
                 SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] aeq_ptpm_lemma
                 ],
     old_thms = [fv_def, TypeBase.induction_of ``:prelterm$l0term``,
                 ptpm_def,
                 aeq_distinct, CONJ aeq_var_11 aeq_app_11,
                 lam_aeq_thm, lami_aeq_thm, fresh_swap, (* ptpm_is_perm,*)
                 Q.INST [`lamf` |-> `lm`, `limf` |-> `li`] recursion0,
                 finite_fv,
                 ptpm_sing_inv, ptpm_NIL, ptpm_flip_args, ptpm_id_front,
                 ptpm_fv, ptpm_INVERSE]}

val _ = List.app (fn s => remove_ovl_mapping s {Name = s, Thy = "prelterm"})
                 ["app", "lam", "lami", "fv", "var", "ptpm"]

val _ = Save_Thm("ltpm_NIL", ltpm_NIL)

val ltpm_fresh = save_thm("ltpm_fresh", GSYM FRESH_swap0)

val _ = Save_Thm("lterm_distinct", LAM_distinct);
val _ = Save_Thm("lterm_11", lterm_11);
val _ = Save_Thm("ltpm_thm", ltpm_thm);
val _ = Save_Thm("FV_thm", FV_thm);
val _ = Save_Thm("FINITE_FV", FINITE_FV);
val _ = Save_Thm("ltpm_sing_inv", ltpm_sing_inv);
val _ = Save_Thm("ltpm_id_front", ltpm_id_front);
val _ = Save_Thm("ltpm_FV", ltpm_FV)
val _ = Save_Thm("ltpm_inverse", ltpm_inverse)

val _ = save_thm("lLAM_eq_thm", LAM_eq_thm);
val _ = save_thm("lLAMi_eq_thm", LAMi_eq_thm);
val _ = save_thm("ltm_recursion", ltm_recursion)

val _ = save_thm("ltpm_flip_args", ltpm_flip_args)
val _ = save_thm("simple_lterm_induction", simple_lterm_induction)

val ltpm_is_perm = Store_Thm(
  "ltpm_is_perm",
  ``is_perm ltpm``,
  SRW_TAC [][is_perm_def, FUN_EQ_THM, permeq_def] THEN
  Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][lswapstr_APPEND]);

(* properties of ltpm *)
val ltpm_eql = store_thm(
  "ltpm_eql",
  ``(ltpm pi t = u) = (t = ltpm (REVERSE pi) u)``,
  METIS_TAC [ltpm_inverse])
val ltpm_eqr = store_thm(
  "ltpm_eqr",
  ``(t = ltpm pi u) = (ltpm (REVERSE pi) t =  u)``,
  METIS_TAC [ltpm_inverse])
val ltpm_APPEND = store_thm(
  "ltpm_APPEND",
  ``ltpm (p1 ++ p2) t = ltpm p1 (ltpm p2 t)``,
  METIS_TAC [ltpm_is_perm, is_perm_def]);


(* alpha-convertibility *)
val ltpm_ALPHA = store_thm(
  "ltpm_ALPHA",
  ``~(v IN FV t) ==> (LAM u t = LAM v (ltpm [(v,u)] t))``,
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, ltpm_flip_args]);
val ltpm_ALPHAi = store_thm(
  "ltpm_ALPHAi",
  ``~(v IN FV t) ==> (LAMi n u t M = LAMi n v (ltpm [(v,u)] t) M)``,
  SRW_TAC [boolSimps.CONJ_ss][LAMi_eq_thm, ltpm_flip_args]);

val subst_lemma = prove(
  ``~(y = v) /\ ~(x = v) /\ ~(x IN FV N) /\ ~(y IN FV N) ==>
    (ltpm [(x,y)] (if swapstr x y s = v then N else VAR (swapstr x y s)) =
     (if s = v then N else VAR s))``,
  SRW_TAC [][swapstr_eq_left, ltpm_fresh]);

val ltpm_apart = store_thm(
  "ltpm_apart",
  ``!t. ~(x IN FV t) /\ (y IN FV t) ==> ~(ltpm [(x,y)] t = t)``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    SRW_TAC [][LAM_eq_thm] THEN
    Cases_on `x = s` THEN SRW_TAC [][swapstr_def],
    SRW_TAC [][swapstr_def, LAM_eq_thm],
    SRW_TAC [][LAMi_eq_thm] THEN
    Cases_on `x = s` THEN SRW_TAC [][swapstr_def],
    SRW_TAC [][LAMi_eq_thm],
    SRW_TAC [][LAMi_eq_thm, swapstr_def],
    SRW_TAC [][LAMi_eq_thm, swapstr_def]
  ]);

val supp_tpm = Store_Thm(
  "supp_tpm",
  ``supp ltpm = FV``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def, ltpm_fresh] THEN
  METIS_TAC [ltpm_apart, ltpm_flip_args]);

val silly_lemma = prove(``?x. ~(x = y) /\ ~(x IN FV M)``,
                        Q.SPEC_THEN `y INSERT FV M` MP_TAC NEW_def THEN
                        SRW_TAC [][] THEN METIS_TAC [])

val supp_partial_LAMi = prove(
  ``supp (fnpm ltpm ltpm) (LAMi n a t) = FV t DELETE a``,
  MATCH_MP_TAC supp_unique_apart THEN
  SRW_TAC [][FUN_EQ_THM, support_def, fnpm_def, LAMi_eq_thm] THEN
  SRW_TAC [][ltpm_fresh] THENL [
    Cases_on `a = x` THEN1 SRW_TAC [][swapstr_def, ltpm_fresh] THEN
    Cases_on `a = y` THEN SRW_TAC [][swapstr_def, ltpm_fresh],
    SRW_TAC [boolSimps.CONJ_ss][swapstr_def],
    SRW_TAC [boolSimps.CONJ_ss][swapstr_def, ltpm_flip_args],
    METIS_TAC [ltpm_apart, ltpm_flip_args],
    Cases_on `a = b` THEN SRW_TAC [][swapstr_def]
  ]);

val subst_exists =
    (SIMP_RULE (srw_ss()) [SKOLEM_THM, FORALL_AND_THM] o
     Q.GEN `N` o Q.GEN `x` o
     SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def, subst_lemma,
                           silly_lemma, supp_partial_LAMi] o
     Q.INST [`A` |-> `x INSERT FV N`, `apm` |-> `ltpm`,
             `vr` |-> `\s. if s = x then N else VAR s`,
             `ap` |-> `APP`,
             `lm` |-> `LAM`, `li` |-> `LAMi`] o
     SPEC_ALL o
     INST_TYPE [alpha |-> ``:lterm``]) ltm_recursion

val SUB_DEF = new_specification("lSUB_DEF", ["SUB"], subst_exists)

val _ = overload_on ("@@", ``APP``)

val lSUB_THM = Store_Thm(
  "lSUB_THM",
  ``([N/x] (VAR x) = N) /\ (~(x = y) ==> ([N/x] (VAR y) = VAR y)) /\
    ([N/x] (M @@ P) = [N/x] M @@ [N/x] P) /\
    (~(v IN FV N) /\ ~(v = x) ==> ([N/x] (LAM v M) = LAM v ([N/x] M))) /\
    (~(v IN FV N) /\ ~(v = x) ==>
        ([N/x] (LAMi n v M P) = LAMi n v ([N/x]M) ([N/x]P)))``,
  SRW_TAC [][SUB_DEF]);
val lSUB_VAR = store_thm(
  "lSUB_VAR",
  ``[N/x] (VAR s : lterm) = if s = x then N else VAR s``,
  SRW_TAC [][SUB_DEF]);

val lterm_bvc_induction = store_thm(
  "lterm_bvc_induction",
  ``!P X. FINITE X /\
          (!s. P (VAR s)) /\
          (!M N. P M /\ P N ==> P (APP M N)) /\
          (!v M. ~(v IN X) /\ P M ==> P (LAM v M)) /\
          (!n v M N. ~(v IN X) /\ ~(v IN FV N) /\ P M /\ P N ==>
                     P (LAMi n v M N)) ==>
          !t. P t``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t pi. P (ltpm pi t)` THEN1 METIS_TAC [ltpm_NIL] THEN
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  REPEAT CONJ_TAC THEN TRY (SRW_TAC [][] THEN NO_TAC) THENL [
    Q.X_GEN_TAC `t` THEN STRIP_TAC THEN
    MAP_EVERY Q.X_GEN_TAC [`s`, `pi`] THEN
    Q_TAC (NEW_TAC "z") `perm_of pi s INSERT FV (ltpm pi t) UNION X` THEN
    Q_TAC SUFF_TAC `LAM (perm_of pi s) (ltpm pi t) =
                    LAM z (ltpm [(z,perm_of pi s)] (ltpm pi t))`
          THEN1 SRW_TAC [][GSYM ltpm_APPEND] THEN
    SRW_TAC [][ltpm_ALPHA],
    MAP_EVERY Q.X_GEN_TAC [`t1`, `t2`] THEN STRIP_TAC THEN
    MAP_EVERY Q.X_GEN_TAC [`s`, `n`, `pi`] THEN
    Q_TAC (NEW_TAC "z")
          `perm_of pi s INSERT FV (ltpm pi t2) UNION X
           UNION FV (ltpm pi t1)` THEN
    Q_TAC SUFF_TAC
          `LAMi n (perm_of pi s) (ltpm pi t1) (ltpm pi t2) =
           LAMi n z (ltpm [(z,perm_of pi s)] (ltpm pi t1)) (ltpm pi t2)`
          THEN1 SRW_TAC [][GSYM ltpm_APPEND] THEN
    SRW_TAC [][ltpm_ALPHAi]
  ]);

val fresh_ltpm_subst = store_thm(
  "fresh_ltpm_subst",
  ``!t. ~(u IN FV t) ==> (ltpm [(u,v)] t = [VAR u/v] t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][] THEN SRW_TAC [][lSUB_VAR]);

val l14a = Store_Thm(
  "l14a",
  ``!t : lterm. [VAR v/v] t = t``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][lSUB_VAR]);

val l14b = store_thm(
  "l14b",
  ``!t:lterm. ~(v IN FV t) ==> ([u/v]t = t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SRW_TAC [][SUB_DEF]);

val l15a = store_thm(
  "l15a",
  ``!t:lterm. ~(v IN FV t) ==> ([u/v] ([VAR v/x] t) = [u/x] t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{x;v} UNION FV u` THEN
  SRW_TAC [][SUB_DEF]);

(* ----------------------------------------------------------------------
    set up lterm recursion (where recursive arguments are still available)
   ---------------------------------------------------------------------- *)

val ltm_precursion_ex =
  (UNDISCH o
   Q.INST [`VR` |-> `vr`, `AP` |-> `ap`, `LM` |-> `lm`, `LI` |-> `li`,
           `APM` |-> `apm`] o
   SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def, pairpm_def,
                         pairTheory.FORALL_PROD,
                         ASSUME ``is_perm (APM: 'a pm)``] o
   Q.INST [`vr` |-> `\s. (VR s, VAR s)`,
           `ap` |-> `\t u. (AP (FST t) (FST u) (SND t) (SND u),
                            SND t @@ SND u)`,
           `lm` |-> `\v t. (LM (FST t) v (SND t), LAM v (SND t))`,
           `li` |-> `\n v t u. (LI (FST t) (FST u) n v (SND t) (SND u),
                                LAMi n v (SND t) (SND u))`,
           `apm` |-> `pairpm APM ltpm`] o
   SPEC_ALL o
   INST_TYPE [alpha |-> ``:'a # lterm``]) ltm_recursion

val bod = #2 (dest_exists (concl ltm_precursion_ex))

val ltm_snd_res = prove(
  ``FINITE A ==> ^bod ==> !M. SND (f M) = M``,
  NTAC 2 STRIP_TAC THEN HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `A` THEN SRW_TAC [][])

val ltm_precursion_ex2 = prove(
  ``FINITE A ==> ^bod ==>
    ?f. ((!s. f (VAR s) = vr s) /\
         (!M N. f (M @@ N) = ap (f M) (f N) M N) /\
         (!v M. ~(v IN A) ==> (f (LAM v M) = lm (f M) v M)) /\
         (!n v M N. ~(v IN A) ==>
                       (f (LAMi n v M N) = li (f M) (f N) n v M N))) /\
        (!x y t. ~(x IN A) /\ ~(y IN A) ==>
                 (f (ltpm [(x,y)] t) = apm [(x,y)] (f t)))``,
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `FST o f` THEN SRW_TAC [][] THEN
  IMP_RES_TAC ltm_snd_res THEN SRW_TAC [][])

val supp_lemma = prove(
  ``is_perm apm ==> ((!x y t. f (ltpm [(x,y)] t) = apm [(x,y)] (f t)) =
                     (!pi t. f (ltpm pi t) = apm pi (f t)))``,
  SRW_TAC [][EQ_IMP_THM] THEN
  Q.ID_SPEC_TAC `t`  THEN Induct_on `pi` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, is_perm_nil] THEN
  MAP_EVERY Q.X_GEN_TAC [`a`,`b`,`M`] THEN
  `ltpm ((a,b)::pi) M = ltpm [(a,b)] (ltpm pi M)`
     by SRW_TAC [][GSYM tpm_APPEND] THEN SRW_TAC [][] THEN
  SRW_TAC [][GSYM is_perm_decompose]);

val ltm_recursion_nosideset = save_thm(
  "ltm_recursion_nosideset",
  (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, supp_lemma] o
   Q.INST [`A` |-> `{}`] o
   DISCH_ALL o
   CHOOSE(``f:lterm -> 'a # lterm``, ltm_precursion_ex) o UNDISCH o
   UNDISCH) ltm_precursion_ex2);

val term_info_string =
    "local\n\
    \fun k |-> v = {redex = k, residue = v}\n\
    \val term_info = \n\
    \   {nullfv = ``labelledTerms$LAM \"\" (VAR \"\")``,\n\
    \    pm_rewrites = [],\n\
    \    pm_constant = ``labelledTerms$ltpm``,\n\
    \    fv_rewrites = [],\n\
    \    fv_constant = ``labelledTerms$FV``,\n\
    \    recursion_thm = SOME ltm_recursion_nosideset,\n\
    \    binders = [(``labelledTerms$LAM``, 0, ltpm_ALPHA),\n\
    \               (``labelledTerms$LAMi``, 1, ltpm_ALPHAi)]}\n\
    \val _ = binderLib.type_db :=\n\
    \          Binarymap.insert(!binderLib.type_db, \n\
    \                           {Thy = \"labelledTerms\", Name=\"lterm\"},\n\
    \                           binderLib.NTI term_info)\n\
    \in end;\n"

val _ = adjoin_to_theory
        { sig_ps = NONE,
          struct_ps =
          SOME (fn pps => PP.add_string pps term_info_string)}




val _ = export_theory()

