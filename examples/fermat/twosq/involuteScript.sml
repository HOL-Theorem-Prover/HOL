(* ------------------------------------------------------------------------- *)
(* Involution: Basic                                                         *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "involute";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* arithmeticTheory -- load by default *)

(* val _ = load "helperTheory"; *)
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open helperTheory; (* for FUNPOW_closure *)

(* arithmeticTheory -- load by default *)
open arithmeticTheory pred_setTheory;


(* ------------------------------------------------------------------------- *)
(* Involution: Basic Documentation                                           *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   f endo s            = !x. x IN s ==> f x IN s
   f involute s        = !x. x IN s ==> f x IN s /\ (f (f x) = x)
*)
(*

   Helper Theorem:

   Involution:
   involute_endo         |- !f s. f involute s ==> f endo s
   involute_inj          |- !f s. f involute s ==> INJ f s s
   involute_surj         |- !f s. f involute s ==> SURJ f s s
   involute_bij          |- !f s. f involute s ==> f PERMUTES s
   involute_LINV         |- !f s. f involute s ==> LINV f s involute s
   involute_FUNPOW       |- !f A x n. f involute A /\ x IN A ==>
                                        (FUNPOW f n x = if EVEN n then x else f x)
   involute_FUNPOW_LINV  |- !f A x n. f involute A /\ x IN A ==>
                                        (FUNPOW (LINV f A) n x = FUNPOW f n x)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorem                                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Involution                                                                *)
(* ------------------------------------------------------------------------- *)

(* Overload on involution *)
(*
val _ = overload_on("involute", ``\f. f o f = I``);
val _ = clear_overloads_on "involute";
*)

(* An endofunction has its domain equal to its co-domain. *)
val _ = overload_on("endo", ``\f s. !x. x IN s ==> f x IN s``);
val _ = set_fixity "endo" (Infix(NONASSOC, 450)); (* same as relation *)

val _ = overload_on("involute", ``\f s. !x. x IN s ==> f x IN s /\ (f (f x) = x)``);
val _ = set_fixity "involute" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: f involute s ==> f endo s *)
(* Proof: by notation *)
val involute_endo = store_thm(
  "involute_endo",
  ``!f s. f involute s ==> f endo s``,
  simp[]);

(* Theorem: f involute s ==> INJ f s s *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) !x. x IN s ==> f x IN s, true    by f involute s.
   (2) !x y. x IN s /\ y IN s ==> f x = f y ==> x = y
               f x = f y
       ==> f (f x) = f (f y)     by f x IN s, f y IN s
       ==>       x = y           by f involute s
*)
val involute_inj = store_thm(
  "involute_inj",
  ``!f s. f involute s ==> INJ f s s``,
  metis_tac[INJ_DEF]);

(* Theorem: f involute s ==> SURJ f s s *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) !x. x IN s ==> f x IN s, true    by f involute s.
   (2) !x. x IN s ==> ?y. y IN s /\ f y = x
       Let y = f x, then y IN s         by f involute s
       and f y = f (f x) = x            by f involute s
*)
val involute_surj = store_thm(
  "involute_surj",
  ``!f s. f involute s ==> SURJ f s s``,
  prove_tac[SURJ_DEF]);

(* Theorem: f involute s ==> f PERMUTES s *)
(* Proof: by BIJ_DEF, involute_inj, involute_surj *)
val involute_bij = store_thm(
  "involute_bij",
  ``!f s. f involute s ==> f PERMUTES s``,
  rw[BIJ_DEF, involute_inj, involute_surj]);

(* Theorem: f involute s ==> (LINV f s) involute s *)
(* Proof:
       f involute s
   ==> f PERMUTES s                        by involute_bij
   ==> (LINV f s) PERMUTES s               by BIJ_LINV_BIJ
   Thus x IN s ==> LINV f s x IN s         by BIJ_ELEMENT
   Since f (f x) = x                       by involution
      so     f x = LINV f s x              by BIJ_LINV_THM
      or       x = LINV f s (LINV f s x)   by BIJ_LINV_THM
*)
val involute_LINV = store_thm(
  "involute_LINV",
  ``!f s. f involute s ==> (LINV f s) involute s``,
  ntac 3 strip_tac >>
  `f PERMUTES s /\ (LINV f s) PERMUTES s` by rw[involute_bij, BIJ_LINV_BIJ] >>
  rpt strip_tac >-
  metis_tac[BIJ_ELEMENT] >>
  metis_tac[BIJ_LINV_THM]);

(* Theorem: f involute A /\ x IN A ==>
            (FUNPOW f n x = if EVEN n then x else f x) *)
(* Proof:
   Note FUNPOW f 2 x
      = f (f x)                    by FUNPOW_2
      = x                          by involution
    ==> FUNPOW f (2 * k) x = x     by FUNPOW_MULTIPLE

   If EVEN n, then n = 2 * k       by EVEN_EXISTS
      Thus FUNPOW f (2 * k) x = x  by above
   If ~EVEN n, then ODD n.         by EVEN_ODD
      Thus n = SUC (2 * k)         by ODD_EXISTS
        FUNPOW f n x
      = FUNPOW f (SUC (2 * k)) x   by above
      = f (FUNPOW f (2 * k) x)     by FUNPOW_SUC
      = f x                        by above
*)
val involute_FUNPOW = store_thm(
  "involute_FUNPOW",
  ``!f A x n. f involute A /\ x IN A ==>
      (FUNPOW f n x = if EVEN n then x else f x)``,
  rpt strip_tac >>
  `FUNPOW f 2 x = x` by rw[FUNPOW_2] >>
  (imp_res_tac FUNPOW_MULTIPLE >> fs[]) >>
  (Cases_on `EVEN n` >> simp[]) >-
  metis_tac[EVEN_EXISTS] >>
  metis_tac[EVEN_ODD, ODD_EXISTS, FUNPOW_SUC]);

(* Theorem: f involute A /\ x IN A ==>
            (FUNPOW (LINV f A) n x = FUNPOW f n x) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f A) 0 x = FUNPOW f 0 x, true by FUNPOW_0
   Step: FUNPOW (LINV f A) n x = FUNPOW f n x ==>
         FUNPOW (LINV f A) (SUC n) x = FUNPOW f (SUC n) x
         Note f PERMUTES A                           by involute_bij
          and FUNPOW f n x IN A                      by FUNPOW_closure
         also FUNPOW f (SUC n) x IN A                by FUNPOW_closure
           FUNPOW (LINV f A) (SUC n) x
         = LINV f A (FUNPOW (LINV f A) n x)          by FUNPOW_SUC
         = LINV f A (FUNPOW f n x)                   by induction hypothesis
         = LINV f A (LINV f A (f (FUNPOW f n x)))    by BIJ_LINV_THM,
         = LINV f A (LINV f A (FUNPOW f (SUC n) x))  by FUNPOW_SUC
         = FUNPOW f (SUC n) x                        by involute_LINV
*)
val involute_FUNPOW_LINV = store_thm(
  "involute_FUNPOW_LINV",
  ``!f A x n. f involute A /\ x IN A ==>
             (FUNPOW (LINV f A) n x = FUNPOW f n x)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `f PERMUTES A` by rw[involute_bij] >>
  `FUNPOW f n x IN A /\ FUNPOW f (SUC n) x IN A` by rw[FUNPOW_closure] >>
  `FUNPOW (LINV f A) (SUC n) x = LINV f A (FUNPOW (LINV f A) n x)` by rw[FUNPOW_SUC] >>
  `_ = LINV f A (FUNPOW f n x)` by rw[] >>
  `_ = LINV f A (LINV f A (f (FUNPOW f n x)))` by metis_tac[BIJ_LINV_THM] >>
  `_ = LINV f A (LINV f A (FUNPOW f (SUC n) x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW f (SUC n) x` by metis_tac[involute_LINV] >>
  simp[]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
