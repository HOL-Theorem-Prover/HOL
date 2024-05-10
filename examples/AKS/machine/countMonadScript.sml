(* ------------------------------------------------------------------------- *)
(* Count Monad                                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countMonad";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory pairTheory optionTheory;

open errorStateMonadTheory;

open monadsyntax;

val _ = set_grammar_ancestry ["pair", "option", "arithmetic"];

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "errorState";

(* ------------------------------------------------------------------------- *)
(* Count Monad Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   counter = Count num
*)
(* Overloading:
#  ecm     = :('a # counter)
*)
(* Definitions and Theorems (# are exported):

   Count:
   unit_def      |- !x. unit x = (x,Count 0)
   tick_def      |- !c. tick c = ((),Count c)
   valueOf_def   |- !ac. valueOf ac = FST ac
   stepsOf_def   |- !ac. stepsOf ac = case ac of (a,Count n) => n
   bind_def      |- !ac f. bind ac f =
                           case ac of
                             (a,Count c1) => case f a of (b,Count c2) => (b,Count (c1 + c2))
   bind_unit1    |- !f x. monad_bind (unit x) f = f x
   bind_unit2    |- !m. monad_bind m unit = m
   bind_assoc    |- !m f g. do a <- m; monad_bind (f a) g od = monad_bind (monad_bind m f) g
   bind_cong     |- !m1 m2 fm1 fm2. m1 = m2 /\ (!mval. mval = valueOf m1 ==> fm1 mval = fm2 mval) ==>
                     monad_bind m1 fm1 = monad_bind m2 fm2

#  unit_value    |- !x. valueOf (unit x) = x
#  tick_value    |- !n. valueOf (tick n) = ()
#  bind_value    |- !m f. valueOf (monad_bind m f) = valueOf (f (valueOf m))
#  unit_count    |- !x. stepsOf (unit x) = 0
#  tick_count    |- !n. stepsOf (tick n) = n
#  bind_count    |- !m f. stepsOf (monad_bind m f) = stepsOf m + stepsOf (f (valueOf m))

   Count Monad:
   Count  :=   {      bind = ``bind``,
                    choice = NONE,
                      fail = NONE,
                     guard = NONE,
                ignorebind = NONE,
                      unit = ``unit``}

   app1_def      |- !f xM. app1 f xM = monad_bind xM f
   app2_def      |- !f xM yM. app2 f xM yM = do x <- xM; y <- yM; f x y od
   map_def       |- !f m. map f m = (f ## I) m

   ifM_def       |- !gM tM eM. ifM gM tM eM = do b <- gM; if b then tM else eM od
   ifM_value     |- !gM tM eM. valueOf (ifM gM tM eM) =
                               if valueOf gM then valueOf tM else valueOf eM
   ifM_count     |- !gM tM eM. stepsOf (ifM gM tM eM) =
                               stepsOf gM + if valueOf gM then stepsOf tM else stepsOf eM
*)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Count Monad                                                               *)
(* ------------------------------------------------------------------------- *)

(* Define Count type *)
val _ = Datatype`counter = Count num`;

(* value and counter of an elementary count monad *)
val _ = temp_type_abbrev("ecm", ``:('a # counter)``);

(* unit of an elementary count monad *)
val unit_def = Define`unit (x:'a) : 'a ecm = (x, Count 0)`;

(* tick of an elementary count monad *)
val tick_def = Define`tick c : unit ecm = ((), Count c)`;

(* value of an accumulating monad *)
val valueOf_def = Define`
    valueOf (ac :('a # counter)) = FST ac
`;

(* count of steps in an accumulating monad *)
(*
val stepsOf_def = Define`
    stepsOf (ac :('a # counter)) = counter_size (SND (THE ac))
`;
*)
val stepsOf_def = Define`
    stepsOf (ac :('a # counter)) =
      case ac of
      | (a, Count n) => n
`;

(* binding an executing function with an accumulating monad *)
val bind_def = Define`
  bind (ac : 'a ecm) (f : 'a -> 'b ecm) =
    case ac of
      | (a,Count c1) =>
          (case f a of
             | (b,Count c2) => (b, Count (c1 + c2)))
`;

(* count cases and tactic *)
val count_CASES = TypeBase.nchotomy_of ``:counter``;
val cmetis = metis_tac[pair_CASES, count_CASES];

(* Theorem: alternate form of bind *)
(* Proof: by bind_def *)
val bind_alt = store_thm(
  "bind_alt",
  ``!v1 c1 f. bind (v1, Count c1) f =
    case f v1 of
      (v2, Count c2) => (v2, Count (c1 + c2))``,
  rw[bind_def]);

(* Theorem: alternate form of valueOf *)
(* Proof: by valueOf_def *)
val valueOf_alt = store_thm(
  "valueOf_alt",
  ``!v c. valueOf (v, Count c) = v``,
  rw[valueOf_def]);

(* Theorem: alternate form of stepsOf *)
(* Proof: by stepsOf_def *)
val stepsOf_alt = store_thm(
  "stepsOf_alt",
  ``!v c. stepsOf (v, Count c) = c``,
  rw[stepsOf_def]);

(* Theorem: bind (unit x) f = f x *)
(* Proof: by bind_def, unit_def *)
val bind_unit1 = store_thm(
  "bind_unit1",
  ``!f x. bind (unit x) f = f x``,
  rw[bind_def, unit_def] >>
  (`?b c2. f x = (b, Count c2)` by cmetis >> simp[]));

(* Theorem: bind m unit = m *)
(* Proof: by bind_def, unit_def *)
val bind_unit2 = store_thm(
  "bind_unit2",
  ``!m. bind m unit = m``,
  rw[bind_def, unit_def, AllCaseEqs(), PULL_EXISTS] >>
  cmetis);

(* Theorem: bind m (\a. bind (f a) g) = bind (bind m f) g *)
(* Proof: by bind_def *)
val bind_assoc = store_thm(
  "bind_assoc",
  ``!m f g. bind m (\a. bind (f a) g) = bind (bind m f) g``,
  rw[bind_def, AllCaseEqs(), PULL_EXISTS] >>
  csimp[] >>
  cmetis);

(* Theorem: (m1 = m2) /\ (!mval. mval = valueOf m1 ==> fm1 mval = fm2 mval)
            ==> (bind m1 fm1 = bind m2 fm2) *)
(* Proof: by bind_def, valueOf_def *)
val bind_cong = store_thm(
  "bind_cong[defncong]",
  ``!m1 m2 fm1 fm2. (m1 = m2) /\ (!mval. mval = valueOf m1 ==> fm1 mval = fm2 mval) ==>
      (bind m1 fm1 = bind m2 fm2)``,
  rw[bind_def, valueOf_def] >>
  Cases_on `m1` >>
  Cases_on `r` >>
  fs[]);
(* for total define, or tDefine *)

(*
If using try and catch,
change to:   'a option # num

 bind m1 f =
    case m1 of
      (NONE, c) => (NONE, c)
    | (SOME v, c1) =>
        case f v of
          (NONE, c2) => (NONE, c1 + c2)
       | (SOME v', c2) => (SOME v', c1 + c2)
  choice m1 m2 =
     case m1 of
       (NONE, c1) => (FST m2, c1 + SND m2)
     | (SOME v, c) => (SOME v, c)

*)

(* Theorem: valueOf (unit x) = x *)
(* Proof: by valueOf_def, unit_def *)
val unit_value = store_thm(
  "unit_value[simp]",
  ``!x. valueOf (unit x) = x``,
  rw[valueOf_def, unit_def]);

(* Theorem: valueOf (tick n) = () *)
(* Proof: by valueOf_def, tick_def *)
val tick_value = store_thm(
  "tick_value[simp]",
  ``!n. valueOf (tick n) = ()``,
  rw[valueOf_def, tick_def]);

(* Theorem: valueOf (bind m f) = valueOf (f (valueOf m)) *)
(* Proof:
   By definitions, and resolving cases.
*)
val bind_value = store_thm(
  "bind_value[simp]",
  ``!m f. valueOf (bind m f) = valueOf (f (valueOf m))``,
  rw[bind_def, valueOf_def] >>
  (Cases_on `m` >> simp[]) >>
  (Cases_on `r` >> simp[]) >>
  (Cases_on `f q` >> simp[]) >>
  (Cases_on `r` >> simp[]));
(* Once in [simp], just rw[] proves it. *)

(* Theorem: stepsOf (unit x) = 0 *)
(* Proof: by stepsOf_def, unit_def *)
val unit_count = store_thm(
  "unit_count[simp]",
  ``!x. stepsOf (unit x) = 0``,
  rw[stepsOf_def, unit_def]);

(* Theorem: stepsOf (tick n) = n *)
(* Proof: by stepsOf_def, tick_def *)
val tick_count = store_thm(
  "tick_count[simp]",
  ``!n. stepsOf (tick n) = n``,
  rw[stepsOf_def, tick_def]);

(* Theorem: stepsOf (bind m f) = stepsOf m + stepsOf (f (valueOf m)) *)
(* Proof:
   By definitions, this is to show:
      ?a a' c1 c2. m = (a',Count c1) /\ f a' = (a,Count c2)
   The values exists by pair_CASES and count_CASES.
*)
val bind_count = store_thm(
  "bind_count[simp]",
  ``!m f. stepsOf (bind m f) = stepsOf m + stepsOf (f (valueOf m))``,
  rw[bind_def, stepsOf_def, valueOf_def, AllCaseEqs(), PULL_EXISTS] >>
  csimp[] >>
  cmetis);
(* Once in [simp], this proof is not repeatable. Just rw[] proves it. *)

(* ------------------------------------------------------------------------- *)
(* Count Monad                                                               *)
(* ------------------------------------------------------------------------- *)

(* The Count monad *)
val _ = declare_monad ("Count",
            {      bind = ``bind``,
                 choice = NONE,
                   fail = NONE,
                  guard = NONE,
             ignorebind = NONE,
                   unit = ``unit``});

(* constant as unit *)
(* val _ = add_bare_numeral_form(#"c", SOME "unit"); *)
(* original:
val cnum_def = Define`cnum n = UNIT n`;
val _ = add_numeral_form(#"c", SOME "cnum");
*)

(* unary application monad *)
val app1_def = Define`app1 f xM = bind xM f`;

(* binary application monad *)
val app2_def = Define`app2 f xM yM = bind xM (\x. bind yM (\y. f x y))`;

(* Map monad *)
val map_def = Define`map (f:'a -> 'b) m : 'b ecm = (f ## I) m`;


(* IF monad *)
val ifM_def = Define`
  ifM (gM : bool ecm) (tM : 'a ecm) eM = bind gM (\b. if b then tM else eM)
`;
(* for EVAL ifM *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);

(* Theorem: valueOf (ifM gM tM eM) = if valueOf gM then valueOf tM else valueOf eM *)
(* Proof: by ifM_def *)
val ifM_value = store_thm(
  "ifM_value[simp]",
  ``!gM tM eM. valueOf (ifM gM tM eM) = if valueOf gM then valueOf tM else valueOf eM``,
  rw[ifM_def]);

(* Theorem: stepsOf (ifM gM tM eM) =
            stepsOf gM + if valueOf gM then stepsOf tM else stepsOf eM *)
(* Proof: by ifM_def *)
val ifM_count = store_thm(
  "ifM_count[simp]",
  ``!gM tM eM. stepsOf (ifM gM tM eM) =
    stepsOf gM + if valueOf gM then stepsOf tM else stepsOf eM``,
  rw[ifM_def]);

(* for EVAL IFm *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);
(* This EVAL IFm is not stored in the theory file! *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
