(* ========================================================================== *)
(* FILE          : ttt_demoScript.sml                                         *)
(* DESCRIPTION   : TacticToe demo                                             *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2019                                                       *)
(* ========================================================================== *)

(* Updated and extended 2026 by Lukasz Czajka *)

(* Before trying the commented ttt calls, you need to record the standard
   library. Run from the HOL4 repository root:
     export HOLDIR="$PWD"
     src/tactictoe/examples/ttt_recordall.sh
   Use --keep on later runs to reuse recordings that are still up to date. *)

Theory ttt_demo
Ancestors
  list rich_list pred_set sum_num arithmetic relation sorting finite_map gcd
  divides
Libs
  tacticToe


(* mlibUseful.trace_level := 0; mesonLib.chatting := 0; *)

(* --------------------------------------------------------------------------
   Example 1: equations
   ------------------------------------------------------------------------- *)

(* ttt ([],``(2 * x + 1 = 3) ==> (x = 1)``); *)
Theorem ex1:
    (2 * x + 1 = 3) ==> (x = 1)
Proof
  asm_simp_tac (bool_ss ++ old_ARITH_ss ++ numSimps.REDUCE_ss) []
QED

(* --------------------------------------------------------------------------
   Example 2: lists
   ------------------------------------------------------------------------- *)

(* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
Theorem ex2:
    (!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)
Proof
  asm_simp_tac (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss) [LIST_EQ_REWRITE] >>
  metis_tac [EL_MAP, rich_listTheory.EL_REPLICATE]
QED

(* --------------------------------------------------------------------------
   Example 4: set theory, count x = {0,1,2,...,x}
   -------------------------------------------------------------------------- *)

(* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
Theorem ex4:
    count (n+m) DIFF count n = IMAGE ($+n) (count m)
Proof
  srw_tac [ARITH_ss] [EXTENSION, EQ_IMP_THM] >>
  Q.EXISTS_TAC `x - n` >>
  srw_tac [ARITH_ss] []
QED

(* --------------------------------------------------------------------------
   Example 5: sums
   -------------------------------------------------------------------------- *)

(* set_timeout 60.0; *)
(* ttt  ([],``!n. 2 * SUM (n+1) I = n * (n+1) ``); *)
Theorem ex5:
    !n. 2 * SUM (n+1) I = n * (n+1)
Proof
  Induct >|
    [rewrite_tac [numeralTheory.numeral_distrib] >>
       srw_tac [] [SUM_1],
     asm_simp_tac (srw_ss () ++ ARITH_ss) [arithmeticTheory.ADD_CLAUSES] >>
       srw_tac [ARITH_ss] [SUM_def] >>
       srw_tac [ARITH_ss] [arithmeticTheory.MULT_CLAUSES]]
QED

(* --------------------------------------------------------------------------
   Example 6: maps, reversals, and append
   ------------------------------------------------------------------------- *)

(* ttt ([],``MAP f (REVERSE xs ++ REVERSE ys) =
             REVERSE (MAP f ys ++ MAP f xs)``); *)
Theorem ex6:
    MAP f (REVERSE xs ++ REVERSE ys) =
    REVERSE (MAP f ys ++ MAP f xs)
Proof
  metis_tac [listTheory.REVERSE_APPEND, listTheory.MAP_APPEND,
    listTheory.MAP_REVERSE]
QED

(* --------------------------------------------------------------------------
   Example 7: flattening mapped, appended lists
   ------------------------------------------------------------------------- *)

(* ttt ([],``FLAT (MAP (MAP f) (xss ++ yss)) =
             MAP f (FLAT xss ++ FLAT yss)``); *)
Theorem ex7:
    FLAT (MAP (MAP f) (xss ++ yss)) =
    MAP f (FLAT xss ++ FLAT yss)
Proof
  metis_tac [FLAT_EQ_APPEND, listTheory.MAP_FLAT]
QED

(* --------------------------------------------------------------------------
   Example 8: filters through composed maps
   ------------------------------------------------------------------------- *)

(* ttt ([],``FILTER P (MAP (f o g) xs) =
             MAP f (FILTER (P o f) (MAP g xs))``); *)
Theorem ex8:
    FILTER P (MAP (f o g) xs) =
    MAP f (FILTER (P o f) (MAP g xs))
Proof
  metis_tac [listTheory.MAP_MAP_o, FILTER_MAP]
QED

(* --------------------------------------------------------------------------
   Example 9: reversing a flattened list of lists
   ------------------------------------------------------------------------- *)

(* set_timeout 60.0; *)
(* ttt ([],``REVERSE (FLAT xss) =
             FLAT (MAP REVERSE (REVERSE xss))``); *)
Theorem ex9:
    REVERSE (FLAT xss) = FLAT (MAP REVERSE (REVERSE xss))
Proof
  Cases_on `REVERSE x` >>
  pop_assum (mp_tac o Q.AP_TERM `REVERSE`) >>
  metis_tac [listTheory.REVERSE_REVERSE, FLAT_REVERSE]
QED

(* --------------------------------------------------------------------------
   Example 10: images of unions and differences
   ------------------------------------------------------------------------- *)

(* ttt ([],``IMAGE f ((s UNION t) DIFF u) SUBSET
             (IMAGE f s UNION IMAGE f t)``); *)
Theorem ex10:
    IMAGE f ((s UNION t) DIFF u) SUBSET
    (IMAGE f s UNION IMAGE f t)
Proof
  pure_rewrite_tac [SUBSET_DEF, IN_UNION] >>
  srw_tac [] [] >>
  metis_tac []
QED

(* --------------------------------------------------------------------------
   Example 11: injective images preserve set difference
   ------------------------------------------------------------------------- *)

(* ttt ([],``INJ f (s UNION t) UNIV ==>
             IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t``); *)
Theorem ex11:
    INJ f (s UNION t) UNIV ==>
    IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t
Proof
  let fun rw thl = srw_tac [] thl in
    rw [EXTENSION, EQ_IMP_THM] >|
      [metis_tac [],
       imp_res_tac LINV_DEF >> metis_tac [IN_UNION],
       metis_tac []]
  end
QED

(* --------------------------------------------------------------------------
   Example 12: powersets distribute over intersection
   ------------------------------------------------------------------------- *)

(* ttt ([],``POW (s INTER t) = POW s INTER POW t``); *)
Theorem ex12:
    POW (s INTER t) = POW s INTER POW t
Proof
  simp_tac bool_ss [IN_INTER, EXTENSION] >>
  srw_tac [] [POW_DEF]
QED

(* --------------------------------------------------------------------------
   Example 13: finite sums distribute over pointwise addition
   ------------------------------------------------------------------------- *)

(* ttt ([],``SUM n (\i. f i + g i) = SUM n f + SUM n g``); *)
Theorem ex13:
    SUM n (\i. f i + g i) = SUM n f + SUM n g
Proof
  Induct_on `n` >|
    [srw_tac [] [SUM_def],
     srw_tac [ARITH_ss] [SUM_def]]
QED

(* --------------------------------------------------------------------------
   Example 14: splitting a finite sum at an offset
   ------------------------------------------------------------------------- *)

(* ttt ([],``SUM (m + n) f = SUM m f + SUM n (\i. f (m + i))``); *)
Theorem ex14:
    SUM (m + n) f = SUM m f + SUM n (\i. f (m + i))
Proof
  Induct_on `n` >|
    [metis_tac [SUM_ZERO, numeralTheory.numeral_distrib],
     asm_simp_tac ((bool_ss ++ ARITH_ss) ++ numSimps.REDUCE_ss)
       [ADD_CLAUSES] >>
     srw_tac [ARITH_ss] [SUM_def]]
QED

(* --------------------------------------------------------------------------
   Example 15: flattened lengths over appended lists
   ------------------------------------------------------------------------- *)

(* ttt ([],``SUM (MAP LENGTH (xss ++ yss)) =
             LENGTH (FLAT xss) + LENGTH (FLAT yss)``); *)
Theorem ex15:
    SUM (MAP LENGTH (xss ++ yss)) =
    LENGTH (FLAT xss) + LENGTH (FLAT yss)
Proof
  let
    fun simp l =
      asm_simp_tac ((srw_ss () ++ boolSimps.LET_ss) ++ ARITH_ss) l
  in
    simp [] >> metis_tac [LENGTH_FLAT, listTheory.SUM_APPEND]
  end
QED

(* --------------------------------------------------------------------------
   Example 16: composing three reflexive-transitive paths
   ------------------------------------------------------------------------- *)

(* ttt ([],``RTC R w x /\ RTC R x y /\ RTC R y z ==> RTC R w z``); *)
Theorem ex16:
    RTC R w x /\ RTC R x y /\ RTC R y z ==> RTC R w z
Proof
  mesonLib.MESON_TAC [RTC_RTC]
QED

(* --------------------------------------------------------------------------
   Example 17: monotonicity of reflexive-transitive closure
   ------------------------------------------------------------------------- *)

(* ttt ([],``(!a b. (R:'a -> 'a -> bool) a b ==>
                       (Q:'a -> 'a -> bool) a b) /\
             RTC R x y ==> RTC Q x y``); *)
Theorem ex17:
    (!a b. (R:'a -> 'a -> bool) a b ==> (Q:'a -> 'a -> bool) a b) /\
    RTC R x y ==> RTC Q x y
Proof
  Induct_on `RTC` >>
  rewrite_tac [RTC_ALT_DEF] >>
  metis_tac []
QED

(* --------------------------------------------------------------------------
   Example 18: lifting paths into a union of relations
   ------------------------------------------------------------------------- *)

(* ttt ([],``RTC R x y ==> RTC (R RUNION Q) x y``); *)
Theorem ex18:
    RTC R x y ==> RTC (R RUNION Q) x y
Proof
  match_mp_tac RTC_INDUCT >>
  prove_tac [RTC_RULES, RUNION]
QED

(* --------------------------------------------------------------------------
   Example 19: quicksort is both sorted and a permutation
   ------------------------------------------------------------------------- *)

(* ttt ([],``transitive R /\ total R ==>
             PERM (QSORT R xs) xs /\ SORTED R (QSORT R xs)``); *)
Theorem ex19:
    transitive R /\ total R ==>
    PERM (QSORT R xs) xs /\ SORTED R (QSORT R xs)
Proof
  prove_tac [QSORT_PERM, QSORT_SORTED, PERM_SYM]
QED

(* --------------------------------------------------------------------------
   Example 20: permutations survive mapping and preserve length
   ------------------------------------------------------------------------- *)

(* ttt ([],``PERM xs ys ==>
             PERM (MAP f xs) (MAP f ys) /\
             LENGTH (MAP f xs) = LENGTH ys``); *)
Theorem ex20:
    PERM xs ys ==>
    PERM (MAP f xs) (MAP f ys) /\
    LENGTH (MAP f xs) = LENGTH ys
Proof
  simp [] >> metis_tac [PERM_MAP, PERM_LENGTH]
QED

(* --------------------------------------------------------------------------
   Example 21: shadowing a finite-map update
   ------------------------------------------------------------------------- *)

(* ttt ([],``FLOOKUP (fm |+ (k,v1) |+ (k,v2)) k = SOME v2 /\
             FDOM (fm |+ (k,v1) |+ (k,v2)) = k INSERT FDOM fm``); *)
Theorem ex21:
    FLOOKUP (fm |+ (k,v1) |+ (k,v2)) k = SOME v2 /\
    FDOM (fm |+ (k,v1) |+ (k,v2)) = k INSERT FDOM fm
Proof
  metis_tac [FUPDATE_EQ, FDOM_FUPDATE, FLOOKUP_UPDATE]
QED

(* --------------------------------------------------------------------------
   Example 22: gcds of products
   ------------------------------------------------------------------------- *)

(* ttt ([],``gcd (a * b) b = b /\ gcd a (a * b) = a``); *)
Theorem ex22:
    gcd (a * b) b = b /\ gcd a (a * b) = a
Proof
  (srw_tac []) [GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ANTISYM]
QED

(* --------------------------------------------------------------------------
   Example 23: divisibility is preserved by exponentiation
   ------------------------------------------------------------------------- *)

(* ttt ([],``divides a b ==> divides (a ** n) (b ** n)``); *)
Theorem ex23:
    divides a b ==> divides (a ** n) (b ** n)
Proof
  rw_tac numLib.std_ss [divides_def] >>
  metis_tac [EXP_BASE_MULT]
QED

(* --------------------------------------------------------------------------
   Example 24: expanding a square over natural numbers
   ------------------------------------------------------------------------- *)

(* ttt ([],``(a + b) * (a + b) =
             a * a + 2 * a * b + b * b``); *)
Theorem ex24:
    (a + b) * (a + b) = a * a + 2 * a * b + b * b
Proof
  rewrite_tac [TWO, MULT_CLAUSES, RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB] >>
  simp_tac bool_ss [AC ADD_SYM ADD_ASSOC, AC MULT_SYM MULT_ASSOC]
QED

(* --------------------------------------------------------------------------
   Example 25: parity of a sum of three numbers
   ------------------------------------------------------------------------- *)

(* ttt ([],``EVEN (a + b + c) <=>
             (EVEN a <=> (EVEN b <=> EVEN c))``); *)
Theorem ex25:
    EVEN (a + b + c) <=> (EVEN a <=> (EVEN b <=> EVEN c))
Proof
  rewrite_tac [GSYM ADD_ASSOC] >>
  asm_rewrite_tac [EVEN_ADD]
QED

(* --------------------------------------------------------------------------
   Example 26: the sum of the first odd numbers
   ------------------------------------------------------------------------- *)

(* ttt ([],``!n. SUM n (\i. 2 * i + 1) = n * n``); *)
Theorem ex26:
    !n. SUM n (\i. 2 * i + 1) = n * n
Proof
  Induct >|
    [metis_tac [numeralTheory.numeral_distrib, SUM_ZERO],
     srw_tac [ARITH_ss] [SUM_def] >>
     rewrite_tac [EXP, TWO, ONE, MULT_CLAUSES, ADD_CLAUSES] >>
     metis_tac [MULT_SUC, ADD_ASSOC, numeralTheory.numeral_distrib,
       RIGHT_ADD_DISTRIB, MULT]]
QED

(* --------------------------------------------------------------------------
   Example 27: linearity of finite sums
   ------------------------------------------------------------------------- *)

(* ttt ([],``!n. SUM n (\i. c * f i + d * g i) =
             c * SUM n f + d * SUM n g``); *)
Theorem ex27:
    !n. SUM n (\i. c * f i + d * g i) =
        c * SUM n f + d * SUM n g
Proof
  Induct >|
    [srw_tac [] [SUM_def],
     srw_tac [ARITH_ss] [SUM_def]]
QED

(* --------------------------------------------------------------------------
   Example 28: a geometric sum
   ------------------------------------------------------------------------- *)

(* ttt ([],``!n. SUM n (\i. 2 ** i) = 2 ** n - 1``); *)
Theorem ex28:
    !n. SUM n (\i. 2 ** i) = 2 ** n - 1
Proof
  Induct >|
    [srw_tac [] [SUM_def],
     simp_tac bool_ss [EXP] >>
     srw_tac [ARITH_ss] [SUM_def]]
QED

(* --------------------------------------------------------------------------
   Example 29: flattening a list after duplicating every element
   ------------------------------------------------------------------------- *)

(* ttt ([],``!xs. LENGTH (FLAT (MAP (\x. [x;x]) xs)) =
              2 * LENGTH xs``); *)
Theorem ex29:
    !xs. LENGTH (FLAT (MAP (\x. [x;x]) xs)) = 2 * LENGTH xs
Proof
  INDUCT_THEN list_INDUCT strip_assume_tac >|
    [srw_tac [] [],
     rw []]
QED

(* --------------------------------------------------------------------------
   Example 30: complementary filters partition list length
   ------------------------------------------------------------------------- *)

(* ttt ([],``!xs. LENGTH (FILTER P xs) +
                    LENGTH (FILTER ($~ o P) xs) = LENGTH xs``); *)
Theorem ex30:
    !xs. LENGTH (FILTER P xs) +
         LENGTH (FILTER ($~ o P) xs) = LENGTH xs
Proof
  Induct >|
    [srw_tac [] [],
     rw_tac arith_ss [FILTER, LENGTH]]
QED

(* --------------------------------------------------------------------------
   Example 31: reversing flattened pairs
   ------------------------------------------------------------------------- *)

(* ttt ([],``!xs. REVERSE (FLAT (MAP (\x. [f x; g x]) xs)) =
              FLAT (MAP (\x. [g x; f x]) (REVERSE xs))``); *)
Theorem ex31:
    !xs. REVERSE (FLAT (MAP (\x. [f x; g x]) xs)) =
         FLAT (MAP (\x. [g x; f x]) (REVERSE xs))
Proof
  Induct >|
    [metis_tac [REVERSE_DEF, listTheory.MAP, FLAT_REVERSE],
     srw_tac [] []]
QED

(* --------------------------------------------------------------------------
   Example 32: projecting a truncated ZIP
   ------------------------------------------------------------------------- *)

(* ttt ([],``!xs ys. MAP FST (ZIP (xs,ys)) =
                 TAKE (MIN (LENGTH xs) (LENGTH ys)) xs``); *)
Theorem ex32:
    !xs ys. MAP FST (ZIP (xs,ys)) =
            TAKE (MIN (LENGTH xs) (LENGTH ys)) xs
Proof
  let fun rw thl = srw_tac [] thl in
    INDUCT_THEN list_INDUCT strip_assume_tac >|
      [srw_tac [] [] >> metis_tac [ZIP_def],
       Cases_on `ys` >|
         [full_simp_tac (srw_ss ()) [] >> metis_tac [ZIP_def],
          rw [MIN_DEF]]]
  end
QED

(* --------------------------------------------------------------------------
   Example 33: summing pairwise combinations of two lists
   ------------------------------------------------------------------------- *)

(* ttt ([],``!xs ys. LENGTH xs = LENGTH ys ==>
      SUM (MAP (\(x,y). f x + g y) (ZIP (xs,ys))) =
      SUM (MAP f xs) + SUM (MAP g ys)``); *)
Theorem ex33:
    !xs ys. LENGTH xs = LENGTH ys ==>
      SUM (MAP (\(x,y). f x + g y) (ZIP (xs,ys))) =
      SUM (MAP f xs) + SUM (MAP g ys)
Proof
  let
    fun fs thl = full_simp_tac (srw_ss () ++ ARITH_ss) thl
  in
    INDUCT_THEN list_INDUCT strip_assume_tac >|
      [srw_tac [] [],
       srw_tac [ARITH_ss] [] >> Cases_on `ys` >> fs []]
  end
QED

(* --------------------------------------------------------------------------
   Example 34: a ranking function is monotone along RTC paths
   ------------------------------------------------------------------------- *)

(* ttt ([],``(!a b. R a b ==> f a < f b) /\
             RTC R x y ==> f x <= f y``); *)
Theorem ex34:
    (!a b. R a b ==> f a < f b) /\
    RTC R x y ==> f x <= f y
Proof
  Induct_on `RTC` >>
  rpt strip_tac >|
    [srw_tac [] [],
     metis_tac [numLib.ARITH_PROVE ``x < y /\ y <= z ==> x <= z``]]
QED

(* --------------------------------------------------------------------------
   Example 35: order-preserving maps preserve sortedness
   ------------------------------------------------------------------------- *)

(* ttt ([],``(!x y. R x y ==> Q (f x) (f y)) /\ SORTED R xs ==>
             SORTED Q (MAP f xs)``); *)
Theorem ex35:
    (!x y. R x y ==> Q (f x) (f y)) /\ SORTED R xs ==>
    SORTED Q (MAP f xs)
Proof
  Cases_on `xs` >|
    [metis_tac [sorted_map, SORTED_SING, SORTED_TL],
     rw [SORTED_EL_SUC, EL_MAP]]
QED
