(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
app load
  ["bossLib","realLib","rich_listTheory","stringTheory",
   "metisLib","posrealLib","expectationTheory","intLib", "wpTheory", "valueTheory", "arithmeticTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory posrealTheory posrealLib expectationTheory wpTheory valueTheory arithmeticTheory;

(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "simpledc"                                         *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "looprules";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = I prove;

val let_imp_not_infty = store_thm
  ("let_imp_not_infty",
   ``!x:posreal. (?y. (y < infty) /\ (x <= y)) ==>
		 (~(x = infty))``,
   METIS_TAC [let_trans, infty_le, preal_lt_def]);

val le1_imp_not_infty = store_thm
  ("le1_imp_not_infty",
   ``!x:posreal. (x <= 1) ==> (~(x = infty))``,
   `1 < infty` by RW_TAC posreal_ss [preal_lt_def]
   ++ METIS_TAC [let_imp_not_infty]);

val let_lemma = store_thm
  ("let_lemma",
   ``(let x = (a:posreal) in x * y) = a * y``,
   RW_TAC std_ss []);

val let_lin_lemma = store_thm
  ("let_lin_lemma",
   ``(let x = (a:posreal) in x * y + (1 - x) * z) = a * y + (1 - a) * z``,
   RW_TAC std_ss []);

val wp_assign = store_thm
  ("wp_assign",
  ``!v s postE.
	wp (Assign v s) postE = 
    (\s'. postE (\w. (if w = v then s s' else s' w)))``,
   RW_TAC std_ss [wp_def, assign_eta]);

val wp_seq = store_thm
  ("wp_seq",
   ``!prog prog' postE.
	wp (Seq prog prog') postE =
	wp prog (wp prog' postE)``,
   RW_TAC std_ss [wp_def]);

val while_unwind_lemma = store_thm
  ("while_unwind_lemma",
   ``!g body Inv.
	wp (While g body) Inv = (\s. if g s then wp body (wp (While g body) Inv) s else Inv s)``,
   REPEAT STRIP_TAC
   ++ RW_TAC posreal_ss [wp_def, cond_eta]
   ++ `monotonic (expect,Leq) (\e s. (if g s then wp body e s else Inv s))`
	by (RW_TAC std_ss [monotonic_def, Leq_def]
	    ++ Cases_on `g s`
	    >> METIS_TAC [wp_mono, Leq_def]
	    ++ RW_TAC posreal_ss [One_def])
   ++ `lfp (expect,Leq) (\e s. (if g s then wp body e s else Inv s))
	(expect_lfp (\e s. (if g s then wp body e s else Inv s)))`
	by METIS_TAC [expect_lfp_def]
   ++ FULL_SIMP_TAC std_ss [Leq_def, wp_def, cond_eta, lfp_def, expect_def]);

val while_unwind_val_lemma = store_thm
  ("while_unwind_val_lemma",
   ``wp (While g (body:value command)) Inv = (\s. if g s then wp body (wp (While g body) Inv) s else Inv s)``,
   REPEAT STRIP_TAC
   ++ RW_TAC posreal_ss [wp_def, cond_eta]
   ++ `monotonic (expect,Leq) (\e s. (if g s then wp body e s else Inv s))`
	by (RW_TAC std_ss [monotonic_def, Leq_def]
	    ++ Cases_on `g s`
	    >> METIS_TAC [wp_mono, Leq_def]
	    ++ RW_TAC posreal_ss [One_def])
   ++ `lfp (expect,Leq) (\e s. (if g s then wp body e s else Inv s))
	(expect_lfp (\e s. (if g s then wp body e s else Inv s)))`
	by METIS_TAC [expect_lfp_def]
   ++ FULL_SIMP_TAC std_ss [Leq_def, wp_def, cond_eta, lfp_def, expect_def]);

val INT_OF_NUM_POSINT_EQ = store_thm
  ("INT_OF_NUM_POSINT_EQ",
   ``!(x:int). (0 < x) ==> ((& (Num x)) = x)``,
   REPEAT STRIP_TAC
   ++ `?n. x = &n` by METIS_TAC [NUM_POSINT_EXISTS, INT_LT_IMP_LE]
   ++ ASM_REWRITE_TAC [NUM_OF_INT]);

val expect1_postE_imp_expect1_wp_postE = store_thm
  ("expect1_postE_imp_expect1_wp_postE",
   ``!prog postE. (expect1 postE) ==> (expect1 (wp prog postE))``,
   METIS_TAC [sublinear_expect1, healthy_def, wp_healthy]);

val Term_Leq_One = store_thm
  ("Term_Leq_One",
   ``!prog. Leq (wp prog One) One``,
   `expect1(One)`
	by RW_TAC posreal_ss [One_def, expect1_def]
   ++ METIS_TAC [Leq_def, One_def, expect1_def, expect1_postE_imp_expect1_wp_postE]);

val lt_trans = store_thm
  ("lt_trans",
   ``!(x:posreal) (y:posreal) (z:posreal). (x<y) /\ (y < z) ==> x < z``,
   REPEAT STRIP_TAC
   ++ `(x = 0) \/ (x = infty) \/
       ~(x = 0) /\ ?x'. ~(x' = 0) /\ 0 <= x' /\ (x = preal x')` 
	by METIS_TAC [posreal_trich]
   ++ `(y = 0) \/ (y = infty) \/
       ~(y = 0) /\ ?y'. ~(y' = 0) /\ 0 <= y' /\ (y = preal y')` 
	by METIS_TAC [posreal_trich]
   ++ `(z = 0) \/ (z = infty) \/
       ~(z = 0) /\ ?z'. ~(z' = 0) /\ 0 <= z' /\ (z = preal z')` 
	by METIS_TAC [posreal_trich]
   ++ FULL_SIMP_TAC posreal_ss [preal_lt_def, zero_le, le_infty]
   ++ Suff `preal x' < preal z'` >> METIS_TAC [preal_lt_def]
   ++ `preal x' < preal y'` by METIS_TAC [preal_lt_def]
   ++ `preal y' < preal z'` by METIS_TAC [preal_lt_def]
   ++ METIS_TAC [lte_trans, lt_le]
);

val max_swap = store_thm
  ("max_swap",
   ``!x y z. (max (max x y) z) = (max y (max x z))``,
   RW_TAC posreal_ss [preal_max_def, le_trans, le_antisym]
   ++ METIS_TAC [le_antisym, preal_lt_def, lt_trans, le_total]);

val mul_operands_le1_le1 = store_thm
  ("mul_operands_le1_le1",
   ``!(x:posreal)(y:posreal). 
	(x<=1) /\ (y<=1) ==>
	(x*y <= 1)``,
   RW_TAC posreal_ss []
   ++ `(x = 0) \/ (x = infty) \/
       ~(x = 0) /\ ?x'. ~(x' = 0) /\ 0 <= x' /\ (x = preal x')`
	by METIS_TAC [posreal_trich]
   ++ FULL_SIMP_TAC posreal_ss []
   ++ `(y = 0) \/ (y = infty) \/
       ~(y = 0) /\ ?y'. ~(y' = 0) /\ 0 <= y' /\ (y = preal y')`
	by METIS_TAC [posreal_trich]
   ++ FULL_SIMP_TAC posreal_ss [preal_mul]
   ++ `((1:posreal) = (0:posreal)) \/ ((1:posreal) = infty) \/
       ~((1:posreal) = (0:posreal)) /\ ?one'. ~(one' = 0) /\ 0 <= one' /\ ((1:posreal) = preal one')`
		by METIS_TAC [posreal_trich]
   ++ FULL_SIMP_TAC posreal_ss [preal_le]
   ++ MATCH_MP_TAC preal_le
   ++ `one' = one' * one'`
	by (`preal (one' * one') = preal one' * preal one'`
		by METIS_TAC [preal_mul]
	    ++ `preal (one' * one') = (1:posreal)`
		by (`(1:posreal)*(1:posreal)=(1:posreal)` 
			by RW_TAC posreal_ss []
		    ++ METIS_TAC [])
	    ++ MATCH_MP_TAC preal_inj
	    ++ RW_TAC real_ss [REAL_LE_SQUARE])
   ++ Suff `x' * y' <= one' * one'`
   >> METIS_TAC []
   ++ `x' <= one'`
	by (MATCH_MP_TAC le_preal
	    ++ METIS_TAC [])
   ++ `y' <= one'`
	by (MATCH_MP_TAC le_preal
	    ++ METIS_TAC [])
   ++ METIS_TAC [REAL_LE_MUL2]);

val operand_le_one_imp_mul_le_one = store_thm
  ("operand_le_one_imp_mul_le_one",
   ``!(x:posreal)(y:posreal).
	(x <= 1) ==>
	(x*y <= y)``,
   METIS_TAC [le_mul2, le_refl, mul_lone]);
   

val mul_nonzero_operands_imp_nonzero_result = store_thm
  ("mul_nonzero_operands_imp_nonzero_result",
   ``!(x:posreal) (y:posreal). (0 < x) /\ (0 < y) ==> (0 < x * y)``,
   RW_TAC posreal_ss [preal_lt_def, entire]
   ++ `~(x <= 0)` by METIS_TAC [preal_lt_def]
   ++ `~(y <= 0)` by METIS_TAC [preal_lt_def]
   ++ METIS_TAC [le_zero]);

val INT_LE_EQ_LT_ADD1 = store_thm
  ("INT_LE_EQ_LT_ADD1",
   ``(x:int) <= (y:int) = x < y + 1``,
   REPEAT STRIP_TAC
    ++ `x <= y ==> x < y + 1` by METIS_TAC [INT_LT_ADD1]
    ++ `x < y + 1 ==> x <= y`
        by (`(?x'. (x = & x') /\ ~(x' = 0)) \/ (?x'. (x = ~& x') /\ ~(x' = 0)) \/
                   (x = 0)` by METIS_TAC [INT_NUM_CASES]
	    ++ `(?y'. (y = & y') /\ ~(y' = 0)) \/ (?y'. (y = ~& y') /\ ~(y' = 0)) \/
                      (y = 0)` by METIS_TAC [INT_NUM_CASES]
	    ++ FULL_SIMP_TAC int_ss [INT_ADD_CALCULATE]
		++ Cases_on `y' <= 1`
		++ FULL_SIMP_TAC int_ss [])
    ++ METIS_TAC []);

val posreal_pow_def = Define
   `(posreal_pow (e:posreal) 0 = 1) /\
    (posreal_pow (e:posreal) (SUC n) = e * (posreal_pow e n))`;

val posreal_pow_1bounded_base_1bounded = store_thm
  ("posreal_pow_1bounded_base_1bounded",
   ``!e n. (e <= 1) ==> (posreal_pow e n <= 1)``,
   RW_TAC posreal_ss []
   ++ Induct_on `n`
   ++ RW_TAC posreal_ss [posreal_pow_def]
   ++ METIS_TAC [mul_operands_le1_le1]);

val posreal_pow_base1_eq_1 = store_thm
  ("posreal_pow_base1_eq_1",
   ``!n. posreal_pow 1 n = 1``,
   Induct
   ++ METIS_TAC [posreal_pow_def, mul_lone]);

val zero_lt_posreal_pow = store_thm
  ("zero_lt_posreal_pow",
   ``!e n. (0 < e) ==> (0 < (posreal_pow e n))``,
   GEN_TAC
   ++ Induct_on `n`
   ++ RW_TAC posreal_ss [posreal_pow_def]
   ++ `0 < posreal_pow e n`
	by METIS_TAC []
   ++ METIS_TAC [mul_nonzero_operands_imp_nonzero_result]);

val NO_INT_BETWEEN_ZERO_AND_ONE = store_thm
  ("NO_INT_BETWEEN_ZERO_AND_ONE",
   ``!(x:int). ~(0<x /\ x < 1)``,
   `1 = 0 + (1:int)` by RW_TAC int_ss []
   ++ METIS_TAC [INT_DISCRETE]);

val variant_rule = store_thm
  ("variant_rule",
   ``!(g :'a state -> bool) (body :'a command) (Inv :'a state -> bool)
       (H :int) (L :int) (e :posreal).
      (0 :posreal) < e /\ e <= (1 :posreal) /\
      Leq
        (\(s :'a state).
           (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
        (wp body
           (\(s :'a state).
              (if Inv s then (1 :posreal) else (0 :posreal)))) /\
      Leq
        (\(s :'a state).
           (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
        (\(s :'a state).
           (if L <= (Var :'a state -> int) s /\ Var s < H then
              (1 :
            posreal)
            else
              (0 :
            posreal))) /\
      (!(N :int).
         Leq
           (\(s :'a state).
              (if g s /\ Inv s /\ (Var s = N) then e else (0 :posreal)))
           (wp body
              (\(s :'a state).
                 (if Var s < N then (1 :posreal) else (0 :posreal))))) ==>
      Leq
        (\(s :'a state).
           (if Inv s then posreal_pow e (Num (H - L)) else (0 :posreal)))
        (wp (While g body) (One :'a state expect))``,
RW_TAC std_ss []
++ `!(N :int).
      Leq
        (\(s :'a state).
           (if
              (g :'a state -> bool) s /\ (Inv :'a state -> bool) s /\
              ((Var :'a state -> int) s = N)
            then
              (e :posreal)
            else
              (0 :
            posreal)))
        (wp (body :'a command)
           (\(s :'a state).
              (if Inv s /\ Var s < N then (1 :posreal) else (0 :posreal))))`
	by (GEN_TAC 
	    ++ `wp (body :'a command)
      (\(s :'a state).
         (if
            (Inv :'a state -> bool) s /\ (Var :'a state -> int) s < (N :int)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) =
    wp body
      (Conj (\(s :'a state). (if Inv s then (1 :posreal) else (0 :posreal)))
         (\(s :'a state).
            (if Var s < N then (1 :posreal) else (0 :posreal))))`
		by (`(\(s :'a state).
       (if
          (Inv :'a state -> bool) s /\ (Var :'a state -> int) s < (N :int)
        then
          (1 :
        posreal)
        else
          (0 :
        posreal))) =
    Conj (\(s :'a state). (if Inv s then (1 :posreal) else (0 :posreal)))
      (\(s :'a state). (if Var s < N then (1 :posreal) else (0 :posreal)))`
			by (RW_TAC std_ss [FUN_EQ_THM, Conj_def]
			    ++ RW_TAC posreal_ss []
			    ++ FULL_SIMP_TAC std_ss [])
		    ++ RW_TAC std_ss [])
	    ++ RW_TAC std_ss []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (\(s :'a state).
         (if
            (g :'a state -> bool) s /\ (Inv :'a state -> bool) s /\
            ((Var :'a state -> int) s = (N :int))
          then
            (e :posreal)
          else
            (0 :
          posreal)))
      (Conj
         (\(s :'a state).
            (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
         (\(s :'a state).
            (if g s /\ Inv s /\ (Var s = N) then e else (0 :posreal))))`
		by (RW_TAC std_ss [Leq_def, Conj_def]
	            ++ RW_TAC posreal_ss [add_comm, add_sub]
	            ++ FULL_SIMP_TAC posreal_ss [])
	    ++ Suff `Leq
      (Conj
         (\(s :'a state).
            (if (g :'a state -> bool) s /\ (Inv :'a state -> bool) s then
               (1 :
             posreal)
             else
               (0 :
             posreal)))
         (\(s :'a state).
            (if g s /\ Inv s /\ ((Var :'a state -> int) s = (N :int)) then
               (e :posreal)
             else
               (0 :
             posreal))))
      (wp (body :'a command)
         (Conj
            (\(s :'a state). (if Inv s then (1 :posreal) else (0 :posreal)))
            (\(s :'a state).
               (if Var s < N then (1 :posreal) else (0 :posreal)))))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq (Conj (wp body (\s. if Inv s then 1 else 0))
			  (wp body (\s. if (Var s < N) then 1 else 0)))
		    (wp body (Conj (\s. (if Inv s then 1 else 0))
            			   (\s. (if Var s < N then 1 else 0))))`
		by METIS_TAC [wp_conj]
	    ++ Suff `Leq (Conj (\s. (if g s /\ Inv s then 1 else 0))
         		       (\s. (if g s /\ Inv s /\ (Var s = N) then e else 0)))
			 (Conj (wp body (\s. (if Inv s then 1 else 0)))
               		       (wp body (\s. (if Var s < N then 1 else 0))))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ FULL_SIMP_TAC std_ss [Leq_def, Conj_def]
	    ++ GEN_TAC
	    ++ MATCH_MP_TAC sub_mono
	    ++ SIMP_TAC posreal_ss []
	    ++ METIS_TAC [le_add2])
++ `!(n :num).
      Leq
        (\(s :'a state).
           (if
              (Inv :'a state -> bool) s /\
              (Var :'a state -> int) s < (L :int) + (& n :int)
            then
              posreal_pow (e :posreal) n
            else
              (0 :
            posreal)))
        (wp
           (While (\(s :'a state). (g :'a state -> bool) s)
              (body :'a command)) (One :'a state expect))`
	by (GEN_TAC
	    ++ Induct_on `n`
	    >> (RW_TAC int_ss [posreal_pow_def]
		++ `Leq
      (\(s :'a state).
         (if
            (Inv :'a state -> bool) s /\ (Var :'a state -> int) s < (L :int)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (\(s :'a state).
         (if ~(g :'a state -> bool) s then (1 :posreal) else (0 :posreal)))`
			by (FULL_SIMP_TAC std_ss [Leq_def]
			    ++ GEN_TAC
			    ++ RW_TAC posreal_ss []
			    ++ `(if
       (g :'a state -> bool) (s :'a state) /\ (Inv :'a state -> bool) s
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) <=
    (if (L :int) <= (Var :'a state -> int) s /\ Var s < (H :int) then
       (1 :
     posreal)
     else
       (0 :
     posreal))`
				by METIS_TAC []
			    ++ `(if
       (g :'a state -> bool) (s :'a state) /\ (Inv :'a state -> bool) s
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) =
    (1 :
    posreal)` 
				by RW_TAC posreal_ss []
			    ++ `(if
       (L :int) <= (Var :'a state -> int) (s :'a state) /\ Var s < (H :int)
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) =
    (0 :
    posreal)` 
				by (RW_TAC posreal_ss []
	    		            ++ FULL_SIMP_TAC int_ss [int_le])
			    ++ `~((1:posreal)<=(0:posreal))`
				by RW_TAC posreal_ss [le_zero]
			    ++ FULL_SIMP_TAC posreal_ss [])
		++ `Leq
      (\(s :'a state).
         (if ~(g :'a state -> bool) s then (1 :posreal) else (0 :posreal)))
      (wp (While (\(s :'a state). g s) (body :'a command))
         (One :'a state expect))`
			by (FULL_SIMP_TAC std_ss [Leq_def]
			    ++ GEN_TAC
			    ++ RW_TAC posreal_ss [zero_le, wp_def, cond_eta]
			    ++ `monotonic
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))`
				by (RW_TAC std_ss [monotonic_def, Leq_def]
	    			    ++ Cases_on `g s'`
	    			    >> METIS_TAC [wp_mono, Leq_def]
	    			    ++ RW_TAC posreal_ss [One_def])
			    ++ `lfp
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))
      (expect_lfp
         (\(e :'a state expect) (s :'a state).
            (if g s then wp body e s else One s)))`
				by METIS_TAC [expect_lfp_def]
			    ++ FULL_SIMP_TAC std_ss [lfp_def, expect_def]
			    ++ Suff `(1 :posreal) <=
    (\(s :'a state).
       (if (g :'a state -> bool) s then
          wp (body :'a command)
            (expect_lfp
               (\(e :'a state expect) (s :'a state).
                  (if g s then wp body e s else One s))) s
        else
          One s)) (s :'a state)`
			    >> METIS_TAC []
			    ++ RW_TAC posreal_ss [One_def])
		++ METIS_TAC [leq_trans])
	    ++ `Leq
      (\(s :'a state).
         (if
            (Inv :'a state -> bool) s /\
            (Var :'a state -> int) s < (L :int) + (& (SUC (n :num)) :int)
          then
            posreal_pow (e :posreal) (SUC n)
          else
            (0 :
          posreal)))
      (Max
         (\(s :'a state).
            (\(s :'a state).
               (if (g :'a state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :'a state).
               (if Inv s /\ Var s < L + (& (SUC n) :int) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))) s)
         (\(s :'a state).
            (\(s :'a state). (if ~g s then (1 :posreal) else (0 :posreal)))
              s *
            (\(s :'a state).
               (if Inv s /\ Var s < L + (& (SUC n) :int) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))) s))`
		by (RW_TAC std_ss [Max_def, Leq_def]
		    ++ Cases_on `g s`
		    ++ RW_TAC posreal_ss [])
	    ++ Suff `Leq
      (Max
         (\(s :'a state).
            (\(s :'a state).
               (if (g :'a state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :'a state).
               (if
                  (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s <
                  (L :int) + (& (SUC (n :num)) :int)
                then
                  posreal_pow (e :posreal) (SUC n)
                else
                  (0 :
                posreal))) s)
         (\(s :'a state).
            (\(s :'a state). (if ~g s then (1 :posreal) else (0 :posreal)))
              s *
            (\(s :'a state).
               (if Inv s /\ Var s < L + (& (SUC n) :int) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))) s))
      (wp (While (\(s :'a state). g s) (body :'a command))
         (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (\(s :'a state).
         (if ~(g :'a state -> bool) s then (1 :posreal) else (0 :posreal)))
      (wp (While (\(s :'a state). g s) (body :'a command))
         (One :'a state expect))`
			by (FULL_SIMP_TAC std_ss [Leq_def]
			    ++ GEN_TAC
			    ++ RW_TAC posreal_ss [zero_le, wp_def, cond_eta]
			    ++ `monotonic
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))`
				by (RW_TAC std_ss [monotonic_def, Leq_def]
	    			    ++ Cases_on `g s'`
	    			    >> METIS_TAC [wp_mono, Leq_def]
	    			    ++ RW_TAC posreal_ss [One_def])
			    ++ `lfp
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))
      (expect_lfp
         (\(e :'a state expect) (s :'a state).
            (if g s then wp body e s else One s)))`
				by METIS_TAC [expect_lfp_def]
			    ++ FULL_SIMP_TAC std_ss [lfp_def, expect_def]
			    ++ Suff `(1 :posreal) <=
    (\(s :'a state).
       (if (g :'a state -> bool) s then
          wp (body :'a command)
            (expect_lfp
               (\(e :'a state expect) (s :'a state).
                  (if g s then wp body e s else One s))) s
        else
          One s)) (s :'a state)`
			    >> METIS_TAC []
			    ++ RW_TAC posreal_ss [One_def])
	    ++ `Leq
      (Max
         (\(s :'a state).
            (\(s :'a state).
               (if (g :'a state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :'a state).
               (if
                  (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s <
                  (L :int) + (& (SUC (n :num)) :int)
                then
                  posreal_pow (e :posreal) (SUC n)
                else
                  (0 :
                posreal))) s)
         (\(s :'a state).
            (\(s :'a state). (if ~g s then (1 :posreal) else (0 :posreal)))
              s *
            (\(s :'a state).
               (if Inv s /\ Var s < L + (& (SUC n) :int) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))) s))
      (Max
         (\(s :'a state).
            (\(s :'a state). (if g s then (1 :posreal) else (0 :posreal)))
              s *
            (\(s :'a state).
               (if Inv s /\ Var s < L + (& (SUC n) :int) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))) s)
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ Cases_on `g s`
		    ++ RW_TAC posreal_ss []
		    ++ Suff `posreal_pow (e :posreal) (SUC (n :num)) <= (1 :posreal)`
		    >> (`(1 :posreal) <=
    wp (While (\(s :'a state). (g :'a state -> bool) s) (body :'a command))
      (One :'a state expect) (s :'a state)`
			by (FULL_SIMP_TAC posreal_ss [Leq_def]
			    ++ METIS_TAC [])
		        ++ METIS_TAC [le_trans])
		    ++ METIS_TAC [posreal_pow_1bounded_base_1bounded])
	    ++ Suff `Leq
      (Max
         (\(s :'a state).
            (\(s :'a state).
               (if (g :'a state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :'a state).
               (if
                  (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s <
                  (L :int) + (& (SUC (n :num)) :int)
                then
                  posreal_pow (e :posreal) (SUC n)
                else
                  (0 :
                posreal))) s)
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (\(s :'a state).
            (\(s :'a state).
               (if (g :'a state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :'a state).
               (if
                  (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s <
                  (L :int) + (& (SUC (n :num)) :int)
                then
                  posreal_pow (e :posreal) (SUC n)
                else
                  (0 :
                posreal))) s)
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))
      (Max
         (Max
            (\(s :'a state).
               (if g s /\ Inv s /\ Var s < L + (& n :int) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal)))
            (\(s :'a state).
               (if g s /\ Inv s /\ (Var s = L + (& n :int)) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ `(Var :'a state -> int) (s :'a state) <
    (L :int) + (& (SUC (n :num)) :int) =
    Var s <= L + (& n :int)`
			by RW_TAC int_ss [INT, INT_ADD_ASSOC, INT_LE_EQ_LT_ADD1]
		    ++ `(Var :'a state -> int) (s :'a state) <= (L :int) + (& (n :num) :int) =
    Var s < L + (& n :int) \/ (Var s = L + (& n :int))`
			by RW_TAC int_ss [INT_LE_LT]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ Cases_on `Var s < L + &n`
		    ++ ASM_REWRITE_TAC []
		    ++ Cases_on `g s`
		    ++ ASM_REWRITE_TAC []
		    ++ RW_TAC int_ss [max_lzero, mul_lone, mul_lzero, max_refl]
		    ++ RW_TAC posreal_ss [zero_lt_posreal_pow])
	    ++ Suff `Leq
      (Max
         (Max
            (\(s :'a state).
               (if
                  (g :'a state -> bool) s /\ (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s < (L :int) + (& (n :num) :int)
                then
                  posreal_pow (e :posreal) (SUC n)
                else
                  (0 :
                posreal)))
            (\(s :'a state).
               (if g s /\ Inv s /\ (Var s = L + (& n :int)) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (Max
            (\(s :'a state).
               (if
                  (g :'a state -> bool) s /\ (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s < (L :int) + (& (n :num) :int)
                then
                  posreal_pow (e :posreal) (SUC n)
                else
                  (0 :
                posreal)))
            (\(s :'a state).
               (if g s /\ Inv s /\ (Var s = L + (& n :int)) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))
      (Max
         (Max
            (\(s :'a state).
               e *
               wp (While (\(s :'a state). g s) body) (One :'a state expect)
                 s)
            (\(s :'a state).
               (if g s /\ Inv s /\ (Var s = L + (& n :int)) then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ `!(x :posreal). (e :posreal) * x <= x`
			by METIS_TAC [mul_lone, le_refl, le_mul2]
		    ++ RW_TAC posreal_ss []
		    ++ FULL_SIMP_TAC int_ss [DE_MORGAN_THM, INT_LT_IMP_NE, Leq_def]
		    ++ RW_TAC std_ss [posreal_pow_def]
		    ++ `max
      ((e :posreal) *
       wp
         (While (\(s :'a state). (g :'a state -> bool) s)
            (body :'a command)) (One :'a state expect) (s :'a state))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect) s) =
    wp (While (\(s :'a state). g s) body) (One :'a state expect) s`
				by METIS_TAC [preal_max_def]
		    ++ `max
      (max
         ((e :posreal) *
          wp
            (While (\(s :'a state). (g :'a state -> bool) s)
               (body :'a command)) (One :'a state expect) (s :'a state))
         (e * posreal_pow e (n :num)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect) s) =
    max (e * posreal_pow e n)
      (wp (While (\(s :'a state). g s) body) (One :'a state expect) s)`
				by METIS_TAC [max_swap, preal_max_def]
		    ++ METIS_TAC [preal_max_def, le_trans, le_refl])
	    ++ Suff `Leq
      (Max
         (Max
            (\(s :'a state).
               (e :posreal) *
               wp
                 (While (\(s :'a state). (g :'a state -> bool) s)
                    (body :'a command)) (One :'a state expect) s)
            (\(s :'a state).
               (if
                  g s /\ (Inv :'a state -> bool) s /\
                  ((Var :'a state -> int) s = (L :int) + (& (n :num) :int))
                then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (Max
            (\(s :'a state).
               (e :posreal) *
               wp
                 (While (\(s :'a state). (g :'a state -> bool) s)
                    (body :'a command)) (One :'a state expect) s)
            (\(s :'a state).
               (if
                  g s /\ (Inv :'a state -> bool) s /\
                  ((Var :'a state -> int) s = (L :int) + (& (n :num) :int))
                then
                  posreal_pow e (SUC n)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))
      (Max
         (\(s :'a state).
            posreal_pow e n *
            wp body
              (\(s :'a state).
                 (if Inv s /\ Var s < L + (& n :int) then
                    (1 :
                  posreal)
                  else
                    (0 :
                  posreal))) s)
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ `!(x :posreal). (e :posreal) * x <= x`
			by METIS_TAC [mul_lone, le_refl, le_mul2]
		    ++ `max
      (max
         ((e :posreal) *
          wp
            (While (\(s :'a state). (g :'a state -> bool) s)
               (body :'a command)) (One :'a state expect) (s :'a state))
         (if
            g s /\ (Inv :'a state -> bool) s /\
            ((Var :'a state -> int) s = (L :int) + (& (n :num) :int))
          then
            posreal_pow e (SUC n)
          else
            (0 :
          posreal)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect) s) =
    max
      (if g s /\ Inv s /\ (Var s = L + (& n :int)) then
         posreal_pow e (SUC n)
       else
         (0 :
       posreal))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect) s)`
			by (`max
      (max
         ((e :posreal) *
          wp
            (While (\(s :'a state). (g :'a state -> bool) s)
               (body :'a command)) (One :'a state expect) (s :'a state))
         (if
            g s /\ (Inv :'a state -> bool) s /\
            ((Var :'a state -> int) s = (L :int) + (& (n :num) :int))
          then
            posreal_pow e (SUC n)
          else
            (0 :
          posreal)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect) s) =
    max
      (if g s /\ Inv s /\ (Var s = L + (& n :int)) then
         posreal_pow e (SUC n)
       else
         (0 :
       posreal))
      (max
         (e *
          wp (While (\(s :'a state). g s) body) (One :'a state expect) s)
         (wp (While (\(s :'a state). g s) body) (One :'a state expect) s))`
				by METIS_TAC [max_swap]
			    ++ METIS_TAC [preal_max_def])
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(if
       (g :'a state -> bool) (s :'a state) /\ (Inv :'a state -> bool) s /\
       ((Var :'a state -> int) s = (L :int) + (& (n :num) :int))
     then
       posreal_pow (e :posreal) (SUC n)
     else
       (0 :
     posreal)) =
    posreal_pow e n *
    (if g s /\ Inv s /\ (Var s = L + (& n :int)) then e else (0 :posreal))`
			by RW_TAC posreal_ss [posreal_pow_def, mul_comm, mul_rzero]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `posreal_pow (e :posreal) (n :num) *
    (if
       (g :'a state -> bool) (s :'a state) /\ (Inv :'a state -> bool) s /\
       ((Var :'a state -> int) s = (L :int) + (& n :int))
     then
       e
     else
       (0 :
     posreal)) <=
    posreal_pow e n *
    wp (body :'a command)
      (\(s :'a state).
         (if Inv s /\ Var s < L + (& n :int) then
            (1 :
          posreal)
          else
            (0 :
          posreal))) s`
			by (`(if
       (g :'a state -> bool) (s :'a state) /\ (Inv :'a state -> bool) s /\
       ((Var :'a state -> int) s = (L :int) + (& (n :num) :int))
     then
       (e :posreal)
     else
       (0 :
     posreal)) <=
    wp (body :'a command)
      (\(s :'a state).
         (if Inv s /\ Var s < L + (& n :int) then
            (1 :
          posreal)
          else
            (0 :
          posreal))) s`
				by (FULL_SIMP_TAC posreal_ss [Leq_def]
				    ++ METIS_TAC [])
			    ++ METIS_TAC [le_refl, le_mul2])
		    ++ RW_TAC posreal_ss [preal_max_def, le_refl, le_trans]
		    ++ METIS_TAC [le_trans, le_total])
	    ++ Suff `Leq
      (Max
         (\(s :'a state).
            posreal_pow (e :posreal) (n :num) *
            wp (body :'a command)
              (\(s :'a state).
                 (if
                    (Inv :'a state -> bool) s /\
                    (Var :'a state -> int) s < (L :int) + (& n :int)
                  then
                    (1 :
                  posreal)
                  else
                    (0 :
                  posreal))) s)
         (wp (While (\(s :'a state). (g :'a state -> bool) s) body)
            (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `(\(s :'a state).
       posreal_pow (e :posreal) (n :num) *
       wp (body :'a command)
         (\(s :'a state).
            (if
               (Inv :'a state -> bool) s /\
               (Var :'a state -> int) s < (L :int) + (& n :int)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))) s) =
    wp body
      (\(s :'a state).
         (if Inv s /\ Var s < L + (& n :int) then
            posreal_pow e n
          else
            (0 :
          posreal)))`
		by (RW_TAC std_ss [FUN_EQ_THM]
		    ++ `(\(s :'a state).
       (if
          (Inv :'a state -> bool) s /\
          (Var :'a state -> int) s < (L :int) + (& (n :num) :int)
        then
          posreal_pow (e :posreal) n
        else
          (0 :
        posreal))) =
    (\(s :'a state).
       posreal_pow e n *
       (if Inv s /\ Var s < L + (& n :int) then
          (1 :
        posreal)
        else
          (0 :
        posreal)))`
			by METIS_TAC [FUN_EQ_THM, mul_rone, mul_rzero]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `posreal_pow (e :posreal) (n :num) *
    wp (body :'a command)
      (\(s :'a state).
         (if
            (Inv :'a state -> bool) s /\
            (Var :'a state -> int) s < (L :int) + (& n :int)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) (s :'a state) =
    wp body
      (\(s :'a state).
         posreal_pow e n *
         (\(s :'a state).
            (if Inv s /\ Var s < L + (& n :int) then
               (1 :
             posreal)
             else
               (0 :
             posreal))) s) s`
			by METIS_TAC [wp_scale]
		    ++ METIS_TAC [])
	    ++ ASM_REWRITE_TAC []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (wp (body :'a command)
            (\(s :'a state).
               (if
                  (Inv :'a state -> bool) s /\
                  (Var :'a state -> int) s < (L :int) + (& (n :num) :int)
                then
                  posreal_pow (e :posreal) n
                else
                  (0 :
                posreal))))
         (wp (While (\(s :'a state). (g :'a state -> bool) s) body)
            (One :'a state expect)))
      (Max
         (wp body
            (wp (While (\(s :'a state). g s) body) (One :'a state expect)))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))`
		by (`Leq
      (wp (body :'a command)
         (\(s :'a state).
            (if
               (Inv :'a state -> bool) s /\
               (Var :'a state -> int) s < (L :int) + (& (n :num) :int)
             then
               posreal_pow (e :posreal) n
             else
               (0 :
             posreal))))
      (wp body
         (wp (While (\(s :'a state). (g :'a state -> bool) s) body)
            (One :'a state expect)))`
			by METIS_TAC [wp_mono]
		    ++ RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ FULL_SIMP_TAC posreal_ss [Leq_def]
		    ++ RW_TAC posreal_ss [preal_max_def, le_refl, le_trans]
		    ++ METIS_TAC [le_trans, le_total])
	    ++ Suff `Leq
      (Max
         (wp (body :'a command)
            (wp (While (\(s :'a state). (g :'a state -> bool) s) body)
               (One :'a state expect)))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (wp (body :'a command)
         (wp (While (\(s :'a state). (g :'a state -> bool) s) body)
            (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
		by (`monotonic
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))`
				by (RW_TAC std_ss [monotonic_def, Leq_def]
	    			    ++ Cases_on `g s`
	    			    >> METIS_TAC [wp_mono, Leq_def]
	    			    ++ RW_TAC posreal_ss [One_def])
		    ++ `lfp
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))
      (expect_lfp
         (\(e :'a state expect) (s :'a state).
            (if g s then wp body e s else One s)))`
			by METIS_TAC [expect_lfp_def]
		    ++ FULL_SIMP_TAC std_ss [Leq_def, wp_def, cond_eta, lfp_def, expect_def]
		    ++ GEN_TAC
		    ++ Suff `wp (body :'a command)
      (expect_lfp
         (\(e :'a state expect) (s :'a state).
            (if (g :'a state -> bool) s then wp body e s else One s)))
      (s :'a state) <=
    (\(s :'a state).
       (if g s then
          wp body
            (expect_lfp
               (\(e :'a state expect) (s :'a state).
                  (if g s then wp body e s else One s))) s
        else
          One s)) s`
		    >> METIS_TAC []
		    ++ RW_TAC posreal_ss [le_refl, One_def]
		    ++ `expect_lfp
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            (1 :
          posreal))) =
    wp (While (\(s :'a state). g s) body) (One :'a state expect)` 
			by RW_TAC posreal_ss [wp_def, cond_eta, One_def]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `wp (body :'a command)
      (wp (While (\(s :'a state). (g :'a state -> bool) s) body)
         (One :'a state expect)) (s :'a state) =
    wp (Seq body (While (\(s :'a state). g s) body)) (One :'a state expect)
      s`
			by RW_TAC posreal_ss [wp_def]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ METIS_TAC [Leq_def, One_def, Term_Leq_One])
	    ++ FULL_SIMP_TAC posreal_ss [Leq_def, Max_def, preal_max_def, le_refl])
++ `(\(s :'a state).
       (if (Inv :'a state -> bool) s then
          posreal_pow (e :posreal) (Num ((H :int) - (L :int)))
        else
          (0 :
        posreal))) =
    Max
      (\(s :'a state).
         (if (g :'a state -> bool) s /\ Inv s then
            posreal_pow e (Num (H - L))
          else
            (0 :
          posreal)))
      (\(s :'a state).
         (if ~g s /\ Inv s then
            posreal_pow e (Num (H - L))
          else
            (0 :
          posreal)))`
		by (RW_TAC posreal_ss [FUN_EQ_THM, Max_def]
		    ++ Cases_on `g s`
		    ++ METIS_TAC [max_lzero, max_rzero])
	    ++ ASM_REWRITE_TAC []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (\(s :'a state).
         (if ~(g :'a state -> bool) s then (1 :posreal) else (0 :posreal)))
      (wp (While (\(s :'a state). g s) (body :'a command))
         (One :'a state expect))`
		by (FULL_SIMP_TAC std_ss [Leq_def]
		    ++ GEN_TAC
		    ++ RW_TAC posreal_ss [zero_le, wp_def, cond_eta]
		    ++ `monotonic
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))`
			by (RW_TAC std_ss [monotonic_def, Leq_def]
    			    ++ Cases_on `g s'`
    			    >> METIS_TAC [wp_mono, Leq_def]
    			    ++ RW_TAC posreal_ss [One_def])
		    ++ `lfp
      ((expect :'a state expect -> bool),
       (Leq :'a state expect -> 'a state expect -> bool))
      (\(e :'a state expect) (s :'a state).
         (if (g :'a state -> bool) s then
            wp (body :'a command) e s
          else
            One s))
      (expect_lfp
         (\(e :'a state expect) (s :'a state).
            (if g s then wp body e s else One s)))`
			by METIS_TAC [expect_lfp_def]
		    ++ FULL_SIMP_TAC std_ss [lfp_def, expect_def]
		    ++ Suff `(1 :posreal) <=
    (\(s :'a state).
       (if (g :'a state -> bool) s then
          wp (body :'a command)
            (expect_lfp
               (\(e :'a state expect) (s :'a state).
                  (if g s then wp body e s else One s))) s
        else
          One s)) (s :'a state)`
		    >> METIS_TAC []
		    ++ RW_TAC posreal_ss [One_def])
	    ++ `Leq
      (Max
         (\(s :'a state).
            (if (g :'a state -> bool) s /\ (Inv :'a state -> bool) s then
               posreal_pow (e :posreal) (Num ((H :int) - (L :int)))
             else
               (0 :
             posreal)))
         (\(s :'a state).
            (if ~g s /\ Inv s then
               posreal_pow e (Num (H - L))
             else
               (0 :
             posreal))))
      (Max
         (\(s :'a state).
            (if g s /\ Inv s then
               posreal_pow e (Num (H - L))
             else
               (0 :
             posreal)))
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))`
		by (FULL_SIMP_TAC posreal_ss [Leq_def, Max_def]
		    ++ GEN_TAC
		    ++ Cases_on `g s`
		    ++ RW_TAC posreal_ss [preal_max_def, max_lzero, max_rzero]
		    ++ METIS_TAC [le_trans, posreal_pow_1bounded_base_1bounded])
	    ++ Suff `Leq
      (Max
         (\(s :'a state).
            (if (g :'a state -> bool) s /\ (Inv :'a state -> bool) s then
               posreal_pow (e :posreal) (Num ((H :int) - (L :int)))
             else
               (0 :
             posreal)))
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (\(s :'a state).
            (if (g :'a state -> bool) s /\ (Inv :'a state -> bool) s then
               posreal_pow (e :posreal) (Num ((H :int) - (L :int)))
             else
               (0 :
             posreal)))
         (wp (While (\(s :'a state). g s) (body :'a command))
            (One :'a state expect)))
      (Max
         (\(s :'a state).
            (if Inv s /\ L <= (Var :'a state -> int) s /\ Var s < H then
               posreal_pow e (Num (H - L))
             else
               (0 :
             posreal)))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))`
		by (FULL_SIMP_TAC posreal_ss [Leq_def, Max_def]
		    ++ GEN_TAC
		    ++ `(if
       (g :'a state -> bool) (s :'a state) /\ (Inv :'a state -> bool) s
     then
       posreal_pow (e :posreal) (Num ((H :int) - (L :int)))
     else
       (0 :
     posreal)) <=
    (if Inv s /\ L <= (Var :'a state -> int) s /\ Var s < H then
       posreal_pow e (Num (H - L))
     else
       (0 :
     posreal))`
			by (Cases_on `g s /\ Inv s`
			    >> (`(L :int) <= (Var :'a state -> int) (s :'a state) /\ Var s < (H :int)`
				   by (`(1 :posreal) <=
    (if
       (L :int) <= (Var :'a state -> int) (s :'a state) /\ Var s < (H :int)
     then
       (1 :
     posreal)
     else
       (0 :
     posreal))` 
						by METIS_TAC []
				       ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
				       ++ FULL_SIMP_TAC posreal_ss [])
				++ METIS_TAC [le_refl])
			    ++ METIS_TAC [zero_le])
		    ++ METIS_TAC [max_le2_imp, le_refl])
	    ++ Suff `Leq
      (Max
         (\(s :'a state).
            (if
               (Inv :'a state -> bool) s /\
               (L :int) <= (Var :'a state -> int) s /\ Var s < (H :int)
             then
               posreal_pow (e :posreal) (Num (H - L))
             else
               (0 :
             posreal)))
         (wp
            (While (\(s :'a state). (g :'a state -> bool) s)
               (body :'a command)) (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (\(s :'a state).
            (if
               (Inv :'a state -> bool) s /\
               (L :int) <= (Var :'a state -> int) s /\ Var s < (H :int)
             then
               posreal_pow (e :posreal) (Num (H - L))
             else
               (0 :
             posreal)))
         (wp
            (While (\(s :'a state). (g :'a state -> bool) s)
               (body :'a command)) (One :'a state expect)))
      (Max
         (\(s :'a state).
            (if Inv s /\ Var s < L + (& (Num (H - L)) :int) then
               posreal_pow e (Num (H - L))
             else
               (0 :
             posreal)))
         (wp (While (\(s :'a state). g s) body) (One :'a state expect)))`
		by (FULL_SIMP_TAC posreal_ss [Leq_def, Max_def]
		    ++ GEN_TAC
		    ++ `(if
       (Inv :'a state -> bool) (s :'a state) /\
       (L :int) <= (Var :'a state -> int) s /\ Var s < (H :int)
     then
       posreal_pow (e :posreal) (Num (H - L))
     else
       (0 :
     posreal)) <=
    (if Inv s /\ Var s < L + (& (Num (H - L)) :int) then
       posreal_pow e (Num (H - L))
     else
       (0 :
     posreal))`
			by (Cases_on `L < H`
			    >> (`(0 :int) < (H :int) - (L :int)` by RW_TAC int_ss [INT_SUB_LT]
				++ `(& (Num ((H :int) - (L :int))) :int) = H - L` by METIS_TAC [INT_OF_NUM_POSINT_EQ]
				++ ASM_REWRITE_TAC [INT_SUB_ADD2]
				++ METIS_TAC [le_refl, INT_LT_IMP_LE, zero_le])
			    ++ `~((L :int) <= (Var :'a state -> int) (s :'a state) /\ Var s < (H :int))` by METIS_TAC [INT_LET_TRANS, INT_LT_IMP_LE]
			    ++ METIS_TAC [zero_le])
		    ++ METIS_TAC [max_le2_imp, le_refl])
	    ++ Suff `Leq
      (Max
         (\(s :'a state).
            (if
               (Inv :'a state -> bool) s /\
               (Var :'a state -> int) s <
               (L :int) + (& (Num ((H :int) - L)) :int)
             then
               posreal_pow (e :posreal) (Num (H - L))
             else
               (0 :
             posreal)))
         (wp
            (While (\(s :'a state). (g :'a state -> bool) s)
               (body :'a command)) (One :'a state expect)))
      (wp (While (\(s :'a state). g s) body) (One :'a state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ FULL_SIMP_TAC posreal_ss [Leq_def, Max_def]
	    ++ METIS_TAC [le_refl, max_le]);

val variant_rule2 = store_thm
  ("variant_rule2",
   ``!(g :'a state -> bool) (body :'a command) (Inv :'a state -> bool)
            (H :int) (L :int).
           Leq
             (\(s :'a state).
                (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
             (wp body
                (\(s :'a state).
                   (if Inv s then (1 :posreal) else (0 :posreal)))) /\
           Leq
             (\(s :'a state).
                (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
             (\(s :'a state).
                (if L <= (Var :'a state -> int) s /\ Var s < H then
                   (1 :
                 posreal)
                 else
                   (0 :
                 posreal))) /\
           (!(N :int).
              Leq
                (\(s :'a state).
                   (if g s /\ Inv s /\ (Var s = N) then
                      (1 :
                    posreal)
                    else
                      (0 :
                    posreal)))
                (wp body
                   (\(s :'a state).
                      (if Var s < N then
                         (1 :
                       posreal)
                       else
                         (0 :
                       posreal))))) ==>
           Leq
             (\(s :'a state).
                (if Inv s then (1 :posreal) else (0 :posreal)))
             (wp (While g body) (One :'a state expect))``,
   RW_TAC posreal_ss [] 
   ++ `Leq
      (\(s :'a state).
         (if (Inv :'a state -> bool) s then
            posreal_pow (1 :posreal) (Num ((H :int) - (L :int)))
          else
            (0 :
          posreal)))
      (wp (While (g :'a state -> bool) (body :'a command))
         (One :'a state expect))` 
	by (`(0 :posreal) < (1 :posreal)` by RW_TAC posreal_ss []
   	    ++ `(1:posreal) <= (1:posreal)` by RW_TAC posreal_ss [le_refl]
	    ++ METIS_TAC [variant_rule])
   ++ `(\(s :'a state).
       (if (Inv :'a state -> bool) s then (1 :posreal) else (0 :posreal))) =
    (\(s :'a state).
       (if Inv s then
          posreal_pow (1 :posreal) (Num ((H :int) - (L :int)))
        else
          (0 :
        posreal)))`
	by METIS_TAC [FUN_EQ_THM, posreal_pow_base1_eq_1]
   ++ ASM_REWRITE_TAC []);

val While_variant_rule = store_thm
  ("While_variant_rule",
``!(i :string) (n :string) (body :value command).
           ~(n = i) /\
           Leq
             (\(s :value state).
                (if
                   (\(s :value state). (0 :int) <= int_of_value (s i)) s
                 then
                   (1 :
                 posreal)
                 else
                   (0 :
                 posreal)))
             (wp body
                (\(s :value state).
                   (if
                      (\(s :value state). (0 :int) <= int_of_value (s i)) s
                    then
                      (1 :
                    posreal)
                    else
                      (0 :
                    posreal)))) /\
           (!(N :int).
              Leq
                (\(s :value state).
                   (if
                      (\(s :value state).
                         int_of_value (s i) < int_of_value (s n)) s /\
                      (\(s :value state). (0 :int) <= int_of_value (s i))
                        s /\
                      ((\(s :value state).
                          int_of_value (s n) - int_of_value (s i)) s =
                       N)
                    then
                      (1 :
                    posreal)
                    else
                      (0 :
                    posreal)))
                (wp body
                   (\(s :value state).
                      (if
                         (\(s :value state).
                            int_of_value (s n) - int_of_value (s i)) s <= N
                       then
                         (1 :
                       posreal)
                       else
                         (0 :
                       posreal))))) ==>
           Leq
             (\(s :value state).
                (if
                   (\(s :value state). (0 :int) <= int_of_value (s i)) s
                 then
                   (1 :
                 posreal)
                 else
                   (0 :
                 posreal)))
             (wp
                (While
                   (\(s :value state).
                      int_of_value (s i) < int_of_value (s n))
                   (Seq body
                      (Assign i
                         (\(s :value state).
                            Int (int_of_value (s i) + (1 :int))))))
                (One :value state expect))``,
REPEAT GEN_TAC
++ Q.ABBREV_TAC `Inv = (\(s :value state). (0 :int) <= int_of_value (s (i :string)))`
++ Q.ABBREV_TAC `g = (\(s :value state).
                int_of_value (s (i :string)) <
                int_of_value (s (n :string)))`
++ Q.ABBREV_TAC `Var = (\(s :value state).
                int_of_value (s (n :string)) -
                int_of_value (s (i :string)))`
++ Q.ABBREV_TAC `loopbody = Seq (body :value command)
               (Assign (i :string)
                  (\(s :value state). Int (int_of_value (s i) + (1 :int))))`
++ REPEAT STRIP_TAC
++ `Leq
      (\(s :value state).
         (if (g :value state -> bool) s /\ (Inv :value state -> bool) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp (loopbody :value command)
         (\(s :value state).
            (if Inv s then (1 :posreal) else (0 :posreal))))`
	by (Q.UNABBREV_TAC `Inv`
	    ++ Q.UNABBREV_TAC `g`
	    ++ Q.UNABBREV_TAC `loopbody`
	    ++ RW_TAC posreal_ss [wp_def, assign_eta, int_of_value_def]
	    ++ `Leq
      (wp (body :value command)
         (\(s :value state).
            (if
               (\(s :value state). (0 :int) <= int_of_value (s (i :string)))
                 s
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))
      (wp body
         (\(s :value state).
            (if (0 :int) <= int_of_value (s i) + (1 :int) then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
		by (MATCH_MP_TAC wp_mono
		    ++ RW_TAC posreal_ss [Leq_def]
		    ++ RW_TAC posreal_ss []
		    ++ METIS_TAC [INT_LE_ADD, INT_LE_01])
	    ++ Suff `Leq
      (\(s :value state).
         (if
            int_of_value (s (i :string)) < int_of_value (s (n :string)) /\
            (0 :int) <= int_of_value (s i)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (\(s :value state).
         (if (\(s :value state). (0 :int) <= int_of_value (s i)) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))`
	    >> METIS_TAC [leq_trans]
	    ++ RW_TAC posreal_ss [Leq_def]
	    ++ RW_TAC posreal_ss [le_refl])
++ ASM_REWRITE_TAC []
++ `!(N :int).
      Leq
        (\(s :value state).
           (if
              (g :value state -> bool) s /\ (Inv :value state -> bool) s /\
              ((Var :value state -> int) s = N)
            then
              (1 :
            posreal)
            else
              (0 :
            posreal)))
        (wp (loopbody :value command)
           (\(s :value state).
              (if Var s < N then (1 :posreal) else (0 :posreal))))`
	by (Q.UNABBREV_TAC `Inv`
	    ++ Q.UNABBREV_TAC `g`
	    ++ Q.UNABBREV_TAC `loopbody`
	    ++ Q.UNABBREV_TAC `Var`
	    ++ RW_TAC posreal_ss [wp_def, assign_eta, int_of_value_def]
	    ++ FULL_SIMP_TAC posreal_ss []
	    ++ `(\(s :value state).
       (if
          int_of_value (s (n :string)) -
          (int_of_value (s (i :string)) + (1 :int)) < (N :int)
        then
          (1 :
        posreal)
        else
          (0 :
        posreal))) =
    (\(s :value state).
       (if
          (\(s :value state). int_of_value (s n) - int_of_value (s i)) s <=
          N
        then
          (1 :
        posreal)
        else
          (0 :
        posreal)))`
		by (RW_TAC posreal_ss [FUN_EQ_THM]
		    ++ `int_of_value ((s :value state) (n :string)) -
    (int_of_value (s (i :string)) + (1 :int)) =
    int_of_value (s n) - int_of_value (s i) + ((0 :int) - (1 :int))` 
				by (`int_of_value ((s :value state) (n :string)) =
    int_of_value (s n) + (0 :int)` by RW_TAC int_ss []
				    ++ METIS_TAC [INT_ADD2_SUB2])
		    ++ ASM_REWRITE_TAC []
		    ++ FULL_SIMP_TAC int_ss [INT_LT_ADDNEG2, INT_LE_EQ_LT_ADD1])
	    ++ ASM_REWRITE_TAC []
	    ++ METIS_TAC [])
++ ASM_REWRITE_TAC []
++ `!(N :int).
      Leq
        (\(s :value state).
           (if
              (g :value state -> bool) s /\ (Inv :value state -> bool) s /\
              ((Var :value state -> int) s = N)
            then
              (1 :
            posreal)
            else
              (0 :
            posreal)))
        (wp (loopbody :value command)
           (\(s :value state).
              (if Inv s /\ Var s < N then (1 :posreal) else (0 :posreal))))`
	by (GEN_TAC 
	    ++ `wp (loopbody :value command)
      (\(s :value state).
         (if
            (Inv :value state -> bool) s /\
            (Var :value state -> int) s < (N :int)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) =
    wp loopbody
      (Conj
         (\(s :value state). (if Inv s then (1 :posreal) else (0 :posreal)))
         (\(s :value state).
            (if Var s < N then (1 :posreal) else (0 :posreal))))`
		by (`(\(s :value state).
       (if
          (Inv :value state -> bool) s /\
          (Var :value state -> int) s < (N :int)
        then
          (1 :
        posreal)
        else
          (0 :
        posreal))) =
    Conj (\(s :value state). (if Inv s then (1 :posreal) else (0 :posreal)))
      (\(s :value state).
         (if Var s < N then (1 :posreal) else (0 :posreal)))`
			by (RW_TAC std_ss [FUN_EQ_THM, Conj_def]
			    ++ RW_TAC posreal_ss []
			    ++ FULL_SIMP_TAC std_ss [])
		    ++ RW_TAC std_ss [])
	    ++ RW_TAC std_ss []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (\(s :value state).
         (if
            (g :value state -> bool) s /\ (Inv :value state -> bool) s /\
            ((Var :value state -> int) s = (N :int))
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (Conj
         (\(s :value state).
            (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
         (\(s :value state).
            (if g s /\ Inv s /\ (Var s = N) then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
		by (RW_TAC std_ss [Leq_def, Conj_def]
	            ++ RW_TAC posreal_ss [add_comm, add_sub]
	            ++ FULL_SIMP_TAC posreal_ss [])
	    ++ Suff `Leq
      (Conj
         (\(s :value state).
            (if
               (g :value state -> bool) s /\ (Inv :value state -> bool) s
             then
               (1 :
             posreal)
             else
               (0 :
             posreal)))
         (\(s :value state).
            (if
               g s /\ Inv s /\ ((Var :value state -> int) s = (N :int))
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))
      (wp (loopbody :value command)
         (Conj
            (\(s :value state).
               (if Inv s then (1 :posreal) else (0 :posreal)))
            (\(s :value state).
               (if Var s < N then (1 :posreal) else (0 :posreal)))))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Conj
         (wp (loopbody :value command)
            (\(s :value state).
               (if (Inv :value state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))))
         (wp loopbody
            (\(s :value state).
               (if (Var :value state -> int) s < (N :int) then
                  (1 :
                posreal)
                else
                  (0 :
                posreal)))))
      (wp loopbody
         (Conj
            (\(s :value state).
               (if Inv s then (1 :posreal) else (0 :posreal)))
            (\(s :value state).
               (if Var s < N then (1 :posreal) else (0 :posreal)))))`
		by METIS_TAC [wp_conj]
	    ++ Suff `Leq
      (Conj
         (\(s :value state).
            (if
               (g :value state -> bool) s /\ (Inv :value state -> bool) s
             then
               (1 :
             posreal)
             else
               (0 :
             posreal)))
         (\(s :value state).
            (if
               g s /\ Inv s /\ ((Var :value state -> int) s = (N :int))
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))
      (Conj
         (wp (loopbody :value command)
            (\(s :value state).
               (if Inv s then (1 :posreal) else (0 :posreal))))
         (wp loopbody
            (\(s :value state).
               (if Var s < N then (1 :posreal) else (0 :posreal)))))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ FULL_SIMP_TAC std_ss [Leq_def, Conj_def]
	    ++ GEN_TAC
	    ++ MATCH_MP_TAC sub_mono
	    ++ SIMP_TAC posreal_ss []
	    ++ METIS_TAC [le_add2])
++ `!(N :num).
      Leq
        (\(s :value state).
           (if
              (Inv :value state -> bool) s /\
              (Var :value state -> int) s < (1 :int) + (& N :int)
            then
              posreal_pow (1 :posreal) N
            else
              (0 :
            posreal)))
        (wp
           (While (\(s :value state). (g :value state -> bool) s)
              (loopbody :value command)) (One :value state expect))`
	by (GEN_TAC
	    ++ Induct_on `N`
	    >> (RW_TAC int_ss [posreal_pow_def]
		++ `Leq
      (\(s :value state).
         (if
            (Inv :value state -> bool) s /\
            (Var :value state -> int) s < (1 :int)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (\(s :value state).
         (if ~(g :value state -> bool) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))`
			by (Q.UNABBREV_TAC `g`
			    ++ Q.UNABBREV_TAC `Inv`
			    ++ Q.UNABBREV_TAC `Var`
			    ++ FULL_SIMP_TAC std_ss [Leq_def]
			    ++ GEN_TAC
			    ++ RW_TAC posreal_ss []
			    ++ `(0 :int) + int_of_value ((s :value state) (i :string)) <
    int_of_value (s (n :string))`
				by RW_TAC int_ss []
			    ++ `(0 :int) <
    int_of_value ((s :value state) (n :string)) -
    int_of_value (s (i :string))`
				by METIS_TAC [INT_LT_ADD_SUB]
			    ++ METIS_TAC [NO_INT_BETWEEN_ZERO_AND_ONE])
		++ `Leq
      (\(s :value state).
         (if ~(g :value state -> bool) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp (While (\(s :value state). g s) (loopbody :value command))
         (One :value state expect))`
			by (FULL_SIMP_TAC std_ss [Leq_def]
			    ++ GEN_TAC
			    ++ RW_TAC posreal_ss [zero_le, wp_def, cond_eta]
			    ++ `monotonic
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))`
				by (RW_TAC std_ss [monotonic_def, Leq_def]
	    			    ++ Cases_on `g s'`
	    			    >> METIS_TAC [wp_mono, Leq_def]
	    			    ++ RW_TAC posreal_ss [One_def])
			    ++ `lfp
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))
      (expect_lfp
         (\(e :value state expect) (s :value state).
            (if g s then wp loopbody e s else One s)))`
				by METIS_TAC [expect_lfp_def]
			    ++ FULL_SIMP_TAC std_ss [lfp_def, expect_def]
			    ++ Suff `(1 :posreal) <=
    (\(s :value state).
       (if (g :value state -> bool) s then
          wp (loopbody :value command)
            (expect_lfp
               (\(e :value state expect) (s :value state).
                  (if g s then wp loopbody e s else One s))) s
        else
          One s)) (s :value state)`
			    >> METIS_TAC []
			    ++ RW_TAC posreal_ss [One_def])
		++ METIS_TAC [leq_trans])
	    ++ `Leq
      (\(s :value state).
         (if
            (Inv :value state -> bool) s /\
            (Var :value state -> int) s < (1 :int) + (& (SUC (N :num)) :int)
          then
            posreal_pow (1 :posreal) (SUC N)
          else
            (0 :
          posreal)))
      (Max
         (\(s :value state).
            (\(s :value state).
               (if (g :value state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :value state).
               (if Inv s /\ Var s < (1 :int) + (& (SUC N) :int) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s)
         (\(s :value state).
            (\(s :value state).
               (if ~g s then (1 :posreal) else (0 :posreal))) s *
            (\(s :value state).
               (if Inv s /\ Var s < (1 :int) + (& (SUC N) :int) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s))`
		by (RW_TAC std_ss [Max_def, Leq_def]
		    ++ Cases_on `g s`
		    ++ RW_TAC posreal_ss [])
	    ++ Suff `Leq
      (Max
         (\(s :value state).
            (\(s :value state).
               (if (g :value state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :value state).
               (if
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s <
                  (1 :int) + (& (SUC (N :num)) :int)
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s)
         (\(s :value state).
            (\(s :value state).
               (if ~g s then (1 :posreal) else (0 :posreal))) s *
            (\(s :value state).
               (if Inv s /\ Var s < (1 :int) + (& (SUC N) :int) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s))
      (wp (While (\(s :value state). g s) (loopbody :value command))
         (One :value state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (\(s :value state).
         (if ~(g :value state -> bool) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp (While (\(s :value state). g s) (loopbody :value command))
         (One :value state expect))`
			by (FULL_SIMP_TAC std_ss [Leq_def]
			    ++ GEN_TAC
			    ++ RW_TAC posreal_ss [zero_le, wp_def, cond_eta]
			    ++ `monotonic
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))`
				by (RW_TAC std_ss [monotonic_def, Leq_def]
	    			    ++ Cases_on `g s'`
	    			    >> METIS_TAC [wp_mono, Leq_def]
	    			    ++ RW_TAC posreal_ss [One_def])
			    ++ `lfp
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))
      (expect_lfp
         (\(e :value state expect) (s :value state).
            (if g s then wp loopbody e s else One s)))`
				by METIS_TAC [expect_lfp_def]
			    ++ FULL_SIMP_TAC std_ss [lfp_def, expect_def]
			    ++ Suff `(1 :posreal) <=
    (\(s :value state).
       (if (g :value state -> bool) s then
          wp (loopbody :value command)
            (expect_lfp
               (\(e :value state expect) (s :value state).
                  (if g s then wp loopbody e s else One s))) s
        else
          One s)) (s :value state)`
			    >> METIS_TAC []
			    ++ RW_TAC posreal_ss [One_def])
	    ++ `Leq
      (Max
         (\(s :value state).
            (\(s :value state).
               (if (g :value state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :value state).
               (if
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s <
                  (1 :int) + (& (SUC (N :num)) :int)
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s)
         (\(s :value state).
            (\(s :value state).
               (if ~g s then (1 :posreal) else (0 :posreal))) s *
            (\(s :value state).
               (if Inv s /\ Var s < (1 :int) + (& (SUC N) :int) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s))
      (Max
         (\(s :value state).
            (\(s :value state).
               (if g s then (1 :posreal) else (0 :posreal))) s *
            (\(s :value state).
               (if Inv s /\ Var s < (1 :int) + (& (SUC N) :int) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s)
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ Cases_on `g s`
		    ++ RW_TAC posreal_ss []
		    ++ Suff `posreal_pow (1 :posreal) (SUC (N :num)) <= (1 :posreal)`
		    >> (`(1 :posreal) <=
    wp
      (While (\(s :value state). (g :value state -> bool) s)
         (loopbody :value command)) (One :value state expect)
      (s :value state)`
			by (FULL_SIMP_TAC posreal_ss [Leq_def]
			    ++ METIS_TAC [])
		        ++ METIS_TAC [le_trans])
		    ++ METIS_TAC [posreal_pow_1bounded_base_1bounded, le_refl])
	    ++ Suff `Leq
      (Max
         (\(s :value state).
            (\(s :value state).
               (if (g :value state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :value state).
               (if
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s <
                  (1 :int) + (& (SUC (N :num)) :int)
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s)
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (\(s :value state).
            (\(s :value state).
               (if (g :value state -> bool) s then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))) s *
            (\(s :value state).
               (if
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s <
                  (1 :int) + (& (SUC (N :num)) :int)
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))) s)
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))
      (Max
         (Max
            (\(s :value state).
               (if g s /\ Inv s /\ Var s < (1 :int) + (& N :int) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal)))
            (\(s :value state).
               (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ `(Var :value state -> int) (s :value state) <
    (1 :int) + (& (SUC (N :num)) :int) =
    Var s <= (1 :int) + (& N :int)`
			by RW_TAC int_ss [INT, INT_ADD_ASSOC, INT_LE_EQ_LT_ADD1]
		    ++ `(Var :value state -> int) (s :value state) <=
    (1 :int) + (& (N :num) :int) =
    Var s < (1 :int) + (& N :int) \/ (Var s = (1 :int) + (& N :int))`
			by RW_TAC int_ss [INT_LE_LT]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ Cases_on `Var s < 1 + &N`
		    ++ ASM_REWRITE_TAC []
		    ++ Cases_on `g s`
		    ++ ASM_REWRITE_TAC []
		    ++ RW_TAC int_ss [max_lzero, mul_lone, mul_lzero, max_refl]
		    ++ RW_TAC posreal_ss [zero_lt_posreal_pow])
	    ++ Suff `Leq
      (Max
         (Max
            (\(s :value state).
               (if
                  (g :value state -> bool) s /\
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s < (1 :int) + (& (N :num) :int)
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal)))
            (\(s :value state).
               (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (Max
            (\(s :value state).
               (if
                  (g :value state -> bool) s /\
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s < (1 :int) + (& (N :num) :int)
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal)))
            (\(s :value state).
               (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))
      (Max
         (Max
            (\(s :value state).
               (1 :posreal) *
               wp (While (\(s :value state). g s) loopbody)
                 (One :value state expect) s)
            (\(s :value state).
               (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ RW_TAC posreal_ss []
		    ++ FULL_SIMP_TAC int_ss [DE_MORGAN_THM, INT_LT_IMP_NE, Leq_def]
		    ++ RW_TAC std_ss [mul_lone, posreal_pow_def]
		    ++ `max
      (wp
         (While (\(s :value state). (g :value state -> bool) s)
            (loopbody :value command)) (One :value state expect)
         (s :value state))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect) s) =
    wp (While (\(s :value state). g s) loopbody) (One :value state expect) s`
				by METIS_TAC [preal_max_def]
		    ++ `max
      (max
         (wp
            (While (\(s :value state). (g :value state -> bool) s)
               (loopbody :value command)) (One :value state expect)
            (s :value state)) (posreal_pow (1 :posreal) (N :num)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect) s) =
    max (posreal_pow (1 :posreal) N)
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect) s)`
				by METIS_TAC [max_swap, preal_max_def]
		    ++ METIS_TAC [preal_max_def, le_trans, le_refl])
	    ++ Suff `Leq
      (Max
         (Max
            (\(s :value state).
               (1 :posreal) *
               wp
                 (While (\(s :value state). (g :value state -> bool) s)
                    (loopbody :value command)) (One :value state expect) s)
            (\(s :value state).
               (if
                  g s /\ (Inv :value state -> bool) s /\
                  ((Var :value state -> int) s =
                   (1 :int) + (& (N :num) :int))
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (Max
            (\(s :value state).
               (1 :posreal) *
               wp
                 (While (\(s :value state). (g :value state -> bool) s)
                    (loopbody :value command)) (One :value state expect) s)
            (\(s :value state).
               (if
                  g s /\ (Inv :value state -> bool) s /\
                  ((Var :value state -> int) s =
                   (1 :int) + (& (N :num) :int))
                then
                  posreal_pow (1 :posreal) (SUC N)
                else
                  (0 :
                posreal))))
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))
      (Max
         (\(s :value state).
            posreal_pow (1 :posreal) N *
            wp loopbody
              (\(s :value state).
                 (if Inv s /\ Var s < (1 :int) + (& N :int) then
                    (1 :
                  posreal)
                  else
                    (0 :
                  posreal))) s)
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))`
		by (RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ `max
      (max
         (wp
            (While (\(s :value state). (g :value state -> bool) s)
               (loopbody :value command)) (One :value state expect)
            (s :value state))
         (if
            g s /\ (Inv :value state -> bool) s /\
            ((Var :value state -> int) s = (1 :int) + (& (N :num) :int))
          then
            posreal_pow (1 :posreal) (SUC N)
          else
            (0 :
          posreal)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect) s) =
    max
      (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
         posreal_pow (1 :posreal) (SUC N)
       else
         (0 :
       posreal))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect) s)`
			by (`max
      (max
         (wp
            (While (\(s :value state). (g :value state -> bool) s)
               (loopbody :value command)) (One :value state expect)
            (s :value state))
         (if
            g s /\ (Inv :value state -> bool) s /\
            ((Var :value state -> int) s = (1 :int) + (& (N :num) :int))
          then
            posreal_pow (1 :posreal) (SUC N)
          else
            (0 :
          posreal)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect) s) =
    max
      (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
         posreal_pow (1 :posreal) (SUC N)
       else
         (0 :
       posreal))
      (max
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect) s)
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect) s))`
				by METIS_TAC [max_swap]
			    ++ METIS_TAC [preal_max_def])
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(if
       (g :value state -> bool) (s :value state) /\
       (Inv :value state -> bool) s /\
       ((Var :value state -> int) s = (1 :int) + (& (N :num) :int))
     then
       posreal_pow (1 :posreal) (SUC N)
     else
       (0 :
     posreal)) =
    posreal_pow (1 :posreal) N *
    (if g s /\ Inv s /\ (Var s = (1 :int) + (& N :int)) then
       (1 :
     posreal)
     else
       (0 :
     posreal))`
			by RW_TAC posreal_ss [posreal_pow_def, mul_comm, mul_rzero]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `posreal_pow (1 :posreal) (N :num) *
    (if
       (g :value state -> bool) (s :value state) /\
       (Inv :value state -> bool) s /\
       ((Var :value state -> int) s = (1 :int) + (& N :int))
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) <=
    posreal_pow (1 :posreal) N *
    wp (loopbody :value command)
      (\(s :value state).
         (if Inv s /\ Var s < (1 :int) + (& N :int) then
            (1 :
          posreal)
          else
            (0 :
          posreal))) s`
			by (`(if
       (g :value state -> bool) (s :value state) /\
       (Inv :value state -> bool) s /\
       ((Var :value state -> int) s = (1 :int) + (& (N :num) :int))
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) <=
    wp (loopbody :value command)
      (\(s :value state).
         (if Inv s /\ Var s < (1 :int) + (& N :int) then
            (1 :
          posreal)
          else
            (0 :
          posreal))) s`
				by (FULL_SIMP_TAC posreal_ss [Leq_def]
				    ++ METIS_TAC [])
			    ++ METIS_TAC [le_refl, le_mul2])
		    ++ FULL_SIMP_TAC posreal_ss [posreal_pow_base1_eq_1, mul_lone]
		    ++ RW_TAC posreal_ss [preal_max_def, le_refl, le_trans]
		    ++ METIS_TAC [le_trans, le_total])
	    ++ Suff `Leq
      (Max
         (\(s :value state).
            posreal_pow (1 :posreal) (N :num) *
            wp (loopbody :value command)
              (\(s :value state).
                 (if
                    (Inv :value state -> bool) s /\
                    (Var :value state -> int) s < (1 :int) + (& N :int)
                  then
                    (1 :
                  posreal)
                  else
                    (0 :
                  posreal))) s)
         (wp
            (While (\(s :value state). (g :value state -> bool) s) loopbody)
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `(\(s :value state).
       posreal_pow (1 :posreal) (N :num) *
       wp (loopbody :value command)
         (\(s :value state).
            (if
               (Inv :value state -> bool) s /\
               (Var :value state -> int) s < (1 :int) + (& N :int)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))) s) =
    wp loopbody
      (\(s :value state).
         (if Inv s /\ Var s < (1 :int) + (& N :int) then
            posreal_pow (1 :posreal) N
          else
            (0 :
          posreal)))`
		by (RW_TAC std_ss [FUN_EQ_THM]
		    ++ `(\(s :value state).
       (if
          (Inv :value state -> bool) s /\
          (Var :value state -> int) s < (1 :int) + (& (N :num) :int)
        then
          posreal_pow (1 :posreal) N
        else
          (0 :
        posreal))) =
    (\(s :value state).
       posreal_pow (1 :posreal) N *
       (if Inv s /\ Var s < (1 :int) + (& N :int) then
          (1 :
        posreal)
        else
          (0 :
        posreal)))`
			by METIS_TAC [FUN_EQ_THM, mul_rone, mul_rzero]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `posreal_pow (1 :posreal) (N :num) *
    wp (loopbody :value command)
      (\(s :value state).
         (if
            (Inv :value state -> bool) s /\
            (Var :value state -> int) s < (1 :int) + (& N :int)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) (s :value state) =
    wp loopbody
      (\(s :value state).
         posreal_pow (1 :posreal) N *
         (\(s :value state).
            (if Inv s /\ Var s < (1 :int) + (& N :int) then
               (1 :
             posreal)
             else
               (0 :
             posreal))) s) s`
			by METIS_TAC [wp_scale]
		    ++ METIS_TAC [])
	    ++ ASM_REWRITE_TAC []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (Max
         (wp (loopbody :value command)
            (\(s :value state).
               (if
                  (Inv :value state -> bool) s /\
                  (Var :value state -> int) s < (1 :int) + (& (N :num) :int)
                then
                  posreal_pow (1 :posreal) N
                else
                  (0 :
                posreal))))
         (wp
            (While (\(s :value state). (g :value state -> bool) s) loopbody)
            (One :value state expect)))
      (Max
         (wp loopbody
            (wp (While (\(s :value state). g s) loopbody)
               (One :value state expect)))
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))`
		by (`Leq
      (wp (loopbody :value command)
         (\(s :value state).
            (if
               (Inv :value state -> bool) s /\
               (Var :value state -> int) s < (1 :int) + (& (N :num) :int)
             then
               posreal_pow (1 :posreal) N
             else
               (0 :
             posreal))))
      (wp loopbody
         (wp
            (While (\(s :value state). (g :value state -> bool) s) loopbody)
            (One :value state expect)))`
			by METIS_TAC [wp_mono]
		    ++ RW_TAC posreal_ss [Leq_def, Max_def]
		    ++ FULL_SIMP_TAC posreal_ss [Leq_def]
		    ++ RW_TAC posreal_ss [preal_max_def, le_refl, le_trans]
		    ++ METIS_TAC [le_trans, le_total])
	    ++ Suff `Leq
      (Max
         (wp (loopbody :value command)
            (wp
               (While (\(s :value state). (g :value state -> bool) s)
                  loopbody) (One :value state expect)))
         (wp (While (\(s :value state). g s) loopbody)
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
	    >> METIS_TAC [leq_trans]
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `Leq
      (wp (loopbody :value command)
         (wp
            (While (\(s :value state). (g :value state -> bool) s) loopbody)
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
		by (`monotonic
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))`
				by (RW_TAC std_ss [monotonic_def, Leq_def]
	    			    ++ Cases_on `g s`
	    			    >> METIS_TAC [wp_mono, Leq_def]
	    			    ++ RW_TAC posreal_ss [One_def])
		    ++ `lfp
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))
      (expect_lfp
         (\(e :value state expect) (s :value state).
            (if g s then wp loopbody e s else One s)))`
			by METIS_TAC [expect_lfp_def]
		    ++ FULL_SIMP_TAC std_ss [Leq_def, wp_def, cond_eta, lfp_def, expect_def]
		    ++ GEN_TAC
		    ++ Suff `wp (loopbody :value command)
      (expect_lfp
         (\(e :value state expect) (s :value state).
            (if (g :value state -> bool) s then
               wp loopbody e s
             else
               One s))) (s :value state) <=
    (\(s :value state).
       (if g s then
          wp loopbody
            (expect_lfp
               (\(e :value state expect) (s :value state).
                  (if g s then wp loopbody e s else One s))) s
        else
          One s)) s`
		    >> METIS_TAC []
		    ++ RW_TAC posreal_ss [le_refl, One_def]
		    ++ `expect_lfp
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            (1 :
          posreal))) =
    wp (While (\(s :value state). g s) loopbody) (One :value state expect)` 
			by RW_TAC posreal_ss [wp_def, cond_eta, One_def]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `wp (loopbody :value command)
      (wp (While (\(s :value state). (g :value state -> bool) s) loopbody)
         (One :value state expect)) (s :value state) =
    wp (Seq loopbody (While (\(s :value state). g s) loopbody))
      (One :value state expect) s`
			by RW_TAC posreal_ss [wp_def]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ METIS_TAC [Leq_def, One_def, Term_Leq_One])
	    ++ FULL_SIMP_TAC posreal_ss [Leq_def, Max_def, preal_max_def, le_refl])
++ `!(N :num).
      Leq
        (\(s :value state).
           (if
              (Inv :value state -> bool) s /\
              (Var :value state -> int) s < (1 :int) + (& N :int)
            then
              (1 :
            posreal)
            else
              (0 :
            posreal)))
        (wp
           (While (\(s :value state). (g :value state -> bool) s)
              (loopbody :value command)) (One :value state expect))`
	by METIS_TAC [posreal_pow_base1_eq_1]
++ `(\(s :value state).
       (if (Inv :value state -> bool) s then
          (1 :
        posreal)
        else
          (0 :
        posreal))) =
    Max
      (\(s :value state).
         (if (g :value state -> bool) s /\ Inv s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (\(s :value state).
         (if ~g s /\ Inv s then (1 :posreal) else (0 :posreal)))`
	by (RW_TAC posreal_ss [FUN_EQ_THM, Max_def]
	    ++ Cases_on `g s`
	    ++ METIS_TAC [max_lzero, max_rzero])
++ ASM_REWRITE_TAC []
++ POP_ASSUM (K ALL_TAC)
++ `Leq
      (Max
         (\(s :value state).
            (if
               (g :value state -> bool) s /\ (Inv :value state -> bool) s
             then
               (1 :
             posreal)
             else
               (0 :
             posreal)))
         (\(s :value state).
            (if ~g s /\ Inv s then (1 :posreal) else (0 :posreal))))
      (Max
         (\(s :value state).
            (if g s /\ Inv s then (1 :posreal) else (0 :posreal)))
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))`
	by (`Leq
      (\(s :value state).
         (if ~(g :value state -> bool) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp (While (\(s :value state). g s) (loopbody :value command))
         (One :value state expect))`
		by (FULL_SIMP_TAC std_ss [Leq_def]
		    ++ GEN_TAC
		    ++ RW_TAC posreal_ss [zero_le, wp_def, cond_eta]
		    ++ `monotonic
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))`
			by (RW_TAC std_ss [monotonic_def, Leq_def]
    			    ++ Cases_on `g s'`
    			    >> METIS_TAC [wp_mono, Leq_def]
    			    ++ RW_TAC posreal_ss [One_def])
		    ++ `lfp
      ((expect :value state expect -> bool),
       (Leq :value state expect -> value state expect -> bool))
      (\(e :value state expect) (s :value state).
         (if (g :value state -> bool) s then
            wp (loopbody :value command) e s
          else
            One s))
      (expect_lfp
         (\(e :value state expect) (s :value state).
            (if g s then wp loopbody e s else One s)))`
			by METIS_TAC [expect_lfp_def]
		    ++ FULL_SIMP_TAC std_ss [lfp_def, expect_def]
		    ++ Suff `(1 :posreal) <=
    (\(s :value state).
       (if (g :value state -> bool) s then
          wp (loopbody :value command)
            (expect_lfp
               (\(e :value state expect) (s :value state).
                  (if g s then wp loopbody e s else One s))) s
        else
          One s)) (s :value state)`
		    >> METIS_TAC []
		    ++ RW_TAC posreal_ss [One_def])
	    ++ FULL_SIMP_TAC posreal_ss [Leq_def, Max_def]
	    ++ GEN_TAC
	    ++ Cases_on `g s`
	    ++ RW_TAC posreal_ss [preal_max_def, max_lzero, max_rzero]
	    ++ METIS_TAC [le_trans, posreal_pow_1bounded_base_1bounded])
++ Suff `Leq
      (Max
         (\(s :value state).
            (if
               (g :value state -> bool) s /\ (Inv :value state -> bool) s
             then
               (1 :
             posreal)
             else
               (0 :
             posreal)))
         (wp (While (\(s :value state). g s) (loopbody :value command))
            (One :value state expect)))
      (wp (While (\(s :value state). g s) loopbody)
         (One :value state expect))`
>> METIS_TAC [leq_trans]
++ POP_ASSUM (K ALL_TAC)
++ Suff `Leq
      (\(s :value state).
         (if (g :value state -> bool) s /\ (Inv :value state -> bool) s then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp (While (\(s :value state). g s) (loopbody :value command))
         (One :value state expect))`
>> (FULL_SIMP_TAC posreal_ss [Leq_def, Max_def]
    ++ METIS_TAC [le_refl, max_le])
++ FULL_SIMP_TAC posreal_ss [Leq_def]
++ GEN_TAC
++ Q.UNABBREV_TAC `Inv`
++ Q.UNABBREV_TAC `g`
++ Q.UNABBREV_TAC `loopbody`
++ Q.UNABBREV_TAC `Var`
++ FULL_SIMP_TAC posreal_ss []
++ Cases_on `0 <= int_of_value (s i)`
>> (Cases_on `int_of_value (s i) < int_of_value (s n)`
    >> (`?(n'' :num). int_of_value ((s :value state) (n :string)) = (& n'' :int)` by METIS_TAC [NUM_POSINT_EXISTS, INT_LT_IMP_LE, INT_LE_TRANS]
	++ `(if
       int_of_value ((s :value state) (i :string)) <
       int_of_value (s (n :string)) /\ (0 :int) <= int_of_value (s i)
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) <=
    (if
       (0 :int) <= int_of_value (s i) /\
       int_of_value (s n) - int_of_value (s i) <
       (1 :int) + int_of_value (s n)
     then
       (1 :
     posreal)
     else
       (0 :
     posreal))`
		by (POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ Q.ABBREV_TAC `n' = int_of_value (s n)`
		    ++ Q.ABBREV_TAC `i' = int_of_value (s i)`
		    ++ SIMP_TAC int_ss [INT_LT_SUB_RADD]
		    ++ `(if (0 :int) <= (i' :int) /\ (n' :int) < (1 :int) + n' + i' then
       (1 :
     posreal)
     else
       (0 :
     posreal)) =
    (if (0 :int) <= i' /\ (0 :int) + n' < (1 :int) + n' + i' then
       (1 :
     posreal)
     else
       (0 :
     posreal))` by RW_TAC int_ss []
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(if
       (0 :int) <= (i' :int) /\ (0 :int) + (n' :int) < (1 :int) + n' + i'
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) =
    (if (0 :int) <= i' /\ (0 :int) < (1 :int) + n' + i' - n' then
       (1 :
     posreal)
     else
       (0 :
     posreal))`
			by METIS_TAC [INT_LT_ADD_SUB]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(1 :int) + (n' :int) + (i' :int) - n' = (1 :int) + i' + n' - n'`
			by METIS_TAC [INT_ADD_COMM, INT_ADD_ASSOC]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(1 :int) + (i' :int) + (n' :int) - n' = i' + (1 :int)`
			by RW_TAC int_ss [INT_SUB_REFL, INT_ADD_COMM]
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(0 :int) <= (i' :int) ==> (0 :int) < i' + (1 :int)` by METIS_TAC [INT_LT_ADD1]
		    ++ RW_TAC posreal_ss []
		    ++ FULL_SIMP_TAC int_ss [])
	++ Suff `(if
       (0 :int) <= int_of_value ((s :value state) (i :string)) /\
       int_of_value (s (n :string)) - int_of_value (s i) <
       (1 :int) + int_of_value (s n)
     then
       (1 :
     posreal)
     else
       (0 :
     posreal)) <=
    wp
      (While (\(s :value state). int_of_value (s i) < int_of_value (s n))
         (Seq (body :value command)
            (Assign i
               (\(s :value state). Int (int_of_value (s i) + (1 :int))))))
      (One :value state expect) s`
	>> METIS_TAC [le_trans]
	++ POP_ASSUM (K ALL_TAC)
	++ METIS_TAC [])
	++ METIS_TAC [zero_le])
++ METIS_TAC [zero_le]);

val For_i_0_to_n_variant_rule = store_thm
  ("For_i_0_to_n_variant_rule",
``!(i :string) (n :string) (body :value command list).
           ~(n = i) /\
           Leq
             (\(s :value state).
                (if
                   (\(s :value state). (0 :int) <= int_of_value (s i)) s
                 then
                   (1 :
                 posreal)
                 else
                   (0 :
                 posreal)))
             (wp (Program body)
                (\(s :value state).
                   (if
                      (\(s :value state). (0 :int) <= int_of_value (s i)) s
                    then
                      (1 :
                    posreal)
                    else
                      (0 :
                    posreal)))) /\
           (!(N :int).
              Leq
                (\(s :value state).
                   (if
                      (\(s :value state).
                         int_of_value (s i) < int_of_value (s n)) s /\
                      (\(s :value state). (0 :int) <= int_of_value (s i))
                        s /\
                      ((\(s :value state).
                          int_of_value (s n) - int_of_value (s i)) s =
                       N)
                    then
                      (1 :
                    posreal)
                    else
                      (0 :
                    posreal)))
                (wp (Program body)
                   (\(s :value state).
                      (if
                         (\(s :value state).
                            int_of_value (s n) - int_of_value (s i)) s <= N
                       then
                         (1 :
                       posreal)
                       else
                         (0 :
                       posreal))))) ==>
           (wp (For_0_to_n i n body) (One :value state expect) =
            (One :value state expect))``,
RW_TAC posreal_ss [For_0_to_n_def, For_def]
++ MATCH_MP_TAC leq_antisym
++ SIMP_TAC std_ss [Term_Leq_One]
++ `wp
      (Seq (Assign (i :string) (\(s :value state). Int (0 :int)))
         (While
            (\(s :value state).
               int_of_value (s i) < int_of_value (s (n :string)))
            (Seq (Program (body :value command list))
               (Assign i
                  (\(s :value state).
                     Int (int_of_value (s i) + (1 :int))))))) =
    (\(s :value state expect).
       wp (Assign i (\(s :value state). Int (0 :int)))
         (wp
            (While
               (\(s :value state). int_of_value (s i) < int_of_value (s n))
               (Seq (Program body)
                  (Assign i
                     (\(s :value state).
                        Int (int_of_value (s i) + (1 :int)))))) s))`
	by METIS_TAC [wp_def]
++ ASM_REWRITE_TAC []
++ POP_ASSUM (K ALL_TAC)
++ SIMP_TAC std_ss []
++ `wp (Assign (i :string) (\(s :value state). Int (0 :int))) =
    (\(r :value state expect) (s :value state).
       r (assign i (\(s :value state). Int (0 :int)) s))`
	by METIS_TAC [wp_def]
++ ASM_REWRITE_TAC []
++ POP_ASSUM (K ALL_TAC)
++ SIMP_TAC std_ss [assign_eta, Leq_def]
++ GEN_TAC
++ `Leq
      (\(s :value state).
         (if (0 :int) <= int_of_value (s (i :string)) then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < int_of_value (s (n :string)))
            (Seq (Program (body :value command list))
               (Assign i
                  (\(s :value state).
                     Int (int_of_value (s i) + (1 :int))))))
         (One :value state expect))`
	by METIS_TAC [While_variant_rule]
++ `!(s :value state).
      (\(s :value state).
         (if (0 :int) <= int_of_value (s (i :string)) then
            (1 :
          posreal)
          else
            (0 :
          posreal))) s <=
      wp
        (While
           (\(s :value state).
              int_of_value (s i) < int_of_value (s (n :string)))
           (Seq (Program (body :value command list))
              (Assign i
                 (\(s :value state). Int (int_of_value (s i) + (1 :int))))))
        (One :value state expect) s`
	by FULL_SIMP_TAC std_ss [Leq_def]
++ `(\(s :value state).
       (if (0 :int) <= int_of_value (s (i :string)) then
          (1 :
        posreal)
        else
          (0 :
        posreal)))
      (\(w :string).
         (if w = i then Int (0 :int) else (s :value state) w)) <=
    wp
      (While
         (\(s :value state).
            int_of_value (s i) < int_of_value (s (n :string)))
         (Seq (Program (body :value command list))
            (Assign i
               (\(s :value state). Int (int_of_value (s i) + (1 :int))))))
      (One :value state expect)
      (\(w :string). (if w = i then Int (0 :int) else s w))`
	by ASM_REWRITE_TAC []
++ Suff `One (s :value state) <=
    (\(s :value state).
       (if (0 :int) <= int_of_value (s (i :string)) then
          (1 :
        posreal)
        else
          (0 :
        posreal))) (\(w :string). (if w = i then Int (0 :int) else s w))`
>> METIS_TAC [le_trans]
++ SIMP_TAC posreal_ss [One_def, int_of_value_def, INT_LE_REFL]);

val bool_Inv_rule = store_thm
  ("bool_Inv_rule",
   ``!(Inv :num -> 'a state -> bool) (g :'a state -> bool)
            (body :'a command).
           (!(v :num).
              Leq (bool_exp (\(s :'a state). g s /\ Inv v s))
                (wp body
                   (bool_exp
                      (\(s :'a state).
                         ?(v' :num). Inv v' s /\ v' < v)))) ==>
           !(v :num).
             Leq (bool_exp (Inv v))
               (wp (While g body)
                  (bool_exp (\(s :'a state). ?(v' :num). Inv v' s /\ ~g s)))``,
   REPEAT STRIP_TAC
   ++ completeInduct_on `v`
   ++ ONCE_REWRITE_TAC [while_unwind_lemma]
   ++ RW_TAC posreal_ss [Leq_def]
   ++ Cases_on `~(g s)`
   >> (FULL_SIMP_TAC bool_ss [] 
       ++ RW_TAC posreal_ss [bool_exp_def]
       ++ METIS_TAC [])
   ++ FULL_SIMP_TAC bool_ss []
   ++ RW_TAC posreal_ss [bool_exp_def, zero_le]
   ++ FULL_SIMP_TAC posreal_ss [Leq_def, bool_exp_def]
   ++ `(1 :posreal) <=
    wp (body :'a command)
      (\(s :'a state).
         (if
            ?(v' :num). (Inv :num -> 'a state -> bool) v' s /\ v' < (v :num)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) (s :'a state)` 
	by METIS_TAC [le_refl, zero_le]
   ++ `Leq
      (\(s :'a state).
         (if
            ?(v' :num). (Inv :num -> 'a state -> bool) v' s /\ v' < (v :num)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))
      (wp (While (g :'a state -> bool) (body :'a command))
         (\(s :'a state).
            (if ?(v' :num). Inv v' s /\ ~g s then
               (1 :
             posreal)
             else
               (0 :
             posreal))))` 
	by (RW_TAC std_ss [Leq_def]
    	    ++ RW_TAC posreal_ss [zero_le, le_refl]
    	    ++ METIS_TAC [zero_le, le_refl])
   ++ `!(prog :'a command) (e0 :'a state expect) (e1 :'a state expect).
      Leq e0 e1 ==> Leq (wp prog e0) (wp prog e1)` by METIS_TAC [wp_mono]
   ++ FULL_SIMP_TAC posreal_ss [Leq_def]
   ++ `!(s :'a state).
      (\(s :'a state).
         (if
            ?(v' :num). (Inv :num -> 'a state -> bool) v' s /\ v' < (v :num)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) s <=
      wp (While (g :'a state -> bool) (body :'a command))
        (\(s :'a state).
           (if ?(v' :num). Inv v' s /\ ~g s then
              (1 :
            posreal)
            else
              (0 :
            posreal))) s` 
	by ASM_SIMP_TAC std_ss []
   ++`!(s :'a state).
      wp (body :'a command)
        (\(s :'a state).
           (if
              ?(v' :num).
                (Inv :num -> 'a state -> bool) v' s /\ v' < (v :num)
            then
              (1 :
            posreal)
            else
              (0 :
            posreal))) s <=
      wp body
        (wp (While (g :'a state -> bool) body)
           (\(s :'a state).
              (if ?(v' :num). Inv v' s /\ ~g s then
                 (1 :
               posreal)
               else
                 (0 :
               posreal)))) s`
	by RW_TAC posreal_ss []
   ++ METIS_TAC [le_trans]);

val assign_while_immediate_term = store_thm
  ("assign_while_immediate_term",
   ``!(i :string) (body :value command) (n :num)
            (postE :value state expect).
           wp (Assign i (\(s :value state). Int (& n :int)))
             (wp
                (While (\(s :value state). int_of_value (s i) < (& n :int))
                   body) postE) =
           wp (Assign i (\(s :value state). Int (& n :int))) postE``,
   REPEAT GEN_TAC
   ++ Q.ABBREV_TAC `g = (\(s :value state).
            int_of_value (s (i :string)) < (& (n :num) :int))`
   ++ `wp (While (g :value state -> bool) (body :value command))
      (postE :value state expect) =
    (\(s :value state).
       (if g s then wp body (wp (While g body) postE) s else postE s))`
	by METIS_TAC [while_unwind_lemma]
   ++ Q.ABBREV_TAC `foo = (\(s :value state).
                (if (g :value state -> bool) s then
                   wp (body :value command)
                     (wp (While g body) (postE :value state expect)) s
                 else
                   postE s))`
   ++ ASM_REWRITE_TAC []
   ++ Q.UNABBREV_TAC `foo`
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.UNABBREV_TAC `g`
   ++ RW_TAC int_ss [int_of_value_def, wp_assign]);

val while_reverse_unwind_part1 = store_thm
  ("while_reverse_unwind_part1",
   ``!(body :value command) (i :string) (postE :'a).
           (!(postE :value state expect) (m :num).
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (& (m + (1 :num)) :int)
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w))) =
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (int_of_value (s i) + (1 :int))
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w)))) ==>
           !(m :num) (n :num) (postE :value state expect).
             m < n ==>
             (wp (Assign i (\(s :value state). Int (& m :int)))
                (wp
                   (While
                      (\(s :value state). int_of_value (s i) < (& n :int))
                      (Seq body
                         (Assign i
                            (\(s :value state).
                               Int (int_of_value (s i) + (1 :int))))))
                   postE) =
              wp (Assign i (\(s :value state). Int (& m :int)))
                (wp body
                   (wp
                      (Assign i
                         (\(s :value state). Int (& (m + (1 :num)) :int)))
                      (wp
                         (While
                            (\(s :value state).
                               int_of_value (s i) < (& n :int))
                            (Seq body
                               (Assign i
                                  (\(s :value state).
                                     Int (int_of_value (s i) + (1 :int))))))
                         postE))))``,
   REPEAT STRIP_TAC
   ++ `wp (Assign (i :string) (\(s :value state). Int (& (m :num) :int)))
      (wp
         (While (\(s :value state). int_of_value (s i) < (& (n :num) :int))
            (Seq (body :value command)
               (Assign i
                  (\(s :value state).
                     Int (int_of_value (s i) + (1 :int))))))
         (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& m :int)))
      (\(s :value state).
         (if (\(s :value state). int_of_value (s i) < (& n :int)) s then
            wp
              (Seq body
                 (Assign i
                    (\(s :value state).
                       Int (int_of_value (s i) + (1 :int)))))
              (wp
                 (While (\(s :value state). int_of_value (s i) < (& n :int))
                    (Seq body
                       (Assign i
                          (\(s :value state).
                             Int (int_of_value (s i) + (1 :int)))))) postE)
              s
          else
            postE s))`
	by (`wp
      (While
         (\(s :value state).
            int_of_value (s (i :string)) < (& (n :num) :int))
         (Seq (body :value command)
            (Assign i
               (\(s :value state). Int (int_of_value (s i) + (1 :int))))))
      (postE :value state expect) =
    (\(s :value state).
       (if (\(s :value state). int_of_value (s i) < (& n :int)) s then
          wp
            (Seq body
               (Assign i
                  (\(s :value state). Int (int_of_value (s i) + (1 :int)))))
            (wp
               (While (\(s :value state). int_of_value (s i) < (& n :int))
                  (Seq body
                     (Assign i
                        (\(s :value state).
                           Int (int_of_value (s i) + (1 :int)))))) postE) s
        else
          postE s))`
		by (Q.ABBREV_TAC `g = (\(s :value state).
                int_of_value (s (i :string)) < (& (n :num) :int))`
	  	    ++ METIS_TAC [while_unwind_lemma])
   	    ++ Q.ABBREV_TAC `foo = 
			     (\(s :value state).
                (if
                   (\(s :value state).
                      int_of_value (s (i :string)) < (& (n :num) :int)) s
                 then
                   wp
                     (Seq (body :value command)
                        (Assign i
                           (\(s :value state).
                              Int (int_of_value (s i) + (1 :int)))))
                     (wp
                        (While
                           (\(s :value state).
                              int_of_value (s i) < (& n :int))
                           (Seq body
                              (Assign i
                                 (\(s :value state).
                                    Int (int_of_value (s i) + (1 :int))))))
                        (postE :value state expect)) s
                 else
                   postE s))`
	    ++ ASM_REWRITE_TAC [])
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC std_ss [int_of_value_def, wp_seq, wp_assign]
   ++ `(& (m :num) :int) < (& (n :num) :int)` by RW_TAC int_ss []
   ++ ASM_REWRITE_TAC []);

val while_reverse_unwind_lemma = store_thm
  ("while_reverse_unwind_lemma",
   ``!(n :num) (m :num) (body :value command) (i :string)
            (postE :value state expect).
           (!(postE :value state expect) (m :num).
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (& (m + (1 :num)) :int)
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w))) =
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (int_of_value (s i) + (1 :int))
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w)))) /\
           m <= n ==>
           (wp
              (Seq (Assign i (\(s :value state). Int (& m :int)))
                 (While
                    (\(s :value state).
                       int_of_value (s i) < (& (SUC n) :int))
                    (Seq body
                       (Assign i
                          (\(s :value state).
                             Int (int_of_value (s i) + (1 :int)))))))
              postE =
            wp
              (Seq (Assign i (\(s :value state). Int (& m :int)))
                 (Seq
                    (While
                       (\(s :value state). int_of_value (s i) < (& n :int))
                       (Seq body
                          (Assign i
                             (\(s :value state).
                                Int (int_of_value (s i) + (1 :int))))))
                    (Seq body
                       (Assign i
                          (\(s :value state).
                             Int (int_of_value (s i) + (1 :int))))))) postE)``,
   REPEAT STRIP_TAC
   ++ `!(m :num) (n :num) (postE :value state expect).
      m < n ==>
      (wp (Assign (i :string) (\(s :value state). Int (& m :int)))
         (wp
            (While (\(s :value state). int_of_value (s i) < (& n :int))
               (Seq (body :value command)
                  (Assign i
                     (\(s :value state).
                        Int (int_of_value (s i) + (1 :int)))))) postE) =
       wp (Assign i (\(s :value state). Int (& m :int)))
         (wp body
            (wp (Assign i (\(s :value state). Int (& (m + (1 :num)) :int)))
               (wp
                  (While
                     (\(s :value state). int_of_value (s i) < (& n :int))
                     (Seq body
                        (Assign i
                           (\(s :value state).
                              Int (int_of_value (s i) + (1 :int))))))
                  postE))))`
	by METIS_TAC [while_reverse_unwind_part1]
   ++ Q.ABBREV_TAC `loopbody = Seq (body :value command)
               (Assign (i :string)
                  (\(s :value state). Int (int_of_value (s i) + (1 :int))))`
   ++ Induct_on `n - m`
   >> (RW_TAC arith_ss [INT]
       ++ SIMP_TAC std_ss [wp_seq]
       ++ `wp (Assign (i :string) (\(s :value state). Int (& (m :num) :int)))
      (wp
         (While (\(s :value state). int_of_value (s i) < (& (n :num) :int))
            (loopbody :value command))
         (wp loopbody (postE :value state expect))) =
    wp (Assign i (\(s :value state). Int (& m :int))) (wp loopbody postE)`
	by (`(m :num) = (n :num)` by RW_TAC arith_ss [LESS_EQ_ANTISYM]
	    ++ METIS_TAC [assign_while_immediate_term])
       ++ ASM_REWRITE_TAC []
       ++ POP_ASSUM (K ALL_TAC)
       ++ `wp (Assign (i :string) (\(s :value state). Int (& (m :num) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& (n :num) :int) + (1 :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& m :int)))
      (wp (body :value command)
         (wp (Assign i (\(s :value state). Int (& (m + (1 :num)) :int)))
            postE))`
	by (`wp (Assign (i :string) (\(s :value state). Int (& (m :num) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& (n :num) :int) + (1 :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& n :int)))
      (wp (body :value command)
         (wp (Assign i (\(s :value state). Int (& (n + (1 :num)) :int)))
            (wp
               (While
                  (\(s :value state).
                     int_of_value (s i) < (& (n + (1 :num)) :int)) loopbody)
               postE)))`
		by (`(m :num) = (n :num)` by RW_TAC arith_ss [LESS_EQ_ANTISYM]
		    ++ `(& ((n :num) + (1 :num)) :int) = (& n :int) + (1 :int)` by RW_TAC int_ss [INT_ADD]
		    ++ `(n :num) < n + (1 :num)` by RW_TAC arith_ss []
		    ++ METIS_TAC [])
	    ++ `wp
      (Assign (i :string)
         (\(s :value state). Int (& ((n :num) + (1 :num)) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& (n + (1 :num)) :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& (n + (1 :num)) :int))) postE`
		by METIS_TAC [assign_while_immediate_term]
	    ++ `(m:num) = (n:num)` by RW_TAC arith_ss [LESS_EQ_ANTISYM]
	    ++ ASM_REWRITE_TAC [])
       ++ ASM_REWRITE_TAC []
       ++ POP_ASSUM (K ALL_TAC)
       ++ Q.UNABBREV_TAC `loopbody`
       ++ RW_TAC std_ss [int_of_value_def, wp_seq, wp_assign])
   ++ REPEAT STRIP_TAC
   ++ FULL_SIMP_TAC std_ss [INT]
   ++ `(v :num) = (n :num) - ((m :num) + (1 :num))`
	by RW_TAC arith_ss []
   ++ `(m :num) + (1 :num) <= (n :num) ==>
    (wp
       (Seq
          (Assign (i :string)
             (\(s :value state). Int (& (m + (1 :num)) :int)))
          (While
             (\(s :value state). int_of_value (s i) < (& n :int) + (1 :int))
             (loopbody :value command))) (postE :value state expect) =
     wp
       (Seq (Assign i (\(s :value state). Int (& (m + (1 :num)) :int)))
          (Seq
             (While (\(s :value state). int_of_value (s i) < (& n :int))
                loopbody) loopbody)) postE)`
	by METIS_TAC []
   ++ Cases_on `m < n`
   >> (`(m :num) + (1 :num) <= (n :num)` by RW_TAC arith_ss []
       ++ FULL_SIMP_TAC std_ss [wp_seq]
       ++ `wp (Assign (i :string) (\(s :value state). Int (& (m :num) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& (n :num) :int) + (1 :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& m :int)))
      (wp (body :value command)
         (wp (Assign i (\(s :value state). Int (& (m + (1 :num)) :int)))
            (wp
               (While
                  (\(s :value state).
                     int_of_value (s i) < (& n :int) + (1 :int)) loopbody)
               postE)))`
	by (`(m :num) < (n :num) + (1 :num)` by RW_TAC arith_ss []
            ++ `wp (Assign (i :string) (\(s :value state). Int (& (m :num) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& ((n :num) + (1 :num)) :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& m :int)))
      (wp (body :value command)
         (wp (Assign i (\(s :value state). Int (& (m + (1 :num)) :int)))
            (wp
               (While
                  (\(s :value state).
                     int_of_value (s i) < (& (n + (1 :num)) :int)) loopbody)
               postE)))` by METIS_TAC []
	    ++ `(& ((n :num) + (1 :num)) :int) = (& n :int) + (1 :int)` by RW_TAC int_ss [INT_ADD]
	    ++ FULL_SIMP_TAC std_ss [])
       ++ ASM_REWRITE_TAC [])
   ++ `(m:num) = (n:num)` by RW_TAC arith_ss []
   ++ ASM_REWRITE_TAC [assign_while_immediate_term, wp_seq]
   ++ POP_ASSUM (K ALL_TAC)
   ++ `wp (Assign (i :string) (\(s :value state). Int (& (n :num) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& (n + (1 :num)) :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& n :int)))
      (wp (body :value command)
         (wp (Assign i (\(s :value state). Int (& (n + (1 :num)) :int)))
            (wp
               (While
                  (\(s :value state).
                     int_of_value (s i) < (& (n + (1 :num)) :int)) loopbody)
               postE)))`
	by (`(n :num) < n + (1 :num)` by RW_TAC arith_ss []
	    ++ METIS_TAC [])
   ++ `wp
      (Assign (i :string)
         (\(s :value state). Int (& ((n :num) + (1 :num)) :int)))
      (wp
         (While
            (\(s :value state).
               int_of_value (s i) < (& (n + (1 :num)) :int))
            (loopbody :value command)) (postE :value state expect)) =
    wp (Assign i (\(s :value state). Int (& (n + (1 :num)) :int))) postE`
	by METIS_TAC [assign_while_immediate_term]
   ++ FULL_SIMP_TAC std_ss []
   ++ POP_ASSUM (K ALL_TAC)
   ++ `While
      (\(s :value state).
         int_of_value (s (i :string)) < (& ((n :num) + (1 :num)) :int))
      (loopbody :value command) =
    While (\(s :value state). int_of_value (s i) < (& n :int) + (1 :int))
      loopbody`
	by (`(& ((n :num) + (1 :num)) :int) = (& n :int) + (1 :int)` by RW_TAC int_ss [INT_ADD]
	    ++ METIS_TAC [])
   ++ FULL_SIMP_TAC std_ss []
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.UNABBREV_TAC `loopbody`
   ++ RW_TAC std_ss [int_of_value_def, wp_seq, wp_assign]);

val For_reverse_unwind_lemma = store_thm
  ("For_reverse_unwind_lemma",
   ``!(n :num) (m :num) (body :value command) (i :string)
            (postE :value state expect).
           (!(postE :value state expect) (m :num).
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (& (m + (1 :num)) :int)
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w))) =
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (int_of_value (s i) + (1 :int))
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w)))) /\
           m <= n ==>
           (wp
              (For i (\(s :value state). Int (& m :int))
                 (\(s :value state). int_of_value (s i) < (& (SUC n) :int))
                 (\(s :value state). Int (int_of_value (s i) + (1 :int)))
                 [body]) postE =
            wp
              (Seq
                 (For i (\(s :value state). Int (& m :int))
                    (\(s :value state). int_of_value (s i) < (& n :int))
                    (\(s :value state). Int (int_of_value (s i) + (1 :int)))
                    [body])
                 (Seq body
                    (Assign i
                       (\(s :value state).
                          Int (int_of_value (s i) + (1 :int)))))) postE)``,
   RW_TAC std_ss [For_def, Program_def]
   ++ METIS_TAC [while_reverse_unwind_lemma, wp_seq]);

val For_0_to_n_reverse_unwind_lemma = store_thm
  ("For_0_to_n_reverse_unwind_lemma",
   ``!(n :num) (body :value command) (i :string)
            (postE :value state expect).
           (!(postE :value state expect) (m :num).
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (& (m + (1 :num)) :int)
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w))) =
              (\(s :value state).
                 wp body
                   (\(s :value state).
                      postE
                        (\(w :string).
                           (if w = i then
                              Int (int_of_value (s i) + (1 :int))
                            else
                              s w)))
                   (\(w :string).
                      (if w = i then Int (& m :int) else s w)))) ==>
           (wp
              (For i (\(s :value state). Int (0 :int))
                 (\(s :value state). int_of_value (s i) < (& (SUC n) :int))
                 (\(s :value state). Int (int_of_value (s i) + (1 :int)))
                 [body]) postE =
            wp
              (Seq
                 (For i (\(s :value state). Int (0 :int))
                    (\(s :value state). int_of_value (s i) < (& n :int))
                    (\(s :value state). Int (int_of_value (s i) + (1 :int)))
                    [body])
                 (Seq body
                    (Assign i
                       (\(s :value state).
                          Int (int_of_value (s i) + (1 :int)))))) postE)``,
   REPEAT STRIP_TAC
   ++ `(0 :num) <= (n :num)` by RW_TAC arith_ss []
   ++ `0 = &0` by RW_TAC int_ss []
   ++ METIS_TAC [For_reverse_unwind_lemma]);

val _ = export_theory();