(* ========================================================================= *)
(* Create "wpTheory" containing syntax and semantics of a small imperative   *)
(* probabilistic language.                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
app load
  ["bossLib","realLib","rich_listTheory","stringTheory",
   "metisLib","posrealLib","expectationTheory","intLib"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory posrealTheory posrealLib expectationTheory;

(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "wp"                                            *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "wp";

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

(* ------------------------------------------------------------------------- *)
(* The HOL type we use to model states                                       *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("state", Type `:string -> 'a`);

val assign_def = Define
  `assign v (e : 'a state -> 'a) (s:'a state) w = if v = w then e s else s w`;

val assign_eta = store_thm
  ("assign_eta",
   ``!v e s. assign v e s = \w. if w = v then e s else s w``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss [assign_def]);

(* ------------------------------------------------------------------------- *)
(* Probabilisitic programs: syntax                                           *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `command =
       Abort
     | Consume of ('a state -> posreal)
     | Assign of string => ('a state -> 'a)
     | Seq of command => command
     | Nondet of command => command
     | Prob of ('a state -> posreal) => command => command
     | While of ('a state -> bool) => command`;

val Assert_def = Define
  `Assert (x : 'a state -> posreal) (c : 'a command) = c`;

val Skip_def = Define `Skip = Consume (\s. 0)`;

val Program_def = Define
  `(Program [] = Skip) /\
   (Program [c] = c) /\
   (Program (c :: c' :: cs) = Seq c (Program (c' :: cs)))`;

val If_def = Define `If c a b = Prob (\s. if c s then 1 else 0) a b`;

(* wp (Nondets []) should evaluate to the identity for Nondet, which is *)
(* Magic. But we don't allow magic (i.e., miraculous) programs, so we *)
(* underspecify Nondets to avoid this nasty case. *)

val Nondets_def = Define
  `(Nondets [x] = x) /\
   (Nondets (x :: y :: z) = Nondet x (Nondets (y :: z)))`;

val NondetAssign_def = Define
  `NondetAssign v xs = Nondets (MAP (\x. Assign v (\s. x)) xs)`;

val guards_def = Define
  `(guards cs [] = if cs = [] then Abort else Nondets cs) /\
   (guards cs ((p, c) :: rest) =
    If p (guards (c :: cs) rest) (guards cs rest))`;

val Guards_def = Define `Guards l = guards [] l`;

val (Probs_def, _) = Defn.tprove
  (Defn.Hol_defn "Probs_def"
   `(Probs [] = Abort) /\
    (Probs ((p, x) :: rest) =
     Prob (\v. p) x (Probs (MAP (\ (q, y). (q / (1 - p), y)) rest)))`,
   TotalDefn.WF_REL_TAC `measure LENGTH`
   ++ RW_TAC list_ss []);

val _ = save_thm ("Probs_def", Probs_def);

val ProbAssign_def = Define
  `ProbAssign v xs =
   Probs (MAP (\x. (1 / & (LENGTH xs), Assign v (\s. x))) xs)`;

val For_def = Define
   `For i init cond incr c =
  	Seq (Assign i init)
	    (While cond (Seq (Program c) (Assign i incr)))`;

val WhileProgram_def = Define `WhileProgram c l = While c (Program l)`;

(* ------------------------------------------------------------------------- *)
(* Probabilisitic programs: weakest precondition semantics.                  *)
(* ------------------------------------------------------------------------- *)

val wp_def = Define
  `(wp Abort = \r. Zero) /\
   (wp (Consume k) = \r. r) /\
   (wp (Assign v e) = \r s. r (assign v e s)) /\
   (wp (Seq a b) = \r. wp a (wp b r)) /\
   (wp (Nondet a b) = \r. Min (wp a r) (wp b r)) /\
   (wp (Prob p a b) = \r. Lin p (wp a r) (wp b r)) /\
   (wp (While c b) = \r. expect_lfp (\e. Cond c (wp b e) r))`;

(* ------------------------------------------------------------------------- *)
(* Showing the need for SUB-linearity                                        *)
(* (assuming there are at least two distinct values)                         *)
(* ------------------------------------------------------------------------- *)

val sublinear_necessary = store_thm
  ("sublinear_necessary",
   ``(?x y : 'a. ~(x = y)) ==>
     ?prog r1 r2 s : 'a state.
       wp prog r1 s + wp prog r2 s < wp prog (\s'. r1 s' + r2 s') s``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `Nondet (Assign "n" (\v. x)) Skip`
   ++ Q.EXISTS_TAC `\v. if v "n" = x then 1 else 0`
   ++ Q.EXISTS_TAC `\v. if v "n" = y then 1 else 0`
   ++ Q.EXISTS_TAC `(\v. y)`
   ++ REWRITE_TAC [wp_def, assign_eta, Skip_def]
   ++ SIMP_TAC int_ss [Min_def]
   ++ ASM_SIMP_TAC posreal_ss [preal_min_def]);

(* ------------------------------------------------------------------------- *)
(* All wp transformers are healthy                                           *)
(* ------------------------------------------------------------------------- *)

val healthy_wp_abort = lemma
  (``healthy (wp Abort)``,
   RW_TAC posreal_ss
   [wp_def, healthy_def, feasible_def, sublinear_def, Zero_def]
   ++ RW_TAC posreal_ss [up_continuous_def, lub_def, expect_def]
   ++ RW_TAC posreal_ss [Leq_def]);

val () = print "wp Abort is healthy\n";

val healthy_wp_consume = lemma
  (``!k. healthy (wp (Consume k))``,
   RW_TAC posreal_ss [wp_def, healthy_def, feasible_def, sublinear_def]
   ++ RW_TAC posreal_ss [up_continuous_def, lub_def]);

val () = print "wp Skip is healthy\n";

val healthy_wp_assign = lemma
  (``!v e. healthy (wp (Assign v e))``,
   RW_TAC posreal_ss
   [wp_def, healthy_def, sublinear_def, feasible_def, Zero_def, sub_mono,
    assign_eta]
   ++ RW_TAC real_ss [up_continuous_def, lub_def, Leq_def, expect_def]
   >> (BETA_TAC ++ PROVE_TAC [])
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`r'`,`r`)
   ++ REPEAT STRIP_TAC
   ++ Know
      `z s =
       (\f. if f = (\w. if w = v then e s else s w) then z s else r f)
       (\w. if w = v then e s else s w)`
   >> RW_TAC posreal_ss []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   ++ Q.PAT_ASSUM `!x. (!y. P x y) ==> Q x`
      (MATCH_MP_TAC o CONV_RULE (QUANT_CONV RIGHT_IMP_FORALL_CONV))
   ++ RW_TAC posreal_ss []
   ++ RW_TAC posreal_ss []
   ++ Know `y (\w. if w = v then e s else s w) =
            (\s. y (\w. if w = v then e s else s w)) s`
   >> RW_TAC posreal_ss []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ Q.PAT_ASSUM `!y. P y` MATCH_MP_TAC
   ++ METIS_TAC []);

val () = print "wp Assign is healthy\n";

val healthy_wp_seq = lemma
  (``!prog prog'.
        healthy (wp prog) /\ healthy (wp prog') ==>
        healthy (wp (Seq prog prog'))``,
   RW_TAC posreal_ss [wp_def]
   ++ RW_TAC posreal_ss [healthy_def]
   << [RW_TAC posreal_ss [feasible_def]
       ++ METIS_TAC [healthy_def, feasible_def],
       Know `sublinear (wp prog)` >> PROVE_TAC [healthy_sublinear]
       ++ RW_TAC posreal_ss [sublinear_def]
       ++ Q.PAT_ASSUM `!x. P x`
          (MP_TAC o
           Q.SPECL [`wp prog' r`, `wp prog' r'`, `c1`, `c2`, `c`, `s`])
       ++ ASM_SIMP_TAC real_ss []
       ++ Know `!x y z : posreal. y <= z ==> (x <= y ==> x <= z)`
       >> METIS_TAC [le_trans]
       ++ DISCH_THEN MATCH_MP_TAC
       ++ Q.SPEC_TAC (`s`, `s`)
       ++ SIMP_TAC (simpLib.++ (std_ss, boolSimps.ETA_ss)) [GSYM Leq_def]
       ++ MATCH_MP_TAC healthy_mono
       ++ RW_TAC std_ss [Leq_def]
       ++ Know `sublinear (wp prog')` >> PROVE_TAC [healthy_sublinear]
       ++ SIMP_TAC posreal_ss [sublinear_def]
       ++ DISCH_THEN MATCH_MP_TAC
       ++ RW_TAC std_ss [],
       RW_TAC std_ss [up_continuous_def]
       ++ Know `up_continuous (expect,Leq) (wp prog')`
       >> PROVE_TAC [healthy_up_continuous]
       ++ RW_TAC std_ss [up_continuous_def]
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ Q.SPEC_TAC (`r'`,`r`)
       ++ REPEAT STRIP_TAC
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`c`, `r`])
       ++ RW_TAC posreal_ss []
       ++ Know `up_continuous (expect,Leq) (wp prog)`
       >> PROVE_TAC [healthy_up_continuous]
       ++ RW_TAC std_ss [up_continuous_def]
       ++ POP_ASSUM
          (MP_TAC o Q.SPECL
           [`\y. ?z. (expect z /\ c z) /\ (y = wp prog' z)`, `wp prog' r`])
       ++ ASM_SIMP_TAC posreal_ss []
       ++ MATCH_MP_TAC (PROVE [] ``c /\ (a = b) ==> ((c ==> a) ==> b)``)
       ++ CONJ_TAC
       >> (Q.PAT_ASSUM `chain X Y` MP_TAC
           ++ REPEAT (Q.PAT_ASSUM `lub X Y Z` (K ALL_TAC))
           ++ RW_TAC std_ss [chain_def]
           ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPECL [`z`, `z'`])
           ++ ASM_SIMP_TAC std_ss []
           ++ PROVE_TAC [healthy_mono])
       ++ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
       ++ CONV_TAC FUN_EQ_CONV
       ++ RW_TAC posreal_ss [expect_def]
       ++ METIS_TAC []]);

val () = print "wp Seq is healthy\n";

val healthy_wp_nondet = lemma
  (``!prog prog'.
        healthy (wp prog) /\ healthy (wp prog') ==>
        healthy (wp (Nondet prog prog'))``,
   RW_TAC real_ss [wp_def]
   ++ RW_TAC real_ss [healthy_def]
   << [RW_TAC posreal_ss [feasible_def]
       ++ METIS_TAC [refl_min, healthy_def, feasible_def],
       RW_TAC real_ss [wp_def, sublinear_def, Min_def]
       ++ Know `sublinear (wp prog)` >> PROVE_TAC [healthy_sublinear]
       ++ SIMP_TAC real_ss [sublinear_def]
       ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `r'`, `c1`, `c2`, `c`, `s`])
       ++ Know `sublinear (wp prog')` >> PROVE_TAC [healthy_sublinear]
       ++ SIMP_TAC real_ss [sublinear_def]
       ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `r'`, `c1`, `c2`, `c`, `s`])
       ++ ASM_SIMP_TAC posreal_ss []
       ++ Q.SPEC_TAC (`wp prog' r s`, `x1'`)
       ++ Q.SPEC_TAC (`wp prog' r' s`, `x2'`)
       ++ Q.SPEC_TAC (`wp prog r s`, `x1`)
       ++ Q.SPEC_TAC (`wp prog r' s`, `x2`)
       ++ Q.SPEC_TAC(`wp prog' (\s'. c1 * r s' + c2 * r' s' - c) s`, `y'`)
       ++ Q.SPEC_TAC (`wp prog (\s'. c1 * r s' + c2 * r' s' - c) s`, `y`)
       ++ RW_TAC posreal_ss []
       ++ REWRITE_TAC [le_min]
       ++ CONJ_TAC
       << [POP_ASSUM MP_TAC ++ POP_ASSUM (K ALL_TAC)
           ++ Know `!x y z : posreal. z <= x ==> (x <= y ==> z <= y)`
           >> METIS_TAC [le_trans]
           ++ DISCH_THEN MATCH_MP_TAC
           ++ MATCH_MP_TAC sub_mono
           ++ RW_TAC posreal_ss []
           ++ MATCH_MP_TAC le_add2
           ++ RW_TAC posreal_ss [le_lmul_imp],
           POP_ASSUM (K ALL_TAC) ++ POP_ASSUM MP_TAC
           ++ Know `!x y z : posreal. z <= x ==> (x <= y ==> z <= y)`
           >> METIS_TAC [le_trans]
           ++ DISCH_THEN MATCH_MP_TAC
           ++ MATCH_MP_TAC sub_mono
           ++ RW_TAC posreal_ss []
           ++ MATCH_MP_TAC le_add2
           ++ RW_TAC posreal_ss [le_lmul_imp]],
       RW_TAC std_ss [up_continuous_def]
       ++ Know `up_continuous (expect,Leq) (wp prog)`
       >> PROVE_TAC [healthy_up_continuous]
       ++ RW_TAC std_ss [up_continuous_def]
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ Q.SPEC_TAC (`r'`,`r`)
       ++ REPEAT STRIP_TAC
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`c`, `r`])
       ++ RW_TAC posreal_ss []
       ++ Know `up_continuous (expect,Leq) (wp prog')`
       >> PROVE_TAC [healthy_up_continuous]
       ++ RW_TAC std_ss [up_continuous_def]
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`c`, `r`])
       ++ RW_TAC posreal_ss []
       ++ RW_TAC std_ss [lub_def, expect_def]
       >> (RW_TAC std_ss [Leq_def, Min_def]
           ++ MATCH_MP_TAC min_le2_imp
           ++ FULL_SIMP_TAC std_ss [lub_def]
           ++ RW_TAC std_ss []
           << [Suff `Leq (wp prog r') (wp prog r)` >> RW_TAC std_ss [Leq_def]
               ++ FIRST_ASSUM MATCH_MP_TAC
               ++ PROVE_TAC [expect_def],
               Suff `Leq (wp prog' r') (wp prog' r)` >> RW_TAC std_ss [Leq_def]
               ++ FIRST_ASSUM MATCH_MP_TAC
               ++ PROVE_TAC [expect_def]])
       ++ RW_TAC real_ss [Leq_def, Min_def, min_le]
       ++ CCONTR_TAC
       ++ FULL_SIMP_TAC posreal_ss [GSYM preal_lt_def]
       ++ MP_TAC (Q.SPECL [`\y. ?z. (expect z /\ c z) /\ (y = wp prog z)`,
                           `wp prog r`, `z`, `s`]
                  (INST_TYPE [alpha |-> ``:'a state``] expect_lt_lub))
       ++ ASM_REWRITE_TAC [expect_def]
       ++ BETA_TAC
       ++ STRIP_TAC
       ++ MP_TAC (Q.SPECL [`\y. ?z. (expect z /\ c z) /\ (y = wp prog' z)`,
                           `wp prog' r`, `z`, `s`]
                  (INST_TYPE [alpha |-> ``:'a state``] expect_lt_lub))
       ++ ASM_REWRITE_TAC [expect_def]
       ++ BETA_TAC
       ++ STRIP_TAC
       ++ REPEAT (Q.PAT_ASSUM `z s < wp X Y Z` (K ALL_TAC))
       ++ RW_TAC std_ss []
       ++ Know `Leq z' z'' \/ Leq z'' z'` >> PROVE_TAC [chain_def, expect_def]
       ++ STRIP_TAC
       << [Know `z s < wp prog z'' s`
           >> (MATCH_MP_TAC lte_trans
               ++ Q.EXISTS_TAC `wp prog z' s`
               ++ ASM_REWRITE_TAC []
               ++ Suff `Leq (wp prog z') (wp prog z'')`
               >> RW_TAC std_ss [Leq_def]
               ++ PROVE_TAC [healthy_mono])
           ++ POP_ASSUM_LIST
              (EVERY o map ASSUME_TAC o rev o
               filter (not o free_in ``z':'a state->real`` o concl))
           ++ STRIP_TAC
           ++ Q.PAT_ASSUM `!y. P y`
              (MP_TAC o Q.SPEC `Min (wp prog z'') (wp prog' z'')`)
           ++ MATCH_MP_TAC (PROVE[]``x /\ (y ==> z) ==> ((x ==> y) ==> z)``)
           ++ CONJ_TAC >> PROVE_TAC []
           ++ RW_TAC std_ss [Leq_def, Min_def]
           ++ Q.EXISTS_TAC `s`
           ++ RW_TAC posreal_ss [min_le]
           ++ RW_TAC posreal_ss [GSYM preal_lt_def],
           Know `z s < wp prog' z' s`
           >> (MATCH_MP_TAC lte_trans
               ++ Q.EXISTS_TAC `wp prog' z'' s`
               ++ ASM_REWRITE_TAC []
               ++ Suff `Leq (wp prog' z'') (wp prog' z')`
               >> RW_TAC std_ss [Leq_def]
               ++ PROVE_TAC [healthy_mono])
           ++ POP_ASSUM_LIST
              (EVERY o map ASSUME_TAC o rev o
               filter (not o free_in ``z'':'a state->real`` o concl))
           ++ STRIP_TAC
           ++ Q.PAT_ASSUM `!y. P y`
              (MP_TAC o Q.SPEC `Min (wp prog z') (wp prog' z')`)
           ++ MATCH_MP_TAC (PROVE[]``x /\ (y ==> z) ==> ((x ==> y) ==> z)``)
           ++ CONJ_TAC >> PROVE_TAC []
           ++ RW_TAC std_ss [Leq_def, Min_def]
           ++ Q.EXISTS_TAC `s`
           ++ RW_TAC posreal_ss [min_le]
           ++ RW_TAC posreal_ss [GSYM preal_lt_def]]]);

val () = print "wp Nondet is healthy\n";

val healthy_wp_prob = lemma
  (``!f prog prog'.
        healthy (wp prog) /\ healthy (wp prog') ==>
        healthy (wp (Prob f prog prog'))``,
   RW_TAC real_ss [wp_def, lin_eta]
   ++ RW_TAC real_ss [healthy_def]
   << [RW_TAC posreal_ss [feasible_def]
       ++ Know `wp prog Zero = Zero` >> METIS_TAC [healthy_def, feasible_def]
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ Know `wp prog' Zero = Zero` >> METIS_TAC [healthy_def, feasible_def]
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ CONV_TAC FUN_EQ_CONV
       ++ RW_TAC posreal_ss [Zero_def, LET_THM],
       RW_TAC std_ss [sublinear_def]
       ++ Know `sublinear (wp prog)` >> PROVE_TAC [healthy_sublinear]
       ++ SIMP_TAC std_ss [sublinear_def]
       ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `r'`, `c1`, `c2`, `c`, `s`])
       ++ Know `sublinear (wp prog')` >> PROVE_TAC [healthy_sublinear]
       ++ SIMP_TAC std_ss [sublinear_def]
       ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `r'`, `c1`, `c2`, `c`, `s`])
       ++ ASM_SIMP_TAC std_ss []
       ++ Q.SPEC_TAC (`wp prog' r s`, `x1'`)
       ++ Q.SPEC_TAC (`wp prog' r' s`, `x2'`)
       ++ Q.SPEC_TAC (`wp prog r s`, `x1`)
       ++ Q.SPEC_TAC (`wp prog r' s`, `x2`)
       ++ Q.SPEC_TAC (`wp prog' (\s'. c1 * r s' + c2 * r' s' - c) s`, `y'`)
       ++ Q.SPEC_TAC (`wp prog (\s'. c1 * r s' + c2 * r' s' - c) s`, `y`)
       ++ REPEAT (Q.PAT_ASSUM `healthy X` (K ALL_TAC))
       ++ RW_TAC posreal_ss [add_ldistrib]
       ++ Know `!a b c d : posreal. (a + b) + (c + d) = (a + c) + (b + d)`
       >> METIS_TAC [add_comm, add_assoc]
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ Suff
          `(bound1 (f s) * (c1 * x1) + bound1 (f s) * (c2 * x2)) +
           (c1 * ((1 - bound1 (f s)) * x1') + c2 * ((1 - bound1 (f s)) * x2'))
           - c <= bound1 (f s) * y + (1 - bound1 (f s)) * y'`
       >> (`!a a' b. (a = a') ==> a <= b ==> a' <= b` by PROVE_TAC [] 
           ++ METIS_TAC [mul_comm, mul_assoc])
       ++ Suff
          `(bound1 (f s) * (c1 * x1) + bound1 (f s) * (c2 * x2)) +
           ((1 - bound1 (f s)) * (c1 * x1') + (1 - bound1 (f s)) * (c2 * x2'))
           - c <= bound1 (f s) * y + (1 - bound1 (f s)) * y'`
       >> (`!a a' b. (a = a') ==> a <= b ==> a' <= b` by PROVE_TAC [] 
            ++ METIS_TAC [mul_comm, mul_assoc]) 
       ++ RW_TAC std_ss [GSYM add_ldistrib]
       ++ MATCH_MP_TAC sub_le_imp
       ++ ASM_REWRITE_TAC []
       ++ Know `c = bound1 (f s) * c + (1 - bound1 (f s)) * c`
       >> RW_TAC posreal_ss [GSYM add_rdistrib, bound1_cancel]
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ Know `!a b c d : posreal. (a + b) + (c + d) = (a + c) + (b + d)`
       >> METIS_TAC [add_comm, add_assoc]
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ RW_TAC posreal_ss [GSYM add_ldistrib]
       ++ MATCH_MP_TAC le_add2
       ++ CONJ_TAC
       ++ MATCH_MP_TAC le_lmul_imp
       ++ METIS_TAC [sub_le_eq]
       ++ METIS_TAC [mul_swap, add_ldistrib, le_lmul_imp, sub_le_eq],
       RW_TAC std_ss [up_continuous_def]
       ++ Know `up_continuous (expect,Leq) (wp prog)`
       >> PROVE_TAC [healthy_up_continuous]
       ++ RW_TAC std_ss [up_continuous_def, expect_def]
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ Q.SPEC_TAC (`r'`,`r`)
       ++ REPEAT STRIP_TAC
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`c`, `r`])
       ++ RW_TAC posreal_ss []
       ++ Know `up_continuous (expect,Leq) (wp prog')`
       >> PROVE_TAC [healthy_up_continuous]
       ++ RW_TAC std_ss [up_continuous_def, expect_def]
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`c`, `r`])
       ++ RW_TAC posreal_ss []
       ++ RW_TAC std_ss [lub_def, expect_def]
       >> (RW_TAC std_ss [Leq_def]
           ++ MATCH_MP_TAC le_add2
           ++ (CONJ_TAC ++ MATCH_MP_TAC le_lmul_imp)
           << [Suff `Leq (wp prog r') (wp prog r)` >> RW_TAC std_ss [Leq_def]
               ++ MATCH_MP_TAC healthy_mono
               ++ METIS_TAC [lub_def, expect_def],
               Suff `Leq (wp prog' r') (wp prog' r)` >> RW_TAC std_ss [Leq_def]
               ++ MATCH_MP_TAC healthy_mono
               ++ PROVE_TAC [lub_def, expect_def]])
       ++ RW_TAC posreal_ss [Leq_def]
       ++ MATCH_MP_TAC le_trans
       ++ Q.EXISTS_TAC
          `sup
           (\r.
              ?z.
                c z /\
                (r = bound1 (f s) * wp prog z s +
                     (1 - bound1 (f s)) * wp prog' z s))`
       ++ REVERSE CONJ_TAC
       >> (RW_TAC posreal_ss [sup_le]
           ++ Suff
              `Leq (\s. bound1 (f s) * wp prog z' s +
                    (1 - bound1 (f s)) * wp prog' z' s) z`
           >> (RW_TAC posreal_ss [Leq_def]
           ++ METIS_TAC [])
           ++ FIRST_ASSUM MATCH_MP_TAC
           ++ CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
           ++ RW_TAC posreal_ss []
           ++ PROVE_TAC [])
       ++ RW_TAC posreal_ss [le_sup]
       ++ MATCH_MP_TAC le_trans
       ++ Q.EXISTS_TAC
          `sup (\r. ?z. c z /\ (r = bound1 (f s) * wp prog z s)) +
           sup (\r. ?z. c z /\ (r = (1 - bound1 (f s)) * wp prog' z s))`
       ++ REVERSE CONJ_TAC
       >> (RW_TAC posreal_ss [add_sup, sup_le]
           << [ Know `?w. c w /\ Leq z' w /\ Leq z'' w`
               >> (MP_TAC (Q.SPECL [`expect`, `Leq`, `c`]
                           (INST_TYPE [alpha |-> ``:'a state expect``]
                                      chain_def))
                   ++ METIS_TAC [expect_def, leq_refl])
               ++ STRIP_TAC
               ++ MATCH_MP_TAC le_trans
               ++ Q.EXISTS_TAC
                  `bound1 (f s) * wp prog w s +
                   (1 - bound1 (f s)) * wp prog' w s`
               ++ REVERSE CONJ_TAC >> METIS_TAC []
               ++ MATCH_MP_TAC le_add2
               ++ CONJ_TAC
	       ++ RW_TAC posreal_ss []
               ++ MATCH_MP_TAC le_lmul_imp
               ++ Q.SPEC_TAC (`s`, `s`)
               ++ Know `!e f : 'a state expect. Leq e f ==> (!s. e s <= f s)`
               >> METIS_TAC [Leq_def]
               ++ DISCH_THEN HO_MATCH_MP_TAC
               ++ CONV_TAC (DEPTH_CONV ETA_CONV)
               ++ METIS_TAC [healthy_mono]
               ++ METIS_TAC [Leq_def]
               ++ METIS_TAC [healthy_mono],
               MATCH_MP_TAC le_trans
               ++ Q.EXISTS_TAC
                  `bound1 (f s) * wp prog z' s +
                   (1 - bound1 (f s)) * wp prog' z' s`
               ++ REVERSE CONJ_TAC >> METIS_TAC []
               ++ MATCH_MP_TAC le_add2
               ++ RW_TAC posreal_ss [],
               MATCH_MP_TAC le_trans
               ++ Q.EXISTS_TAC
                  `bound1 (f s) * wp prog z' s +
                   (1 - bound1 (f s)) * wp prog' z' s`
               ++ REVERSE CONJ_TAC >> METIS_TAC []
               ++ MATCH_MP_TAC le_add2
               ++ RW_TAC posreal_ss [],
               RW_TAC posreal_ss []])
       ++ RW_TAC posreal_ss []
       ++ POP_ASSUM (K ALL_TAC)
       ++ POP_ASSUM (K ALL_TAC)
       ++ SIMP_TAC posreal_ss [sup_lmult]
       ++ MATCH_MP_TAC le_add2
       ++ (CONJ_TAC
           ++ MATCH_MP_TAC le_lmul_imp
           ++ Q.SPEC_TAC (`s`, `s`)
           ++ Know `!e f : 'a state expect. Leq e f ==> (!s. e s <= f s)`
           >> METIS_TAC [Leq_def]
           ++ DISCH_THEN HO_MATCH_MP_TAC
           ++ CONV_TAC (DEPTH_CONV ETA_CONV)) 
       << [Q.PAT_ASSUM `lub X Y Z` (K ALL_TAC)
           ++ Q.PAT_ASSUM `lub X Y Z` MP_TAC
           ++ RW_TAC real_ss [lub_def, expect_def]
           ++ FIRST_ASSUM MATCH_MP_TAC
           ++ RW_TAC posreal_ss [Leq_def]   
           ++ MATCH_MP_TAC le_sup_imp
           ++ BETA_TAC
           ++ METIS_TAC [],
           Q.PAT_ASSUM `lub X Y Z` MP_TAC
           ++ Q.PAT_ASSUM `lub X Y Z` (K ALL_TAC)
           ++ RW_TAC real_ss [lub_def, expect_def]
           ++ FIRST_ASSUM MATCH_MP_TAC
           ++ RW_TAC posreal_ss [Leq_def]
           ++ MATCH_MP_TAC le_sup_imp
           ++ BETA_TAC
           ++ METIS_TAC []]]);

val () = print "wp Prob is healthy\n";

val wp_while_monotonic = lemma
  (``!trans cond l.
       healthy trans /\
       (!r. expect_lfp (\e s. (if cond s then trans e s else r s)) = l r) ==>
       monotonic (expect,Leq) l``,
   RW_TAC std_ss []
   ++ RW_TAC std_ss [monotonic_def, expect_def, lub_def]
   ++ Q.PAT_ASSUM `!r. P r` (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ MATCH_MP_TAC refines_lfp
   ++ (RW_TAC posreal_ss [monotonic_def, refines_def, expect_def]
       ++ RW_TAC std_ss [Leq_def]
       ++ RW_TAC posreal_ss [])
   << [Suff `Leq (trans e) (trans e')` >> RW_TAC std_ss [Leq_def]
       ++ METIS_TAC [healthy_mono],
       Suff `Leq (trans e) (trans e')` >> RW_TAC std_ss [Leq_def]
       ++ METIS_TAC [healthy_mono],
       FULL_SIMP_TAC std_ss [Leq_def]]);

val wp_while_upcontinuous = lemma
  (``!trans cond l.
       healthy trans /\
       (!r. expect_lfp (\e s. (if cond s then trans e s else r s)) = l r) ==>
       (!r. (\s. (if cond s then trans (l r) s else r s)) = l r) /\
       (!r y.
          Leq (\s. (if cond s then trans y s else r s)) y ==> Leq (l r) y) ==>
       up_continuous (expect,Leq) l``,
   RW_TAC std_ss []
   ++ RW_TAC std_ss [up_continuous_def, expect_def, lub_def]
   >> (FIRST_ASSUM MATCH_MP_TAC
       ++ Q.PAT_ASSUM `!r. P r = Q r`
          (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
       ++ RW_TAC std_ss [Leq_def]
       ++ RW_TAC posreal_ss []
       ++ Suff `Leq z x` >> SIMP_TAC std_ss [Leq_def]
       ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC leq_trans
   ++ Q.EXISTS_TAC `\s. sup (\r. ?y. c y /\ (r = l y s))`
   ++ REVERSE CONJ_TAC
   >> (RW_TAC posreal_ss [sup_le, Leq_def]
       ++ Suff `Leq (l y) z`
       >> RW_TAC posreal_ss [Leq_def]
       ++ FIRST_ASSUM MATCH_MP_TAC
       ++ PROVE_TAC [])
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ Q.PAT_ASSUM `!r. P r = Q r`
      (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   ++ RW_TAC std_ss [Leq_def]
   ++ REVERSE (RW_TAC std_ss [])
      >> (Suff `Leq x (\s. sup (\r. ?y. c y /\ (r = y s)))`
          >> RW_TAC std_ss [Leq_def]
          ++ FIRST_ASSUM MATCH_MP_TAC
          ++ RW_TAC std_ss [Leq_def, le_sup]
          ++ PROVE_TAC [])
   ++ Know `up_continuous (expect,Leq) trans` >> PROVE_TAC [healthy_def]
   ++ SIMP_TAC std_ss [expect_def, up_continuous_def]
   ++ DISCH_THEN
      (MP_TAC o Q.SPECL
       [`\y : 'a -> posreal. ?z : 'a -> posreal. c z /\ (y = l z)`,
        `\s : 'a. sup (\r. ?y : 'a -> posreal. c y /\ (r = l y s))`])
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC
   >> (REVERSE CONJ_TAC
       >> (RW_TAC posreal_ss [lub_def, expect_def, Leq_def, le_sup, sup_le]
           >> METIS_TAC []
           ++ Q.SPEC_TAC (`s'`, `q`)
           ++ FIRST_ASSUM HO_MATCH_MP_TAC
           ++ CONV_TAC (DEPTH_CONV ETA_CONV)
           ++ METIS_TAC [])
       ++ Q.PAT_ASSUM `chain X Y` MP_TAC
       ++ RW_TAC posreal_ss [chain_def, expect_def]
       ++ MP_TAC (Q.SPECL [`trans`, `cond`, `l`] wp_while_monotonic)
       ++ RW_TAC std_ss [monotonic_def, expect_def]
       ++ METIS_TAC [])
   ++ RW_TAC std_ss [lub_def, expect_def]
   ++ Suff
      `Leq (trans (\s : 'a. sup (\r. ?y : 'a -> posreal. c y /\ (r = l y s))))
       (\s. sup (\r. ?y. c y /\ (r = trans (l y) s)))`
   >> RW_TAC std_ss [Leq_def]
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ RW_TAC posreal_ss [Leq_def, le_sup]
   ++ METIS_TAC []);

val wp_while_sublinear1 = lemma
  (``!cond prog l.
       healthy (wp prog) /\
       (!r. (\s. (if cond s then wp prog (l r) s else r s)) = l r) /\
       (!r y.
          Leq (\s. (if cond s then wp prog y s else r s)) y ==> Leq (l r) y) ==>
       (!r c s. ~(c = infty) ==> l r s - c <= l (\s'. r s' - c) s)``,
   RW_TAC posreal_ss []
   ++ MATCH_MP_TAC sub_le_imp
   ++ RW_TAC std_ss []
   ++ Suff `Leq (l r) (\s. l (\s'. r s' - c) s + c)`
   >> RW_TAC std_ss [Leq_def]
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss [Leq_def]
   ++ Q.PAT_ASSUM `!r. P r = Q r`
      (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
   ++ REVERSE (RW_TAC std_ss [])
   >> (Cases_on `c <= r s` >> METIS_TAC [sub_add, le_refl]
       ++ MATCH_MP_TAC le_trans
       ++ Q.EXISTS_TAC `c`
       ++ METIS_TAC [le_total, le_addl])
   ++ Know `sublinear (wp prog)` >> METIS_TAC [healthy_def]
   ++ RW_TAC std_ss [sublinear_alt]
   ++ Q.PAT_ASSUM `!c r s. P c ==> Q c r s`
      (MP_TAC o Q.SPECL [`c`, `\s. l (\s':'a state. r s' - c) s + c`, `s`])
   ++ ASM_SIMP_TAC std_ss [add_sub, sub_le_eq]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ METIS_TAC []);

val healthy_wp_while = lemma
  (``!cond prog. healthy (wp prog) ==> healthy (wp (While cond prog))``,
   RW_TAC real_ss [wp_def, cond_eta]
   ++ Know
      `!r.
         (expect_lfp (\e s. (if cond s then wp prog e s else r s)) =
          (\r. expect_lfp (\e s. (if cond s then wp prog e s else r s))) r) /\
         lfp (expect,Leq) (\e s. if cond s then wp prog e s else r s)
         ((\r. expect_lfp (\e s. (if cond s then wp prog e s else r s))) r)`
   >> (RW_TAC std_ss []
       ++ MATCH_MP_TAC expect_lfp_def
       ++ RW_TAC std_ss [monotonic_def, expect_def]
       ++ RW_TAC posreal_ss [Leq_def]
       ++ RW_TAC posreal_ss []
       ++ Q.SPEC_TAC (`s`, `s`)
       ++ Know `!e f : 'a state expect. Leq e f ==> (!s. e s <= f s)`
       >> METIS_TAC [Leq_def]
       ++ DISCH_THEN HO_MATCH_MP_TAC
       ++ CONV_TAC (DEPTH_CONV ETA_CONV)
       ++ METIS_TAC [healthy_mono])
   ++ Q.SPEC_TAC
      (`\r. expect_lfp (\e s. (if cond s then wp prog e s else r s))`, `l`)
   ++ SIMP_TAC std_ss [lfp_def, expect_def, FORALL_AND_THM]
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`cond`, `l`] (Q.ISPEC `wp prog` wp_while_monotonic))
   ++ MP_TAC (Q.SPECL [`cond`, `l`] (Q.ISPEC `wp prog` wp_while_upcontinuous))
   ++ RW_TAC std_ss []
   ++ ASM_SIMP_TAC real_ss [healthy_def]
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (a ==> b) ==> a /\ b``)
   ++ CONJ_TAC
   >> (RW_TAC real_ss [feasible_def]
       ++ RW_TAC std_ss [GSYM leq_zero]
       ++ Q.PAT_ASSUM `!r. P r` MATCH_MP_TAC
       ++ RW_TAC std_ss [Leq_def]
       ++ RW_TAC posreal_ss []
       ++ Q.SPEC_TAC (`s`, `s`)
       ++ Know `!e f : 'a state expect. Leq e f ==> (!s. e s <= f s)`
       >> METIS_TAC [Leq_def]
       ++ DISCH_THEN HO_MATCH_MP_TAC
       ++ CONV_TAC (DEPTH_CONV ETA_CONV)
       ++ RW_TAC std_ss [leq_zero]
       ++ METIS_TAC [feasible_def, healthy_feasible])
   ++ RW_TAC real_ss [sublinear_alt]
   << [MP_TAC (Q.SPECL [`cond`, `prog`, `l`] wp_while_sublinear1)
       ++ RW_TAC std_ss [],
       Suff `Leq (\s. c * l r s) (l (\s'. c * r s'))` >> RW_TAC std_ss [Leq_def]
       ++ Q.SPEC_TAC (`c`, `c`)
       ++ HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!p. (!c. ~(c = infty) ==> p c) /\ p infty ==> !c. p c``)
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (a ==> b) ==> a /\ b``)
       ++ CONJ_TAC
       >> (RW_TAC std_ss [Leq_def]
           ++ Cases_on `c = 0` >> RW_TAC posreal_ss []
           ++ MATCH_MP_TAC le_trans
           ++ Q.EXISTS_TAC `c * (inv c * l (\s'. c * r s') s)`
           ++ REVERSE CONJ_TAC >> RW_TAC posreal_ss [GSYM mul_assoc, mul_rinv]
           ++ MATCH_MP_TAC le_lmul_imp
           ++ Suff `Leq (l r) (\s. inv c * l (\s'. c * r s') s)`
           >> RW_TAC std_ss [Leq_def]
           ++ FIRST_ASSUM MATCH_MP_TAC
           ++ RW_TAC std_ss [Leq_def]
           ++ Q.PAT_ASSUM `!r. P r = Q r`
              (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))
           ++ RW_TAC posreal_ss [GSYM mul_assoc, mul_linv, mul_lone]
           ++ Know `!x y. inv c * (c * x) <= y ==> x <= y`
           >> RW_TAC posreal_ss [GSYM mul_assoc, mul_linv, mul_lone]
           ++ DISCH_THEN MATCH_MP_TAC
           ++ MATCH_MP_TAC le_lmul_imp
           ++ Know `sublinear (wp prog)` >> METIS_TAC [healthy_sublinear]
           ++ SIMP_TAC std_ss [sublinear_def]
           ++ DISCH_THEN
              (MP_TAC o Q.SPECL
               [`\s. inv c * l (\s' : 'a state. c * r s') s`, `r`, `c`,
                `0`, `0`, `s`])
           ++ ASM_SIMP_TAC posreal_ss [GSYM mul_assoc, mul_rinv, mul_lone]
           ++ CONV_TAC (DEPTH_CONV ETA_CONV)
           ++ RW_TAC std_ss [])
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `up_continuous X Y` MP_TAC
       ++ SIMP_TAC std_ss [up_continuous_def]
       ++ DISCH_THEN
          (MP_TAC o Q.SPECL
           [`\z. ?n : num. !s. z s = & n * r s`, `\s. infty * r s`])
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> (a ==> b) ==> c``)
       ++ CONJ_TAC
       >> (POP_ASSUM_LIST (K ALL_TAC)
           ++ (RW_TAC posreal_ss [chain_def, lub_def, expect_def, Leq_def]
               ++ RW_TAC posreal_ss [])
           << [MP_TAC (Q.SPECL [`& n`, `& n'`] le_total)
               ++ METIS_TAC [le_rmul_imp],
               MATCH_MP_TAC le_rmul_imp
               ++ RW_TAC posreal_ss [],
               MATCH_MP_TAC le_trans
               ++ Q.EXISTS_TAC `sup (\q. ?n. q = & n * r s)`
               ++ CONJ_TAC >> RW_TAC posreal_ss [sup_num_mul]
               ++ RW_TAC posreal_ss [sup_le]
               ++ Q.SPEC_TAC (`s`, `s`)
               ++ FIRST_ASSUM HO_MATCH_MP_TAC
               ++ METIS_TAC []])
       ++ RW_TAC std_ss [lub_def, expect_def]
       ++ MATCH_MP_TAC leq_trans
       ++ Q.EXISTS_TAC `\s. sup (\q. ?n : num. q = & n * l r s)`
       ++ CONJ_TAC >> RW_TAC posreal_ss [sup_num_mul, leq_refl]
       ++ RW_TAC posreal_ss [sup_le, Leq_def]
       ++ MATCH_MP_TAC le_trans
       ++ Q.EXISTS_TAC `l (\s'. & n * r s') s`
       ++ CONJ_TAC
       >> (Suff `Leq (\s. & n * l r s) (l (\s'. & n * r s'))`
           >> SIMP_TAC posreal_ss [Leq_def]
           ++ RW_TAC posreal_ss [])
       ++ Suff `Leq (l (\s'. & n * r s')) (l (\s'. infty * r s'))`
       >> SIMP_TAC posreal_ss [Leq_def]
       ++ FIRST_ASSUM MATCH_MP_TAC
       ++ Q.EXISTS_TAC `\s. & n * r s`
       ++ RW_TAC std_ss []
       ++ METIS_TAC [],
       Suff `Leq (\s. l r1 s + l r2 s) (l (\s'. r1 s' + r2 s'))`
       >> RW_TAC posreal_ss [Leq_def]
       ++ MATCH_MP_TAC leq_trans
       ++ Q.EXISTS_TAC
          `\s. sup (\q. ?r n. (!s. r s = if & n <= r2 s then & n else r2 s) /\
                          (q = l r1 s + l r s))`
       ++ CONJ_TAC
       >> (MATCH_MP_TAC leq_trans
           ++ Q.EXISTS_TAC
              `\s. l r1 s +
                 sup (\q. ?r n. (!s. r s = if & n <= r2 s then & n else r2 s) /\
                      (q = l r s))`
           ++ REVERSE CONJ_TAC
           >> (RW_TAC posreal_ss [le_sup, Leq_def]
               ++ Cases_on `y = infty` >> RW_TAC posreal_ss []
               ++ ONCE_REWRITE_TAC [add_comm]
               ++ Cases_on
                  `sup (\q. ?r n. (!s. r s = if & n <= r2 s then & n else r2 s)
                        /\ (q = l r s)) = 0`
               >> (RW_TAC posreal_ss []
                   ++ FIRST_ASSUM MATCH_MP_TAC
                   ++ Q.EXISTS_TAC `Zero`
                   ++ Q.EXISTS_TAC `0`
                   ++ RW_TAC posreal_ss [Zero_def]
                   ++ RW_TAC posreal_ss [GSYM Zero_def]
                   ++ Q.PAT_ASSUM `feasible l` MP_TAC
                   ++ RW_TAC std_ss [feasible_def]
                   ++ RW_TAC posreal_ss [Zero_def])
               ++ RW_TAC posreal_ss [GSYM le_sub_eq, sup_le]
               ++ MATCH_MP_TAC le_sub_imp
               ++ RW_TAC std_ss []
               ++ ONCE_REWRITE_TAC [add_comm]
               ++ FIRST_ASSUM MATCH_MP_TAC
               ++ METIS_TAC [])
           ++ RW_TAC posreal_ss [Leq_def, le_ladd]
           ++ DISJ2_TAC
           ++ Suff
              `Leq (l r2)
               (\s. sup
                (\q. ?r n.
                 (!s. r s = (if & n <= r2 s then & n else r2 s)) /\
                 (q = l r s)))`
           >> RW_TAC std_ss [Leq_def]
           ++ Q.PAT_ASSUM `up_continuous X Y` MP_TAC
           ++ SIMP_TAC std_ss [up_continuous_def]
           ++ DISCH_THEN
              (MP_TAC o Q.SPECL
               [`\e. ?n. e = \x. if & n <= r2 x then & n else r2 x`, `r2`])
           ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
           ++ CONJ_TAC
           >> ((RW_TAC std_ss [chain_def, lub_def, expect_def, Leq_def]
                ++ RW_TAC posreal_ss [])
               >> METIS_TAC [le_total, le_refl, le_trans]
               ++ REVERSE (Cases_on `r2 s = infty`)
               >> (Know `?n : num. ~(& n <= r2 s)`
                   >> (pcases_on `r2 s`
                       ++ MP_TAC (Q.SPEC `y` REAL_BIGNUM)
                       ++ RW_TAC std_ss []
                       ++ RW_TAC posreal_ss [posreal_of_num_def, preal_le_eq]
                       ++ METIS_TAC [real_lt])
                   ++ RW_TAC std_ss []
                   ++ Q.PAT_ASSUM `!y. P y`
                      (MP_TAC o Q.SPEC `\x. if & n <= r2 x then & n else r2 x`)
                   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b==>c) ==> ((a==>b)==>c)``)
                   ++ CONJ_TAC >> METIS_TAC []
                   ++ DISCH_THEN (MP_TAC o Q.SPEC `s`)
                   ++ RW_TAC std_ss [])
               ++ ASM_REWRITE_TAC [GSYM sup_num]
               ++ RW_TAC std_ss [sup_le]
               ++ Q.PAT_ASSUM `!y. P y`
                  (MP_TAC o Q.SPEC `\x. if & n <= r2 x then & n else r2 x`)
               ++ MATCH_MP_TAC (PROVE [] ``a /\ (b==>c) ==> ((a==>b)==>c)``)
               ++ CONJ_TAC >> METIS_TAC []
               ++ DISCH_THEN (MP_TAC o Q.SPEC `s`)
               ++ RW_TAC posreal_ss [])
           ++ RW_TAC posreal_ss [lub_def, expect_def]
           ++ FIRST_ASSUM MATCH_MP_TAC
           ++ RW_TAC posreal_ss [Leq_def, le_sup]
           ++ FIRST_ASSUM MATCH_MP_TAC
           ++ RW_TAC posreal_ss []
           ++ Q.EXISTS_TAC `\s. if & n <= r2 s then & n else r2 s`
           ++ Q.EXISTS_TAC `n`
           ++ RW_TAC std_ss [])
       ++ MATCH_MP_TAC leq_trans
       ++ Q.EXISTS_TAC
          `\s. sup (\q. ?r n. (!s. r s = (if & n <= r2 s then & n else r2 s))
                    /\ (q = l (\s'. r1 s' + r s') s))`
       ++ REVERSE CONJ_TAC
       >> (RW_TAC posreal_ss [Leq_def, sup_le]
           ++ RW_TAC posreal_ss []
           ++ Suff
              `Leq (l (\s'. r1 s' + if & n <= r2 s' then & n else r2 s'))
               (l (\s'. r1 s' + r2 s'))`
           >> RW_TAC posreal_ss [Leq_def]
           ++ Q.PAT_ASSUM `montonic X Y` MP_TAC
           ++ SIMP_TAC posreal_ss [monotonic_def, expect_def]
           ++ DISCH_THEN MATCH_MP_TAC
           ++ RW_TAC posreal_ss [Leq_def, le_ladd]
           ++ METIS_TAC [le_refl])
       ++ RW_TAC posreal_ss [Leq_def]
       ++ MATCH_MP_TAC sup_le_sup_imp
       ++ RW_TAC posreal_ss []
       ++ Q.EXISTS_TAC `l (\s'. r1 s' + r s') s`
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `r`
           ++ Q.EXISTS_TAC `n`
           ++ RW_TAC posreal_ss [])
       ++ Know `!s. r s <= & n`
       >> (RW_TAC posreal_ss [] ++ METIS_TAC [le_total])
       ++ POP_ASSUM (K ALL_TAC)
       ++ STRIP_TAC
       ++ Know `!s. ~(r s = infty)`
       >> (REPEAT STRIP_TAC
           ++ Q.PAT_ASSUM `!s. P s` (MP_TAC o Q.SPEC `s`)
           ++ RW_TAC posreal_ss [])
       ++ STRIP_TAC
       ++ Know `!s. l r s <= & n`
       >> (GEN_TAC
           ++ MP_TAC (Q.SPECL [`cond`, `prog`, `l`] wp_while_sublinear1)
           ++ ASM_SIMP_TAC std_ss []
           ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `& n`, `s`])
           ++ ASM_SIMP_TAC posreal_ss [sub_le_eq]
           ++ Suff `l (\s. r s - & n) = Zero`
           >> RW_TAC posreal_ss [Zero_def]
           ++ Q.PAT_ASSUM `feasible l` MP_TAC
           ++ Suff `(\s. r s - & n) = Zero`
           ++ SIMP_TAC std_ss [feasible_def]
           ++ RW_TAC posreal_ss [FUN_EQ_THM, Zero_def]
           ++ MATCH_MP_TAC le_imp_sub_zero
           ++ RW_TAC posreal_ss [])
       ++ STRIP_TAC
       ++ Know `!s. ~(l r s = infty)`
       >> (REPEAT STRIP_TAC
           ++ Q.PAT_ASSUM `!s. P s` (MP_TAC o Q.SPEC `s`)
           ++ RW_TAC posreal_ss [])
       ++ STRIP_TAC
       ++ Cases_on `l r1 s = 0`
       >> (RW_TAC posreal_ss []
           ++ Q.PAT_ASSUM `monotonic X Y` MP_TAC
           ++ SIMP_TAC std_ss [monotonic_def, expect_def]
           ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `\s'. r1 s' + r s'`])
           ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
           ++ CONJ_TAC >> RW_TAC posreal_ss [Leq_def]
           ++ RW_TAC posreal_ss [Leq_def])
       ++ RW_TAC std_ss [GSYM le_sub_eq]
       ++ POP_ASSUM (K ALL_TAC)
       ++ Suff `Leq (l r1) (\s. l (\s'. r1 s' + r s') s - l r s)`
       >> (SIMP_TAC posreal_ss [Leq_def]
           ++ DISCH_THEN (MP_TAC o Q.SPEC `s`)
           ++ RW_TAC std_ss [])
       ++ FIRST_ASSUM MATCH_MP_TAC
       ++ Q.PAT_ASSUM `!r. P r = Q r`
          (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))       
       ++ RW_TAC posreal_ss [Leq_def]
       ++ REVERSE (Cases_on `cond s` ++ ASM_SIMP_TAC posreal_ss [add_sub])
       ++ POP_ASSUM (K ALL_TAC)
       ++ MP_TAC (Q.SPECL [`\s. l (\s' : 'a state. r1 s' + r s' : posreal) s`,
                           `l (r:'a state expect)`, `& n`]
                  (Q.ISPEC `wp prog` healthy_sub))
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC
       >> (RW_TAC posreal_ss []
           ++ Suff `Leq (l r) (l (\s. r1 s + r s))` >> RW_TAC std_ss [Leq_def]
           ++ Q.PAT_ASSUM `monotonic X Y` MP_TAC
           ++ SIMP_TAC std_ss [monotonic_def, expect_def]
           ++ DISCH_THEN MATCH_MP_TAC
           ++ RW_TAC posreal_ss [Leq_def])
       ++ CONV_TAC (DEPTH_CONV ETA_CONV)
       ++ RW_TAC posreal_ss [Leq_def]]);

val () = print "wp While is healthy\n";

val wp_healthy = store_thm
  ("wp_healthy",
   ``!prog. healthy (wp prog)``,
   Induct
   << [PROVE_TAC [healthy_wp_abort],
       PROVE_TAC [healthy_wp_consume],
       PROVE_TAC [healthy_wp_assign],
       PROVE_TAC [healthy_wp_seq],
       PROVE_TAC [healthy_wp_nondet],
       PROVE_TAC [healthy_wp_prob],
       PROVE_TAC [healthy_wp_while]]);

(* ------------------------------------------------------------------------- *)
(* And so we can transfer the following nice properties to wp transformers   *)
(* ------------------------------------------------------------------------- *)

val wp_zero = store_thm
  ("wp_zero",
   ``!p. wp p Zero = Zero``,
   PROVE_TAC [healthy_zero, wp_healthy]);

val wp_mono = store_thm
  ("wp_mono",
   ``!p r1 r2. Leq r1 r2 ==> Leq (wp p r1) (wp p r2)``,
   PROVE_TAC [healthy_mono, wp_healthy]);

val wp_scale = store_thm
  ("wp_scale",
   ``!p r c s. wp p (\s'. c * r s') s = c * wp p r s``,
   METIS_TAC [healthy_scale, wp_healthy]);

val wp_conj = store_thm
  ("wp_conj",
   ``!p r1 r2. Leq (Conj (wp p r1) (wp p r2)) (wp p (Conj r1 r2))``,
   PROVE_TAC [healthy_conj, wp_healthy]);

(* ------------------------------------------------------------------------- *)
(* Useful properties of programs                                             *)
(* ------------------------------------------------------------------------- *)

val seq_assoc = store_thm
  ("seq_assoc",
   ``!p q r. wp (Seq p (Seq q r)) = wp (Seq (Seq p q) r)``,
   RW_TAC std_ss [wp_def]);

val wp_skip = store_thm
  ("wp_skip",
   ``!r. wp Skip r = r``,
   RW_TAC std_ss [wp_def, Skip_def]);

val wp_if = store_thm
  ("wp_if",
   ``!c a b r. wp (If c a b) r = Cond c (wp a r) (wp b r)``,
   RW_TAC std_ss [wp_def, If_def, cond_eta, lin_eta]
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC posreal_ss [bound1_basic]
   ++ Q.UNABBREV_TAC `x`
   ++ RW_TAC posreal_ss [mul_lone, mul_lzero]);

(* ------------------------------------------------------------------------- *)
(* Anything refines Abort                                                    *)
(* ------------------------------------------------------------------------- *)

val refines_abort = store_thm
  ("refines_abort",
   ``!p. refines (wp Abort) (wp p)``,
   RW_TAC std_ss [wp_def, wp_healthy, refines_zero]);

(* ------------------------------------------------------------------------- *)
(* Probabilistic choice refines demonic choice                               *)
(* ------------------------------------------------------------------------- *)

val refines_nondet_prob = store_thm
  ("refines_nondet_prob",
   ``!f p q. refines (wp (Nondet p q)) (wp (Prob f p q))``,
   RW_TAC std_ss [refines_def, wp_def, Min_def, Leq_def, min_le_lin, Lin_def]
   ++ Q.UNABBREV_TAC `x`
   ++ RW_TAC posreal_ss [min_le_lin, Lin_def]);

(* ------------------------------------------------------------------------- *)
(* wlp is the partial-correctness analogue of wp.                            *)
(* ------------------------------------------------------------------------- *)

val wlp_def = Define
  `(wlp Abort = \r. Magic) /\
   (wlp (Consume k) = \r. r) /\
   (wlp (Assign v e) = \r s. r (assign v e s)) /\
   (wlp (Seq a b) = \r. wlp a (wlp b r)) /\
   (wlp (Nondet a b) = \r. Min (wlp a r) (wlp b r)) /\
   (wlp (Prob p a b) = \r. Lin p (wlp a r) (wlp b r)) /\
   (wlp (While c b) = \r. expect_gfp (\e. Cond c (wlp b e) r))`;

(* ------------------------------------------------------------------------- *)
(* wlp is not healthy, but it does satisfy some nice properties.             *)
(* [It's obvious that wlp can't be healthy, because wlp Abort Zero = Magic.] *)
(* ------------------------------------------------------------------------- *)

val wlp_mono = store_thm
  ("wlp_mono",
   ``!p r1 r2. Leq r1 r2 ==> Leq (wlp p r1) (wlp p r2)``,
   (Induct ++ RW_TAC std_ss [wlp_def, leq_refl])
   << [FULL_SIMP_TAC std_ss [Leq_def, assign_eta],
       METIS_TAC [min_leq2_imp],
       RW_TAC std_ss [Leq_def, lin_eta]
       ++ MATCH_MP_TAC le_add2
       ++ METIS_TAC [Leq_def, le_lmul_imp, le_add2],
       MATCH_MP_TAC refines_gfp
       ++ RW_TAC std_ss [monotonic_def, refines_def, Leq_def, cond_eta]
       ++ RW_TAC posreal_ss []
       ++ METIS_TAC [Leq_def]]);

(* ------------------------------------------------------------------------- *)
(* The whole point of using wlp is that it gives the following nice rule for *)
(* calculating weakest preconditions of while loops, ASSUMING THAT THE LOOP  *)
(* TERMINATES.                                                               *)
(* ------------------------------------------------------------------------- *)

val wlp_while = store_thm
  ("wlp_while",
   ``!cond body pre post.
       Leq pre (Cond cond (wlp body pre) post) ==>
       Leq pre (wlp (While cond body) post)``,
   RW_TAC std_ss [wlp_def, cond_eta]
   ++ Know
      `!r.
         (expect_gfp (\e s. (if cond s then wlp body e s else r s)) =
          (\r. expect_gfp (\e s. (if cond s then wlp body e s else r s))) r) /\
         gfp (expect,Leq) (\e s. if cond s then wlp body e s else r s)
         ((\r. expect_gfp (\e s. (if cond s then wlp body e s else r s))) r)`
   >> (RW_TAC std_ss []
       ++ MATCH_MP_TAC expect_gfp_def
       ++ RW_TAC std_ss [monotonic_def, expect_def]
       ++ RW_TAC posreal_ss [Leq_def]
       ++ RW_TAC posreal_ss []
       ++ Q.SPEC_TAC (`s`, `s`)
       ++ SIMP_TAC posreal_ss [GSYM Leq_def]
       ++ CONV_TAC (DEPTH_CONV ETA_CONV)
       ++ METIS_TAC [wlp_mono, monotonic_def, expect_def])
   ++ DISCH_THEN (MP_TAC o Q.SPEC `post`)
   ++ SIMP_TAC std_ss []
   ++ Q.SPEC_TAC
      (`expect_gfp (\e s. (if cond s then wlp body e s else post s))`, `g`)
   ++ RW_TAC std_ss [gfp_def, expect_def]);

(* ------------------------------------------------------------------------- *)
(* wlp of derived programs.                                                  *)
(* ------------------------------------------------------------------------- *)

val wlp_skip = store_thm
  ("wlp_skip",
   ``!r. wlp Skip r = r``,
   RW_TAC std_ss [Skip_def,wlp_def]);

val wlp_if = store_thm
  ("wlp_if",
   ``!c a b r. wlp (If c a b) r = Cond c (wlp a r) (wlp b r)``,
   RW_TAC std_ss [wlp_def, If_def, cond_eta, lin_eta]
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC posreal_ss [bound1_basic]
   ++ Q.UNABBREV_TAC `x`
   ++ RW_TAC posreal_ss [mul_lone, mul_lzero]);

(* ------------------------------------------------------------------------- *)
(* Automatic tool for calculating wlps.                                      *)
(* ------------------------------------------------------------------------- *)

val wlp_assert_vc = store_thm
  ("wlp_assert_vc",
   ``!pre mid post.
        Leq mid (wlp a post) /\
        Leq pre mid ==>
        Leq pre (wlp (Assert pre a) post)``,
   RW_TAC std_ss [Assert_def]
   ++ METIS_TAC [leq_trans]);

val wlp_abort_vc = store_thm
  ("wlp_abort_vc",
   ``!post. Leq Magic (wlp Abort post)``,
   RW_TAC posreal_ss [wlp_def, Leq_def, Magic_def]);

val wlp_consume_vc = store_thm
  ("wlp_consume_vc",
   ``!post k. Leq post (wlp (Consume k) post)``,
   RW_TAC std_ss [wlp_def, leq_refl]);

val wlp_assign_vc = store_thm
  ("wlp_assign_vc",
   ``!post v e. Leq (post o assign v e) (wlp (Assign v e) post)``,
   RW_TAC std_ss [wlp_def, Leq_def, assign_eta, o_THM, le_refl]);

val wlp_seq_vc = store_thm
  ("wlp_seq_vc",
   ``!pre mid post c1 c2.
       Leq mid (wlp c2 post) /\ Leq pre (wlp c1 mid) ==>
       Leq pre (wlp (Seq c1 c2) post)``,
   RW_TAC std_ss [wlp_def]
   ++ MATCH_MP_TAC leq_trans
   ++ Q.EXISTS_TAC `wlp c1 mid`
   ++ RW_TAC std_ss []
   ++ METIS_TAC [wlp_mono, Leq_def]);

val wlp_nondet_vc = store_thm
  ("wlp_nondet_vc",
   ``!pre1 pre2 post c1 c2.
       Leq pre1 (wlp c1 post) /\ Leq pre2 (wlp c2 post) ==>
       Leq (Min pre1 pre2) (wlp (Nondet c1 c2) post)``,
   RW_TAC std_ss [wlp_def, Leq_def]
   ++ MATCH_MP_TAC le_trans
   ++ Q.EXISTS_TAC `Min pre1 pre2 s`
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [Min_def, le_refl]
   ++ METIS_TAC [min_le2_imp]);

val wlp_prob_vc = store_thm
  ("wlp_prob_vc",
   ``!pre1 pre2 post p c1 c2.
       Leq pre1 (wlp c1 post) /\ Leq pre2 (wlp c2 post) ==>
       Leq (Lin p pre1 pre2) (wlp (Prob p c1 c2) post)``,
   RW_TAC std_ss [wlp_def, Leq_def]
   ++ MATCH_MP_TAC le_trans
   ++ Q.EXISTS_TAC `Lin p pre1 pre2 s`
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [Lin_def, le_refl]
   ++ METIS_TAC [le_add2, le_lmul_imp]);

val wlp_while_vc = store_thm
  ("wlp_while_vc",
   ``!pre post mid b c.
       Leq mid (wlp c pre) /\ Leq pre (Cond b mid post) ==>
       Leq pre (wlp (Assert pre (While b c)) post)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC wlp_assert_vc
   ++ Q.EXISTS_TAC `pre`
   ++ RW_TAC std_ss [leq_refl]
   ++ MATCH_MP_TAC wlp_while
   ++ FULL_SIMP_TAC std_ss [Leq_def, Cond_def]
   ++ METIS_TAC [le_trans]);

val wlp_skip_vc = store_thm
  ("wlp_skip_vc",
   ``!post. Leq post (wlp Skip post)``,
   RW_TAC std_ss [wlp_skip, leq_refl]);

val wlp_if_vc = store_thm
  ("wlp_if_vc",
   ``!pre1 pre2 post b c1 c2.
       Leq pre1 (wlp c1 post) /\ Leq pre2 (wlp c2 post) ==>
       Leq (Cond b pre1 pre2) (wlp (If b c1 c2) post)``,
   RW_TAC std_ss [wlp_if, Leq_def, Cond_def]
   ++ METIS_TAC [le_trans]);

(* ------------------------------------------------------------------------- *)
(* Counter-example:                                                          *)
(* We would like it to be the case that                                      *)
(* !prog. (wp prog One = One) ==> (!postE. wp prog postE = wlp prog postE)   *)
(* 									     *)
(* For the loop below, wp loop One = One				     *)
(* but wp loop [x = 0] = One and                                             *)
(*    wlp loop [x = 0] = (\s. if s x = 0 then 1 else infty)                  *)
(* ------------------------------------------------------------------------- *)

val Counterexample_to_wp_one_eq_one_imp_wlp_eq_wp = store_thm
  ("Counterexample_to_wp_one_eq_one_imp_wlp_eq_wp",
   ``(\s. if s x = 0 then 1 else infty) =
     wlp (While (\s. ~((s x) = 0))
      	        (ProbAssign x [(0:int);1]))
         (bool_exp (\s. s x = 0))``,
   RW_TAC std_ss [bool_exp_def, wp_def, wlp_def, cond_eta, ProbAssign_def, Probs_def, MAP, LENGTH, assign_eta]
   ++ `(\v:int state.
       (1 :posreal) / (2 :posreal) /
       ((1 :posreal) - (1 :posreal) / (2 :posreal))) =
       (\v:int state. (1 :posreal))`
			by (RW_TAC posreal_ss [FUN_EQ_THM, sub_ratr, div_rat, preal_div_def]
			    ++ MATCH_MP_TAC mul_linv
			    ++ RW_TAC posreal_ss [])
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM (K ALL_TAC)
   ++ `!(a:posreal) x y z. (let x = a in x * y + (1 - x) * z) = a * y + (1 - a) * z` by RW_TAC std_ss []
   ++ RW_TAC posreal_ss [lin_eta]
   ++ `(1:posreal) - 1 / 2 = 1 / 2` by RW_TAC posreal_ss [sub_ratr]
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM (K ALL_TAC)
   ++ `monotonic (expect, Leq) 
	         (\e s. (if ~(s x = 0) then
              		   1 / 2 * e (\w. (if w = x then 0 else s w)) +
              		   1 / 2 * e (\w. (if w = x then 1 else s w))
           	         else 1))`
	by (RW_TAC std_ss [monotonic_def, Leq_def]
	    ++ Cases_on `s x = 0`
	    >> METIS_TAC [le_refl]
	    ++ Q.ABBREV_TAC `w0 = (\w. (if w = x then 0 else s w))`
	    ++ Q.ABBREV_TAC `w1 = (\w. (if w = x then 1 else s w))`
	    ++ ASM_REWRITE_TAC []
	    ++ `1 / 2 * e w0 + 1 / 2 * e w1 =
		1 / 2 * (e w0 + e w1)`
		by METIS_TAC [add_ldistrib]
	    ++ ASM_REWRITE_TAC []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ `1 / 2 * e' w0 + 1 / 2 * e' w1 =
		1 / 2 * (e' w0 + e' w1)`
		by METIS_TAC [add_ldistrib]
	    ++ ASM_REWRITE_TAC []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ MATCH_MP_TAC le_lmul_imp
	    ++ MATCH_MP_TAC le_add2
	    ++ METIS_TAC [])
   ++ `gfp (expect, Leq)
	   (\e s. (if ~(s x = 0) then
              	      1 / 2 * e (\w. (if w = x then 0 else s w)) +
              	      1 / 2 * e (\w. (if w = x then 1 else s w))
           	   else 1))
	   (\s. if s x = 0 then 1 else infty)`
	by (RW_TAC int_ss [gfp_def, expect_def]
	    >> (`1 / 2 * infty = infty`
				by RW_TAC posreal_ss [mul_rinfty_rat, posreal_of_num_def]
		++ RW_TAC posreal_ss [mul_rinfty, FUN_EQ_THM]
		++ Cases_on `s x = 0`
		++ RW_TAC posreal_ss [])
	    ++ FULL_SIMP_TAC std_ss [Leq_def]
	    ++ GEN_TAC
	    ++ Cases_on `s x = 0`
	    >> METIS_TAC []
	    ++ RW_TAC posreal_ss [le_infty])
   ++ MATCH_MP_TAC monotonic_and_gfp_imp_eq_expect_gfp
   ++ METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* Add proof that wp loop One = One and wp loop [x = 0] = One  ?????         *)
(* ------------------------------------------------------------------------- *)

val _ = export_theory();
