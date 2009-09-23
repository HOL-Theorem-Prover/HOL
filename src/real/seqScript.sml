(*===========================================================================*)
(* Theory of sequences and series of real numbers                            *)
(*===========================================================================*)

(*
*)
structure seqScript =
struct

(*
app load ["hol88Lib",
          "numLib",
          "reduceLib",
          "PairedLambda",
          "jrhUtils",
          "netsTheory"];
*)


open HolKernel Parse boolLib hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory prim_recTheory
     jrhUtils realTheory topologyTheory netsTheory BasicProvers;

infix THEN THENL ORELSE ORELSEC ##;

val _ = new_theory "seq";

val num_EQ_CONV = Arithconv.NEQ_CONV;

val _ = add_implicit_rewrites pairTheory.pair_rws;

(*---------------------------------------------------------------------------*)
(* Specialize net theorems to sequences:num->real                            *)
(*---------------------------------------------------------------------------*)

val geq = Term `$>= : num->num->bool`;

val _ = hide "-->";  (* hide previous definition in quotient library *)

val tends_num_real = new_infixr_definition("tends_num_real",
  (--`$--> x x0 = (x tends x0)(mtop(mr1), ^geq)`--),750);

val SEQ = store_thm("SEQ",
  (--`!x x0.
      (x --> x0) =
      !e. &0 < e
          ==> ?N. !n. n >= N ==> abs(x(n) - x0) < e`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real, SEQ_TENDS, MR1_DEF] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)  [ABS_SUB]
  THEN REFL_TAC);

val SEQ_CONST = store_thm("SEQ_CONST",
  (--`!k. (\x. k) --> k`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[SEQ, REAL_SUB_REFL, ABS_0] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);

val SEQ_ADD = store_thm("SEQ_ADD",
  (--`!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) + y(n)) --> (x0 + y0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_ADD THEN MATCH_ACCEPT_TAC DORDER_NGE);

val SEQ_MUL = store_thm("SEQ_MUL",
  (--`!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) * y(n)) --> (x0 * y0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_MUL THEN MATCH_ACCEPT_TAC DORDER_NGE);

val SEQ_NEG = store_thm("SEQ_NEG",
  (--`!x x0. x --> x0 = (\n. ~(x n)) --> ~x0`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_NEG THEN MATCH_ACCEPT_TAC DORDER_NGE);

val SEQ_INV = store_thm("SEQ_INV",
  (--`!x x0. x --> x0 /\ ~(x0 = &0) ==> (\n. inv(x n)) --> inv x0`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_INV THEN MATCH_ACCEPT_TAC DORDER_NGE);

val SEQ_SUB = store_thm("SEQ_SUB",
  (--`!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) - y(n)) --> (x0 - y0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_SUB THEN MATCH_ACCEPT_TAC DORDER_NGE);

val SEQ_DIV = store_thm("SEQ_DIV",
  (--`!x x0 y y0. x --> x0 /\ y --> y0 /\ ~(y0 = &0) ==>
                  (\n. x(n) / y(n)) --> (x0 / y0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC NET_DIV THEN MATCH_ACCEPT_TAC DORDER_NGE);

val SEQ_UNIQ = store_thm("SEQ_UNIQ",
  (--`!x x1 x2. x --> x1 /\ x --> x2 ==> (x1 = x2)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
  MATCH_ACCEPT_TAC DORDER_NGE);

(*---------------------------------------------------------------------------*)
(* Define convergence and Cauchy-ness                                        *)
(*---------------------------------------------------------------------------*)

val convergent = new_definition("convergent",
  (--`convergent f = ?l. f --> l`--));

val cauchy = new_definition("cauchy",
  (--`cauchy f = !e. &0 < e ==>
        ?N:num. !m n. m >= N /\ n >= N ==> abs(f(m) - f(n)) < e`--));

val lim = new_definition("lim",
  (--`lim f = @l. f --> l`--));

val SEQ_LIM = store_thm("SEQ_LIM",
  (--`!f. convergent f = (f --> lim f)`--),
  GEN_TAC THEN REWRITE_TAC[convergent] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[lim],
    DISCH_TAC THEN EXISTS_TAC (--`lim f`--) THEN POP_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Define a subsequence                                                      *)
(*---------------------------------------------------------------------------*)

val subseq = new_definition("subseq",
  (--`subseq f = !m n:num. m < n ==> f m < (f n):num`--));

val SUBSEQ_SUC = store_thm("SUBSEQ_SUC",
  (--`!f. subseq f = !n. f(n) < f(SUC n)`--),
  GEN_TAC THEN REWRITE_TAC[subseq] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC (--`n:num`--) THEN POP_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LESS_SUC_REFL],
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC[GSYM ADD1] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`p:num`--) SUBST1_TAC) THEN
    SPEC_TAC((--`p:num`--),(--`p:num`--)) THEN INDUCT_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`f(m + (SUC p)):num`--)] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES]]);

(*---------------------------------------------------------------------------*)
(* Define monotonicity                                                       *)
(*---------------------------------------------------------------------------*)

val mono = new_definition("mono",
  (--`mono f = (!m n:num. m <= n ==> f(m) <= (f n:real))
               \/
               (!m n. m <= n ==> f(m) >= f(n))`--));

val MONO_SUC = store_thm("MONO_SUC",
 (--`!f:num->real.
         mono f
           =
         (!n. f(SUC n) >= f n) \/ (!n. f(SUC n) <= f(n))`--),
GEN_TAC THEN REWRITE_TAC[mono, real_ge] THEN
 MATCH_MP_TAC(TAUT_CONV (--`(a = c) /\ (b = d) ==> (a \/ b = c \/ d)`--))
  THEN CONJ_TAC THEN (EQ_TAC THENL
    [DISCH_THEN(MP_TAC o GEN (--`n:num`--) o
                SPECL [(--`n:num`--), (--`SUC n`--)]) THEN
     REWRITE_TAC[LESS_EQ_SUC_REFL],
     DISCH_TAC THEN REPEAT GEN_TAC THEN
     DISCH_THEN(X_CHOOSE_THEN (--`p:num`--) SUBST1_TAC
                o MATCH_MP LESS_EQUAL_ADD) THEN
     SPEC_TAC((--`p:num`--),(--`p:num`--)) THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[ADD_CLAUSES, REAL_LE_REFL] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`f(m + p:num):real`--) THEN
     ASM_REWRITE_TAC[]]));

(*---------------------------------------------------------------------------*)
(* Simpler characterization of bounded sequence                              *)
(*---------------------------------------------------------------------------*)

val MAX_LEMMA = store_thm("MAX_LEMMA",
  (--`!s N. ?k. !n:num. n < N ==> abs(s n) < k`--),
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THEN
  POP_ASSUM(X_CHOOSE_TAC (--`k:real`--)) THEN
  DISJ_CASES_TAC (SPECL [(--`k:real`--), (--`abs(s(N:num))`--)] REAL_LET_TOTAL) THENL
   [EXISTS_TAC (--`abs(s(N:num)) + &1`--), EXISTS_TAC (--`k:real`--)] THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[LESS_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LT_ADD1) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LT_ADD1 THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`k:real`--) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_REWRITE_TAC[]);

val SEQ_BOUNDED = store_thm("SEQ_BOUNDED",
  (--`!s. bounded(mr1, ^geq) s = ?k. !n. abs(s n) < k`--),
  GEN_TAC THEN REWRITE_TAC[MR1_BOUNDED] THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN (--`k:real`--) (X_CHOOSE_TAC (--`N:num`--))) THEN
    MP_TAC(SPECL [(--`s:num->real`--), (--`N:num`--)] MAX_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_TAC (--`l:real`--)) THEN
    DISJ_CASES_TAC (SPECL [(--`k:real`--), (--`l:real`--)] REAL_LE_TOTAL) THENL
     [EXISTS_TAC (--`l:real`--), EXISTS_TAC (--`k:real`--)] THEN
    X_GEN_TAC (--`n:num`--) THEN MP_TAC(SPECL [(--`n:num`--), (--`N:num`--)] LESS_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN(ANTE_RES_THEN ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    FIRST_ASSUM(fn th => EXISTS_TAC(rand(concl th)) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC),
    DISCH_THEN(X_CHOOSE_TAC (--`k:real`--)) THEN
    MAP_EVERY EXISTS_TAC [(--`k:real`--), (--`0:num`--)] THEN
    GEN_TAC THEN ASM_REWRITE_TAC[]]);

val SEQ_BOUNDED_2 = store_thm("SEQ_BOUNDED_2",
  (--`!f k k'. (!n. k <= f(n) /\ f(n) <= k') ==> bounded(mr1, ^geq) f`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEQ_BOUNDED] THEN
  EXISTS_TAC (--`(abs(k) + abs(k')) + &1`--) THEN GEN_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(k) + abs(k')`--) THEN
  REWRITE_TAC[REAL_LT_ADDR, REAL_LT_01] THEN
  GEN_REWR_TAC LAND_CONV  [abs] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(k')`--) THEN
    REWRITE_TAC[REAL_LE_ADDL, ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`k':real`--) THEN
    ASM_REWRITE_TAC[ABS_LE],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(k)`--) THEN
    REWRITE_TAC[REAL_LE_ADDR, ABS_POS] THEN
    REWRITE_TAC[abs] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG] THEN
    SUBGOAL_THEN (--`&0 <= f(n:num)`--) MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`k:real`--) THEN ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[]]]);

(*---------------------------------------------------------------------------*)
(* Show that every Cauchy sequence is bounded                                *)
(*---------------------------------------------------------------------------*)

val SEQ_CBOUNDED = store_thm("SEQ_CBOUNDED",
  (--`!f. cauchy f ==> bounded(mr1, ^geq) f`--),
  GEN_TAC THEN REWRITE_TAC[bounded, cauchy] THEN
  DISCH_THEN(MP_TAC o SPEC (--`&1`--)) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN
  MAP_EVERY EXISTS_TAC [(--`&1`--), (--`(f:num->real) N`--), (--`N:num`--)] THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  POP_ASSUM(MP_TAC o SPEC (--`N:num`--)) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL, MR1_DEF]);

(*---------------------------------------------------------------------------*)
(* Show that a bounded and monotonic sequence converges                      *)
(*---------------------------------------------------------------------------*)

val SEQ_ICONV = store_thm("SEQ_ICONV",
 (--`!f. bounded(mr1, ^geq) f /\ (!m n:num. m >= n ==> f(m) >= f(n))
           ==> convergent f`--),
GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC (--`\x:real. ?n:num. x = f(n)`--) REAL_SUP) THEN BETA_TAC THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [(--`f(0:num):real`--), (--`0:num`--)] THEN REFL_TAC,
      POP_ASSUM(MP_TAC o REWRITE_RULE[SEQ_BOUNDED] o CONJUNCT1) THEN
      DISCH_THEN(X_CHOOSE_TAC (--`k:real`--)) THEN
      EXISTS_TAC (--`k:real`--) THEN
      GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) SUBST1_TAC) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(f(n:num))`--) THEN
      ASM_REWRITE_TAC[ABS_LE]], ALL_TAC] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_TAC THEN
  REWRITE_TAC[convergent] THEN EXISTS_TAC (--`sup(\x. ?n:num. x = f(n))`--) THEN
  REWRITE_TAC[SEQ] THEN X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o assert(is_forall o concl)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`sup(\x. ?n:num. x = f(n)) - e`--)) THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) MP_TAC) THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN (--`n:num`--) SUBST1_TAC)) THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[GSYM REAL_LT_SUB_RADD] THEN
  DISCH_TAC THEN SUBGOAL_THEN (--`!n. f(n) <= sup(\x. ?n:num. x = f(n))`--)
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC (--`sup(\x. ?n:num. x = f(n))`--)) THEN
    REWRITE_TAC[REAL_LT_REFL] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
    REWRITE_TAC[TAUT_CONV (--`~(a /\ b) = a ==> ~b`--)] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN
    CONV_TAC(ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
    DISCH_THEN(MP_TAC o GEN (--`n:num`--) o SPECL [(--`(f:num->real) n`--), (--`n:num`--)]) THEN
    REWRITE_TAC[], ALL_TAC] THEN
  EXISTS_TAC (--`n:num`--) THEN X_GEN_TAC (--`m:num`--) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_SUB_RADD]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_LT_SUB_RADD]) THEN
  REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(sup(\x. ?m:num. x = f(m)) - e) < f(m)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`(f:num->real) n`--) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[abs] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_NEG_SUB] THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`&0`--) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
    (SUBST1_TAC o REWRITE_RULE[REAL_ADD_RINV] o C SPECL REAL_LE_RADD)
      [(--`(f:num->real) m`--), (--`(sup(\x. ?n:num. x = f(n)))`--),
       (--`~(sup(\x. ?n:num. x = f(n)))`--)] THEN
    ASM_REWRITE_TAC[],
    REWRITE_TAC[REAL_LT_SUB_RADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[GSYM REAL_LT_SUB_RADD] THEN ASM_REWRITE_TAC[]]);

val SEQ_NEG_CONV = store_thm("SEQ_NEG_CONV",
  (--`!f. convergent f = convergent (\n. ~(f n))`--),
  GEN_TAC THEN REWRITE_TAC[convergent] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC (--`l:real`--)) THEN
  EXISTS_TAC (--`~l`--) THEN POP_ASSUM MP_TAC THEN
  SUBST1_TAC(SYM(SPEC (--`l:real`--) REAL_NEGNEG)) THEN
  REWRITE_TAC[GSYM SEQ_NEG] THEN REWRITE_TAC[REAL_NEGNEG]);

val SEQ_NEG_BOUNDED = store_thm("SEQ_NEG_BOUNDED",
  (--`!f. bounded(mr1, ^geq)(\n. ~(f n)) = bounded(mr1, ^geq) f`--),
  GEN_TAC THEN REWRITE_TAC[SEQ_BOUNDED] THEN BETA_TAC THEN
  REWRITE_TAC[ABS_NEG]);

val SEQ_BCONV = store_thm("SEQ_BCONV",
  (--`!f. bounded(mr1, ^geq) f /\ mono f ==> convergent f`--),
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[mono] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [MATCH_MP_TAC SEQ_ICONV THEN ASM_REWRITE_TAC[GREATER_EQ, real_ge],
    ONCE_REWRITE_TAC[SEQ_NEG_CONV] THEN MATCH_MP_TAC SEQ_ICONV THEN
    ASM_REWRITE_TAC[SEQ_NEG_BOUNDED] THEN BETA_TAC THEN
    REWRITE_TAC[GREATER_EQ, real_ge, REAL_LE_NEG] THEN
    ONCE_REWRITE_TAC[GSYM real_ge] THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Show that every sequence contains a monotonic subsequence                 *)
(*---------------------------------------------------------------------------*)

val SEQ_MONOSUB = store_thm("SEQ_MONOSUB",
  (--`!s:num->real. ?f. subseq f /\ mono(\n. s(f n))`--),
  GEN_TAC THEN
  ASM_CASES_TAC (--`!n. ?p:num. p>n /\ !m. m >= p ==> s(m) <= s(p)`--) THENL
  [(X_CHOOSE_THEN (--`f:num->num`--) MP_TAC o EXISTENCE o
    C ISPECL num_Axiom_old)
     [(--`@p:num. p>0 /\ (!m. m >= p ==> (s m) <= (s p))`--),
      (--`\x. \n:num. @p:num. p > x /\ (!m. m >= p ==> (s m) <= (s p))`--)] THEN
    BETA_TAC THEN RULE_ASSUM_TAC
    (GEN (--`n:num`--) o SELECT_RULE o SPEC (--`n:num`--)) THEN
    POP_ASSUM(fn th => DISCH_THEN(ASSUME_TAC o GSYM) THEN
        MP_TAC(SPEC (--`0:num`--) th) THEN
        MP_TAC(GEN (--`n:num`--) (SPEC (--`(f:num->num) n`--) th))) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC (--`f:num->num`--) THEN ASM_REWRITE_TAC[SUBSEQ_SUC, GSYM GREATER_DEF] THEN
    SUBGOAL_THEN (--`!(p:num) q. p >= (f q) ==> s(p) <= s(f(q:num))`--) MP_TAC THENL
     [REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC (--`q:num`--) num_CASES) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN (--`q:num`--) o SPECL [(--`f(SUC q):num`--), (--`q:num`--)]) THEN
    SUBGOAL_THEN (--`!q. f(SUC q) >= f(q):num`--) (fn th => REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GREATER_EQ] THEN MATCH_MP_TAC LESS_IMP_LESS_OR_EQ
      THEN ASM_REWRITE_TAC[GSYM GREATER_DEF], ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[MONO_SUC] THEN DISJ2_TAC THEN
    BETA_TAC THEN ASM_REWRITE_TAC[],
    POP_ASSUM(X_CHOOSE_TAC (--`N:num`--) o CONV_RULE NOT_FORALL_CONV) THEN
    POP_ASSUM(MP_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    REWRITE_TAC[TAUT_CONV (--`~(a /\ b) = a ==> ~b`--)] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
    REWRITE_TAC[NOT_IMP, REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN (--`!p. p >= SUC N ==> (?m. m > p /\ s(p) < s(m))`--)
    MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[GREATER_EQ, GSYM LESS_EQ] THEN
      REWRITE_TAC[GSYM GREATER_DEF] THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC[GREATER_EQ, LESS_OR_EQ, RIGHT_AND_OVER_OR, GREATER_DEF] THEN
      DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) DISJ_CASES_TAC) THENL
       [EXISTS_TAC (--`m:num`--) THEN ASM_REWRITE_TAC[],
        FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[REAL_LT_REFL]], ALL_TAC] THEN
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    (X_CHOOSE_THEN (--`f:num->num`--) MP_TAC o EXISTENCE o
     C ISPECL num_Axiom_old)
     [(--`@m. m > SUC N /\ s(SUC N) < s(m)`--),
      (--`\x:num. \n:num. @m. m > x /\ s(x) < s(m)`--)] THEN
    BETA_TAC THEN DISCH_THEN ASSUME_TAC THEN SUBGOAL_THEN
      (--`!n. f(n) >= SUC N /\
           f(SUC n) > f(n) /\ s(f n) < s(f(SUC n))`--) MP_TAC THENL
     [INDUCT_TAC THENL
       [SUBGOAL_THEN (--`f(0:num) >= SUC N`--) MP_TAC THENL
         [FIRST_ASSUM(MP_TAC o SPEC (--`SUC N`--)) THEN
          REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
          DISCH_THEN(MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
          MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN
          ASM_REWRITE_TAC[GSYM GREATER_DEF], ALL_TAC] THEN
        DISCH_THEN(fn th => ASSUME_TAC th THEN REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fn th => REWRITE_TAC[CONJUNCT2 th]) THEN
        CONV_TAC SELECT_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM(UNDISCH_TAC o
          assert(curry op =3 o length o strip_conj) o concl) THEN
        DISCH_THEN STRIP_ASSUME_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[GREATER_EQ] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
          EXISTS_TAC (--`(f:num->num) n`--) THEN REWRITE_TAC[GSYM GREATER_EQ] THEN
          CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
          REWRITE_TAC[GREATER_EQ] THEN MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN
          REWRITE_TAC[GSYM GREATER_DEF] THEN FIRST_ASSUM ACCEPT_TAC,
          FIRST_ASSUM(SUBST1_TAC o SPEC (--`SUC n`--) o CONJUNCT2) THEN
          CONV_TAC SELECT_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[GREATER_EQ] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
          EXISTS_TAC (--`(f:num->num) n`--) THEN
          REWRITE_TAC[GSYM GREATER_EQ] THEN CONJ_TAC THEN
          TRY(FIRST_ASSUM ACCEPT_TAC) THEN
          REWRITE_TAC[GREATER_EQ] THEN MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN
          REWRITE_TAC[GSYM GREATER_DEF] THEN
          FIRST_ASSUM ACCEPT_TAC]], ALL_TAC] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    EXISTS_TAC (--`f:num->num`--) THEN REWRITE_TAC[SUBSEQ_SUC, MONO_SUC] THEN
    ASM_REWRITE_TAC[GSYM GREATER_DEF] THEN DISJ1_TAC THEN BETA_TAC THEN
    GEN_TAC THEN REWRITE_TAC[real_ge] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Show that a subsequence of a bounded sequence is bounded                  *)
(*---------------------------------------------------------------------------*)

val SEQ_SBOUNDED = store_thm("SEQ_SBOUNDED",
  (--`!s f. bounded(mr1,^geq) s ==> bounded(mr1,^geq) (\n. s(f n))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[SEQ_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_TAC (--`k:real`--)) THEN EXISTS_TAC (--`k:real`--) THEN
  GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Show we can take subsequential terms arbitrarily far up a sequence        *)
(*---------------------------------------------------------------------------*)

val SEQ_SUBLE = store_thm("SEQ_SUBLE",
  (--`!f. subseq f ==> !n. n <= f(n)`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[GSYM NOT_LESS, NOT_LESS_0],
    MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`SUC(f(n:num))`--) THEN
    ASM_REWRITE_TAC[LESS_EQ_MONO] THEN REWRITE_TAC[GSYM LESS_EQ] THEN
    UNDISCH_TAC (--`subseq f`--) THEN REWRITE_TAC[SUBSEQ_SUC] THEN
    DISCH_THEN MATCH_ACCEPT_TAC]);

val SEQ_DIRECT = store_thm("SEQ_DIRECT",
  (--`!f. subseq f ==> !N1 N2. ?n. n >= N1 /\ f(n) >= N2`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [(--`N1:num`--), (--`N2:num`--)] LESS_EQ_CASES) THENL
   [EXISTS_TAC (--`N2:num`--) THEN ASM_REWRITE_TAC[GREATER_EQ] THEN
    MATCH_MP_TAC SEQ_SUBLE THEN FIRST_ASSUM ACCEPT_TAC,
    EXISTS_TAC (--`N1:num`--) THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
    REWRITE_TAC[GREATER_EQ] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC (--`N1:num`--) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SEQ_SUBLE THEN FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Now show that every Cauchy sequence converges                             *)
(*---------------------------------------------------------------------------*)

val SEQ_CAUCHY = store_thm("SEQ_CAUCHY",
  (--`!f. cauchy f = convergent f`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEQ_CBOUNDED) THEN
    MP_TAC(SPEC (--`f:num->real`--) SEQ_MONOSUB) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`g:num->num`--) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (--`bounded(mr1, ^geq)(\n. f(g(n):num))`--) ASSUME_TAC THENL
     [MATCH_MP_TAC SEQ_SBOUNDED THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    SUBGOAL_THEN (--`convergent (\n. f(g(n):num))`--) MP_TAC THENL
     [MATCH_MP_TAC SEQ_BCONV THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[convergent] THEN DISCH_THEN(X_CHOOSE_TAC (--`l:real`--)) THEN
    EXISTS_TAC (--`l:real`--) THEN REWRITE_TAC[SEQ] THEN
    X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
    UNDISCH_TAC (--`(\n. f(g(n):num)) --> l`--) THEN REWRITE_TAC[SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC (--`e / &2`--)) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_TAC (--`N1:num`--)) THEN
    UNDISCH_TAC (--`cauchy f`--) THEN REWRITE_TAC[cauchy] THEN
    DISCH_THEN(MP_TAC o SPEC (--`e / &2`--)) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N2:num`--) ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SEQ_DIRECT) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`N1:num`--), (--`N2:num`--)]) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`N2:num`--) THEN X_GEN_TAC (--`m:num`--) THEN DISCH_TAC THEN
    UNDISCH_TAC (--`!n:num. n >= N1 ==> abs(f(g n:num) - l) < (e / &2)`--) THEN
    DISCH_THEN(MP_TAC o SPEC (--`n:num`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`g(n:num):num`--), (--`m:num`--)]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    SUBGOAL_THEN (--`f(m:num) - l = (f(m) - f(g(n:num))) + (f(g n) - l)`--)
    SUBST1_TAC THENL [REWRITE_TAC[REAL_SUB_TRIANGLE], ALL_TAC] THEN
    EXISTS_TAC (--`abs(f(m:num) - f(g(n:num))) + abs(f(g n) - l)`--) THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    SUBST1_TAC(SYM(SPEC (--`e:real`--) REAL_HALF_DOUBLE)) THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[],

    REWRITE_TAC[convergent] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) MP_TAC) THEN
    REWRITE_TAC[SEQ, cauchy] THEN DISCH_TAC THEN
    X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC (--`e / &2`--)) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN
    EXISTS_TAC (--`N:num`--) THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    SUBGOAL_THEN (--`f(m:num) - f(n) = (f(m) - l) + (l - f(n))`--)
    SUBST1_TAC THENL [REWRITE_TAC[REAL_SUB_TRIANGLE], ALL_TAC] THEN
    EXISTS_TAC (--`abs(f(m:num) - l) + abs(l - f(n))`--) THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    SUBST1_TAC(SYM(SPEC (--`e:real`--) REAL_HALF_DOUBLE)) THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* The limit comparison property for sequences                               *)
(*---------------------------------------------------------------------------*)

val SEQ_LE = store_thm("SEQ_LE",
  (--`!f g l m. f --> l /\ g --> m /\ (?N. !n. n >= N ==> f(n) <= g(n))
        ==> l <= m`--),
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC geq NET_LE) THEN
  REWRITE_TAC[DORDER_NGE, tends_num_real, GREATER_EQ, LESS_EQ_REFL] THEN
  DISCH_THEN MATCH_ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* We can displace a convergent series by 1                                  *)
(*---------------------------------------------------------------------------*)

val SEQ_SUC = store_thm("SEQ_SUC",
  (--`!f l. f --> l = (\n. f(SUC n)) --> l`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[SEQ, GREATER_EQ] THEN EQ_TAC THEN
  DISCH_THEN(fn th => X_GEN_TAC (--`e:real`--) THEN
    DISCH_THEN(MP_TAC o MATCH_MP th)) THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THENL
   [EXISTS_TAC (--`N:num`--) THEN X_GEN_TAC (--`n:num`--) THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC (--`SUC N`--) THEN ASM_REWRITE_TAC[LESS_EQ_MONO, LESS_EQ_SUC_REFL],
    EXISTS_TAC (--`SUC N`--) THEN X_GEN_TAC (--`n:num`--) THEN
    STRUCT_CASES_TAC (SPEC (--`n:num`--) num_CASES) THENL
     [REWRITE_TAC[GSYM NOT_LESS, LESS_0],
      REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);

(*---------------------------------------------------------------------------*)
(* Prove a sequence tends to zero iff its abs does                           *)
(*---------------------------------------------------------------------------*)

val SEQ_ABS = store_thm("SEQ_ABS",
  (--`!f. (\n. abs(f n)) --> &0 = f --> &0`--),
  GEN_TAC THEN REWRITE_TAC[SEQ] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO, ABS_ABS]);

(*---------------------------------------------------------------------------*)
(* Half this is true for a general limit                                     *)
(*---------------------------------------------------------------------------*)

val SEQ_ABS_IMP = store_thm("SEQ_ABS_IMP",
  (--`!f l. f --> l ==> (\n. abs(f n)) --> abs(l)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_num_real] THEN
  MATCH_ACCEPT_TAC NET_ABS);

(*---------------------------------------------------------------------------*)
(* Prove that an unbounded sequence's inverse tends to 0                     *)
(*---------------------------------------------------------------------------*)

val SEQ_INV0 = store_thm("SEQ_INV0",
  (--`!f. (!y. ?N. !n. n >= N ==> f(n) > y)
               ==>
          (\n. inv(f n)) --> &0`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEQ, REAL_SUB_RZERO] THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC (--`N:num`--) o SPEC (--`inv e`--)) THEN
  EXISTS_TAC (--`N:num`--) THEN X_GEN_TAC (--`n:num`--) THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN ANTE_RES_THEN MP_TAC th) THEN
  REWRITE_TAC[real_gt] THEN BETA_TAC THEN IMP_RES_TAC REAL_INV_POS THEN
  SUBGOAL_THEN (--`&0 < f(n:num)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`inv e`--) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM real_gt] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`&0 < inv(f(n:num))`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`~(f(n:num) = &0)`--) ASSUME_TAC THENL
   [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
  SUBGOAL_THEN (--`e = inv(inv e)`--) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`(f:num->real) n`--) THEN
  ASM_REWRITE_TAC[ABS_LE]);

(*---------------------------------------------------------------------------*)
(* Important limit of c^n for |c| < 1                                        *)
(*---------------------------------------------------------------------------*)

val SEQ_POWER_ABS = store_thm("SEQ_POWER_ABS",
  (--`!c. abs(c) < &1 ==> (\n. abs(c) pow n) --> &0`--),
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC (--`c:real`--) ABS_POS) THEN
  REWRITE_TAC[REAL_LE_LT] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN (--`!n. abs(c) pow n = inv(inv(abs(c) pow n))`--)
      (fn th => ONCE_REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
      MATCH_MP_TAC POW_NZ THEN
      ASM_REWRITE_TAC[ABS_NZ, ABS_ABS], ALL_TAC] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:num`--) (--`inv(abs(c) pow n)`--)]) THEN
    MATCH_MP_TAC SEQ_INV0 THEN BETA_TAC THEN X_GEN_TAC (--`y:real`--) THEN
    SUBGOAL_THEN (--`~(abs(c) = &0)`--) (fn th => REWRITE_TAC[MATCH_MP POW_INV th]) THENL
     [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN REWRITE_TAC[real_gt] THEN
    SUBGOAL_THEN (--`&0 < inv(abs c) - &1`--) ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_SUB_LADD] THEN REWRITE_TAC[REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[GSYM REAL_INV1] THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    MP_TAC(SPEC (--`inv(abs c) - &1`--) REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC (--`N:num`--) o SPEC (--`y:real`--)) THEN
    EXISTS_TAC (--`N:num`--) THEN X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[GREATER_EQ] THEN
    DISCH_TAC THEN SUBGOAL_THEN (--`y < (&n * (inv(abs c) - &1))`--)
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (--`&N * (inv(abs c) - &1)`--) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fn th => GEN_REWR_TAC I [MATCH_MP REAL_LE_RMUL th]) THEN
      ASM_REWRITE_TAC[REAL_LE], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`&n * (inv(abs c) - &1)`--) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC (--`&1 + (&n * (inv(abs c) - &1))`--) THEN
    REWRITE_TAC[REAL_LT_ADDL, REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`(&1 + (inv(abs c) - &1)) pow n`--) THEN CONJ_TAC THENL
     [MATCH_MP_TAC POW_PLUS1 THEN ASM_REWRITE_TAC[],
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_LE_REFL]],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SEQ] THEN
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (--`1:num`--) THEN
    X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[GREATER_EQ] THEN BETA_TAC THEN
    STRUCT_CASES_TAC(SPEC (--`n:num`--) num_CASES) THENL
     [REWRITE_TAC[GSYM NOT_LESS, ONE, LESS_0],
      REWRITE_TAC[POW_0, REAL_SUB_RZERO, ABS_0] THEN
      REWRITE_TAC[ASSUME (--`&0 < e`--)]]]);

(*---------------------------------------------------------------------------*)
(* Similar version without the abs                                           *)
(*---------------------------------------------------------------------------*)

val SEQ_POWER = store_thm("SEQ_POWER",
  (--`!c. abs(c) < &1 ==> (\n. c pow n) --> &0`--),
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM SEQ_ABS] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM POW_ABS] THEN
  POP_ASSUM(ACCEPT_TAC o MATCH_MP SEQ_POWER_ABS));

(*---------------------------------------------------------------------------*)
(* Useful lemmas about nested intervals and proof by bisection               *)
(*---------------------------------------------------------------------------*)

val NEST_LEMMA = store_thm("NEST_LEMMA",
 (--`!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) ==>
                ?l m. l <= m /\ ((!n. f(n) <= l) /\ f --> l) /\
                                ((!n. m <= g(n)) /\ g --> m)`--),
  REPEAT STRIP_TAC THEN MP_TAC(SPEC (--`f:num->real`--) MONO_SUC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`g:num->real`--) MONO_SUC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN SUBGOAL_THEN (--`bounded(mr1,^geq) f`--) ASSUME_TAC THENL
   [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
    MAP_EVERY EXISTS_TAC [(--`(f:num->real) 0`--), (--`(g:num->real) 0`--)] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(f:num->real) n`--) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`g(SUC n):real`--) THEN
      ASM_REWRITE_TAC[] THEN SPEC_TAC((--`SUC n`--),(--`m:num`--)) THEN
      INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`g(m:num):real`--) THEN
      ASM_REWRITE_TAC[]], ALL_TAC] THEN
  SUBGOAL_THEN (--`bounded(mr1, ^geq) g`--) ASSUME_TAC THENL
   [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
    MAP_EVERY EXISTS_TAC [(--`(f:num->real) 0`--), (--`(g:num->real) 0`--)] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`(f:num->real) (SUC n)`--) THEN
      ASM_REWRITE_TAC[] THEN SPEC_TAC((--`SUC n`--),(--`m:num`--)) THEN
      INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(f:num->real) m`--) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(g:num->real) n`--) THEN
      ASM_REWRITE_TAC[]], ALL_TAC] THEN
  MP_TAC(SPEC (--`f:num->real`--) SEQ_BCONV) THEN ASM_REWRITE_TAC[SEQ_LIM] THEN
  DISCH_TAC THEN MP_TAC(SPEC (--`g:num->real`--) SEQ_BCONV) THEN
  ASM_REWRITE_TAC[SEQ_LIM] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [(--`lim f`--), (--`lim g`--)] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SEQ_LE THEN
    MAP_EVERY EXISTS_TAC [(--`f:num->real`--), (--`g:num->real`--)] THEN
    ASM_REWRITE_TAC[],
    X_GEN_TAC (--`m:num`--) THEN
    GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
    PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC (--`f --> lim f`--) THEN REWRITE_TAC[SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC (--`f(m) - lim f`--)) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`p:num`--) MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC (--`p + m:num`--)) THEN
    REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD] THEN REWRITE_TAC[abs] THEN
    SUBGOAL_THEN (--`!p:num. lim f <= f(p + m)`--) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC,
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (--`f(p + m:num):real`--) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[]],
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_NOT_LT, real_sub, REAL_LE_RADD] THEN
      SPEC_TAC((--`p:num`--),(--`p:num`--)) THEN INDUCT_TAC THEN
      REWRITE_TAC[REAL_LE_REFL, ADD_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`f(p + m:num):real`--) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN ASM_REWRITE_TAC[]],
    X_GEN_TAC (--`m:num`--) THEN
    GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
    PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC (--`g --> lim g`--) THEN REWRITE_TAC[SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC (--`lim g - g(m)`--)) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`p:num`--) MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC (--`p + m:num`--)) THEN
    REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD] THEN REWRITE_TAC[abs] THEN
    SUBGOAL_THEN (--`!p. g(p + m:num) < lim g`--) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (--`g(p + m:num):real`--) THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[REAL_SUB_LE] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_NOT_LT, REAL_NEG_SUB] THEN
      REWRITE_TAC[real_sub, REAL_LE_LADD, REAL_LE_NEG] THEN
      SPEC_TAC((--`p:num`--),(--`p:num`--)) THEN INDUCT_TAC THEN
      REWRITE_TAC[REAL_LE_REFL, ADD_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`g(p + m:num):real`--) THEN
      ASM_REWRITE_TAC[]]]);

val NEST_LEMMA_UNIQ = store_thm("NEST_LEMMA_UNIQ",
  (--`!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) /\
         (\n. f(n) - g(n)) --> &0 ==>
                ?l. ((!n. f(n) <= l) /\ f --> l) /\
                    ((!n. l <= g(n)) /\ g --> l)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NEST_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`m:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`l:real`--) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (--`l:real = m`--) (fn th => ASM_REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [(--`f:num->real`--), (--`l:real`--), (--`g:num->real`--), (--`m:real`--)] SEQ_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ(ASSUME (--`(\n. f(n) - g(n)) --> &0`--))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_UNIQ) THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_SUB_0]);


val BOLZANO_LEMMA = store_thm("BOLZANO_LEMMA",
  (--`!P. (!a b c. a <= b /\ b <= c /\ P(a,b) /\ P(b,c) ==> P(a,c)) /\
       (!x. ?d. &0 < d /\ !a b. a <= x /\ x <= b /\ (b - a) < d ==> P(a,b))
      ==> !a b. a <= b ==> P(a,b)`--),
  REPEAT STRIP_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
  DISCH_TAC THEN
  (X_CHOOSE_THEN (--`f:num->real#real`--) STRIP_ASSUME_TAC o
   EXISTENCE o BETA_RULE o C ISPECL num_Axiom_old)
    [(--`(a:real,(b:real))`--),
     (--`\fn (n:num). if P(FST fn,(FST fn + SND fn) / &2)
                      then ((FST fn + SND fn) / &2,SND fn)
                      else (FST fn,(FST fn + SND fn) / &2)`--)] THEN
  MP_TAC(SPECL
    [(--`\n:num. FST(f(n) :real#real)`--), (--`\n:num. SND(f(n) :real#real)`--)]
    NEST_LEMMA_UNIQ) THEN BETA_TAC THEN
  SUBGOAL_THEN (--`!n:num. FST(f n) <= SND(f n)`--) ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_MIDDLE2, MATCH_MP_TAC REAL_MIDDLE1] THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN REWRITE_TAC[real_ge] THEN
  SUBGOAL_THEN (--`!n:num. FST(f n :real#real) <= FST(f(SUC n))`--)
  ASSUME_TAC THENL
   [REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
    FIRST_ASSUM(fn th => GEN_REWR_TAC (funpow 2 RAND_CONV) [th]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_MIDDLE1 THEN FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~P(FST((f:num->real#real) n),SND(f n))`--) ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC (--`~P(FST((f:num->real#real) n),SND(f n)):bool`--) THEN
    PURE_REWRITE_TAC[IMP_CLAUSES, NOT_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC (--`(FST(f(n:num)) + SND(f(n))) / &2`--) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MIDDLE1, MATCH_MP_TAC REAL_MIDDLE2] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (--`!n:num. SND(f(SUC n) :real#real) <= SND(f n)`--) ASSUME_TAC THENL
   [BETA_TAC THEN INDUCT_TAC THEN
    FIRST_ASSUM(fn th => GEN_REWR_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_MIDDLE2 THEN FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (--`!n:num. SND(f n) - FST(f n) = (b - a) / (&2 pow n)`--)
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[pow, real_div, REAL_INV1, REAL_MUL_RID], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC (--`&2`--) THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    (SUBGOAL_THEN (--`~(&2 = &0)`--) (fn th => REWRITE_TAC[th] THEN
     REWRITE_TAC[MATCH_MP REAL_DIV_LMUL th]) THENL
      [REWRITE_TAC[REAL_INJ] THEN CONV_TAC(RAND_CONV num_EQ_CONV) THEN
       REWRITE_TAC[], ALL_TAC]) THEN
    REWRITE_TAC[GSYM REAL_DOUBLE] THEN
    GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [REAL_ADD_SYM]
    THEN (SUBGOAL_THEN (--`!x y z:real. (x + y) - (x + z) = y - z`--)
            (fn th => REWRITE_TAC[th])
     THENL
      [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD] THEN
       GEN_REWR_TAC RAND_CONV  [GSYM REAL_ADD_RID] THEN
       SUBST1_TAC(SYM(SPEC (--`x:real`--) REAL_ADD_LINV)) THEN
       CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)), ALL_TAC]) THEN
    ASM_REWRITE_TAC[REAL_DOUBLE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[pow] THEN
    (SUBGOAL_THEN (--`~(&2 = &0) /\ ~(&2 pow n = &0)`--)
       (fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THENL
      [CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC POW_NZ] THEN
       REWRITE_TAC[REAL_INJ] THEN
       CONV_TAC(RAND_CONV num_EQ_CONV) THEN REWRITE_TAC[],
       ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
       GEN_REWR_TAC (RATOR_CONV o RAND_CONV)
                        [GSYM REAL_MUL_LID] THEN
       AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_INJ] THEN
       CONV_TAC(RAND_CONV num_EQ_CONV) THEN REWRITE_TAC[]]),
    ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert (can (find_term is_cond)) o concl) THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o fst o dest_imp o rand o snd) THENL
   [ONCE_REWRITE_TAC[SEQ_NEG] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[REAL_NEG_SUB, REAL_NEG_0] THEN
    REWRITE_TAC[real_div] THEN SUBGOAL_THEN (--`~(&2 = &0)`--) ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INJ] THEN CONV_TAC(RAND_CONV num_EQ_CONV) THEN
      REWRITE_TAC[], ALL_TAC] THEN
    (MP_TAC o C SPECL SEQ_MUL)
      [(--`\n:num. b - a`--), (--`b - a`--), (--`\n. (inv (&2 pow n))`--), (--`&0`--)] THEN
    REWRITE_TAC[SEQ_CONST, REAL_MUL_RZERO] THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_INV th]) THEN
    ONCE_REWRITE_TAC[GSYM SEQ_ABS] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM POW_ABS] THEN MATCH_MP_TAC SEQ_POWER_ABS THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
    REWRITE_TAC[ABS_N] THEN SUBGOAL_THEN (--`&0 < &2`--)
    (fn th => ONCE_REWRITE_TAC [GSYM (MATCH_MP REAL_LT_RMUL th)]) THENL
     [REWRITE_TAC[REAL_LT, num_CONV (--`2:num`--), LESS_0], ALL_TAC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[REAL_LT] THEN
    REWRITE_TAC[num_CONV (--`2:num`--), LESS_SUC_REFL],
    DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN (--`d:real`--) MP_TAC o SPEC (--`l:real`--)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    UNDISCH_TAC (--`(\n:num. SND(f n :real#real)) --> l`--) THEN
    UNDISCH_TAC (--`(\n:num. FST(f n :real#real)) --> l`--) THEN
    REWRITE_TAC[SEQ] THEN DISCH_THEN(MP_TAC o SPEC (--`d / &2`--)) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N1:num`--) (ASSUME_TAC o BETA_RULE)) THEN
    DISCH_THEN(MP_TAC o SPEC (--`d / &2`--)) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N2:num`--) (ASSUME_TAC o BETA_RULE)) THEN
    DISCH_THEN(MP_TAC o
      SPECL [(--`FST((f:num->real#real) (N1 + N2))`--),
             (--`SND((f:num->real#real) (N1 + N2))`--)]) THEN
    UNDISCH_TAC (--`!n:num. (SND(f n)) - (FST(f n)) = (b - a) / ((& 2) pow n)`--) THEN
    DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs(FST(f(N1 + N2:num)) - l) +
                abs(SND(f(N1 + N2)) - l)`--) THEN
    GEN_REWR_TAC (funpow 2 RAND_CONV) [GSYM REAL_HALF_DOUBLE] THEN
    CONJ_TAC THENL
     [GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [ABS_SUB]
      THEN ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC] THEN
      REWRITE_TAC[(EQT_ELIM o AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM))
        (--`a + (b + (c + d)) = (d + a) + (c + b)`--)] THEN
      REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID, REAL_LE_REFL],
      MATCH_MP_TAC REAL_LT_ADD2 THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_EQ_ADD]]]);

(*---------------------------------------------------------------------------*)
(* Define infinite sums                                                      *)
(*---------------------------------------------------------------------------*)

val sums = new_infixr_definition("sums",
  (--`$sums f s = (\n. sum(0,n) f) --> s`--),750);

val summable = new_definition("summable",
  (--`summable f = ?s. f sums s`--));

val suminf = new_definition("suminf",
  (--`suminf f = @s. f sums s`--));

(*---------------------------------------------------------------------------*)
(* If summable then it sums to the sum (!)                                   *)
(*---------------------------------------------------------------------------*)

val SUM_SUMMABLE = store_thm("SUM_SUMMABLE",
  (--`!f l. f sums l ==> summable f`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[summable] THEN
  EXISTS_TAC (--`l:real`--) THEN POP_ASSUM ACCEPT_TAC);

val SUMMABLE_SUM = store_thm("SUMMABLE_SUM",
  (--`!f. summable f ==> f sums (suminf f)`--),
  GEN_TAC THEN REWRITE_TAC[summable, suminf] THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  MATCH_ACCEPT_TAC SELECT_AX);

(*---------------------------------------------------------------------------*)
(* And the sum is unique                                                     *)
(*---------------------------------------------------------------------------*)

val SUM_UNIQ = store_thm("SUM_UNIQ",
  (--`!f x. f sums x ==> (x = suminf f)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`summable f`--) MP_TAC THENL
   [REWRITE_TAC[summable] THEN EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(ASSUME_TAC o MATCH_MP SUMMABLE_SUM) THEN
    MATCH_MP_TAC SEQ_UNIQ THEN
    EXISTS_TAC (--`\n. sum(0,n) f`--) THEN ASM_REWRITE_TAC[GSYM sums]]);

(*---------------------------------------------------------------------------*)
(* Series which is zero beyond a certain point                               *)
(*---------------------------------------------------------------------------*)

val SER_0 = store_thm("SER_0",
  (--`!f n. (!m. n <= m ==> (f(m) = &0)) ==>
        f sums (sum(0,n) f)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sums, SEQ] THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN EXISTS_TAC (--`n:num`--) THEN
  X_GEN_TAC (--`m:num`--) THEN REWRITE_TAC[GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
  W(C SUBGOAL_THEN SUBST1_TAC o C (curry mk_eq) (--`&0`--) o rand o rator o snd) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ABS_ZERO, REAL_SUB_0] THEN
  BETA_TAC THEN REWRITE_TAC[GSYM SUM_TWO, REAL_ADD_RID_UNIQ] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[GREATER_EQ] SUM_ZERO)) THEN
  MATCH_ACCEPT_TAC LESS_EQ_REFL);

(*---------------------------------------------------------------------------*)
(* Summable series of positive terms has limit >(=) any partial sum          *)
(*---------------------------------------------------------------------------*)

val SER_POS_LE = store_thm("SER_POS_LE",
  (--`!f n. summable f /\ (!m. n <= m ==> &0 <= f(m))
        ==> sum(0,n) f <= suminf f`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN REWRITE_TAC[sums] THEN
  MP_TAC(SPEC (--`sum(0,n) f`--) SEQ_CONST) THEN
  GEN_REWR_TAC I [TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--)] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT_CONV (--`a /\ b /\ c ==> d = c ==> a /\ b ==> d`--)]
    SEQ_LE) THEN BETA_TAC THEN
  EXISTS_TAC (--`n:num`--) THEN X_GEN_TAC (--`m:num`--) THEN REWRITE_TAC[GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
  REWRITE_TAC[GSYM SUM_TWO, REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val SER_POS_LT = store_thm("SER_POS_LT",
  (--`!f n. summable f /\ (!m. n <= m ==> &0 < f(m))
        ==> sum(0,n) f < suminf f`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`sum(0,n + 1) f`--) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_TWO, REAL_LT_ADDR] THEN
    REWRITE_TAC[ONE, sum, REAL_ADD_LID, ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN MATCH_ACCEPT_TAC LESS_EQ_REFL,
    MATCH_MP_TAC SER_POS_LE THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`SUC n`--) THEN
    REWRITE_TAC[LESS_EQ_SUC_REFL] THEN ASM_REWRITE_TAC[ADD1]]);

(*---------------------------------------------------------------------------*)
(* Theorems about grouping and offsetting (and *not* permuting) terms        *)
(*---------------------------------------------------------------------------*)

val SER_GROUP = store_thm("SER_GROUP",
  (--`!f (k:num). summable f /\ 0 < k ==>
          (\n. sum(n * k,k) f) sums (suminf f)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums, SEQ] THEN BETA_TAC THEN
  DISCH_THEN(fn t => X_GEN_TAC (--`e:real`--) THEN DISCH_THEN(MP_TAC o MATCH_MP t)) THEN
  REWRITE_TAC[GREATER_EQ] THEN DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN
  REWRITE_TAC[SUM_GROUP] THEN EXISTS_TAC (--`N:num`--) THEN
  X_GEN_TAC (--`n:num`--) THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`n:num`--) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC (--`0 < k:num`--) THEN
  STRUCT_CASES_TAC(SPEC (--`k:num`--) num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES, LESS_EQ_ADD, LESS_EQ_0] THEN
  REWRITE_TAC[LESS_REFL]);

val SER_PAIR = store_thm("SER_PAIR",
  (--`!f. summable f ==> (\n. sum(2 * n,2) f) sums (suminf f)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o C CONJ (SPEC (--`1:num`--) LESS_0)) THEN
  REWRITE_TAC[SYM(num_CONV (--`2:num`--))] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_ACCEPT_TAC SER_GROUP);

val SER_OFFSET = store_thm("SER_OFFSET",
  (--`!f. summable f ==> !k. (\n. f(n + k)) sums (suminf f - sum(0,k) f)`--),
  GEN_TAC THEN DISCH_THEN(curry op THEN GEN_TAC o MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums, SEQ] THEN
  DISCH_THEN(fn th => GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  BETA_TAC THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN
  EXISTS_TAC (--`N:num`--) THEN X_GEN_TAC (--`n:num`--) THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_OFFSET] THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (b + d) + (a + c)`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID] THEN REWRITE_TAC[GSYM real_sub] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
  EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC[LESS_EQ_ADD]);

(*---------------------------------------------------------------------------*)
(* Similar version for pairing up terms                                      *)
(*---------------------------------------------------------------------------*)

val SER_POS_LT_PAIR = store_thm("SER_POS_LT_PAIR",
  (--`!f n. summable f /\
         (!d. &0 < (f(n + (2 * d))) + f(n + ((2 * d) + 1)))
        ==> sum(0,n) f < suminf f`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums, SEQ] THEN BETA_TAC THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC (--`f(n:num) + f(n + 1)`--)) THEN
  FIRST_ASSUM(MP_TAC o SPEC (--`0:num`--)) THEN
  REWRITE_TAC[ADD_CLAUSES, MULT_CLAUSES] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:num`--) MP_TAC) THEN
  SUBGOAL_THEN (--`sum(0,n + 2) f <= sum(0,(2 * (SUC N)) + n) f`--)
  ASSUME_TAC THENL
   [SPEC_TAC((--`N:num`--),(--`N:num`--)) THEN INDUCT_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES] THEN
      GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
      MATCH_ACCEPT_TAC REAL_LE_REFL,
      ABBREV_TAC (--`M = SUC N`--) THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      REWRITE_TAC[TWO, ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[ADD_SYM] ADD1)] THEN
      REWRITE_TAC[SYM TWO] THEN REWRITE_TAC[ADD_CLAUSES] THEN
      GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [ADD1] THEN
      (* changed for new term nets.
       old: REWRITE_TAC[GSYM ADD_ASSOC, GSYM ADD1, SYM(num_CONV (--`2`--))] *)
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      REWRITE_TAC [GSYM ADD1, SYM TWO] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`sum(0,(2 * M) + n) f`--) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[sum] THEN
      REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_LE_ADDR] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[ADD1] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      ONCE_REWRITE_TAC[SPEC (--`1:num`--) ADD_SYM] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]],
    DISCH_THEN(MP_TAC o SPEC (--`(2 * SUC N) + n`--)) THEN
    W(C SUBGOAL_THEN (fn th => REWRITE_TAC[th])
                        o funpow 2(fst o dest_imp) o snd)
    THENL
     [REWRITE_TAC[TWO, MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC[AC(ADD_ASSOC,ADD_SYM)
       (--`(a + (b + c)) + d = b + (a + (c + d:num))`--)] THEN
      REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD], ALL_TAC] THEN
    SUBGOAL_THEN (--`suminf f + (f(n:num) + f(n + 1))
                     <= sum(0,(2 * (SUC N)) + n) f`--)
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`sum(0,n + 2) f`--) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`sum(0,n) f + (f(n:num) + f(n + 1))`--) THEN
      ASM_REWRITE_TAC[REAL_LE_RADD] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      CONV_TAC(REDEPTH_CONV num_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES, sum, REAL_ADD_ASSOC], ALL_TAC] THEN
    SUBGOAL_THEN (--`suminf f <= sum(0,(2 * (SUC N)) + n) f`--)
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`suminf f + (f(n:num) + f(n + 1))`--) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_ADDR] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_LT_SUB_RADD] THEN
    GEN_REWR_TAC (funpow 2 RAND_CONV) [REAL_ADD_SYM]
    THEN ASM_REWRITE_TAC[REAL_NOT_LT]]);

(*---------------------------------------------------------------------------*)
(* Prove a few composition formulas for series                               *)
(*---------------------------------------------------------------------------*)

val SER_ADD = store_thm("SER_ADD",
  (--`!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) + y(n)) sums (x0 + y0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[sums, SUM_ADD] THEN
  CONV_TAC((RAND_CONV o EXACT_CONV)[X_BETA_CONV (--`n:num`--) (--`sum(0,n) x`--)]) THEN
  CONV_TAC((RAND_CONV o EXACT_CONV)[X_BETA_CONV (--`n:num`--) (--`sum(0,n) y`--)]) THEN
  MATCH_ACCEPT_TAC SEQ_ADD);

val SER_CMUL = store_thm("SER_CMUL",
  (--`!x x0 c. x sums x0 ==> (\n. c * x(n)) sums (c * x0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[sums, SUM_CMUL] THEN DISCH_TAC THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:num`--) (--`sum(0,n) x`--)]) THEN
  CONV_TAC((RATOR_CONV o EXACT_CONV)[X_BETA_CONV (--`n:num`--) (--`c:real`--)]) THEN
  MATCH_MP_TAC SEQ_MUL THEN ASM_REWRITE_TAC[SEQ_CONST]);

val SER_NEG = store_thm("SER_NEG",
  (--`!x x0. x sums x0 ==> (\n. ~(x n)) sums ~x0`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  MATCH_ACCEPT_TAC SER_CMUL);

val SER_SUB = store_thm("SER_SUB",
  (--`!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) - y(n)) sums (x0 - y0)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(fn th => MP_TAC (MATCH_MP SER_ADD
      (CONJ (CONJUNCT1 th) (MATCH_MP SER_NEG (CONJUNCT2 th))))) THEN
  BETA_TAC THEN REWRITE_TAC[real_sub]);

val SER_CDIV = store_thm("SER_CDIV",
  (--`!x x0 c. x sums x0 ==> (\n. x(n) / c) sums (x0 / c)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC SER_CMUL);

(*---------------------------------------------------------------------------*)
(* Prove Cauchy-type criterion for convergence of series                     *)
(*---------------------------------------------------------------------------*)

val SER_CAUCHY = store_thm("SER_CAUCHY",
  (--`!f. summable f =
          !e. &0 < e ==> ?N. !m n. m >= N ==> abs(sum(m,n) f) < e`--),
  GEN_TAC THEN REWRITE_TAC[summable, sums] THEN
  REWRITE_TAC[GSYM convergent] THEN
  REWRITE_TAC[GSYM SEQ_CAUCHY] THEN REWRITE_TAC[cauchy] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[GREATER_EQ] THEN BETA_TAC THEN
  REWRITE_TAC[TAUT_CONV (--`((a ==> b) = (a ==> c)) = a ==> (b = c)`--)] THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN
  EXISTS_TAC (--`N:num`--) THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC[SUM_DIFF] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`m:num`--) THEN
    ASM_REWRITE_TAC[LESS_EQ_ADD],
    DISJ_CASES_THEN MP_TAC (SPECL [(--`m:num`--), (--`n:num`--)] LESS_EQ_CASES) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`p:num`--) SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THENL
     [ONCE_REWRITE_TAC[ABS_SUB], ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_DIFF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Show that if a series converges, the terms tend to 0                      *)
(*---------------------------------------------------------------------------*)

val SER_ZERO = store_thm("SER_ZERO",
  (--`!f. summable f ==> f --> &0`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEQ] THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
  UNDISCH_TAC (--`summable f`--) THEN REWRITE_TAC[SER_CAUCHY] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:num`--) MP_TAC) THEN
  DISCH_THEN(curry op THEN (EXISTS_TAC (--`N:num`--) THEN X_GEN_TAC (--`n:num`--) THEN DISCH_TAC)
    o MP_TAC) THEN DISCH_THEN(MP_TAC o SPECL [(--`n:num`--), (--`SUC 0`--)]) THEN
  ASM_REWRITE_TAC[sum, REAL_SUB_RZERO, REAL_ADD_LID, ADD_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Now prove the comparison test                                             *)
(*---------------------------------------------------------------------------*)

val SER_COMPAR = store_thm("SER_COMPAR",
  (--`!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable f`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[SER_CAUCHY, GREATER_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`N1:num`--)) MP_TAC) THEN
  REWRITE_TAC[SER_CAUCHY, GREATER_EQ] THEN DISCH_TAC THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`N2:num`--)) THEN EXISTS_TAC (--`N1 + N2:num`--) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`sum(m,n)(\k. abs(f k))`--) THEN REWRITE_TAC[ABS_SUM] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`sum(m,n) g`--) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN BETA_TAC THEN
    X_GEN_TAC (--`p:num`--) THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`m:num`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC (--`N1 + N2:num`--) THEN ASM_REWRITE_TAC[LESS_EQ_ADD], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(sum(m,n) g)`--) THEN
  REWRITE_TAC[ABS_LE] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`N1 + N2:num`--) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[LESS_EQ_ADD]);

(*---------------------------------------------------------------------------*)
(* And a similar version for absolute convergence                            *)
(*---------------------------------------------------------------------------*)

val SER_COMPARA = store_thm("SER_COMPARA",
  (--`!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable (\k. abs(f k))`--),
  REPEAT GEN_TAC THEN SUBGOAL_THEN (--`!n. abs(f(n)) = abs((\k:num. abs(f k)) n)`--)
  (fn th => GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [GEN_TAC THEN BETA_TAC THEN REWRITE_TAC[ABS_ABS],
    MATCH_ACCEPT_TAC SER_COMPAR]);

(*---------------------------------------------------------------------------*)
(* Limit comparison property for series                                      *)
(*---------------------------------------------------------------------------*)

val SER_LE = store_thm("SER_LE",
  (--`!f g. (!n. f(n) <= g(n)) /\ summable f /\ summable g
        ==> suminf f <= suminf g`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (fn th => ASSUME_TAC th THEN ASSUME_TAC
    (REWRITE_RULE[sums] (MATCH_MP SUMMABLE_SUM th)))) THEN
  MATCH_MP_TAC SEQ_LE THEN REWRITE_TAC[CONJ_ASSOC] THEN
  MAP_EVERY EXISTS_TAC [(--`\n. sum(0,n) f`--), (--`\n. sum(0,n) g`--)] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM sums] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUMMABLE_SUM THEN FIRST_ASSUM ACCEPT_TAC,
    EXISTS_TAC (--`0:num`--) THEN REWRITE_TAC[GREATER_EQ, ZERO_LESS_EQ] THEN
    GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_LE THEN
    GEN_TAC THEN ASM_REWRITE_TAC[ZERO_LESS_EQ]]);

val SER_LE2 = store_thm("SER_LE2",
  (--`!f g. (!n. abs(f n) <= g(n)) /\ summable g ==>
                summable f /\ suminf f <= suminf g`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`summable f`--) ASSUME_TAC THENL
   [MATCH_MP_TAC SER_COMPAR THEN EXISTS_TAC (--`g:num->real`--) THEN
    ASM_REWRITE_TAC[], ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SER_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`n:num`--) THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`abs(f(n:num))`--) THEN ASM_REWRITE_TAC[ABS_LE]);

(*---------------------------------------------------------------------------*)
(* Show that absolute convergence implies normal convergence                 *)
(*---------------------------------------------------------------------------*)

val SER_ACONV = store_thm("SER_ACONV",
  (--`!f. summable (\n. abs(f n)) ==> summable f`--),
  GEN_TAC THEN REWRITE_TAC[SER_CAUCHY] THEN REWRITE_TAC[SUM_ABS] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC (--`e:real`--) THEN DISCH_TAC) o MP_TAC) THEN
  DISCH_THEN(IMP_RES_THEN (X_CHOOSE_TAC (--`N:num`--))) THEN
  EXISTS_TAC (--`N:num`--) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`sum(m,n)(\m. abs(f m))`--) THEN ASM_REWRITE_TAC[ABS_SUM]);

(*---------------------------------------------------------------------------*)
(* Absolute value of series                                                  *)
(*---------------------------------------------------------------------------*)

val SER_ABS = store_thm("SER_ABS",
  (--`!f. summable(\n. abs(f n)) ==> abs(suminf f) <= suminf(\n. abs(f n))`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_SUM o MATCH_MP SER_ACONV) THEN
  POP_ASSUM(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  REWRITE_TAC[sums] THEN DISCH_TAC THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP SEQ_ABS_IMP) THEN
  MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
   [(--`\n. abs(sum(0,n)f)`--), (--`\n. sum(0,n)(\n. abs(f n))`--)] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC (--`0:num`--) THEN X_GEN_TAC (--`n:num`--) THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN MATCH_ACCEPT_TAC SUM_ABS_LE);

(*---------------------------------------------------------------------------*)
(* Prove sum of geometric progression (useful for comparison)                *)
(*---------------------------------------------------------------------------*)

val GP_FINITE = store_thm("GP_FINITE",
  (--`!x. ~(x = &1) ==>
        !n. (sum(0,n) (\n. x pow n) = ((x pow n) - &1) / (x - &1))`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[sum, pow, REAL_SUB_REFL, REAL_DIV_LZERO],
    REWRITE_TAC[sum, pow] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN (--`~(x - &1 = &0)`--) ASSUME_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_0] THEN
    MP_TAC(GENL [(--`p:real`--), (--`q:real`--)]
     (SPECL [(--`p:real`--), (--`q:real`--), (--`x - &1`--)] REAL_EQ_RMUL)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN SUBGOAL_THEN
      (--`!p. (p / (x - &1)) * (x - &1) = p`--) (fn th => REWRITE_TAC[th]) THENL
      [GEN_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[], ALL_TAC]
    THEN REWRITE_TAC[REAL_SUB_LDISTRIB] THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      (--`(a + b) + (c + d) = (c + b) + (d + a)`--)] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_ADD_LINV, REAL_ADD_RID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val GP = store_thm("GP",
  (--`!x. abs(x) < &1 ==> (\n. x pow n) sums inv(&1 - x)`--),
  GEN_TAC THEN ASM_CASES_TAC (--`x = &1`--) THEN
  ASM_REWRITE_TAC[ABS_1, REAL_LT_REFL] THEN DISCH_TAC THEN
  REWRITE_TAC[sums] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP GP_FINITE th]) THEN
  REWRITE_TAC[REAL_INV_1OVER] THEN REWRITE_TAC[real_div] THEN
  GEN_REWR_TAC (LAND_CONV o ABS_CONV) [GSYM REAL_NEG_MUL2] THEN
  SUBGOAL_THEN (--`~(x - &1 = &0)`--) (fn t =>REWRITE_TAC[MATCH_MP REAL_NEG_INV t]) THENL
    [ASM_REWRITE_TAC[REAL_SUB_0], ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_SUB, GSYM real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:num`--) (--`&1 - (x pow n)`--)]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:num`--) (--`&1 - x`--)]) THEN
  MATCH_MP_TAC SEQ_DIV THEN BETA_TAC THEN REWRITE_TAC[SEQ_CONST] THEN
  REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_SUB_RZERO]
  THEN CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:num`--) (--`x pow n`--)]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:num`--) (--`&1`--)]) THEN
  MATCH_MP_TAC SEQ_SUB THEN BETA_TAC THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_POWER THEN FIRST_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Now prove the ratio test                                                  *)
(*---------------------------------------------------------------------------*)

val ABS_NEG_LEMMA = store_thm("ABS_NEG_LEMMA",
  (--`!c. c <= &0 ==> !x y. abs(x) <= c * abs(y) ==> (x = &0)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_GE0] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN MP_TAC(SPECL [(--`~c`--), (--`abs(y)`--)] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[ABS_POS, GSYM REAL_NEG_LMUL, REAL_NEG_GE0] THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C CONJ th)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[ABS_NZ, REAL_NOT_LE]);

val SER_RATIO = store_thm("SER_RATIO",
  (--`!f c (N:num).
         c < &1 /\ (!n. n >= N ==> abs(f(SUC n)) <= c * abs(f(n)))
          ==>
        summable f`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISJ_CASES_TAC (SPECL [(--`c:real`--), (--`&0`--)] REAL_LET_TOTAL) THENL
   [REWRITE_TAC[SER_CAUCHY] THEN X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
    SUBGOAL_THEN (--`!n. n >= N ==> (f(SUC n) = &0)`--) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      MATCH_MP_TAC ABS_NEG_LEMMA THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (--`!n. n >= SUC N ==> (f(n) = &0)`--) ASSUME_TAC THENL
     [GEN_TAC THEN STRUCT_CASES_TAC(SPEC (--`n:num`--) num_CASES) THENL
       [REWRITE_TAC[GREATER_EQ] THEN DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
        REWRITE_TAC[NOT_LESS_0],
        REWRITE_TAC[GREATER_EQ, LESS_EQ_MONO] THEN
        ASM_REWRITE_TAC[GSYM GREATER_EQ]], ALL_TAC] THEN
    EXISTS_TAC (--`SUC N`--) THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUM_ZERO) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN (fn th => REWRITE_TAC[th])) THEN
    ASM_REWRITE_TAC[ABS_0],

    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC (--`\n:num. (abs(f N) / c pow N) * (c pow n)`--) THEN
    CONJ_TAC THENL
     [EXISTS_TAC (--`N:num`--) THEN X_GEN_TAC (--`n:num`--) THEN
      REWRITE_TAC[GREATER_EQ] THEN
      DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD)
      THEN BETA_TAC THEN REWRITE_TAC[POW_ADD] THEN REWRITE_TAC[real_div] THEN
      ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
        (--`(a * b) * (c * d) = (a * d) * (b * c)`--)] THEN
      SUBGOAL_THEN (--`~(c pow N = &0)`--)
        (fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th, REAL_MUL_RID]) THENL
       [MATCH_MP_TAC POW_NZ THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      SPEC_TAC((--`d:num`--),(--`d:num`--)) THEN INDUCT_TAC THEN
      REWRITE_TAC[pow, ADD_CLAUSES, REAL_MUL_RID, REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`c * abs(f((N:num) + d))`--) THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD],
        ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          (--`a * (b * c) = b * (a * c)`--)] THEN
        FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th])],

      REWRITE_TAC[summable] THEN
      EXISTS_TAC (--`(abs(f(N:num)) / (c pow N)) * inv(&1 - c)`--) THEN
      MATCH_MP_TAC SER_CMUL THEN
      MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) GP) THEN
      ASSUME_TAC(MATCH_MP REAL_LT_IMP_LE (ASSUME (--`&0 <  c`--))) THEN
      ASM_REWRITE_TAC[abs]]]);

(*---------------------------------------------------------------------------*)
(* Useful lemmas for proving inequalities of limits                          *)
(*---------------------------------------------------------------------------*)

val LE_SEQ_IMP_LE_LIM = store_thm
  ("LE_SEQ_IMP_LE_LIM",
   ``!x y f. (!n. x <= f n) /\ f --> y ==> x <= y``,
   RW_TAC boolSimps.bool_ss [SEQ]
   THEN MATCH_MP_TAC REAL_LE_EPSILON
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   THEN RW_TAC boolSimps.bool_ss []
   THEN POP_ASSUM (MP_TAC o Q.SPEC `N`)
   THEN Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   THEN RW_TAC boolSimps.bool_ss
        [GREATER_EQ, LESS_EQ_REFL, abs, REAL_LE_SUB_LADD, REAL_ADD_LID]
   THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
        [REAL_NOT_LE, REAL_NEG_SUB, REAL_LT_SUB_RADD]
   THEN PROVE_TAC [REAL_LET_TRANS, REAL_LT_ADDR, REAL_LTE_TRANS, REAL_LE_TRANS,
                   REAL_LT_LE, REAL_ADD_SYM]);

val SEQ_LE_IMP_LIM_LE = store_thm
  ("SEQ_LE_IMP_LIM_LE",
   ``!x y f. (!n. f n <= x) /\ f --> y ==> y <= x``,
   RW_TAC boolSimps.bool_ss [SEQ]
   THEN MATCH_MP_TAC REAL_LE_EPSILON
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   THEN RW_TAC boolSimps.bool_ss []
   THEN POP_ASSUM (MP_TAC o Q.SPEC `N`)
   THEN Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   THEN (RW_TAC boolSimps.bool_ss
         [GREATER_EQ, LESS_EQ_REFL, abs, REAL_LE_SUB_LADD, REAL_ADD_LID]
         THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
              [REAL_NOT_LE, REAL_NEG_SUB, REAL_LT_SUB_RADD])
   THENL [MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `x`
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TRANS])
          THEN PROVE_TAC [REAL_LE_ADDR, REAL_LT_LE],
          MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `f N + e`
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LT_LE, REAL_ADD_SYM])
          THEN PROVE_TAC [REAL_LE_ADD2, REAL_LE_REFL]]);

val SEQ_MONO_LE = store_thm
  ("SEQ_MONO_LE",
   ``!f x n. (!n. f n <= f (n + 1)) /\ f --> x ==> f n <= x``,
   RW_TAC boolSimps.bool_ss [SEQ]
   THEN MATCH_MP_TAC REAL_LE_EPSILON
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   THEN RW_TAC boolSimps.bool_ss [GREATER_EQ]
   THEN MP_TAC (Q.SPECL [`N`, `n`] LESS_EQ_CASES)
   THEN (STRIP_TAC
         THEN1 (Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`)
                THEN RW_TAC boolSimps.bool_ss
                     [abs, REAL_LE_SUB_LADD, REAL_LT_SUB_RADD, REAL_ADD_LID,
                      REAL_NEG_SUB]
                THENL [PROVE_TAC [REAL_LT_LE, REAL_ADD_SYM],
                       simpLib.FULL_SIMP_TAC boolSimps.bool_ss [REAL_NOT_LE]
                       THEN MATCH_MP_TAC REAL_LE_TRANS
                       THEN Q.EXISTS_TAC `x`
                       THEN PROVE_TAC [REAL_LT_LE, REAL_LE_ADDR]]))
   THEN (SUFF_TAC ``!i : num. f (N - i) <= x + (e : real)``
         THEN1 PROVE_TAC [LESS_EQUAL_DIFF])
   THEN numLib.INDUCT_TAC
   THENL [Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
          THEN RW_TAC boolSimps.bool_ss [abs, LESS_EQ_REFL, SUB_0]
          THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
               [REAL_LT_SUB_RADD, REAL_NEG_SUB, REAL_NOT_LE, REAL_ADD_LID,
                REAL_LE_SUB_LADD]
          THEN PROVE_TAC
               [REAL_LT_LE, REAL_ADD_SYM, REAL_LE_TRANS, REAL_LE_ADDR],
          MP_TAC (numLib.ARITH_PROVE
                  ``(N - i = N - SUC i) \/ (N - i = (N - SUC i) + 1)``)
          THEN PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]);

val SEQ_LE_MONO = store_thm
  ("SEQ_LE_MONO",
   ``!f x n. (!n. f (n + 1) <= f n) /\ f --> x ==> x <= f n``,
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPECL [`\n. ~f n`, `~x`, `n`] SEQ_MONO_LE)
   THEN RW_TAC boolSimps.bool_ss [GSYM SEQ_NEG, REAL_LE_NEG]);

val _ = export_theory();

(*
*)
end;
