(*---------------------------------------------------------------------------*)
(* Set up context                                                            *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib numLib;
open optionTheory pairTheory relationTheory arithmeticTheory
     pred_setTheory bagTheory containerTheory
     listTheory rich_listTheory stringTheory sortingTheory mergesortTheory
     comparisonTheory balanced_mapTheory regexp_mapTheory osetTheory
     finite_mapTheory vec_mapTheory charsetTheory regexpTheory
;


val _ = numLib.temp_prefer_num();

fun pat_elim q = Q.PAT_X_ASSUM q (K ALL_TAC);

val byA = BasicProvers.byA;
infix byA;

val subst_all_tac = SUBST_ALL_TAC;
val simp_rule = SIMP_RULE;

val SET_EQ_THM = FUN_EQ_THM;

val list_ss = list_ss ++ rewrites [LENGTH_NIL, LENGTH_NIL_SYM];

val set_ss = list_ss ++ pred_setLib.PRED_SET_ss ++ rewrites [SET_EQ_THM,IN_DEF]

val comparison_distinct = TypeBase.distinct_of ``:ordering``

(*---------------------------------------------------------------------------*)
(* Trivial lemmas                                                            *)
(*---------------------------------------------------------------------------*)

Triviality INTER_DELETE :
  !A a. A INTER (A DELETE a) = A DELETE a
Proof
  SET_TAC []
QED

Triviality IN_SET_UNION :
 !x s t.
   x IN s ==> (s UNION t = s UNION (x INSERT t))
Proof
 SET_TAC []
QED

Triviality leq_thm :
  transitive (<=) /\ total (<=) /\ antisymmetric (<=)
Proof
   srw_tac [ARITH_ss] [transitive_def, total_def, antisymmetric_def]
QED

Theorem MAX_LE_THM[local] :
  !m n. m <= MAX m n /\ n <= MAX m n
Proof
  RW_TAC arith_ss [MAX_DEF]
QED

Theorem IS_SOME_EXISTS[local] :
  !x. IS_SOME x = ?y. x = SOME y
Proof
  Cases THEN METIS_TAC [optionTheory.IS_SOME_DEF]
QED

Triviality length_mergesort :
  !l R. LENGTH (mergesort R l) = LENGTH l
Proof
  metis_tac[mergesort_perm,PERM_LENGTH]
QED

Triviality LENGTH_NIL_SYM =
   GEN_ALL (CONV_RULE (LHS_CONV SYM_CONV) (SPEC_ALL LENGTH_NIL));

Theorem string_to_numlist[local] :
 !s. (!c. c IN set s ==> ORD c IN set ALPHABET)
     ==>
      ?nl. (s = MAP CHR nl) /\
           (!n. n IN set nl ==> n IN set ALPHABET)
Proof
 Induct >> rw []
  >> `?nl. (s = MAP CHR nl) /\ !n. MEM n nl ==> MEM n ALPHABET` by metis_tac[]
  >> `?n. (h = CHR n) /\ n < 256` by metis_tac [CHR_ONTO]
  >> Q.EXISTS_TAC `n::nl`
  >> rw []
  >> metis_tac [ORD_CHR_RWT,alphabet_size_def]
QED

Theorem all_ord_string[local] :
 EVERY (\c. MEM (ORD c) ALPHABET) s
   <=>
  EVERY (\c. ORD c < alphabet_size) s
Proof
 simp_tac list_ss [mem_alphabet_iff]
QED

(*---------------------------------------------------------------------------*)
(* Let's get started                                                         *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "regexp_compiler";

(*---------------------------------------------------------------------------*)
(* Output of the compiler is in terms of vectors.                            *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `vector = Vector of 'a list`;

Definition fromList_def : fromList l = Vector l
End

Definition sub_def : sub (Vector l) n = EL n l
End

Definition length_def : length (Vector l) = LENGTH l
End

Theorem fromList_Vector = SIMP_RULE list_ss [GSYM FUN_EQ_THM] fromList_def;

(*---------------------------------------------------------------------------*)
(* Operations on the set of seen states                                      *)
(*---------------------------------------------------------------------------*)

val _ = Parse.type_abbrev("regexp_set", ``:(regexp,unit)balanced_map``);

Definition insert_regexp_def :
  insert_regexp r seen =
      balanced_map$insert regexp_compare r () seen
End

Definition mem_regexp_def :
  mem_regexp r seen =
    balanced_map$member regexp_compare r seen
End

(*---------------------------------------------------------------------------*)
(* Transitions out of a state (regexp).                                      *)
(*---------------------------------------------------------------------------*)

Definition transitions_def :
  transitions r = MAP (\c. (c,smart_deriv c r)) ALPHABET
End

(*---------------------------------------------------------------------------*)
(* Special case for Empty (failure state)                                    *)
(*---------------------------------------------------------------------------*)

Definition Empty_arcs_def :
 Empty_arcs =
  [(0,Empty);  (1,Empty);  (2,Empty);  (3,Empty);
   (4,Empty);  (5,Empty);  (6,Empty);  (7,Empty);
   (8,Empty);  (9,Empty);  (10,Empty); (11,Empty);
   (12,Empty); (13,Empty); (14,Empty); (15,Empty);
   (16,Empty); (17,Empty); (18,Empty); (19,Empty);
   (20,Empty); (21,Empty); (22,Empty); (23,Empty);
   (24,Empty); (25,Empty); (26,Empty); (27,Empty);
   (28,Empty); (29,Empty); (30,Empty); (31,Empty);
   (32,Empty); (33,Empty); (34,Empty); (35,Empty);
   (36,Empty); (37,Empty); (38,Empty); (39,Empty);
   (40,Empty); (41,Empty); (42,Empty); (43,Empty);
   (44,Empty); (45,Empty); (46,Empty); (47,Empty);
   (48,Empty); (49,Empty); (50,Empty); (51,Empty);
   (52,Empty); (53,Empty); (54,Empty); (55,Empty);
   (56,Empty); (57,Empty); (58,Empty); (59,Empty);
   (60,Empty); (61,Empty); (62,Empty); (63,Empty);
   (64,Empty); (65,Empty); (66,Empty); (67,Empty);
   (68,Empty); (69,Empty); (70,Empty); (71,Empty);
   (72,Empty); (73,Empty); (74,Empty); (75,Empty);
   (76,Empty); (77,Empty); (78,Empty); (79,Empty);
   (80,Empty); (81,Empty); (82,Empty); (83,Empty);
   (84,Empty); (85,Empty); (86,Empty); (87,Empty);
   (88,Empty); (89,Empty); (90,Empty); (91,Empty);
   (92,Empty); (93,Empty); (94,Empty); (95,Empty);
   (96,Empty); (97,Empty); (98,Empty); (99,Empty);
   (100,Empty); (101,Empty) ; (102,Empty); (103,Empty);
   (104,Empty); (105,Empty);
   (106,Empty); (107,Empty); (108,Empty); (109,Empty);
   (110,Empty); (111,Empty); (112,Empty); (113,Empty);
   (114,Empty); (115,Empty); (116,Empty); (117,Empty);
   (118,Empty); (119,Empty); (120,Empty); (121,Empty);
   (122,Empty); (123,Empty); (124,Empty); (125,Empty);
   (126,Empty); (127,Empty); (128,Empty); (129,Empty);
   (130,Empty); (131,Empty); (132,Empty); (133,Empty);
   (134,Empty); (135,Empty); (136,Empty); (137,Empty);
   (138,Empty); (139,Empty); (140,Empty); (141,Empty);
   (142,Empty); (143,Empty); (144,Empty); (145,Empty);
   (146,Empty); (147,Empty); (148,Empty); (149,Empty);
   (150,Empty); (151,Empty); (152,Empty); (153,Empty);
   (154,Empty); (155,Empty); (156,Empty); (157,Empty);
   (158,Empty); (159,Empty); (160,Empty); (161,Empty);
   (162,Empty); (163,Empty); (164,Empty); (165,Empty);
   (166,Empty); (167,Empty); (168,Empty); (169,Empty);
   (170,Empty); (171,Empty); (172,Empty); (173,Empty);
   (174,Empty); (175,Empty); (176,Empty); (177,Empty);
   (178,Empty); (179,Empty); (180,Empty); (181,Empty);
   (182,Empty); (183,Empty); (184,Empty); (185,Empty);
   (186,Empty); (187,Empty); (188,Empty); (189,Empty);
   (190,Empty); (191,Empty); (192,Empty); (193,Empty);
   (194,Empty); (195,Empty); (196,Empty); (197,Empty);
   (198,Empty); (199,Empty); (200,Empty); (201,Empty);
   (202,Empty); (203,Empty); (204,Empty); (205,Empty);
   (206,Empty); (207,Empty); (208,Empty); (209,Empty);
   (210,Empty); (211,Empty); (212,Empty); (213,Empty);
   (214,Empty); (215,Empty); (216,Empty); (217,Empty);
   (218,Empty); (219,Empty); (220,Empty); (221,Empty);
   (222,Empty); (223,Empty); (224,Empty); (225,Empty);
   (226,Empty); (227,Empty); (228,Empty); (229,Empty);
   (230,Empty); (231,Empty); (232,Empty); (233,Empty);
   (234,Empty); (235,Empty); (236,Empty); (237,Empty);
   (238,Empty); (239,Empty); (240,Empty); (241,Empty);
   (242,Empty); (243,Empty); (244,Empty); (245,Empty);
   (246,Empty); (247,Empty); (248,Empty); (249,Empty);
   (250,Empty); (251,Empty); (252,Empty); (253,Empty);
   (254,Empty); (255,Empty)]
End;

Theorem Empty_arcs_thm :
  MAP (\c. (c,smart_deriv c Empty)) ALPHABET = Empty_arcs
Proof
  rw_tac (srw_ss())
    [ALPHABET_def, Empty_arcs_def, smart_deriv_def,
     Empty_def,Epsilon_def,charset_mem_empty]
QED

Theorem transitions_thm :
  transitions r = if r = Empty then Empty_arcs
                  else MAP (\c. (c,smart_deriv c r)) ALPHABET
Proof
  rw_tac list_ss [transitions_def] >> metis_tac [Empty_arcs_thm]
QED

(*---------------------------------------------------------------------------*)
(* Given the outgoing arcs (c_1,r_1) ... (c_n,r_n) from node r, add all the  *)
(* not-yet-seen r_i regexps to the state map and return the row as a list of *)
(* (c_i, state_map(r_i)) pairs                                               *)
(*---------------------------------------------------------------------------*)

Definition extend_states_def :
 (extend_states next_state state_map row [] = (next_state,state_map,row)) /\
 (extend_states next_state state_map row ((c,r')::t) =
   case lookup regexp_compare r' state_map
    of SOME n => extend_states next_state state_map ((c,n)::row) t
     | NONE   => extend_states
                   (next_state + 1n)
                   (insert regexp_compare r' next_state state_map)
                   ((c,next_state)::row)
                   t)
End

(*---------------------------------------------------------------------------*)
(* Compute the row corresponding to state r and cons it on to the table      *)
(* under construction. Also keep the state_map uptodate.                     *)
(*---------------------------------------------------------------------------*)

Definition build_table_def :
 build_table arcs r (next_state,state_map,table) =
   let (next_state',state_map',row) =
             extend_states next_state state_map [] arcs
   in case lookup regexp_compare r state_map'
       of SOME n => (next_state', state_map', (n,row)::table)
        | NONE   => (next_state' + 1n,
                     insert regexp_compare r next_state' state_map',
                     (next_state',row)::table)
End

(*---------------------------------------------------------------------------*)
(* The core regexp compiler. The seen argument holds the already-seen        *)
(* regexps, which map to states in the final DFA. The n argument is a        *)
(* step-index used to ensure that the function terminates.                   *)
(*---------------------------------------------------------------------------*)

Definition Brz_def :
  Brz seen work acc n =
     if n <= 0n then
       NONE
     else
     if null work then
       SOME (seen,acc)
     else
         let (m,t) = deleteFindMin work;
             r = FST m;
         in if mem_regexp r seen then
               Brz seen t acc (n-1)
            else
             let arcs = transitions r
             in Brz (insert_regexp r seen)
                    (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                    (build_table arcs r acc)
                    (n-1)
End

Definition MAXNUM_32_def :
  MAXNUM_32 = 2147483647n
End

(*---------------------------------------------------------------------------*)
(* Build Greve-style Brz function                                            *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Domain of the function.                                                   *)
(*---------------------------------------------------------------------------*)

Definition dom_Brz_def :
  dom_Brz seen work acc = ?d. IS_SOME(Brz seen work acc d)
End

(*---------------------------------------------------------------------------*)
(* Create measure function rdepth. Uses following code copied from           *)
(*                                                                           *)
(*       HOLDIR/src/pfl/defchoose                                            *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*  MINCHOOSE (sname, cname,``!x1 ... xn. ?z. M[x1,...,xn,z]``)              *)
(*   returns                                                                 *)
(*                                                                           *)
(*    |- !x1...xn z. M[x1,...,xn,z] ==>                                      *)
(*                   M[x1,...,xn,cname x1...xn] /\                           *)
(*                   !m. M[x1,...,xn,m] ==> cname x1...xn <= m               *)
(*                                                                           *)
(* where cname in the theorem is a constant. This theorem is stored in the   *)
(* current theory under sname. Thus this rule is a form of the               *)
(* well-ordering property.                                                   *)
(*---------------------------------------------------------------------------*)

Theorem WOP_ALT[local] :
 !P. (?n. P n) ==> ?min. P min /\ !k. P k ==> min <= k
Proof
 METIS_TAC [arithmeticTheory.WOP,DECIDE ``~(m<n) ==> n<=m``]
QED

fun MINCHOOSE (store_name,const_name,tm) =
 let val (V,body) = strip_forall tm
     val P = snd(dest_comb body)
     val wop_thm = BETA_RULE(SPEC P WOP_ALT)
     val min_term = snd(dest_imp (concl wop_thm))
     val min_term_pred = snd(dest_comb min_term)
     val th1 = BETA_RULE(GSYM (ISPECL [body,min_term_pred] RIGHT_EXISTS_IMP_THM))
     val th2 = EQ_MP th1 wop_thm
     val th3 = GENL V th2
     val th4 = Ho_Rewrite.REWRITE_RULE[SKOLEM_THM] th3
     val th5 = Ho_Rewrite.REWRITE_RULE[GSYM LEFT_FORALL_IMP_THM] th4
 in
  new_specification(store_name, [const_name], th5)
 end
 handle e => raise wrap_exn "" "MINCHOOSE" e;

val rdepth_thm =
   MINCHOOSE ("rdepth_thm", "rdepth",
    ``!seen work acc. ?d. IS_SOME(Brz seen work acc d)``)

(*---------------------------------------------------------------------------*)
(* Define Brzozo                                                             *)
(*---------------------------------------------------------------------------*)

Definition Brzozo_def :
  Brzozo seen work acc =
      THE (Brz seen work acc (rdepth seen work acc))
End


(*---------------------------------------------------------------------------*)
(* Lemmas about Brz and definedness                                          *)
(*---------------------------------------------------------------------------*)

Theorem IS_SOME_Brz[local] :
 !d seen work acc.
    IS_SOME (Brz seen work acc d) ==> d <> 0
Proof
 Cases >> rw[Once Brz_def]
QED

Theorem Brz_SOME[local] :
 !d seen work acc res.
   (Brz seen work acc d = SOME res) ==> d <> 0
Proof
 METIS_TAC [IS_SOME_Brz,IS_SOME_EXISTS]
QED

Theorem Brz_dlem[local] :
 !d seen work acc.
   IS_SOME (Brz seen work acc d)
   ==>
   (Brz seen work acc d = Brz seen work acc (SUC d))
Proof
 Ho_Rewrite.REWRITE_TAC [IS_SOME_EXISTS,GSYM LEFT_FORALL_IMP_THM]
 >> Induct
    >- metis_tac [Brz_SOME]
    >- (rw_tac bool_ss []
        >> pop_assum (mp_tac o SYM)
        >> ONCE_REWRITE_TAC [Brz_def]
        >> rw_tac list_ss [LET_THM]
        >> Cases_on `(deleteFindMin work)`
        >> BasicProvers.NORM_TAC list_ss []
        >> fs[])
QED

Theorem Brz_monotone[local] :
 !d1 d2 seen work acc.
      IS_SOME(Brz seen work acc d1) /\ d1 <= d2
       ==> (Brz seen work acc d1 = Brz seen work acc d2)
Proof
 RW_TAC arith_ss [LESS_EQ_EXISTS] THEN
 Induct_on `p` THEN METIS_TAC [ADD_CLAUSES,Brz_dlem]
QED

Theorem Brz_norm[local] :
 !d seen work acc.
   IS_SOME(Brz seen work acc d)
    ==>
   (Brz seen work acc d = Brz seen work acc (rdepth seen work acc))
Proof
  METIS_TAC [Brz_monotone,rdepth_thm]
QED

Theorem Brz_determ :
 !d1 d2 seen work acc.
    IS_SOME(Brz seen work acc d1) /\ IS_SOME(Brz seen work acc d2)
       ==> (Brz seen work acc d1 = Brz seen work acc d2)
Proof
  METIS_TAC [Brz_norm]
QED

(*---------------------------------------------------------------------------*)
(* Derive eqns for dom_Brz                                                   *)
(*---------------------------------------------------------------------------*)

Theorem lem[local] :
 !seen work acc.
   null work ==> IS_SOME (Brz seen work acc 1)
Proof
 RW_TAC arith_ss [Once Brz_def]
QED

Theorem dom_base_case[local] :
 !seen work acc.
   null work ==> dom_Brz seen work acc
Proof
 METIS_TAC [dom_Brz_def, lem]
QED

Theorem step2_lem1a[local] :
 !seen work acc r x t.
   ~null work /\
   (deleteFindMin work = ((r,x),t)) /\
   mem_regexp r seen /\ dom_Brz seen work acc
    ==> dom_Brz seen t acc
Proof
 rw_tac std_ss [dom_Brz_def]
  >> `d<>0` by metis_tac [IS_SOME_Brz]
  >> qexists_tac `d-1`
  >> qpat_x_assum `IS_SOME arg` (mp_tac o ONCE_REWRITE_RULE [Brz_def])
  >> rw_tac arith_ss [LET_THM]
QED

Theorem step2_lem1b[local] :
 !seen work acc r x t arcs.
   ~null work /\
   (deleteFindMin work = ((r,x),t)) /\
   ~mem_regexp r seen /\
   (arcs = transitions r) /\
   dom_Brz seen work acc
    ==> dom_Brz (insert_regexp r seen)
                (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                (build_table arcs r acc)
Proof
 rw_tac std_ss [dom_Brz_def]
  >> `d<>0` by metis_tac [IS_SOME_Brz]
  >> qexists_tac `d-1`
  >> qpat_x_assum `IS_SOME arg` (mp_tac o ONCE_REWRITE_RULE [Brz_def])
  >> rw_tac arith_ss [LET_THM]
QED

Theorem step2_lem2a[local] :
 !seen work acc r x t.
   ~null work /\
   (deleteFindMin work = ((r,x),t)) /\
   mem_regexp r seen /\ dom_Brz seen t acc
   ==> dom_Brz seen work acc
Proof
 rw_tac std_ss [dom_Brz_def]
   >> Q.EXISTS_TAC `SUC d`
   >> rw [Once Brz_def]
QED

Theorem step2_lem2b[local] :
 !seen work acc r x t arcs.
   ~null work /\
   (deleteFindMin work = ((r,x),t)) /\
   (arcs = transitions r) /\
  ~mem_regexp r seen /\
  dom_Brz (insert_regexp r seen)
          (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
          (build_table arcs r acc)
   ==> dom_Brz seen work acc
Proof
 rw_tac std_ss [dom_Brz_def]
   >> Q.EXISTS_TAC `SUC d`
   >> rw [Once Brz_def,LET_THM]
QED


(*---------------------------------------------------------------------------*)
(* Equational characterization of dom.                                       *)
(*---------------------------------------------------------------------------*)

Theorem dom_Brz_eqns :
 dom_Brz seen work acc =
    if null work then
      T
    else let (m,t) = deleteFindMin work ;
             r = FST m;
         in
           if mem_regexp r seen then
               dom_Brz seen t acc
           else let arcs = transitions r
                in dom_Brz (insert_regexp r seen)
                           (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                           (build_table arcs r acc)
Proof
 Cases_on `null work`
  >- metis_tac[dom_base_case]
  >- (asm_simp_tac list_ss []
       >> Cases_on `deleteFindMin work`
       >> rw []
       >> Cases_on `q`
       >> fs[]
          >- metis_tac [step2_lem1a,step2_lem2a]
          >- metis_tac [step2_lem1b,step2_lem2b])
QED

(*---------------------------------------------------------------------------*)
(* Optimization: dom_Brz doesn't depend on its "acc" argument, so can be     *)
(* replaced by a version that doesn't have it.                               *)
(*---------------------------------------------------------------------------*)

Definition dom_Brz_alt_def :
  dom_Brz_alt seen work = dom_Brz seen work ARB
End

Theorem acc_irrelevant[local] :
 !n seen work acc acc1.
     IS_SOME (Brz seen work acc n) ==> IS_SOME (Brz seen work acc1 n)
Proof
 Induct
   >- rw [Once Brz_def]
   >- (ONCE_REWRITE_TAC [Brz_def]
        >> rw_tac list_ss [LET_THM]
        >> Cases_on `(deleteFindMin work)`
        >> fs []
        >> metis_tac[])
QED

Theorem dom_Brz_alt_equal :
 !seen work acc.
     dom_Brz seen work acc = dom_Brz_alt seen work
Proof
  rw [dom_Brz_def, dom_Brz_alt_def] >> metis_tac [acc_irrelevant]
QED

Theorem dom_Brz_alt_eqns :
 dom_Brz_alt seen work =
    if null work then
      T
    else let (m,t) = deleteFindMin work ;
             r = FST m;
         in
           if mem_regexp r seen then
               dom_Brz_alt seen t
           else let arcs = transitions r
                in dom_Brz_alt (insert_regexp r seen)
                           (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
Proof
 metis_tac [SIMP_RULE bool_ss [dom_Brz_alt_equal] dom_Brz_eqns]
QED

(*---------------------------------------------------------------------------*)
(* Recursion equations for Brzozo                                            *)
(*---------------------------------------------------------------------------*)

Theorem Brzozo_base[local] :
 !seen work acc.
    dom_Brz seen work acc /\ null work
    ==>
   (Brzozo seen work acc = (seen,acc))
Proof
 rw_tac std_ss [Brzozo_def,dom_Brz_def]
  >> `rdepth seen work acc <> 0`
       by METIS_TAC [IS_SOME_Brz,rdepth_thm]
  >> rw_tac arith_ss [Once Brz_def]
QED

Theorem Brzozo_rec1[local] :
 !seen work accr r x t.
     ~null work /\
     (deleteFindMin work = ((r,x),t)) /\
      dom_Brz seen work acc /\
      mem_regexp r seen
     ==>
      (Brzozo seen work acc = Brzozo seen t acc)
Proof
 rw_tac std_ss [Brzozo_def,dom_Brz_def]
  >> `d <> 0` by METIS_TAC [IS_SOME_Brz]
  >> `Brz seen work acc d = Brz seen t acc (d-1)`
      by rw_tac list_ss [SimpLHS,Once Brz_def,LET_THM]
  >> metis_tac [IS_SOME_EXISTS,NOT_SOME_NONE,THE_DEF,Brz_norm]
QED

Theorem Brzozo_rec2[local] :
 !seen work accr r x t.
    ~null work /\
    (deleteFindMin work = ((r,x),t)) /\
    dom_Brz seen work acc /\
    ~mem_regexp r seen
    ==>
    (Brzozo seen work acc =
       let arcs = transitions r
       in Brzozo (insert_regexp r seen)
                 (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                 (build_table arcs r acc))
Proof
 rw_tac std_ss [Brzozo_def,dom_Brz_def,LET_THM]
  >> `d <> 0` by METIS_TAC [IS_SOME_Brz]
  >> `Brz seen work acc d =
      let arcs = transitions r
      in Brz (insert_regexp r seen)
          (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
          (build_table arcs r acc) (d-1)`
      by rw_tac list_ss [SimpLHS,Once Brz_def,LET_THM]
  >> METIS_TAC [IS_SOME_EXISTS,NOT_SOME_NONE,THE_DEF,Brz_norm,LET_THM]
QED

(*---------------------------------------------------------------------------*)
(* Equational characterization of Brzozo.                                    *)
(*---------------------------------------------------------------------------*)

Theorem Brzozo_eqns[local] :
 !seen work acc.
    dom_Brz seen work acc
    ==>
     Brzozo seen work acc =
       if null work then
          (seen,acc)
       else
         let (rp,t) = deleteFindMin work;
                  r = FST rp;
         in
           if mem_regexp r seen then
              Brzozo seen t acc
          else
            let arcs = transitions r
            in
             Brzozo (insert_regexp r seen)
                    (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                    (build_table arcs r acc)
Proof
 rw_tac list_ss [LET_THM]
 >- metis_tac [Brzozo_base]
 >- (Cases_on `deleteFindMin work`
      >> Cases_on `q`
      >> fs[]
      >> metis_tac [Brzozo_rec1,Brzozo_rec2])
QED

(*---------------------------------------------------------------------------*)
(* Now prove induction theorem. This is based on using rdepth as a measure   *)
(* on the recursion. Thus we first have some lemmas about how rdepth         *)
(* decreases in recursive calls.                                             *)
(*---------------------------------------------------------------------------*)

Theorem step3a_lt[local] :
 !seen work acc r x t.
   ~null work /\
   (deleteFindMin work = ((r,x),t)) /\
   mem_regexp r seen /\
    dom_Brz seen work acc
    ==> rdepth seen t acc  < rdepth seen work acc
Proof
 rw_tac std_ss [dom_Brz_def] THEN IMP_RES_TAC rdepth_thm THEN
   `rdepth seen work acc <> 0` by METIS_TAC [IS_SOME_Brz] THEN
   `rdepth seen work acc - 1 < rdepth seen work acc` by DECIDE_TAC THEN
   `IS_SOME (Brz seen t acc (rdepth seen work acc - 1))`
     by (qpat_x_assum `IS_SOME (Brz seen work acc (rdepth seen work acc))`
              (mp_tac o SIMP_RULE arith_ss [Once Brz_def])
         >> rw[LET_THM])
    >> `rdepth seen t acc <= rdepth seen work acc - 1`
        by metis_tac [rdepth_thm]
    >> decide_tac
QED

Theorem step3b_lt[local] :
 !seen work acc r x t arcs.
    ~null work /\
    (deleteFindMin work = ((r,x),t)) /\
    ~mem_regexp r seen /\
    (arcs = transitions r) /\ dom_Brz seen work acc
    ==> rdepth (insert_regexp r seen)
               (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
               (build_table arcs r acc)
         <
        rdepth seen work acc
Proof
 rw_tac std_ss [dom_Brz_def] THEN IMP_RES_TAC rdepth_thm
  >> `rdepth seen work acc <> 0` by METIS_TAC [IS_SOME_Brz]
  >> `rdepth seen work acc - 1 < rdepth seen work acc` by DECIDE_TAC
  >> `IS_SOME (Brz (insert_regexp r seen)
                   (FOLDL (\work a. insert_regexp (SND a) work) t (transitions r))
                   (build_table (transitions r) r acc)
                   (rdepth seen work acc - 1))`
     by (qpat_x_assum `IS_SOME (Brz seen work acc (rdepth seen work acc))`
              (mp_tac o SIMP_RULE arith_ss [Once Brz_def])
         >> rw[LET_THM])
    >> `rdepth (insert_regexp r seen)
               (FOLDL (\work a. insert_regexp (SND a) work) t (transitions r))
               (build_table (transitions r) r acc) <= rdepth seen work acc - 1`
        by metis_tac [rdepth_thm]
    >> decide_tac
QED

(*---------------------------------------------------------------------------*)
(* Induction for Brzozo is obtained by instantiating the WF induction        *)
(* theorem with the rdepth measure and then simplifying.                     *)
(*---------------------------------------------------------------------------*)

Theorem ind_lemA =
  prim_recTheory.WF_measure
   |> Q.ISPEC `\(seen,work,acc). rdepth seen work acc`
   |> MATCH_MP relationTheory.WF_INDUCTION_THM
   |> simp_rule std_ss [prim_recTheory.measure_thm]
   |> Q.ISPEC `\(seen,work,acc).
                  dom_Brz seen work acc ==> P seen work acc`
   |> simp_rule std_ss [pairTheory.FORALL_PROD]
;

Theorem ind_lemB[local] :
  !P. (!seen work acc.
         (!a b c. rdepth a b c < rdepth seen work acc
                  ==> dom_Brz a b c
                  ==> P a b c)
         ==> dom_Brz seen work acc ==> P seen work acc)
  ==>
  !seen work acc. dom_Brz seen work acc ==> P seen work acc
Proof
rpt strip_tac
 >> pop_assum mp_tac
 >> `?a b c. acc = (a,b,c)` by metis_tac [ABS_PAIR_THM]
 >> pop_assum SUBST_ALL_TAC
 >> MAP_EVERY Q.ID_SPEC_TAC [`a`,`b`, `c`,`work`,`seen`]
 >> match_mp_tac ind_lemA
 >> fs [FORALL_PROD]
QED

Theorem Brzozowski_ind :
 !P.
   (!seen work acc.
       dom_Brz seen work acc /\
       (!r x t. ~null work /\
                (deleteFindMin work = ((r,x),t)) /\
                mem_regexp r seen ==> P seen t acc) /\
       (!r x t arcs.
           ~null work /\ (deleteFindMin work = ((r,x),t)) /\
           (arcs = transitions r) /\ ~mem_regexp r seen
           ==> P (insert_regexp r seen)
                 (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                 (build_table arcs r acc))
         ==> P seen work acc)
  ==> !seen work acc. dom_Brz seen work acc ==> P seen work acc
Proof
  gen_tac
  >> strip_tac
  >> ho_match_mp_tac ind_lemB
  >> simp_tac bool_ss [AND_IMP_INTRO]
  >> rpt gen_tac
  >> disch_then (fn th => first_x_assum match_mp_tac >> assume_tac th)
  >> rw []
  >> (first_x_assum match_mp_tac
       >> asm_simp_tac list_ss [step3a_lt,step3b_lt]
       >> mp_tac dom_Brz_eqns
       >> rw [])
QED

(*---------------------------------------------------------------------------*)
(* Efficient executable version of Brzozo                                    *)
(*---------------------------------------------------------------------------*)

Definition exec_Brz_def :
  exec_Brz seen work acc d =
    if d=0n then
       (if dom_Brz seen work acc then Brzozo seen work acc else ARB)
    else
    if null work then
          (seen,acc)
    else
      let (m,t) = deleteFindMin work ;
              r = FST m;
      in
         if mem_regexp r seen then
             exec_Brz seen t acc (d - 1)
         else
           let arcs = transitions r
           in exec_Brz (insert_regexp r seen)
                       (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                       (build_table arcs r acc) (d - 1)
End

Theorem exec_Brz_equals_Brzozo[local] :
  !d seen work acc.
    dom_Brz seen work acc
    ==>
     (exec_Brz seen work acc d = Brzozo seen work acc)
Proof
 Induct
  >> rw_tac std_ss [Once exec_Brz_def,LET_THM]
  >- metis_tac [Brzozo_eqns]
  >- (`?r x t. deleteFindMin work = ((r,x),t)` by metis_tac [ABS_PAIR_THM]
      >> rw [Brzozo_eqns]
      >> (first_x_assum match_mp_tac
           >> qpat_x_assum `dom_Brz seen work acc`
              (mp_tac o SIMP_RULE list_ss [Once dom_Brz_eqns])
           >> rw []))
QED

(*---------------------------------------------------------------------------*)
(* The final definition of the core functionality of the compiler            *)
(*---------------------------------------------------------------------------*)

Definition Brzozowski_def :
  Brzozowski seen work acc =
      if dom_Brz seen work acc then
         Brzozo seen work acc
      else
         exec_Brz seen work acc MAXNUM_32
End

(*---------------------------------------------------------------------------*)
(* Theorem showing that Brzozowski can be executed w.o. termination proof.   *)
(* In order to evaluate Brzozowski, we can dispatch to exec_Brz.             *)
(*---------------------------------------------------------------------------*)

Theorem Brzozowski_exec_Brz :
   Brzozowski seen work acc = exec_Brz seen work acc MAXNUM_32
Proof
 rw_tac std_ss [Brzozowski_def,exec_Brz_equals_Brzozo]
QED

(*---------------------------------------------------------------------------*)
(* In order to reason about Brzozowski, we use the following theorem.        *)
(*---------------------------------------------------------------------------*)

Theorem Brzozowski_eqns :
 dom_Brz seen work acc
  ==>
 Brzozowski seen work acc =
    if null work then
        (seen,acc)
    else let (m,t) = deleteFindMin work;
                 r = FST m;
         in if mem_regexp r seen then
                Brzozowski seen t acc
            else
              let arcs = transitions r
              in Brzozowski (insert_regexp r seen)
                            (FOLDL (\work a. insert_regexp (SND a) work) t arcs)
                            (build_table arcs r acc)
Proof
rw_tac std_ss [Brzozowski_def,LET_THM]
 >- metis_tac [Brzozo_eqns]
 >- (`?r x t. deleteFindMin work = ((r,x),t)` by metis_tac [ABS_PAIR_THM]
      >> rw []
      >> rw [SimpLHS, Once Brzozo_eqns]
      >> (qpat_x_assum `dom_Brz seen work acc`
              (mp_tac o SIMP_RULE list_ss [Once dom_Brz_eqns])
          >> rw []))
QED

(*---------------------------------------------------------------------------*)
(* Definitions that find the accept states and map the final results to      *)
(* vector form.                                                              *)
(*---------------------------------------------------------------------------*)

Definition get_accepts_def :
  get_accepts fmap =
    mergesort (\a b:num. a <= b)
       (balanced_map$foldrWithKey
         (\r (n:num) nlist. if nullable r then n::nlist else nlist)
         [] fmap)
End

Definition accepts_to_vector_def:
  accepts_to_vector accept_states max_state =
     alist_to_vec (MAP (\x. (x,T)) accept_states) F max_state max_state
End

Definition table_to_vectors_def:
  table_to_vectors table =
     MAP (\(k:num,table2).
             alist_to_vec (mergesort (inv_image (\a b:num. a <= b) FST)
                                (MAP (\(c,n). (c, SOME n)) table2))
                          NONE alphabet_size alphabet_size)
         (mergesort (inv_image (\a b:num. a <= b) FST) table)
End

(*---------------------------------------------------------------------------*)
(* The basic regexp compiler function                                        *)
(*---------------------------------------------------------------------------*)

Definition compile_regexp_def :
  compile_regexp r =
    let r' = normalize r ;
        (states,last_state,state_numbering,table)
          = Brzozowski balanced_map$empty
                       (balanced_map$singleton r' ())
                       (1n, balanced_map$singleton r' 0n, []) ;
        delta_vecs = table_to_vectors table ;
        accepts_vec = accepts_to_vector (get_accepts state_numbering) last_state
    in
      (state_numbering, delta_vecs, accepts_vec)
End

(*---------------------------------------------------------------------------*)
(* DFA evaluator                                                             *)
(*---------------------------------------------------------------------------*)

Definition exec_dfa_def :
 exec_dfa finals table n s =
   case s of
    | "" => sub finals n
    | c::t =>
      case sub (sub table n) (ORD c) of
       | NONE => F
       | SOME k => exec_dfa finals table k t
End

Theorem exec_dfa_thm :
  (exec_dfa finals table n [] = sub finals n) /\
  (exec_dfa finals table n (c::t) =
    case sub (sub table n) (ORD c) of
     | NONE => F
     | SOME k => exec_dfa finals table k t)
Proof
  CONJ_TAC
   >- rw_tac list_ss [exec_dfa_def]
   >- rw_tac list_ss [SimpLHS, Once exec_dfa_def]
QED

(*---------------------------------------------------------------------------*)
(* Set of strings accepted by DFA generated from regexp r                    *)
(*---------------------------------------------------------------------------*)

Definition Brz_lang_def :
  Brz_lang r =
    let (state_map,table_vec,finals_vec) = compile_regexp r ;
        tableV = fromList (MAP fromList table_vec) ;
        finalsV = fromList finals_vec ;
    in
       exec_dfa finalsV tableV
         (THE (lookup regexp_compare (normalize r) state_map))
End


(*---------------------------------------------------------------------------*)
(* Combines the DFA compilation and the DFA evaluator. Returns a function of *)
(* type :string -> bool                                                      *)
(*---------------------------------------------------------------------------*)

Definition regexp_matcher_def :
 regexp_matcher r =
    let (state_map,delta,accepts) = compile_regexp r ;
        start_state = THE (lookup regexp_compare (normalize r) state_map) ;
        acceptsV = fromList accepts ;
        deltaV = fromList (MAP fromList delta) ;
    in
      exec_dfa acceptsV deltaV start_state
End

(*---------------------------------------------------------------------------*)
(* Properties of get_accepts                                                 *)
(*---------------------------------------------------------------------------*)

Theorem sorted_get_accepts :
  !fmap.
     SORTED $<= (get_accepts fmap)
Proof
 RW_TAC set_ss [get_accepts_def] THEN
 CONV_TAC (DEPTH_CONV ETA_CONV) THEN
 MATCH_MP_TAC mergesort_sorted THEN
 RW_TAC arith_ss [transitive_def, total_def]
QED


Theorem mem_get_acceptsA[local] :
 !fmap P x acc.
    balanced_map$invariant regexp_compare fmap /\
    MEM x (foldrWithKey
               (\r n nlist. if P r then n::nlist else nlist)
               acc fmap)
     ==>
    MEM x acc \/ ?r. P r /\ (lookup regexp_compare r fmap = SOME x)
Proof
 Induct THEN RW_TAC std_ss []
  >- full_simp_tac list_ss [foldrWithKey_def,lookup_def]
  >- (simp_tac list_ss [lookup_bin]
       >>
      `invariant regexp_compare fmap /\
       invariant regexp_compare fmap' /\
       key_ordered regexp_compare k fmap Greater /\
       key_ordered regexp_compare k fmap' Less`
           by metis_tac [invariant_def]
      >> qpat_x_assum `invariant cmp (Bin n k v fmap fmap')` (K ALL_TAC)
      >> fs []
      >> RULE_ASSUM_TAC (REWRITE_RULE [foldrWithKey_def])
      >> RES_THEN MP_TAC >> BETA_TAC >> rw[]
        >- metis_tac [regexp_compare_eq]
        >- metis_tac [key_less_lookup,regexp_compare_good,good_cmp_thm]
        >- metis_tac [key_greater_lookup,regexp_compare_good,good_cmp_thm]
        >- metis_tac [key_less_lookup,regexp_compare_good,good_cmp_thm]
        >- metis_tac [key_greater_lookup,regexp_compare_good,good_cmp_thm])
QED

Theorem mem_foldrWithKey_mono[local] :
 !P fmap x acc.
    MEM x acc
     ==>
     MEM x (foldrWithKey
               (\r n nlist. if P r then n::nlist else nlist)
               acc fmap)
Proof
  gen_tac
   >> Induct
   >> RW_TAC std_ss [foldrWithKey_def]
   >> metis_tac [MEM]
QED

Theorem mem_get_acceptsB[local] :
 !P fmap r x acc.
    P r /\ (lookup regexp_compare r fmap = SOME x)
     ==>
    MEM x (foldrWithKey (\r n nlist. if P r then n::nlist else nlist) acc fmap)
Proof
  gen_tac >> Induct
  >- rw_tac list_ss [lookup_def,foldrWithKey_def]
  >- (rw_tac list_ss [lookup_bin,regexp_compare_eq,foldrWithKey_def]
       >> metis_tac [mem_foldrWithKey_mono,MEM])
QED

Theorem mem_get_accepts[local] :
 !bmap x.
    invariant regexp_compare bmap
    ==>
     (MEM x (get_accepts bmap)
       <=>
      ?r. nullable r /\
          (lookup regexp_compare r bmap = SOME x))
Proof
 rw_tac list_ss [get_accepts_def,mergesort_mem]
  >> metis_tac [mem_get_acceptsA,mem_get_acceptsB,MEM]
QED

(*---------------------------------------------------------------------------*)
(* Properties of extend_states                                               *)
(*---------------------------------------------------------------------------*)

Definition extend_states_inv_def :
  extend_states_inv next_state state_map table =
     (invariant regexp_compare state_map /\
      fmap_inj regexp_compare state_map /\
      (frange regexp_compare state_map = count next_state) /\
      (!n. MEM n (MAP SND table) ==> n < next_state))
End

Theorem extend_states_inv[local] :
 !next_state state_map table states next_state' state_map' table'.
     (extend_states next_state state_map table states
         = (next_state',state_map',table')) /\
     extend_states_inv next_state state_map table
    ==>
    extend_states_inv next_state' state_map' table'
Proof
 ho_match_mp_tac extend_states_ind
  >> rw [extend_states_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> fs []
  >> FIRST_X_ASSUM match_mp_tac
  >> rw []
  >> fs [extend_states_inv_def, frange_def,
         MEM_MAP,EXTENSION,GSYM LEFT_FORALL_IMP_THM]
  >> `good_cmp regexp_compare /\ eq_cmp regexp_compare`
        by metis_tac [eq_cmp_regexp_compare,regexp_compare_good]
  >> rw_tac set_ss []
  >- metis_tac [insert_thm]
  >- (fs [fmap_inj_def,lookup_insert_thm]
       >> rw [regexp_compare_eq,fdom_insert]
       >> metis_tac [DECIDE ``x < (x:num) ==> F``,eq_cmp_def])
  >- (rw [lookup_insert_thm,regexp_compare_eq,EQ_IMP_THM]
       >- (pop_assum mp_tac >> rw_tac set_ss []
            >> metis_tac [DECIDE ``x < x + 1n``,LESS_TRANS])
       >- (`x < next_state \/ (x=next_state)` by DECIDE_TAC
             >> metis_tac [NOT_SOME_NONE]))
  >- rw_tac set_ss []
  >- metis_tac [LESS_TRANS,DECIDE ``x < x+1n``,IN_DEF]
  >- (rw_tac set_ss [] >> metis_tac[])
  >- metis_tac [LESS_TRANS,DECIDE ``x < x+1n``,IN_DEF]
QED


Theorem extend_states_thm :
 !next_state state_map table states next_state' state_map' table'.
    (extend_states next_state state_map table states
       = (next_state',state_map',table')) /\
    invariant regexp_compare state_map
   ==>
  (fdom regexp_compare state_map' =
      (fdom regexp_compare state_map UNION set (MAP SND states))) /\
  submap regexp_compare state_map state_map' /\
  next_state <= next_state' /\
  (table' = REVERSE
             (MAP (\(c,r). (c, fapply regexp_compare state_map' r)) states)
            ++ table) /\
  invariant regexp_compare state_map'
Proof
 `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare]
  >> ho_match_mp_tac extend_states_ind
  >> rw [extend_states_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> `invariant regexp_compare (insert regexp_compare r' next_state state_map)`
       by metis_tac [insert_thm,eq_cmp_def]
  >> fs [submap_id]
  >> res_tac
  >- (rw_tac set_ss [fdom_insert] >> metis_tac[])
  >- (`r' IN fdom regexp_compare state_map` by rw [fdom_def]
       >> rw_tac set_ss [IN_SET_UNION])
  >- (match_mp_tac submap_insert >> rw [fdom_def] >> metis_tac [NOT_SOME_NONE])
  >- decide_tac
  >- (pat_elim `$! M` >> rw[]
       >> qpat_x_assum `submap _ __ ___` mp_tac
      >> rw_tac set_ss [submap_def,fapply_def]
      >> pop_assum (mp_tac o Q.SPEC `r'`)
      >> rw [fdom_insert]
      >> pop_assum mp_tac
      >> `good_cmp regexp_compare` by metis_tac [regexp_compare_good]
      >> rw [lookup_insert_thm,regexp_compare_eq]
      >> metis_tac [THE_DEF])
  >- (pat_elim `$! M` >> rw[]
       >> qpat_x_assum `submap _ __ ___` mp_tac
      >> rw_tac set_ss [submap_def,fapply_def]
      >> pop_assum (mp_tac o Q.SPEC `r'`)
      >> rw [fdom_def]
      >> metis_tac [THE_DEF])
QED

(*---------------------------------------------------------------------------*)
(* What it means to be a good table                                          *)
(*---------------------------------------------------------------------------*)

Definition good_table_def :
  good_table state_map table =
     (ALL_DISTINCT (MAP FST table) /\
     (!n table2.
        (ALOOKUP table n = SOME table2)
        ==>
        (set (MAP FST table2) = set ALPHABET)) /\
     (!n c n' table2.
        (ALOOKUP table n = SOME table2) /\
        (ALOOKUP table2 c = SOME n')
       ==>
       MEM c ALPHABET /\
       ?r r'.
         (lookup regexp_compare r state_map = SOME n) /\
         (lookup regexp_compare r' state_map = SOME n') /\
         (r' = smart_deriv c r)))
End

(*---------------------------------------------------------------------------*)
(* Some abbreviations                                                        *)
(*---------------------------------------------------------------------------*)

Definition invar_def : invar = invariant regexp_compare
End

Definition dom_def   : dom = fdom regexp_compare
End

Definition range_def : range = frange regexp_compare
End

Definition union_def : union = ounion regexp_compare
End

Definition set_def   : set = oset regexp_compare
End

Definition image_def : image = oimage regexp_compare
End

Definition apply_def : apply = fapply regexp_compare
End

Definition set_of_def : set_of oset = fapply regexp_compare
End

Theorem dom_union[local] :
 !a b.
    invariant regexp_compare a /\ invariant regexp_compare b
    ==>
   (dom (union a b) = (dom a) UNION (dom b))
Proof
 metis_tac [regexp_compare_good,fdom_ounion,dom_def,union_def]
QED

(*---------------------------------------------------------------------------*)
(* Invariants on regexp compilation                                          *)
(*---------------------------------------------------------------------------*)

Definition Brz_invariant_def :
 Brz_invariant seen todo (next_state,state_map,table) <=>
    invar todo /\ invar state_map /\ invar seen /\
    (!r. oin regexp_compare r todo ==> is_normalized r) /\
    (!r. mem_regexp r seen ==> is_normalized r) /\
    (!r. r IN dom state_map ==> is_normalized r) /\
    (dom (union seen todo) = dom state_map) /\
    (range state_map = count next_state) /\
    (set (MAP FST table) = fdom num_cmp (oimage num_cmp (apply state_map) seen)) /\
    fmap_inj regexp_compare state_map /\
    good_table state_map table
End

Theorem triv_lem[local] :
  !s1 s2. (s1 = s2) ==> ((s1 UNION s) = (s2 UNION s))
Proof
 SET_TAC[]
QED

Theorem Brz_inv_pres[local] :
 !todo1 x todos work seen next_state state_map table.
    ~null work /\
    (deleteFindMin work = ((todo1,x),todos)) /\
    Brz_invariant seen work (next_state,state_map,table) /\
    ~mem_regexp todo1 seen
   ==>
   Brz_invariant (insert_regexp todo1 seen)
                 (FOLDL (\work a. insert_regexp (SND a) work) todos (transitions todo1))
                 (build_table (transitions todo1)
                              todo1 (next_state,state_map,table))
Proof
 rw_tac list_ss [good_table_def,insert_regexp_def, invar_def,
                 Brz_invariant_def, build_table_def, transitions_def,set_def] >>
 imp_res_tac extend_states_thm
 >> `todo1 IN dom work`
          by metis_tac [deleteFindMin_thm,EXTENSION,IN_UNION,IN_INSERT,dom_def]
 >> `todo1 IN dom state_map` by metis_tac [dom_union,IN_UNION]
 >> `todo1 IN dom state_map'` by metis_tac [submap_def,dom_def]
 >> pop_assum (strip_assume_tac o SIMP_RULE set_ss [dom_def, fdom_def])
 >> rw []
 >> rw [Brz_invariant_def, good_table_def,invar_def]
 (* 13 subgoals *)
  >- metis_tac [deleteFindMin_thm,invariant_foldl]
  >- metis_tac [insert_thm,regexp_compare_good]
  >- (`MEM r (MAP SND (MAP (\c. (c,smart_deriv c todo1)) ALPHABET)) \/
       oin regexp_compare r todos`
         by metis_tac [oin_foldl_insert,deleteFindMin_thm]
       >- (fs [MEM_MAP,MAP_MAP_o,combinTheory.o_DEF]
           >> match_mp_tac smart_deriv_normalized
           >> `todo1 IN dom work`
                  by metis_tac [deleteFindMin_thm,dom_def]
           >> `oin regexp_compare todo1 work`
                  by metis_tac [oin_fdom,dom_def]
           >> metis_tac [])
       >- (fs [oin_fdom]
           >> `FDOM (to_fmap regexp_compare todos) =
               FDOM (DRESTRICT (to_fmap regexp_compare work)
                        (FDOM (to_fmap regexp_compare work) DELETE
                                key_set regexp_compare todo1))`
               by metis_tac [deleteFindMin,regexp_compare_good]
           >> fs [FDOM_DRESTRICT,INTER_DELETE]
           >> `{r} IN FDOM (to_fmap regexp_compare todos)`
                 by metis_tac[SING_IN_FDOM,eq_cmp_regexp_compare,deleteFindMin_thm]
           >> rfs[]
           >> metis_tac [SING_IN_FDOM,eq_cmp_regexp_compare,deleteFindMin_thm])
     )
  >- metis_tac [member_insert,mem_regexp_def,eq_cmp_regexp_compare,insert_thm,eq_cmp_def]
  >- (`r IN fdom regexp_compare state_map \/
       r IN set (MAP SND (MAP (\c. (c,smart_deriv c todo1)) ALPHABET))`
       by metis_tac [EXTENSION,dom_def,IN_UNION]
       >- metis_tac [dom_def]
       >- (fs [MAP_MAP_o,MEM_MAP] >> metis_tac [smart_deriv_normalized, dom_def]))
  >- (fs [GSYM dom_def] >> qpat_x_assum `dom _ = dom __` (assume_tac o SYM)
       >> rw [GSYM set_def]
       >> `invariant regexp_compare (insert regexp_compare todo1 () seen)`
            by metis_tac [insert_thm,regexp_compare_good]
       >> `dom (insert regexp_compare todo1 () seen) =
           dom (set [todo1]) UNION dom seen`
            by (rw [dom_def,fdom_insert,eq_cmp_regexp_compare,Once INSERT_SING_UNION]
                >> match_mp_tac triv_lem
                >> rw_tac bool_ss [EXTENSION,set_def]
                >> rw [in_dom_oset,eq_cmp_regexp_compare])
       >> `invariant regexp_compare
             (FOLDL (\work' a. insert regexp_compare (SND a) () work') todos
                (MAP (\c. (c,smart_deriv c todo1)) ALPHABET))`
           by metis_tac [invariant_foldl,deleteFindMin_thm]
       >> rw [dom_union]
       >> rw [EXTENSION]
       >> `invariant regexp_compare todos` by metis_tac [deleteFindMin_thm]
       >> rw [oin_foldl_insert |> SIMP_RULE std_ss [oin_fdom,GSYM dom_def]]
       >> rw [AC DISJ_COMM DISJ_ASSOC]
       >> qsuff_tac `x IN dom work <=> (x IN dom (set [todo1]) \/ x IN dom todos)`
           >- metis_tac[]
       >> `dom work = {todo1} UNION dom todos`
            by metis_tac [deleteFindMin_thm,dom_def]
       >> qsuff_tac `{todo1} = dom (set [todo1])`
           >- metis_tac[IN_UNION,EXTENSION]
       >> simp_tac list_ss [dom_def,set_def,dom_oset_lem,eq_cmp_regexp_compare])
  >- (`extend_states_inv next_state state_map ([]:(num,num) alist)`
               by (rw [extend_states_inv_def] >> metis_tac [range_def])
       >> imp_res_tac extend_states_inv
       >> fs [extend_states_inv_def, count_def, EXTENSION, range_def])
  >- (`todo1 IN dom state_map'` by (fs[submap_def] >> metis_tac[dom_def])
      >> `eq_cmp num_cmp /\ eq_cmp regexp_compare`
            by metis_tac[eq_cmp_regexp_compare,num_cmp_good,num_cmp_antisym,eq_cmp_def]
      >> rw [GSYM oinsert_def,fdom_oimage_insert]
      >> `apply state_map' todo1 = x'` by rw [apply_def,fapply_def]
      >> pop_assum SUBST_ALL_TAC
      >> AP_TERM_TAC
      >> `dom seen SUBSET dom state_map` by
           (qpat_x_assum `dom _ = dom state_map` (SUBST_ALL_TAC o SYM)
             >> metis_tac [invariant_oset, eq_cmp_def,dom_union,SUBSET_UNION])
      >> rw[fdom_oimage_inst,SET_EQ_THM,EQ_IMP_THM,oin_fdom]
      >> Q.EXISTS_TAC `x'''` >> rw[]
      >> `x''' IN dom state_map` by metis_tac [SUBSET_DEF,dom_def]
      >> `(x''' IN dom state_map') /\
          (lookup regexp_compare x''' state_map = lookup regexp_compare x''' state_map')`
           by metis_tac [submap_def,dom_def]
      >> rw [apply_def,fapply_def])
  >- (`extend_states_inv next_state state_map ([]:(num,num) alist)`
               by (rw [extend_states_inv_def] >> metis_tac [range_def])
       >> imp_res_tac extend_states_inv
       >> pop_assum mp_tac
       >> rw [extend_states_inv_def])
  >- (rw_tac set_ss [fdom_oimage_inst,GSYM IMP_DISJ_THM,oneTheory.one,
                     oin_fdom,fdom_def,apply_def,fapply_def]
       >> strip_tac
       >> `fmap_inj regexp_compare state_map'`
           by (`extend_states_inv next_state state_map ([]:(num,num) alist)`
                 by (rw [extend_states_inv_def] >> metis_tac [range_def])
               >> imp_res_tac extend_states_inv
               >> pop_assum mp_tac
               >> rw [extend_states_inv_def])
       >> `dom seen SUBSET dom state_map` by
           (`eq_cmp num_cmp /\ eq_cmp regexp_compare`
                by metis_tac[eq_cmp_regexp_compare,
                             num_cmp_good,num_cmp_antisym,eq_cmp_def]
             >> qpat_x_assum `dom _ = dom state_map` (SUBST_ALL_TAC o SYM)
             >> metis_tac [invariant_oset, eq_cmp_def,dom_union,SUBSET_UNION])
       >> pop_assum mp_tac
       >> rw_tac set_ss [dom_def, fdom_def, member_iff_lookup,SUBSET_DEF,oneTheory.one]
       >> Q.EXISTS_TAC `x''` >> rw[]
       >> strip_tac
       >> `x'' IN fdom regexp_compare state_map` by fs [SUBSET_DEF,dom_def, fdom_def]
       >> `(x'' IN fdom regexp_compare state_map') /\
           (lookup regexp_compare x'' state_map = lookup regexp_compare x'' state_map')`
             by (fs [submap_def,fdom_def, member_iff_lookup] >> metis_tac [])
       >> fs []
       >> `x'' <> todo1` by (fs[mem_regexp_def,member_iff_lookup] >> metis_tac[])
       >> metis_tac [fmap_inj_def,eq_cmp_regexp_compare, eq_cmp_def])
  >- (pop_assum mp_tac
        >> rw[MAP_MAP_o,combinTheory.o_DEF]
        >> fs[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF]
        >> metis_tac[])
  >- (qpat_x_assum `(if _ then __ else ___) = ____` mp_tac
        >> rw[MAP_MAP_o,combinTheory.o_DEF]
             >- (imp_res_tac alistTheory.ALOOKUP_MEM
                  >> fs [MEM_REVERSE,MEM_MAP])
             >- metis_tac[])
  >- (qpat_x_assum `(if _ then __ else ___) = ____` mp_tac
        >> rw[MAP_MAP_o,combinTheory.o_DEF]
           >- (qexists_tac `todo1` >> rw[]
                  >> imp_res_tac alistTheory.ALOOKUP_MEM
                  >> pop_assum mp_tac
                  >> rw_tac set_ss [MEM_REVERSE,MEM_MAP,fapply_def]
                  >> `smart_deriv c todo1 IN fdom regexp_compare state_map'`
                      by (rw [MAP_MAP_o,combinTheory.o_DEF,MEM_MAP]
                           >> disj2_tac
                           >> qexists_tac `c` >> rw[]
                           >> metis_tac [IN_DEF])
                  >> fs [fdom_def, member_iff_lookup])
           >- (fs[submap_def, fdom_def, member_iff_lookup] >> metis_tac[]))
QED

Theorem Brz_inv_thm[local] :
 !seen work acc.
   dom_Brz seen work acc
   ==>
    !seen' acc'.
      Brz_invariant seen work acc /\
      (Brzozowski seen work acc = (seen',acc'))
      ==>
       Brz_invariant seen' balanced_map$empty acc'
Proof
 simp_tac std_ss [empty_def]
 >> ho_match_mp_tac Brzozowski_ind
 >> rw []
 >> qpat_x_assum `Brzozowski _ __ ___ = _4` mp_tac
 >> rw [Brzozowski_eqns]
    >- (Cases_on `work` >> fs[null_def])
    >- (`?r work'. deleteFindMin work = ((r,()),work')`
            by metis_tac [ABS_PAIR_THM,oneTheory.one]
        >> fs[]
        >> BasicProvers.NORM_TAC set_ss []
        >> first_x_assum match_mp_tac
        >> rw[]
        >- (qpat_x_assum `Brz_invariant _ _ _` mp_tac
            >> `?next_state state_map table.
                  acc = (next_state,state_map,table)` by metis_tac[ABS_PAIR_THM]
            >> pop_assum subst_all_tac
            >> rw [Brz_invariant_def]
               >- metis_tac [deleteFindMin_thm,invar_def]
               >- metis_tac[deleteFindMin_thm,invar_def,
                            oin_fdom,IN_UNION,IN_INSERT,EXTENSION]
               >- (qpat_x_assum `dom (union seen work) = dom state_map`
                                (subst_all_tac o SYM)
                   >> fs [invar_def,dom_def,union_def, mem_regexp_def,GSYM oin_def]
                   >> `invariant regexp_compare work' /\
                       fdom regexp_compare work =
                       {r} UNION fdom regexp_compare work'`
                       by metis_tac[deleteFindMin_thm,invar_def]
                   >> fs [GSYM oin_fdom,EXTENSION,oin_ounion,good_oset_def,
                          regexp_compare_good]
                   >> metis_tac[]))
        >- metis_tac [Brz_inv_pres,ABS_PAIR_THM])
QED


Theorem Brz_mono[local] :
 !seen work acc.
   dom_Brz seen work acc
   ==>
   !seen' acc'.
     Brz_invariant seen work acc /\
     (Brzozowski seen work acc = (seen',acc'))
     ==>
     submap regexp_compare (FST (SND acc)) (FST(SND acc'))
Proof
 ho_match_mp_tac Brzozowski_ind
 >> rw[]
 >> qpat_x_assum `Brzozowski _ __ ___ = _4` mp_tac
 >> rw [Brzozowski_eqns]
 >> fs []
  >- metis_tac [submap_id]
  >- (`?r work'. deleteFindMin work = ((r,()),work')`
            by metis_tac [ABS_PAIR_THM,oneTheory.one]
      >> fs[]
      >> BasicProvers.NORM_TAC set_ss []
       >- (first_assum match_mp_tac
           >> qexists_tac `seen'` >> rw[]
           >> qpat_x_assum `Brz_invariant seen work acc` mp_tac
           >> `?next_state state_map table.
                     acc = (next_state,state_map,table)` by metis_tac[ABS_PAIR_THM]
           >> pop_assum subst_all_tac
           >> rw [Brz_invariant_def,invar_def]
            >- metis_tac [deleteFindMin_thm]
            >- metis_tac[deleteFindMin_thm,invar_def,
                         oin_fdom,IN_UNION,IN_INSERT,EXTENSION]
            >- (qpat_x_assum `dom (union seen work) = dom state_map`
                             (subst_all_tac o SYM)
                >> fs [invar_def,dom_def,union_def,
                       mem_regexp_def,GSYM oin_def]
                >> `invariant regexp_compare work' /\
                    fdom regexp_compare work =
                    {r} UNION fdom regexp_compare work'`
                          by metis_tac[deleteFindMin_thm,invar_def]
                >> fs [GSYM oin_fdom,EXTENSION,oin_ounion,
                       good_oset_def,regexp_compare_good]
                >> metis_tac[])
          )
       >- (`?next_state state_map table.
               acc = (next_state,state_map,table)` by metis_tac[ABS_PAIR_THM]
           >> pop_assum subst_all_tac
           >> imp_res_tac Brz_inv_pres
           >> fs []
           >> match_mp_tac submap_trans
           >> qexists_tac
              `FST (SND (build_table (transitions r) r
                                     (next_state,state_map,table)))`
           >> fs[]
           >> rw[build_table_def,LET_THM]
           >> `?next_state' state_map' trans'.
                 extend_states next_state state_map [] (transitions r)
                  = (next_state',state_map', trans')`
                by metis_tac[ABS_PAIR_THM]
           >> rw[]
           >> `invariant regexp_compare state_map` by metis_tac [Brz_invariant_def,invar_def]
           >> imp_res_tac extend_states_thm
           >> CASE_TAC
           >> rw[]
           >> match_mp_tac submap_mono
           >> rw[eq_cmp_regexp_compare]
           >> strip_tac
           >> `r IN fdom regexp_compare state_map'` by metis_tac[submap_def]
           >> pop_assum mp_tac
           >> simp_tac set_ss [fdom_def]
           >> metis_tac[NOT_SOME_NONE]))
QED

Theorem Brz_invariant_final[local] :
 !seen next_state state_map table.
   Brz_invariant seen empty (next_state,state_map,table)
    ==>
    (next_state = LENGTH table) /\
    PERM (MAP FST table) (COUNT_LIST (LENGTH table)) /\
    (!x. MEM x (get_accepts state_map) ==> x < LENGTH table) /\
    (!n l c. (ALOOKUP table n = SOME l) /\ (?x. ALOOKUP l c = SOME x) ==> MEM c ALPHABET)
Proof
 simp [Brz_invariant_def,invar_def,set_def,ounion_oempty,union_def] >>
 rpt gen_tac >> strip_tac >> conj_asm1_tac
 >- (`!x. x IN set (MAP FST table) ==> x < next_state`
           by (fs [count_def, EXTENSION, range_def, frange_def,dom_def]
                >> rw [fdom_oimage_inst,apply_def,oin_fdom]
                >> fs [fdom_def,fapply_def]
                >> metis_tac [THE_DEF,ounion_oempty,oempty_def])
     >>
     `LENGTH table = CARD (set (MAP FST table))`
           by metis_tac [LENGTH_MAP,ALL_DISTINCT_CARD_LIST_TO_SET, good_table_def]
     >>
     `fdom num_cmp (oimage num_cmp (apply state_map) seen) = range state_map`
       by (simp_tac set_ss [range_def, frange_def] >>
           qpat_x_assum `dom _ = dom __` mp_tac >>
           rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def, dom_def] >>
           fs[fdom_def,ounion_oempty, GSYM oempty_def,EXTENSION] >>
           metis_tac[THE_DEF])
     >> rw [])
 >> conj_asm1_tac
   >- (match_mp_tac PERM_ALL_DISTINCT
       >> rw [all_distinct_count_list, MEM_COUNT_LIST]
        >- fs [good_table_def]
        >- (`fdom num_cmp (oimage num_cmp (apply state_map) seen) = range state_map`
             by (simp_tac set_ss [range_def, frange_def] >>
                 qpat_x_assum `dom _ = dom __` mp_tac >>
                 simp_tac set_ss [ounion_oempty, GSYM oempty_def] >>
                 rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def, dom_def] >>
                 fs [fdom_def,EXTENSION] >> metis_tac[THE_DEF])
            >> qpat_x_assum `set (MAP FST table) = _` (subst_all_tac o SYM)
            >> rw[]))
 >> conj_tac
 >- (rw [mem_get_accepts]
     >> `x IN range state_map`
           by (simp_tac set_ss [range_def, frange_def] >> metis_tac[])
     >> rfs [count_def])
 >- (rw [] >> fs [good_table_def] >> metis_tac [])
QED


(*---------------------------------------------------------------------------*)
(* table_lang parallels the definition of exec_dfa                           *)
(*---------------------------------------------------------------------------*)

Definition table_lang_def :
  (table_lang final_states table n [] = MEM n final_states) /\
  (table_lang final_states table n (c::t) =
     case ALOOKUP table n of
       | NONE => F
       | SOME table2 =>
           case ALOOKUP table2 c of
             | NONE => F
             | SOME n' => table_lang final_states table n' t)
End

Theorem table_lang_correct[local] :
 !finals table state_map.
   fmap_inj regexp_compare state_map /\
   good_table state_map table /\
   (set (MAP FST table) = frange regexp_compare state_map) /\
   (!n r. (lookup regexp_compare r state_map = SOME n) ==> (MEM n finals <=> nullable r))
   ==>
   !n r s.
     (!c. MEM c s ==> MEM c ALPHABET) /\
     (lookup regexp_compare r state_map = SOME n)
     ==>
     (table_lang finals table n s <=> smart_deriv_matches r (MAP CHR s))
Proof
 rpt gen_tac >>
 strip_tac >>
 Induct_on `s` >>
 rw [table_lang_def, smart_deriv_matches_def] >>
 fs [good_table_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 rw []
 >- (imp_res_tac alistTheory.ALOOKUP_NONE
     >> fs [EXTENSION]
     >> `n NOTIN frange regexp_compare state_map` by metis_tac[]
     >> fs [frange_def])
 >- metis_tac [alistTheory.ALOOKUP_NONE]
 >- (`?r'.(lookup regexp_compare r' state_map = SOME n) /\
          (lookup regexp_compare (smart_deriv h r') state_map =
           SOME x')` by metis_tac []
     >> `table_lang finals table x' s <=>
         smart_deriv_matches (smart_deriv h r') (MAP CHR s)`
         by metis_tac[]
     >> pop_assum SUBST_ALL_TAC
     >> `r' = r`
         by (qpat_x_assum `fmap_inj _ __` mp_tac
              >> rw_tac set_ss [fmap_inj_def,fdom_def,regexp_compare_eq])
     >> rw []
     >> metis_tac [ORD_CHR_lem,mem_alphabet])
QED

Theorem vec_lang_lem1[local] :
 !(n:num).
    MEM n finals_list <=> (ALOOKUP (MAP (\x. (x,T)) finals_list) n = SOME T)
Proof
 rw [EQ_IMP_THM]
  >- rw [alistTheory.ALOOKUP_TABULATE]
  >- (`MEM (n,T) (MAP (\x. (x,T)) finals_list)` by METIS_TAC [alistTheory.ALOOKUP_MEM]
      >> fs[MEM_MAP])
QED

Theorem vec_lang_lem2 =
  alistTheory.alookup_stable_sorted
     |> Q.INST_TYPE [`:'a` |-> `:num`, `:'b` |-> `:(num, 'a) alist`]
     |> Q.SPECL [`$<=`, `mergesort`, `n`, `table`]
     |> SIMP_RULE (srw_ss()++ARITH_ss) [transitive_def, total_def, mergesort_STABLE_SORT];

Theorem vec_lang_lem3 =
  alistTheory.alookup_stable_sorted
     |> Q.INST_TYPE [`:'a` |-> `:num`, `:'b` |-> `:'a option`]
     |> Q.SPECL [`$<=`, `mergesort`, `n`, `MAP (\(c,n). (c,SOME n)) table2`]
     |> SIMP_RULE (srw_ss()++ARITH_ss)
           [transitive_def, total_def, mergesort_STABLE_SORT, stringTheory.char_le_def];

Theorem vec_lang_lem4[local] :
 !l x. ALOOKUP (MAP (\(c,n). (c,SOME n)) l) x = OPTION_MAP SOME (ALOOKUP l x)
Proof
 Induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 rw [] >>
 fs [stringTheory.ORD_11]
QED


Theorem table_to_vec_thm[local] :
 !table final_states max_char max_state table' final_states'.
    (max_char = alphabet_size) /\
    SORTED $<= final_states /\
    (!x. MEM x final_states ==> x < max_state) /\
    (!n l c. (ALOOKUP table n = SOME l) /\
             (?x. ALOOKUP l c = SOME x) ==> c < max_char) /\
    PERM (MAP FST table) (COUNT_LIST (LENGTH table)) /\
    (table_to_vectors table = table') /\
    (accepts_to_vector final_states max_state = final_states')
  ==>
   (LENGTH table' = LENGTH table) /\
   (LENGTH final_states' = max_state) /\
   (!n. MEM n final_states <=> n < LENGTH final_states' /\ EL n final_states') /\
   (!n. (?l. ALOOKUP table n = SOME l) <=> n < LENGTH table') /\
   (!n l. n < LENGTH table' ==> (LENGTH (EL n table') = max_char)) /\
   (!n c x.
     (?l. (ALOOKUP table n = SOME l) /\ (ALOOKUP l c = SOME x)) <=>
     n < LENGTH table' /\
     c < LENGTH (EL n table') /\ (EL c (EL n table') = SOME x))
Proof
 simp [good_table_def, table_to_vectors_def,accepts_to_vector_def] >>
 rpt gen_tac >>
 strip_tac >>
 qabbrev_tac `sorted_table = mergesort (inv_image $<= FST) table` >>
 `LENGTH sorted_table = LENGTH table` by metis_tac [mergesort_perm, PERM_LENGTH] >>
 `SORTS mergesort (inv_image $<= (FST : num # (num,'a) alist -> num))`
          by metis_tac [mergesort_STABLE_SORT, STABLE_DEF,
                        leq_thm, total_inv_image, transitive_inv_image] >>
 `MAP FST sorted_table = COUNT_LIST (LENGTH table)`
            by (match_mp_tac sorted_perm_count_list >>
                fs [SORTS_DEF] >>
                rw [] >>
                metis_tac [PERM_TRANS, PERM_SYM, PERM_MAP]) >>
 simp [] >>
 conj_tac
 >- metis_tac[mergesort_perm,PERM_LENGTH] >>
 conj_tac
 >- (`SORTED $<= (MAP FST (MAP (\x.(x,T)) final_states))`
            by rw [MAP_MAP_o, combinTheory.o_DEF]
      >> metis_tac [alist_to_vec_thm]) >>
 conj_tac
 >- (`SORTED $<= (MAP FST (MAP (\x.(x,T)) final_states))`
            by rw [MAP_MAP_o, combinTheory.o_DEF]
     >> `LENGTH (alist_to_vec (MAP (\x. (x,T)) final_states)
                              F max_state max_state) = max_state`
           by METIS_TAC [alist_to_vec_thm]
    >> POP_ASSUM SUBST_ALL_TAC
    >> RW_TAC std_ss [EQ_IMP_THM]
       >- (`n < max_state` by METIS_TAC [] >>
           `ALOOKUP (MAP (\x. (x,T)) final_states) n = SOME T`
               by METIS_TAC [vec_lang_lem1] >> METIS_TAC [alist_to_vec_thm])
       >- (CCONTR_TAC >> fs []
           >> Cases_on `ALOOKUP (MAP (\x. (x,T)) final_states) n`
              >- (metis_tac [alist_to_vec_thm, vec_lang_lem1])
              >- (NTAC 2 (POP_ASSUM MP_TAC) >> rw [vec_lang_lem1]
                  >> DISCH_TAC >> fs[] >> rw[] >> metis_tac [alist_to_vec_thm])))
 >>
 conj_asm1_tac
 >- (rw [] >> eq_tac >> rw []
     >- (imp_res_tac alistTheory.ALOOKUP_MEM >>
         imp_res_tac MEM_PERM >>
         fs [MEM_MAP, MEM_COUNT_LIST] >>
         metis_tac [FST,mergesort_perm,PERM_LENGTH])
     >- (`ALOOKUP sorted_table n = SOME (EL n (MAP SND sorted_table))`
             by metis_tac [dense_alist_to_vec_thm,
                   LENGTH_COUNT_LIST,mergesort_perm,PERM_LENGTH] >>
         `ALOOKUP table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [vec_lang_lem2] >>
         rw [])) >>
 `SORTS mergesort (inv_image $<= (FST : num # 'a option -> num))`
          by metis_tac [mergesort_STABLE_SORT, STABLE_DEF, leq_thm,
                        total_inv_image, transitive_inv_image] >>
 `(\a b:num. a <= b) = $<=` by metis_tac [] >> pop_assum SUBST_ALL_TAC >>
 simp [EL_MAP,length_mergesort] >>
 conj_tac
 >- (rw [] >>
     `?n' table2'. EL n sorted_table = (n',table2')`
          by metis_tac [pair_CASES] >> rw [] >>
     qabbrev_tac `sorted_table2 =
         mergesort (inv_image $<= FST) (MAP (\(c,n). (c,SOME n)) table2')` >>
     qabbrev_tac `table2 = EL n (MAP SND sorted_table)` >>
     `SORTED $<= (MAP FST sorted_table2)`
             by (fs [SORTS_DEF, sorted_map, leq_thm] >> metis_tac []) >>
     metis_tac [alist_to_vec_thm])
 >- (* last conjunct *)
 (fs [length_mergesort] >>
  rw [] >>  eq_tac >>  strip_tac >> res_tac >> simp [EL_MAP] >>
 `?n' table2'. EL n sorted_table = (n',table2')` by metis_tac [pair_CASES] >>
 rw [] >>
 qabbrev_tac `sorted_table2 =
      mergesort (inv_image $<= FST) (MAP (\(c,n). (c,SOME n)) table2')` >>
 qabbrev_tac `table2 = EL n (MAP SND sorted_table)` >>
 `SORTED $<= (MAP FST sorted_table2)`
         by (fs [SORTS_DEF, sorted_map, leq_thm] >> metis_tac [])
 >- metis_tac [alist_to_vec_thm]
 >- (imp_res_tac alist_to_vec_thm >>
     fs [AND_IMP_INTRO] >>
     FIRST_X_ASSUM match_mp_tac >>  rw [] >>
     `table2' = table2` by (UNABBREV_ALL_TAC >> rw [EL_MAP]) >> rw [] >>
     `ALOOKUP sorted_table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [dense_alist_to_vec_thm, LENGTH_COUNT_LIST] >>
     `ALOOKUP table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [vec_lang_lem2] >>
     rw [] >>
     fs [] >>
     `ALOOKUP (MAP (\(c,n). (c,SOME n)) table2) c = SOME (SOME x)`
              by metis_tac [vec_lang_lem4, OPTION_MAP_DEF] >>
     fs [Once (GSYM vec_lang_lem3)] >>
     metis_tac [NOT_SOME_NONE, alist_to_vec_thm])
 >- (REV_FULL_SIMP_TAC std_ss [EL_MAP] >>
     `table2' = table2` by (UNABBREV_ALL_TAC >> rw [EL_MAP]) >> fs [] >>
     res_tac >> simp [] >>
     Cases_on `ALOOKUP sorted_table2 c`
     >- (`ALOOKUP (MAP (\(c,n). (c,SOME n)) table2) c = NONE`
          by metis_tac [vec_lang_lem4, OPTION_MAP_DEF, vec_lang_lem3] >>
         metis_tac [NOT_SOME_NONE, alist_to_vec_thm])
    >- (`ALOOKUP sorted_table n = SOME (EL n (MAP SND sorted_table))`
           by metis_tac [dense_alist_to_vec_thm, LENGTH_COUNT_LIST] >>
        `ALOOKUP table n = SOME (EL n (MAP SND sorted_table))`
           by metis_tac [vec_lang_lem2] >>
        rw [] >>
        REV_FULL_SIMP_TAC std_ss [EL_MAP] >>
        `SOME x = x'` by metis_tac [SOME_11, alist_to_vec_thm] >>
        simp [] >>
        qunabbrev_tac `sorted_table2` >>
        fs [Once vec_lang_lem3] >>
        fs [vec_lang_lem4])))
QED


(*---------------------------------------------------------------------------*)
(* Well-formedness of final state vector                                     *)
(*---------------------------------------------------------------------------*)

Definition good_vec_def :
 good_vec vec final_states
      <=>
    (!l c. MEM c ALPHABET /\ MEM l vec ==> c < LENGTH l) /\
    (!n1 c n2 l. n1 < LENGTH vec /\ (EL n1 vec = l) /\
                 c < LENGTH (EL n1 vec) /\
                 (EL c (EL n1 vec) = SOME n2) ==> n2 < LENGTH vec) /\
    (LENGTH final_states = LENGTH vec)
End


Theorem Brz_inv_to_good_vec[local] :
 !seen next_state state_map table.
   Brz_invariant seen empty (next_state,state_map,table) /\
    (table_to_vectors table = vec) /\
    (accepts_to_vector (get_accepts state_map) next_state = final_states)
    ==>
    (next_state = LENGTH table) /\
    good_vec vec final_states /\
    (!r n. (lookup regexp_compare r state_map = SOME n) ==> n < LENGTH vec)
Proof
 simp [good_vec_def]
  >> rpt gen_tac >> strip_tac
  >> imp_res_tac Brz_invariant_final
  >> fs [Brz_invariant_def,invar_def,
        ounion_oempty,GSYM oempty_def,union_def, set_def, oset_def]
  >>
  `(LENGTH vec = LENGTH table) /\
   (LENGTH final_states = LENGTH table) /\
   (!n. MEM n (get_accepts state_map) <=> n < LENGTH final_states /\ EL n final_states) /\
   (!n. (?l. ALOOKUP table n = SOME l) <=> n < LENGTH vec) /\
   (!n l. n < LENGTH vec ==> (LENGTH (EL n vec) = alphabet_size)) /\
   (!n c x.
     (?l. (ALOOKUP table n = SOME l) /\ (ALOOKUP l c = SOME x))
     <=>
       n < LENGTH vec /\ c < LENGTH (EL n vec) /\
       (EL c (EL n vec) = SOME x))`
     by
      (match_mp_tac table_to_vec_thm
        >> rw [sorted_get_accepts]
        >> metis_tac [mem_alphabet,alphabet_size_def])
  >> rw []
 >- (fs [MEM_EL] >> rw []
      >> metis_tac [EL_MEM,mem_alphabet,alphabet_size_def])
 >- (`!a. a < LENGTH table <=> MEM a (MAP FST table)`
        by metis_tac [MEM_PERM,MEM_COUNT_LIST]
      >> rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def,SYM dom_def]
      >> rw [dom_def,fdom_def, member_iff_lookup]
      >> metis_tac [good_table_def,THE_DEF])
 >- (`!a. a < LENGTH table <=> MEM a (MAP FST table)`
        by metis_tac [MEM_PERM,MEM_COUNT_LIST]
       >> rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def,SYM dom_def]
       >> simp_tac set_ss [dom_def,fdom_def, member_iff_lookup]
       >> metis_tac [THE_DEF])
QED

Theorem compile_regexp_good_vec :
 !r state_map table final_states.
    dom_Brz empty (singleton (normalize r) ())
                 (1,singleton (normalize r) 0,[]) /\
    (compile_regexp r = (state_map, table, final_states))
    ==>
    good_vec table final_states /\
    (!r n. (lookup regexp_compare r state_map = SOME n) ==> n < LENGTH table) /\
    normalize r IN fdom regexp_compare state_map
Proof
 simp [compile_regexp_def]
  >> rpt gen_tac >> strip_tac
  >> fs []
  >> `?seen next_state state_map table.
         Brzozowski empty
               (singleton (normalize r) ())
               (1,singleton (normalize r) 0,[]) = (seen,next_state,state_map,table)`
       by metis_tac [pair_CASES]
  >> fs []
  >> `Brz_invariant empty (singleton (normalize r) ()) (1,singleton (normalize r) 0,[])`
     by
      (fs [Brz_invariant_def,invar_def,dom_def, normalize_thm, fmap_inj_def, good_table_def,
          singleton_thm,empty_def,invariant_def,mem_regexp_def,member_iff_lookup]
        >> rw [lookup_def]
           >- (fs[singleton_def,oin_def,member_def]
                >> BasicProvers.EVERY_CASE_TAC
                >- metis_tac[]
                >- metis_tac[eq_cmp_regexp_compare,eq_cmp_def,normalize_thm]
                >- metis_tac[])
           >- (fs [fdom_def, singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw []
                >> metis_tac [eq_cmp_regexp_compare, eq_cmp_def,normalize_thm])
           >- (rw [union_def,set_def,GSYM empty_def, GSYM oempty_def] >>
               rw [EXTENSION,fdom_def, osingleton_def, singleton_def, lookup_def] >>
               CASE_TAC)
           >- (rw [range_def,frange_def, EXTENSION, singleton_def,lookup_def,EQ_IMP_THM]
                >- (BasicProvers.EVERY_CASE_TAC >> rw [])
                >- (Q.EXISTS_TAC `normalize r` >> rw [regexp_compare_id] >> decide_tac))
           >- (rw [GSYM empty_def, GSYM oempty_def]
               >> rw [fdom_def, lookup_def, empty_def, oempty_def])
           >- (ntac 2 (pop_assum mp_tac)
                >> simp_tac set_ss [fdom_def,singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw[]
                >> metis_tac [eq_cmp_def, eq_cmp_regexp_compare]))
 >> imp_res_tac Brz_inv_thm
 >> imp_res_tac Brz_mono
 >> imp_res_tac Brz_inv_to_good_vec
 >> fs []
 >> rw []
    >- metis_tac []
    >- (`normalize r IN fdom regexp_compare (singleton (normalize r) 0)`
         by rw [submap_def,fdom_def,singleton_def,lookup_def,regexp_compare_id]
         >> metis_tac [submap_def])
QED

Theorem vec_lang_correct :
 !table final_states max_char vec final_states'.
   (max_char = alphabet_size) /\
   SORTED $<= final_states /\
   (!x. MEM x final_states ==> x < LENGTH table) /\
   (!n l c. (ALOOKUP table n = SOME l) /\ (?x. ALOOKUP l c = SOME x) ==> c < max_char) /\
   (PERM (MAP FST table) (COUNT_LIST (LENGTH table))) /\
   (!n'. n' IN BIGUNION (IMAGE alist_range (alist_range table)) ==> n' < LENGTH table) /\
   (table_to_vectors table = vec) /\
   (accepts_to_vector final_states (LENGTH table) = final_states')
   ==>
   !n s. (!c. MEM c s ==> c < max_char) /\ n < LENGTH table
         ==>
        (table_lang final_states table n s
           <=>
         exec_dfa (fromList final_states')
                  (fromList (MAP fromList vec))
                  n
                  (MAP CHR s))
Proof
 rpt gen_tac
  >> strip_tac
  >> `(LENGTH vec = LENGTH table) /\
      (LENGTH final_states' = LENGTH table) /\
      (!n. MEM n final_states <=> n < LENGTH final_states' /\ EL n final_states') /\
      (!n. (?l. ALOOKUP table n = SOME l) <=> n < LENGTH vec) /\
      (!n l. n < LENGTH vec ==> (LENGTH (EL n vec) = max_char)) /\
      (!n c x.
        (?l. (ALOOKUP table n = SOME l) /\ (ALOOKUP l c = SOME x))
        <=>
        n < LENGTH vec /\ c < LENGTH (EL n vec) /\
        (EL c (EL n vec) = SOME x))`
        by (match_mp_tac table_to_vec_thm
             >> rw []
             >> metis_tac [])
  >> Induct_on `s`
  >> rw [table_lang_def, exec_dfa_thm,fromList_Vector,sub_def]
  >> `h < alphabet_size` by metis_tac []
  >> rw [ORD_CHR_lem]
  >> BasicProvers.EVERY_CASE_TAC
  >> fs []
     >- metis_tac [NOT_SOME_NONE]
     >- (`n < LENGTH (table_to_vectors table)` by metis_tac[]
         >> fs [EL_MAP,sub_def]
         >> metis_tac [SOME_11, NOT_SOME_NONE])
     >- (`n < LENGTH (table_to_vectors table)` by metis_tac[]
         >> fs [EL_MAP,sub_def]
         >> metis_tac [NOT_SOME_NONE])
     >- (`n < LENGTH (table_to_vectors table)` by metis_tac[]
         >> fs [EL_MAP,sub_def]
         >> `x' = x''` by metis_tac [SOME_11, NOT_SOME_NONE]
          >> rw []
          >> fs [fromList_Vector]
          >> FIRST_X_ASSUM match_mp_tac
          >> FIRST_X_ASSUM match_mp_tac
          >> rw [PULL_EXISTS]
          >> rw [alistTheory.alist_range_def, EXTENSION]
          >> metis_tac [])
QED


(*---------------------------------------------------------------------------*)
(* Main correctness theorem: strings accepted by DFA are just the strings    *)
(* specified by regexp r                                                     *)
(*---------------------------------------------------------------------------*)

Theorem Brzozowski_correct :
 !r s.
   dom_Brz empty (singleton (normalize r) ())
           (1,singleton (normalize r) 0,[]) /\
   (!c. MEM c s ==> MEM (ORD c) ALPHABET)
   ==>
   (Brz_lang r s = regexp_lang (normalize r) s)
Proof
 rw [GSYM regexp_lang_smart_deriv, Brz_lang_def]
  >> UNABBREV_ALL_TAC
  >> fs [compile_regexp_def]
  >> `?seen next_state state_map table.
        Brzozowski empty (singleton (normalize r) ())
                  (1,singleton (normalize r) 0,[]) = (seen,next_state,state_map,table)`
       by metis_tac [pair_CASES,SND]
  >> fs [LET_THM]
  >> rw []
  >> `Brz_invariant empty (singleton (normalize r) ())
                   (1,singleton (normalize r) 0,[])`
      by (rw_tac set_ss [Brz_invariant_def,invar_def,dom_def, normalize_thm,
                      fmap_inj_def, good_table_def, singleton_thm,empty_def,
                      invariant_def,mem_regexp_def,member_iff_lookup]
           >- (fs[singleton_def,oin_def,member_def]
                >> BasicProvers.EVERY_CASE_TAC
                >- metis_tac[]
                >- metis_tac[eq_cmp_regexp_compare,eq_cmp_def,normalize_thm]
                >- metis_tac[])
           >- fs [lookup_def]
           >- (fs [fdom_def, singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw []
                >> metis_tac [eq_cmp_regexp_compare, eq_cmp_def,normalize_thm])
           >- (rw [union_def,set_def,GSYM empty_def, GSYM oempty_def] >>
               rw [EXTENSION,fdom_def, osingleton_def, singleton_def, lookup_def] >>
               CASE_TAC)
           >- (rw [range_def,frange_def, EXTENSION, singleton_def,lookup_def,EQ_IMP_THM]
                >- (BasicProvers.EVERY_CASE_TAC >> rw [])
                >- (Q.EXISTS_TAC `normalize r` >> rw [regexp_compare_id] >> decide_tac))
           >- (rw [GSYM empty_def, GSYM oempty_def]
               >> rw [fdom_def, lookup_def, empty_def, oempty_def])
           >- (ntac 2 (pop_assum mp_tac)
                >> simp_tac set_ss [fdom_def,singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw[]
                >> metis_tac [eq_cmp_def, eq_cmp_regexp_compare])
           >- fs [alistTheory.ALOOKUP_def]
           >- fs [alistTheory.ALOOKUP_def]
           >- fs [alistTheory.ALOOKUP_def])
 >> imp_res_tac Brz_inv_thm
 >> imp_res_tac Brz_mono
 >> imp_res_tac Brz_invariant_final
 >> fs [Brz_invariant_def]
 >> `smart_deriv_matches (normalize r) s
      <=>
     table_lang (get_accepts state_map) table (apply state_map (normalize r)) (MAP ORD s)`
     by (fs [invar_def,set_def,ounion_oempty,union_def]
          >> `fdom num_cmp (oimage num_cmp (apply state_map) seen)
               = frange regexp_compare state_map`
                    by (simp_tac set_ss [frange_def] >>
                        qpat_x_assum `dom _ = dom __` mp_tac >>
                        rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def, dom_def] >>
                        fs[ounion_oempty, GSYM oempty_def] >>
                        simp_tac set_ss [fdom_def] >> metis_tac[THE_DEF])
          >> mp_tac (table_lang_correct
                   |> INST_TYPE [alpha |-> ``:num``]
                   |> Q.SPEC `get_accepts state_map`
                   |> Q.SPEC `table:(num,(num,num)alist)alist`
                   |> Q.SPEC `state_map:(regexp,num)balanced_map`)
          >> fs[]
          >> `(!n r. (lookup regexp_compare r state_map = SOME n) ==>
                     (MEM n (get_accepts state_map) <=> nullable r))`
               by (rw [mem_get_accepts,EQ_IMP_THM]
                    >- (`r' IN fdom regexp_compare state_map` by rw [fdom_def]
                         >> metis_tac [fmap_inj_def, eq_cmp_regexp_compare, eq_cmp_def])
                    >- metis_tac[])
          >> rw []
          >> pop_assum mp_tac
          >> imp_res_tac string_to_numlist
          >> DISCH_THEN (assume_tac o Q.SPECL [`0n`, `normalize r`, `nl`])
          >> rfs[]
          >> rw[]
          >> `normalize r IN fdom regexp_compare (singleton (normalize r) 0)`
                by (rw [fdom_def, singleton_def,lookup_def,EQ_IMP_THM]
                     >> BasicProvers.EVERY_CASE_TAC
                     >> fs [regexp_compare_id])
          >> `normalize r IN fdom regexp_compare state_map /\
              (lookup regexp_compare (normalize r) (singleton (normalize r) 0) =
               lookup regexp_compare (normalize r) state_map)`
              by metis_tac [submap_def]
          >> fs [singleton_def,lookup_def,regexp_compare_id]
          >> qpat_x_assum `table_lang (get_accepts state_map) table 0 nl <=>
                         smart_deriv_matches (normalize r) (MAP CHR nl)`
             (SUBST_ALL_TAC o SYM)
          >> rw [MAP_MAP_o,combinTheory.o_DEF,apply_def, fapply_def]
          >> pop_assum (SUBST_ALL_TAC o SYM)
          >> rw []
          >> `MAP (\x. ORD (CHR x)) nl = MAP (\x.x) nl`
              by (irule MAP_CONG >> rw [] >> metis_tac [mem_alphabet,ORD_CHR_lem])
         >> rw[])
 >> rw []
 >> imp_res_tac string_to_numlist
 >> rw [MAP_MAP_o,combinTheory.o_DEF,apply_def, fapply_def]
 >> `MAP (\x. ORD (CHR x)) nl = MAP (\x.x) nl`
              by (irule MAP_CONG >> rw [] >> metis_tac [mem_alphabet,ORD_CHR_lem])
 >> rw []
 >> match_mp_tac (GSYM (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] vec_lang_correct))
 >> rw []
    >- rw [sorted_get_accepts]
    >- metis_tac [mem_alphabet]
    >- (fs [good_table_def, alistTheory.alist_range_def]
         >> res_tac
         >> `n'' IN range state_map`
              by (simp_tac set_ss [range_def, frange_def] >> metis_tac[])
         >> `n'' IN count (LENGTH table)` by metis_tac [EXTENSION]
         >> metis_tac [IN_COUNT])
   >- metis_tac [mem_alphabet]
   >- (`normalize r IN fdom regexp_compare (singleton (normalize r) 0)`
          by (rw [fdom_def, singleton_def,lookup_def,EQ_IMP_THM]
               >> BasicProvers.EVERY_CASE_TAC
               >> fs [regexp_compare_id])
        >> `normalize r IN fdom regexp_compare state_map /\
            (lookup regexp_compare (normalize r) state_map =
             lookup regexp_compare (normalize r) (singleton (normalize r) 0))`
               by metis_tac [submap_def]
        >> rw [singleton_def,lookup_def,regexp_compare_id]
        >> `0n IN range state_map`
              by (simp_tac set_ss [range_def, frange_def]
                    >> Q.EXISTS_TAC `normalize r`
                    >> rw [singleton_def,lookup_def,EQ_IMP_THM]
                    >> CASE_TAC
                    >> fs [regexp_compare_id])
        >> `0n IN count (LENGTH table)` by metis_tac [EXTENSION]
        >> metis_tac [IN_COUNT])
QED

Theorem Brzozowski_correct_alt :
 !r s.
    dom_Brz empty (singleton (normalize r) ())
            (1,singleton (normalize r) 0,[]) /\
    (!c. MEM c s ==> MEM (ORD c) ALPHABET)
   ==>
   (regexp_matcher r s = regexp_lang r s)
Proof
 rw []
  >> `Brz_lang r s = regexp_lang r s`
      by metis_tac [regexp_lang_normalize,Brzozowski_correct]
  >> pop_assum (SUBST_ALL_TAC o SYM)
  >> rw [Brz_lang_def, regexp_matcher_def, LET_THM,apply_def,fapply_def]
QED

Theorem Brzozowski_partial_eval :
 !r state_numbering delta accepts deltaV acceptsV start_state.
    (compile_regexp r = (state_numbering,delta,accepts)) /\
    (deltaV = fromList (MAP fromList delta)) /\
    (acceptsV = fromList accepts) /\
    (lookup regexp_compare (normalize r) state_numbering = SOME start_state) /\
    dom_Brz empty (singleton (normalize r) ())
                  (1,singleton (normalize r) 0,[])
    ==>
    !s. EVERY (\c. MEM (ORD c) ALPHABET) s
    ==>
    (exec_dfa acceptsV deltaV start_state s = regexp_lang r s)
Proof
 rw [EVERY_MEM]
  >> `regexp_matcher r s = regexp_lang r s`
      by metis_tac [Brzozowski_correct_alt]
  >> pop_assum (SUBST_ALL_TAC o SYM)
  >> rw [regexp_matcher_def, LET_THM]
QED


Theorem Brzozowski_partial_eval_conseq :
 !r state_numbering delta accepts deltaV acceptsV start_state.
    (compile_regexp r = (state_numbering,delta,accepts)) /\
    (deltaV = fromList (MAP fromList delta)) /\
    (acceptsV = fromList accepts) /\
    (lookup regexp_compare (normalize r) state_numbering = SOME start_state) /\
    dom_Brz_alt empty (singleton (normalize r) ())
    ==>
    !s. EVERY (\c. ORD c < alphabet_size) s
    ==>
    (exec_dfa acceptsV deltaV start_state s = regexp_lang r s)
Proof
 metis_tac[Brzozowski_partial_eval,all_ord_string,
           dom_Brz_alt_equal,all_ord_string]
QED

(*---------------------------------------------------------------------------*)
(* Eliminate check that all chars in string are in alphabet. This can be     *)
(* be done when alphabet = [0..255]                                          *)
(*---------------------------------------------------------------------------*)

Theorem Brzozowski_partial_eval_256 =
  if Regexp_Type.alphabet_size = 256 then
   SIMP_RULE list_ss [ORD_BOUND,alphabet_size_def] Brzozowski_partial_eval_conseq
  else TRUTH;


Theorem regexp_matcher_correct:
   dom_Brz_alt empty (singleton (normalize r) ()) ==>
               (regexp_matcher r s <=> s IN regexp_lang r)
Proof
  rw[regexp_matcher_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac compile_regexp_good_vec
  \\ rfs[dom_Brz_alt_equal,fdom_def]
  \\ imp_res_tac Brzozowski_partial_eval_256
  \\ simp[IN_DEF]
QED

(* val _ = EmitTeX.tex_theory"-"; *)

val _ = export_theory();
