(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(* Originated from Konrad Slind, tweaked by MJCG for Accellera PSL SEREs     *)
(* An automata-based matcher added by Joe Hurd                               *)
(*---------------------------------------------------------------------------*)

(*
app load
["bossLib", "rich_listTheory", "metisLib", "pred_setTheory", "regexpTheory"];
*)

open HolKernel Parse boolLib;
open bossLib metisLib pairTheory combinTheory listTheory rich_listTheory
     pred_setTheory arithmeticTheory;
open regexpTheory;

val () = new_theory "matcher";

(*---------------------------------------------------------------------------*)
(* Symbolic tacticals.                                                       *)
(*---------------------------------------------------------------------------*)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;

fun FULL_CONV_TAC c =
  CONV_TAC c THEN POP_ASSUM_LIST (EVERY o map (ASSUME_TAC o CONV_RULE c) o rev);

local
  val prover = METIS_TAC [ABS_PAIR_THM];

  fun rewriter th =
    FULL_SIMP_TAC bool_ss [th]
    THEN FULL_CONV_TAC (DEPTH_CONV pairLib.let_CONV);
in
  fun INTRODUCE_TAC tm =
    let
      val (l,r) = dest_eq tm
      val assumer = if is_var l then K ALL_TAC else ASSUME_TAC
      val vs = free_vars r
    in
      (KNOW_TAC (list_mk_exists (vs,tm)) THEN1 prover)
      THEN STRIP_TAC
      THEN POP_ASSUM (fn th => rewriter th THEN assumer th)
    end;
end;
  
val Introduce = Q_TAC INTRODUCE_TAC;

val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;

(*---------------------------------------------------------------------------*)
(* Misc. theorems                                                            *)
(*---------------------------------------------------------------------------*)

val NO_MEM = prove
  (``!l. (!x. ~MEM x l) = (l = [])``,
   Cases ++ RW_TAC std_ss [MEM] ++ METIS_TAC []);

val set_of_list_def = Define
  `(set_of_list [] = {}) /\
   (set_of_list (h :: t) = h INSERT set_of_list t)`;

val set_of_list = prove
  (``!l x. x IN set_of_list l = MEM x l``,
   Induct ++ RW_TAC std_ss [set_of_list_def, MEM, NOT_IN_EMPTY, IN_INSERT]);

(*---------------------------------------------------------------------------*)
(* BIGLIST is designed to speed up evaluation of very long lists.            *)
(*---------------------------------------------------------------------------*)

val drop_def = pureDefine
  `(drop 0 l = l) /\
   (drop (SUC i) l = if NULL l then [] else drop i (TL l))`;

val BIGLIST_def = Define `BIGLIST l = drop 0 l`;

val drop_nil = prove
  (``!i. drop i [] = []``,
   Induct ++ RW_TAC std_ss [NULL_DEF, drop_def]);

val null_drop = store_thm
  ("null_drop",
   ``!i l. NULL (drop i l) = LENGTH l <= i``,
   Induct
   >> (RW_TAC arith_ss [drop_def] ++ METIS_TAC [LENGTH_NIL, NULL_EQ_NIL])
   ++ Cases_on `l`
   ++ RW_TAC arith_ss [drop_def, LENGTH, NULL_DEF, TL]);

val tl_drop = store_thm
  ("tl_drop",
   ``!i l.
       TL (drop i l) = if i < LENGTH l then drop (SUC i) l else TL (drop i l)``,
   Induct
   >> (RW_TAC arith_ss [drop_def, NULL_EQ_NIL]
       ++ FULL_SIMP_TAC arith_ss [LENGTH])
   ++ Cases_on `l`
   ++ RW_TAC arith_ss [drop_def, LENGTH, NULL_EQ_NIL, TL]
   ++ Q.PAT_ASSUM `!l. P l` (fn th => ONCE_REWRITE_TAC [th])
   ++ FULL_SIMP_TAC arith_ss [LENGTH, drop_def, NULL_EQ_NIL]);

val head_drop = store_thm
  ("head_drop",
   ``!i l h t. (drop i l = h :: t) ==> (HD (drop i l) = h)``,
   RW_TAC std_ss [HD]);

val tail_drop = store_thm
  ("tail_drop",
   ``!l i h t. (drop i l = h :: t) ==> (drop (SUC i) l = t)``,
   Induct >> RW_TAC bool_ss [drop_def, drop_nil]
   ++ RW_TAC std_ss [drop_def, TL, NULL, drop_nil]
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `i`
   ++ RW_TAC std_ss [drop_def, NULL_EQ_NIL, TL]);

val length_drop = store_thm
  ("length_drop",
   ``!i l h. (drop i l = [h]) ==> (LENGTH l = SUC i)``,
   Induct >> RW_TAC arith_ss [drop_def, LENGTH]
   ++ Cases
   ++ RW_TAC std_ss [drop_def, TL, NULL_EQ_NIL, drop_nil, LENGTH]);

(*---------------------------------------------------------------------------*)
(* Non-deterministic and deterministic automata.                             *)
(*---------------------------------------------------------------------------*)

val () = type_abbrev ("na", Type`:'a # ('a->'b->'a->bool) # ('a->bool)`);
val () = type_abbrev ("da", Type`:'a # ('a->'b->'a) # ('a->bool)`);

val initial_def    = Define `initial    ((i,trans,acc) : ('a,'b) na) = i`;
val transition_def = Define `transition ((i,trans,acc) : ('a,'b) na) = trans`;
val accept_def     = Define `accept     ((i,trans,acc) : ('a,'b) na) = acc`;

val na_step_def = Define
  `(na_step ((i,trans,acc) : ('a,'b) na) s [] = (acc s)) /\
   (na_step (i,trans,acc) s (h :: t) =
    ?s'. trans s h s' /\ na_step (i,trans,acc) s' t)`;

val na_accepts_def = Define
  `na_accepts (i,trans,acc) l = na_step (i,trans,acc) i l`;

val da_step_def = Define
  `(da_step ((i,trans,acc) : ('a,'b) da) s [] = acc s) /\
   (da_step (i,trans,acc) s (h :: t) =
    da_step (i,trans,acc) (trans s h) t)`;

val da_accepts_def = Define
  `da_accepts (i,trans,acc) l = da_step (i,trans,acc) i l`;

val na2da_def = Define
  `na2da (n : ('a,'b) na) =
   ({initial n},
    (\s c. {y | ?x. x IN s /\ transition n x c y}),
    (\s. ?x. x IN s /\ accept n x))`;

val na2da_lemma = prove
  (``!n s l. da_step (na2da n) s l = ?x. x IN s /\ na_step n x l``,
   RW_TAC std_ss []
   ++ Introduce `n = (i,trans,acc)`
   ++ RW_TAC std_ss [na2da_def, initial_def, transition_def, accept_def]
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ Induct_on `l`
   >> (RW_TAC std_ss [da_step_def, na_step_def, IN_SING]
       ++ METIS_TAC [])
   ++ RW_TAC std_ss [da_step_def, na_step_def]
   ++ RW_TAC std_ss [GSYM na2da_def, GSPECIFICATION]
   ++ METIS_TAC []);

val na2da = store_thm
  ("na2da",
   ``!n l. na_accepts n l = da_accepts (na2da n) l``,
   RW_TAC std_ss []
   ++ Introduce `n = (i,trans,acc)`
   ++ RW_TAC std_ss [na_accepts_def, da_accepts_def, na2da_def]
   ++ RW_TAC std_ss [na2da_lemma, GSYM na2da_def, IN_SING]
   ++ RW_TAC std_ss [initial_def]);

(*---------------------------------------------------------------------------*)
(* A checker that works by constructing a deterministic finite automata.     *)
(*---------------------------------------------------------------------------*)

val regexp2na_def = Define
 `(regexp2na (Atom b) = (1, (\s x s'. (s=1) /\ b x /\ (s'=0)), \s. s=0)) /\
   (regexp2na (r1 # r2) =
    let (i1,t1,a1) = regexp2na r1 in
    let (i2,t2,a2) = regexp2na r2 in
    (i1 + i2 + 1,
     (\s x s'.
        if s <= i2 then t2 s x s'
        else if s' <= i2 then a1 (s - (i2 + 1)) /\ t2 i2 x s'
        else t1 (s - (i2 + 1)) x (s' - (i2 + 1))),
     \s. if s <= i2 then a2 s else a2 i2 /\ a1 (s - (i2 + 1)))) /\
   (regexp2na (r1 % r2) =
    let (i1,t1,a1) = regexp2na r1 in
    let (i2,t2,a2) = regexp2na r2 in
    (i1 + i2 + 1,
     (\s x s'.
        if s <= i2 then t2 s x s'
        else if s' <= i2 then ?y. t1 (s - (i2 + 1)) x y /\ a1 y /\ t2 i2 x s'
        else t1 (s - (i2 + 1)) x (s' - (i2 + 1))),
     a2)) /\
   (regexp2na (r1 | r2) =
    let (i1,t1,a1) = regexp2na r1 in
    let (i2,t2,a2) = regexp2na r2 in
    (i1 + i2 + 2,
     (\s x s'.
        if s = i1 + i2 + 2 then
          if s' <= i1 then t1 i1 x s' else t2 i2 x (s' - (i1 + 1))
        else if s <= i1 then t1 s x s'
        else ~(s' <= i1) /\ t2 (s - (i1 + 1)) x (s' - (i1 + 1))),
     \s.
        if s = i1 + i2 + 2 then a1 i1 \/ a2 i2
        else if s <= i1 then a1 s else a2 (s - (i1 + 1)))) /\
   (regexp2na (r1 & r2) =
    let (i1,t1,a1) = regexp2na r1 in
    let (i2,t2,a2) = regexp2na r2 in
    (i1 * i2 + i1 + i2,
     (\s x s'.
        t1 (s DIV (i2 + 1)) x (s' DIV (i2 + 1)) /\
        t2 (s MOD (i2 + 1)) x (s' MOD (i2 + 1))),
     \s. a1 (s DIV (i2 + 1)) /\ a2 (s MOD (i2 + 1)))) /\
   (regexp2na (Repeat r) =
    let (i,t,a) = regexp2na r in
      if a i then (i, (\s x s'. t s x s' \/ a s /\ t i x s'), a)
      else
        (i + 1,
         (\s x s'.
            if s = i + 1 then t i x s'
            else t s x s' \/ a s /\ t i x s'),
         \s. (s = i + 1) \/ a s))`;

val regexp2da_def = Define `regexp2da r = na2da (regexp2na r)`;

val da_match_def = Define `da_match r = da_accepts (regexp2da r)`;

(*---------------------------------------------------------------------------*)
(* Correctness of the finite automata matcher                                *)
(*---------------------------------------------------------------------------*)

val regexp2na_acc = prove
  (``!r i trans acc s. (regexp2na r = (i,trans,acc)) /\ acc s ==> s <= i``,
   Induct
   << [FULL_SIMP_TAC std_ss [regexp2na_def],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ Know `!j. j - (i2 + 1) <= i1 ==> j <= i1 + i2 + 1` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ Know `!j. j - (i1 + 1) <= i2 ==> j <= i1 + i2 + 2` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ MP_TAC (Q.SPEC `i2 + 1` DIVISION)
       ++ DISCH_THEN (MP_TAC o Q.SPEC `s` o SIMP_RULE arith_ss [])
       ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       ++ MATCH_MP_TAC LESS_EQ_TRANS
       ++ Q.EXISTS_TAC `(s DIV (i2 + 1)) * (i2 + 1) + i2`
       ++ SIMP_TAC std_ss [ADD_MONO_LESS_EQ, LESS_EQ_MONO_ADD_EQ]
       ++ CONJ_TAC >> METIS_TAC []
       ++ Know `!m n. m * n + m = m * (n + 1)`
       >> METIS_TAC [MULT_CLAUSES, ADD1, MULT_COMM]
       ++ DISCH_THEN (fn th => REWRITE_TAC [th])
       ++ MATCH_MP_TAC LESS_MONO_MULT
       ++ METIS_TAC [],
       REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r = (i,t,a)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL]]);

val regexp2na_trans = prove
  (``!r i trans acc s x s'.
       (regexp2na r = (i,trans,acc)) /\ trans s x s' ==> s <= i /\ s' <= i``,
   Induct
   << [FULL_SIMP_TAC std_ss [regexp2na_def],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ Know `!j. j - (i2 + 1) <= i1 ==> j <= i1 + i2 + 1` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, regexp2na_acc],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ Know `!j. j - (i2 + 1) <= i1 ==> j <= i1 + i2 + 1` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ Know `!j. j - (i1 + 1) <= i2 ==> j <= i1 + i2 + 2` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL],
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       << [MP_TAC (Q.SPEC `i2 + 1` DIVISION)
           ++ DISCH_THEN (MP_TAC o Q.SPEC `s` o SIMP_RULE arith_ss [])
           ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
           ++ MATCH_MP_TAC LESS_EQ_TRANS
           ++ Q.EXISTS_TAC `(s DIV (i2 + 1)) * (i2 + 1) + i2`
           ++ SIMP_TAC std_ss [ADD_MONO_LESS_EQ, LESS_EQ_MONO_ADD_EQ]
           ++ CONJ_TAC >> METIS_TAC []
           ++ Know `!m n. m * n + m = m * (n + 1)`
           >> METIS_TAC [MULT_CLAUSES, ADD1, MULT_COMM]
           ++ DISCH_THEN (fn th => REWRITE_TAC [th])
           ++ MATCH_MP_TAC LESS_MONO_MULT
           ++ METIS_TAC [],
           MP_TAC (Q.SPEC `i2 + 1` DIVISION)
           ++ DISCH_THEN (MP_TAC o Q.SPEC `s'` o SIMP_RULE arith_ss [])
           ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
           ++ MATCH_MP_TAC LESS_EQ_TRANS
           ++ Q.EXISTS_TAC `(s' DIV (i2 + 1)) * (i2 + 1) + i2`
           ++ SIMP_TAC std_ss [ADD_MONO_LESS_EQ, LESS_EQ_MONO_ADD_EQ]
           ++ CONJ_TAC >> METIS_TAC []
           ++ Know `!m n. m * n + m = m * (n + 1)`
           >> METIS_TAC [MULT_CLAUSES, ADD1, MULT_COMM]
           ++ DISCH_THEN (fn th => REWRITE_TAC [th])
           ++ MATCH_MP_TAC LESS_MONO_MULT
           ++ METIS_TAC []],
       REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r = (i,t,a)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ METIS_TAC
          [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL, regexp2na_acc]]);

val na_match_atom = prove
  (``!b l. na_accepts (regexp2na (Atom b)) l = sem (Atom b) l``,
   RW_TAC std_ss [regexp2na_def, sem_def, LENGTH_EQ_ONE, na_accepts_def]
   ++ Cases_on `l`
   ++ RW_TAC std_ss [na_step_def, HD]
   ++ Cases_on `t`
   ++ RW_TAC std_ss [na_step_def, HD]);

val na_match_concat = prove
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 # r2)) l = sem (r1 # r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (fn th => REWRITE_TAC [GSYM th]))
   ++ Suff
      `!k.
         na_step
           (i1 + i2 + 1,
            (\s x s'.
               if s <= i2 then t2 s x s'
               else if s' <= i2 then a1 (s - (i2 + 1)) /\ t2 i2 x s'
               else t1 (s - (i2 + 1)) x (s' - (i2 + 1))),
            (\s. if s <= i2 then a2 s else a2 i2 /\ a1 (s - (i2 + 1))))
           (k + i2 + 1) l =
         ?w1 w2.
           (l = w1 <> w2) /\ na_step (i1,t1,a1) k w1 /\
           na_step (i2,t2,a2) i2 w2`
   >> METIS_TAC []
   ++ Induct_on `l`
   >> (RW_TAC std_ss [na_step_def, APPEND_eq_NIL]
       ++ FULL_SIMP_TAC arith_ss []
       ++ METIS_TAC [])
   ++ RW_TAC std_ss []
   ++ Know `!P Q. (Q = P [] \/ ?t h. P (h :: t)) ==> (Q = (?l. P l))`
   >> (POP_ASSUM_LIST (K ALL_TAC) ++ METIS_TAC [list_CASES])
   ++ DISCH_THEN HO_MATCH_MP_TAC
   ++ RW_TAC arith_ss [APPEND, na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q R X Y Z.
           ((?x : num. P x /\ Q x /\ Z x) = X) /\
           ((?x. ~P x /\ R x /\ Z x) = Y) ==>
           ((?x. (if P x then Q x else R x) /\ Z x) = X \/ Y)``)
   ++ REVERSE CONJ_TAC
   >> (Suff
       `!P Q.
          ((?x : num. P (x + i2 + 1)) = Q) ==>
          ((?x. ~(x <= i2) /\ P x) = Q)`
       >> (DISCH_THEN HO_MATCH_MP_TAC
           ++ POP_ASSUM MP_TAC
           ++ RW_TAC arith_ss []
           ++ POP_ASSUM (K ALL_TAC)
           ++ METIS_TAC [])
       ++ POP_ASSUM (K ALL_TAC)
       ++ Suff `!x. ~(x <= i2) = (?y. x = y + i2 + 1)` >> METIS_TAC []
       ++ RW_TAC arith_ss []
       ++ REVERSE EQ_TAC >> RW_TAC arith_ss []
       ++ RW_TAC arith_ss []
       ++ Q.EXISTS_TAC `x - (i2 + 1)`
       ++ DECIDE_TAC)
   ++ POP_ASSUM (K ALL_TAC)
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!A B C D E.
           (!x. E x ==> A x) /\ (!x. A x ==> (D x = E x)) ==>
           ((?x. A x /\ (B /\ C x) /\ D x) = B /\ ?x. C x /\ E x)``)
   ++ CONJ_TAC
   >> (Cases_on `l`
       ++ RW_TAC std_ss [na_step_def]
       ++ METIS_TAC [regexp2na_trans, regexp2na_acc])
   ++ Induct_on `l` >> RW_TAC std_ss [na_step_def]
   ++ RW_TAC std_ss [na_step_def]
   ++ METIS_TAC [regexp2na_trans]);

val na_match_fuse = prove
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 % r2)) l = sem (r1 % r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (fn th => REWRITE_TAC [GSYM th]))
   ++ Suff
      `!k.
         na_step
         (i1 + i2 + 1,
          (\s x s'.
             if s <= i2 then t2 s x s'
             else if s' <= i2 then
                ?y. t1 (s - (i2 + 1)) x y /\ a1 y /\ t2 i2 x s'
             else t1 (s - (i2 + 1)) x (s' - (i2 + 1))),a2) (k + i2 + 1) l =
         ?w1 w2 c.
           (l = w1 <> [c] <> w2) /\ na_step (i1,t1,a1) k (w1 <> [c]) /\
           na_step (i2,t2,a2) i2 ([c] <> w2)`
   >> METIS_TAC []
   ++ Induct_on `l`
   >> (RW_TAC std_ss [na_step_def, APPEND_eq_NIL]
       ++ Suff `~(k + i2 + 1 <= i2)` >> METIS_TAC [regexp2na_acc]
       ++ RW_TAC arith_ss [])
   ++ RW_TAC std_ss []
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE [list_CASES]
       ``!P Q. (Q = P [] \/ ?t h. P (h :: t)) ==> (Q = (?l. P l))``)
   ++ RW_TAC arith_ss [na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q R X Y Z.
           ((?x : num. P x /\ Q x /\ Z x) = X) /\
           ((?x. ~P x /\ R x /\ Z x) = Y) ==>
           ((?x. (if P x then Q x else R x) /\ Z x) = X \/ Y)``)
   ++ REVERSE CONJ_TAC
   >> (Suff
       `!P Q.
          ((?x : num. P (x + i2 + 1)) = Q) ==>
          ((?x. ~(x <= i2) /\ P x) = Q)`
       >> (DISCH_THEN HO_MATCH_MP_TAC
           ++ POP_ASSUM MP_TAC
           ++ RW_TAC arith_ss []
           ++ POP_ASSUM (K ALL_TAC)
           ++ RW_TAC arith_ss [na_step_def, APPEND]
           ++ METIS_TAC [])
       ++ POP_ASSUM (K ALL_TAC)
       ++ Suff `!x. ~(x <= i2) = (?y. x = y + i2 + 1)` >> METIS_TAC []
       ++ RW_TAC arith_ss []
       ++ REVERSE EQ_TAC >> RW_TAC arith_ss []
       ++ RW_TAC arith_ss []
       ++ Q.EXISTS_TAC `x - (i2 + 1)`
       ++ DECIDE_TAC)
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC std_ss [APPEND, na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!A B C D E G.
           (!x. G x ==> A x) /\ (!x. A x ==> (E x = G x)) ==>
           ((?x. A x /\ (?y. B y /\ C y /\ D x) /\ E x) =
            (?y. B y /\ C y) /\ (?x. D x /\ G x))``)
   ++ CONJ_TAC
   >> (Cases_on `l`
       ++ RW_TAC std_ss [na_step_def]
       ++ METIS_TAC [regexp2na_trans, regexp2na_acc])
   ++ Induct_on `l` >> RW_TAC std_ss [na_step_def]
   ++ RW_TAC std_ss [na_step_def]
   ++ METIS_TAC [regexp2na_trans]);

val na_match_or = prove
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 | r2)) l = sem (r1 | r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (fn th => REWRITE_TAC [GSYM th]))
   ++ Cases_on `l` >> RW_TAC std_ss [na_step_def]
   ++ RW_TAC std_ss [na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q R X Y Z.
           ((?x : num. Z x /\ P x /\ R x) = X) /\
           ((?x. ~Z x /\ Q x /\ R x) = Y) ==>
           ((?x. (if Z x then P x else Q x) /\ R x) = X \/ Y)``)
   ++ CONJ_TAC
   >> (HO_MATCH_MP_TAC
       (METIS_PROVE []
        ``!P Q R X.
            (!x. P x ==> X x) /\ (!x : num. X x ==> (Q x = R x)) ==>
            ((?x. X x /\ P x /\ Q x) = (?x. P x /\ R x))``)
       ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
       ++ Induct_on `t`
       >> RW_TAC arith_ss [na_step_def]
       ++ RW_TAC arith_ss [na_step_def]
       ++ HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (!x : num. P x ==> (Q x = R x)) ==>
               ((?x. P x /\ Q x) = (?x. P x /\ R x))``)
       ++ RW_TAC std_ss []
       ++ Know `s'' <= i1` >> METIS_TAC [regexp2na_trans]
       ++ POP_ASSUM (K ALL_TAC)
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `!k. P k` (MP_TAC o Q.SPEC `s''`)
       ++ RW_TAC arith_ss [])
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q.
           (!x. P x ==> ?y. x = y + (i1 + 1)) /\
           (!x : num. P (x + (i1 + 1)) = Q x) ==>
           ((?x. P x) = (?x. Q x))``)
   ++ CONJ_TAC
   >> (RW_TAC std_ss []
       ++ Q.EXISTS_TAC `s' - (i1 + 1)`
       ++ POP_ASSUM (K ALL_TAC)
       ++ DECIDE_TAC)
   ++ RW_TAC arith_ss []
   ++ MATCH_MP_TAC (PROVE [] ``!x y z. (x ==> (y = z)) ==> (x /\ y = x /\ z)``)
   ++ STRIP_TAC
   ++ Know `s' <= i2` >> METIS_TAC [regexp2na_trans]
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.SPEC_TAC (`s'`, `k`)
   ++ Induct_on `t` >> RW_TAC arith_ss [na_step_def]
   ++ RW_TAC arith_ss [na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q.
           (!x. P x ==> ?y. x = y + (i1 + 1)) /\
           (!x : num. P (x + (i1 + 1)) = Q x) ==>
           ((?x. P x) = (?x. Q x))``)
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `!x. P x` (K ALL_TAC)
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `s' - (i1 + 1)`
       ++ POP_ASSUM (K ALL_TAC)
       ++ DECIDE_TAC)
   ++ RW_TAC arith_ss []
   ++ MATCH_MP_TAC (PROVE [] ``!x y z. (x ==> (y = z)) ==> (x /\ y = x /\ z)``)
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `s'`)
   ++ Know `s' <= i2` >> METIS_TAC [regexp2na_trans]
   ++ RW_TAC arith_ss []);

val na_match_and = prove
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 & r2)) l = sem (r1 & r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (fn th => REWRITE_TAC [GSYM th]))
   ++ Suff
      `!j k.
         j <= i1 /\ k <= i2 ==>
         (na_step
          (i1 * i2 + i1 + i2,
           (\s x s'.
              t1 (s DIV (i2 + 1)) x (s' DIV (i2 + 1)) /\
              t2 (s MOD (i2 + 1)) x (s' MOD (i2 + 1))),
           (\s. a1 (s DIV (i2 + 1)) /\ a2 (s MOD (i2 + 1))))
          (j * (i2 + 1) + k) l =
        na_step (i1,t1,a1) j l /\ na_step (i2,t2,a2) k l)`
   >> (DISCH_THEN (MP_TAC o Q.SPECL [`i1`, `i2`])
       ++ RW_TAC arith_ss [LEFT_ADD_DISTRIB])
   ++ Know `0 < i2 + 1` >> DECIDE_TAC ++ STRIP_TAC
   ++ Know `!k. k < i2 + 1 = k <= i2` >> DECIDE_TAC ++ STRIP_TAC
   ++ Induct_on `l` >> RW_TAC std_ss [na_step_def, DIV_MULT, MOD_MULT]
   ++ RW_TAC std_ss [na_step_def, DIV_MULT, MOD_MULT]
   ++ CONV_TAC
      (REDEPTH_CONV (LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `i2 + 1` DIVISION)
   ++ ASM_REWRITE_TAC []
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q A B C.
           ((?x. A x /\ B (P x)) = C) ==>
           ((!x. (x = P x) /\ Q x) ==> ((?x. A x /\ B x) = C))``)
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P A B C.
           (!x. A x ==> P x) /\ ((?x. A x /\ (P x ==> B x)) = C) ==>
           ((?x. A x /\ B x) = C)``)
   ++ Q.EXISTS_TAC `\x. x DIV (i2 + 1) <= i1 /\ x MOD (i2 + 1) <= i2`
   ++ BETA_TAC
   ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
   ++ Q.PAT_ASSUM `!x. P x` (fn th => RW_TAC std_ss [th])
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P A B C.
           (!x. A x ==> P x) /\ ((?x. A x /\ B x) = C) ==>
           ((?x. A x /\ (P x ==> B x)) = C)``)
   ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
   ++ EQ_TAC >> METIS_TAC []
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `s' * (i2 + 1) + s''`
   ++ Know `s'' <= i2` >> METIS_TAC [regexp2na_trans]
   ++ RW_TAC std_ss [DIV_MULT, MOD_MULT]);

val na_match_repeat = prove
  (``!r.
       (!l. na_accepts (regexp2na r) l = sem r l) ==>
       !l. na_accepts (regexp2na (Repeat r)) l = sem (Repeat r) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r = (i, t, a)`
   ++ (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def]
       ++ (REPEAT o Q.PAT_ASSUM `!x. P x`)
          (fn th => REWRITE_TAC [GSYM (MATCH_MP EQ_EXT th)]))
   >> (HO_MATCH_MP_TAC
       (METIS_PROVE [list_CASES]
        ``!P Q. (Q = P [] \/ ?w ws. P (w :: ws)) ==> (Q = (?l. P l))``)
       ++ RW_TAC std_ss [CONCAT_def, ALL_EL]
       ++ Cases_on `l = []` >> RW_TAC std_ss [na_step_def]
       ++ RW_TAC std_ss []
       ++ Suff
          `!k.
             (na_step (i,(\s x s'. t s x s' \/ a s /\ t i x s'),a) k l =
              ?w ws.
                (l = w <> CONCAT ws) /\ na_step (i,t,a) k w /\
                ALL_EL (na_step (i,t,a) i) ws)`
       >> RW_TAC std_ss []
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `l`
       >> (RW_TAC std_ss [na_step_def, APPEND_eq_NIL]
           ++ REVERSE (Cases_on `a k`) >> RW_TAC std_ss []
           ++ RW_TAC std_ss []
           ++ Q.EXISTS_TAC `[]`
           ++ RW_TAC std_ss [CONCAT_def, ALL_EL])
       ++ RW_TAC std_ss []
       ++ HO_MATCH_MP_TAC
          (METIS_PROVE [list_CASES]
           ``!P Q. (Q = P [] \/ ?c cs. P (c :: cs)) ==> (Q = (?l. P l))``)
       ++ RW_TAC std_ss [na_step_def, APPEND]
       ++ RW_TAC std_ss [RIGHT_AND_OVER_OR, EXISTS_OR_THM]
       ++ MATCH_MP_TAC (PROVE [] ``(a = d) /\ (b = c) ==> (a \/ b = c \/ d)``)
       ++ CONJ_TAC >> METIS_TAC []
       ++ POP_ASSUM (K ALL_TAC)
       ++ REVERSE (Cases_on `a k`) >> RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ POP_ASSUM (K ALL_TAC)
       ++ EQ_TAC
       >> (RW_TAC std_ss []
           ++ Q.EXISTS_TAC `(h::w) :: ws`
           ++ RW_TAC std_ss [ALL_EL, CONCAT_def, na_step_def, APPEND]
           ++ PROVE_TAC [])
       ++ RW_TAC std_ss []
       ++ Induct_on `ws` >> RW_TAC std_ss [CONCAT_def]
       ++ Cases >> RW_TAC std_ss [CONCAT_def, APPEND, ALL_EL, na_step_def]
       ++ POP_ASSUM (K ALL_TAC)
       ++ RW_TAC std_ss [CONCAT_def, APPEND, ALL_EL, na_step_def]
       ++ PROVE_TAC [])
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE [list_CASES]
       ``!P Q. (Q = P [] \/ ?w ws. P (w :: ws)) ==> (Q = (?l. P l))``)
   ++ RW_TAC std_ss [CONCAT_def, ALL_EL]
   ++ Cases_on `l` >> RW_TAC std_ss [na_step_def]
   ++ RW_TAC std_ss [na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE [list_CASES]
       ``!P Q. (Q = P [] \/ ?x xs. P (x :: xs)) ==> (Q = (?l. P l))``)
   ++ RW_TAC std_ss [CONCAT_def, ALL_EL, APPEND, na_step_def]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q A B C.
           (!x. P x ==> x <= i) /\
           (!x. x <= i ==> (Q x = ?y z. A y z /\ B x y z /\ C y z)) ==>
           ((?x. P x /\ Q x) = ?y z. A y z /\ (?x. P x /\ B x y z) /\ C y z)``)
   ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
   ++ Induct_on `t'`
   >> (RW_TAC arith_ss [na_step_def, APPEND_eq_NIL]
       ++ REVERSE (Cases_on `a s'`) >> RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `[]`
       ++ RW_TAC std_ss [CONCAT_def, ALL_EL])
   ++ RW_TAC std_ss []
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE [list_CASES]
       ``!P Q. (Q = P [] \/ ?x xs. P (x :: xs)) ==> (Q = (?l. P l))``)
   ++ RW_TAC arith_ss [CONCAT_def, ALL_EL, APPEND, na_step_def]
   ++ RW_TAC std_ss [RIGHT_AND_OVER_OR, EXISTS_OR_THM]
   ++ MATCH_MP_TAC (PROVE [] ``(a = d) /\ (b = c) ==> (a \/ b = c \/ d)``)
   ++ CONJ_TAC
   >> (HO_MATCH_MP_TAC
       (METIS_PROVE []
        ``!P A B C.
            (!x. A x ==> P x) /\ ((?x. A x /\ (P x ==> B x)) = C) ==>
            ((?x. A x /\ B x) = C)``)
       ++ Q.EXISTS_TAC `\x. x <= i`
       ++ BETA_TAC
       ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
       ++ Q.PAT_ASSUM `!x. P x` (fn th => RW_TAC std_ss [th])
       ++ HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P A B C.
               (!x. A x ==> P x) /\ ((?x. A x /\ B x) = C) ==>
               ((?x. A x /\ (P x ==> B x)) = C)``)
       ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
       ++ METIS_TAC [])
   ++ REVERSE (Cases_on `a s'`) >> RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q R.
           (!x. P x ==> x <= i) /\ ((?x. P x /\ (x <= i ==> Q x)) = R) ==>
           ((?x. P x /\ Q x) = R)``)
   ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
   ++ RW_TAC std_ss []
   ++ NTAC 3 (POP_ASSUM (K ALL_TAC))
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!P Q R.
           (!x. P x ==> x <= i) /\ ((?x. P x /\ Q x) = R) ==>
           ((?x. P x /\ (x <= i ==> Q x)) = R)``)
   ++ CONJ_TAC >> METIS_TAC [regexp2na_trans]
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ Q.EXISTS_TAC `(h::xs) :: ws`
       ++ RW_TAC std_ss [ALL_EL, CONCAT_def, na_step_def, APPEND]
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss []
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ Cases_on `ws` >> RW_TAC std_ss [CONCAT_def]
   ++ Cases_on `h'` >> RW_TAC std_ss [na_step_def, ALL_EL]
   ++ RW_TAC std_ss [CONCAT_def, APPEND, ALL_EL, na_step_def]
   ++ METIS_TAC []);

val na_match = prove
  (``!r l. na_accepts (regexp2na r) l = sem r l``,
   Induct
   ++ RW_TAC std_ss [na_match_atom, na_match_concat, na_match_fuse,
                     na_match_or, na_match_and, na_match_repeat]);

val da_accepts_regexp2da = prove
  (``!r. sem r = da_accepts (regexp2da r)``,
   RW_TAC std_ss [FUN_EQ_THM, regexp2da_def, GSYM na2da, na_match]);

val da_match = store_thm
  ("da_match",
   ``!r l. da_match r l = sem r l``,
   RW_TAC std_ss [da_match_def, da_accepts_regexp2da]);

val kleene_regexp2dfa = store_thm
  ("kleene_regexp2dfa",
   ``!exp : 'a regexp. ?dfa : (num->bool,'a) da. sem exp = da_accepts dfa``,
   METIS_TAC [da_accepts_regexp2da]);

(*---------------------------------------------------------------------------*)
(* A version of the automata matcher that is easy to execute.                *)
(*---------------------------------------------------------------------------*)

val initial_regexp2na_def = pureDefine
  `initial_regexp2na r = initial (regexp2na r)`;

val accept_regexp2na_def = pureDefine
  `accept_regexp2na r = accept (regexp2na r)`;

val transition_regexp2na_def = pureDefine
  `transition_regexp2na r = transition (regexp2na r)`;

val transition_regexp2na_fuse_def = Define
  `(transition_regexp2na_fuse a t 0 = F) /\
   (transition_regexp2na_fuse a t (SUC s') =
    a s' /\ t s' \/ transition_regexp2na_fuse a t s')`;

val transition_regexp2na_fuse = prove
  (``!k r s x i t a.
       (regexp2na r = (i,t,a)) ==>
       (transition_regexp2na_fuse a (t s x) k = ?y. a y /\ y < k /\ t s x y)``,
   Induct
   ++ RW_TAC arith_ss [transition_regexp2na_fuse_def]
   ++ METIS_TAC [prim_recTheory.LESS_THM]);

val initial_regexp2na = store_thm
  ("initial_regexp2na",
   ``(initial_regexp2na (Atom b : 'a regexp) = 1) /\
     (initial_regexp2na (r1 # r2 : 'a regexp) =
      initial_regexp2na r1 + initial_regexp2na r2 + 1) /\
     (initial_regexp2na (r1 % r2) =
      initial_regexp2na r1 + initial_regexp2na r2 + 1) /\
     (initial_regexp2na (r1 | r2) =
      initial_regexp2na r1 + initial_regexp2na r2 + 2) /\
     (initial_regexp2na (r1 & r2) =
      let i1 = initial_regexp2na r1 in
      let i2 = initial_regexp2na r2 in i1 * i2 + i1 + i2) /\
     (initial_regexp2na (Repeat r : 'a regexp) =
      let i = initial_regexp2na r in
      if accept_regexp2na r i then i else i + 1)``,
   Introduce `regexp2na r1 = (i1,t1,a1)`
   ++ Introduce `regexp2na r2 = (i2,t2,a2)`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ RW_TAC std_ss
      [regexp2na_def, initial_def, accept_def,
       initial_regexp2na_def, accept_regexp2na_def]);

val accept_regexp2na = store_thm
  ("accept_regexp2na",
   ``(accept_regexp2na (Atom b : 'a regexp) s = (s = 0)) /\
     (accept_regexp2na (r1 # r2 : 'a regexp) s =
      let i2 = initial_regexp2na r2 in
      if s <= i2 then accept_regexp2na r2 s
      else accept_regexp2na r2 i2 /\
           accept_regexp2na r1 (s - (i2 + 1))) /\
     (accept_regexp2na (r1 % r2) s = accept_regexp2na r2 s) /\
     (accept_regexp2na (r1 | r2) s =
      let i1 = initial_regexp2na r1 in
      let i2 = initial_regexp2na r2 in
      if s = i1 + i2 + 2 then
        accept_regexp2na r1 i1 \/ accept_regexp2na r2 i2
      else if s <= i1 then accept_regexp2na r1 s
      else accept_regexp2na r2 (s - (i1 + 1))) /\
     (accept_regexp2na (r1 & r2) s =
      let i2 = initial_regexp2na r2 in
      accept_regexp2na r1 (s DIV (i2 + 1)) /\
      accept_regexp2na r2 (s MOD (i2 + 1))) /\
     (accept_regexp2na (Repeat r : 'a regexp) s =
      accept_regexp2na r s \/
      let i = initial_regexp2na r in
      (s = i + 1) /\ ~accept_regexp2na r i)``,
   Introduce `regexp2na r1 = (i1,t1,a1)`
   ++ Introduce `regexp2na r2 = (i2,t2,a2)`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ REPEAT CONJ_TAC
   ++ RW_TAC std_ss
      [regexp2na_def, initial_def, accept_def,
       initial_regexp2na_def, accept_regexp2na_def]
   ++ METIS_TAC []);

val transition_regexp2na = store_thm
  ("transition_regexp2na",
   ``(transition_regexp2na (Atom b : 'a regexp) s x s' =
      (s = 1) /\ (s' = 0) /\ b x) /\
     (transition_regexp2na (r1 # r2 : 'a regexp) s x s' =
      let i2 = initial_regexp2na r2 in
      if s <= i2 then transition_regexp2na r2 s x s'
      else if s' <= i2 then
        accept_regexp2na r1 (s - (i2 + 1)) /\
        transition_regexp2na r2 i2 x s'
      else
        transition_regexp2na r1 (s - (i2 + 1)) x (s' - (i2 + 1))) /\
     (transition_regexp2na (r1 % r2) s x s' =
      let i2 = initial_regexp2na r2 in
      if s <= i2 then transition_regexp2na r2 s x s'
      else if s' <= i2 then
        transition_regexp2na r2 i2 x s' /\
        let i1 = initial_regexp2na r1 in
        transition_regexp2na_fuse (accept_regexp2na r1)
        (transition_regexp2na r1 (s - (i2 + 1)) x) (SUC i1)
      else transition_regexp2na r1 (s - (i2 + 1)) x (s' - (i2 + 1))) /\
     (transition_regexp2na (r1 | r2) s x s' =
      let i1 = initial_regexp2na r1 in
      let i2 = initial_regexp2na r2 in
      if s = i1 + i2 + 2 then
        if s' <= i1 then transition_regexp2na r1 i1 x s'
        else transition_regexp2na r2 i2 x (s' - (i1 + 1))
      else if s <= i1 then transition_regexp2na r1 s x s'
      else ~(s' <= i1) /\
           transition_regexp2na r2 (s - (i1 + 1)) x (s' - (i1 + 1))) /\
     (transition_regexp2na (r1 & r2) s x s' =
      let i2 = initial_regexp2na r2 in
      transition_regexp2na r1 (s DIV (i2 + 1)) x (s' DIV (i2 + 1)) /\
      transition_regexp2na r2 (s MOD (i2 + 1)) x (s' MOD (i2 + 1))) /\
     (transition_regexp2na (Repeat r : 'a regexp) s x s' =
      let i = initial_regexp2na r in
      if s = i + 1 then
        ~accept_regexp2na r i /\
        transition_regexp2na r i x s'
      else
        transition_regexp2na r s x s' \/
        accept_regexp2na r s /\ transition_regexp2na r i x s')``,
   Introduce `regexp2na r1 = (i1,t1,a1)`
   ++ Introduce `regexp2na r2 = (i2,t2,a2)`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ RW_TAC std_ss
      [regexp2na_def, initial_def, accept_def, transition_def,
       initial_regexp2na_def, accept_regexp2na_def, transition_regexp2na_def]
   << [METIS_TAC [],
       MP_TAC (Q.SPECL [`SUC i1`, `r1`, `s - (i2 + 1)`, `x`, `i1`, `t1`, `a1`]
               transition_regexp2na_fuse)
       ++ RW_TAC std_ss []
       ++ Know `!p q. p < SUC q = p <= q` >> DECIDE_TAC
       ++ METIS_TAC [regexp2na_acc],
       Know `!n. ~(n + 1 <= n)` >> DECIDE_TAC
       ++ METIS_TAC [regexp2na_trans, regexp2na_acc],
       Know `!n. ~(n + 1 <= n)` >> DECIDE_TAC
       ++ METIS_TAC [regexp2na_trans, regexp2na_acc]]);

val calc_transitions_def = Define
  `(calc_transitions r l c 0 a = a) /\
   (calc_transitions r l c (SUC s') a =
    calc_transitions r l c s'
    (if EXISTS (\s. transition_regexp2na r s c s') l then s' :: a else a))`;

val eval_transitions_def = pureDefine
  `eval_transitions r l c =
   calc_transitions r l c (SUC (initial_regexp2na r)) []`;

val (astep_def, astep_ind) = Defn.tprove
  (Hol_defn "astep"
   `astep r l cs =
    if NULL cs then EXISTS (accept_regexp2na r) l
    else astep r (eval_transitions r l (HD cs)) (TL cs)`,
   WF_REL_TAC `measure (LENGTH o SND o SND)`
   ++ Cases
   ++ RW_TAC arith_ss [NULL_DEF, TL, LENGTH]);

val _ = save_thm ("astep_def", astep_def);
val _ = save_thm ("astep_ind", astep_ind);

val amatch_def = Define
  `amatch r l = let i = initial_regexp2na r in astep r [i] l`;

(*---------------------------------------------------------------------------*)
(* Correctness of this version of the automata matcher.                      *)
(*---------------------------------------------------------------------------*)

val da_accepts_na2da = prove
  (``!n. da_accepts (na2da n) = da_step (na2da n) (set_of_list [initial n])``,
   STRIP_TAC
   ++ Introduce `n = (i,t,a)`
   ++ RW_TAC std_ss
      [FUN_EQ_THM, na2da_def, da_accepts_def, initial_def, set_of_list_def]);

val da_step_regexp2na = prove
  (``(da_step (na2da (regexp2na r)) (set_of_list l) [] =
      EXISTS (accept (regexp2na r)) l) /\
     (da_step (na2da (regexp2na r)) (set_of_list l) (c :: cs) =
      let i = initial (regexp2na r) in
      let l' = calc_transitions r l c (SUC i) [] in
      da_step (na2da (regexp2na r)) (set_of_list l') cs)``,
   Introduce `regexp2na r = (i,t,a)`
   ++ RW_TAC std_ss [da_step_def, na2da_def, EXISTS_MEM, set_of_list]
   ++ REPEAT (AP_TERM_TAC || AP_THM_TAC)
   ++ RW_TAC std_ss [EXTENSION, GSPECIFICATION, set_of_list, initial_def]
   ++ Suff
      `!k.
         MEM x (calc_transitions r l c (SUC i) k) =
         IS_EL x k \/ (x < SUC i /\ ?y. IS_EL y l /\ transition (i,t,a) y c x)`
   >> (DISCH_THEN (MP_TAC o Q.SPEC `[]`)
       ++ Know `!x. x < SUC i = x <= i` >> DECIDE_TAC
       ++ RW_TAC std_ss [MEM, transition_def]
       ++ METIS_TAC [regexp2na_trans])
   ++ Q.SPEC_TAC (`SUC i`, `n`)
   ++ Induct
   ++ RW_TAC arith_ss
      [calc_transitions_def, EXISTS_MEM, MEM, transition_regexp2na_def]
   ++ Know `!a b. ~(a < b) /\ a < SUC b = (a = b)` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ EQ_TAC
   ++ RW_TAC arith_ss []
   ++ RW_TAC arith_ss []
   ++ METIS_TAC []);

val amatch = store_thm
  ("amatch",
   ``!r l. amatch r l = sem r l``,
   RW_TAC std_ss
   [GSYM da_match, da_match_def, regexp2da_def, da_accepts_na2da, amatch_def]
   ++ RW_TAC std_ss [initial_regexp2na_def]
   ++ Suff `!k. astep r k l = da_step (na2da (regexp2na r)) (set_of_list k) l`
   >> RW_TAC std_ss []
   ++ Induct_on `l`
   >> RW_TAC std_ss
      [astep_def, da_step_def, na2da_def, EXISTS_MEM, set_of_list,
       accept_regexp2na_def, NULL_DEF, TL]
   ++ ONCE_REWRITE_TAC [astep_def]
   ++ SIMP_TAC std_ss [da_step_regexp2na, eval_transitions_def, NULL_DEF, TL]
   ++ RW_TAC std_ss [initial_regexp2na_def, HD]);

val () = export_theory ();
