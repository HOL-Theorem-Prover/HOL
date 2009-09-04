(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(* Originated from Konrad Slind, tweaked by MJCG for Accellera PSL SEREs     *)
(* An automata-based matcher added by Joe Hurd                               *)
(*---------------------------------------------------------------------------*)

(*
app load
["bossLib", "rich_listTheory", "metisLib", "pred_setTheory", "stringTheory",
 "regexpTheory"];
*)

open HolKernel Parse boolLib;
open bossLib metisLib
open pairTheory combinTheory listTheory rich_listTheory
     stringTheory pred_setTheory arithmeticTheory;
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
val lemma = prove;

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

fun GCONJUNCTS th =
  let
    val tm = concl th
    val (vs, imps) = strip_forall tm
    val (xs, conjs) = strip_imp imps
    val add_imps = fn th => foldr (fn (x,t) => DISCH x t) th xs
    val add_vars = fn th => foldr (fn (v,t) => GEN v t) th vs
  in
    (map (add_vars o add_imps) o CONJUNCTS o UNDISCH_ALL o SPEC_ALL) th
  end;

(*---------------------------------------------------------------------------*)
(* Misc. theorems                                                            *)
(*---------------------------------------------------------------------------*)

val MLEX_def = Define `MLEX f r x y = f x < f y \/ (f x = f y) /\ r x y`;

val WF_MLEX = store_thm
  ("WF_MLEX",
   ``!f r. WF r ==> WF (MLEX f r)``,
   RW_TAC std_ss []
   ++ Suff `MLEX f r = inv_image ((<) LEX r) (\x. (f x, x))`
   >> METIS_TAC [prim_recTheory.WF_LESS, WF_LEX, relationTheory.WF_inv_image]
   ++ RW_TAC std_ss [FUN_EQ_THM,MLEX_def,relationTheory.inv_image_def,LEX_DEF]);

val NO_MEM = store_thm
  ("NO_MEM",
   ``!l. (!x. ~MEM x l) = (l = [])``,
   Cases ++ RW_TAC std_ss [MEM] ++ METIS_TAC []);

val set_of_list_def = Define
  `(set_of_list [] = {}) /\
   (set_of_list (h :: t) = h INSERT set_of_list t)`;

val set_of_list = store_thm
  ("set_of_list",
   ``!l x. x IN set_of_list l = MEM x l``,
   Induct ++ RW_TAC std_ss [set_of_list_def, MEM, NOT_IN_EMPTY, IN_INSERT]);

val interval_def = Define
  `(interval x 0 = []) /\
   (interval x (SUC n) = x :: interval (SUC x) n)`;

val MEM_interval = store_thm
  ("MEM_interval",
   ``!x k n. MEM x (interval k n) = k <= x /\ x < k + n``,
   Induct_on `n`
   ++ RW_TAC arith_ss [MEM, interval_def]);

val MEM_FILTER = store_thm
  ("MEM_FILTER",
   ``!p l x. MEM x (FILTER p l) = MEM x l /\ p x``,
   Induct_on `l`
   ++ RW_TAC std_ss [FILTER, MEM]
   ++ METIS_TAC []);

val EVERY_MONO = store_thm
  ("EVERY_MONO",
   ``!p q l. (!x. p x ==> q x) /\ EVERY p l ==> EVERY q l``,
   METIS_TAC [EVERY_MONOTONIC]);

val partition_def = Define
  `(partition p [] = ([],[])) /\
   (partition p (h :: t) =
    let (l,r) = partition p t in if p h then (h::l,r) else (l,h::r))`;

val LENGTH_partition = store_thm
  ("LENGTH_partition",
   ``!p l x y. (partition p l = (x,y)) ==> (LENGTH l = LENGTH x + LENGTH y)``,
   Induct_on `l`
   ++ RW_TAC list_ss [partition_def]
   ++ Introduce `partition p l = (a,b)`
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC arith_ss [LENGTH]
   ++ RES_TAC
   ++ RW_TAC arith_ss [LENGTH]);

val MEM_partition = store_thm
  ("MEM_partition",
   ``!p l x y k.
       (partition p l = (x,y)) ==>
       (MEM k x = p k /\ MEM k l) /\
       (MEM k y = ~p k /\ MEM k l)``,
   Induct_on `l`
   ++ RW_TAC list_ss [partition_def]
   ++ Introduce `partition p l = (a,b)`
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC arith_ss [MEM]
   ++ RES_TAC
   ++ RW_TAC arith_ss [MEM]
   ++ METIS_TAC []);

val BUTFIRSTN_EL = store_thm
  ("BUTFIRSTN_EL",
   ``!n l.
       n < LENGTH l ==>
       (EL n l :: BUTFIRSTN (SUC n) l = BUTFIRSTN n l)``,
   Induct
   ++ Cases
   ++ RW_TAC arith_ss [EL, BUTFIRSTN, LENGTH, HD, TL]);

val BUTFIRSTN_HD = store_thm
  ("BUTFIRSTN_HD",
   ``!n l. n < LENGTH l ==> (HD (BUTFIRSTN n l) = EL n l)``,
   Induct
   ++ Cases
   ++ RW_TAC arith_ss [EL, BUTFIRSTN, LENGTH, HD, TL]);

val BUTFIRSTN_TL = store_thm
  ("BUTFIRSTN_TL",
   ``!n l. n < LENGTH l ==> (TL (BUTFIRSTN n l) = BUTFIRSTN (SUC n) l)``,
   Induct
   ++ Cases
   ++ RW_TAC arith_ss [EL, BUTFIRSTN, LENGTH, HD, TL]);

(*---------------------------------------------------------------------------*)
(* Theorems for reducing character equations.                                *)
(*---------------------------------------------------------------------------*)

val chr_11 = store_thm
  ("chr_11",
   ``!m n x. (m = ORD x) /\ (n = ORD x) = (m = n) /\ (m = ORD x)``,
   METIS_TAC []);

val chr_suff = store_thm
  ("chr_suff",
   ``!n p. (?x. (n = ORD x) \/ p x) = n < 256 \/ ?x. p x``,
   METIS_TAC [ORD_ONTO]);

val chr_suff1 = store_thm
  ("chr_suff1",
   ``!n. (?x. (n = ORD x)) = n < 256``,
   METIS_TAC [ORD_ONTO]);

(*---------------------------------------------------------------------------*)
(* Dijkstra's reachability algorithm.                                        *)
(*---------------------------------------------------------------------------*)

val accepting_path_def = Define
  `(accepting_path (t : 'a->'a->bool) a s [] = a s) /\
   (accepting_path t a s (s' :: l) = t s s' /\ accepting_path t a s' l)`;

val accepting_path_tail = store_thm
  ("accepting_path_tail",
   ``!p t a k ks.
       ~p k /\ accepting_path t a k ks ==>
       ?j js n.
         n <= LENGTH ks /\ (j :: js = BUTFIRSTN n (k :: ks)) /\
         ~p j /\ EVERY p js /\ accepting_path t a j js``,
   completeInduct_on `LENGTH ks`
   ++ RW_TAC std_ss []
   ++ Cases_on `EVERY p ks`
   >> (Q.EXISTS_TAC `k`
       ++ Q.EXISTS_TAC `ks`
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC arith_ss [EVERY_MEM, BUTFIRSTN])
   ++ POP_ASSUM (MP_TAC o REWRITE_RULE [EVERY_MEM, MEM_EL])
   ++ RW_TAC std_ss []
   ++ Suff
      `?j js n'.
         n' <= LENGTH (BUTFIRSTN (SUC n) ks) /\
         (j::js = BUTFIRSTN n' (EL n ks :: BUTFIRSTN (SUC n) ks)) /\ ~p j /\
         ALL_EL p js /\ accepting_path t a j js`
   >> (Q.PAT_ASSUM `!m. P m` (K ALL_TAC)
       ++ RW_TAC arith_ss [BUTFIRSTN_EL, LENGTH_BUTFIRSTN]
       ++ Know `n' + n < LENGTH ks` >> DECIDE_TAC
       ++ STRIP_TAC
       ++ Q.EXISTS_TAC `EL (n + n') ks`
       ++ Q.EXISTS_TAC `BUTFIRSTN (SUC n + n') ks`
       ++ Q.EXISTS_TAC `SUC n + n'`
       ++ FULL_SIMP_TAC arith_ss
          [BUTFIRSTN, ALL_EL_BUTFIRSTN, BUTFIRSTN_EL, BUTFIRSTN_BUTFIRSTN, ADD]
       ++ Suff `(j = EL (n + n') ks) /\ (js = BUTFIRSTN (SUC (n + n')) ks)`
       >> METIS_TAC []
       ++ METIS_TAC [HD, TL, BUTFIRSTN_HD, BUTFIRSTN_TL])
   ++ Q.PAT_ASSUM `!x. P x` MP_TAC
   ++ SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]
   ++ DISCH_THEN MATCH_MP_TAC
   ++ RW_TAC arith_ss [LENGTH_BUTFIRSTN]
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`k`, `k`)
   ++ Q.SPEC_TAC (`ks`, `ks`)
   ++ Induct_on `n`
   ++ Cases
   ++ RW_TAC arith_ss [BUTFIRSTN, LENGTH, EL, HD, accepting_path_def, TL]
   ++ METIS_TAC []);

val (dijkstra_def, dijkstra_ind) = Defn.tprove
 (Defn.Hol_defn "dijkstra"
  `(dijkstra t a [] w = F) /\
   (dijkstra t a (s :: l) w =
    let (x,y) = partition (t s) w
    in EXISTS a x \/ dijkstra t a (x <> l) y)`,
  WF_REL_TAC `measure (\ (_,_,l,w). LENGTH l + LENGTH w)`
  ++ RW_TAC list_ss []
  ++ POP_ASSUM (ASSUME_TAC o SYM)
  ++ MP_TAC (Q.SPECL [`(t : 'a->'a->bool) s`, `w`, `x`, `y`] LENGTH_partition)
  ++ RW_TAC arith_ss []);

val _ = save_thm ("dijkstra_def", dijkstra_def);

val dijkstra = store_thm
  ("dijkstra",
   ``!t a u v.
       EXISTS a u \/ dijkstra t a u v =
       ?k l.
         MEM k u /\ EVERY (\x. MEM x (u <> v)) l /\
         accepting_path t a k l``,
   SIMP_TAC std_ss [EXISTS_MEM]
   ++ recInduct dijkstra_ind
   ++ RW_TAC list_ss [dijkstra_def]
   ++ Introduce `partition (t s) w = (x,y)`
   ++ Q.PAT_ASSUM `!x y. P x y` (MP_TAC o Q.SPECL [`x`, `y`])
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [RIGHT_AND_OVER_OR, EXISTS_OR_THM, GSYM DISJ_ASSOC]
   ++ RW_TAC std_ss [DISJ_ASSOC]
   ++ Know
      `(a s \/ (?k. IS_EL k l /\ a k)) \/ SOME_EL a x =
       a s \/ ?k. (IS_EL k x \/ IS_EL k l) /\ a k`
   >> METIS_TAC [EXISTS_MEM]
   ++ DISCH_THEN (fn th => REWRITE_TAC [th])
   ++ RW_TAC std_ss [GSYM DISJ_ASSOC]
   ++ Q.PAT_ASSUM `X = Y` (K ALL_TAC)
   ++ Cases_on
      `?q.
         ALL_EL (\k. (k = s) \/ IS_EL k l \/ IS_EL k w) q /\
         accepting_path t a s q`
   >> (ASM_SIMP_TAC std_ss []
       ++ Know
          `?q. ALL_EL (\x. IS_EL x l \/ IS_EL x w) q /\ accepting_path t a s q`
       >> (POP_ASSUM STRIP_ASSUME_TAC
           ++ MP_TAC (Q.SPECL [`\k. ~(k = s)`, `t`, `a`, `s`, `l'`]
                      accepting_path_tail)
           ++ RW_TAC std_ss []
           ++ Q.EXISTS_TAC `js`
           ++ RW_TAC std_ss []
           ++ Suff `ALL_EL (\k. ~(k = s)) js /\
                    ALL_EL (\k. (k = s) \/ IS_EL k l \/ IS_EL k w) js`
           >> (SIMP_TAC std_ss [GSYM EVERY_CONJ]
               ++ Q.SPEC_TAC (`js`, `js`)
               ++ MATCH_MP_TAC EVERY_MONOTONIC
               ++ RW_TAC std_ss [FUN_EQ_THM]
               ++ METIS_TAC [])
           ++ RW_TAC std_ss []
           ++ Q.PAT_ASSUM `X = BUTFIRSTN N L` MP_TAC
           ++ Cases_on `n`
           ++ RW_TAC std_ss [BUTFIRSTN]
           ++ Know `js = TL (BUTFIRSTN n' l')` >> METIS_TAC [TL]
           ++ RW_TAC arith_ss [BUTFIRSTN_TL]
           ++ METIS_TAC [ALL_EL_BUTFIRSTN])
       ++ POP_ASSUM (K ALL_TAC)
       ++ RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ Cases_on `q`
       ++ RW_TAC std_ss [accepting_path_def]
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `h`
       ++ Q.EXISTS_TAC `t'`
       ++ RW_TAC std_ss []
       >> (FULL_SIMP_TAC std_ss [EVERY_DEF] ++ METIS_TAC [MEM_partition])
       ++ MATCH_MP_TAC EVERY_MONO
       ++ Q.EXISTS_TAC `\k. MEM k l \/ MEM k w`
       ++ (RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [EVERY_DEF])
       ++ METIS_TAC [MEM_partition])
   ++ ASM_SIMP_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ SIMP_TAC std_ss []
   ++ DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [PROVE [] ``a \/ b = ~a ==> b``])
   ++ SIMP_TAC std_ss []
   ++ STRIP_TAC
   ++ Cases_on `a s`
   >> (Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `[]`)
       ++ RW_TAC std_ss [EVERY_DEF, accepting_path_def])
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [RIGHT_AND_OVER_OR, EXISTS_OR_THM]
   ++ MATCH_MP_TAC (PROVE [] ``~a /\ (b = c) ==> (a \/ b = c)``)
   ++ CONJ_TAC
   >> (SIMP_TAC std_ss []
       ++ ONCE_REWRITE_TAC [PROVE [] ``a \/ b = ~a ==> b``]
       ++ ONCE_REWRITE_TAC [PROVE [] ``a \/ b = ~a ==> b``]
       ++ RW_TAC std_ss []
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `k :: l'`)
       ++ RW_TAC std_ss [EVERY_DEF, accepting_path_def]
       << [METIS_TAC [MEM_partition],
           MATCH_MP_TAC EVERY_MONO
           ++ Q.EXISTS_TAC `\k. IS_EL k x \/ IS_EL k l \/ IS_EL k y`
           ++ RW_TAC std_ss []
           ++ METIS_TAC [MEM_partition],
           METIS_TAC [MEM_partition]])
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``(!x y. A x y /\ C x y ==> (B x y = D x y)) ==>
         ((?x y. A x y /\ B x y /\ C x y) = (?x y. A x y /\ D x y /\ C x y))``)
   ++ RW_TAC std_ss []
   ++ EQ_TAC
   >> (Q.SPEC_TAC (`l'`, `l'`)
       ++ MATCH_MP_TAC EVERY_MONOTONIC
       ++ METIS_TAC [MEM_partition])
   ++ STRIP_TAC
   ++ Suff `EVERY (\k. ~(k = s)) l'`
   >> (POP_ASSUM MP_TAC
       ++ SIMP_TAC std_ss [AND_IMP_INTRO, GSYM EVERY_CONJ]
       ++ Q.SPEC_TAC (`l'`, `l'`)
       ++ MATCH_MP_TAC EVERY_MONOTONIC
       ++ METIS_TAC [MEM_partition])
   ++ RW_TAC std_ss [EVERY_MEM, MEM_EL]
   ++ CCONTR_TAC
   ++ FULL_SIMP_TAC std_ss []
   ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `BUTFIRSTN (SUC n) l'`)
   ++ RW_TAC std_ss []
   >> (Q.PAT_ASSUM `EVERY P L` MP_TAC
       ++ Q.SPEC_TAC (`EL n l'`, `s`)
       ++ RW_TAC std_ss []
       ++ Know `SUC n <= LENGTH l'` >> DECIDE_TAC
       ++ Q.SPEC_TAC (`n`, `n`)
       ++ MATCH_MP_TAC ALL_EL_BUTFIRSTN
       ++ RW_TAC std_ss [])
   ++ POP_ASSUM MP_TAC
   ++ Q.PAT_ASSUM `accepting_path t a k l'` MP_TAC
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ SIMP_TAC std_ss [AND_IMP_INTRO]
   ++ Q.SPEC_TAC (`k`, `k`)
   ++ Q.SPEC_TAC (`l'`, `l`)
   ++ Induct_on `n`
   ++ Cases
   ++ RW_TAC arith_ss [LENGTH, BUTFIRSTN, EL, HD, TL, accepting_path_def]
   ++ METIS_TAC []);

val dijkstra_partition = store_thm
  ("dijkstra_partition",
   ``!t a p l u v.
       (partition p l = (u,v)) ==>
       (EXISTS a u \/ dijkstra t a u v =
        ?k ks. MEM k u /\ EVERY (\j. MEM j l) ks /\ accepting_path t a k ks)``,
   RW_TAC std_ss [dijkstra, MEM_APPEND]
   ++ Suff `!j. MEM j l = MEM j u \/ MEM j v`
   >> RW_TAC std_ss []
   ++ METIS_TAC [MEM_partition]);

val dijkstra1 = store_thm
  ("dijkstra1",
   ``!t a s l.
       MEM s l ==>
       (a s \/ dijkstra t a [s] (FILTER (\x. ~(x = s)) l) =
        ?ks. EVERY (\j. MEM j l) ks /\ accepting_path t a s ks)``,
   RW_TAC std_ss []
   ++ Know `a s = EXISTS a [s]` >> RW_TAC std_ss [EXISTS_DEF]
   ++ DISCH_THEN (fn th => REWRITE_TAC [th])
   ++ RW_TAC std_ss [dijkstra]
   ++ RW_TAC std_ss [MEM, MEM_APPEND]
   ++ Suff `!j. (j = s) \/ IS_EL j (FILTER (\x. ~(x = s)) l) = IS_EL j l`
   >> RW_TAC std_ss []
   ++ RW_TAC std_ss [MEM_FILTER]
   ++ METIS_TAC []);

(*---------------------------------------------------------------------------*)
(* BIGLIST is designed to speed up evaluation of very long lists.            *)
(* (But it doesn't seem to have the desired effect, so we don't use it.)     *)
(*---------------------------------------------------------------------------*)

val drop_def = pureDefine
  `(drop 0 l = l) /\
   (drop (SUC i) l = if NULL l then [] else drop i (TL l))`;

val BIGLIST_def = Define `BIGLIST l = drop 0 l`;

val drop_nil = lemma
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

val na2da_lemma = lemma
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
       \s. (s = i + 1) \/ a s)) /\
   (regexp2na (Prefix r) =
    let (i,t,a) = regexp2na r in
    (i, t, \s. ?l. accepting_path (\s s'. ?x. t s x s') a s l))`;

val regexp2da_def = Define `regexp2da r = na2da (regexp2na r)`;

val da_match_def = Define `da_match r = da_accepts (regexp2da r)`;

(*---------------------------------------------------------------------------*)
(* Correctness of the finite automata matcher                                *)
(*---------------------------------------------------------------------------*)

val regexp2na_bounds = lemma
  (``!r i trans acc.
       (regexp2na r = (i,trans,acc)) ==>
       (!s. acc s ==> s <= i) /\
       (!s x s'. trans s x s' ==> s <= i /\ s' <= i)``,
   Induct
   << [(* Atom *)
       FULL_SIMP_TAC std_ss [regexp2na_def],
       (* # *)
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ STRIP_TAC
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss []
       ++ Know `!j. j - (i2 + 1) <= i1 ==> j <= i1 + i2 + 1` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL],
       (* % *)
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss []
       ++ Know `!j. j - (i2 + 1) <= i1 ==> j <= i1 + i2 + 1` >> DECIDE_TAC
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM],
       (* | *)
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
       (* & *)
       Introduce `r = r1`
       ++ Introduce `r' = r2`
       ++ REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r1 = (i1,t1,a1)`
       ++ Introduce `regexp2na r2 = (i2,t2,a2)`
       ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPECL [`i2`,`t2`,`a2`])
       ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPECL [`i1`,`t1`,`a1`])
       ++ SIMP_TAC std_ss []
       ++ REPEAT (DISCH_THEN STRIP_ASSUME_TAC)
       ++ CONJ_TAC
       << [REPEAT (POP_ASSUM MP_TAC)
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
           REPEAT (POP_ASSUM MP_TAC)
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
               ++ METIS_TAC []]],
       (* Repeat *)
       REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r = (i,t,a)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       ++ METIS_TAC [LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM, LESS_EQ_REFL],
       (* Prefix *)
       REPEAT GEN_TAC
       ++ SIMP_TAC std_ss [regexp2na_def]
       ++ Introduce `regexp2na r = (i,t,a)`
       ++ REPEAT (POP_ASSUM MP_TAC)
       ++ (RW_TAC std_ss [] ++ POP_ASSUM MP_TAC ++ RW_TAC std_ss [])
       << [POP_ASSUM MP_TAC
           ++ Cases_on `l`
           ++ RW_TAC std_ss [accepting_path_def]
           ++ METIS_TAC [],
           METIS_TAC [],
           METIS_TAC []]]);

val regexp2na_acc = lemma
  (``!r i trans acc s. (regexp2na r = (i,trans,acc)) /\ acc s ==> s <= i``,
   METIS_TAC [regexp2na_bounds]);

val regexp2na_trans = lemma
  (``!r i trans acc s x s'.
       (regexp2na r = (i,trans,acc)) /\ trans s x s' ==> s <= i /\ s' <= i``,
   METIS_TAC [regexp2na_bounds]);

val na_match_atom = lemma
  (``!b l. na_accepts (regexp2na (Atom b)) l = sem (Atom b) l``,
   RW_TAC std_ss [regexp2na_def, sem_def, LENGTH_EQ_ONE, na_accepts_def]
   ++ Cases_on `l`
   ++ RW_TAC std_ss [na_step_def, HD]
   ++ Cases_on `t`
   ++ RW_TAC std_ss [na_step_def, HD]);

val na_match_concat = lemma
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 # r2)) l = sem (r1 # r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ NTAC 2 (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def])
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

val na_match_fuse = lemma
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 % r2)) l = sem (r1 % r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ NTAC 2 (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def])
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

val na_match_or = lemma
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 | r2)) l = sem (r1 | r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ NTAC 2 (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def])
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

val na_match_and = lemma
  (``!r1 r2.
       (!l. na_accepts (regexp2na r1) l = sem r1 l) /\
       (!l. na_accepts (regexp2na r2) l = sem r2 l) ==>
       !l. na_accepts (regexp2na (r1 & r2)) l = sem (r1 & r2) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r1 = (i1, t1, a1)`
   ++ Introduce `regexp2na r2 = (i2, t2, a2)`
   ++ NTAC 2 (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def])
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

val na_match_repeat = lemma
  (``!r.
       (!l. na_accepts (regexp2na r) l = sem r l) ==>
       !l. na_accepts (regexp2na (Repeat r)) l = sem (Repeat r) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r = (i, t, a)`
   ++ (NTAC 2 (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def])
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

val na_match_prefix = lemma
  (``!r.
       (!l. na_accepts (regexp2na r) l = sem r l) ==>
       !l. na_accepts (regexp2na (Prefix r)) l = sem (Prefix r) l``,
   REPEAT GEN_TAC
   ++ Introduce `regexp2na r = (i, t, a)`
   ++ (NTAC 2 (RW_TAC std_ss [regexp2na_def, sem_def, na_accepts_def])
       ++ (REPEAT o Q.PAT_ASSUM `!x. P x`)
          (fn th => REWRITE_TAC [GSYM (MATCH_MP EQ_EXT th)]))
   ++ Suff
      `!k.
         na_step
         (i,t,(\s. ?l. accepting_path (\s s'. ?x. t s x s') a s l)) k l =
         ?w'. na_step (i,t,a) k (l <> w')`
   >> RW_TAC std_ss []
   ++ REVERSE (Induct_on `l`)
   >> (RW_TAC std_ss [na_step_def, APPEND]
       ++ HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (!s. P s ==> (Q s = ?w. R w s)) ==>
               ((?s. P s /\ Q s) = ?w s. P s /\ R w s)``)
       ++ POP_ASSUM (fn th => RW_TAC std_ss [GSYM th]))
   ++ RW_TAC std_ss [APPEND, na_step_def]
   ++ Suff
      `!n k.
         (?l. (LENGTH l = n) /\ accepting_path (\s s'. ?x. t s x s') a k l) =
         ?w'. (LENGTH w' = n) /\ na_step (i,t,a) k w'`
   >> METIS_TAC []
   ++ Induct >> RW_TAC std_ss [LENGTH_NIL, accepting_path_def, na_step_def]
   ++ RW_TAC std_ss [LENGTH_CONS, accepting_path_def, na_step_def,
                     GSYM LEFT_EXISTS_AND_THM]
   ++ METIS_TAC []);

val na_match = lemma
  (``!r l. na_accepts (regexp2na r) l = sem r l``,
   Induct
   ++ RW_TAC std_ss
      [na_match_atom, na_match_concat, na_match_fuse,
       na_match_or, na_match_and, na_match_repeat, na_match_prefix]);

val da_accepts_regexp2da = lemma
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

(*
val (accept_regexp2na_prefix_def, accept_regexp2na_prefix_ind) = Defn.tprove
  (Defn.Hol_defn "accept_regexp2na_prefix"
   `(accept_regexp2na_prefix r [] w = F) /\
    (accept_regexp2na_prefix r (s :: l) w =
     accept_regexp2na_prefix' r s l [] w) /\
    (accept_regexp2na_prefix' r s l w [] = accept_regexp2na_prefix r l w) /\
    (accept_regexp2na_prefix' r s l w (h :: t) =
     if (?x. transition_regexp2na r s x h) then
       accept_regexp2na r h \/ accept_regexp2na_prefix' r s (h :: l) w t
     else accept_regexp2na_prefix' r s l (h :: w) t)`,
   WF_REL_TAC
   `MLEX (sum_case (\ (_,l,w). 2 * (LENGTH l + LENGTH w))
          (\ (_,_,l,w,t). 2 * (LENGTH l + LENGTH w + LENGTH t) + 1))
    (measure (sum_case (\_. 0) (\ (_,_,_,_,t). LENGTH t)))`
   ++ RW_TAC arith_ss [MLEX_def, LENGTH]
   ++ RW_TAC std_ss [GSYM prim_recTheory.measure_thm]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ METIS_TAC [WF_MLEX, prim_recTheory.WF_measure]);

val accept_regexp2na_prefix_ind1 = hd (GCONJUNCTS accept_regexp2na_prefix_ind);
*)

val exists_transition_regexp2na_def = pureDefine
  `exists_transition_regexp2na r s s' = ?x. transition_regexp2na r s x s'`;

val transition_regexp2na_fuse_def = Define
  `(transition_regexp2na_fuse a t 0 = F) /\
   (transition_regexp2na_fuse a t (SUC s') =
    a s' /\ t s' \/ transition_regexp2na_fuse a t s')`;

val transition_regexp2na_fuse = lemma
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
      if accept_regexp2na r i then i else i + 1) /\
     (initial_regexp2na (Prefix r : 'a regexp) = initial_regexp2na r)``,
   Introduce `regexp2na r1 = (i1,t1,a1)`
   ++ Introduce `regexp2na r2 = (i2,t2,a2)`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ NTAC 2
      (RW_TAC std_ss
       [regexp2na_def, initial_def, accept_def,
        initial_regexp2na_def, accept_regexp2na_def]));

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
      (s = i + 1) /\ ~accept_regexp2na r i) /\
     (accept_regexp2na (Prefix r : 'a regexp) s =
      accept_regexp2na r s \/
      dijkstra (exists_transition_regexp2na r) (accept_regexp2na r)
      [s] (FILTER (\x. ~(x = s)) (interval 0 (SUC (initial_regexp2na r)))))``,
   Introduce `regexp2na r1 = (i1,t1,a1)`
   ++ Introduce `regexp2na r2 = (i2,t2,a2)`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ NTAC 2
      (RW_TAC std_ss
       [regexp2na_def, initial_def, accept_def,
        initial_regexp2na_def, accept_regexp2na_def])
   >> METIS_TAC []
   ++ Know `exists_transition_regexp2na r = \s s'. ?x. t s x s'`
   >> RW_TAC std_ss
      [exists_transition_regexp2na_def, FUN_EQ_THM,
       transition_regexp2na_def, transition_def]
   ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
   ++ REVERSE (Cases_on `s <= i`)
   >> (MATCH_MP_TAC (PROVE [] ``~a /\ ~b ==> (a = b)``)
       ++ RW_TAC std_ss []
       << [Cases_on `l`
           ++ RW_TAC std_ss [accepting_path_def]
           ++ METIS_TAC [regexp2na_acc, regexp2na_trans],
           METIS_TAC [regexp2na_acc],
           RW_TAC std_ss [dijkstra_def]
           ++ Suff `!l. partition (\s'. ?x. t s x s') l = ([],l)`
           >> (DISCH_THEN (fn th => FULL_SIMP_TAC std_ss [th])
               ++ RW_TAC std_ss [EXISTS_DEF, APPEND, dijkstra_def])
           ++ Induct
           ++ RW_TAC std_ss [partition_def]
           ++ METIS_TAC [regexp2na_trans]])
   ++ Know `MEM s (interval 0 (SUC i))`
   >> RW_TAC arith_ss [MEM_interval]
   ++ RW_TAC std_ss [dijkstra1]
   ++ REVERSE EQ_TAC >> METIS_TAC []
   ++ RW_TAC arith_ss [MEM_interval]
   ++ Q.EXISTS_TAC `l`
   ++ Know `!k. k < SUC i = k <= i` >> DECIDE_TAC
   ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ Induct_on `l`
   ++ RW_TAC std_ss [accepting_path_def, EVERY_DEF]
   ++ METIS_TAC [regexp2na_trans]);

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
        accept_regexp2na r s /\ transition_regexp2na r i x s') /\
     (transition_regexp2na (Prefix r : 'a regexp) s x s' =
      transition_regexp2na r s x s')``,
   Introduce `regexp2na r1 = (i1,t1,a1)`
   ++ Introduce `regexp2na r2 = (i2,t2,a2)`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ NTAC 2
      (RW_TAC std_ss
       [regexp2na_def, initial_def, accept_def, transition_def,
        initial_regexp2na_def, accept_regexp2na_def, transition_regexp2na_def])
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

val eval_accepts_def = pureDefine
  `(eval_accepts (Prefix r) l =
    EXISTS (accept_regexp2na r) l \/
    let i = initial_regexp2na r in
    dijkstra (exists_transition_regexp2na r) (accept_regexp2na r)
    l (FILTER (\x. ~MEM x l) (interval 0 (SUC (initial_regexp2na r))))) /\
   (eval_accepts r l = EXISTS (accept_regexp2na r) l)`;

val eval_accepts = prove
  (``!r l. eval_accepts r l = EXISTS (accept_regexp2na r) l``,
   Cases
   ++ RW_TAC std_ss [eval_accepts_def]
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss []
   ++ Introduce `r' = r`
   ++ Introduce `regexp2na r = (i,t,a)`
   ++ RW_TAC std_ss [dijkstra]
   ++ RW_TAC std_ss [MEM_APPEND, EXISTS_MEM, accept_regexp2na_def,
                     accept_def, regexp2na_def]
   ++ Know `exists_transition_regexp2na r = \s s'. ?x. t s x s'`
   >> RW_TAC std_ss
      [exists_transition_regexp2na_def, FUN_EQ_THM,
       transition_regexp2na_def, transition_def]
   ++ DISCH_THEN (fn th => RW_TAC std_ss [th])
   ++ RW_TAC arith_ss [MEM_FILTER, MEM_interval]
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``(!l k. C k l ==> B k l) ==>
         ((?k l'. A k /\ B k l' /\ C k l') = (?e. A e /\ ?l. C e l))``)
   ++ Know `!x y. x < SUC y = x <= y` >> DECIDE_TAC
   ++ DISCH_THEN
      (fn th => ASM_SIMP_TAC std_ss [th, initial_regexp2na_def, initial_def])
   ++ Induct
   ++ RW_TAC std_ss [EVERY_DEF, accepting_path_def]
   ++ METIS_TAC [regexp2na_trans]);

val calc_transitions_def = Define
  `(calc_transitions r l c 0 a = a) /\
   (calc_transitions r l c (SUC s') a =
    calc_transitions r l c s'
    (if EXISTS (\s. transition_regexp2na r s c s') l then s' :: a else a))`;

val eval_transitions_def = pureDefine
  `eval_transitions r l c =
   calc_transitions r l c (SUC (initial_regexp2na r)) []`;

val areport_def = pureDefine `areport h b = b`;

val astep_def = Define
  `(astep r l [] = eval_accepts r l) /\
   (astep r l (c :: cs) = astep r (eval_transitions r l c) cs)`;

val amatch_def = Define
  `amatch r l = let i = initial_regexp2na r in astep r [i] l`;

val acheckpt_def = Define
  `(acheckpt r f h l [] = T) /\
   (acheckpt r f h l (c :: cs) =
    let l' = eval_transitions r l c in
    let h = c :: h in
    (eval_accepts r l' ==> areport h (f (c :: cs))) /\ acheckpt r f h l' cs)`;

val acheck_def = Define
  `acheck r f l = let i = initial_regexp2na r in acheckpt r f [] [i] l`;

(*---------------------------------------------------------------------------*)
(* Correctness of this version of the automata matcher.                      *)
(*---------------------------------------------------------------------------*)

val da_accepts_na2da = lemma
  (``!n. da_accepts (na2da n) = da_step (na2da n) (set_of_list [initial n])``,
   STRIP_TAC
   ++ Introduce `n = (i,t,a)`
   ++ RW_TAC std_ss
      [FUN_EQ_THM, na2da_def, da_accepts_def, initial_def, set_of_list_def]);

val da_step_regexp2na = lemma
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
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss [initial_regexp2na_def]
   ++ Suff `!k. astep r k l = da_step (na2da (regexp2na r)) (set_of_list k) l`
   >> RW_TAC std_ss []
   ++ Induct_on `l`
   >> RW_TAC std_ss
      [astep_def, da_step_def, na2da_def, eval_accepts, EXISTS_MEM,
       set_of_list, accept_regexp2na_def]
   ++ ONCE_REWRITE_TAC [astep_def]
   ++ SIMP_TAC std_ss [da_step_regexp2na, eval_transitions_def, NULL_DEF, TL]
   ++ RW_TAC std_ss [initial_regexp2na_def, HD]);

val acheck = store_thm
  ("acheck",
   ``!r l.
       acheck r f l =
       !n. n < LENGTH l /\ sem r (FIRSTN (SUC n) l) ==> f (BUTFIRSTN n l)``,
   RW_TAC std_ss
   [acheck_def, GSYM da_match, da_match_def, regexp2da_def, da_accepts_na2da]
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss [initial_regexp2na_def]
   ++ Q.SPEC_TAC (`[initial (regexp2na r)]`, `k`)
   ++ Q.SPEC_TAC (`[]`, `h`)
   ++ Induct_on `l` >> RW_TAC arith_ss [acheckpt_def, LENGTH]
   ++ ONCE_REWRITE_TAC [acheckpt_def]
   ++ RW_TAC std_ss []
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss []
   ++ HO_MATCH_MP_TAC
      (METIS_PROVE [num_CASES]
       ``(P = Q 0 /\ !n. Q (SUC n)) ==> (P = !n. Q n)``)
   ++ RW_TAC arith_ss
      [LENGTH, FIRSTN, BUTFIRSTN, da_step_regexp2na, areport_def, eval_accepts,
       accept_regexp2na_def, eval_transitions_def, initial_regexp2na_def]);

val () = export_theory ();
