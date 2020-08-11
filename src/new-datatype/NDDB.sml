structure NDDB :> NDDB =
struct

open NDSupportTheory

val C_DEF = combinTheory.C_DEF;
val o_DEF = combinTheory.o_DEF;

val one_ty = oneSyntax.one_ty;

val J_tm = Term`J`;
val KT_tm = Term`KT`;

val RW_HELP_TAC = CONV_TAC (REWR_CONV FUN_EQ_THM) THEN Cases;

val DEEP_SYM = GEN_ALL o SYM o SPEC_ALL;

(* rich types storage *)

type rich_type = {
  inj_pair: Thm.thm,
  ret_map : Thm.thm,
  (* ALL *)
  all_tm   : Term.term,
  all_thm  : Thm.thm,
  all_map  : Thm.thm,
  all_T    : Thm.thm,
  all_mono : Thm.thm
};

(* empty types store *)
val types = ref ([]:string list, []:rich_type list);

local
  fun insert (a:string) (b:rich_type) ([], []) = ([a], [b])
    | insert a b (x::xs, y::ys) = if a = x
        then (x::xs, b::ys)
        else (
        let val (X, Y) = insert a b (xs, ys)
        in (x::X, y::Y) end)
in
  fun register_type(a, b) = K () (types := insert a b (!types))
end;


(* *val fun_positivity_map = ``[F; T]``;*)

(* map definitions *)
val map_defs = [
     fun_map_def,
     sum_map_def,
    prod_map_def,
    list_map_def,
  option_map_def
];

(* retrieve definitions *)

(* ``combin$C (((combin$C $o) combin$C) o ($o o OPTION_BIND))`` *)

val retrieve_defs = [
     fun_retrieve_def,
     sum_retrieve_def,
    prod_retrieve_def,
    list_retrieve_def,
  option_retrieve_def
];


(************************ ALL definitions ************************)

(*****************************************************************)

val sum_prod_duality = prove(``!f1 f2.
     (prod_retrieve f1 f2) =
     (combin$C (sum_retrieve (combin$C f1) (combin$C f2)))``,
   simp[C_DEF]
>> REPEAT GEN_TAC
>> REPEAT RW_HELP_TAC
>> BETA_TAC
>> simp[sum_retrieve_def, prod_retrieve_def]
);

(*-- injective pairs --*)

val inj_pair_tm = prim_mk_const {Name="inj_pair", Thy="NDSupport"};

val inj_pair_id = prove(``!f. inj_pair I f``,
    simp[inj_pair_def, combinTheory.I_DEF]);

val inj_pair_some = prove(``!g. inj_pair g (\x (y:one).SOME x)``,
    simp[inj_pair_def, ABS_SIMP]);

val _ = prove(``!g. INJ g = inj_pair g J``,
      simp[inj_pair_def, INJ_def, J_def]);


(*(********** CLOSED UNDER INJECTIONS ******)
val inj_pair_closed = prove(``!f g h.
    INJ h ==> (inj_pair f g) ==> (inj_pair (f o h) (g o h))``,
   simp[inj_pair_def, INJ_def, o_DEF]
);
val retrieve_map_closed = prove(``
(((g o (h:'b->'a)) o (f o (h:'d->'a)) = ((($o g):('b->'a)->'b->'c->'e) f) o (h:'d->'a)))  ``
``(g o h) o (f o h) = (g o f) o h``
simp[o_DEF, inj_pair_def]


prove(``!f1 g1 f2 g2.
 ((sum_retrieve g1 g2)o h) o ((sum_map f1 f2)o h) =
 ((sum_retrieve (g1 o f1) (g2 o f2)) o h)``

Cases_on`h (INL x')`
Cases_on`h (INL (f1 x))`
*)

(*************************** SUM TYPE ****************************)

val sum_inj_pair_thm = prove(``!f1 g1 f2 g2.
  (inj_pair f1 g1) ==>
  (inj_pair f2 g2) ==>
  (inj_pair (sum_map f1 f2) (sum_retrieve g1 g2))``,
   REPEAT GEN_TAC
>> simp[inj_pair_def] >> REPEAT DISCH_TAC >> Cases
>> simp[pairTheory.FORALL_PROD] >> simp[sum_retrieve_def]
>> Cases
>> simp[sum_retrieve_def, sum_map_def, sumTheory.SUM_MAP_def]
);

val sum_retrieve_map_thm = prove(``!f1 g1 f2 g2.
 (sum_retrieve g1 g2) o (sum_map f1 f2) =
 (sum_retrieve (g1 o f1) (g2 o f2))
``, REPEAT GEN_TAC >> simp[o_DEF]
>> RW_HELP_TAC
>> BETA_TAC >> simp[sum_map_def]
>> RW_HELP_TAC
>> simp[sum_retrieve_def]);

val sum_fancy_all_thm = prove(``!P Q z. sum_all P Q z =
    (!b. sum_retrieve (\x u. SOME (P x)) (\y u. SOME (Q y)) z b <> SOME F)``,
   GEN_TAC >> GEN_TAC >> Cases
>> simp[pairTheory.FORALL_PROD]
>> simp[sum_retrieve_def, sum_all_def]
);

val sum_all_map_thm = prove(``!P1 P2 f1 f2.
  (sum_all P1 P2) o (sum_map f1 f2) = sum_all (P1 o f1) (P2 o f2)
``, REPEAT GEN_TAC >> simp[o_DEF]
>> RW_HELP_TAC
>> BETA_TAC >> simp[sum_map_def]
>> simp[sum_all_def]
);

val sum_all_T_thm = prove(``sum_all KT KT = KT``,
  RW_HELP_TAC >> simp[sum_all_def, KT_def]
);

val sum_all_mono_thm = prove(``!P Q P' Q'.
  (P SUBSET P') /\ (Q SUBSET Q') ==> (sum_all P Q) SUBSET (sum_all P' Q')
``, simp[pred_setTheory.SUBSET_DEF, boolTheory.IN_DEF]
>> REPEAT GEN_TAC >> REPEAT DISCH_TAC
>> Cases >> simp[sum_all_def]
);

val _ = register_type("sum", {
  inj_pair = sum_inj_pair_thm,
  ret_map = sum_retrieve_map_thm,
  all_tm = ``sum_all``,
  all_thm = sum_all_def,
  all_map = sum_all_map_thm,
  all_T = sum_all_T_thm,
  all_mono = sum_all_mono_thm
});


(*************************** PROD TYPE ***************************)

val prod_inj_pair_thm = prove(``!f1 g1 f2 g2.
  (inj_pair f1 g1) ==>
  (inj_pair f2 g2) ==>
  (inj_pair (f1 ## f2) (prod_retrieve g1 g2))``,
   REPEAT GEN_TAC
>> simp[inj_pair_def] >> REPEAT DISCH_TAC
>> Cases >> Cases >> DISCH_TAC >> fs[]
>> first_assum(fn th => (Q.GENL [`z'`]
     (Q.SPEC `INL z'` th)) |> BETA_RULE |> ASSUME_TAC)
>> first_x_assum(fn th => (Q.GENL [`z''`]
     (Q.SPEC `INR z''` th)) |> BETA_RULE |> ASSUME_TAC)
>> fs[prod_retrieve_def, prod_map_def, pairTheory.PAIR_MAP]
);

val prod_retrieve_map_thm = prove(``!f1 g1 f2 g2.
 (prod_retrieve g1 g2) o (f1 ## f2) =
 (prod_retrieve (g1 o f1) (g2 o f2))
``, REPEAT GEN_TAC >> simp[o_DEF]
>> RW_HELP_TAC >> BETA_TAC
>> RW_HELP_TAC >> simp[prod_retrieve_def]
);

(*val prod_fancy_all_thm = prove(``!P Q z. prod_all P Q z =
    (!b. prod_retrieve (\x u. SOME (P x)) (\y u. SOME (Q y)) z b <> SOME F)``,
   GEN_TAC >> GEN_TAC >> Cases
>> simp[sumTheory.FORALL_SUM]
>> simp[prod_retrieve_def, prod_all_def]
);*)


val prod_all_map_thm = prove(``!P1 P2 f1 f2.
 (prod_all P1 P2) o (prod_map f1 f2) = prod_all (P1 o f1) (P2 o f2)
``, REPEAT GEN_TAC >> simp[o_DEF]
>> RW_HELP_TAC
>> BETA_TAC >> simp[prod_map_def, prod_all_def]
);

val prod_all_T_thm = prove(``prod_all KT KT = KT``,
  RW_HELP_TAC >> simp[prod_all_def, KT_def]
);

val prod_all_mono_thm = prove(``!P Q P' Q'.
  (P SUBSET P') /\ (Q SUBSET Q') ==> (prod_all P Q) SUBSET (prod_all P' Q')
``, simp[pred_setTheory.SUBSET_DEF, boolTheory.IN_DEF]
>> REPEAT GEN_TAC >> REPEAT DISCH_TAC
>> Cases >> simp[prod_all_def]
);


val _ = register_type("prod", {
  inj_pair = prod_inj_pair_thm,
  ret_map = prod_retrieve_map_thm,
  all_thm = prod_all_def,
  all_tm = ``prod_all``,
  all_map = prod_all_map_thm,
  all_T = prod_all_T_thm,
  all_mono = prod_all_mono_thm
});


(*************************** LIST TYPE ***************************)

val _ = register_type("list", {
  inj_pair = TRUTH,
  ret_map = TRUTH,
  all_thm = listTheory.EVERY_DEF,
  all_tm = ``list_all``,
  all_map = TRUTH, all_T = TRUTH, all_mono = TRUTH
});

(*
val list_inj_pair_thm = prove(``!f g.
  (inj_pair f g) ==>
  (inj_pair (MAP f) (list_retrieve g))``,
   REPEAT GEN_TAC
>> simp[inj_pair_def] >> REPEAT DISCH_TAC

>> Induct >> Induct_on`y`
>> simp[listTheory.MAP]
>> REPEAT GEN_TAC >> DISCH_TAC >> fs[]

first_x_assum(fn th => (Q.SPEC `(SUC n, c)` th) |> BETA_RULE |> ASSUME_TAC)

fs[list_retrieve_def]

first_x_assum(fn th => (Q.SPEC `x` th) |> BETA_RULE |> ASSUME_TAC)


>> DISCH_TAC >> fs[]
>> first_x_assum(fn th => (Q.GENL [`c`, `n`]
     (Q.SPEC `(n, c)` th)) |> BETA_RULE |> ASSUME_TAC)

>> first_assum(fn th => ((Q.SPEC `0` th)) |> BETA_RULE |> ASSUME_TAC)
>>
>> first_x_assum(fn th => ((Q.SPEC `SUC n` th)) |> BETA_RULE |> ASSUME_TAC)

>> fs[prod_retrieve_def, prod_map_def, pairTheory.PAIR_MAP]
);

val prod_retrieve_map_thm = prove(``!f1 g1 f2 g2.
 (prod_retrieve g1 g2) o (f1 ## f2) =
 (prod_retrieve (g1 o f1) (g2 o f2))
``, REPEAT GEN_TAC >> simp[o_DEF]
>> RW_HELP_TAC >> BETA_TAC
>> RW_HELP_TAC >> simp[prod_retrieve_def]
);

register_type("prod", {
  inj_pair = pair_inj_pair_thm,
  ret_map = prod_retrieve_map_thm,
  map_map = TRUTH
});



*)(*
val list_inj_pair = prove(
``(inj_pair f g) ==> (inj_pair (list_retrieve f) (list_map g))``,

  simp[inj_pair_def, list_map_def, listTheory.MAP] >> DISCH_TAC >> Induct >> Induct >> simp[] >> Induct_on`y` >> simp[]

simp[pairTheory.FORALL_PROD, list_retrieve_def]
>> REPEAT DISCH_TAC
*)

(*
val tm = ``(\pi. list_CASE pi (g x) (f x)) = (\pi. list_CASE pi (g y) (f y))``;
val ass = ASSUME tm
val th1 = AP_THM ass ``[]:'a list``
val th2 = BETA_RULE th1
val one = PURE_ASM_REWRITE_RULE [listTheory.list_case_def] th2
val th3 = BETA_RULE (Q.AP_THM ass `z::t`)
val th4 = PURE_ASM_REWRITE_RULE [listTheory.list_case_def] th3
val th5 = EXT (Q.GEN `t` th4)
val two = Q.GEN `z` th5
val th6 = CONJ two one


Q.GENL [`y`, `x`] th6

``(inj_pair f g) ==> (INJ (\t pi. list_CASE pi (g t) (f t)) (\_.T) (\_.T))``

simp[inj_pair_def, pred_setTheory.INJ_DEF] >> DISCH_TAC >> REPEAT GEN_TAC

*)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(* constant functions
val retrieve_k =
    mk_abs (mk_var("x",  alpha),
    mk_abs (mk_var("y", one_ty),
    mk_arb(gamma)));
val map_k = I_tm;*)

val some_inj_thm = prove(
``inj_pair (\x. ()) (\x (u:one). SOME x)``, simp[inj_pair_def]);

val k_inj_thm = prove(
``inj_pair I J``, simp[inj_pair_def, J_def]);
val k_map_map_thm = prove(
``I o I = I``, simp[o_DEF]);
val k_ret_map_thm = prove(
``J o I = J``, simp[o_DEF, J_def]);

val k_all_rule = prove(``KT ARB = T``, simp[KT_def]);

val constantly_rich = {
  inj_pair = k_inj_thm,
  ret_map = k_ret_map_thm,
  all_tm = KT_tm,
  all_thm = prove(``!x. KT x = T``,simp[KT_def]),
  all_map = TRUTH,
  all_T   = REFL KT_tm,
  all_mono= SPEC KT_tm pred_setTheory.SUBSET_REFL
} : rich_type;


(* support for option type *)

val option_inj_pair_thm = prove(
``!f g. (inj_pair f g) ==>
  (inj_pair (option_map f) (option_retrieve g))``,
   REPEAT GEN_TAC
>> simp[inj_pair_def] >> DISCH_TAC
>> Induct >> Induct_on`y`
>> simp[option_retrieve_def,
    option_map_def, optionTheory.OPTION_MAP_DEF]
);

val option_map_map_thm = prove(``!f1 f2.
   (option_map f1) o (option_map f2) = (option_map (f1 o f2))
``, REPEAT GEN_TAC >> simp[o_DEF]
>> CONV_TAC (REWR_CONV FUN_EQ_THM) >> Induct
>> simp[option_map_def, optionTheory.OPTION_MAP_DEF]);

val option_retrieve_map_thm = prove(``!f g.
  (option_retrieve g) o (option_map f) = (option_retrieve (g o f))
``, REPEAT GEN_TAC >>  simp[o_DEF]
>> CONV_TAC (REWR_CONV FUN_EQ_THM) >> Induct
>> (TRY GEN_TAC) >> BETA_TAC
>> CONV_TAC (REWR_CONV FUN_EQ_THM) >> GEN_TAC
>> simp[option_map_def,
        optionTheory.OPTION_MAP_DEF, option_retrieve_def]);

(*val option_map_1 = prove(``option_map I = I``,
   RW_HELP_TAC THEN simp[option_map_def, sumTheory.SUM_MAP_def]
);

val option_retrieve_1 = prove(``option_retrieve J = J``,
REPEAT RW_HELP_TAC THEN simp[J_def]
>> CONV_TAC (REWR_CONV FUN_EQ_THM)
>> simp[option_retrieve_def, J_def]
);
*)


val option_all_map_thm = prove(``!P f.
 (option_all P) o (option_map f) = option_all (P o f)
``, REPEAT GEN_TAC >> simp[o_DEF]
>> RW_HELP_TAC
>> BETA_TAC >> simp[option_map_def, option_all_def]
);

val option_all_T_thm = prove(``option_all KT = KT``,
  RW_HELP_TAC >> simp[option_all_def, KT_def]
);

val option_all_mono_thm = prove(``!P P'.
  (P SUBSET P') ==> (option_all P) SUBSET (option_all P')
``, simp[pred_setTheory.SUBSET_DEF, boolTheory.IN_DEF]
>> REPEAT GEN_TAC >> REPEAT DISCH_TAC
>> Cases >> simp[option_all_def]
);


val _ = register_type("option", {
  inj_pair = option_inj_pair_thm,
  ret_map = option_retrieve_map_thm,
  all_tm = ``option_all``,
  all_thm = option_all_def,
  all_map = option_all_map_thm,
  all_T = option_all_T_thm,
  all_mono = option_all_mono_thm
});

(* test: all *)
val _ = prove(``let sum_all2 =
(\P Q x. !p. (option_CASE (sum_retrieve (\x1 _. SOME (P x1)) (\x2 _. SOME (Q x2)) x p) T I)) in (
      (sum_all2 P Q (INL x') = P x')
   /\ (sum_all2 P Q (INR y') = Q y')
)``, simp[] >> CONJ_TAC
>> simp[pairTheory.FORALL_PROD]
>> simp[optionTheory.option_case_def, sum_retrieve_def]);



(**********************************)

(* Constructor *)

val inj_constr_thm = prove(
``!f g. (inj_pair f g) ==> (INJ (\t pi. case pi of
         []    => (f t, 0)
       | p::ps => (case (g t p) of
                     NONE => (ARB, 0)
                   | SOME c => (case c ps of (r, n) => (r, SUC n)
))))
``, REPEAT GEN_TAC
>> simp[INJ_def, inj_pair_def, FUN_EQ_THM]
>> DISCH_TAC >> REPEAT GEN_TAC >> DISCH_TAC
>> first_assum (ASSUME_TAC o BETA_RULE o (Q.SPEC `[]`))
>> first_x_assum(fn th => (Q.GENL [`xs`,`x`]
     (Q.SPEC `x::xs` th)) |> BETA_RULE |> ASSUME_TAC)
>> Cases_on `g t = g t'` >> fs[]
>> first_assum (ASSUME_TAC o (MATCH_MP (CONV_RULE
     CONTRAPOS_CONV (Q.SPECL [`g t`, `g t'`] EQ_EXT))))
>> fs[] >> first_x_assum (ASSUME_TAC o (Q.SPEC `x`))
>> Cases_on `g t x` >> Cases_on `g t' x`
>> fs[optionTheory.option_case_def, pairTheory.pair_CASE_def]
>> first_x_assum (ASSUME_TAC
               o (Q.GEN `xs` )
               o (PURE_REWRITE_RULE
                   [DEEP_SYM pairTheory.PAIR_FST_SND_EQ])
               o (Q.SPEC `xs`))
>> first_x_assum (mp_tac o EXT) >> simp[]
);


(*val inj_constr_thm = prove(
``!f g. (inj_pair f g) ==>
        (INJ (\t pi. list_CASE pi (f t) (g t)))
``, REPEAT GEN_TAC
>> simp[INJ_def, inj_pair_def, FUN_EQ_THM]
>> DISCH_TAC >> REPEAT GEN_TAC >> DISCH_TAC
>> first_assum (ASSUME_TAC o BETA_RULE o (Q.SPEC `[]`))
>> first_x_assum(fn th => (Q.GENL [`xs`,`x`]
     (Q.SPEC `x::xs` th)) |> BETA_RULE |> ASSUME_TAC)
>> Cases_on `g t = g t'` >> fs[]
);*)

end;
