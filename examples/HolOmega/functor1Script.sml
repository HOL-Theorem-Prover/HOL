(*---------------------------------------------------------------------------
             Functors and Natural Transformations in HOL-Omega
                   Version emphasizing rewriting tactics
                       (Peter Vincent Homeier)
 ---------------------------------------------------------------------------*)

structure functor1Script =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory

val _ = set_trace "Unicode" 1;


val _ = new_theory "functor1";


(*---------------------------------------------------------------------------
            Functor type abbreviation
 ---------------------------------------------------------------------------*)

val _ = try type_abbrev ("functor", Type `: \'t. !'a 'b. ('a -> 'b) -> 'a 't -> 'b 't`);

(*---------------------------------------------------------------------------
            Functor predicate
 ---------------------------------------------------------------------------*)

val functor_def = new_definition("functor_def", Term
   `functor (phi: 't functor) =
      (* Identity *)
          (!:'a. phi (I:'a->'a) = I) /\
      (* Homomorphism *)
          (!:'a 'b 'c. !(f:'a -> 'b) (g:'b -> 'c).
                phi (g o f) = phi g o phi f)
     `);

val identity_functor = store_thm
  ("identity_functor",
   ``functor ((\:'a 'b. I) : I functor)``,
   REWRITE_TAC[functor_def]
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[I_THM]
  );

val MAP_I = store_thm
  ("MAP_I",
   ``MAP (I:'a -> 'a) = I``,
   CONV_TAC FUN_EQ_CONV
   THEN Induct
   THEN ASM_REWRITE_TAC[listTheory.MAP,I_THM]
  );

val MAP_o = store_thm
  ("MAP_o",
   ``!(f:'a->'b) (g:'b->'c). MAP (g o f) = MAP g o MAP f``,
   REPEAT GEN_TAC
   THEN CONV_TAC FUN_EQ_CONV
   THEN Induct
   THEN ASM_REWRITE_TAC[listTheory.MAP,o_THM]
  );

val map_functor = store_thm
  ("map_functor",
   ``functor (\:'a 'b. MAP : ('a -> 'b) -> ('a list -> 'b list))``,
   REWRITE_TAC[functor_def]
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[MAP_I,MAP_o]
  );

val map_map_functor0 = store_thm
  ("map_map_functor0",
   ``functor (\:'a 'b. MAP o (MAP : ('a -> 'b) -> ('a list -> 'b list)))``,
   REWRITE_TAC[functor_def]
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[o_THM,MAP_I,MAP_o]
  );

val functor_o = store_thm
  ("functor_o",
   ``!(phi: 't1 functor) (psi: 't2 functor).
      functor phi /\ functor psi ==>
      functor (\:'a 'b. psi o phi)``,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[functor_def]
   THEN REPEAT STRIP_TAC
   THEN TY_BETA_TAC
   THEN ASM_REWRITE_TAC[o_THM]
  );

val map_map_functor = save_thm
  ("map_map_functor",
   (TY_BETA_RULE o MATCH_MP functor_o) (CONJ map_functor map_functor)
  );



(*---------------------------------------------------------------------------
            Natural transformation type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("nattransf", Type `: \'t1 't2. !'a. 'a 't1 -> 'a 't2`);

(*---------------------------------------------------------------------------
            Natural transformation predicate
 ---------------------------------------------------------------------------*)

val _ = set_trace "beta_conv_types" 1;

val nattransf_def = new_definition("nattransf_def", Term
   `nattransf ( phi  : 't1 functor )
              ( psi  : 't2 functor )
              (kappa : ('t1,'t2)nattransf) =
         !:'a 'b. !(f:'a -> 'b) x.
                   psi f (kappa x) = kappa (phi f x)`);

val nattransf_THM = store_thm
  ("nattransf_THM",
  ``nattransf phi psi (kappa : !'a. 'a 't1 -> 'a 't2) =
         !:'a 'b. !(f:'a -> 'b).
                   psi f o kappa = kappa o phi f``,
   REWRITE_TAC[nattransf_def,FUN_EQ_THM,o_THM]
  );

val nattransf_functor_comp1 = store_thm
  ("nattransf_functor_comp1",
   ``nattransf phi1 phi2 (kappa : ('t1,'t2)nattransf) /\
     functor (psi : 't3 functor) ==>
     nattransf (\:'a 'b. phi1 o psi)
               (\:'a 'b. phi2 o psi)
               (\:'a. kappa[:'a 't3:])``,
   REWRITE_TAC[nattransf_def,functor_def]
   THEN REPEAT STRIP_TAC
   THEN TY_BETA_TAC
   THEN ASM_REWRITE_TAC[o_THM]
  );

val nattransf_functor_comp2 = store_thm
  ("nattransf_functor_comp2",
   ``nattransf phi1 phi2 (kappa : ('t1,'t2)nattransf) /\
     functor (psi : 't3 functor) ==>
     nattransf (\:'a 'b. psi o phi1)
               (\:'a 'b. psi o phi2)
               (\:'a. psi kappa)``,
   REWRITE_TAC[nattransf_THM,functor_def]
   THEN REPEAT STRIP_TAC
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[o_THM]
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th])
   THEN ASM_REWRITE_TAC[]
  );

val nattransf_comp1 = store_thm
  ("nattransf_comp1",
   ``nattransf phi1 phi2 (kappa1 : ('t1,'t2)nattransf) /\
     nattransf phi2 phi3 (kappa2 : ('t2,'t3)nattransf) ==>
     nattransf phi1 phi3 (\:'a. kappa2 o kappa1)``,
   REWRITE_TAC[nattransf_THM]
   THEN REPEAT STRIP_TAC
   THEN TY_BETA_TAC
   THEN ASM_REWRITE_TAC[nattransf_THM,o_ASSOC]
   THEN ASM_REWRITE_TAC[GSYM o_ASSOC]
  );

val nattransf_commute1 = store_thm
  ("nattransf_commute1",
   ``nattransf (phi1 : 's1 functor) (psi1 : 't1 functor) kappa1 /\
     nattransf (phi2 : 's2 functor) (psi2 : 't2 functor) kappa2  ==>
     (kappa2 o phi2 (kappa1[:'a:]) = psi2 kappa1 o kappa2)``,
   REWRITE_TAC[nattransf_THM]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
  );

val nattransf_comp2 = store_thm
  ("nattransf_comp2",
   ``nattransf phi1 psi1 (kappa1 : ('r1,'s1) nattransf) /\
     nattransf phi2 psi2 (kappa2 : ('r2,'s2) nattransf) /\
     functor phi2 ==>
     nattransf (\:'a 'b. phi2 o phi1)
               (\:'a 'b. psi2 o psi1)
               ((\:'a. kappa2 o phi2 kappa1))``,
   REWRITE_TAC[nattransf_THM,functor_def]
   THEN REPEAT STRIP_TAC
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[o_THM]
   THEN REWRITE_TAC[o_ASSOC]
   THEN ASM_REWRITE_TAC[]
   THEN REWRITE_TAC[GSYM o_ASSOC]
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th])
   THEN ASM_REWRITE_TAC[]
  );

(* An example of a natural transformation: REVERSE *)

val nattransf_REVERSE = store_thm
  ("nattransf_REVERSE",
   ``nattransf (\:'a 'b. MAP)
               (\:'a 'b. MAP)
               (\:'a. REVERSE)``,
   REWRITE_TAC[nattransf_THM]
   THEN REPEAT STRIP_TAC
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN FULL_SIMP_TAC list_ss []
  );


(*---------------------------------------------------------------------------
            Bifunctor type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("bifunctor",
    ``: \'t. !'a 'b 'c 'd. ('a->'b) -> ('c->'d) -> ('a, 'c) 't -> ('b, 'd) 't``);

(*---------------------------------------------------------------------------
            Functor predicate
 ---------------------------------------------------------------------------*)

val bifunctor_def = new_definition("bifunctor_def", Term
   `bifunctor (phi: 't bifunctor) =
      (* Identity *)
          (!:'a 'b. phi (I:'a->'a) (I:'b->'b) = I) /\
      (* Homomorphism *)
          (!:'a 'b 'c 'd 'e 'f.
             !(f1:'a -> 'b) (g1:'b -> 'c) (f2:'d -> 'e) (g2:'e -> 'f).
                phi (g1 o f1) (g2 o f2) = phi g1 g2 o phi f1 f2)
     `);

val PAIR_I = store_thm
  ("PAIR_I",
   ``((I:'a->'a) ## (I:'b->'b)) = I``,
   REWRITE_TAC[FUN_EQ_THM]
   THEN pairLib.PGEN_TAC ``(x:'a,y:'b)``
   THEN REWRITE_TAC[pairTheory.PAIR_MAP_THM,I_THM]
  );

val PAIR_COMPOSE = store_thm
  ("PAIR_COMPOSE",
   ``!(f1 :'a -> 'b) (g1 :'b -> 'c) (f2 :'d -> 'e) (g2 :'e -> 'f).
        (g1 o f1 ## g2 o f2) = (g1 ## g2) o (f1 ## f2)``,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN pairLib.PGEN_TAC ``(x:'a,y:'d)``
   THEN REWRITE_TAC[pairTheory.PAIR_MAP_THM,o_THM]
  );

val prod_bifunctor = store_thm
  ("prod_bifunctor",
   ``bifunctor ((\:'a 'b 'c 'd. ($## :('a->'b)->('c->'d)->('a#'c -> 'b#'d))) : prod bifunctor)``,
   REWRITE_TAC[bifunctor_def]
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[PAIR_I,PAIR_COMPOSE]
  );

val prod_bifunctor = store_thm
  ("prod_bifunctor",
   ``bifunctor ((\:'a 'b 'c 'd. $##) : prod bifunctor)``,
   REWRITE_TAC[bifunctor_def]
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[PAIR_I,PAIR_COMPOSE]
  );

val SUM_I = store_thm
  ("SUM_I",
   ``((I:'a->'a) ++ (I:'b->'b)) = I``,
   REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN REWRITE_TAC[sumTheory.SUM_MAP_def,I_THM]
  );

val SUM_COMPOSE = store_thm
  ("SUM_COMPOSE",
   ``!(f1 :'a -> 'b) (g1 :'b -> 'c) (f2 :'d -> 'e) (g2 :'e -> 'f).
        (g1 o f1 ++ g2 o f2) = (g1 ++ g2) o (f1 ++ f2)``,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN REWRITE_TAC[sumTheory.SUM_MAP_def,o_THM]
  );

val sum_bifunctor = store_thm
  ("sum_bifunctor",
   ``bifunctor ((\:'a 'b 'c 'd. sum$++ ) : sum bifunctor)``,
   REWRITE_TAC[bifunctor_def]
   THEN TY_BETA_TAC
   THEN REWRITE_TAC[SUM_I,SUM_COMPOSE]
  );

val I_o_I = store_thm
  ("I_o_I",
   ``((I:'a->'a) o I) = I``,
   REWRITE_TAC[FUN_EQ_THM]
   THEN REWRITE_TAC[o_THM,I_THM]
  );

val functor_bifunctor_left = store_thm
  ("functor_bifunctor_left",
   ``bifunctor (phi : 'g bifunctor) ==>
     functor ((\:'c 'd. phi [:'a:] I))``,
   REWRITE_TAC[bifunctor_def,functor_def]
   THEN TY_BETA_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th,I_o_I])
  );

val functor_bifunctor_right = store_thm
  ("functor_bifunctor_right",
   ``bifunctor (phi : 'g bifunctor) ==>
     functor ((\:'c 'd. \f. phi f (I:'a->'a)))``,
   REWRITE_TAC[bifunctor_def,functor_def]
   THEN TY_BETA_TAC
   THEN BETA_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th,I_o_I])
  );



val _ = html_theory "functor1";

val _ = export_theory();

end; (* structure functor1Script *)
