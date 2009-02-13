(*---------------------------------------------------------------------------
                   Functors and Natural Transformations
              Originally written for HOL2P by Norbert Voelker
         Ported to HOL-Omega and expanded by Peter Vincent Homeier
                Version emphasizing simplification tactics
 ---------------------------------------------------------------------------*)

structure functorScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory combinSimps

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;


val _ = new_theory "functor";

val combin_ss = bool_ss ++ COMBIN_ss


(*---------------------------------------------------------------------------
     This file presents a formalization of some of chapter 2 of the book
     "Algebra of Programming" by Richard Bird and Oege de Moor, published
     by Prentice Hall in 1997.

     We will represent category theory as a shallow embedding in the logic
     of HOL-Omega.  Thus, this represents actually only one category,
     where the objects of the category are the types of the logic with
     kind `::ty`, and the arrows of the category are the total functions
     from a source type to a target type.  We do not explicitly model the
     operations that take an arrow and return either the source or target
     objects.  The operation that takes an object A to an arrow id_A is
     modeled by ``I:'A -> 'A``.  The compositon operation on arrows is
     modeled by the normal infix function composition operator ``combin$o``.
     Because of the strong typing of the logic, any composition which is
     well-typed is defined.  Then composition is associative and has
     identity arrows as units, as required.
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
            Monic predicate
 ---------------------------------------------------------------------------*)

val monic_def = new_definition("monic_def", Term
   `monic (m : 'a -> 'b) =
          !:'c. !(f:'c -> 'a) g. (f = g) = (m o f = m o g)
     `);

(* monic is the same as injective (one-to-one) *)

val monic_injective = store_thm
  ("monic_injective",
   ``monic (m : 'a -> 'b) = !x y. (m x = m y) ==> (x = y)``,
   SIMP_TAC bool_ss [monic_def]
   THEN EQ_TAC THEN REPEAT STRIP_TAC
   THENL
     [ FIRST_ASSUM (fn th =>
           MP_TAC (SYM(SPECL[``K x :bool->'a``,``K y :bool->'a``] (TY_SPEC bool th))))
       THEN SIMP_TAC combin_ss [FUN_EQ_THM]
       THEN FIRST_ASSUM (fn th => REWRITE_TAC[th]),

       SIMP_TAC combin_ss [FUN_EQ_THM]
       THEN EQ_TAC THEN REPEAT STRIP_TAC
       THENL
         [ ASM_REWRITE_TAC[],

           FIRST_ASSUM MATCH_MP_TAC
           THEN FIRST_ASSUM MATCH_ACCEPT_TAC
         ]
     ]
  );

(*---------------------------------------------------------------------------
            Epic predicate
 ---------------------------------------------------------------------------*)

val epic_def = new_definition("epic_def", Term
   `epic (e : 'a -> 'b) =
          !:'c. !(f:'b -> 'c) g. (f = g) = (f o e = g o e)
     `);

(* epic is the same as surjective (onto) *)

val epic_surjective = store_thm
  ("epic_surjective",
   ``epic (e : 'a -> 'b) = !y. ?x. e x = y``,
   SIMP_TAC bool_ss [epic_def]
   THEN EQ_TAC THEN REPEAT STRIP_TAC
   THENL
     [ FIRST_ASSUM (fn th =>
           MP_TAC (GSYM(SPECL[``\x:'b. x = y``,``K F :'b -> bool``] (TY_SPEC bool th))))
       THEN SIMP_TAC combin_ss [FUN_EQ_THM],

       SIMP_TAC combin_ss [FUN_EQ_THM]
       THEN EQ_TAC THEN REPEAT STRIP_TAC
       THENL
         [ ASM_REWRITE_TAC[],

           FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``x:'b``)
           THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th])
           THEN ASM_REWRITE_TAC[]
         ]
     ]
  );

(*---------------------------------------------------------------------------
  Functors are homomorphisms between categories.  In this model, functors
  are homomorphisms between the HOL-Omega logic and itself.  A functor
  consists of a type operator F of kind `::ty => ty` and a term operator F
  of type `:!'a 'b. ('a -> 'b) -> 'a F -> 'b F`, so that F f : 'a F -> 'b F
  whenever f : 'a -> 'b.  Functors are also required to preserve identities
  and composition, as defined below.  

  We use the variables F', G, H, etc. to denote functors.
  F' is used instead of F because F is already defined as the constant false.
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
            Functor type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("functor", Type `: \'F. !'a 'b. ('a -> 'b) -> 'a 'F -> 'b 'F`);

(*---------------------------------------------------------------------------
            Functor predicate
 ---------------------------------------------------------------------------*)

val functor_def = new_definition("functor_def", Term
   `functor (F': 'F functor) =
      (* Identity *)
          (!:'a. F' (I:'a->'a) = I) /\
      (* Composition *)
          (!:'a 'b 'c. !(f:'a -> 'b) (g:'b -> 'c).
                 F' (g o f) = F' g o F' f)
     `);

(*---------------------------------------------------------------------------
            Examples of functors
 ---------------------------------------------------------------------------*)

val identity_functor = store_thm
  ("identity_functor",
   ``functor ((\:'a 'b. I) : I functor)``,
   SIMP_TAC combin_ss [functor_def]
  );

val constant_functor = store_thm
  ("constant_functor",
   ``!:'a. functor ((\:'b 'c. \f. I) : ('a K) functor)``,
   SIMP_TAC combin_ss [functor_def]
  );

val PAIR_I = quotient_pairTheory.PAIR_MAP_I;

val PAIR_o = store_thm
  ("PAIR_o",
   ``!(f1 :'a -> 'b) (g1 :'b -> 'c) (f2 :'d -> 'e) (g2 :'e -> 'f).
        (g1 o f1 ## g2 o f2) = (g1 ## g2) o (f1 ## f2)``,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN REWRITE_TAC[pairTheory.PAIR_MAP_THM,o_THM]
  );

val square_functor = store_thm
  ("square_functor",
   ``functor ((\:'b 'c. \f. f ## f) : (\'a. 'a # 'a) functor)``,
   SIMP_TAC bool_ss [functor_def,PAIR_I,PAIR_o]
  );

val MAP_I = quotient_listTheory.LIST_MAP_I;
val MAP_o = rich_listTheory.MAP_o;

val map_functor = store_thm
  ("map_functor",
   ``functor ((\:'a 'b. MAP) : list functor)``,
   SIMP_TAC bool_ss [functor_def,MAP_I,MAP_o]
  );

val I_EQ = store_thm
  ("I_EQ",
   ``I = \x:'a. x``,
   SIMP_TAC combin_ss [FUN_EQ_THM]
  );

val IMAGE_I = store_thm
  ("IMAGE_I",
   ``IMAGE (I:'a -> 'a) = I``,
   SIMP_TAC combin_ss [FUN_EQ_THM,I_EQ,pred_setTheory.IMAGE_ID]
  );

val IMAGE_o = store_thm
  ("IMAGE_o",
   ``!(f :'a -> 'b) (g :'b -> 'c).
        IMAGE (g o f) = IMAGE g o IMAGE f``,
   SIMP_TAC combin_ss [FUN_EQ_THM,pred_setTheory.IMAGE_COMPOSE]
  );

val powerset_functor = store_thm
  ("powerset_functor",
   ``functor ((\:'a 'b. IMAGE) : (\'a. 'a -> bool) functor)``,
   SIMP_TAC bool_ss [functor_def,IMAGE_I,IMAGE_o]
  );

val powerset'_functor = store_thm
  ("powerset'_functor",
   ``functor ((\:'a 'b. \f s. { b | !a. (f a = b) ==> a IN s})
              : (\'a. 'a -> bool) functor)``,
   SIMP_TAC combin_ss [functor_def]
   THEN ONCE_REWRITE_TAC[FUN_EQ_THM]
   THEN SIMP_TAC (combin_ss ++ pred_setSimps.SET_SPEC_ss) [pred_setTheory.EXTENSION]
   THEN REPEAT STRIP_TAC
   THEN METIS_TAC[]
  );

val map_map_functor0 = store_thm
  ("map_map_functor0",
   ``functor (\:'a 'b. MAP o MAP)``,
   SIMP_TAC combin_ss [functor_def,MAP_I,MAP_o]
  );

(*---------------------------------------------------------------------------
            Functor theorems
 ---------------------------------------------------------------------------*)

val oo_def = Define `$oo (G: 'G functor) (F': 'F functor) = \:'a 'b. G o F' [:'a,'b:]`;
val _ = add_infix("oo", 800, HOLgrammars.RIGHT);
val _ = overload_on ("o", Term`$oo : 'G functor -> 'F functor -> ('F o 'G) functor`);
(*
val _ = set_trace "overload" 1;
*)

val functor_o = store_thm
  ("functor_o",
   ``!(F': 'F functor) (G: 'G functor).
      functor F' /\ functor G ==>
      functor (\:'a 'b. G o F')``,
   SIMP_TAC combin_ss [functor_def]
  );

val functor_oo = store_thm
  ("functor_oo",
   ``!(F': 'F functor) (G: 'G functor).
      functor F' /\ functor G ==>
      functor (G o F')``,
   SIMP_TAC combin_ss [functor_def,oo_def]
  );

(* As a simple application, we can immediately derive that MAP o MAP is a functor. *)

val map_o_map_functor = save_thm
  ("map_o_map_functor",
   (TY_BETA_RULE o MATCH_MP functor_o) (CONJ map_functor map_functor)
  );

val map_oo_map_functor = save_thm
  ("map_oo_map_functor",
   (TY_BETA_RULE o MATCH_MP functor_oo) (CONJ map_functor map_functor)
  );



(*---------------------------------------------------------------------------
            Bifunctor type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("bifunctor",
    ``: \'F. !'a 'b 'c 'd. ('a->'b) -> ('c->'d) -> ('a, 'c) 'F -> ('b, 'd) 'F``);

(*---------------------------------------------------------------------------
            Bifunctor predicate
 ---------------------------------------------------------------------------*)

val bifunctor_def = new_definition("bifunctor_def", Term
   `bifunctor (F': 'F bifunctor) =
      (* Identity *)
          (!:'a 'b. F' (I:'a->'a) (I:'b->'b) = I) /\
      (* Composition *)
          (!:'a 'b 'c 'd 'e 'f.
             !(f1:'a -> 'b) (g1:'b -> 'c) (f2:'d -> 'e) (g2:'e -> 'f).
                F' (g1 o f1) (g2 o f2) = F' g1 g2 o F' f1 f2)
     `);

(*---------------------------------------------------------------------------
            Examples of bifunctors
 ---------------------------------------------------------------------------*)

val prod_bifunctor = store_thm
  ("prod_bifunctor",
   ``bifunctor ((\:'a 'b 'c 'd. $##) : prod bifunctor)``,
   SIMP_TAC bool_ss [bifunctor_def,PAIR_I,PAIR_o]
  );

val SUM_I = sumTheory.SUM_MAP_I;

val SUM_o = store_thm
  ("SUM_o",
   ``!(f1 :'a -> 'b) (g1 :'b -> 'c) (f2 :'d -> 'e) (g2 :'e -> 'f).
        (g1 o f1 ++ g2 o f2) = (g1 ++ g2) o (f1 ++ f2)``,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN REWRITE_TAC[sumTheory.SUM_MAP_def,o_THM]
  );

val sum_bifunctor = store_thm
  ("sum_bifunctor",
   ``bifunctor ((\:'a 'b 'c 'd. $++) : sum bifunctor)``,
   SIMP_TAC bool_ss [bifunctor_def,SUM_I,SUM_o]
  );

val MAP_REL_def = Define
   `MAP_REL (f:'a -> 'b) (g:'c -> 'd) R =
      \x y. ?u v. (f u = x) /\ (g v = y) /\ R u v`;

val MAP_REL_bifunctor = store_thm
  ("MAP_REL_bifunctor",
   ``bifunctor (\:'a 'b 'c 'd. MAP_REL)``,
   SIMP_TAC combin_ss [bifunctor_def,FUN_EQ_THM,MAP_REL_def]
   THEN REPEAT STRIP_TAC
   THEN METIS_TAC[]
  );


(*---------------------------------------------------------------------------
            Bifunctor theorems
 ---------------------------------------------------------------------------*)

val functor_bifunctor_left = store_thm
  ("functor_bifunctor_left",
   ``bifunctor (F' : 'F bifunctor) ==>
     functor ((\:'c 'd. F' [:'a:] I))``,
   REWRITE_TAC[bifunctor_def,functor_def]
   THEN REPEAT STRIP_TAC
   THEN ASM_SIMP_TAC bool_ss []
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th,I_o_ID])
  );

val functor_bifunctor_right = store_thm
  ("functor_bifunctor_right",
   ``bifunctor (F' : 'F bifunctor) ==>
     functor ((\:'c 'd. \f. F' f (I:'a->'a)))``,
   REWRITE_TAC[bifunctor_def,functor_def]
   THEN REPEAT STRIP_TAC
   THEN ASM_SIMP_TAC bool_ss []
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th,I_o_ID])
  );



(*---------------------------------------------------------------------------
            Natural transformation type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("nattransf", Type `: \'F 'G. !'a. 'a 'F -> 'a 'G`);

(*---------------------------------------------------------------------------
            Natural transformation predicate
 ---------------------------------------------------------------------------*)

val nattransf_def = new_definition("nattransf_def", Term
   `nattransf (phi : ('F,'G) nattransf)
              ( F' : 'F functor )
              ( G  : 'G functor ) =
         !:'a 'b. !(h:'a -> 'b).
                G h o phi = phi o F' h`);

(*---------------------------------------------------------------------------
            Natural transformation theorems
 ---------------------------------------------------------------------------*)

(* The identity natural transformation, transforms any functor to itself *)

val identity_nattransf = store_thm
  ("identity_nattransf",
   ``!:'F. !F' : 'F functor.
        nattransf (\:'a. I) F' F'``,
   SIMP_TAC combin_ss [nattransf_def]
  );

(* Vertical composition of two natural transformations *)

val ooo_def = Define `$ooo (phi2: ('G,'H)nattransf) (phi1: ('F,'G)nattransf) = \:'a. phi2 o (phi1[:'a:])`;
val _ = add_infix("ooo", 800, HOLgrammars.RIGHT);
val _ = overload_on ("o", Term`$ooo : ('G,'H)nattransf -> ('F,'G)nattransf -> ('F,'H)nattransf`);


val nattransf_comp = store_thm
  ("nattransf_comp",
   ``nattransf (     phi1     : ('F,'G)nattransf) F' G /\
     nattransf (     phi2     : ('G,'H)nattransf) G  H ==>
     nattransf ((phi2 o phi1) : ('F,'H)nattransf) F' H``,
   SIMP_TAC bool_ss [nattransf_def,ooo_def]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[o_ASSOC]
   THEN ASM_REWRITE_TAC[GSYM o_ASSOC]
  );

(* Composition of a functor (on the left) with a natural transformation *)

val foo_def = Define `$foo (H: 'H functor) (phi: ('F,'G)nattransf) = \:'a. H [:'a 'F, 'a 'G:] phi`;
val _ = add_infix("foo", 750, HOLgrammars.LEFT);
val _ = overload_on ("o", Term`$foo : 'H functor -> ('F,'G) nattransf -> ('F o 'H,'G o 'H) nattransf`);


val functor_nattransf_comp = store_thm
  ("functor_nattransf_comp",
   ``nattransf (phi : ('F,'G)nattransf) F' G  /\
     functor (H : 'H functor) ==>
     nattransf (H o phi)      (* H foo phi *)
               (H o F')       (* H oo F'   *)
               (H o G)``,     (* H oo G    *)
   SIMP_TAC combin_ss [nattransf_def,functor_def,oo_def,foo_def]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM th])
   THEN ASM_REWRITE_TAC[]
  );

(* Composition of a natural transformation with a functor (on the right) *)

val oof_def = Define `$oof (phi: ('F,'G) nattransf) (H': 'H functor) = \:'a. phi [:'a 'H:]`;
val _ = add_infix("oof", 750, HOLgrammars.LEFT);
val _ = overload_on ("o", Term`$oof : ('F,'G) nattransf -> 'H functor -> ('H o 'F,'H o 'G) nattransf`);


val nattransf_functor_comp = store_thm
  ("nattransf_functor_comp",
   ``nattransf (phi : ('F,'G)nattransf) F' G /\
     functor (H : 'H functor) ==>
     nattransf (phi o H)     (* phi oof H *)
               ( F' o H)     (*  F' oo  H *)
               ( G  o H)``,  (*  G  oo  H *)
   SIMP_TAC combin_ss [nattransf_def,functor_def,oo_def,oof_def]
  );

val nattransf_commute = store_thm
  ("nattransf_commute",
   ``nattransf (phi1 : ('F1,'G1) nattransf) F1 G1 /\
     nattransf (phi2 : ('F2,'G2) nattransf) F2 G2  ==>
     (phi2 o F2 (phi1[:'a:]) = G2 phi1 o phi2)``,
   SIMP_TAC bool_ss [nattransf_def]
  );

(* Horizontal composition of two natural transformations *)

val nattransf_comp2 = store_thm
  ("nattransf_comp2",
   ``nattransf (phi1 : ('F1,'G1) nattransf) F1 G1 /\
     nattransf (phi2 : ('F2,'G2) nattransf) F2 G2 /\
     functor F2 ==>
     nattransf (\:'a. phi2 o F2 (phi1[:'a:]))
               (F2 oo F1)
               (G2 oo G1)``,
   SIMP_TAC bool_ss [nattransf_def,functor_def,oo_def]
   THEN REPEAT STRIP_TAC
   THEN ASM_SIMP_TAC bool_ss [o_THM,o_ASSOC]
   THEN POP_ASSUM (fn th => REWRITE_TAC[GSYM o_ASSOC,GSYM th])
   THEN ASM_REWRITE_TAC[]
  );

(*---------------------------------------------------------------------------
            Examples of natural transformations
 ---------------------------------------------------------------------------*)

(* REVERSE reverses the order of elements in a list. *)

val nattransf_REVERSE = store_thm
  ("nattransf_REVERSE",
   ``nattransf (\:'a. REVERSE)
               (\:'a 'b. MAP)
               (\:'a 'b. MAP)``,
   SIMP_TAC bool_ss [nattransf_def]
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN FULL_SIMP_TAC list_ss []
  );

(* INITS takes a list l and returns a list of all prefixes of l. *)

val INITS_def = Define
  `(INITS [] = [[]]) /\
   (INITS ((x:'a)::xs) = [] :: MAP (CONS x) (INITS xs))`;

val MAP_o_CONS = store_thm
  ("MAP_o_CONS",
   ``!(f:'a -> 'b) x. MAP f o CONS x = CONS (f x) o MAP f``,
   REPEAT GEN_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN ASM_SIMP_TAC list_ss []
  );

val MAP_INITS = store_thm
  ("MAP_INITS",
   ``!l f:'a -> 'b. (MAP o MAP) f (INITS l) = INITS (MAP f l)``,
   Induct
   THEN FULL_SIMP_TAC list_ss [INITS_def,rich_listTheory.MAP_MAP_o,MAP_o_CONS]
   THEN ASM_REWRITE_TAC [GSYM rich_listTheory.MAP_MAP_o]
  );

val nattransf_INITS = store_thm
  ("nattransf_INITS",
   ``nattransf (\:'a. INITS)
               (\:'a 'b. MAP)
               (\:'a 'b. MAP o MAP)``,
   SIMP_TAC bool_ss [nattransf_def]
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN FULL_SIMP_TAC list_ss [MAP_INITS]
  );

val FORK_def = Define
  `FORK (a:'a) = (a,a)`;

val nattransf_FORK = store_thm
  ("nattransf_FORK",
   ``nattransf ((\:'a. FORK) : (I, \'a. 'a # 'a)nattransf)
               (\:'a 'b. I)
               (\:'a 'b. \f (a,b). (f a,f b))``,
   SIMP_TAC list_ss [nattransf_def,FORK_def,FUN_EQ_THM]
  );


(*---------------------------------------------------------------------------
            Natural transformation on bifunctors type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("binattransf", Type `: \'F 'G. !'a 'b. ('a,'b) 'F -> ('a,'b) 'G`);

(*---------------------------------------------------------------------------
            Natural transformation on bifunctors predicate
 ---------------------------------------------------------------------------*)

val binattransf_def = new_definition("binattransf_def",
  ``binattransf (phi : ('F,'G) binattransf)
                ( F' : 'F bifunctor )
                ( G  : 'G bifunctor ) =
         !:'a 'b 'c 'd. !(h:'a -> 'b) (i:'c -> 'd).
                G h i o phi = phi o F' h i``);

(*---------------------------------------------------------------------------
            Examples of natural transformations on bifunctors
 ---------------------------------------------------------------------------*)

val SWAP_def = Define
  `SWAP (a:'a,b:'b) = (b,a)`;

val binattransf_SWAP = store_thm
  ("binattransf_SWAP",
   ``binattransf (\:'a 'b. SWAP)
                 (\:'a 'b 'c 'd. $##)
                 (\:'a 'b 'c 'd. \f g. g ## f)``,
   SIMP_TAC bool_ss [binattransf_def]
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN SIMP_TAC std_ss [SWAP_def]
  );

(* E denotes the existential image bifunctor which maps a type 'a to 'a set,
   and a relation R to its existential image function:
           (E R) s = { a | ?b. R a b /\ b IN s }
*)

val binattransf_E = store_thm
  ("binattransf_E",
   ``binattransf (\:'a 'b. SWAP)
                 (\:'a 'b 'c 'd. $##)
                 (\:'a 'b 'c 'd. \f g. g ## f)``,
   SIMP_TAC bool_ss [binattransf_def]
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN SIMP_TAC std_ss [SWAP_def]
  );



val _ = html_theory "functor";

val _ = export_theory();

end; (* structure functorScript *)
