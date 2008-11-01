(*---------------------------------------------------------------------------
            Algebra of Programming (AoP) Examples in HOL-Omega
   Homomorphisms, initial algebras, catamorphisms, and banana split theorem
              Originally written for HOL2P by Norbert Voelker
         Ported to HOL-Omega and expanded by Peter Vincent Homeier
 ---------------------------------------------------------------------------*)

structure aopScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory functorTheory;

val combin_ss = bool_ss ++ combinSimps.COMBIN_ss

val _ = set_trace "Unicode" 1;


val _ = new_theory "aop";

(*---------------------------------------------------------------------------
     This file presents a formalization of some of chapter 2 of the book
     "Algebra of Programming" by Richard Bird and Oege de Moor, published
     by Prentice Hall in 1997.

     Some of the comments below are adaptations of sentences from this book.
 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
            Algebra type abbreviation
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("algebra", Type `: \'F 'a. 'a 'F -> 'a`);


(*---------------------------------------------------------------------------
  An F-homomorphism from an algegra f :'a 'F -> 'a to an algegra g :'b 'F -> 'b
  is a mapping h :'a -> 'b such that h o f = g o F h.
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
            Homomorphism predicate
 ---------------------------------------------------------------------------*)

val homo_def = new_definition("homo_def", Term
   `homo (F': 'F functor) f g (h:'a -> 'b) = (h o f = g o F' h)`);

val identity_homo = store_thm
  ("identity_homo",
   ``!(F':'F functor) f.
       functor F' ==>
       homo F' f f (I:'a -> 'a)``,
   SIMP_TAC combin_ss [homo_def,functor_def]
  );

val homo_comp = store_thm
  ("homo_comp",
   ``!(F':'F functor) f1 f3 (h1:'a -> 'b) (h2:'b -> 'c).
       (?f2. homo F' f1 f2 h1 /\ homo F' f2 f3 h2) /\
       functor F' ==>
       homo F' f1 f3 (h2 o h1)``,
   RW_TAC bool_ss [homo_def,functor_def]
   THEN ASM_REWRITE_TAC[GSYM o_ASSOC]
   THEN ASM_REWRITE_TAC[o_ASSOC]
  );


(*---------------------------------------------------------------------------
  Because there is an identity homomorphism, and the composition of two
  homomorphisms is a homomorphism, F-algebras form the objects of a category
  called Alg(F) whose arrows are homomorphisms.  For many functors, this
  category has an initial object, which we will call alpha : 't 'F -> 't.

  The existence of an initial F-algebra means that for any other F-algebra
  f : 'a 'F -> 'a, there is a unique homomorphism from alpha to f.
  We call this homomorphism the catamorphism of f, of type 't -> 'a.
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
            Catamorphism function
 ---------------------------------------------------------------------------*)

val cata_def = new_definition("cata_def", Term
   `cata (  F'  : 'F functor)
         (alpha : ('F,'t)algebra) (* initial object of the category of algebras *)
         (  f   : ('F,'a)algebra) =
         @h. homo F' alpha f h`);

(*---------------------------------------------------------------------------
            Initial algebra predicate
 ---------------------------------------------------------------------------*)

val ialg_def = new_definition("ialg_def", Term
   `ialg (  F'  : 'F functor)
         (alpha : ('F,'t)algebra) =
      !:'a. !(f : ('F,'a)algebra). ?!h. homo F' alpha f h`);

val identity_cata = store_thm
  ("identity_cata",
  ``functor (F' : 'F functor) /\ ialg F' (alpha : ('F,'t)algebra) ==>
    (cata F' alpha alpha = I)``,
   RW_TAC bool_ss [functor_def,cata_def,ialg_def,EXISTS_UNIQUE_THM]
   THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC ``alpha: ('F,'t)algebra`` o TY_SPEC ``:'t``)
   THEN SELECT_ELIM_TAC
   THEN CONJ_TAC
   THENL [ PROVE_TAC[],

           RW_TAC combin_ss [homo_def]
         ]
  );

val homo_cata = store_thm
  ("homo_cata",
  ``ialg (F' : 'F functor) (alpha : ('F,'t)algebra) ==>
    !:'a. !f: ('F,'a)algebra. homo F' alpha (f: ('F,'a)algebra) (cata F' alpha f)``,
   RW_TAC bool_ss [homo_def,cata_def,ialg_def,EXISTS_UNIQUE_THM]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL o TY_SPEC_ALL)
   THEN SELECT_ELIM_TAC
   THEN PROVE_TAC[]
  );

val cata_property = store_thm
  ("cata_property",
  ``ialg (F' : 'F functor) (alpha : ('F,'t)algebra) ==>
    !:'a. !(f : ('F,'a)algebra) h. ((h = cata F' alpha f) = (h o alpha = f o F' h))``,
   REPEAT STRIP_TAC
   THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL o TY_SPEC_ALL
                      o REWRITE_RULE[ialg_def,EXISTS_UNIQUE_THM])
   THEN REWRITE_TAC [GSYM homo_def]
   THEN EQ_TAC
   THEN RW_TAC bool_ss [homo_cata]
  );

val eq_cata = store_thm
  ("eq_cata",
  ``ialg (F' : 'F functor) (alpha : ('F,'t)algebra) /\
    homo F' alpha (f: ('F,'a)algebra) h ==>
    (cata F' alpha f = h)``,
   RW_TAC bool_ss [homo_def,cata_def,ialg_def,EXISTS_UNIQUE_THM]
   THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL o TY_SPEC ``:'a``)
   THEN SELECT_ELIM_TAC
   THEN CONJ_TAC
   THENL [ EXISTS_TAC ``h': 't -> 'a``
           THEN FIRST_ASSUM ACCEPT_TAC,

           ASM_SIMP_TAC bool_ss []
         ]
  );

val cata_fusion = store_thm
  ("cata_fusion",
  ``ialg (F' : 'F functor) (alpha : ('F,'t)algebra) /\
    homo F' f g (h: 't -> 'a) /\ functor F' ==>
    (h o cata F' alpha f = cata F' alpha g)``,
   STRIP_TAC
   THEN CONV_TAC SYM_CONV
   THEN MATCH_MP_TAC eq_cata
   THEN ASM_REWRITE_TAC[]
   THEN MATCH_MP_TAC homo_comp
   THEN ASM_REWRITE_TAC[]
   THEN EXISTS_TAC ``f: ('F,'t)algebra``
   THEN ASM_SIMP_TAC bool_ss [homo_cata]
  );


(*---------------------------------------------------------------------------
            Natural numbers as an initial algebra
 ---------------------------------------------------------------------------*)

(* Injection of constructors *)

val alpha_num_def = new_definition("alpha_num_def", Term
   `alpha_num = sum_case (K 0 :'a -> num) SUC`);

(* The functor for which `:num F -> num` is an initial algebra:
   F 'a = one + 'a  and   F h = I ++ h                          *)

val ifun_num_def = new_definition("ifun_num_def", Term
   `ifun_num = \:'a 'b. \f. (I: one -> one) ++ (f: 'a -> 'b)`);

val SUM_I = sumTheory.SUM_MAP_I;

val functor_ifun_num = store_thm
  ("functor_ifun_num",
  ``functor ifun_num``,
   SIMP_TAC bool_ss [functor_def,ifun_num_def,SUM_I,GSYM SUM_o,I_o_ID]
  );

val num_rec_def = Define
   `(num_rec v f 0 = (v:'a)) /\
    (num_rec v f (SUC n) = f (num_rec v f n))`;

val num_rec_cata_lemma = store_thm
  ("num_rec_cata_lemma",
  ``((h: num -> 'a) o alpha_num = f o ifun_num h)
    = (h = num_rec (f(INL ())) (f o INR))``,
   SIMP_TAC std_ss [alpha_num_def,ifun_num_def,o_DEF,FUN_EQ_THM,sumTheory.FORALL_SUM]
   THEN EQ_TAC THEN STRIP_TAC
   THEN Induct
   THEN ASM_SIMP_TAC std_ss [num_rec_def]
   THEN Cases
   THEN REFL_TAC
  );

val ialg_alpha_num = store_thm
  ("ialg_alpha_num",
  ``ialg ifun_num alpha_num``,
   SIMP_TAC bool_ss [ialg_def,homo_def,num_rec_cata_lemma]
  );

val ifun_num_decompose = store_thm
  ("ifun_num_decompose",
  ``!h: 'a (\'a. one + 'a) -> 'a.
      ?(c:one -> 'a) (f:'a -> 'a). h = sum_case c f``,
   STRIP_TAC
   THEN EXISTS_TAC ``(h: one + 'a -> 'a) o INL``
   THEN EXISTS_TAC ``(h: one + 'a -> 'a) o INR``
   THEN REWRITE_TAC[FUN_EQ_THM]
   THEN Cases
   THEN SIMP_TAC std_ss []
  );

val cata_num_rec = store_thm
  ("cata_num_rec",
  ``cata ifun_num alpha_num (f:one + 'a -> 'a) = num_rec (f(INL ())) (f o INR)``,
   SIMP_TAC bool_ss [eq_cata, ialg_alpha_num, num_rec_cata_lemma, homo_def]
  );

val sum_case_o_INL = store_thm
  ("sum_case_o_INL",
  ``!(f:'a -> 'c) (g:'b -> 'c). sum_case f g o INL = f``,
   SIMP_TAC std_ss [FUN_EQ_THM, o_THM]
  );

val sum_case_o_INR = store_thm
  ("sum_case_o_INR",
  ``!(f:'a -> 'c) (g:'b -> 'c). sum_case f g o INR = g``,
   SIMP_TAC std_ss [FUN_EQ_THM, o_THM]
  );

val num_rec_cata = store_thm
  ("num_rec_cata",
  ``num_rec (e:'a) f = cata ifun_num alpha_num (sum_case (K e) f)``,
   SIMP_TAC std_ss [cata_num_rec, sum_case_o_INR]
  );


(*---------------------------------------------------------------------------
            Lists as an initial algebra
 ---------------------------------------------------------------------------*)

(* Injection of constructors *)

val alpha_list_def = new_definition("alpha_list_def", Term
   `alpha_list = sum_case (K [] :one -> 'a list) (UNCURRY CONS)`);

(* The functor for which `:list` is an initial algebra *)

val _ = type_abbrev ("ifun_functor", Type `: \'a. (\'b. one + 'a # 'b)functor`);

val ifun_list_def = new_definition("ifun_list_def", Term
   `ifun_list = \:'b 'c. \f: 'b -> 'c. (I :one -> one) ++ ((I :'a -> 'a) ## f)`);

val PAIR_I = quotient_pairTheory.PAIR_MAP_I;

val functor_ifun_list = store_thm
  ("functor_ifun_list",
  ``functor (ifun_list :'a ifun_functor)``,
   SIMP_TAC bool_ss [functor_def,ifun_list_def,PAIR_I,SUM_I,GSYM PAIR_o,GSYM SUM_o,I_o_ID]
  );

val foldr_cata_lemma = store_thm
  ("foldr_cata_lemma",
  ``((h :'a list -> 'b) o alpha_list = f o ifun_list h)
    = (h = FOLDR (CURRY(f o INR)) (f(INL ())))``,
   SIMP_TAC std_ss [alpha_list_def,ifun_list_def,o_DEF,FUN_EQ_THM,
                    pairTheory.FORALL_PROD,sumTheory.FORALL_SUM]
   THEN EQ_TAC THEN STRIP_TAC
   THEN Induct
   THEN ASM_SIMP_TAC std_ss [listTheory.FOLDR]
   THEN Cases
   THEN REFL_TAC
  );

val ialg_alpha_list = store_thm
  ("ialg_alpha_list",
  ``ialg (ifun_list :'a ifun_functor) alpha_list``,
   SIMP_TAC bool_ss [ialg_def,homo_def,foldr_cata_lemma]
  );

val cata_foldr = store_thm
  ("cata_foldr",
  ``cata (ifun_list :'a ifun_functor) alpha_list (f:one + 'a # 'b -> 'b)
      = FOLDR (CURRY(f o INR)) (f(INL ()))``,
   SIMP_TAC bool_ss [eq_cata, ialg_alpha_list, foldr_cata_lemma, homo_def]
  );

val foldr_cata = store_thm
  ("foldr_cata",
  ``FOLDR f (e:'b) = cata (ifun_list :'a ifun_functor)
                          alpha_list (sum_case (K e) (UNCURRY f))``,
   SIMP_TAC std_ss [cata_foldr, sum_case_o_INR]
  );


(*---------------------------------------------------------------------------
            Banana split theorem
 ---------------------------------------------------------------------------*)

val SPLIT_def = Define `SPLIT (f:'a -> 'b) (g:'a -> 'c) = \p. (f p, g p)`;

val SPLIT_compose_left = store_thm
  ("SPLIT_compose_left",
  ``((h :'b -> 'd) ## (i :'c -> 'd)) o (SPLIT f g : 'a -> 'b # 'c) = SPLIT (h o f) (i o g)``,
   SIMP_TAC std_ss [FUN_EQ_THM,o_THM,SPLIT_def]
  );

val SPLIT_compose_right = store_thm
  ("SPLIT_compose_right",
  ``(SPLIT f g o (h:'a -> 'b)) : 'a -> 'c # 'd = SPLIT (f o h) (g o h)``,
   SIMP_TAC std_ss [FUN_EQ_THM,o_THM,SPLIT_def]
  );

val FST_SPLIT = store_thm
  ("FST_SPLIT",
  ``FST o (SPLIT f g : 'a -> 'b # 'c) = f``,
   SIMP_TAC std_ss [FUN_EQ_THM,o_THM,SPLIT_def]
  );

val SND_SPLIT = store_thm
  ("SND_SPLIT",
  ``SND o (SPLIT f g : 'a -> 'b # 'c) = g``,
   SIMP_TAC std_ss [FUN_EQ_THM,o_THM,SPLIT_def]
  );

val banana_split = store_thm
  ("banana_split",
  ``ialg phi (alpha : ('t,'a) algebra) /\ functor phi ==>
    (SPLIT (cata phi alpha (f : ('t,'b) algebra))
           (cata phi alpha (g : ('t,'c) algebra))
       = cata phi alpha (SPLIT (f o phi FST) (g o phi SND)))``,
   SIMP_TAC std_ss [functor_def]
   THEN STRIP_TAC
   THEN MATCH_MP_TAC (GSYM eq_cata)
   THEN ASM_SIMP_TAC std_ss [homo_def, SPLIT_compose_right, GSYM o_ASSOC]
   THEN FIRST_ASSUM (fn th => REWRITE_TAC[GSYM th])
   THEN REWRITE_TAC[FST_SPLIT,SND_SPLIT]
   THEN ASM_SIMP_TAC bool_ss [REWRITE_RULE[homo_def] homo_cata]
  );


(*---------------------------------------------------------------------------
            Banana split instance for natural numbers
 ---------------------------------------------------------------------------*)

val SPLIT_num_rec = store_thm
  ("SPLIT_num_rec",
  ``SPLIT (num_rec (e1:'b1) f1) (num_rec (e2:'b2) f2)
      = num_rec (e1,e2) (f1 ## f2)``,
   SIMP_TAC bool_ss [num_rec_cata, ialg_alpha_num, functor_ifun_num, banana_split]
   THEN AP_TERM_TAC
   THEN SIMP_TAC std_ss [FUN_EQ_THM,sumTheory.FORALL_SUM,
                         pairTheory.FORALL_PROD,SPLIT_def,ifun_num_def]
  );


(*---------------------------------------------------------------------------
            Banana split instance for lists
 ---------------------------------------------------------------------------*)

val SPLIT_FOLDR = store_thm
  ("SPLIT_FOLDR",
  ``SPLIT (FOLDR f1 e1) (FOLDR f2 e2)
      = FOLDR (\(a:'a) (b:'b, c:'c). (f1 a b, f2 a c)) (e1,e2)``,
   SIMP_TAC bool_ss [foldr_cata, ialg_alpha_list, functor_ifun_list, banana_split]
   THEN AP_TERM_TAC
   THEN SIMP_TAC std_ss [FUN_EQ_THM,sumTheory.FORALL_SUM,
                         pairTheory.FORALL_PROD,SPLIT_def,ifun_list_def]
  );


(*---------------------------------------------------------------------------
            Banana split application example

 Calculate length and sum of a list in a catamorphism by a single transversal.
 Could be used for an efficient calculation of list average.
 ---------------------------------------------------------------------------*)

(* Express SUM via FOLDR *)

val SUM_FOLDR = store_thm
  ("SUM_FOLDR",
  ``SUM = FOLDR (\a b. a + b) 0``,
   REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN ASM_SIMP_TAC list_ss []
  );

(* Express LENGTH via FOLDR *)

val LENGTH_FOLDR = store_thm
  ("LENGTH_FOLDR",
  ``LENGTH = FOLDR (\(a:'a) b. SUC b) 0``,
   REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN ASM_SIMP_TAC list_ss []
  );

val SPLIT_LENGTH_SUM = store_thm
  ("SPLIT_LENGTH_SUM",
  ``SPLIT LENGTH SUM = FOLDR (\a (b,c). (SUC b, a + c)) (0,0)``,
   SIMP_TAC bool_ss [LENGTH_FOLDR, SUM_FOLDR, SPLIT_FOLDR]
  );



val _ = html_theory "aop";

val _ = export_theory();

end; (* structure aopScript *)
