(*---------------------------------------------------------------------------
            Algebra of Programming (AoP) Examples in HOL-Omega
              Homomorphisms, initial algebras, catamorphisms
                       (Peter Vincent Homeier)
 ---------------------------------------------------------------------------*)

structure aopScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory functorTheory;

val _ = set_trace "Unicode" 1;
val _ = set_trace "beta_conv_types" 1;


val _ = new_theory "aop";


(*---------------------------------------------------------------------------
            Homomorphism predicate
 ---------------------------------------------------------------------------*)

val homo_def = new_definition("homo_def", Term
   `homo (phi: 't functor) f g (h:'a -> 'b) = (h o f = g o phi h)`);

val homo_comp_0 = store_thm
  ("homo_comp_0",
   ``!(phi:'t functor) f1 f3 (h1:'a -> 'b) (h2:'b -> 'c).
       (?f2. homo phi f1 f2 h1 /\ homo phi f2 f3 h2) /\
       (phi (h2 o h1) = phi h2 o phi h1) ==>
       homo phi f1 f3 (h2 o h1)``,
   REWRITE_TAC [homo_def]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[GSYM o_ASSOC]
   THEN ASM_REWRITE_TAC[o_ASSOC]
  );

val homo_comp = store_thm
  ("homo_comp",
   ``!(phi:'t functor) f1 f3 (h1:'a -> 'b) (h2:'b -> 'c).
       (?f2. homo phi f1 f2 h1 /\ homo phi f2 f3 h2) /\
       functor phi ==>
       homo phi f1 f3 (h2 o h1)``,
   REWRITE_TAC [homo_def,functor_def]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[GSYM o_ASSOC]
   THEN ASM_REWRITE_TAC[o_ASSOC]
  );


(*---------------------------------------------------------------------------
            Catamorphism predicate
 ---------------------------------------------------------------------------*)

val cata_def = new_definition("cata_def", Term
   `cata ( phi  : 't functor  )
         (alpha : 'a 't -> 'a )
         (beta  : 'b 't -> 'b ) =
         @h. homo phi alpha beta h`);

val ialg_def = new_definition("ialg_def", Term
   `ialg ( phi  : 't functor)
         (alpha : 'a 'l 't -> 'a 'l) =
         !:'b. !(f:'b 't -> 'b). ?!h. homo phi alpha f h`);

val homo_cata = store_thm
  ("homo_cata",
  ``ialg (phi : 't functor) (alpha : 'a 'l 't -> 'a 'l) ==>
    homo phi alpha (beta: 'b 't -> 'b) (cata phi alpha beta)``,
   REWRITE_TAC[homo_def,cata_def,ialg_def]
   THEN CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   THEN DISCH_THEN (STRIP_ASSUME_TAC o SPEC ``beta: 'b 't -> 'b`` o TY_SPEC_ALL)
   THEN SELECT_ELIM_TAC
   THEN CONJ_TAC
   THENL [ EXISTS_TAC ``h: 'a 'l -> 'b``
           THEN ASM_REWRITE_TAC[],

           REPEAT STRIP_TAC
         ]
  );



val _ = html_theory "aop";

val _ = export_theory();

end; (* structure aopScript *)
