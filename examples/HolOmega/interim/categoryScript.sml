(*---------------------------------------------------------------------------
	     Categories, Functors and Natural Transformations
	      $Id$
              Originally written for HOL2P by Norbert Voelker
         Ported to HOL-Omega and expanded by Peter Vincent Homeier
      Adapted to categories with arbitrary arrow type by Jeremy Dawson
 ---------------------------------------------------------------------------*)

structure categoryScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory pairTheory

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;
val _ = set_trace "Var of Universal Type Complaint" 1; (* set to 0 to suppress warnings *)

val _ = new_theory "category";

(** categories of arbitrary arrow type, that is, arrows are of type
  ('a, 'b) 'A instead of 'a -> 'b, and functors can be from one category to 
  a category of a different arrow type **)
(* a category is specified by the identity arrows and composition of arrows *)
(* some of this is, in effect, copied from functorScript.sml, 
  but adapted to the more general setting, and many comments copied also *)
(* prefix g_ is used to distinguish types, constants, theorems, etc
  from functorScript.sml *)

val _ = type_abbrev ("id", Type `: \'A. !'a. ('a ('a 'A))`);

val _ = type_abbrev ("o_arrow", Type `: \'A. 
  (!'a 'b 'c. ('c ('b 'A)) -> ('b ('a 'A)) -> ('c ('a 'A)))`);

val _ = type_abbrev ("category", Type `: \'A. (!'a. ('a ('a 'A))) # 
  (!'a 'b 'c. ('c ('b 'A)) -> ('b ('a 'A)) -> ('c ('a 'A)))`) ;

(*
val _ = type_abbrev ("C", Type `: \'A 'a 'b. ('b, 'a) 'A`) ;
*)

val category_def = new_definition("category_def", 
  ``category = \:'A. \ (id: 'A id, comp: 'A o_arrow).
    (* Left Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp id f = f) /\
    (* Right Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp f id = f) /\
    (* Composition *)
    (!:'a 'b 'c 'd. !(f:'b ('a 'A)) (g:'c ('b 'A)) (h:'d ('c 'A)). 
      comp h (comp g f) = comp (comp h g) f)``) ;

(* category_thm can't be done as a definition because 
  new_definition does not yet support `name [:tyvar:] tmvar ... = body` *)
val category_thm = store_thm ("category_thm", 
  ``category [:'A:] (id: 'A id, comp: 'A o_arrow) = (
    (* Left Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp id f = f) /\
    (* Right Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp f id = f) /\
    (* Composition *)
    (!:'a 'b 'c 'd. !(f:'b ('a 'A)) (g:'c ('b 'A)) (h:'d ('c 'A)). 
      comp h (comp g f) = comp (comp h g) f))``,
  SRW_TAC [] [category_def]) ;

val (categoryD, _) = EQ_IMP_RULE (SPEC_ALL category_thm) ;
val [catDLU, catDRU, catDAss] =
  map (TY_GEN_ALL o GEN_ALL o DISCH_ALL) (CONJUNCTS (UNDISCH categoryD)) ;
val catDRAss = GSYM catDAss ;
val _ = map save_thm [("catDLU", catDLU), ("catDRU", catDRU),
  ("catDAss", catDAss), ("catDRAss", catDRAss)] ;

val category_fun = store_thm ("category_fun",
  ``category (((\:'a. I), (\:'a 'b 'c. combin$o) ) : fun category)``,
  SRW_TAC [] [category_def]) ;

(** reversing direction of arrows to form the dual category **)
  
val dual_comp_def = new_definition ("dual_comp_def",
  ``dual_comp (comp : 'A o_arrow) : ('A C) o_arrow = 
    (\:'c 'b 'a. \f g. comp [:'a,'b,'c:] g f)``) ;

(* this fails to parse without the type argument to category,
  even with the annotation category ((id, dual_comp comp) : ('A C) category),
  on this, see discussion which is currently (r7221) in KmonadScript.sml *)
val category_dual = store_thm ("category_dual",
  ``category [:'A:] (id, comp) = category [:'A C:] (id, dual_comp comp)``,
  EQ_TAC THEN SRW_TAC [] [category_thm, dual_comp_def]) ;

(*---------------------------------------------------------------------------
  Functors are homomorphisms between categories.  In this model, functors
  are homomorphisms between the HOL-Omega logic and itself.  A functor
  consists of a type operator F of kind `::ty => ty` and
  a term operator F of type `:!'a 'b. ('a, 'b) 'C -> ('a 'F, 'b 'F) 'D`,
  so that F [:'a,'b:] f : ('a 'F, 'b 'F) 'D whenever f : ('a, 'b) 'C.
  Functors are also required to preserve identities and composition,
  as defined below.  

  We use the variables F', G, H, etc. to denote functors.
  F' is used instead of F because F is already defined as the constant false.
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
      Functor type abbreviation (functor from category 'C to category 'D)
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("g_functor", 
  Type `: \'C 'D 'F. !'a 'b. ('a, 'b) 'C -> ('a 'F, 'b 'F) 'D`);

val _ = type_abbrev ("g_functor_dual", 
  Type `: \'C 'D 'F. !'b 'a. ('a, 'b) 'C -> ('a 'F, 'b 'F) 'D`);

(*---------------------------------------------------------------------------
            Functor predicate
 ---------------------------------------------------------------------------*)

val g_functor_def = new_definition("g_functor_def", 
   ``g_functor = \:'C 'D. \ (idC : 'C id, compC : 'C o_arrow) 
     (idD : 'D id, compD : 'D o_arrow) (F': 'F (('C, 'D) g_functor)).
      (* Identity *) 
          (!:'a. F' [:'a, 'a:] idC = idD) /\
      (* Composition *)
          (!:'a 'b 'c. !(f:('a, 'b) 'C) (g:('b, 'c) 'C).
	    F' (compC g f) = compD (F' g) (F' f)) `` );

val g_functor_thm = store_thm ("g_functor_thm", 
   ``g_functor [:'C, 'D:] (idC : 'C id, compC : 'C o_arrow) 
     (idD : 'D id, compD : 'D o_arrow) (F': 'F (('C, 'D) g_functor)) =
      (* Identity *) 
          (!:'a. F' [:'a, 'a:] idC = idD) /\
      (* Composition *)
          (!:'a 'b 'c. !(f:('a, 'b) 'C) (g:('b, 'c) 'C).
	    F' (compC g f) = compD (F' g) (F' f)) ``,
    SRW_TAC [] [g_functor_def]) ;

(* identity g_functors is a g_functor *)

val g_I_def = Define 
  `g_I = \:'C. \:'a 'b. I : ('a, 'b) 'C -> ('a, 'b) 'C` ;

val g_functor_I = store_thm ("g_functor_I", 
  ``g_functor (idC, compC : 'C o_arrow) (idC, compC) (g_I [:'C:])``,
  SRW_TAC [] [g_functor_thm, g_I_def]) ;

(* composition of g_functors is a g_functor *)

val g_oo_def = Define 
  `$g_oo = \: 'C 'D 'E. 
    \ (G : ('D, 'E, 'G) g_functor) (F' : ('C, 'D, 'F) g_functor).
    \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]` ;
val _ = add_infix("g_oo", 800, HOLgrammars.RIGHT);

val g_oo_thm = store_thm ("g_oo_thm",
  ``(G : ('D, 'E, 'G) g_functor) g_oo (F' : ('C, 'D, 'F) g_functor) =
    \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]``,
  EVERY [(REWRITE_TAC [g_oo_def]), TY_BETA_TAC, BETA_TAC, REFL_TAC ]) ;

val tmo = ``$g_oo G F' = \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]`` ;
val tmw = ``$g_oo [:'C,'D,'E:] G F' =
  \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]`` ;

val ng_oo_def = Define 
  `ng_oo = \: 'C 'D 'E. 
    \ (G : ('D, 'E, 'G) g_functor) (F' : ('C, 'D, 'F) g_functor).
    \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]` ;

val ng_oo_thm = store_thm ("ng_oo_thm",
  ``ng_oo G F' = \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]``,
  EVERY [(REWRITE_TAC [ng_oo_def]), TY_BETA_TAC, BETA_TAC, REFL_TAC ]) ;

val tmno = ``ng_oo G F' = \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]`` ;
val tmnw = ``ng_oo [:'C,'D,'E:] G F' =
  \:'a 'b. G [:'a 'F, 'b 'F:] o F' [:'a,'b:]`` ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)
  
val g_functor_oo = store_thm ("g_functor_oo", 
  ``g_functor (idD, compD) (idE, compE) (G : ('D, 'E, 'G) g_functor) /\
    g_functor (idC, compC) (idD, compD) (F' : ('C, 'D, 'F) g_functor) ==>
    g_functor (idC, compC) (idE, compE) (G g_oo F')``,
    SRW_TAC [] [g_functor_def, g_oo_def]) ;

(* a functor also is a functor between the dual categories;
  but this is a good example of the intricacies of typechecking
  in this area of work, as you have to dualise the functor
  regarding the order of quantifying over the two objects 
  (source and target of an arrow) *)

val g_dual_functor_def = new_definition ("g_dual_functor_def",
  ``g_dual_functor (F': 'F (('C, 'D) g_functor)) =
    (\:'a 'b. F' [:'b, 'a:]) : 'F (('C, 'D) g_functor_dual)``) ;

val g_functor_dual = store_thm ("g_functor_dual",
  ``g_functor [:'C, 'D:] ((idC, compC) : 'C category)
      ((idD, compD) : 'D category) (F': 'F (('C, 'D) g_functor)) =
    g_functor [:'C C, 'D C:] ((idC, dual_comp compC) : 'C C category)
      ((idD, dual_comp compD) : 'D C category) (g_dual_functor F') ``,
  EQ_TAC THEN
  SRW_TAC [] [g_functor_def, g_dual_functor_def, dual_comp_def]) ;

(* but note, 
  ``g_dual_functor (g_I [:'C C:]) = g_I [:'C:]``
  fails parsing, how do we annotate this to make it work?? *)

val g_I_dual = store_thm ("g_I_dual",
  ``g_dual_functor (g_I [:'C:]) = g_I [:'C C:]``,
  SRW_TAC [] [g_dual_functor_def, g_I_def]) ;
  
val g_oo_dual = store_thm ("g_oo_dual",
  ``g_dual_functor ($g_oo [:'C,'D,'E:] G F') =
    $g_oo [:'C C,'D C,'E C:] (g_dual_functor G) (g_dual_functor F')``,
  SRW_TAC [] [g_dual_functor_def, g_oo_thm]) ;

(*---------------------------------------------------------------------------
            Natural transformation type abbreviation
	    (doesn't involve the arrow type of the source category)
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("g_nattransf", ``: \'D 'F 'G. !'a. ('a 'F, 'a 'G) 'D``);

(*---------------------------------------------------------------------------
            Natural transformation predicate
 ---------------------------------------------------------------------------*)

val g_nattransf_prev_def = new_definition("g_nattransf_prev_def", 
   ``g_nattransf_prev = 
     \ (idD, compD : 'D o_arrow) (phi : ('D, 'F,'G) g_nattransf)
	  ( F' : ('C, 'D, 'F) g_functor ) ( G  : ('C, 'D, 'G) g_functor ).
       !:'a 'b. !(h: ('a, 'b) 'C). compD (G h) phi = compD phi (F' h)``) ;

(* the definition g_nattransf_prev_def gave typing problems, 
  including the following rather weird one:

``g_nattransf_prev (idD, dual_comp compD : 'D C o_arrow)
 (phi : ('D C, 'F,'G) g_nattransf)`` ; (* OK *)

``g_nattransf_prev (idD, dual_comp compD : 'D o_arrow)
 (phi : ('D, 'X,'Y) g_nattransf)`` ; (* OK *)

``g_nattransf_prev (idD, dual_comp compD : 'D C o_arrow)
 (phi : ('D C, 'F,'G) g_nattransf)`` ; (* OK *)

``g_nattransf_prev (idD, dual_comp compD : 'D C o_arrow)
 (phi : ('D C, 'X,'Y) g_nattransf)`` handle e => Raise e ; (* fails *)

why should it make a difference whether I use ('F,'G) or ('X,'Y) ??
*) 

val g_nattransf_def = new_definition("g_nattransf_def", 
   ``g_nattransf = \:'D. 
     \ (idD : 'D id, compD : 'D o_arrow) (phi : ('D, 'F,'G) g_nattransf)
	  ( F' : ('C, 'D, 'F) g_functor ) ( G  : ('C, 'D, 'G) g_functor ).
       !:'a 'b. !(h: ('a, 'b) 'C). compD (G h) phi = compD phi (F' h)``) ;

val g_nattransf_thm = store_thm("g_nattransf_thm", 
   ``g_nattransf [:'D:] (idD, compD) (phi : ('D, 'F,'G) g_nattransf) F' G =
       !:'a 'b. !(h: ('a, 'b) 'C). compD (G h) phi = compD phi (F' h)``,
    SRW_TAC [] [g_nattransf_def]) ;

(* thus
``(phi : ('D, 'F,'G) g_nattransf) = (phi : ('D C, 'G,'F) g_nattransf)`` ;
*)

val g_nattransf_dual = store_thm ("g_nattransf_dual",
  ``g_nattransf (idD, compD : 'D o_arrow) (phi : ('D, 'F,'G) g_nattransf)
      ( F' : ('C, 'D, 'F) g_functor ) ( G  : ('C, 'D, 'G) g_functor ) = 
    g_nattransf [:'D C:] (idD, dual_comp compD : 'D C o_arrow) 
      phi (g_dual_functor G) (g_dual_functor F')``,
    EQ_TAC THEN 
    SRW_TAC [] [g_nattransf_thm, dual_comp_def, g_dual_functor_def]) ;
	      
val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "category";

val _ = export_theory();

end; (* structure categoryScript *)

