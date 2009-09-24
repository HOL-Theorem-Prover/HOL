(*---------------------------------------------------------------------------
	     Categories, Functors and Natural Transformations
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

val _ = type_abbrev ("comp", Type `: \'A. 
  (!'a 'b 'c. ('c ('b 'A)) -> ('b ('a 'A)) -> ('c ('a 'A)))`);

val _ = type_abbrev ("category", Type `: \'A. (!'a. ('a ('a 'A))) # 
  (!'a 'b 'c. ('c ('b 'A)) -> ('b ('a 'A)) -> ('c ('a 'A)))`) ;

val _ = type_abbrev ("C", Type `: \'A 'a 'b. ('b, 'a) 'A`) ;

val category_def = new_definition("category_def", 
  ``category = \:'A. \ (id: 'A id, comp: 'A comp).
    (* Left Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp id f = f) /\
    (* Right Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp f id = f) /\
    (* Composition *)
    (!:'a 'b 'c 'd. !(f:'b ('a 'A)) (g:'c ('b 'A)) (h:'d ('c 'A)). 
      comp h (comp g f) = comp (comp h g) f)``) ;

val category_thm = store_thm ("category_thm", 
  ``category [:'A:] (id: 'A id, comp: 'A comp) = (
    (* Left Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp id f = f) /\
    (* Right Identity *)
    (!:'a 'b. !(f:'b ('a 'A)). comp f id = f) /\
    (* Composition *)
    (!:'a 'b 'c 'd. !(f:'b ('a 'A)) (g:'c ('b 'A)) (h:'d ('c 'A)). 
      comp h (comp g f) = comp (comp h g) f))``,
  EVERY [ (REWRITE_TAC [category_def]),
    (CONV_TAC (DEPTH_CONV TY_BETA_CONV)),
    (REWRITE_TAC [UNCURRY_DEF]),
    (CONV_TAC (DEPTH_CONV BETA_CONV)), REFL_TAC ]) ;

(* trying to do category_thm as a definition, get error 
Exception raised at Definition.new_definition:
at new_definition.dest_atom lhs:
at Definition.new_definition:
expected a term of the form "v = M"
*)

(* tried to do this with category_def - failed - why ??
(*** PVH: new_definition does not yet support `name [:tyvar:] tmvar ... = body` ***)
val (categoryD, _) = EQ_IMP_RULE (SPEC_ALL category_def) ;
val cd1 = REWRITE_RULE [FUN_EQ_THM, TY_FUN_EQ_THM, FORALL_PROD] category_def ;
(* why doesn't it rewrite using FORALL_PROD ? *)
(*** PVH: because there are no occurrences of (∀(p :'a # 'b). (P :'a # 'b -> bool) p). ***)
val cd2 = CONV_RULE (DEPTH_CONV TY_BETA_CONV) cd1 ;
val cd3 = (TY_SPEC_ALL cd2) ;
val (fp1, _) = EQ_IMP_RULE FORALL_PROD ;
MATCH_MP fp1 cd3 handle e => Raise e ; (* why ? *)
HO_MATCH_MP fp1 cd3 handle e => Raise e ; (*** PVH: because it needs higher-order matching ***)
val cd3 = SPEC_ALL (TY_SPEC_ALL cd2) ;
*)

val (categoryD, _) = EQ_IMP_RULE (SPEC_ALL category_thm) ;
val [catDLU, catDRU, catDAss] =
  map (TY_GEN_ALL o GEN_ALL o DISCH_ALL) (CONJUNCTS (UNDISCH categoryD)) ;
val _ = map save_thm [("catDLU", catDLU), ("catDRU", catDRU),
  ("catDAss", catDAss)] ;

val category_fun = store_thm ("category_fun",
  ``category (((\:'a. I), (\:'a 'b 'c. combin$o) ) : fun category)``,
  EVERY [ (REWRITE_TAC [category_def]), TY_BETA_TAC,
    (REWRITE_TAC [o_THM, I_THM, FUN_EQ_THM, UNCURRY_DEF]),
    BETA_TAC, TY_BETA_TAC, (REWRITE_TAC [o_THM, I_THM]) ]) ;

(** reversing direction of arrows to form the dual category **)
  
val dual_comp_def = new_definition ("dual_comp_def",
  ``dual_comp (comp : 'A comp) : ('A C) comp = 
    (\:'c 'b 'a. \f g. comp [:'a,'b,'c:] g f)``) ;

(* this fails to parse without the type argument to category,
  even with the annotation category ((id, dual_comp comp) : ('A C) category),
  on this, see discussion which is currently (r7221) in KmonadScript.sml *)
val category_dual = store_thm ("category_dual",
  ``category [:'A:] (id, comp) ==> category [:'A C:] (id, dual_comp comp)``,
  EVERY [ (REWRITE_TAC [category_def, dual_comp_def]), TY_BETA_TAC,
   (REWRITE_TAC [UNCURRY_DEF]), BETA_TAC, TY_BETA_TAC, BETA_TAC,
   (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []) ]) ;

(*---------------------------------------------------------------------------
  Functors are homomorphisms between categories.  In this model, functors
  are homomorphisms between the HOL-Omega logic and itself.  A functor
  consists of a type operator F of kind `::ty => ty` and a term operator F
  of type `:!'a 'b. ('a, 'b) 'C -> ('a 'F, 'b 'F) 'D`,
  so that F f : ('a 'F, 'b 'F) 'D whenever ('a, 'b) 'C.
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
   ``g_functor = \:'C 'D. \ (idC : 'C id, compC : 'C comp) 
     (idD : 'D id, compD : 'D comp) (F': 'F (('C, 'D) g_functor)).
      (* Identity *) 
          (!:'a. F' [:'a, 'a:] idC = idD) /\
      (* Composition *)
          (!:'a 'b 'c. !(f:('a, 'b) 'C) (g:('b, 'c) 'C).
	    F' (compC g f) = compD (F' g) (F' f)) 
      `` );

val g_functor_thm = store_thm ("g_functor_thm", 
   ``g_functor [:'C, 'D:] (idC : 'C id, compC : 'C comp) 
     (idD : 'D id, compD : 'D comp) (F': 'F (('C, 'D) g_functor)) =
      (* Identity *) 
          (!:'a. F' [:'a, 'a:] idC = idD) /\
      (* Composition *)
          (!:'a 'b 'c. !(f:('a, 'b) 'C) (g:('b, 'c) 'C).
	    F' (compC g f) = compD (F' g) (F' f)) ``,
    SRW_TAC [] [g_functor_def]) ;

(* a functor also is a functor between the dual categories;
  but you have to dualise the functor regarding the order of quantifying
  over the two objects (source and target of an arrow) *)

val g_dual_functor_def = new_definition ("g_dual_functor_def",
  ``g_dual_functor (F': 'F (('C, 'D) g_functor)) =
    (\:'a 'b. F' [:'b, 'a:]) : 'F (('C, 'D) g_functor_dual)``) ;

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "category";

val _ = export_theory();

end; (* structure categoryScript *)

