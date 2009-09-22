

structure KmonadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory pairTheory

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "Kmonad";


(* when using Holmake 
Holmake -I /home/users/jeremy/hol-omega/examples/HolOmega
*)

(* try to extend to categories of arbitrary arrow type *)
(* a category is specified by the identity arrows and composition of arrows *)

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
  on this, see discussion below, following Kmonad_IMP_Kcat *)
val category_dual = store_thm ("category_dual",
  ``category [:'A:] (id, comp) ==> category [:'A C:] (id, dual_comp comp)``,
  EVERY [ (REWRITE_TAC [category_def, dual_comp_def]), TY_BETA_TAC,
   (REWRITE_TAC [UNCURRY_DEF]), BETA_TAC, TY_BETA_TAC, BETA_TAC,
   (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []) ]) ;

(* Kleisli arrow, 'A = arrow type in original category, 'M = monad type *)
val _ = type_abbrev ("Kleisli", Type `: \'A 'M 'a 'b. ('a, 'b 'M) 'A`) ;
  
val _ = type_abbrev ("ext", Type `: \'A 'M. !'a 'b. 
  ('a, 'b 'M) 'A -> ('a 'M, 'b 'M) 'A`);

val Kcomp_def = new_definition("Kcomp_def", Term
   `Kcomp ((id, comp) : 'A category) (ext : ('A, 'M) ext) = \:'a 'b 'c.
     \ (h : ('A,'M,'b,'c) Kleisli) (k : ('A,'M,'a,'b) Kleisli). 
     comp (ext h) k : ('A,'M,'a,'c) Kleisli`) ;

val Kmonad_def = new_definition("Kmonad_def", Term
   `Kmonad ((id, comp) : 'A category) 
     (unit: (!'a. ('a, 'a 'M) 'A), ext: 'M ('A ext)) = 
      (* Left unit *)
          (!:'a 'b. !(k: ('a, 'b 'M) 'A). comp (ext k) unit = k) /\
      (* Right unit *)
          (!:'a.  ext (unit : ('a, 'a 'M) 'A) = id) /\
      (* Associative *)
          (!:'a 'b 'c. !(k:('a, 'b 'M) 'A) (h:('b, 'c 'M) 'A).
	      comp (ext h) (ext k) = ext (comp (ext h) k))`);

val (Kcat_monadD, _) = EQ_IMP_RULE (SPEC_ALL Kmonad_def) ;
val [KcmRU, KcmLU, KcmAss] = CONJUNCTS (UNDISCH Kcat_monadD) ;

(* Kleisli category is a category iff 'M is a monad *)

(* VIEW_GOAL_TAC : ((term list * term) -> tactic) -> tactic *)
fun VIEW_GOAL_TAC f (assns, goal) = f (assns, goal) (assns, goal) ;

val Kcat_IMP_Kmonad = store_thm ("Kcat_IMP_Kmonad",
  ``category [:'A:] (id, comp) /\
    category [: ('A, 'M) Kleisli :] (unit, Kcomp (id, comp) ext) ==>
    Kmonad (id, comp) (unit, ext : ('A, 'M) ext)``,
    (REWRITE_TAC [Kmonad_def, Kcomp_def]) THEN
    (REPEAT STRIP_TAC) THENL [
    EVERY [
      (POP_ASSUM (ASSUME_TAC o MATCH_MP catDRU)),
      (POP_ASSUM (ASSUME_TAC o BETA_RULE o TY_BETA_RULE)),
      (ASM_REWRITE_TAC []) ],

    EVERY [
      (POP_ASSUM (ASSUME_TAC o MATCH_MP catDLU)),
      (VIEW_GOAL_TAC (fn (_, goal) => 
	(POP_ASSUM (fn th => MP_TAC (PART_MATCH rand th (rand goal)))))),
      TY_BETA_TAC, BETA_TAC, 
      (POP_ASSUM (ASSUME_TAC o MATCH_MP catDRU)),
      (ASM_REWRITE_TAC []) ],

    EVERY [
      (POP_ASSUM (ASSUME_TAC o MATCH_MP catDAss)),
      (FIRST_ASSUM (ASSUME_TAC o MATCH_MP catDRU)),
      (VIEW_GOAL_TAC (fn (_, goal) => 
	(POP_ASSUM (fn th => MP_TAC (PART_MATCH rand th (rand goal)))))),
      (MATCH_MP_TAC (hd (RES_CANON EQ_TRANS))),
      (POP_ASSUM (ASSUME_TAC o BETA_RULE o TY_BETA_RULE)),
      (POP_ASSUM (ASSUME_TAC o GSYM)),
      (FIRST_ASSUM (ASSUME_TAC o MATCH_MP catDRU)),
      (ASM_REWRITE_TAC []) ]]) ;


(* this next doesn't work (doesn't parse properly) without the type 
  parameter for category (even with a type annotation, ie
  category ((unit, Kcomp (id, comp) ext) : ('A, 'M) Kleisli category)
  so why don't the predicates functor (etc)
  require a type parameter similarly ?? *)
val Kmonad_IMP_Kcat = store_thm ("Kmonad_IMP_Kcat",
  ``category [:'A:] (id, comp) /\
    Kmonad (id, comp) (unit, ext : ('A, 'M) ext) ==> 
    category [: ('A, 'M) Kleisli :] (unit, Kcomp (id, comp) ext)``,
  EVERY [ (REWRITE_TAC [category_def, Kmonad_def, Kcomp_def]),
    (CONV_TAC (DEPTH_CONV TY_BETA_CONV)),
    (REWRITE_TAC [o_THM, I_THM, FUN_EQ_THM, UNCURRY_DEF]),
    (CONV_TAC (TOP_DEPTH_CONV (BETA_CONV ORELSEC TY_BETA_CONV))),
    (REPEAT STRIP_TAC),
    (ASM_REWRITE_TAC [o_THM, I_THM]) ]) ;

(*** PVH:
  If the second type parameter [: ('M, 'A) Kleisli :] is left out,
  the system incorrectly infers that the type parameter needed is
     [:λ'b 'a. ('a, 'a 'M) 'A:]
  which is wrong; the right choice is
     [:λ'a 'b. ('a, 'b 'M) 'A:]
  or [:λ'b 'a. ('b, 'a 'M) 'A:], equivalently.
  Once this incorrect choice is made, the type inference
  process discovers that "category" cannot be reconciled
  with its arguments.

  Why is the incorrect type parameter inferred?

  In the type inference, the following types are inferred bottom-up
  for the application of category to (unit, Kcomp (id, comp) ext):

  category :
    !'B. ((!'a. ('a,'a)'B) #
          (!'a 'b 'c. ('b,'c)'B -> ('a,'b)'B -> ('a,'c)'B)
         ) -> bool

  (unit, Kcomp (id, comp) ext) :
          (!'a. ('a, 'a 'M)'A) #
          (!'a 'b 'c. ('b, 'c 'M)'A -> ('a, 'b 'M)'A -> ('a, 'c 'M)'A)

The typeinference sees that category has a universal type,
and expects to compute a type parameter to substitute for 'B.
This is done by matching the body of category's type with the
second type.  This is a match of two pairs, which is done in
order, left sides first and then right sides.  Unfortunately,
the left sides are not the most advantageous choice here,
because matching
(1)   !'a. ('a,'a)'B   -to-   !'a. ('a, 'a 'M)'A
does not exhibit a case of 'B being applied in the most
general situation, since its two arguments are the same.
Thus the assignment 'B := λ'b 'a. ('a, 'a 'M)'A is chosen,
which is fine for this but then causes the later matches of
(2)        ('b,'c)'B   -to-   ('b, 'c 'M)'A
etc to fail.

The type inference algorithm makes one pass through the term,
inferring types as it goes.  An alternative algorithm could be
written which would take first collect type matching "problems"
in a list, and then later consider these in whatever order seemed
prudent, such as doing matchings like (2) before (1).  This is
in fact how the higher order matching algorithm for real types
is implemented.  But this would take a fair amount of work,
on the order of weeks.
  
***)
(*
show_types := true ;
show_types := false ;
*)

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "Kmonad";

val _ = export_theory();

end; (* structure KmonadScript *)

