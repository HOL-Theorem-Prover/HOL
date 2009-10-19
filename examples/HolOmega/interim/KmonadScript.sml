

structure KmonadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory pairTheory categoryTheory ;
open auxLib ;
(*
load "auxLib" ;
load "KmonadTheory" ; open KmonadTheory ;
fun sge tm = set_goal ([], tm) ;
fun eev tacs = e (EVERY tacs) ;
fun eall [] = () 
  | eall (t :: ts) = (e t ; eall ts) ;
*)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "Kmonad";

(* Kleisli arrow, 'A = arrow type in original category, 'M = monad type *)
val _ = type_abbrev ("Kleisli", Type `: \'A 'M 'a 'b. ('a, 'b 'M) 'A`) ;
  
val _ = type_abbrev ("ext", Type `: \'A 'M. !'a 'b. 
  ('a, 'b 'M) 'A -> ('a 'M, 'b 'M) 'A`);

val Kcomp_def = new_definition("Kcomp_def", Term
   `Kcomp ((id, comp) : 'A category) (ext : ('A, 'M) ext) = \:'a 'b 'c.
     \ (h : ('A,'M,'b,'c) Kleisli) (k : ('A,'M,'a,'b) Kleisli). 
     comp (ext h) k : ('A,'M,'a,'c) Kleisli`) ;

val Kmonad_def = new_definition("Kmonad_def", Term
   `Kmonad = \:'A 'M. \ ((id, comp) : 'A category) 
     (unit: (!'a. ('a, 'a 'M) 'A), ext: 'M ('A ext)). 
      (* Left unit *)
          (!:'a 'b. !(k: ('a, 'b 'M) 'A). comp (ext k) unit = k) /\
      (* Right unit *)
          (!:'a.  ext (unit : ('a, 'a 'M) 'A) = id) /\
      (* Associative *)
          (!:'a 'b 'c. !(k:('a, 'b 'M) 'A) (h:('b, 'c 'M) 'A).
	      comp (ext h) (ext k) = ext (comp (ext h) k))`);

val Kmonad_thm = store_thm ("Kmonad_thm", Term
   `Kmonad ((id, comp) : 'A category) 
     (unit: (!'a. ('a, 'a 'M) 'A), ext: 'M ('A ext)) = 
      (* Left unit *)
          (!:'a 'b. !(k: ('a, 'b 'M) 'A). comp (ext k) unit = k) /\
      (* Right unit *)
          (!:'a.  ext (unit : ('a, 'a 'M) 'A) = id) /\
      (* Associative *)
          (!:'a 'b 'c. !(k:('a, 'b 'M) 'A) (h:('b, 'c 'M) 'A).
	      comp (ext h) (ext k) = ext (comp (ext h) k))`,
  SRW_TAC [] [Kmonad_def]) ;

val (KmonadD, _) = EQ_IMP_RULE (SPEC_ALL Kmonad_thm) ;
val [KmonDRU, KmonDLU, KmonDAss] = map DISCH_ALL (CONJUNCTS (UNDISCH KmonadD)) ;
val _ = map save_thm [("KmonDLU", KmonDLU), ("KmonDRU", KmonDRU),
  ("KmonDAss", KmonDAss)] ;

(* Kleisli category is a category iff 'M is a monad *)

(* VIEW_GOAL_TAC : ((term list * term) -> tactic) -> tactic *)
fun VIEW_GOAL_TAC f (assns, goal) = f (assns, goal) (assns, goal) ;

val Kcat_IMP_Kmonad = store_thm ("Kcat_IMP_Kmonad",
  ``category [:'A:] (id, comp) /\
    category [: ('A, 'M) Kleisli :] (unit, Kcomp (id, comp) ext) ==>
    Kmonad (id, comp) (unit, ext : ('A, 'M) ext)``,
    (REWRITE_TAC [Kmonad_thm, Kcomp_def]) THEN
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
  EVERY [ (REWRITE_TAC [category_def, Kmonad_thm, Kcomp_def]),
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
(** a monad gives a pair of adjoint functors **)
(* first, the functors, unit o _ and ext *)

val Kmonad_IMP_uof = store_thm ("Kmonad_IMP_uof",
  ``category [:'A:] (id,comp) /\ Kmonad (id,comp) (unit,ext) ==>
    g_functor [:'A, ('A, 'M) Kleisli :] (id, comp) 
      (unit, Kcomp (id,comp) ext) (\:'a 'b. comp [:'a,'b,'b 'M:] unit)``,
  EVERY [ (REPEAT (CHANGED_TAC (ONCE_REWRITE_TAC [Kmonad_thm, Kcomp_def, g_functor_thm, category_thm]))),
    STRIP_TAC, TY_BETA_TAC, BETA_TAC, (ASM_REWRITE_TAC []) ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val Kmonad_IMP_ext_f = store_thm ("Kmonad_IMP_ext_f",
  ``Kmonad (id,comp) (unit,ext) ==> g_functor [: ('A, 'M) Kleisli, 'A :] 
      (unit, Kcomp (id,comp) ext) (id, comp) ext``,
  EVERY [ (REWRITE_TAC [Kmonad_thm, Kcomp_def, g_functor_thm]),
    STRIP_TAC, (CONJ_TAC THEN1 FIRST_ASSUM ACCEPT_TAC),
    TY_BETA_TAC, BETA_TAC, (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)),
    (FIRST_ASSUM ACCEPT_TAC) ]) ;

val Kmonad_IMP_unit_nt = store_thm ("Kmonad_IMP_unit_nt",
  ``Kmonad (id,comp) (unit,ext) ==> 
    g_nattransf [:'A:] (id, comp) unit (g_I [:'A:]) 
      (\: 'a 'b. \f. ext [:'a,'b:] (comp (unit [:'b:]) f))``,
  EVERY [ (REWRITE_TAC [Kmonad_thm, Kcomp_def, g_I_def, g_nattransf_thm]),
    STRIP_TAC, TY_BETA_TAC, BETA_TAC, (ASM_REWRITE_TAC [I_THM]) ]) ;

val Kmonad_extomap' = prove (
  ``category [:'A:] (id, comp) /\ Kmonad [:'A,'M:] (id,comp) (unit,ext) ==> 
    (ext (comp g f) = comp (ext g) (ext (comp unit f)))``,
  EVERY [ (REWRITE_TAC [Kmonad_thm, Kcomp_def, category_thm]),
    STRIP_TAC, (ASM_REWRITE_TAC []) ]) ;

val Kmonad_extomap = save_thm ("Kmonad_extomap", 
  (DISCH_ALL o TY_GEN_ALL o GEN_ALL o UNDISCH_ALL) Kmonad_extomap') ;

(* approach to distributive law for monads;
  a monad in the Kleisli category of another monad *)
(* first note this type equality *)
val true = Type `: (('A, 'M) Kleisli, 'N) Kleisli` =
  Type `: ('A, 'N o 'M) Kleisli` ;

(* following fails typechecking when both monad type arguments 
  ('N and 'N o 'M) are deleted *)
val tmpext = ``category (id, comp) /\ 
  Kmonad [:'A:] (id,comp) (unitM, extM : ('A, 'M) ext) /\ 
  Kmonad [: ('A, 'M) Kleisli, 'N :] 
    (unitM, Kcomp (id,comp) extM) (unitNM, pext) ==>
  Kmonad [: 'A, 'N o 'M :] (id, comp) (unitNM, \:'a 'b. extM o pext)`` ;

val pext_cm = store_thm ("pext_cm", tmpext,
  EVERY [ STRIP_TAC,
    (MATCH_MP_TAC Kcat_IMP_Kmonad),
    (ASM_REWRITE_TAC [Kcomp_def]), TY_BETA_TAC,
    (IMP_RES_TAC Kmonad_IMP_Kcat),
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o CONV_RULE (REDEPTH_CONV
      (REWR_CONV Kcomp_def ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))))),
    (ASM_REWRITE_TAC [combinTheory.o_THM]) ]) ;

val EQ_IMP_IMP =
  auxLib.sfg (auxLib.ufd CONJUNCT1 o fst o EQ_IMP_RULE) EQ_IMP_THM ;
val hrk = (hd (RES_CANON Kmonad_extomap)) ;

val tmepe = ``category (id, comp) /\ 
  Kmonad [:'A:] (id,comp) (unitM, extM : ('A, 'M) ext) /\ 
  (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. 
    extM ((extNM : ('A, 'N o 'M) ext) f) = comp (extNM f) (extM id)) /\
  (pext = \:'a 'b. \f. comp (extNM f) unitM) ==>
  (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. extM (pext f) = extNM f)`` ;

val J1_IMP_ext_pext = store_thm ("J1_IMP_ext_pext", tmepe,
  EVERY [ STRIP_TAC, (ASM_REWRITE_TAC []), 
    (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
    (FIRST_ASSUM (fn th => 
      let val mat1 = MATCH_MP hrk th 
      in FIRST_ASSUM (fn ath => 
          (ONCE_REWRITE_TAC [MATCH_MP mat1 ath])) end)),
    (ASM_REWRITE_TAC []), 
    (FIRST_ASSUM (fn th => 
      (REWRITE_TAC [GSYM (MATCH_MP catDAss th)]))),
    (FIRST_ASSUM (fn th => 
      let val mat1 = MATCH_MP hrk th 
      in FIRST_ASSUM (fn ath => 
          (ONCE_REWRITE_TAC [GSYM (MATCH_MP mat1 ath)])) end)),
    (FIRST_ASSUM (fn th => (REWRITE_TAC [MATCH_MP catDLU th]))),
    (FIRST_X_ASSUM (fn th => (REWRITE_TAC [MATCH_MP KmonDLU th]))),
    (FIRST_X_ASSUM (fn th => (REWRITE_TAC [MATCH_MP catDRU th]))) ]) ;

val tmpexti = ``category (id, comp) /\ 
  Kmonad [:'A:] (id,comp) (unitM, extM : ('A, 'M) ext) /\ 
  Kmonad [: 'A, 'N o 'M :] (id, comp) (unitNM, extNM) /\
  (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. 
    extM (extNM f) = comp (extNM f) (extM id)) /\
  (pext = \:'a 'b. \f. comp (extNM f) unitM) ==>
  Kmonad [: ('A, 'M) Kleisli, 'N :] 
    (unitM, Kcomp (id,comp) extM) (unitNM, pext)`` ;

(* can't do MATCH_MP_TAC (GSYM J1_IMP_ext_pext) ; *)
val gjs = (DISCH_ALL o GSYM o SPEC_ALL o TY_SPEC_ALL o UNDISCH)
  J1_IMP_ext_pext ;

val cm_if_J1 = store_thm ("cm_if_J1", tmpexti,  
  EVERY [ STRIP_TAC,
    (MATCH_MP_TAC Kcat_IMP_Kmonad),
    (IMP_RES_TAC Kmonad_IMP_Kcat),
    (FIRST_X_ASSUM (fn th => CONJ_TAC THEN1 ACCEPT_TAC th)),
    (FIRST_X_ASSUM (fn th => EVERY [MP_TAC th, MATCH_MP_TAC EQ_IMP_IMP,
      BETA_TY_TAC, AP_TERM_TAC, AP_TERM_TAC])),
    (REWRITE_TAC [Kcomp_def, FUN_EQ_THM, TY_FUN_EQ_THM]),
    (* need tactic for \x. A = \y. A *)
    (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
    AP_THM_TAC, AP_TERM_TAC, (MATCH_MP_TAC gjs),
    (ASM_REWRITE_TAC []) ]) ;

(* equivalence between compound monads arising from a monad in the 
  Kleisli category of another monad, and compound monads satisfying
  Jones & Duponcheel condition J1 *)
val tm_Kc_J1 = 
  ``category (id,comp) /\ Kmonad (id,comp) (unitM,extM) ==> 
  (Kmonad [: 'A, 'N o 'M :] (id,comp) (unitNM,extNM) /\
  (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. 
    extM [:'a 'N 'M, 'b 'N:] (extNM f) = 
      comp (extNM f) (extM [:'a 'N 'M, 'a 'N:] id)) /\
  (pext = (\:'a 'b. (\f. comp (extNM f) unitM))) = 
  Kmonad [:('A,'M) Kleisli, 'N:] (unitM,Kcomp (id,comp) extM) (unitNM,pext) /\
  (extNM = (\:'a 'b. (\f. extM (pext f)))))`` ;

val cm_Kc_J1 = store_thm ("cm_Kc_J1", tm_Kc_J1, 
  EVERY [STRIP_TAC, EQ_TAC, REPEAT STRIP_TAC, REPEAT CONJ_TAC]
  THENL [
    (MATCH_MP_TAC cm_if_J1 THEN ASM_REWRITE_TAC []),
    EVERY [ 
      (REWRITE_TAC [FUN_EQ_THM, TY_FUN_EQ_THM]),
      (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
      MATCH_MP_TAC gjs, (ASM_REWRITE_TAC []) ],

    EVERY [ (MP_TAC pext_cm),
      (ASM_REWRITE_TAC []),
      (MATCH_MP_TAC EQ_IMP_IMP),
      (REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC)),
      (REWRITE_TAC [FUN_EQ_THM, TY_FUN_EQ_THM]),
      (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
      (MATCH_ACCEPT_TAC combinTheory.o_THM) ],

    EVERY [
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      (FIRST_X_ASSUM (fn th => 
	CHANGED_TAC (REWRITE_TAC [(MATCH_MP KmonDAss th)]))),
      (FIRST_X_ASSUM (fn th => 
	(REWRITE_TAC [(MATCH_MP catDRU th)]))) ],

    EVERY [
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC, 
      (IMP_RES_TAC KmonDRU),
      (ASM_REWRITE_TAC []),
      (CONV_TAC (DEPTH_CONV ETA_CONV)), 
      (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), 
      REFL_TAC ] ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "Kmonad";

val _ = export_theory();

end; (* structure KmonadScript *)

