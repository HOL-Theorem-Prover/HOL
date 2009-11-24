

structure KmonadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory pairTheory categoryTheory monadTheory ;
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

(* abbreviate a much used tactic *)
fun farwmmp con = (FIRST_ASSUM (fn th => 
  CHANGED_TAC (REWRITE_TAC [MATCH_MP con th]))) ; 

(* given f = \x. ..., put into more usual form *)
fun fix_abs_eq rewrs th = 
  let val th0 = REWRITE_RULE ([TY_FUN_EQ_THM, FUN_EQ_THM] @ rewrs) th ; 
    val th1 = CONV_RULE (DEPTH_CONV TY_BETA_CONV) th0 ; 
    val th2 = CONV_RULE (DEPTH_CONV BETA_CONV) th1 ;
  in th2 end ;

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

val _ = type_abbrev ("gunit", Type `: \'A 'M. !'a. ('a, 'a 'M) 'A`);
val _ = type_abbrev ("gmap",
   Type `: \'A 'M. !'a 'b. ('a, 'b) 'A -> ('a 'M, 'b 'M) 'A`);
val _ = type_abbrev ("gjoin", Type `: \'A 'M. !'a. ('a 'M 'M, 'a 'M) 'A`);

val MAPE_def = Define `MAPE ((id, comp) : 'A category) 
    (unit : ('A, 'M) gunit, ext : ('A, 'M) ext) = 
  \:'a 'b. \ (f : ('a, 'b) 'A).
    ext [:'a, 'b:] (comp [:'a, 'b, 'b 'M:] (unit [:'b:]) f)` ;

val JOINE_def = Define `JOINE ((id, comp) : 'A category)
    (unit : ('A, 'M) gunit, ext : ('A, 'M) ext) =
  \:'a. ext [:'a 'M, 'a:] (id [:'a 'M:])` ;

val EXT_def = Define 
  `(EXT ((id, comp) : 'A category) 
    (map : ('A, 'M) gmap, join: ('A, 'M) gjoin) : ('A, 'M) ext) = 
    \:'a 'b. \f. comp join (map [:'a, 'b 'M:] f)` ;

val Kdmonad_def = Define `Kdmonad = \:'A 'M. \ ((id, comp) : 'A category)
    (unit: (!'a. ('a, 'a 'M) 'A), ext: 'M ('A ext),
      map : ('A, 'M) gmap, join: ('A, 'M) gjoin). 
    Kmonad (id, comp) (unit, ext) /\
    (map = MAPE (id,comp) (unit,ext)) ∧
    (join = JOINE (id,comp) (unit,ext))` ;

val Kdmonad_thm = store_thm ("Kdmonad_thm",
  ``Kdmonad (id, comp) (unit,ext,map,join) = 
    Kmonad (id, comp) (unit, ext) /\
    (map = MAPE (id,comp) (unit,ext)) ∧
    (join = JOINE (id,comp) (unit,ext))``,
  SRW_TAC [] [Kdmonad_def]) ;

val (KdmonadD, KdmonadI) = EQ_IMP_RULE Kdmonad_thm ;
val KdmonadDK = ufd CONJUNCT1 KdmonadD ;

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
  "category ((unit, Kcomp (id, comp) ext) : ('A, 'M) Kleisli category)" )
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
  EVERY [ (REPEAT (CHANGED_TAC (ONCE_REWRITE_TAC 
      [Kmonad_thm, Kcomp_def, g_functor_thm, category_thm]))),
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

val Kmonad_exto_euo' = prove (
  ``category [:'A:] (id, comp) /\ Kmonad [:'A,'M:] (id,comp) (unit,ext) ==> 
    (ext (comp g f) = comp (ext g) (ext (comp unit f)))``,
  EVERY [ (REWRITE_TAC [Kmonad_thm, Kcomp_def, category_thm]),
    STRIP_TAC, (ASM_REWRITE_TAC []) ]) ;

val Kmonad_exto_euo = save_thm ("Kmonad_exto_euo", 
  (DISCH_ALL o TY_GEN_ALL o GEN_ALL o UNDISCH_ALL) Kmonad_exto_euo') ;

val Kmonad_extomap' = prove (
  ``Kmonad [:'A,'M:] (id,comp) (unit,ext) /\ category [:'A:] (id, comp) /\ 
      (map = MAPE (id, comp) (unit, ext)) ==> 
    (ext (comp g f) = comp (ext g) (map f))``,
  SRW_TAC [] [MAPE_def, Kmonad_exto_euo] THEN
  USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_exto_euo) ;

val Kmonad_extomap = save_thm ("Kmonad_extomap", 
  (DISCH_ALL o TY_GEN_ALL o GEN_ALL o UNDISCH_ALL) Kmonad_extomap') ;

val Kdmonad_extomap = DISCH_ALL 
  (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Kmonad_extomap) 
  (UNDISCH KdmonadDK)) ;

val Kdmonad_extomap = store_thm ("Kdmonad_extomap", 
  ``Kdmonad [:'A,'M:] (id,comp) (unit,ext,map,join) /\
    category [:'A:] (id, comp) ==> 
    (ext (comp g f) = comp (ext g) (map f))``,
  SRW_TAC [] [Kdmonad_def] THEN
  USE_LIM_RES_TAC MATCH_ACCEPT_TAC (inst_eqs Kmonad_extomap)) ;

val Kmonad_t2a = store_thm ("Kmonad_t2a", 
  ``Kmonad [:'A, 'M:] (id,comp) (unit,ext) /\ category (id, comp) ==>
    (f = ext [:'a, 'b:] g) ==> (ext [:'a 'M, 'b:] f = comp f (ext id))``,
  EVERY [ REPEAT STRIP_TAC, (ASM_REWRITE_TAC []),
    (farwmmp KmonDAss), (farwmmp catDRU) ]) ;

val tmsgx = ``Kmonad [:'A, 'M:] (id,comp) (unit,ext) /\ category (id, comp) ==>
  (ext [:'a, 'b:] (comp f unit) = 
    comp (ext f) (ext [:'a, 'a 'M:] (comp unit unit)))`` ;
val (_, tmsg) = dest_imp tmsgx ;

val Kmonad_t2b = store_thm ("Kmonad_t2b", 
  ``Kmonad [:'A, 'M:] (id,comp) (unit,ext) /\ category (id, comp) ==>
    (ext [:'a 'M, 'b:] f = comp f (ext id)) ==> (f = ext (comp f unit))``,
  (REPEAT STRIP_TAC) THEN (SUBGOAL_THEN tmsg ASSUME_TAC) THENL [
    MAP_EVERY farwmmp [KmonDAss, catDAss, KmonDRU],
    ASM_REWRITE_TAC [] THEN MAP_EVERY farwmmp [ catDRAss,
      KmonDAss, catDAss, KmonDRU, catDLU, KmonDLU, catDRU] ]) ;

val Kmonad_t2b' = DISCH_ALL (GSYM (UNDISCH_ALL Kmonad_t2b)) ;

val Kdmonad_t2b = DISCH_ALL 
  (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Kmonad_t2b) 
  (UNDISCH KdmonadDK)) ;

(* approach to distributive law for monads;
  a monad in the Kleisli category of another monad *)
(* first note this type equality *)
val true = Type `: (('A, 'M) Kleisli, 'N) Kleisli` =
  Type `: ('A, 'N o 'M) Kleisli` ;

(* following fails typechecking when both monad type arguments 
  ('N and 'N o 'M) are deleted (even after temp_clear_overloads_on "o") *)
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

val J1S_def = Define 
  `J1S ((id, comp) : 'A category) (extM : ('A, 'M) ext) extNM =
    (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A.
      extM ((extNM : ('A, 'N o 'M) ext) f) = comp (extNM f) (extM id))` ;

val EQ_IMP_IMP =
  auxLib.sfg (auxLib.ufd CONJUNCT1 o fst o EQ_IMP_RULE) EQ_IMP_THM ;
val hrk = (hd (RES_CANON Kmonad_exto_euo)) ;

val tmepe = ``category (id, comp) /\ 
  Kmonad [:'A:] (id,comp) (unitM, extM : ('A, 'M) ext) /\ 
  J1S (id, comp) extM extNM /\
  (pext = \:'a 'b. \f. comp (extNM f) unitM) ==>
  (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. extM (pext f) = extNM f)`` ;

val J1_IMP_ext_pext = store_thm ("J1_IMP_ext_pext", tmepe,
  EVERY [ (REWRITE_TAC [J1S_def]), STRIP_TAC, (ASM_REWRITE_TAC []), 
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
  J1S (id, comp) extM extNM /\
  (pext = \:'a 'b. \f. comp (extNM f) unitM) ==>
  Kmonad [: ('A, 'M) Kleisli, 'N :] 
    (unitM, Kcomp (id,comp) extM) (unitNM, pext)`` ;

(* can't do MATCH_MP_TAC (GSYM J1_IMP_ext_pext) ; *)
val gjs = (DISCH_ALL o GSYM o SPEC_ALL o TY_SPEC_ALL o UNDISCH)
  J1_IMP_ext_pext ;
val gjs' = (DISCH_ALL o GSYM o SPEC_ALL o TY_SPEC_ALL o UNDISCH)
  (REWRITE_RULE [J1S_def] J1_IMP_ext_pext) ;

val cm_if_J1 = store_thm ("cm_if_J1", tmpexti,  
  EVERY [ (REWRITE_TAC [J1S_def]), STRIP_TAC,
    (MATCH_MP_TAC Kcat_IMP_Kmonad),
    (IMP_RES_TAC Kmonad_IMP_Kcat),
    (FIRST_X_ASSUM (fn th => CONJ_TAC THEN1 ACCEPT_TAC th)),
    (FIRST_X_ASSUM (fn th => EVERY [MP_TAC th, MATCH_MP_TAC EQ_IMP_IMP,
      AP_TERM_TAC, AP_TERM_TAC])),
    (REWRITE_TAC [Kcomp_def, FUN_EQ_THM, TY_FUN_EQ_THM]),
    (* need tactic for \x. A = \y. A *)
    (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
    AP_THM_TAC, AP_TERM_TAC, (MATCH_MP_TAC gjs'),
    (ASM_REWRITE_TAC []) ]) ;

val cm_if_J1' = REWRITE_RULE [J1S_def] cm_if_J1 ;

(* equivalence between compound monads arising from a monad in the 
  Kleisli category of another monad, and compound monads satisfying
  Jones & Duponcheel condition J1 *)
val tm_Kc_J1 = 
  ``category (id,comp) /\ Kmonad (id,comp) (unitM,extM) ==> 
  (Kmonad [: 'A, 'N o 'M :] (id,comp) (unitNM,extNM) /\
  J1S (id, comp) extM extNM /\
  (pext = (\:'a 'b. (\f. comp (extNM f) unitM))) = 
  Kmonad [:('A,'M) Kleisli, 'N:] (unitM,Kcomp (id,comp) extM) (unitNM,pext) /\
  (extNM = (\:'a 'b. (\f. extM (pext f)))))`` ;

val cm_Kc_J1 = store_thm ("cm_Kc_J1", tm_Kc_J1, 
  EVERY [ REWRITE_TAC [J1S_def], STRIP_TAC,
    EQ_TAC, REPEAT STRIP_TAC, REPEAT CONJ_TAC]
  THENL [
    (MATCH_MP_TAC cm_if_J1' THEN ASM_REWRITE_TAC []),
    EVERY [ 
      (REWRITE_TAC [FUN_EQ_THM, TY_FUN_EQ_THM]),
      (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
      MATCH_MP_TAC gjs', (ASM_REWRITE_TAC []) ],

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

(* see also Barr & Wells, conditions (C3) and (C4) for compatible monads,
  (C3) is a special case of E1D, (C4) is a special case of J1S 
  *)

val tm_J1S_E1D = ``category (id, comp) /\ 
  Kdmonad [:'A, 'M:] (id, comp) (unitM, extM, mapM, joinM) /\
  Kmonad [:'A, 'N o 'M:] (id, comp) (unitNM, extNM) /\
  (unitNM = \:'a. comp (unitM [:'a 'N:]) (unitN [:'a:])) ==>
  J1S (id,comp) extM extNM ==> 
    (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. comp (extNM f) (mapM unitN) = extM f)`` ;

val Kdmonad_t2b' = 
  (DISCH_ALL o TY_GEN_ALL o GEN_ALL o UNDISCH o UNDISCH) Kdmonad_t2b ;

val J1S_IMP_E1D = store_thm ("J1S_IMP_E1D", tm_J1S_E1D,
  EVERY [ (REWRITE_TAC [J1S_def]), (REPEAT STRIP_TAC),
    (FIRST_X_ASSUM (ASSUME_TAC o TY_SPEC_ALL)),
    (FIRST_X_ASSUM (Q.ISPEC_THEN `f` ASSUME_TAC)),
    (USE_LIM_RES_TAC (fn th => ONCE_REWRITE_TAC [th]) Kdmonad_t2b'),
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) (GSYM Kdmonad_extomap)),
    (farwmmp catDRAss),
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o GSYM o fix_abs_eq []))),
    (ASM_REWRITE_TAC []), (farwmmp KmonDRU)]) ;

val tm_E1D_J1S = ``category (id, comp) /\ 
  Kdmonad [:'A, 'M:] (id, comp) (unitM, extM, mapM, joinM) /\
  Kmonad [:'A, 'N o 'M:] (id, comp) (unitNM, extNM) /\
  (!: 'a 'b. !f : ('a, 'b 'N 'M) 'A. 
    comp (extNM f) (mapM (unitN : ('A, 'N) gunit)) = extM f) ==>
  J1S (id,comp) extM extNM`` ;

val E1D_IMP_J1S = store_thm ("E1D_IMP_J1S", tm_E1D_J1S,
  EVERY [ (REWRITE_TAC [J1S_def]), (REPEAT STRIP_TAC),
    (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM th])),
    (farwmmp catDAss), (farwmmp KmonDAss), (farwmmp catDRU) ]) ;

(* Barr & Wells, conditions (C2) and (C5) for compatible monads,
  we show these are equivalent *)

val tmBWC25x =
  ``Gmonad (id,comp) [:'N, 'M:] (dunit,dmap,djoin) 
      (unitNM,mapNM,joinNM) unitM ==>
    category (id,comp) /\ Kmonad [:'A, 'N o 'M:] (id,comp) (unitNM,extNM) ==>
    (extNM unitM = djoin) ==> (comp djoin (extNM id) = extNM djoin)`` ;

val (_, tmBWC25) = dest_imp tmBWC25x ;

val BW_C2_C5 = store_thm ("BW_C2_C5", tmBWC25,
  EVERY [ (REPEAT STRIP_TAC),
    (POP_ASSUM (fn th => REWRITE_TAC [GSYM th])),
    (farwmmp KmonDAss), (farwmmp catDRU) ]) ;

val tmBWC52 = 
  ``category [:'A:] (id,comp) ==> 
    Kmonad [:'A, 'N o 'M:] (id,comp) (unitNM,extNM) ==>
    Kdmonad [:'A, 'N:] (id,comp) (unitN,extN,mapN,joinN) ==>
    Kdmonad [:'A, 'M:] (id,comp) (unitM,extM,mapM,joinM) ==>
    (unitNM = \:'a. comp (unitM [:'a 'N:]) (unitN [:'a:])) ==>
    (comp (mapM (joinN [:'a:])) (extNM (id [:'a 'N 'N 'M:])) =
      extNM (mapM (joinN [:'a:]))) ==>
    (extNM (unitM [:'a 'N:]) = (mapM (joinN [:'a:])))`` ;

val BW_C5_C2 = store_thm ("BW_C5_C2", tmBWC52,
  EVERY [ (REPEAT STRIP_TAC),
    (USE_LIM_RES_TAC (fn th => ONCE_REWRITE_TAC [th]) (GSYM Kmonad_t2b')),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, (farwmmp catDAss),
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o REWRITE_RULE [Kdmonad_thm]))),
    (POP_ASSUM_LIST (MAP_EVERY (MAP_EVERY ASSUME_TAC o CONJUNCTS))),
    (ASM_REWRITE_TAC [MAPE_def, JOINE_def]),
    TY_BETA_TAC, BETA_TAC,
    (farwmmp KmonDRU), (farwmmp catDRAss),
    (farwmmp KmonDRU), (farwmmp catDRU) ]) ; 

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

(*---------------------------------------------------------------------------
  Monad predicate, based on unit, map and join term operators,
  generalised to general arrow types and also generalised to be relevant
  to compound monads 
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("dunit", Type `: \'A 'N 'M. !'a. ('a 'M, 'a 'N 'M) 'A`);
val _ = type_abbrev ("dmap",
   Type `: \'A 'N 'M. !'a 'b. ('a, 'b 'M) 'A -> ('a 'N 'M, 'b 'N 'M) 'A`);
val _ = type_abbrev ("djoin",
   Type `: \'A 'N 'M. !'a. ('a 'N 'N 'M, 'a 'N 'M) 'A`);

val EXTD_def = Define 
  `(EXTD ((id, comp) : 'A category) 
  (dmap : ('A, 'N, 'M) dmap, djoin: ('A, 'N, 'M) djoin) : ('A, 'N o 'M) ext) = 
    \:'a 'b. \f. comp djoin (dmap [:'a, 'b 'N:] f)` ;

val Gmonad_def = Define 
   `Gmonad ((id, comp) : 'A category) = \: 'N 'M. 
     \ (dunit: ('A, 'N, 'M) dunit,
                dmap : ('A, 'N, 'M) dmap ,
                djoin: ('A, 'N, 'M) djoin) 
	       (unitNM: ('A, 'N o 'M) gunit,
                mapNM : ('A, 'N o 'M) gmap ,
                joinNM: ('A, 'N o 'M) gjoin)
   (unitM: ('A, 'M) gunit).
     (* map_I *)         (!:'a. dmap (unitM [:'a:]) = id) /\
     (* map_o *)         (!:'a 'b 'c. !(f: ('a, 'b) 'A) (g: ('b, 'c 'M) 'A).
			      dmap (comp g f) = comp (dmap g) (mapNM f)) /\
     (* map_unit *)      (!:'a 'b. !f: ('a, 'b 'M) 'A.
			      comp (dmap f) unitNM = comp dunit f) /\
     (* map_join *) (!:'a 'b. !f: ('a, 'b 'M) 'A.
             comp (dmap f) joinNM = comp djoin (dmap (dmap f))) /\
     (* join_unit *)     (!:'a. comp djoin dunit = id [:'a 'N 'M:]) /\
     (* join_map_unit *) (!:'a. comp djoin (dmap (unitNM [:'a:])) = id) /\
     (* join_map_join *) (!:'a. 
	  comp (djoin [:'a:]) (dmap djoin) = comp djoin joinNM) ` ;

(* check that these typecheck - 
  what you get when either 'N or 'M is the identity monad  *)
val _ = 
``Gmonad (id, comp) [:'N, I:] (unitN, mapN, joinN) (unitN, mapN, joinN) id `` ;
val _ = ``Gmonad (id, comp) [:I, 'M:] 
  ((\:'a. id [:'a 'M:]), EXT (id, comp) (mapM, joinM), (\:'a. id [:'a 'M:])) 
  (unitM, mapM, joinM) unitM `` ;

(* why does this require more type annotations than Gmonad_def ?? *)
val Gmonad_thm = store_thm ("Gmonad_thm", 
  ``Gmonad (id,comp) [:'N,'M:] (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM =
     (* map_I *)  (!:'a. dmap [:'a, 'a:] (unitM [:'a:]) = id [:'a 'N 'M:]) /\ 
     (* map_o *) (!:'a 'b 'c. !(f :('a, 'b) 'A) (g :('b, 'c 'M) 'A).
                    dmap [:'a, 'c:] (comp [:'a, 'b, 'c 'M:] g f) =
                    comp (dmap [:'b, 'c:] g) (mapNM [:'a, 'b:] f)) /\
     (* map_unit *)      (!:'a 'b. !f: ('a, 'b 'M) 'A.
			      comp (dmap f) unitNM = comp dunit f) /\
     (* map_join *) (!:'a 'b. !f: ('a, 'b 'M) 'A.
             comp (dmap f) joinNM = comp djoin (dmap (dmap f))) /\
     (* join_unit *)     (!:'a. comp djoin dunit = id [:'a 'N 'M:]) /\
     (* join_map_unit *) (!:'a. comp djoin (dmap (unitNM [:'a:])) = id) /\
     (* join_map_join *) (!:'a. 
	  comp (djoin [:'a:]) (dmap djoin) = comp djoin joinNM)``,
  SRW_TAC [] [Gmonad_def]) ;

val (GmonadD, _) = EQ_IMP_RULE Gmonad_thm ;
val [GmD1, GmD2, GmD3, GmD4, GmD5, GmD6, GmD7] = 
  map DISCH_ALL (CONJUNCTS (UNDISCH GmonadD)) ;

val tmj = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (joinNM = \:'a. extNM [:'a 'N 'M, 'a:] (id [:'a 'N 'M:]))`` ;

val Gmonad_join = store_thm ("Gmonad_join", tmj,
   EVERY [ (SRW_TAC [] [EXTD_def]), 
     farwmmp (GSYM GmD1), farwmmp (GSYM GmD4),
     farwmmp GmD1, farwmmp catDLU,
     (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;
  
val tmdj = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:]))`` ;

val Gmonad_djoin = store_thm ("Gmonad_djoin", tmdj,
   EVERY [ (SRW_TAC [] [EXTD_def]), 
     farwmmp GmD1, farwmmp catDRU,
     (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmm = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (mapNM = MAPE (id, comp) (unitNM, extNM))`` ;

val Gmonad_map = store_thm ("Gmonad_map", tmm,
  EVERY [ (SRW_TAC [] [EXTD_def, MAPE_def]), 
    farwmmp GmD2, farwmmp catDAss, farwmmp GmD6, farwmmp catDLU,
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmu = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==> 
   (unitNM = \:'a. comp [:'a, 'a 'M, 'a 'N 'M:]
     (dunit [:'a:]) (unitM [:'a:]))`` ;
   
val Gmonad_unit = store_thm ("Gmonad_unit", tmu,
  EVERY [ (SRW_TAC [] []),
    farwmmp (GSYM GmD3), farwmmp GmD1, farwmmp catDLU,
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmmd = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==> 
   (mapNM = \:'a 'b. \ (f : ('a, 'b) 'A).
     dmap [:'a, 'b:] (comp [:'a, 'b, 'b 'M:] (unitM [:'b:]) f))`` ;

val Gmonad_map_d = store_thm ("Gmonad_map_d", tmmd,
  EVERY [ (SRW_TAC [] []),
    farwmmp GmD2, farwmmp GmD1, farwmmp catDLU,
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmeo = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (extNM (comp g f) = comp (extNM g) (mapNM f))`` ;
  
val Gmonad_ext_o = store_thm ("Gmonad_ext_o", tmeo,
  EVERY [ (SRW_TAC [] [EXTD_def]), 
    farwmmp GmD2, farwmmp catDAss ]) ;

val tmee = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (extNM = EXT (id, comp) (mapNM, joinNM))`` ;

val Gmonad_ext_jm = store_thm ("Gmonad_ext_jm", tmee,
  EVERY [ DISCH_TAC, farwmmp Gmonad_join,
    (SRW_TAC [] [EXTD_def, EXT_def]), 
    farwmmp catDRAss, farwmmp (GSYM GmD2), farwmmp catDLU ]) ;

val tmgc = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   Kmonad (id, comp) (unitNM, extNM)`` ;

val Gmonad_IMP_Kmonad = store_thm ("Gmonad_IMP_Kmonad", tmgc,
  EVERY [ DISCH_TAC,
    (FIRST_ASSUM (ASSUME_TAC o SYM o MATCH_MP Gmonad_ext_jm)),
    (SRW_TAC [] [Kmonad_def, EXTD_def]) ] 
  THENL [ 
    EVERY (map farwmmp [GSYM catDAss, GmD3, catDAss, GmD5, catDLU]),
    farwmmp GmD6, 
    EVERY (map farwmmp [GSYM catDAss, GmD2, catDAss, GmD7, GSYM catDAss])
    THEN EVERY [
     (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o fix_abs_eq [EXT_def]))),
     (ASM_REWRITE_TAC []), farwmmp GmD2,
     (FIRST_ASSUM (fn th => 
       CONV_TAC (DEPTH_CONV (REWR_CONV (MATCH_MP catDAss th))))),
     farwmmp (GSYM GmD4), farwmmp catDRAss,
     (ASM_REWRITE_TAC []) ]]) ;

val tmdm = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (dmap = \:'a 'b. \ (f : ('a, 'b 'M) 'A).
     extNM [:'a, 'b:] (comp [:'a, 'b 'M, 'b 'N 'M:] (dunit [:'b:]) f))`` ;

val Gmonad_dmap = store_thm ("Gmonad_dmap", tmdm,
  EVERY [ DISCH_TAC, 
    (FIRST_ASSUM (ASSUME_TAC o GSYM o MATCH_MP Gmonad_ext_jm)),
    (FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [Kmonad_thm] o
      MATCH_MP Gmonad_IMP_Kmonad)),
    (POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o
      List.concat o map CONJUNCTS)),
    farwmmp (GSYM GmD3),
    (ASM_REWRITE_TAC [EXTD_def]), TY_BETA_TAC, BETA_TAC,
    farwmmp GmD2, farwmmp catDAss,
    farwmmp (GSYM GmD4), farwmmp catDRAss, 
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o fix_abs_eq [EXT_def]))),
    (ASM_REWRITE_TAC []), farwmmp catDRU,
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

(* inverse - compound monad gives Gmonad conditions *)

(* presumably there's a left-to-right element in parsing,
  deleting the first instance of Gmonad ... makes parsing fail,
  and I couldn't work out which annotations were needed to fix it *)

val tmginvx8 = ``
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==>
  category (id,comp) /\ Kmonad (id,comp) (unitNM,extNM) /\
  (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\ 
  (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
  (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) ==>
  (extNM = EXTD (id, comp) (dmap, djoin)) `` ;

val (_, tmginv8) = dest_imp tmginvx8 ;

val Kmonad_extD = store_thm ("Kmonad_extD", tmginv8,
  EVERY [ STRIP_TAC,
    (ASM_REWRITE_TAC [FUN_EQ_THM, TY_FUN_EQ_THM, EXTD_def]),
    TY_BETA_TAC, BETA_TAC, (REPEAT STRIP_TAC),
    (farwmmp KmonDAss), (farwmmp catDAss),
    (FIRST_X_ASSUM (fn th => 
      POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o TY_BETA_RULE o 
	REWRITE_RULE [test_lhs_head_var "djoin" th])))),
    (ASM_REWRITE_TAC []), (farwmmp catDLU)]) ;

val tmginvx = ``
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==>
  category (id,comp) /\ Kmonad (id,comp) (unitNM,extNM) /\
  (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\ 
  (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
  (unitNM = \:'a. comp (dunit [:'a:]) (unitM [:'a:])) /\
  (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) /\
  (mapNM = MAPE (id, comp) (unitNM, extNM)) /\
  (joinNM = JOINE (id, comp) (unitNM, extNM)) ==>
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM`` ;

val tmginvx = ``
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==>
  category (id,comp) /\ Kdmonad (id,comp) (unitNM,extNM,mapNM,joinNM) /\
  (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\ 
  (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
  (unitNM = \:'a. comp (dunit [:'a:]) (unitM [:'a:])) /\
  (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) ==>
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM`` ;

val (_, tmginv) = dest_imp tmginvx ;

val Kmonad_IMP_Gmonad = store_thm ("Kmonad_IMP_Gmonad", tmginv,
  EVERY [ REWRITE_TAC [Kdmonad_thm], STRIP_TAC,
    (USE_LIM_RES_TAC (fn th => 
      REWRITE_TAC [Gmonad_thm, GSYM (fix_abs_eq [EXTD_def] th)]) Kmonad_extD),
    (REPEAT CONJ_TAC THEN REPEAT STRIP_TAC) ]
  THENL [
    EVERY [ (FIRST_ASSUM (fn th => MP_TAC (MATCH_MP KmonDLU th))), 
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      STRIP_TAC, (ASM_REWRITE_TAC [])],
    EVERY [ (FIRST_ASSUM (fn th => REWRITE_TAC [test_lhs_head_var "dmap" th])), 
      TY_BETA_TAC, BETA_TAC, (farwmmp catDAss),
      (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_extomap)],
    EVERY [ (FIRST_ASSUM (fn th => MP_TAC (MATCH_MP KmonDRU th))), 
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      STRIP_TAC, (ASM_REWRITE_TAC [])],
    EVERY [ (ASM_REWRITE_TAC [JOINE_def]),
      TY_BETA_TAC, BETA_TAC, (farwmmp KmonDAss), (farwmmp catDRU)],
    (FIRST_ASSUM MATCH_ACCEPT_TAC),
    (farwmmp KmonDLU),
    EVERY [ (ASM_REWRITE_TAC [JOINE_def]),
      TY_BETA_TAC, (farwmmp KmonDAss), (farwmmp catDRU)]]) ;

val Kmonad_IMP_Gmonad' = REWRITE_RULE [Kdmonad_thm] Kmonad_IMP_Gmonad ;

val tmgiffk = ``category (id,comp) ==> 
  (Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\
    (extNM = EXTD (id,comp) (dmap,djoin)) = 
  Kmonad (id,comp) (unitNM,extNM) /\ 
    (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\
    (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
    (unitNM = \:'a. comp (dunit [:'a:]) (unitM [:'a:])) /\
    (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) /\
    (mapNM = MAPE (id, comp) (unitNM, extNM)) /\
    (joinNM = JOINE (id, comp) (unitNM, extNM)))`` ;

val tmgiffk = ``category (id,comp) ==> 
  (Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\
    (extNM = EXTD (id,comp) (dmap,djoin)) = 
  Kdmonad (id,comp) (unitNM,extNM,mapNM,joinNM) /\ 
    (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\
    (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
    (unitNM = \:'a. comp (dunit [:'a:]) (unitM [:'a:])) /\
    (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) )`` ;

val Gmonad_iff_Kmonad = store_thm ("Gmonad_iff_Kmonad", tmgiffk,
  EVERY [ REWRITE_TAC [Kdmonad_thm], STRIP_TAC,
    EQ_TAC, STRIP_TAC, (REPEAT CONJ_TAC) ] 
  THENL [ (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_IMP_Kmonad),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_map),
    (REWRITE_TAC [JOINE_def]) THEN 
      (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_join),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_djoin),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_dmap),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_unit),
    (USE_LIM_RES_TAC ACCEPT_TAC GmD5), (* MATCH_ACCEPT_TAC fails !! *)
    (* inverse direction *)
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_IMP_Gmonad'),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_extD) ]) ;

val tmgfn = 
  ``((id, comp) = (((\:'a. I), (\:'a 'b 'c. combin$o)) : fun category)) ==> 
  (umj_monad (unitN, mapN, joinN) = 
  Gmonad (id, comp) [:'N, I:] (unitN, mapN, joinN) (unitN, mapN, joinN) id)`` ;

val tmgfm = ``category (id, comp) ==> (Kmonad (id, comp) (unitM, extM) /\
      (mapM = MAPE (id, comp) (unitM, extM)) /\
      (joinM = JOINE (id, comp) (unitM, extM)) = 
    Gmonad (id, comp) [:I, 'M:] 
     ((\:'a. id [:'a 'M:]), extM, (\:'a. id [:'a 'M:])) 
      (unitM, mapM, joinM) unitM)`` ;

val Gmonad_N_umj = store_thm ("Gmonad_N_umj", tmgfn,
  SRW_TAC [] [Gmonad_def, umj_monad_def]) ;

(* reverse implication *)
(* these don't work 
Q.INST [`extNM` |-> `dmap`] Kmonad_IMP_Gmonad ;
Q.INST_TYPE [`:'N` |-> `:I`] Kmonad_IMP_Gmonad ;
val th = Q.GEN `extNM` Kmonad_IMP_Gmonad ;
REWRITE_RULE [GSYM LEFT_EXISTS_IMP_THM] th ;
val thae = (snd o EQ_IMP_RULE o SPEC_ALL) LEFT_EXISTS_IMP_THM ;
HO_MATCH_MP thae th ;
*)

val gen_KG = GEN_ALL Kmonad_IMP_Gmonad' ;
val kgtacs = [ (MATCH_MP_TAC gen_KG),
  (Q.EXISTS_TAC `extM`), TY_BETA_TAC, 
  (FIRST_ASSUM (ASSUME_TAC o MATCH_MP KmonDLU)),
  (FIRST_ASSUM (ASSUME_TAC o MATCH_MP KmonDRU)),
  (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), 
  (ASM_REWRITE_TAC []),
  (* same problem here regarding eta-reduction of types,
  so require following two lines *)
  (REWRITE_TAC [Kmonad_thm]),
  (FIRST_X_ASSUM (ACCEPT_TAC o REWRITE_RULE [Kmonad_thm])) ] ;

val gktacsK = [
  (USE_LIM_RES_TAC MP_TAC (inst_eqs Gmonad_IMP_Kmonad)),
  (REWRITE_TAC [EXTD_def]),
  TY_BETA_TAC,
  (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)),
  STRIP_TAC,
  (* (ASM_REWRITE_TAC []) should work here, but problem with 
    recognising eta-equivalent types
    val (_, goal) = top_goal () ;
    val (lhs, rhs) = dest_eq goal ;
    val (rator, ty) = dest_tycomb lhs ;
    val ty1 = eta_conv_ty ty ;
    val ty2 = deep_eta_ty ty ;
    val ty3 = deep_beta_eta_ty ty ;
    *)
  (REWRITE_TAC [Kmonad_thm]),
  (FIRST_X_ASSUM (ACCEPT_TAC o REWRITE_RULE [Kmonad_thm])) ] ; 

val gktacsM = [ 
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th, EXTD_def])
    (inst_eqs Gmonad_map)),
  TY_BETA_TAC, (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ] ;

val gktacsJ = [
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th, JOINE_def, EXTD_def])
    (inst_eqs Gmonad_join)),
  TY_BETA_TAC, (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)), REFL_TAC ] ;

val Gmonad_M_Kmonad = store_thm ("Gmonad_M_Kmonad", tmgfm, 
  EVERY [ STRIP_TAC,
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP catDLU)),
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP catDRU)),
    EQ_TAC, STRIP_TAC ]
  THENL [ EVERY kgtacs, 
    (REPEAT CONJ_TAC) THENL [
      EVERY gktacsK, EVERY gktacsM, EVERY gktacsJ ] ]) ;

val _ = MATCH_MP Gmonad_iff_Kmonad categoryTheory.category_fun ;
val Gmonad_ext_jm' = inst_eqs Gmonad_ext_jm ;


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

