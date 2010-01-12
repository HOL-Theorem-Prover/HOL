

structure KmonadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory pairTheory categoryTheory monadTheory ;
open auxLib ; infix RS RSN ;
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

(* now in auxLib
(* abbreviate much used tactics *)
fun farwmmp con = (FIRST_ASSUM (fn th => 
  CHANGED_TAC (REWRITE_TAC [MATCH_MP con th]))) ; 

fun frrc_rewr impth =
  FIRST_REP_RES (fn th => CHANGED_TAC (REWRITE_TAC [th])) impth ;

(* given f = \x. ..., put into more usual form *)
fun fix_abs_eq rewrs th = 
  let val th0 = REWRITE_RULE ([TY_FUN_EQ_THM, FUN_EQ_THM] @ rewrs) th ; 
    val th1 = CONV_RULE (DEPTH_CONV TY_BETA_CONV) th0 ; 
    val th2 = CONV_RULE (DEPTH_CONV BETA_CONV) th1 ;
  in th2 end ;
*)

(* Kleisli arrow, 'A = arrow type in original category, 'M = monad type *)
val _ = type_abbrev ("Kleisli", Type `: \'A 'M 'a 'b. ('a, 'b 'M) 'A`) ;
  
val _ = type_abbrev ("ext", Type `: \'A 'M. !'a 'b. 
  ('a, 'b 'M) 'A -> ('a 'M, 'b 'M) 'A`);

val Kcomp_def = new_definition("Kcomp_def", Term
   `Kcomp ((id, comp) : 'A category) (ext : ('A, 'M) ext) = \:'a 'b 'c.
     \ (h : ('A,'M,'b,'c) Kleisli) (k : ('A,'M,'a,'b) Kleisli). 
     comp (ext h) k : ('A,'M,'a,'c) Kleisli`) ;

val Kcomp_thm = save_thm ("Kcomp_thm", fix_abs_eq [] Kcomp_def) ;

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
val KmonDRAss = save_thm ("KmonDRAss", GSYM KmonDAss) ;

val _ = type_abbrev ("gunit", Type `: \'A 'M. !'a. ('a, 'a 'M) 'A`);
val _ = type_abbrev ("gmap",
   Type `: \'A 'M. !'a 'b. ('a, 'b) 'A -> ('a 'M, 'b 'M) 'A`);
val _ = type_abbrev ("gjoin", Type `: \'A 'M. !'a. ('a 'M 'M, 'a 'M) 'A`);
val _ = type_abbrev ("g_umj_monad", Type `: \'A 'M.
  ('A, 'M) gunit # ('A, 'M) gmap # ('A, 'M) gjoin`);
val _ = type_abbrev ("Kdmonad", Type `: \'A 'M.
  ('A, 'M) gunit # ('A, 'M) ext # ('A, 'M) gmap # ('A, 'M) gjoin`);

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

val Kdmonad_def = Define `Kdmonad = \:'A 'M. \ (id, comp)
    (unit, ext, map, join).
    Kmonad [:'A, 'M:] (id, comp) (unit, ext) /\
    (map = MAPE (id,comp) (unit,ext)) ∧
    (join = JOINE (id,comp) (unit,ext))` ;

val Kdcmonad_def = Define `Kdcmonad =
    \:'A 'M. \ (id, comp) (unit, ext, kcomp, map, join).
    Kdmonad [:'A, 'M:] (id, comp) (unit,ext,map,join) /\
      (kcomp = Kcomp (id, comp) ext)` ;

val Kcmonad_def = Define `Kcmonad =
    \:'A 'M. \ (id, comp) (unit, ext, kcomp).
    Kmonad [:'A, 'M:] (id, comp) (unit,ext) /\
      (kcomp = Kcomp (id, comp) ext)` ;

val Kdmonad_thm = store_thm ("Kdmonad_thm",
  ``Kdmonad [:'A, 'M:] (id, comp) (unit,ext,map,join) = 
    Kmonad [:'A, 'M:] (id, comp) (unit, ext) /\
    (map = MAPE (id,comp) (unit,ext)) ∧
    (join = JOINE (id,comp) (unit,ext))``,
  SRW_TAC [] [Kdmonad_def]) ;

val Kdcmonad_thm = store_thm ("Kdcmonad_thm",
  ``Kdcmonad [:'A, 'M:] (id, comp) (unit,ext,kcomp,map,join) = 
    Kdmonad [:'A, 'M:] (id, comp) (unit,ext,map,join) /\
      (kcomp = Kcomp (id, comp) ext)``,
  SRW_TAC [] [Kdcmonad_def]) ;

val Kcmonad_thm = store_thm ("Kcmonad_thm",
  ``Kcmonad [:'A, 'M:] (id, comp) (unit,ext,kcomp) = 
    Kmonad [:'A, 'M:] (id, comp) (unit,ext) /\
      (kcomp = Kcomp (id, comp) ext)``,
  SRW_TAC [] [Kcmonad_def]) ;

val (KdmonadD, KdmonadI) = EQ_IMP_RULE Kdmonad_thm ;
val KdmonadDK = save_thm ("KdmonadDK", ufd CONJUNCT1 KdmonadD) ;
val KdmonadD_JOIN = ufd (CONJUNCT2 o CONJUNCT2) KdmonadD ;
val KdmonadD_MAP = ufd (CONJUNCT1 o CONJUNCT2) KdmonadD ;

val (KdcmonadD, KdcmonadI) = EQ_IMP_RULE Kdcmonad_thm ;
val KdcmonadDK = save_thm ("KdcmonadDK", ufd CONJUNCT1 KdcmonadD) ;
val KdcmonadD_Kcomp = save_thm ("KdcmonadD_Kcomp", ufd CONJUNCT2 KdcmonadD) ;

val (KcmonadD, KcmonadI) = EQ_IMP_RULE Kcmonad_thm ;
val KcmonadDK = save_thm ("KcmonadDK", ufd CONJUNCT1 KcmonadD) ;
val KcmonadD_Kcomp = save_thm ("KcmonadD_Kcomp", ufd CONJUNCT2 KcmonadD) ;

val Kdc_cmonadD = store_thm ("Kdc_cmonadD",
  ``Kdcmonad [:'A, 'M:] (id, comp) (unit,ext,kcomp,map,join) ==>
    Kcmonad [:'A, 'M:] (id, comp) (unit,ext,kcomp)``,
  SRW_TAC [] [Kcmonad_thm, Kdcmonad_thm, Kdmonad_thm]) ;

val KdmonadD_EXT = store_thm ("KdmonadD_EXT",
  ``category (id, comp) ==> Kdmonad (id, comp) (unit,ext,map,join) ==> 
    (ext = EXT (id, comp) (map, join))``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm]), (REPEAT STRIP_TAC),
    (ASM_REWRITE_TAC [MAPE_def, JOINE_def, EXT_def]),
    (REWRITE_TAC [FUN_EQ_THM, TY_FUN_EQ_THM]),
    TY_BETA_TAC, BETA_TAC, (REPEAT STRIP_TAC),
    (farwmmp KmonDAss), (farwmmp catDAss), 
    (farwmmp KmonDRU), (farwmmp catDLU) ]) ;

val KdmonadD_EXTe = (fix_abs_eq [EXT_def] KdmonadD_EXT) ;
val KdmonadD_JOINe = (fix_abs_eq [JOINE_def] KdmonadD_JOIN) ;
val KdmonadD_MAPe = (fix_abs_eq [MAPE_def] KdmonadD_MAP) ;
val _ = ListPair.map save_thm (
  ["KdmonadD_EXTe", "KdmonadD_JOINe", "KdmonadD_MAPe"], 
  [KdmonadD_EXTe, KdmonadD_JOINe, KdmonadD_MAPe]) ; 
val KdmonadD_EXT_SYM = GSYM KdmonadD_EXTe ;
val KdmonadD_JOIN_SYM = GSYM KdmonadD_JOINe ;
val KdmonadD_MAP_SYM = GSYM KdmonadD_MAPe ;
val _ = ListPair.map save_thm (
  ["KdmonadD_EXT_SYM", "KdmonadD_JOIN_SYM", "KdmonadD_MAP_SYM"], 
  [KdmonadD_EXT_SYM, KdmonadD_JOIN_SYM, KdmonadD_MAP_SYM]) ; 

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
  ``category [:'A:] (id, comp) ==>
    Kmonad (id, comp) (unit, ext) ==> 
    category [: ('A, 'M) Kleisli :] (unit, Kcomp (id, comp) ext)``,
  EVERY [ (REWRITE_TAC [category_def, Kmonad_thm, Kcomp_def]),
    (CONV_TAC (DEPTH_CONV TY_BETA_CONV)),
    (REWRITE_TAC [FUN_EQ_THM, UNCURRY_DEF]),
    (CONV_TAC (TOP_DEPTH_CONV (BETA_CONV ORELSEC TY_BETA_CONV))),
    (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []) ]) ;

val Kcmonad_IMP_Kcat = store_thm ("Kcmonad_IMP_Kcat",
  ``category [:'A:] (id, comp) ==>
    Kcmonad (id, comp) (unit, ext, kcomp) ==> 
    category [: ('A, 'M) Kleisli :] (unit, kcomp)``,
  EVERY [ (REWRITE_TAC [Kcmonad_thm]), (REPEAT STRIP_TAC),
    (USE_LIM_RES_TAC ASSUME_TAC Kmonad_IMP_Kcat),
    (ASM_REWRITE_TAC []) ]) ;

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

(*
val Kdmonad_extomap = DISCH_ALL 
  (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Kmonad_extomap) 
  (UNDISCH KdmonadDK)) ;
*)

val Kdmonad_extomap = store_thm ("Kdmonad_extomap", 
  ``Kdmonad [:'A,'M:] (id,comp) (unit,ext,map,join) ==>
    category [:'A:] (id, comp) ==> 
    (ext (comp g f) = comp (ext g) (map f))``,
  SRW_TAC [] [Kdmonad_def] THEN
  USE_LIM_RES_TAC MATCH_ACCEPT_TAC (inst_eqs Kmonad_extomap)) ;

(*
val Kdmonad_extomap' = (REWRITE_RULE [GSYM AND_IMP_INTRO] Kdmonad_extomap) ;
*)

val Kmonad_t2a = store_thm ("Kmonad_t2a", 
  ``Kmonad [:'A, 'M:] (id,comp) (unit,ext) ==> category (id, comp) ==>
    (f = ext [:'a, 'b:] g) ==> (ext [:'a 'M, 'b:] f = comp f (ext id))``,
  EVERY [ REPEAT STRIP_TAC, (ASM_REWRITE_TAC []),
    (farwmmp KmonDAss), (farwmmp catDRU) ]) ;

val Kdmonad_t2a = save_thm ("Kdmonad_t2a", KdmonadDK RS Kmonad_t2a) ;
val Kmonad_umj47 = save_thm ("Kmonad_umj47", inst_eqs Kmonad_t2a) ;

fun exarg (assns, goal) = 
  let val (_, body) = dest_exists goal ;
    val (lhs, _) = dest_eq body ;
    val (_, arg) = dest_comb lhs ;
  in EXISTS_TAC arg (assns, goal) end ;

val Kdmonad_umj4 = store_thm ("Kdmonad_umj4", 
  ``Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==> 
    category (id, comp) ==>
    (ext [:'a 'M, 'b:] (map h) = comp (map h) (ext id))``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, MAPE_def]),
    (REPEAT STRIP_TAC), 
    (USE_LIM_RES_TAC (MATCH_MP_TAC o GEN_ALL) Kmonad_t2a),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC, 
    (* why doesn't this work ??? (Q.EXISTS_TAC `comp unit h`) *)
    (* why doesn't this work ??? 
      (Q.EXISTS_TAC `comp [:'a,'b,'b 'M:] (unit [:'b:]) h`) *)
    exarg, REFL_TAC ]) ;

val Kdmonad_umj4' = store_thm ("Kdmonad_umj4'", 
  ``Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==> 
    category (id, comp) ==>
    (ext [:'a 'M, 'b:] (map h) = comp (map h) join)``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, MAPE_def, JOINE_def]),
    (REPEAT STRIP_TAC), 
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o fix_abs_eq []))),
    (ASM_REWRITE_TAC []), (farwmmp KmonDAss), (farwmmp catDRU) ]) ;

val Kdmonad_umj7 = store_thm ("Kdmonad_umj7", 
  ``Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==> 
    category (id, comp) ==>
    (ext [:'a 'M 'M, 'a:] join = comp join (ext id))``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, JOINE_def]), (REPEAT STRIP_TAC), 
    (USE_LIM_RES_TAC (MATCH_MP_TAC o GEN_ALL) Kmonad_t2a),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC, 
    (* why doesn't this work ??? (Q.EXISTS_TAC `comp unit h`) *)
    exarg, REFL_TAC ]) ;

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

val Kdmonad_t2b = save_thm ("Kdmonad_t2b", DISCH_ALL 
  (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Kmonad_t2b) 
  (UNDISCH KdmonadDK))) ;

(* get the 7 axioms for unit, map, join *)
val Kdmonad_umj2 = store_thm ("Kdmonad_umj2",
  ``category (id,comp) ==> Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==>
    !f g. map (comp g f) = comp (map g) (map f)``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, MAPE_def]), (REPEAT STRIP_TAC),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KmonDAss), (farwmmp catDAss),
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KmonDRU) ]) ;

val Kdmonad_umj3 = store_thm ("Kdmonad_umj3",
  ``category (id,comp) ==> Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==>
    !f. comp (map f) unit = comp unit f``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, MAPE_def]), (REPEAT STRIP_TAC),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KmonDRU) ]) ;

val Kdmonad_umj1 = store_thm ("Kdmonad_umj1",
  ``category (id,comp) ==> Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==>
    (map id = id)``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, MAPE_def]), (REPEAT STRIP_TAC),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC, (farwmmp catDRU), 
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KmonDLU) ]) ;

val Kdmonad_umj5 = store_thm ("Kdmonad_umj5",
  ``category (id,comp) ==> Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==>
    (comp join unit = id)``,
  EVERY [ (REWRITE_TAC [Kdmonad_thm, JOINE_def]), (REPEAT STRIP_TAC),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, 
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KmonDRU) ]) ;

val Kdmonad_umj6 = store_thm ("Kdmonad_umj6",
  ``category (id,comp) ==> Kdmonad [:'A, 'M:] (id,comp) (unit,ext,map,join) ==>
    (comp join (map unit) = id)``,
  EVERY [ (REPEAT STRIP_TAC),
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KdmonadD_EXT_SYM),
    (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP KdmonadDK)),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC KmonDLU) ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

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

(*
val pext_cm = store_thm ("pext_cm", tmpext,
  EVERY [ STRIP_TAC,
    (MATCH_MP_TAC Kcat_IMP_Kmonad),
    (ASM_REWRITE_TAC [Kcomp_def]), TY_BETA_TAC,
    (IMP_RES_TAC Kmonad_IMP_Kcat),
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o CONV_RULE (REDEPTH_CONV
      (REWR_CONV Kcomp_def ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))))),
    (ASM_REWRITE_TAC [combinTheory.o_THM]) ]) ;
*)

val kmcr = reo_prems rev Kmonad_IMP_Kcat ;
val kcmcr = reo_prems rev Kcmonad_IMP_Kcat ;
val Kcat_IMP_Kmonad' = REWRITE_RULE [GSYM AND_IMP_INTRO] Kcat_IMP_Kmonad ;

val pext_cm = store_thm ("pext_cm", tmpext,
  EVERY [ STRIP_TAC,
    (MATCH_MP_TAC Kcat_IMP_Kmonad),
    (ASM_REWRITE_TAC [Kcomp_def]), TY_BETA_TAC,
    (IMP_RES_TAC Kmonad_IMP_Kcat),
    (IMP_RES_TAC kmcr), 
    (* Kmonad_IMP_Kcat won't work here, this is the same error
      described in dist_monadsScript.sml, proof of Kcm_S3 *)
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o CONV_RULE (REDEPTH_CONV
      (REWR_CONV Kcomp_def ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))))),
    (ASM_REWRITE_TAC [combinTheory.o_THM]) ]) ;

val tmKcpext = ``category (id, comp) ==> 
  Kcmonad [:'A, 'M:] (id,comp) (unitM, extM, kcomp) ==> 
  Kmonad [: ('A, 'M) Kleisli, 'N :] (unitM, kcomp) (unitNM, pext) ==>
  Kmonad [: 'A, 'N o 'M :] (id, comp) (unitNM, \:'a 'b. extM o pext)`` ;

val Kc_pext_cm = store_thm ("Kc_pext_cm", tmKcpext,
  EVERY [ REPEAT STRIP_TAC,
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP Kcat_IMP_Kmonad')),
    (USE_LIM_RES_TAC ASSUME_TAC kcmcr),
    (USE_LIM_RES_TAC MP_TAC kmcr),
    (FIRST_ASSUM (fn th => REWRITE_TAC 
      [MATCH_MP KcmonadD_Kcomp th, Kcomp_def])),
    TY_BETA_TAC, BETA_TAC, (ASM_REWRITE_TAC [combinTheory.o_THM]) ]) ;

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
  Kmonad [:'A, 'M:] (id,comp) (unitM, extM) /\ 
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
val gjs'' = REWRITE_RULE [GSYM AND_IMP_INTRO] gjs' ;
val gjs3 = KcmonadDK RSN (2, gjs'') ;

(* TO BE DELETED 
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
*)

(* variation on the above - TO DO, delete one *)

val tmpextic = ``category (id, comp) /\ 
  Kcmonad [:'A, 'M:] (id,comp) (unitM, extM, kcomp) ==> 
  Kmonad [: 'A, 'N o 'M :] (id, comp) (unitNM, extNM) /\
  J1S (id, comp) extM extNM /\
  (pext = \:'a 'b. \f. comp (extNM f) unitM) ==>
  Kmonad [: ('A, 'M) Kleisli, 'N :] (unitM, kcomp) (unitNM, pext)`` ;

val cm_if_J1c = store_thm ("cm_if_J1c", tmpextic,  
  EVERY [ (REWRITE_TAC [J1S_def]), REPEAT STRIP_TAC,
    (USE_LIM_RES_TAC ASSUME_TAC kcmcr), 
    (MATCH_MP_TAC Kcat_IMP_Kmonad),
    (FIRST_X_ASSUM (fn th => CONJ_TAC THEN1 ACCEPT_TAC th)),
    (USE_LIM_RES_TAC MP_TAC kmcr), 
    (FIRST_ASSUM (fn th => 
      REWRITE_TAC [Kcomp_def, MATCH_MP KcmonadD_Kcomp th])),
    (USE_LIM_RES_TAC ((fn th => REWRITE_TAC [th]) o
      TY_GEN_ALL o GEN_ALL) gjs3), 
    TY_BETA_TAC, BETA_TAC, (REWRITE_TAC []) ]) ;

val cm_if_J1c' = REWRITE_RULE [J1S_def, GSYM AND_IMP_INTRO] cm_if_J1c ;

(* equivalence between compound monads arising from a monad in the 
  Kleisli category of another monad, and compound monads satisfying
  Jones & Duponcheel condition J1 *)
(* TO BE DELETED 
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

val KcmD = save_thm ("KcmD", REWRITE_RULE [GSYM AND_IMP_INTRO]
  (ufd CONJUNCT2 (REWRITE_RULE [EQ_IMP_THM] cm_Kc_J1))) ;
val [KcmD_cm, KcmD_J1S, KcmD_pext] = ListPair.map save_thm
  (["KcmD_cm", "KcmD_J1S", "KcmD_pext"], ufdl CONJUNCTS KcmD) ;
*)

(* similar to above, TO DO, delete one *)
val tm_Kc_J1c = 
  ``category (id,comp) /\ Kcmonad (id,comp) (unitM, extM, kcomp) ==> 
  (Kmonad [: 'A, 'N o 'M :] (id,comp) (unitNM,extNM) /\
  J1S (id, comp) extM extNM /\
  (pext = (\:'a 'b. (\f. comp (extNM f) unitM))) = 
  Kmonad [:('A,'M) Kleisli, 'N:] (unitM, kcomp) (unitNM,pext) /\
  (extNM = (\:'a 'b. (\f. extM (pext f)))))`` ;

val cm_Kc_J1c = store_thm ("cm_Kc_J1c", tm_Kc_J1c, 
  EVERY [ REWRITE_TAC [J1S_def], STRIP_TAC,
    EQ_TAC, REPEAT STRIP_TAC, REPEAT CONJ_TAC]
  THENL [
    (USE_LIM_RES_TAC ACCEPT_TAC cm_if_J1c'),
    EVERY [ 
      (USE_LIM_RES_TAC ((fn th => REWRITE_TAC 
          [FUN_EQ_THM, TY_FUN_EQ_THM, th]) o TY_GEN_ALL o GEN_ALL) gjs3), 
      (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC, REFL_TAC ],
    EVERY [ 
      (USE_LIM_RES_TAC MP_TAC Kc_pext_cm),
      (ASM_REWRITE_TAC [combinTheory.o_DEF]) ],
    EVERY [
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      (farwmmp (KcmonadDK RS KmonDAss)), (farwmmp catDRU) ],
    EVERY [
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC, 
      (farwmmp (KcmonadDK RS KmonDRU)),
      (CONV_TAC (fix_abs_eq_conv [])), (ASM_REWRITE_TAC []) ] ]) ;

val Kc_cmD = save_thm ("Kc_cmD", REWRITE_RULE [GSYM AND_IMP_INTRO]
  (ufd CONJUNCT2 (REWRITE_RULE [EQ_IMP_THM] cm_Kc_J1c))) ;
val [Kc_cmD_cm, Kc_cmD_J1S, Kc_cmD_pext] = ListPair.map save_thm
  (["Kc_cmD_cm", "Kc_cmD_J1S", "Kc_cmD_pext"], ufdl CONJUNCTS Kc_cmD) ;

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

val tm_J1S_iff_E1D = ``category (id, comp) /\ 
  Kdmonad [:'A, 'M:] (id, comp) (unitM, extM, mapM, joinM) /\
  Kmonad [:'A, 'N o 'M:] (id, comp) (unitNM, extNM) /\
  (unitNM = \:'a. comp (unitM [:'a 'N:]) (unitN [:'a:])) ==>
  (J1S (id,comp) extM extNM = 
    (!: 'a 'b. !f : ('a, 'b 'N 'M)'A. comp (extNM f) (mapM unitN) = extM f))``;

val J1S_IFF_E1D = store_thm ("J1S_IFF_E1D", tm_J1S_iff_E1D, 
  STRIP_TAC THEN EQ_TAC THENL 
  [ (MATCH_MP_TAC J1S_IMP_E1D) THEN (ASM_REWRITE_TAC []),
    STRIP_TAC THEN (MATCH_MP_TAC E1D_IMP_J1S) THEN (ASM_REWRITE_TAC [])] ) ; 

(* see also Barr & Wells, conditions (C3) and (C4) for compatible monads,
  (C3) is a special case of E1D, (C4) is a special case of J1S 
  but (C3) implies E1D and (C4) implies J1S 
  *)
(* note - the extra condition here is implied by mapNM f = mapm (mapN f) *)
val tm_C4_J1S = ``category (id, comp) /\ 
  Kdmonad [:'A, 'M:] (id, comp) (unitM, extM, mapM, joinM) /\
  Kdmonad [:'A, 'N o 'M:] (id, comp) (unitNM, extNM, mapNM, joinNM) /\
  (!: 'a 'b. !f. extM (mapNM [:'a,'b:] f) = comp (mapNM [:'a,'b:] f) joinM) ==>
  ((!:'a. extM (joinNM [:'a:]) = comp joinNM joinM) =
  J1S (id,comp) extM extNM)`` ;

fun ttac th = FIRST_X_ASSUM (fn ass => 
  REWRITE_TAC [EXT_def, test_lhs_head_var "extNM" (MATCH_MP th ass)]) ;

val C4_IFF_J1S = store_thm ("C4_IFF_J1S", tm_C4_J1S,
  EVERY [ STRIP_TAC, (REWRITE_TAC [J1S_def]), EQ_TAC] 
  THENL [
    EVERY [
      (* that NM is a monad not required after next step *)
      (FIRST_ASSUM (fn ass => ttac (MATCH_MP KdmonadD_EXT ass))),
      TY_BETA_TAC, BETA_TAC,
      (USE_LIM_RES_TAC (fn th => (REWRITE_TAC [th])) Kdmonad_extomap) ,
      (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []),
      (farwmmp catDRAss), AP_TERM_TAC,
      (USE_LIM_RES_TAC (fn th => (REWRITE_TAC [th])) KdmonadD_EXT_SYM) ,
      (USE_LIM_RES_TAC (fn th => (REWRITE_TAC [th])) KdmonadD_JOIN_SYM),
      (ASM_REWRITE_TAC []) ],
    EVERY [ (REPEAT STRIP_TAC),
     (REPEAT (FIRST_X_ASSUM (fn th => 
       (REWRITE_TAC [JOINE_def, MATCH_MP KdmonadD_JOIN th])))), 
      TY_BETA_TAC, (ASM_REWRITE_TAC []) ]]) ;

val tm_C3_iff_E1D = ``category (id, comp) /\ 
  Kdmonad [:'A, 'M:] (id, comp) (unitM, extM, mapM, joinM) /\
  Kdmonad [:'A, 'N:] (id, comp) (unitN, extN, mapN, joinN) /\
  Kdmonad [:'A, 'N o 'M:] (id, comp) (unitNM, extNM, mapNM, joinNM) /\
  (mapNM = \:'a 'b. \f. mapM (mapN f)) ==>
  ((!: 'a. comp joinNM (mapM unitN) = joinM [:'a 'N:]) =
    (!: 'a 'b. !f.  comp (extNM [:'a, 'b:] f) (mapM unitN) = extM f))``;

val C3_IFF_E1D = store_thm ("C3_IFF_E1D", tm_C3_iff_E1D,
  (EVERY [STRIP_TAC, EQ_TAC, REPEAT STRIP_TAC]) 
  THENL [
    (EVERY [ frrc_rewr KdmonadD_EXTe, frrc_rewr KdmonadD_EXTe,
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      (farwmmp catDRAss), frrc_rewr (GSYM Kdmonad_umj2),
      frrc_rewr Kdmonad_umj3, frrc_rewr Kdmonad_umj2, 
      (farwmmp catDAss), (ASM_REWRITE_TAC []) ]),
    (EVERY [ frrc_rewr KdmonadD_JOINe , frrc_rewr KdmonadD_JOINe,
      (ASM_REWRITE_TAC []) ]) ]) ;
     
(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)
(* Barr & Wells, conditions (C2) and (C5) for compatible monads,
  we show these are equivalent; note, (C5) is (J2) of Jones & Duponcheeel *)

val tmBWC25 =
    ``category (id,comp) /\ Kmonad [:'A, 'N o 'M:] (id,comp) (unitNM,extNM) ==>
    (extNM unitM = djoin) ==> (comp djoin (extNM id) = extNM djoin)`` ;

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

(* J1 and J2, ie, C4 and C5, both imply a certain equality *)
val E1D_J12 = store_thm ("E1D_J12", 
  ``Kmonad [:'A, 'M:] (id,comp) (unitM,extM) ==>
    (!: 'a 'b. !f. comp (extNM f) (mapM unitN) = extM f) ==>
    (comp (extNM unitM) (mapM unitN) = id)``,
  EVERY [ (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []), (farwmmp KmonDLU) ]) ;

val C2_J12 = store_thm ("C2_J12",
  ``category [:'A:] (id,comp) ==>
    Kdmonad [:'A, 'N:] (id,comp) (unitN,extN,mapN,joinN) ==>
    Kdmonad [:'A, 'M:] (id,comp) (unitM,extM,mapM,joinM) ==>
    (extNM unitM = mapM joinN) ==> (comp (extNM unitM) (mapM unitN) = id)``,
  EVERY [ (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []), 
    (frrc_rewr (GSYM Kdmonad_umj2)), 
    (frrc_rewr Kdmonad_umj5), (frrc_rewr Kdmonad_umj1) ]) ;

(* and if dunit = mapM unitN, then from J12, 
  ie, (comp (extNM unitM) (mapM unitN) = id),
  we can satisfy the conditions of Kmonad_IMP_Gmonad *) 

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

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

