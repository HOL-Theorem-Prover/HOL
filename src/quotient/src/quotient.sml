(* ===================================================================== *)
(*                                                                       *)
(* FILE          : quotient.sml                                          *)
(* VERSION       : 2.1                                                   *)
(* DESCRIPTION   : Functions for creating a quotient type.               *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : February 28, 2005                                     *)
(* COPYRIGHT     : Copyright (c) 2005 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


(* ===================================================================== *)
(*            Q U O T I E N T   T Y P E S   D E F I N E D                *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* This file defines the function "define_quotient_types", which takes   *)
(* one or more existing type and theorems about thm, along with theorems *)
(* about equivalence relations on the types, and creates new types which *)
(* are isomorphic to the equivalence classes of the old types.           *)
(* In addition to creating the new types, functions are defined in the   *)
(* HOL logic to translate between the old and new types in both          *)
(* directions.                                                           *)
(*                                                                       *)
(* The arguments to "define_quotient_types" include an "equivalence"     *)
(* theorem which states that the equivalence relation is in fact         *)
(* reflexive, symmetric, and transitive.                                 *)
(* --------------------------------------------------------------------- *)

structure quotient :> quotient =
struct

open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;

(* In interactive sessions, do:

app load ["pairTheory", "sumTheory", "listTheory", "listLib"];

*)


open pairTheory;
open pairSyntax;
open pairTools;
open sumTheory;
open listTheory;
open listLib;
open combinTheory;
open quotientTheory;
open Rsyntax;


val chatting = ref false;  (* When chatting is false,
                                 gives no output of lifting.
                              When chatting is true, then
                                 every type, constant, and theorem lifted
                                 is printed. *)

val _ = register_btrace("quotient", chatting);



val LIST_INDUCT_TAC =
 let val tm = Term `!P:'a list -> bool.
                       P [] /\ (!t. P t ==> !x. P (x::t)) ==> !l. P l`
     val eq = Thm.ALPHA (concl listTheory.list_induction) tm
     val list_induction' = EQ_MP eq listTheory.list_induction
 in INDUCT_THEN list_induction' ASSUME_TAC
 end;

(*
val MAP_I = TAC_PROOF(([],
   (--`!lst:('a)list. MAP I lst = lst`--)),
   LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC[MAP,I_THM]
  );
*)

fun del_imps tm = if is_imp tm then (del_imps o #conseq o dest_imp) tm
                                else tm;
fun get_ants tm =
    let val {ant,conseq} = (dest_imp o snd o strip_forall) tm
    in
        ant :: get_ants conseq
    end
    handle _ => []

fun CAREFUL_INST_TYPE sub th =
(* e.g., sub = [{redex = ``:'a``, residue = ``:'a term1``},
                {redex = ``:'c``, residue = ``:'b``}] :
                {redex : hol_type, residue : hol_type} list *)
   let val tyvars = type_varsl (map #residue sub)
       val redexs = map #redex sub
       val (asl,con) = dest_thm th
       val th_tyvars = U (map type_vars_in_term (con::asl))
       val old = subtract (intersect tyvars th_tyvars) redexs
       val new = map (fn v => gen_tyvar()) old
   in
       INST_TYPE (sub @ map op |-> (zip old new)) th
   end;


fun C_MATCH_MP imp th =
    let val ant = (#ant o dest_imp o snd o strip_forall o concl) imp
        val subj = (snd o strip_forall o concl) th
        val (_, ty_sub) = match_term ant subj
        val imp' = CAREFUL_INST_TYPE ty_sub imp
    in
        MATCH_MP imp' th
    end;

fun C_MATCH_MP2 imp th1 th2 =
    let val {ant=ant1, conseq} = (dest_imp o snd o strip_forall o concl) imp
        val {ant=ant2, conseq} = (dest_imp o snd o strip_forall) conseq
        val subj1 = (snd o strip_forall o concl) th1
        val subj2 = (snd o strip_forall o concl) th2
        val (_, ty_sub1) = match_term ant1 subj1
        val (_, ty_sub2) = match_term ant2 subj2
        val imp' = CAREFUL_INST_TYPE (ty_sub1 @ ty_sub2) imp
    in
        MATCH_MP (MATCH_MP imp' th1) th2
    end;


fun REWRITE_THM th = REWRITE_TAC[th];

val rec UNDISCH_ALL_TAC :tactic = fn (asl,gl) =>
        if asl = [] then ALL_TAC (asl,gl)
        else (UNDISCH_TAC (hd asl)
              THEN UNDISCH_ALL_TAC) (asl,gl);

val PROVE = Tactical.default_prover;

fun upto from to =
  if from>to then []
  else from::upto (from+1) to;

fun wargs tylist =
  let val nums = upto 1 (length tylist)
(*  val nms = map (fn n => implode ("T"::(explode(chr(n + ord"0"))))) nums in*)
      val nms = map (fn n => "T"^Lib.int_to_string n) nums
  in
      map Psyntax.mk_var (zip nms tylist)
  end;


(* {tyname} is a string, denoting the name of the new quotient type.
   {abs} is a string, denoting the name of the new onto function from the
         original type to the new quotient type.
   {rep} is a string, denoting the name of the new 1-1 function from the
         new quotient type to the original type.
   {equiv} is an "equivalence theorem" for the appropriate type, of the form
                 !(x:'a) (y:'a). R x y = (R x = R y)
         where 'a is the type being lifted to the new quotient type, and
         where R :'a -> 'a -> bool is an equivalence relation on 'a
OR {equiv} is a "partial equivalence theorem", of the form
   (?(x:'a). R x x) /\ (!(x:'a) (y:'a). R x y = R x x /\ R y y /\ (R x = R y))
         where 'a is the type being lifted to the new quotient type, and
         where R :'a -> 'a -> bool is a partial equivalence relation on 'a
*)

(* Test case:

val FUN_PEQUIV = store_thm
  ("FUN_PEQUIV",
   (--`!f:'a->'b.
         (?x. (\r s. f r = f s) x x) /\
         (!x y. (\r s. f r = f s) x y =
                (\r s. f r = f s) x x /\
                (\r s. f r = f s) y y /\
                ((\r s. f r = f s) x = (\r s. f r = f s) y))`--),
   PROVE_TAC[]
  );

val tyname = "mod7";
val abs    = "mod7_ABS";
val rep    = "mod7_REP";
val equiv  = ISPEC ``\n. n MOD 7`` FUN_PEQUIV;

*)


fun define_partial_quotient_type tyname abs rep equiv =
    let

   (* Extract the existing type, ty, and the equivalence relation, REL. *)
        val (exist,pequiv) = CONJ_PAIR equiv
        val (v, exist_tm) = boolSyntax.dest_exists (concl exist)
        val ty = type_of v
        val REL = rator (rator exist_tm)
        val pty = (==`:^ty -> ^ty -> bool`==)
        val _ = assert (curry op = (type_of REL)) pty

   (* Prove that the partial equivalence relation is symmetric. *)
        val (rs,Rrs) = ((I ## lhs) o strip_forall o concl) pequiv
        val (th1,(th2,th3)) = ((I ## CONJ_PAIR) o CONJ_PAIR)
                                 (CONV_RULE (REWR_CONV pequiv) (ASSUME Rrs))
        val sym1 = GENL rs (DISCH_ALL (CONV_RULE (REWR_CONV (GSYM pequiv))
                                          (LIST_CONJ [th2, th1, SYM th3])))
        val sym = GENL rs
                    (IMP_ANTISYM_RULE (SPECL rs sym1) (SPECL (rev rs) sym1))

(* We will now define the new type, and call it nty here.
   We represent nty values as equivalence classes of ty objects.
   The classes are functions from ty to bool.  However, not all such
   functions are also suitable equivalence classes.  We must restrict
   the type ty->bool by a predicate.

   We take the predicate P to be

     P : (ty -> bool) -> bool
     P = \c. ?r. REL r r /\ (c = REL r)

   That is, consider the sets of ty-values which are REL-equivalent.
   Let each such set be represented by its characteristic function,
   of type ty -> bool.  Then any set of ty-values is such an equivalence
   set if and only if there is some ty, r, which is reflexive on REL
   and whose characteristic function is the same as that of the given set.

   If P c, then c is a suitable function to represent an nty.
*)

(* First we show that there is such a set of objects, that the 
   predicate P is non-empty.  *)

        val r = variant (free_vars REL) (mk_var{Name="r", Ty=ty})
        val rcl = mk_comb{Rator=REL, Rand=r}
        val Rrr = mk_comb{Rator=rcl, Rand=r}
        val cty = type_of rcl
        val c = variant (free_vars rcl) (mk_var{Name="c", Ty=cty})
        val c' = prim_variant (c::free_vars rcl) c
        val P = (--`\^c. ?^r. ^Rrr /\ (^c = ^rcl)`--)
        val x = variant (free_vars P) (mk_var{Name="x", Ty=ty})
        val xcl = mk_comb{Rator=REL, Rand=x}
        val Rxx = mk_comb{Rator=xcl, Rand=x}
        val ty_exists =
            CHOOSE (x,exist)
              (EXISTS (--`?^c. ^P ^c`--, xcl)
                 (EQ_MP (SYM (BETA_CONV (mk_comb{Rator=P, Rand=xcl})))
                        (EXISTS (--`?^r. ^Rrr /\ (^xcl = ^rcl)`--, x)
                           (CONJ (ASSUME Rxx) (REFL xcl)))))
            handle e => Raise e

(* or,
        val ty_exists = TAC_PROOF(([],
                        --`?^c. ^P ^c`--),
                        STRIP_ASSUME_TAC exist
                        THEN FIRST_ASSUM (fn th => EXISTS_TAC(rator(concl th)))
                        THEN CONV_TAC BETA_CONV
                        THEN FIRST_ASSUM (fn th => EXISTS_TAC(rand (concl th)))
                        THEN CONJ_TAC
                        THENL
                          [ POP_ASSUM ACCEPT_TAC,
                            REFL_TAC
                          ])
*)

(* Then we can define the new type obj using 'new_type_definition'. *)
        val TY_DEF =  new_type_definition( tyname, ty_exists )
        val nty = (hd o #Args o dest_type o type_of o #Bvar o dest_exists
                      o concl) TY_DEF

(* This creates the new type, "nty", but only implicitly establishes its
   relationships to the original type of equivalence classes on ty.
   To define the bijections to and from the new type, we use 
   'define_new_type_bijections'.  This defines
                   ty_ABS : (ty -> bool) -> nty
                   ty_REP : nty -> (ty -> bool) .
*)
        val ty_bijections = define_new_type_bijections{
                             name = tyname ^ "_bijections",
                             ABS  = abs ^ "_CLASS",
                             REP  = rep ^ "_CLASS",
                             tyax = TY_DEF}
        val ABS_REP = CONJUNCT1 ty_bijections
        val AR1 = (#lhs o dest_eq o #Body o dest_forall o concl) ABS_REP
        val {Rator=cty_ABS, Rand=AR2} = dest_comb AR1
        val cty_REP = #Rator(dest_comb AR2)
(* or,
        val cty_ABS = mk_const{Name = tyname ^ "_ABS_CLASS",
                              Ty = mk_type{Tyop="fun", Args=[cty,nty]}}
        val cty_REP = mk_const{Name = tyname ^ "_REP_CLASS",
                              Ty = mk_type{Tyop="fun", Args=[nty,cty]}}
*)

(* ty_bijections looks like
        (!a. cty_ABS (cty_REP a) = a) /\
        (!r. (\c. ?r. REL r r /\ (c = REL r)) r =
             (cty_REP (cty_ABS r) = r))
but it could look like
        (!a. cty_ABS (cty_REP a) = a) /\
        (!c. (?r. REL r r /\ (c = REL r)) =
             (cty_REP (cty_ABS c) = c))
*)

(* These bijections can be described more naturally and usefully. *)
        val cty_ABS_REP = save_thm
                (tyname ^ "_ABS_REP_CLASS",
                 CONV_RULE (RAND_CONV (RAND_CONV (ALPHA_CONV c THENC
                                 ABS_CONV (LAND_CONV BETA_CONV))))
                           ty_bijections)
(*
        val cty_ABS_REP = store_thm
                (tyname ^ "_ABS_REP_CLASS",
                 (--`(!a. ^cty_ABS (^cty_REP a) = a) /\
                     (!^c. ^(beta_conv (mk_comb{Rator=P, Rand=c})) =
                           (^cty_REP (^cty_ABS ^c) = ^c))`--),
                 REWRITE_TAC[ty_bijections]
                 THEN REWRITE_TAC[GSYM ty_bijections]
                 THEN BETA_TAC
                 THEN GEN_TAC
                 THEN REFL_TAC)
*)

(* We now use standard functions to prove that these bijection functions
   are one-to-one and onto.  The ABS function is one-to-one on its
   defined domain.
*)
        val cty_REP_one_one = prove_rep_fn_one_one cty_ABS_REP
        val cty_REP_onto    = prove_rep_fn_onto    cty_ABS_REP
        val cty_ABS_one_one = 
              CONV_RULE (RAND_CONV (ALPHA_CONV c THENC
                                 ABS_CONV (RAND_CONV (ALPHA_CONV c' THENC
                                 ABS_CONV
                     (LAND_CONV BETA_CONV THENC
                      RAND_CONV (LAND_CONV BETA_CONV))))))
                              (prove_abs_fn_one_one ty_bijections)
        val cty_ABS_onto    = 
              CONV_RULE (RAND_CONV (ABS_CONV (RAND_CONV (ALPHA_CONV c THENC
                               ABS_CONV (RAND_CONV BETA_CONV)))))
                              (prove_abs_fn_onto ty_bijections)

(*
> val obj_REP_one_one =
    |- !a a'. (obj_REP a = obj_REP a') = a = a'
> val obj_REP_onto =
    |- !r. (\c. ?a. c = ALPHA_obj a) r = (?a. r = obj_REP a)
> val obj_ABS_one_one =
    |- !r r'.
         (\c. ?a. c = ALPHA_obj a) r ==>
         (\c. ?a. c = ALPHA_obj a) r' ==>
         ((obj_ABS r = obj_ABS r') = r = r')
> val obj_ABS_onto =
    |- !a. ?r. (a = obj_ABS r) /\ (\c. ?a. c = ALPHA_obj a) r
*)

(* ===================================================================== *)
(* define function to yield representative objects of the new objects    *)
(*     ty_REP : nty -> ty, etc.                                          *)
(* We use the Hilbert choice operator (@) to not predjudice the choice.  *)
(* ===================================================================== *)

        val ty_REP = mk_var{Name = rep,
                            Ty = mk_type{Tyop="fun", Args=[nty,ty]}}
        val ty_REP_def =
            new_definition(rep ^ "_def",
               --`^ty_REP a = $@ (^cty_REP a)`--)
        val ty_REP = (rator o lhs o #Body o dest_forall o concl) ty_REP_def

(* ===================================================================== *)
(* define function to yield new objects from the base objects            *)
(*     ty_ABS : ty -> nty, etc.                                          *)
(* We use the one-argument version of the curried equivalence relation.  *)
(* ===================================================================== *)

        val ty_ABS = mk_var{Name = abs,
                            Ty = mk_type{Tyop="fun", Args=[ty,nty]}}
        val ty_ABS_def =
            new_definition(abs ^ "_def",
               --`^ty_ABS r = ^cty_ABS (^REL r)`--)
        val ty_ABS = (rator o lhs o #Body o dest_forall o concl) ty_ABS_def

(* ======================= *)
(*       L E M M A S       *)
(* ======================= *)

        val r'tm = mk_var{Name="r'", Ty=ty}
        val r'cl = mk_comb{Rator=REL, Rand=r'tm}
        val rr'cl = mk_comb{Rator=rcl, Rand=r'tm}
        val req = mk_eq{lhs=rcl, rhs=r'cl}

        val atm = mk_var{Name="a", Ty=nty}
        val ABS_REP = CONJUNCT1 cty_ABS_REP
        val REP_ABS = CONJUNCT2 cty_ABS_REP

        val ty_REP_REL =
            GEN atm
               (EQ_MP (SYM (SPEC (mk_comb{Rator=cty_REP, Rand=atm}) REP_ABS))
                      (AP_TERM cty_REP (SPEC atm ABS_REP)))

(* Alternative proof:
        val ty_REP_REL =
            (GEN atm o REWRITE_RULE[GSYM REP_ABS]
               o AP_TERM cty_REP o SPEC atm) ABS_REP
*)

        val cty_REP_ABS = TAC_PROOF(([],
            (--`!r. ^REL r r ==>
                       (^cty_REP (^cty_ABS (^REL r)) = ^REL r)`--)),
            GEN_TAC
            THEN DISCH_TAC
            THEN REWRITE_TAC[GSYM (CONJUNCT2 cty_ABS_REP)]
            THEN EXISTS_TAC r
            THEN ASM_REWRITE_TAC[])

        fun DISCH_ONE th = DISCH (hd (hyp th)) th
        fun DISCH_ALL_REV th = foldr (fn (a,th) => DISCH a th) th (hyp th)

        val cty_ABS_11 =
            let val aeq = mk_eq{lhs=mk_comb{Rator=cty_ABS, Rand=rcl},
                                rhs=mk_comb{Rator=cty_ABS, Rand=r'cl}}
                val th1 = AP_TERM cty_REP (ASSUME aeq)
                val th2 = cty_REP_ABS
                val x = mk_var{Name="x", Ty=cty}
                val y = mk_var{Name="y", Ty=cty}
                val th3 = SUBST [x |-> UNDISCH (SPEC r th2),
                                 y |-> UNDISCH (SPEC r'tm th2)]
                                (mk_eq{lhs=x, rhs=y})
                                th1
                val th4 = DISCH_ONE th3
                val th5 = DISCH_ALL (AP_TERM cty_ABS (ASSUME req))
            in
                GENL[r,r'tm] (DISCH_ALL_REV (IMP_ANTISYM_RULE th4 th5))
            end;

(* Alternative proof:
        val cty_ABS_11 = TAC_PROOF(([],
            (--`!r r'. ^REL r r ==> ^REL r' r' ==>
                       ((^cty_ABS (^REL r) = ^cty_ABS (^REL r')) =
                        (^REL r = ^REL r'))`--)),
            GEN_TAC THEN GEN_TAC
            THEN DISCH_TAC THEN DISCH_TAC
            THEN EQ_TAC
            THENL
              [ DISCH_THEN (MP_TAC o AP_TERM cty_REP)
                THEN IMP_RES_THEN REWRITE_THM cty_REP_ABS,

                DISCH_THEN REWRITE_THM
              ])
*)

        val ty_REL_SELECT_REL =
            GEN r (DISCH_ALL (SYM (last (CONJUNCTS
                      (CONV_RULE (REWR_CONV pequiv)
                            (UNDISCH (ISPECL [rcl,r] SELECT_AX)))))));


(* ================================================= *)
(*       Q U O T I E N T   P R O P E R T I E S       *)
(* ================================================= *)

(* Prove the quotient type bijection properties for ABS and REP. *)

        val ABS_REP_tm = (--`^ty_ABS (^ty_REP a)`--)
        val inst = ASSUME (--`^cty_REP a = ^rcl`--)
        val REP_a_tm = mk_comb{Rator=ty_REP, Rand=atm}

        val ty_ABS_REP =
            (GEN atm o
             REWRITE_RULE[ABS_REP] o 
             CHOOSE (r, SPEC atm ty_REP_REL) o
             UNDISCH o CONV_RULE (REWR_CONV AND_IMP_INTRO) o DISCH_ALL o
             REWRITE_RULE[SYM inst] o
             REWRITE_RULE[UNDISCH (SPEC r ty_REL_SELECT_REL)] o
             REWRITE_RULE[inst])
               (REWRITE_CONV[ty_ABS_def,ty_REP_def] ABS_REP_tm)

        val REL_REP_REFL = TAC_PROOF(([],
            (--`!a. ^REL (^ty_REP a) (^ty_REP a)`--)),
            GEN_TAC
            THEN STRIP_ASSUME_TAC (SPEC atm ty_REP_REL)
            THEN ASM_REWRITE_TAC[ty_REP_def]
            THEN IMP_RES_THEN REWRITE_THM ty_REL_SELECT_REL
            THEN MATCH_MP_TAC sym1
            THEN IMP_RES_THEN REWRITE_THM ty_REL_SELECT_REL
            THEN FIRST_ASSUM ACCEPT_TAC)

(*
        val ty_REP_REFL = GEN atm (SPEC REP_a_tm refl)
*)

        val equiv_ty_ABS = TAC_PROOF(([],
            (--`!r r'. ^REL r r' =
                       ^REL r r /\ ^REL r' r' /\ (^ty_ABS r = ^ty_ABS r')`--)),
            GEN_TAC THEN GEN_TAC
            THEN CONV_TAC (LAND_CONV (REWR_CONV pequiv))
            THEN REWRITE_TAC[ty_ABS_def]
            THEN EQ_TAC
            THEN STRIP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN POP_ASSUM MP_TAC
            THEN IMP_RES_THEN (IMP_RES_THEN REWRITE_THM) cty_ABS_11)

(* alternative proofs:
*)

        val QUOTIENT_thm = REWRITE_RULE[GSYM QUOTIENT_def]
                           (LIST_CONJ [ty_ABS_REP, REL_REP_REFL, equiv_ty_ABS])

    in
       save_thm(tyname^"_QUOTIENT", QUOTIENT_thm)
    end;



fun is_match_term tm1 tm2 =
    (match_term tm1 tm2; true) handle _ => false;

val partial_equiv_tm =
    --`(?(x:'a). R x x) /\
       (!(x:'a) (y:'a). R x y = R x x /\ R y y /\ (R x = R y))`--;

fun is_partial_equiv th = is_match_term partial_equiv_tm (concl th);

fun define_quotient_type tyname abs rep equiv =
    if is_match_term partial_equiv_tm (concl equiv) then
         define_partial_quotient_type tyname abs rep equiv
    else
    let

   (* Extract the existing type, ty, and the equivalence relation, REL. *)
        val (vs, equiv_tm) = strip_forall (concl equiv)
        val v = hd vs
        val ty = type_of v
        val REL = rator (rator (lhs equiv_tm))
        val pty = (==`:^ty -> ^ty -> bool`==)
        val _ = assert (curry op = (type_of REL)) pty

        val refl = GEN v (EQ_MP (SYM (SPECL[v,v] equiv))
                                (REFL (mk_comb{Rator=REL, Rand=v})))

(* We will now define the new type, and call it nty here.
   We represent nty values as equivalence classes of ty objects.
   The classes are functions from ty to bool.  However, not all such
   functions are also suitable equivalence classes.  We must restrict
   the type ty->bool by a predicate.

   We take the predicate P to be

     P : (ty -> bool) -> bool
     P = \c. ?r. c = REL r

   That is, consider the sets of ty-values which are REL-equivalent.
   Let each such set be represented by its characteristic function,
   of type ty -> bool.  Then any set of ty-values is such an equivalence
   set if and only if there is some ty, a, whose characteristic 
   function is the same as that of the given set.

   If P x, then x is a suitable function to represent an obj.
*)

(* First we show that there is such a set of objects, that the 
   predicate P is non-empty.  *)

        val rtm = mk_var{Name="r", Ty=ty}
        val rcl = mk_comb{Rator=REL, Rand=rtm}
        val cty = type_of rcl
        val P = (--`\c. ?r. c = ^rcl`--)
        val ty_exists =
            EXISTS (--`?x. ^P x`--, rcl)
                   (EQ_MP (SYM (BETA_CONV (mk_comb{Rator=P, Rand=rcl})))
                          (EXISTS (--`?a. ^rcl = ^REL a`--, rtm) (REFL rcl)))
(* or,
        val ty_exists = TAC_PROOF(([],
                        --`?x. ^P x`--),
                        EXISTS_TAC rcl
                        THEN BETA_TAC
                        THEN EXISTS_TAC rtm
                        THEN REFL_TAC)
*)

(* Then we can define the new type obj using 'new_type_definition'. *)
        val TY_DEF =  new_type_definition( tyname, ty_exists )
        val nty = (hd o #Args o dest_type o type_of o #Bvar o dest_exists
                      o concl) TY_DEF

(* This creates the new type, "nty", but only implicitly establishes its
   relationships to the original type of equivalence classes on ty.
   To define the bijections to and from the new type, we use 
   'define_new_type_bijections'.  This defines
                   ty_ABS : (ty -> bool) -> nty
                   ty_REP : nty -> (ty -> bool) .
*)
        val ty_bijections = define_new_type_bijections{
                             name = tyname ^ "_bijections",
                             ABS  = abs ^ "_CLASS",
                             REP  = rep ^ "_CLASS",
                             tyax = TY_DEF}
        val ABS_REP = CONJUNCT1 ty_bijections
        val AR1 = (#lhs o dest_eq o #Body o dest_forall o concl) ABS_REP
        val {Rator=cty_ABS, Rand=AR2} = dest_comb AR1
        val cty_REP = #Rator(dest_comb AR2)
(* or,
        val cty_ABS = mk_const{Name = tyname ^ "_ABS_CLASS",
                              Ty = mk_type{Tyop="fun", Args=[cty,nty]}}
        val cty_REP = mk_const{Name = tyname ^ "_REP_CLASS",
                              Ty = mk_type{Tyop="fun", Args=[nty,cty]}}
*)

(* These bijections can be described more naturally and usefully. *)
        val cty_ABS_REP = store_thm
                (tyname ^ "_ABS_REP_CLASS",
                 (--`(!a. ^cty_ABS (^cty_REP a) = a) /\
                     (!r. ^cty_REP (^cty_ABS (^REL r)) = ^REL r)`--),
                 REWRITE_TAC[ty_bijections]
                 THEN REWRITE_TAC[GSYM ty_bijections]
                 THEN BETA_TAC
                 THEN GEN_TAC
                 THEN EXISTS_TAC rtm
                 THEN REFL_TAC)

(* We now use standard functions to prove that these bijection functions
   are one-to-one and onto.  The ABS function is one-to-one on its
   defined domain.
*)
        val cty_REP_one_one = prove_rep_fn_one_one ty_bijections
        val cty_REP_onto    = prove_rep_fn_onto    ty_bijections
        val cty_ABS_one_one = prove_abs_fn_one_one ty_bijections
        val cty_ABS_onto    = prove_abs_fn_onto    ty_bijections

(*
> val obj_REP_one_one =
    |- !a a'. (obj_REP a = obj_REP a') = a = a'
> val obj_REP_onto =
    |- !r. (\c. ?a. c = ALPHA_obj a) r = (?a. r = obj_REP a)
> val obj_ABS_one_one =
    |- !r r'.
         (\c. ?a. c = ALPHA_obj a) r ==>
         (\c. ?a. c = ALPHA_obj a) r' ==>
         ((obj_ABS r = obj_ABS r') = r = r')
> val obj_ABS_onto =
    |- !a. ?r. (a = obj_ABS r) /\ (\c. ?a. c = ALPHA_obj a) r
*)

(* ===================================================================== *)
(* define function to yield representative objects of the new objects    *)
(*     ty_REP : nty -> ty, etc.                                         *)
(* We use the Hilbert choice operator (@) to not predjudice the choice.  *)
(* ===================================================================== *)

        val ty_REP = mk_var{Name = rep,
                            Ty = mk_type{Tyop="fun", Args=[nty,ty]}}
        val ty_REP_def =
            new_definition(rep ^ "_def",
               --`^ty_REP a = $@ (^cty_REP a)`--)
        val ty_REP = (#Rator o dest_comb o #lhs o dest_eq
                       o #Body o dest_forall o concl) ty_REP_def

(* ===================================================================== *)
(* define function to yield new objects from the base objects            *)
(*     ty_ABS : ty -> nty, etc.                                         *)
(* We use the one-argument version of the curried equivalence relation.  *)
(* ===================================================================== *)

        val ty_ABS = mk_var{Name = abs,
                            Ty = mk_type{Tyop="fun", Args=[ty,nty]}}
        val ty_ABS_def =
            new_definition(abs ^ "_def",
               --`^ty_ABS r = ^cty_ABS (^REL r)`--)
        val ty_ABS = (#Rator o dest_comb o #lhs o dest_eq
                       o #Body o dest_forall o concl) ty_ABS_def

(* ======================= *)
(*       L E M M A S       *)
(* ======================= *)

        val r'tm = mk_var{Name="r'", Ty=ty}
        val r'cl = mk_comb{Rator=REL, Rand=r'tm}
        val rr'cl = mk_comb{Rator=rcl, Rand=r'tm}
        val req = mk_eq{lhs=rcl, rhs=r'cl}

        val atm = mk_var{Name="a", Ty=nty}
        val ABS_REP = CONJUNCT1 ty_bijections
        val REP_ABS = CONJUNCT2 ty_bijections

        val ty_REP_REL =
            let val th1 = 
                EQ_MP (SYM (SPEC (mk_comb{Rator=cty_REP, Rand=atm}) REP_ABS))
                      (AP_TERM cty_REP (SPEC atm ABS_REP))
            in
                GEN atm (EQ_MP (BETA_CONV (concl th1)) th1)
            end

(* Alternative proof:
        val ty_REP_REL =
            (GEN atm o BETA_RULE o REWRITE_RULE[GSYM REP_ABS]
               o AP_TERM cty_REP o SPEC atm) ABS_REP
*)

        val cty_ABS_11 =
            let val aeq = mk_eq{lhs=mk_comb{Rator=cty_ABS, Rand=rcl},
                                rhs=mk_comb{Rator=cty_ABS, Rand=r'cl}}
                val th1 = AP_TERM cty_REP (ASSUME aeq)
                val th2 = CONJUNCT2 cty_ABS_REP
                val x = mk_var{Name="x", Ty=cty}
                val y = mk_var{Name="y", Ty=cty}
                val th3 = SUBST [x |-> SPEC rtm th2, y |-> SPEC r'tm th2]
                                (mk_eq{lhs=x, rhs=y})
                                th1
                val th4 = DISCH_ALL th3
                val th5 = DISCH_ALL (AP_TERM cty_ABS (ASSUME req))
            in
                GENL[rtm,r'tm] (IMP_ANTISYM_RULE th4 th5)
            end;

(* Alternative proof:
        val cty_ABS_11 = TAC_PROOF(([],
            (--`!r r'. (^cty_ABS (^REL r) = ^cty_ABS (^REL r')) =
                       (^REL r = ^REL r')`--)),
            GEN_TAC THEN GEN_TAC
            THEN EQ_TAC
            THENL
              [ DISCH_THEN (MP_TAC o AP_TERM cty_REP)
                THEN REWRITE_TAC[cty_ABS_REP],

                DISCH_THEN REWRITE_THM
              ])
*)

        val ty_REL_SELECT_REL =
            let val th1 = MP (ISPECL [rcl,rtm] SELECT_AX) (SPEC rtm refl)
                val th2 = SPECL[rtm,#Rand(dest_comb(concl th1))] equiv
            in
                GEN rtm (SYM (EQ_MP th2 th1))
            end;

(* Alternative proof:
        val ty_REL_SELECT_REL =
            (SYM o REWRITE_RULE[equiv])
             (MP (ISPECL [rcl,rtm] SELECT_AX) (SPEC rtm refl))
*)


(* ================================================= *)
(*       Q U O T I E N T   P R O P E R T I E S       *)
(* ================================================= *)

(* Prove the quotient type bijection properties for ABS and REP. *)

        val ABS_REP_tm = (--`^ty_ABS (^ty_REP a)`--)
        val inst = ASSUME (--`^cty_REP a = ^rcl`--)
        val REP_a_tm = mk_comb{Rator=ty_REP, Rand=atm}

        val ty_ABS_REP =
            (GEN atm o
             REWRITE_RULE[ABS_REP] o 
             CHOOSE (rtm, SPEC atm ty_REP_REL) o
             REWRITE_RULE[SYM inst] o
             REWRITE_RULE[ty_REL_SELECT_REL] o
             REWRITE_RULE[inst])
               (REWRITE_CONV[ty_ABS_def,ty_REP_def] ABS_REP_tm)

        val ty_REP_REFL = GEN atm (SPEC REP_a_tm refl)

        val equiv_ty_ABS = TAC_PROOF(([],
            (--`!r r'. ^REL r r' =
                       ^REL r r /\ ^REL r' r' /\ (^ty_ABS r = ^ty_ABS r')`--)),
            GEN_TAC THEN GEN_TAC
            THEN PURE_REWRITE_TAC[EQT_INTRO (SPEC rtm refl)]
            THEN REWRITE_TAC[ty_ABS_def]
            THEN REWRITE_TAC[cty_ABS_11]
            THEN CONV_TAC (LAND_CONV (REWR_CONV equiv))
            THEN REFL_TAC)

(* alternative proofs:

            GEN_TAC THEN GEN_TAC
            THEN REWRITE_TAC[GSYM cty_REP_one_one]
            THEN REWRITE_TAC[ty_ABS_def]
            THEN REWRITE_TAC[cty_ABS_REP]
            THEN REWRITE_TAC[equiv])

        val equiv_ty_ABS =
            (GEN rtm o GEN r'tm o SYM o
                 REWRITE_CONV[ty_ABS_def,cty_ABS_11,equiv])
                         (--`^ty_ABS r = ^ty_ABS r'`--)
*)

        val QUOTIENT_thm = REWRITE_RULE[GSYM QUOTIENT_def]
                           (LIST_CONJ [ty_ABS_REP, ty_REP_REFL, equiv_ty_ABS])

    in
       save_thm(tyname^"_QUOTIENT", QUOTIENT_thm)
    end;



(* Equivalence theorems have the form:
     !x y. R x y = (R x = R y)

   Here are routines to create equivalence theorems,
   and to convert them into theorems of
   reflexivity, symmetry, and transitivity.              *)

fun equiv_refl equiv =
    CONJUNCT1 (CONV_RULE (REWR_CONV EQUIV_REFL_SYM_TRANS) equiv)

fun equiv_sym equiv =
    CONJUNCT1 (CONJUNCT2 (CONV_RULE (REWR_CONV EQUIV_REFL_SYM_TRANS) equiv))

fun equiv_trans equiv =
    CONJUNCT2 (CONJUNCT2 (CONV_RULE (REWR_CONV EQUIV_REFL_SYM_TRANS) equiv))

fun refl_sym_trans_equiv refl sym trans =
    CONV_RULE (REWR_CONV (GSYM EQUIV_REFL_SYM_TRANS))
              (CONJ refl (CONJ sym trans))



fun mkfun (ty1, ty2) = mk_type{Tyop="fun", Args=[ty1, ty2]};

val bool_ty = mk_type{Tyop="bool", Args=[]};

fun mkRELty ty = mkfun(ty, mkfun(ty, bool_ty));


fun identity_equiv ty =
    INST_TYPE [{redex=alpha, residue=ty}] IDENTITY_EQUIV;

fun pair_equiv left_EQUIV right_EQUIV =
    MATCH_MP (MATCH_MP PAIR_EQUIV left_EQUIV) right_EQUIV;

fun sum_equiv left_EQUIV right_EQUIV =
    MATCH_MP (MATCH_MP SUM_EQUIV left_EQUIV) right_EQUIV;

fun list_equiv elem_EQUIV =
    MATCH_MP LIST_EQUIV elem_EQUIV;

fun option_equiv elem_EQUIV =
    MATCH_MP OPTION_EQUIV elem_EQUIV;


fun find_base tm = (find_base o #conseq o dest_imp o snd o strip_forall) tm
                   handle _ => tm

fun equiv_type th =
    (#Ty o dest_var o #Bvar o dest_forall o find_base o concl) th
                  handle e => raise HOL_ERR {
                     origin_structure = "quotient",
                     origin_function  = "equiv_type",
                     message ="Invalid structure of equivalence theorem:\n"
                                ^ thm_to_string th ^ "\n"
                  }

fun make_equiv equivs ty =
    let val etys = map equiv_type equivs
        val etys_equivs = zip etys equivs

        fun prim_make_equiv ty =
            tryfind (fn (ety, equiv) =>
                        CAREFUL_INST_TYPE (match_type ety ty) equiv)
                    etys_equivs

     (* val ALL_op_EQUIVs = op_EQUIVs @ [PAIR_EQUIV, SUM_EQUIV,
                                         LIST_EQUIV, OPTION_EQUIV] *)
     (*   val ALL_op_EQUIVs = op_EQUIVs
        val bodies = map (find_base o concl) ALL_op_EQUIVs
        val opRELs = map (rator o rator o lhs o snd o strip_forall) bodies
        val opnams = map (#Tyop o dest_type o hd o #Args o dest_type o type_of)
                         opRELs
        val op_nm_EQUIVs = zip opnams ALL_op_EQUIVs *)

        fun main_make_equiv ty =
               let val {Tyop, Args} = dest_type ty
                   val ths = map main_make_equiv Args
                   val tyop = prim_make_equiv ty
                         (* this may be one of the base equiv theorems,
                            or one of the tyop conditional equiv ths. *)
                         (* may need to move type vars in tyop to genvars,
                            to avoid clashes with type vars in "ths" *)
                   val vs = (map type_vars_in_term o get_ants o concl) tyop
                   val vs = mk_set (flatten vs)
                   val gs = map (fn v => Type.gen_tyvar()) vs
                   val sub = map2 (fn v => fn g => {redex=v,residue=g})
                                        vs gs
                   val tyop' = INST_TYPE sub tyop
               in  foldl (fn (arg,qth) => MATCH_MP qth arg
                                          handle _ => qth)
                         tyop' ths
               end
               handle _ => identity_equiv ty
(*
        fun make_equiv' ty = 
           prim_make_equiv ty
           handle _ =>
           let val {Tyop, Args} = dest_type ty in
             if Args = [] then identity_equiv ty
             else
               let val ths = map make_equiv' Args
               in
                   foldl (fn (arg,imp) => MATCH_MP imp arg handle _ => imp)
                         (assoc Tyop op_nm_EQUIVs)
                         ths
                   handle _ => identity_equiv ty
               end
           end
*)
    in
       main_make_equiv ty
       handle _ =>raise HOL_ERR {
                                   origin_structure = "quotient",
                                   origin_function  = "make_equiv",
                                   message = "Could not form the " ^
                                             "equivalence theorem for " ^
                                             type_to_string ty
                                }
    end;




fun identity_quotient ty =
    INST_TYPE [{redex=alpha, residue=ty}] IDENTITY_QUOTIENT;


fun pair_quotient left_QUOTIENT right_QUOTIENT =
    REWRITE_RULE[PAIR_REL_EQ,PAIR_MAP_I]
     (C_MATCH_MP2 PAIR_QUOTIENT left_QUOTIENT right_QUOTIENT);


fun sum_quotient left_QUOTIENT right_QUOTIENT =
    REWRITE_RULE[SUM_REL_EQ,SUM_MAP_I]
     (C_MATCH_MP2 SUM_QUOTIENT left_QUOTIENT right_QUOTIENT);


fun list_quotient elem_QUOTIENT =
    REWRITE_RULE[LIST_REL_EQ,LIST_MAP_I]
     (C_MATCH_MP LIST_QUOTIENT elem_QUOTIENT);


fun option_quotient base_QUOTIENT =
    REWRITE_RULE[OPTION_REL_EQ,OPTION_MAP_I]
     (C_MATCH_MP OPTION_QUOTIENT base_QUOTIENT);


fun fun_quotient domain_QUOTIENT range_QUOTIENT =
    REWRITE_RULE[FUN_REL_EQ,FUN_MAP_I]
     (C_MATCH_MP2 FUN_QUOTIENT domain_QUOTIENT range_QUOTIENT);





(**)
fun ptm s tm = if !chatting then (print s; print_term tm; print "\n"; tm)
                            else tm;

fun pth s th = if !chatting then (print s; print_thm th; print "\n"; th)
                            else th;
(**)

fun quotient_type th = (hd o tl o #Args o dest_type o type_of
                            o rand o find_base o concl) th
                       handle e => raise HOL_ERR {
                          origin_structure = "quotient",
                          origin_function  = "quotient_type",
                          message ="Invalid structure of quotient theorem:\n"
                                     ^ thm_to_string th ^ "\n"
                       }

fun make_quotient quots ty =
    let val qtys = map quotient_type quots
        fun prim_make_quotient ty =
            tryfind (fn (rty,qth) => CAREFUL_INST_TYPE (match_type rty ty) qth)
                    (zip qtys quots)
        fun main_make_quotient ty =
               let val {Tyop, Args} = dest_type ty
                   val ths = map main_make_quotient Args
               in
(*
                 if Tyop = "fun" then
                     fun_quotient (hd ths) (hd (tl ths))
                 else
*)
                     let val tyop = prim_make_quotient ty
                         (* this may be one of the base quotient theorems,
                            or one of the tyop conditional quotient ths. *)
                         (* may need to move type vars in tyop to genvars,
                            to avoid clashes with type vars in "ths" *)
                         val vs = (map type_vars_in_term o get_ants o concl)
                                   tyop
                         val vs = mk_set (flatten vs)
                         val gs = map (fn v => Type.gen_tyvar()) vs
                         val sub = map2 (fn v => fn g => {redex=v,residue=g})
                                        vs gs
                         val tyop' = INST_TYPE sub tyop
                     in  foldl (fn (arg,qth) => MATCH_MP qth arg
                                                handle _ => qth)
                               tyop' ths
                     end
               end
               handle _ => identity_quotient ty
    in
       main_make_quotient ty
    end;





(*
structure Parse:
datatype fixity = RF of term_grammar.rule_fixity | Prefix | Binder

structure term_grammar:
datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | TruePrefix of int

structure HOLgrammars :
datatype associativity = LEFT | RIGHT | NONASSOC
*)






fun fun_tys fty =
    let val {Tyop, Args} = dest_type fty
        val _ = assert (curry op = "fun") Tyop
        val dty = hd Args
        val rty = hd (tl Args)
    in
        dty :: fun_tys rty
    end
    handle _ => [fty];

fun sub_tys ty =
    let val {Tyop, Args} = dest_type ty
    in
        ty :: flatten (map sub_tys Args)
    end
    handle _ => [ty];

fun dest_cons l = (hd l, tl l);


fun form_abs_rep_functions quot_ths tyops tyop_simps =

  let val args = map (snd o strip_comb o concl) quot_ths
      val RELs = map hd args
      val abss = map (hd o tl) args
      val reps = map (hd o tl o tl) args
      val ratys = map (#Args o dest_type o type_of) abss
      val rtys = map hd ratys
      val atys = map (hd o tl) ratys

(*    val (ABS_REP, ABS11) = split (map (Psyntax.dest_conj o concl) quot_ths)
      val (abss, reps) = split (map ((I ## rator) o Psyntax.dest_comb
                                     o lhs o #Body o dest_forall) ABS_REP)
      val RELs = map (rator o rator o lhs o snd o strip_forall) ABS11
      (* atys are the abstract versions of the types being lifted *)
      val atys = map (#Ty o dest_var o #Bvar o dest_forall) ABS_REP
      (* rtys are the representation versions of the types being lifted *)
      val rtys = map (#Ty o dest_var o #Bvar o dest_forall) ABS11
*)
      val rtys_atys = zip rtys atys
      val rtys_abss = zip rtys abss
      val atys_reps = zip atys reps
      val rtys_RELs = zip rtys RELs
(*      val tyops = tyops @
            [{Tyop="list",   Funop="MAP",        Relop="LIST_REL"},
             {Tyop="prod",   Funop="##",         Relop="###"},
             {Tyop="sum",    Funop="++",         Relop="+++"},
             {Tyop="option", Funop="OPTION_MAP", Relop="OPTION_REL"}] *)

      (* we use Type.match_type, Type.type_subst to match types *)

      fun prim_absty ty = tryfind (fn (rty,aty) =>
                                      type_subst (match_type rty ty) aty)
                                  rtys_atys
                          handle _ => ty

      fun prim_repty ty = tryfind (fn (rty,aty) =>
                                      type_subst (match_type aty ty) rty)
                                  rtys_atys
                          handle _ => ty

      fun absty ty = if is_vartype ty then ty
                     else
                       let val {Tyop, Args} = dest_type ty
                           val Args' = map absty Args
                       in prim_absty (mk_type{Tyop=Tyop, Args=Args'})
                       end

      fun repty ty = if is_vartype ty then ty
                     else
                       let val {Tyop, Args} = dest_type ty
                           val Args' = map repty Args
                       in prim_repty (mk_type{Tyop=Tyop, Args=Args'})
                       end

      fun prim_is_abs_ty ty = (tryfind (C match_type ty) atys; true)
                              handle _ => false

      fun prim_is_rep_ty ty = (tryfind (C match_type ty) rtys; true)
                              handle _ => false

      fun is_abs_ty ty = if is_vartype ty then false
                         else
                           prim_is_abs_ty ty orelse
                           exists is_abs_ty (#Args (dest_type ty))

      fun is_rep_ty ty = if is_vartype ty then false
                         else
                           prim_is_rep_ty ty orelse
                           exists is_rep_ty (#Args (dest_type ty))


      fun get_abs ty =
          let val qth = make_quotient (quot_ths @ tyops) ty
          in (rand o rator o concl o PURE_REWRITE_RULE tyop_simps) qth
          end

      fun get_rep ty =
          let val qth = make_quotient (quot_ths @ tyops) (repty ty)
          in (rand o concl o PURE_REWRITE_RULE tyop_simps) qth
          end

      fun tyREL ty =
          let val qth = make_quotient (quot_ths @ tyops) ty
          in (hd o snd o strip_comb o concl) qth
          end

(*
      fun prim_get_abs ty = tryfind (fn (rty,abs) =>
                                      inst (match_type rty ty) abs)
                                    rtys_abss

      fun prim_get_rep ty = tryfind (fn (aty,rep) =>
                                      inst (match_type aty ty) rep)
                                    atys_reps

      fun mk_term_type tm ty = inst (match_type (type_of tm) ty) tm

      fun assoc_fun tyop [] = raise Match
        | assoc_fun tyop ({Tyop, Funop, Relop}::l) =
              if Tyop = tyop then Funop else assoc_fun tyop l

      fun assoc_rel tyop [] = raise Match
        | assoc_rel tyop ({Tyop, Funop, Relop}::l) =
              if Tyop = tyop then Relop else assoc_rel tyop l

      fun get_abs ty = if not (is_rep_ty ty) then
                             mk_const{Name="I", Ty=(==`:^ty -> ^ty`==)}
                       else
                       prim_get_abs ty
                       handle _ =>
                       let val {Tyop, Args} = dest_type ty
                       in
                         if Tyop = "fun" then
                           let val ty1 = hd Args and ty2 = hd (tl Args)
                               val rep1 = get_rep (absty ty1)
                               and abs2 = get_abs ty2
                           in (--`^rep1 --> ^abs2`--)
                           end
                         else (
                         let val Args' = map get_abs Args
                             val tys = map (fn ty => mkfun(ty, absty ty)) Args
                             val res_ty = mkfun(ty, absty ty)
                             val fty = foldr mkfun res_ty tys
                             val nm = assoc_fun Tyop tyops
                             val opr = mk_const{Name=nm, Ty=fty}
                         in list_mk_comb(opr, Args')
                         end
                         handle _ =>
                             raise HOL_ERR {
                                   origin_structure = "quotient",
                                   origin_function  = "get_abs",
                                   message = "Could not form the " ^
                                             "abstraction function for " ^
                                             type_to_string ty
                             }
                         )
                       end

      and get_rep ty = if not (is_abs_ty ty) then
                             mk_const{Name="I", Ty=(==`:^ty -> ^ty`==)}
                       else
                       prim_get_rep ty
                       handle _ =>
                       let val {Tyop, Args} = dest_type ty
                       in
                         if Tyop = "fun" then
                           let val ty1 = hd Args and ty2 = hd (tl Args)
                               val abs1 = get_abs (repty ty1)
                               and rep2 = get_rep ty2
                           in (--`^abs1 --> ^rep2`--)
                           end
                         else (
                         let val Args' = map get_rep Args
                             val tys = map (fn ty => mkfun(ty, repty ty)) Args
                             val res_ty = mkfun(ty, repty ty)
                             val fty = foldr mkfun res_ty tys
                             val nm = assoc_fun Tyop tyops
                             val opr = mk_const{Name=nm, Ty=fty}
                         in list_mk_comb(opr, Args')
                         end
                         handle _ =>
                             raise HOL_ERR {
                                   origin_structure = "quotient",
                                   origin_function  = "get_rep",
                                   message = "Could not form the " ^
                                             "representation function for " ^
                                             type_to_string ty
                             }
                         )
                       end
*)


      fun mkabs tm = let val ty = type_of tm in
                       if not (is_rep_ty ty) then tm
                       else mk_comb{Rator=get_abs ty, Rand=tm}
                     end

      fun mkrep tm = let val ty = type_of tm in
                       if not (is_abs_ty ty) then tm
                       else mk_comb{Rator=get_rep ty, Rand=tm}
                     end

(*
      fun prim_tyREL ty = tryfind (fn (rty,REL) =>
                                      inst (match_type rty ty) REL)
                                  rtys_RELs

      fun tyREL ty = if not (is_rep_ty ty) then
                             mk_const{Name="=", Ty=mkRELty ty}
                       else
                       prim_tyREL ty
                       handle _ =>
                       let val {Tyop, Args} = dest_type ty
                       in
                         if Tyop = "fun" then
                           let val ty1 = hd Args and ty2 = hd (tl Args)
                               val rep1 = get_rep (absty ty1)
                               and abs2 = get_abs ty2
                           in (--`^rep1 =-> ^abs2`--)
                           end
                         else (
                         let val Args' = map tyREL Args
                             val tys = map mkRELty Args
                             val res_ty = mkRELty ty
                             val fty = foldr mkfun res_ty tys
                             val nm = assoc_rel Tyop tyops
                             val opr = mk_const{Name=nm, Ty=fty}
                         in list_mk_comb(opr, Args')
                         end
                         handle _ =>
                             raise HOL_ERR {
                                   origin_structure = "quotient",
                                   origin_function  = "tyREL",
                                   message = "Could not form the " ^
                                             "equivalence relation for " ^
                                             type_to_string ty
                             }
                         )
                       end
*)

  in
    (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep, mkabs, mkrep, tyREL)
  end;


fun tyop_rec th =
    let fun base tm = (base o #conseq o dest_imp o snd o strip_forall) tm
                      handle _ => tm
        val args = snd (strip_comb (base (concl th)))
        val R = hd args
        val abs = (hd o tl) args
        val rep = (hd o tl o tl) args
        val rty = (hd o #Args o dest_type o type_of) abs
(*
        val {conj1=c1, conj2=c2} = snd (strip_comb (base (concl th)))
        val rty = (#Ty o dest_var o #Bvar o dest_forall) c2
        val R = (rator o rator o lhs o snd o strip_forall) c2
        val decmb = Psyntax.dest_comb
        val (abs,rep) = ((I ## rator) o decmb o lhs o body o rand) c1
*)
        val Tyop = (#Tyop o dest_type) rty
        val Relop = (#Name o dest_const o fst o strip_comb) R
        val Funop = (#Name o dest_const o fst o strip_comb) abs
     in {Tyop=Tyop, Relop=Relop, Funop=Funop}
     end


fun define_quotient_lifted_function quot_ths tyops tyop_simps =
    let
(* no refls *)
        val syms  = map (MATCH_MP QUOTIENT_SYM)   quot_ths
        val trans = map (MATCH_MP QUOTIENT_TRANS) quot_ths
      (*  val equiv_ths = map prove_quotient_equiv quot_ths *)

        val unp_quot_ths = map (REWRITE_RULE[QUOTIENT_def]) quot_ths
        val (ABS_REP, (REP_REFL, ABS11)) = ((I ## unzip) o unzip)
                   (map ((I ## CONJ_PAIR) o CONJ_PAIR) unp_quot_ths)
        val (abss, rep_as) = unzip (map
              (Psyntax.dest_comb o lhs o #Body o dest_forall o concl) ABS_REP)
        val reps = map (#Rator o dest_comb) rep_as
        val RELs = map (hd o snd o strip_comb o concl) quot_ths
        val tys = map (hd o #Args o dest_type o type_of) RELs
        val ntys = map (hd o #Args o dest_type o type_of) reps


        val (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep,
              mkabs, mkrep, tyREL) =
                    form_abs_rep_functions quot_ths tyops tyop_simps;


        fun dest_funtype ty =
          if (mem ty tys)
          then [ty]
          else let val {Tyop=f, Args=lr} = dest_type ty
                   val l = hd lr
                   val r = hd (tl lr)
                   val _ = assert(curry op = "fun") f
                in [l]@(dest_funtype r)
               end
               handle _ => [ty]

        fun eta_funtype (ty1::ty2::[]) =
              if not (is_rep_ty ty1) andalso not (is_rep_ty ty2)
                 then [mk_type{Tyop="fun", Args=[ty1,ty2]}]
                 else [ty1,ty2]
          | eta_funtype (ty::[]) = [ty]
          | eta_funtype ([]) = []
          | eta_funtype (ty::tys) =
              let val tys' = eta_funtype tys in
                if (length tys' < length tys)
                   then eta_funtype(ty::tys')
                   else ty::tys'
              end

        fun reptm ((nty,rep)::tyrs) tm =
              if type_of tm = nty then (--`^rep ^tm`--) else reptm tyrs tm
          | reptm [] tm = tm

        fun abstm ((ty,abs)::tyas) tm =
              if type_of tm = ty then (--`^abs ^tm`--) else abstm tyas tm
          | abstm [] tm = tm

        fun define_fun {def_name, fname, func=tm, fixity} =
          let val tyl = dest_funtype(type_of tm)
              val tyl = eta_funtype tyl
              val ntyl = map absty tyl
              val rty = end_itlist (fn t1 => fn t2 =>
                                      mk_type{Tyop="fun", Args=[t1,t2]}) ntyl
              val args = wargs (Lib.butlast ntyl)
              val rargs = map mkrep args
              val l = list_mk_comb(mk_var{Name=fname, Ty=rty}, args)
              val r = mkabs (list_mk_comb(tm,rargs))
              val def = mk_eq{lhs=l, rhs=r}
              fun defname t =
                let val head = #1 (strip_comb (lhs (#2 (strip_forall t))))
                in #Name (dest_var head handle HOL_ERR _ => dest_const head)
                end
              val nam = defname def
          in
            (* new_gen_definition(def_name, def, fixity) *)

(* The following notes are to explain the treatment of fixities:
structure Parse:
datatype fixity = RF of term_grammar.rule_fixity | Prefix | Binder

structure term_grammar:
datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | TruePrefix of int

structure HOLgrammars :
datatype associativity = LEFT | RIGHT | NONASSOC
*)

            case fixity of
              Prefix =>
                    new_definition(def_name, def)
            | Binder =>
                    new_binder_definition(def_name, def)
            | RF rule_fixity =>
               (case rule_fixity of
                  term_grammar.Infix (associativity, priority) =>
                    Definition.new_definition(def_name, def)
                     before
                    Parse.add_infix(nam, priority, associativity)
                | term_grammar.TruePrefix priority =>
                    Definition.new_definition(def_name, def)
                     before
                    Parse.add_rule{term_name=nam,
                                   fixity=TruePrefix priority,
                                   pp_elements=[TOK nam],
                                   paren_style=OnlyIfNecessary,
                                   block_style=(AroundEachPhrase,
                                                (PP.CONSISTENT,0))}
                | term_grammar.Suffix priority =>
                    Definition.new_definition(def_name, def)
                     before
                    Parse.add_rule{term_name=nam,
                                   fixity=Suffix priority,
                                   pp_elements=[TOK nam],
                                   paren_style=OnlyIfNecessary,
                                   block_style=(AroundEachPhrase,
                                                (PP.CONSISTENT,0))}
                | term_grammar.Closefix =>
                    Definition.new_definition(def_name, def)
                     before
                    Parse.add_rule{term_name=nam,
                                   fixity=Closefix,
                                   pp_elements=[TOK nam],
                                   paren_style=OnlyIfNecessary,
                                   block_style=(AroundEachPhrase,
                                                (PP.CONSISTENT,0))}
               )
          end

(* An example of use:
        val newdefs = map define_fun fnlist
*)

    in
       define_fun
    end;


fun prove_quotient_equiv_rep_one_one QUOTIENT =
    let
   (* Extract the existing type, ty, and the equivalence relation, REL. *)
        val unp_quot_th = (REWRITE_RULE[QUOTIENT_def]) QUOTIENT
        val quot_parts = ((I ## CONJ_PAIR) o CONJ_PAIR) unp_quot_th
        val (ABS_REP, (REP_REFL, REL_ABS)) = quot_parts
        val Rar = (snd o strip_comb o concl) QUOTIENT
        val REL = hd Rar
        val abs = (hd o tl) Rar
        val rep = (hd o tl o tl) Rar
        val ty  = (hd o #Args o dest_type o type_of) REL
        val nty = (hd o #Args o dest_type o type_of) rep
        val pty = (==`:^ty -> ^ty -> bool`==)
        val _ = if type_of REL = pty then () else raise Match

(* Prove the one-to-one and onto properties of REP and ABS. *)

        val equiv_rep_one_one = TAC_PROOF(([],
            (--`!a a'. (^REL (^rep a) = ^REL (^rep a')) = (a = a')`--)),
            GEN_TAC THEN GEN_TAC
            THEN EQ_TAC
            THENL
              [ DISCH_THEN (MP_TAC o C AP_THM ``^rep a'``)
                THEN REWRITE_TAC[REP_REFL]
                THEN ONCE_REWRITE_TAC[REL_ABS]
                THEN REWRITE_TAC[REP_REFL]
                THEN REWRITE_TAC[ABS_REP],

                DISCH_THEN REWRITE_THM
              ])

    in
        equiv_rep_one_one
    end;




(* ====================================================================== *)
(* The following function lifts theorems which deal with values of
   the original types, to similarly structured theorems dealing with
   values of the quotient types.

   However, note that this function is partial, and not all theorems 
   can be lifted by this function, even if the lifted versions are true.  *)
(* ====================================================================== *)

(* example from ~/src/integer/integerScript.sml1 :

val _ = print "Establish type of integers\n";

local
    fun mk_def (d,t,n,f) = {def_name=d, fixity=f, fname=n, func=t}
in
    val [INT_10, INT_ADD_SYM, INT_MUL_SYM,
	 INT_ADD_ASSOC, INT_MUL_ASSOC, INT_LDISTRIB,
	 INT_ADD_LID, INT_MUL_LID, INT_ADD_LINV,
	 INT_LT_TOTAL, INT_LT_REFL, INT_LT_TRANS,
	 INT_LT_LADD_IMP, INT_LT_MUL] =
	define_equivalence_type
	{name = "int", equiv = TINT_EQ_EQUIV,
	 defs = [mk_def ("int_0", Term `tint_0`,     "int_0", Prefix),
		 mk_def ("int_1", Term `tint_1`,     "int_1", Prefix),
		 mk_def ("int_neg",Term `tint_neg`,  "int_neg",   Prefix),
		 mk_def ("int_add",Term `$tint_add`, "int_add",   Infixl 500),
		 mk_def ("int_mul",Term `$tint_mul`, "int_mul",   Infixl 600),
		 mk_def ("int_lt",Term `$tint_lt`,   "int_lt",    Infixr 450)],

	 welldefs = [TINT_NEG_WELLDEF, TINT_LT_WELLDEF,
		     TINT_ADD_WELLDEF, TINT_MUL_WELLDEF],
	 old_thms = ([TINT_10] @
		     (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
		      [TINT_ADD_SYM, TINT_MUL_SYM, TINT_ADD_ASSOC,
		       TINT_MUL_ASSOC, TINT_LDISTRIB]) @
		     [TINT_ADD_LID, TINT_MUL_LID, TINT_ADD_LINV,
		      TINT_LT_TOTAL, TINT_LT_REFL, TINT_LT_TRANS,
		      TINT_LT_ADD, TINT_LT_MUL])}
end;

fun mk_def (d,t,n,f) = {def_name=d, fixity=f, fname=n, func=t}
val tyname = "int";
val equiv = TINT_EQ_EQUIV;
val fnlist =    [mk_def ("int_0",  Term `tint_0`,    "int_0",     Prefix),
		 mk_def ("int_1",  Term `tint_1`,    "int_1",     Prefix),
		 mk_def ("int_neg",Term `tint_neg`,  "int_neg",   Prefix),
		 mk_def ("int_add",Term `$tint_add`, "int_add",   Infixl 500),
		 mk_def ("int_mul",Term `$tint_mul`, "int_mul",   Infixl 600),
		 mk_def ("int_lt", Term `$tint_lt`,  "int_lt",    Infixr 450)];
val welldefs = [TINT_NEG_WELLDEF, TINT_LT_WELLDEF,
		     TINT_ADD_WELLDEF, TINT_MUL_WELLDEF];
val old_thms = ([TINT_10] @
		     (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
		      [TINT_ADD_SYM, TINT_MUL_SYM, TINT_ADD_ASSOC,
		       TINT_MUL_ASSOC, TINT_LDISTRIB]) @
		     [TINT_ADD_LID, TINT_MUL_LID, TINT_ADD_LINV,
		      TINT_LT_TOTAL, TINT_LT_REFL, TINT_LT_TRANS,
		      TINT_LT_ADD, TINT_LT_MUL]);

val quot_ths = 
*)


fun lift_theorem_by_quotients quot_ths equivs tyops tyop_simps newdefs
                              respects polydfs polywfs =
    let
        val map_ths = []

        val refls = map equiv_refl equivs
        val syms  = map (MATCH_MP QUOTIENT_SYM)   quot_ths
        val trans = map (MATCH_MP QUOTIENT_TRANS) quot_ths
        (* val equiv_ths = map prove_quotient_equiv quot_ths *)
        (* val rep_one_one = map prove_quotient_rep_fn_one_one quot_ths *)
        (* val abs_iso_equiv = map prove_quotient_abs_iso_equiv quot_ths *)

        val unp_quot_ths = map (REWRITE_RULE[QUOTIENT_def]) quot_ths
        val quot_parts = map ((I ## CONJ_PAIR) o CONJ_PAIR) unp_quot_ths
        val (ABS_REP, (REP_REFL, ABS11)) = ((I ## unzip) o unzip) quot_parts
        val Rars = map (snd o strip_comb o concl) quot_ths
        val RELs = map hd Rars
        val abss = map (hd o tl) Rars
        val reps = map (hd o tl o tl) Rars
(*
        val (abss, rep_as) = unzip (map
              (Psyntax.dest_comb o lhs o #Body o dest_forall o concl) ABS_REP)
        val reps = map (#Rator o dest_comb) rep_as
        val RELs = map (#Rator o dest_comb o #Rator o dest_comb
                             o lhs o snd o strip_forall o concl) ABS11
*)
        val tys  = map (hd o #Args o dest_type o type_of) RELs
        val ntys = map (hd o #Args o dest_type o type_of) reps
        val tys_quot_ths = zip tys quot_ths;


        val (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep,
              mkabs, mkrep, tyREL) =
                     form_abs_rep_functions quot_ths tyops tyop_simps;


        fun dest_funtype ty =
          if (mem ty tys)
          then [ty]
          else let val {Tyop=f, Args=lr} = dest_type ty
                   val l = hd lr
                   val r = hd (tl lr)
                   val _ = assert(curry op = "fun") f
                in [l]@(dest_funtype r)
               end
               handle _ => [ty]

        fun eta_funtype (ty1::ty2::[]) =
              if not (is_rep_ty ty1) andalso not (is_rep_ty ty2)
                 then [mk_type{Tyop="fun", Args=[ty1,ty2]}]
                 else [ty1,ty2]
          | eta_funtype (ty::[]) = [ty]
          | eta_funtype ([]) = []
          | eta_funtype (ty::tys) =
              let val tys' = eta_funtype tys in
                if (length tys' < length tys)
                   then eta_funtype(ty::tys')
                   else ty::tys'
              end


        val funclist = 
          let fun is_abss tm =
                   (tryfind (fn abs => inst (snd (match_term abs tm)) abs)
                            abss;
                         true)
                   handle _ => false
              fun func def =
                let val tm1 = (rhs o snd o strip_forall o concl) def
                    val tm2 = (#Rator o dest_comb) tm1
                              handle _ => tm1
                    val tm3 = if is_abss tm2 then (#Rand o dest_comb) tm1
                                             else tm1
                in
                    (fst o strip_comb) tm3
                end
          in (map func newdefs)
          end

(* only true now for equivalence relations, not quotient relations: *)
        val EQ_APs =
          let fun prove_EQ_AP (REL,refl) =
                    prove
                      ((--`!p q. (p = q) ==> ^REL p q`--),
                       REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
                       MATCH_ACCEPT_TAC refl)
              val Rs = map (rator o rator o #Body o dest_forall o concl) refls
          in map prove_EQ_AP (zip Rs refls)
          end


        fun MAP_CONJ f = (LIST_CONJ o map f o CONJUNCTS)

        val EQ_WELLDEFs =
          let fun prove_EQ_WELLDEF (REL,(sym,trans)) =
          prove
          ((--`!x1 x2 y1 y2. ^REL x1 x2 /\ ^REL y1 y2 ==>
                             (^REL x1 y1 = ^REL x2 y2)`--),
           REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
           [ ALL_TAC, POP_ASSUM (ASSUME_TAC o MATCH_MP sym) ] THEN
           DISCH_THEN (fn th => POP_ASSUM (MP_TAC o CONJ th)) THEN
           DISCH_THEN (MP_TAC o MATCH_MP trans) THENL
           [ POP_ASSUM (ASSUME_TAC o MATCH_MP sym), ALL_TAC ] THEN
           POP_ASSUM (fn th => DISCH_THEN (MP_TAC o CONJ th)) THEN
           DISCH_THEN (ACCEPT_TAC o MATCH_MP trans))
          in
           map prove_EQ_WELLDEF (zip RELs (zip syms trans))
          end

        fun UNDISCH_CONJ th =
            CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th
            handle _ =>
            UNDISCH th

        fun UNSTRIP th =
            UNDISCH_CONJ th
            handle _ =>
            snd (SPEC_VAR th)

(* The RAISE_ONE_RSP rule raises the order of the given wf theorem by one,
   by decreasing the effective arity of the constant and by increasing
   the order of the relation that relates the left and right sides.
   Fails when order cannot be raised any further, i.e., when arity is 0. *)

        fun RAISE_ONE_RSP th =
          let val (left,right) = ((rand ## I) o Psyntax.dest_comb o concl) th
              val lx = rand left and rx = rand right
              val _ = assert not (lx = rx)
              (* Normal case where lx and rx are different variables *)
              val asm = first (fn asm => rand asm = rx andalso
                                         rand (rator asm) = lx) (hyp th)
              val th1 = GEN lx (GEN rx (DISCH asm th))
          in
              REWRITE_RULE[FUN_REL_EQ]
                 (CONV_RULE (REWR_CONV (GSYM FUN_REL)) th1)
          end
          handle _ =>
          (* We repair the special case where lx and rx are the same variable
             and not of a type being lifted; improper but common user error *)
          let val (left,right) = ((rand ## I) o Psyntax.dest_comb o concl) th
              val lx = rand left and rx = rand right
              val _ = assert (curry op = lx) rx
              val _ = assert (not o is_rep_ty o type_of) rx
              val tm = concl th and asl = hyp th
              val free = mk_set (free_vars tm @ flatten (map free_vars asl))
              val ry = Term.variant free rx
(*
              val R = tyREL (type_of rx)
              val asm = mk_comb{Rator=mk_comb{Rator=R, Rand=lx}, Rand=ry}
*)
              val asm = mk_eq{lhs=lx, rhs=ry}
              val th1 = CONV_RULE (RAND_CONV (RAND_CONV
                                       (REWR_CONV (ASSUME asm)))) th
              val th2 = GEN lx (GEN ry (DISCH asm th1))
          in
              REWRITE_RULE[FUN_REL_EQ]
                 (CONV_RULE (REWR_CONV (GSYM FUN_REL)) th2)
          end

(*
        fun DISCH_ONE th = DISCH (last (hyp th)) th
*)

(* The GEN_DISCH_ONE rule discharges the top assumption from the
   assumption list of the given theorem, and generalizes the 
   three free variables of the assumption, if it was a quotient condition. *)

        fun GEN_DISCH_ONE th =
           let val asm = last (hyp th)
               val vars = snd (strip_comb asm)
           in
               GENL vars (DISCH asm th)
           end

(* The prove_ho_respects rule revises the given (possibly conditional)
   respectfulness theorem "resp" to the highest possible order, which is
   the same as the lowest possible arity.  For most respectfulness theorems
   the result will be of arity 0, i.e., the constant with no arguments,
   related to itself by a higher-order quotient relation.  *)

        fun prove_ho_respects resp =
          let val th1 = repeat UNSTRIP resp
              val th2 = repeat RAISE_ONE_RSP th1
          in
              repeat GEN_DISCH_ONE th2
          end

        val ho_respects = map prove_ho_respects respects
        val ho_polywfs  = map prove_ho_respects polywfs

(*
        val REL_REPs = map (MATCH_MP QUOTIENT_REL_REP) quot_ths

        val REP_BETAs = 
          let fun prove_REP_BETA rep =
            prove
            ((--`!f x:'a. (\f x. ^rep (f x)) f x = ^rep (f x)`--),
             REPEAT GEN_TAC
             THEN BETA_TAC
             THEN REFL_TAC)
          in
            map prove_REP_BETA reps
          end
*)

        fun prove_ALL_HIGHER_DEFs def =
          let
              fun MAKE_LOWER_DEF def =
                let val (vrs,df) = (strip_forall o concl) def
                    val {lhs=l,rhs=r} = dest_eq df
                    val {Tyop,Args} = (dest_type o type_of) l
                    val _ = assert (curry op = "fun") Tyop
                    val ty1 = hd Args
                    val ty1n = (#Tyop o dest_type) ty1
                               handle _ =>
                               String.extract(dest_vartype ty1,1,NONE)
                    val ty1n = if String.size ty1n > 0 then ty1n else "z"
                    val xn = String.substring(ty1n,0,1)
                    val asl = hyp def
                    val free = mk_set (free_vars df @
                                       flatten (map free_vars asl))
                    val x = Term.variant free (mk_var{Name=xn, Ty=ty1})
                    val lx = mk_comb{Rator=l, Rand=x}
                    val rb = if is_abs_ty (type_of r) then rand r else r
                    val rx = mkabs (mk_comb{Rator=rb, Rand=mkrep x})
                    val vrsx = vrs @ [x]
                    val dfx = list_mk_forall(vrsx, mk_eq{lhs=lx, rhs=rx})
                in
                   TAC_PROOF((asl,dfx),
                    REPEAT GEN_TAC
                    THEN CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[def]))
                    THEN REWRITE_TAC[FUN_MAP_THM,I_THM])
                end

              fun MAKE_LOWEST_DEF def =
                MAKE_LOWEST_DEF (MAKE_LOWER_DEF def) handle _ => def

              fun prove_HIGHER_DEF def =
                let val (vrs,df) = (strip_forall o concl) def
                    val {lhs=lhs1, rhs=rhs1} = dest_eq df
                    val lhs' = (#Rator o dest_comb) lhs1
                    val cmb = if is_abs_ty (type_of rhs1)
                                 then (#Rand o dest_comb) rhs1
                                 else rhs1
                    val rhs' = (mkabs o #Rator o dest_comb) cmb
                    val ndf = mk_eq{lhs=lhs', rhs=rhs'}
                    val ndef = list_mk_forall(butlast vrs, ndf)
                in
                   prove
                   (ndef,
                    REPEAT GEN_TAC
                    THEN CONV_TAC FUN_EQ_CONV
                    THEN GEN_TAC
                    THEN TRY (CONV_TAC
                               (RAND_CONV (RATOR_CONV (RATOR_CONV
                                                         (REWR_CONV FUN_MAP)
                                                         THENC BETA_CONV)
                                           THENC BETA_CONV)))
                    THEN CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[def]))
                    THEN REWRITE_TAC([I_THM,FUN_MAP_I] @ tyop_simps))
                end

              fun MAKE_HIGHER_DEFS def =
                def :: MAKE_HIGHER_DEFS (prove_HIGHER_DEF def)
                handle _ => [def]
           in
                MAKE_HIGHER_DEFS (MAKE_LOWEST_DEF def)
           end

        val ADD_HIGHER_DEFS = flatten o (map prove_ALL_HIGHER_DEFs)

        val higher_newdefs = ADD_HIGHER_DEFS newdefs


        fun strip_type ty =
           if is_vartype ty then ([],ty)
           else
           let val {Tyop, Args} = dest_type ty in
              if Tyop = "fun" then
                 (((curry op :: (hd Args)) ## I) o strip_type o hd o tl) Args
              else ([],ty)
           end

        fun argty n ty =
           if n >= 1 then
              let val {Tyop, Args} = dest_type ty in
                 if not(Tyop = "fun") then raise Match
                 else if n = 1 then hd Args
                      else argty (n-1) (hd (tl Args))
              end
           else raise Match

        fun resty n ty =
           if n = 0 then ty
           else if n >= 1 then
              let val {Tyop, Args} = dest_type ty in
                 if not(Tyop = "fun") then raise Match
                 else resty (n-1) (hd (tl Args))
              end
           else raise Match

        fun del_imps tm =
                    if is_imp tm then (del_imps o #conseq o dest_imp) tm
                                 else tm

        fun polydf_name th =
          let val tm = (snd o strip_forall
                            o repeat (#conseq o dest_imp o snd o strip_forall)
                            o concl) th
              val {lhs,rhs} = dest_eq tm
              val a1 = if is_comb lhs then (hd o snd o strip_comb) lhs
                                      else lhs
              fun is_a1 b = (b = a1 orelse (is_comb b andalso rand b = a1))
              val tm1 = if exists is_a1 ((snd o strip_comb) rhs)
                          then rhs
                          else (#Rand o dest_comb) rhs
                        handle _ => (#Rand o dest_comb) rhs
          in (#Name o dest_const o fst o strip_comb) tm1
          end

        val poly_lifted_names =
          map polydf_name polydfs

        fun poly_liftedf opp =
          mem (#Name (dest_const opp)) poly_lifted_names
          handle _ => false

        (* return a list of the polymorphic operators in the term
           which have types being lifted. *)
        fun findops tm =
           if is_abs tm then (findops o #Body o dest_abs) tm
           else if is_comb tm then
              let val (opr, args) = strip_comb tm in
                 (findops opr) @ flatten (map findops args)
              end
           else if is_var tm then []
           else let val {Name=nm, Ty= ty} = dest_const tm
                    val (atys,rty) = strip_type ty
                in if poly_liftedf tm andalso is_rep_ty ty
                   then [tm]
                   else []
                end

        fun findaps tm =
           if is_abs tm then (findaps o #Body o dest_abs) tm
           else if is_comb tm then
              let val (opr, args) = strip_comb tm in
                 (findaps opr) @ flatten (map findaps args)
              end
           else if is_const tm then []
           else let val {Name=nm, Ty= ty} = dest_var tm
                    val (atys,rty) = strip_type ty
                in if not (atys = []) andalso is_rep_ty ty
                   then [ty]
                   else []
                end

        fun findabs tm =
           if is_abs tm then
              let val ty = type_of tm
                  val tys = (findabs o #Body o dest_abs) tm
              in if is_rep_ty ty then ty::tys else tys
              end
           else if is_comb tm then
              let val {Rator=opr, Rand=arg} = dest_comb tm in
                 (findabs opr) @ (findabs arg)
              end
           else []

        val TOP_BETA_RULE = CONV_RULE (TOP_DEPTH_CONV BETA_CONV)



(*
So have a function to lift polymorphic already-defined functions
to operate on lifted types as well, and to deal with these functions
appearing in definitions of theorems being lifted:

It should take as arguments in a list of specifications of each
polymorphic function.  The specification for one polymorphic function
would include

   a. the constant, with as polymorphic a type as possible, 
      using the type variables 'a, 'b, 'c, etc. for the polymorphic types.
      These indicate the relevant quotient types/theorems needed
      in order in the antecedents of the theorem below.

   b. a theorem, stating

      !Ra abs_a rep_a ... Rn abs_n rep_n.

         (* the quotient theorem for type "a": *)
         (!a. abs_a(rep_a a) = a) /\
         (!r r'. Ra r r' ==> (abs_a r = abs_a r')) ==>
         . . .
         (* the quotient theorem for type "n": *)
         (!a. abs_a(rep_a a) = a) /\
         (!r r'. Ra r r' ==> (abs_a r = abs_a r')) ==>

         (* the "definition" of the higher function *)
         (!x1 ... xm. F x1 ... xm = abs_r (F (rep_1 x1) ... (rep_m xm)))
         /\
         (* the "well-formedness" or "respectfulness of the equivalences" *)
         (!x1 x1' ... xm xm'.
           R1 x1 x1' /\ ... /\ Rm xm xm' ==>
           Rr (F x1 ... xm) (F x1' ... xm'))

      Here abs_1, rep_1, R1 correspond to the type of the first argument
      of F, ... abs_m, rep_m, Rm correspond to the type of the m-th
      argument of F, and abs_r, rep_r, Rr correspond to the type of the 
      result of F.  If one of these types is not lifted, then use
      I, I, and $= for that abs, rep, and R.
*)

        fun prim_get_quotient ty =
            tryfind (fn (rty,qth) => CAREFUL_INST_TYPE (match_type rty ty) qth)
                    tys_quot_ths

        val tyops' = tyops @ [LIST_QUOTIENT, OPTION_QUOTIENT,
                              PAIR_QUOTIENT,    SUM_QUOTIENT]

        val tyop_tys = map quotient_type tyops

        val tyop_ty_ths = zip tyop_tys tyops

        fun prim_get_tyop_quotient ty =
            tryfind (fn (rty,qth) => CAREFUL_INST_TYPE (match_type rty ty) qth)
                    tyop_ty_ths

        fun get_quotient ty =
            if not (is_rep_ty ty) then identity_quotient ty
            else
            prim_get_quotient ty
            handle _ =>
            let val {Tyop,Args} = dest_type ty
                val ths = map get_quotient Args
            in
(*
               if Tyop="fun" then fun_quotient (el 1 ths) (el 2 ths)
               else
*)
                  let val tyop = prim_get_tyop_quotient ty
                         (* this may be one of the base quotient theorems,
                            or one of the tyop conditional quotient ths. *)
                         (* may need to move type vars in tyop ants to genvars,
                            to avoid clashes with type vars in "ths" *)
                      val vs = (map type_vars_in_term o get_ants o concl) tyop
                      val vs = mk_set (flatten vs)
                      val gs = map (fn v => Type.gen_tyvar()) vs
                      val sub = map2 (fn v => fn g => {redex=v,residue=g})
                                     vs gs
                      val tyop' = INST_TYPE sub tyop
                  in  foldl (fn (arg,qth) => MATCH_MP qth arg
                                             handle _ => qth)
                            tyop' ths
                  end
               handle _ => identity_quotient ty
            end

        fun resolve_quotient th =
            let val qtm = (#ant o dest_imp o snd o strip_forall o concl) th
                val (Q,Rar) = strip_comb qtm
                val _ = assert (curry op = "QUOTIENT") ((#Name o dest_const) Q)
                val rty = (hd o #Args o dest_type o type_of o hd o tl) Rar
                val qth = get_quotient rty
            in 
               MATCH_MP th qth
            end

        fun dest_QUOTIENT_imp tm =
            let val {ant, conseq} = dest_imp tm
                val (Q,_) = strip_comb ant
                val Qname = #Name (dest_const Q)
                val _ = assert (curry op = "QUOTIENT") Qname
            in
                conseq
            end

        fun get_higher_wf_base th =
            let val tm1 = (concl) th
                val tm2 = repeat (dest_QUOTIENT_imp o snd o strip_forall) tm1
                val tm3 = (snd o strip_forall) tm2
            in  #conseq(dest_imp tm3)
                handle _ => tm3
            end

        fun match_higher_wf th gl =
            let val base = get_higher_wf_base th
                val types = snd (match_term (rand base) (rand gl)
                                 handle _ =>
                                 match_term base gl)
                val ith = CAREFUL_INST_TYPE types th
                val wf = repeat resolve_quotient ith
            in  REWRITE_RULE[FUN_REL_EQ] wf
            end

        fun get_higher_eq_base tm =
            let val tm1 = repeat (dest_QUOTIENT_imp o snd o strip_forall) tm
                val tm2 = (snd o strip_forall) tm1
            in  #lhs(dest_eq tm2)
                handle _ => tm2
            end

        fun match_higher_eq th gl =
            let val base = get_higher_eq_base (concl th)
                val types = snd (match_term base gl)
                val ith = CAREFUL_INST_TYPE types th
                val eq = repeat resolve_quotient ith
            in  eq
            end

        fun HIGHER_RSP_TAC th (asl,gl) =
            let val {Rator=R,Rand=tms1} = (dest_comb o #Rator o dest_comb) gl
                val (opp,args) = strip_comb tms1
                val _ = assert is_rep_ty (type_of opp)
                val wf = match_higher_wf th gl
            in ((MATCH_MP_TAC wf handle _ => MATCH_ACCEPT_TAC wf)
                 THEN REPEAT STRIP_TAC) (asl,gl)
            end

        fun get_higher_df_op tm th =
            let val tm1 = (concl) th
                val tm2 = repeat (#conseq o dest_imp o snd o strip_forall) tm1
                val {lhs=lhs2,rhs=rhs2} = (dest_eq o snd o strip_forall) tm2
                val a1 = if is_comb lhs2 then (hd o snd o strip_comb) lhs2
                                         else lhs2
                fun is_a1 b = (b = a1 orelse (is_comb b andalso rand b = a1))
                val tm3 = if exists is_a1 ((snd o strip_comb) rhs2)
                             then rhs2
                             else (#Rand o dest_comb) rhs2
                          handle _ => (#Rand o dest_comb) rhs2
                val opr = (fst o strip_comb) tm3
                val types = snd (match_term opr tm)
                val ith = CAREFUL_INST_TYPE types th
                (* val df = repeat ((C tryfind quot_ths) o MATCH_MP) ith *)
                val df = repeat resolve_quotient ith
                val df' = REWRITE_RULE[FUN_MAP_I] df
            in  if #Name (dest_const opr) = "I" then df'
                else REWRITE_RULE[I_THM] df'
            end

        fun get_higher_wf_op tm th =
            let val tm1 = (concl) th
                val tm2 = repeat (dest_QUOTIENT_imp o snd o strip_forall) tm1
                val base = (del_imps o snd o strip_forall) tm2
                val opr = (fst o strip_comb o #Rand o dest_comb) base
                val types = snd (match_term opr tm)
                val ith = CAREFUL_INST_TYPE types th
                (* val wf = repeat ((C tryfind quot_ths) o MATCH_MP) ith *)
                val wf = repeat resolve_quotient ith
            in  wf
            end


        fun MK_DEF_OP tm =
          let val {Name=nm, Ty=ty} = dest_const tm
          in
            tryfind (get_higher_df_op tm) polydfs
          end

(*
        fun MK_RSP_OP tm =
          let val {Name=nm, Ty=ty} = dest_const tm
          in
            tryfind (get_higher_wf_op tm) polywfs
          end
*)

        fun LAMBDA_RSP_TAC (asl,gl) =
            let val {Rator=Rf, Rand=g} = dest_comb gl
                val {Rator=R, Rand=f} = dest_comb Rf
                val _ = assert is_abs f
                val _ = assert is_abs g
                val free = mk_set (free_vars f @ flatten (map free_vars asl))
                val x = Term.variant     free  (#Bvar (dest_abs f))
                val y = Term.variant (x::free) (#Bvar (dest_abs g))
                val (Rop, Rargs) = strip_comb R
                val _ = assert (curry op = "===>") (#Name (dest_const Rop))
            in
               (CONV_TAC (REWR_CONV FUN_REL)
                THEN X_GEN_TAC x THEN X_GEN_TAC y THEN DISCH_TAC
                THEN CONV_TAC (LAND_CONV BETA_CONV
                               THENC RAND_CONV BETA_CONV)) (asl,gl)
            end;


(*
        val LAMBDA_ABS_REP_RSP_TAC =
            MATCH_MP_TAC LAMBDA_REP_ABS_RSP
            THEN CONJ_TAC
            THENL
              [ REWRITE_TAC[FUN_MAP_I,I_THM]
                THEN REPEAT CONJ_TAC
                THEN GEN_TAC THEN GEN_TAC
                THEN DISCH_TAC,

                ALL_TAC
              ]
*)

        fun get_higher_wf_lambda tm th =
            let val tm1 = (concl) th
                val tm2 = repeat (dest_QUOTIENT_imp o snd o strip_forall) tm1
                val base = (del_imps o snd o strip_forall) tm2
                val types = snd (match_term base tm)
                val ith = CAREFUL_INST_TYPE types th
                (* val wf = repeat ((C tryfind quot_ths) o MATCH_MP) ith *)
                val wf = repeat resolve_quotient ith
            in  wf
            end

(* No longer!
        val LAMBDA_ABS_REP_RSP_WEAK_TAC : tactic =
            W(MATCH_MP_TAC o
              (C get_higher_wf_lambda LAMBDA_REP_ABS_WEAK_RSP) o snd)
*)

        val FUN_REL_TAC : tactic =
            CONV_TAC (REWR_CONV FUN_REL)
            THEN GEN_TAC THEN GEN_TAC
            THEN DISCH_TAC

        fun CON_FUN_REL_TAC (asl,gl) =
            let val r = rand gl
                val l = rand (rator gl)
                val (opr,args) = strip_comb l
                val _ = assert is_const opr
            in FUN_REL_TAC (asl,gl)
            end

        val EQUIV_RES_ABSTRACT_TAC =
            FIRST (map MATCH_MP_TAC [EQUIV_RES_ABSTRACT_LEFT,
                                     EQUIV_RES_ABSTRACT_RIGHT])
            THEN CONJ_TAC

        fun QUOT_MATCH_MP_TAC th =
            W(MATCH_MP_TAC o (match_higher_wf th) o snd)

        fun QUOT_REWR_CONV th =
            W(REWR_CONV o (match_higher_eq th))

        fun QUOT_REWRITE_CONV thl =
            EVERY_CONV (map (TOP_DEPTH_CONV o QUOT_REWR_CONV) thl)

        fun QUOT_REWRITE_RULE thl = CONV_RULE (QUOT_REWRITE_CONV thl)

        fun QUOT_REWRITE_TAC thl = CONV_TAC (QUOT_REWRITE_CONV thl)

        fun SPEC_UNDISCH_ALL th =
              let val th' = UNDISCH_ALL (SPEC_ALL th)
              in if concl th = concl th' then th
                 else SPEC_UNDISCH_ALL th'
              end

(*
        fun QUOT_HO_REWR_CONV th =
            W(Conv.HO_REWR_CONV o pthm o REWRITE_RULE[I_THM] o pthm
                  o repeat resolve_quotient o pthm o UNDISCH_ALL
                  o HO_PART_MATCH I (SPEC_UNDISCH_ALL th)
                (* o ptm "part_match " *) )

        fun QUOT_HO_REWRITE_CONV thl =
            EVERY_CONV (map (TOP_DEPTH_CONV o QUOT_HO_REWR_CONV) thl)

        fun QUOT_HO_REWRITE_RULE thl = CONV_RULE (QUOT_HO_REWRITE_CONV thl)
*)

        fun APPLY_RSP_TAC (asl,gl) =
            let val {Rator=R,Rand=tms1} = (dest_comb o #Rator o dest_comb) gl
                val {Rator=opp,Rand=args} = dest_comb tms1
                val _ = assert is_rep_ty (type_of opp)
                val wf = match_higher_wf APPLY_RSP gl
            in ((MATCH_MP_TAC wf handle _ => MATCH_ACCEPT_TAC wf)
                 THEN REPEAT STRIP_TAC) (asl,gl)
            end

        val ABSTRACT_RES_ABSTRACT_TAC =
            QUOT_MATCH_MP_TAC ABSTRACT_RES_ABSTRACT ORELSE
            QUOT_MATCH_MP_TAC RES_ABSTRACT_ABSTRACT

(*
        val ABS_REP_RSP_TAC : tactic =
            W(MATCH_MP_TAC o
              (C get_higher_wf_lambda REP_ABS_RSP) o snd)
*)
        val ABS_REP_RSP_TAC : tactic =
             QUOT_MATCH_MP_TAC REP_ABS_RSP


        fun LAMBDA_PRS1 fty =
            let val {Tyop=nm, Args=args} = dest_type fty
                val _ = assert (curry op = "fun") nm
                val aty = hd args
                val xtm = mkabs (mk_var{Name="x", Ty=aty})
                val f = mk_var{Name="f", Ty=absty fty}
                val ftm = mkrep (mk_comb{Rator=f, Rand=xtm})
                val rtm = mkabs (--`\x. ^ftm`--)
            in
              (* (\x. f x) = ^(\x. v(f ^x)) *)
            prove
            ((--`!f.
                  (\x. f x) = ^rtm`--),
            GEN_TAC
            THEN CONV_TAC FUN_EQ_CONV
            THEN GEN_TAC
            THEN REWRITE_TAC[FUN_MAP,FUN_MAP_I,I_THM,PAIR_MAP]
            THEN REPEAT (CHANGED_TAC
                   (CONV_TAC (DEPTH_CONV BETA_CONV)
                    THEN REWRITE_TAC map_ths))
            THEN QUOT_REWRITE_TAC[QUOTIENT_ABS_REP]
            THEN REWRITE_TAC [ETA_AX]
            )
            end;


        fun LAMBDA_PRS fty =
            let val {Tyop=nm, Args=args} = dest_type fty
                val _ = assert (curry op = "fun") nm
                val aty = hd args
                val bty = hd (tl args)
                val cldf = CAREFUL_INST_TYPE[alpha |-> aty, beta |-> bty]
                              quotientTheory.LAMBDA_PRS
                val ldf = repeat resolve_quotient cldf
                val ldf' = PURE_REWRITE_RULE[I_THM] ldf
            in
               ldf'   (* (\x. f x) = ^(\x. v(f ^x)) *)
            end;


        fun APPLIC_PRS fty =
            let val tyl = dest_funtype fty
                val tyl = eta_funtype tyl
                val ntyl = map absty tyl
                val rty = end_itlist (fn t1 => fn t2 =>
                                      mk_type{Tyop="fun", Args=[t1,t2]}) ntyl
                val args = wargs (Lib.butlast ntyl)
                val rargs = map mkrep args
                val f   = mk_var{Name="f", Ty=absty fty}
                val l = list_mk_comb(mk_var{Name="f", Ty=rty}, args)
                val r = mkabs (list_mk_comb(mkrep f,rargs))
                val def = mk_eq{lhs=l, rhs=r}
                val gl = list_mk_forall(f::args, def)
            in
              (* (f x) = ^(v(f) v(x)) *)
            prove
            (gl,
            REPEAT GEN_TAC
            THEN REWRITE_TAC[FUN_MAP,FUN_MAP_I,I_THM,PAIR_MAP]
            THEN REPEAT (CHANGED_TAC
                   (CONV_TAC (DEPTH_CONV BETA_CONV)
                    THEN REWRITE_TAC map_ths))
            THEN QUOT_REWRITE_TAC[QUOTIENT_ABS_REP]
            THEN REWRITE_TAC [ETA_AX]
            )
            end;

        fun MATCH_MP0_TAC th = (MATCH_MP_TAC th
                                handle _ => MATCH_ACCEPT_TAC th)


        (* This critical tactic performs the central task of proving
           the expansion of the given, lower version of the theorem
           into a version with "rep o abs" "oil" injected between
           operator results and their uses.  This oil will be used
           in the collapse of the lower operators into their higher
           versions in subsequent rewriting.  *)

        val R_MK_COMB_TAC = FIRST
          [W(C (curry op THEN) (GEN_TAC THEN CONV_TAC
                (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)) o
             CONV_TAC o X_FUN_EQ_CONV o #Bvar o dest_abs o lhs o snd)
           ,
           ABSTRACT_RES_ABSTRACT_TAC,
           LAMBDA_RSP_TAC,
           FIRST (map HIGHER_RSP_TAC (EQUALS_RSP::ho_polywfs))
           ,
           FIRST (map MATCH_ACCEPT_TAC ho_respects),
           ABS_REP_RSP_TAC, (* before APPLY_RSP_TAC *)
           APPLY_RSP_TAC (* after MATCH_ACCEPT_TAC ho_respects,
                           before MK_COMB_TAC *)
           ,
           REFL_TAC,
           MK_COMB_TAC
           ,
           FIRST_ASSUM MATCH_ACCEPT_TAC
           ,
           FIRST (map MATCH_MP_TAC EQ_APs) (* for REGULARIZE later *)
          ]

(* REPEAT R_MK_COMB_TAC *)

        fun prim_liftedf opp =
          exists (fn func => (match_term func opp; true) handle _ => false)
              funclist

        fun liftedf opp =
          prim_liftedf opp orelse poly_liftedf opp

        fun transconv tm =
          if is_abs tm then
            let val {Bvar=v, Body=t} = dest_abs tm
                val vty = type_of v
                val t' = mk_abs{Bvar=v, Body=transconv t}
            in
              if not (is_rep_ty (type_of tm)) then t'
              else
                 mkrep(mkabs(
                    if not (is_rep_ty vty) then t'
                    else
                      let val v' = mkrep(mkabs(v))
                          val t1 = beta_conv (mk_comb{Rator=t', Rand=v'})
                      in
                          mk_abs{Bvar=v, Body=t1}
                      end))
            end
          else
            let val (opp,tms0) = strip_comb tm
                val tms = map transconv tms0
                val ty = type_of tm
            in
              if (((#Name o dest_const) opp = "respects") handle _ => false)
                   then list_mk_comb(opp, (hd tms0)::(tl tms))
              else if (mem ((#Name o dest_const) opp)
                           ["RES_EXISTS_EQUIV","PSUBSETR"]
                          handle _ => false)
                   then list_mk_comb(opp, (hd tms0)::(tl tms))
              else if (mem ((#Name o dest_const) opp)
                           ["IMAGER"]
                          handle _ => false)
                   then list_mk_comb(opp,
                          (hd tms0)::(hd (tl tms0))::(tl (tl tms)))
              else if (liftedf opp andalso is_rep_ty ty) then
                   mkrep(mkabs(list_mk_comb(opp,tms)))
              else if (is_var opp andalso length tms > 0
                                  andalso is_rep_ty ty) then
                   mkrep(mkabs(list_mk_comb(opp,tms)))
              else if tms = [] then opp
              else list_mk_comb(opp, tms)
            end

        fun TRANSFORM_CONV tm =
          let 
              val teq = mk_eq{lhs=tm, rhs=transconv tm}
              val th = TAC_PROOF (([],teq), REPEAT R_MK_COMB_TAC)
          in
              th
          end
          handle _ =>
              raise HOL_ERR {
                    origin_structure = "quotient",
                    origin_function  = "TRANSFORM_CONV",
                    message = "Could not convert to higher types the term\n" ^
                        term_to_string tm ^ "\n" ^
                        "May be missing a respects or a poly_respects theorem"
                        ^ " for some constant in it."
                   }


        fun regularize tm =
          let val ty = type_of tm
              val regularize_abs = (pairLib.mk_pabs o (I ## regularize)
                                                   o pairLib.dest_pabs)
          in
            (* abstraction *)
            if is_abs tm then
              let val tm1 = regularize_abs tm
                  val (dom,rng) = (dom_rng) ty
              in
                if is_rep_ty dom then
                  (--`RES_ABSTRACT (respects (^(tyREL dom))) ^tm1`--)
                  handle _ => tm1
                else tm1
              end
            (* respects(R): *)
            else if (#Name (dest_const (rator tm)) = "respects")
                     handle _ => false
                 then tm
            (* combination *)
            else if is_comb tm then
              let val (opp,args) = strip_comb tm
                (*  val argsr = map regularize args *)
              in
                if is_const opp andalso is_rep_ty (type_of opp) then
                  let val name = #Name (dest_const opp) in
                    if name = "=" then
                      list_mk_comb(tyREL (type_of (hd args)), map regularize args)
                    else if mem name ["!","?","?!"] then
                      let val tm1 = hd args
                          val tm1r = regularize_abs tm1
                          val ty1 = type_of tm1
                          val dom = (fst o dom_rng) ty1
                          val domREL = tyREL dom
                          val res = (--`respects(^domREL)`--)
                      in
                        if name = "!" then
                             (--`RES_FORALL ^res ^tm1r`--)
                        else if name = "?" then
                             (--`RES_EXISTS ^res ^tm1r`--)
                        else if name = "?!" then
                             (--`RES_EXISTS_EQUIV ^domREL ^tm1r`--)
                        else 
                             list_mk_comb(opp, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["SUBSET","PSUBSET"] then
                      let val tm1 = hd args
                          val ty1 = type_of tm1
                          val elemREL = tyREL ty1
                          val res = (--`respects(^elemREL)`--)
                      in
                        if name = "SUBSET" then
                             list_mk_comb(--`SUBSETR ^res`--, map regularize args)
                        else if name = "PSUBSET" then
                             list_mk_comb(--`PSUBSETR ^elemREL`--, map regularize args)
                        else 
                             list_mk_comb(opp, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["IMAGE"] then
                      let val tm1 = hd args
                          val ty1 = type_of tm1
                          val (dom,rng) = dom_rng ty1
                          val domREL = tyREL dom
                          val rngREL = tyREL rng
                      in
                        if name = "IMAGE" then
                             list_mk_comb(--`IMAGER ^domREL ^rngREL`--, map regularize args)
                        else 
                             list_mk_comb(opp, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["RES_FORALL","RES_EXISTS",
                                      "RES_EXISTS_UNIQUE","RES_ABSTRACT"] then
                      if is_comb (hd args) andalso
                         is_const ((rator o hd) args) andalso
                         not (name = "RES_EXISTS_UNIQUE") andalso
                         ((#Name o dest_const o rator o hd) args) = "respects"
                      then
                         list_mk_comb(opp, [hd args,
                                            regularize_abs (hd (tl args)) ])
                      else
                      let val restr = hd args
                          val ropp = (#Name o dest_const o fst o strip_comb)
                                     restr
                          val tm1 = hd (tl args)
                          val tm1r = regularize_abs tm1
                          val ty1 = type_of tm1
                          val dom = (fst o dom_rng) ty1
                          val res = if ropp = "respects" then restr else
                              (--`\z. respects(^(tyREL dom)) z /\ ^restr z`--)
                      in
                        if name = "RES_FORALL" then
                             (--`RES_FORALL ^res ^tm1r`--)
                        else if name = "RES_EXISTS" then
                             (--`RES_EXISTS ^res ^tm1r`--)
                        else if name = "RES_EXISTS_UNIQUE" then
                             (--`RES_EXISTS_EQUIV ^(tyREL dom) ^tm1r`--)
                        else if name = "RES_ABSTRACT" then
                             (--`RES_ABSTRACT ^res ^tm1r`--)
                        else 
                             list_mk_comb(opp, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["RES_EXISTS_EQUIV"] then
(*
                      if is_comb (hd args) andalso
                         is_const ((rator o hd) args) andalso
                         ((#Name o dest_const o rator o hd) args) = "respects"
                      then
*)
                         list_mk_comb(opp, [hd args,
                                         regularize_abs (hd (tl args)) ])
(*
                      else
                      let (*val restr = hd args
                          val ropp = (#Name o dest_const o fst o strip_comb)
                                     restr*)
                          val equiv = hd args
                          val tm1 = hd (tl args)
                          val tm1r = regularize_abs tm1
                          val ty1 = type_of tm1
                          val dom = (fst o dom_rng) ty1
                          (*val res = if ropp = "respects" then restr else
                             (--`\z. respects(^(tyREL dom)) z /\ ^restr z`--)*)
                      in
                        (--`RES_EXISTS_EQUIV ^equiv ^tm1r`--)
                      end
*)
                      handle _ => list_mk_comb(opp, map regularize args)
                    else
                          list_mk_comb(opp, map regularize args)
                  end
                else
                     list_mk_comb(opp, map regularize args)
              end
            else
                 tm
          end


        local
           val erfs  = map (MATCH_MP EQUIV_RES_FORALL) equivs
           val eres  = map (MATCH_MP EQUIV_RES_EXISTS) equivs
           val ereus = map (MATCH_MP EQUIV_RES_EXISTS_UNIQUE) equivs
        in
           val er_rws = erfs @ eres @ ereus
        end


        fun MATCH_EQUIV_TAC equiv =
            MATCH_MP_TAC (MATCH_MP EQUALS_EQUIV_IMPLIES equiv)
            THEN CONJ_TAC
            THEN REPEAT R_MK_COMB_TAC
            THEN NO_TAC


        val REGULARIZE_TAC = FIRST
          [
           W(curry op THEN 
               (FIRST (map MATCH_MP_TAC
                        [FORALL_REGULAR,EXISTS_REGULAR])) o
               X_GEN_TAC o #Bvar o dest_abs o rand o rand o rator o snd),

           W(curry op THEN 
               (FIRST (map MATCH_MP_TAC
                        [RES_FORALL_REGULAR,RES_EXISTS_REGULAR])) o
               X_GEN_TAC o #Bvar o dest_abs o rand o rand o rator o snd)
           THEN DISCH_THEN (ASSUME_TAC o REWRITE_RULE[RESPECTS]),

           W(curry op THEN 
               (MATCH_MP_TAC LEFT_RES_FORALL_REGULAR) o
               X_GEN_TAC o #Bvar o dest_abs o rand o rand o rator o snd)
           THEN CONJ_TAC
           THENL [ REWRITE_TAC[RESPECTS]
                   THEN REPEAT GEN_TAC
                   THEN ASM_REWRITE_TAC[]
                   THEN FIRST (map MATCH_MP_TAC EQ_APs)
                   THEN ASM_REWRITE_TAC[]
                   THEN NO_TAC,

                   CONV_TAC (LAND_CONV BETA_CONV)
                   THEN CONV_TAC (RAND_CONV BETA_CONV)
                 ],

           W(curry op THEN 
               (MATCH_MP_TAC RIGHT_RES_FORALL_REGULAR) o
               X_GEN_TAC o #Bvar o dest_abs o rand o rand o rator o snd)
           THEN DISCH_THEN (ASSUME_TAC o CONV_RULE (REWR_CONV RESPECTS)),

           W(curry op THEN 
               (MATCH_MP_TAC LEFT_RES_EXISTS_REGULAR) o
               X_GEN_TAC o #Bvar o dest_abs o rand o rand o rator o snd)
           THEN DISCH_THEN (ASSUME_TAC o CONV_RULE (REWR_CONV RESPECTS)),

           W(curry op THEN 
               (MATCH_MP_TAC RIGHT_RES_EXISTS_REGULAR) o
               X_GEN_TAC o #Bvar o dest_abs o rand o rand o rator o snd)
           THEN CONJ_TAC
           THENL [ REWRITE_TAC[RESPECTS]
                   THEN REPEAT GEN_TAC
                   THEN ASM_REWRITE_TAC[]
                   THEN FIRST (map MATCH_MP_TAC EQ_APs)
                   THEN ASM_REWRITE_TAC[]
                   THEN NO_TAC,

                   CONV_TAC (LAND_CONV BETA_CONV)
                   THEN CONV_TAC (RAND_CONV BETA_CONV)
                 ],

           MATCH_MP_TAC RES_EXISTS_UNIQUE_REGULAR_SAME
           THEN REWRITE_TAC (map GSYM er_rws)
           THEN REPEAT R_MK_COMB_TAC,

           CONV_TAC (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV),

           DISCH_THEN REWRITE_THM THEN REPEAT R_MK_COMB_TAC THEN NO_TAC,

           FIRST (map MATCH_ACCEPT_TAC EQ_APs),

           FIRST (map MATCH_MP_TAC
                        [EQUALS_IMPLIES,CONJ_IMPLIES,DISJ_IMPLIES,IMP_IMPLIES,
                         NOT_IMPLIES])
           THEN REPEAT CONJ_TAC,

           MATCH_ACCEPT_TAC EQ_IMPLIES,

           FIRST (map MATCH_EQUIV_TAC equivs),

           W(C (curry op THEN) (GEN_TAC THEN CONV_TAC
                (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)) o
             CONV_TAC o X_FUN_EQ_CONV o #Bvar o dest_abs o lhs o snd)
           ,
           CONV_TAC FUN_EQ_CONV THEN GEN_TAC,
           REFL_TAC,
           EQ_TAC,
           MK_COMB_TAC
          ]

        fun REGULARIZE th =
          let 
              val tm = concl th
              val rmp = mk_imp{ant=tm, conseq=regularize tm}
              val rth = prove(rmp, REWRITE_TAC er_rws
                                   THEN REPEAT REGULARIZE_TAC)
          in
            MP rth th
          end


        fun REGULARIZE_RULE th =
               let val tm = concl th
                   val tm' = regularize tm
               in
                  if tm = tm' then th
                  else
                    REGULARIZE th
                    handle _ => raise HOL_ERR {
                         origin_structure = "quotient",
                         origin_function  = "REGULARIZE",
                         message = "Could not lift the irregular theorem\n" ^
                             thm_to_string th ^ "\n" ^
                             "May try proving and then lifting\n" ^
                             term_to_string tm'
                   }
               end

        fun check_high tm =
            (if is_comb tm andalso is_const (rator tm)
                andalso #Name (dest_const (rator tm)) = "respects"
                    then ()
             else if is_abs tm then check_high (#Body (dest_abs tm))
             else if is_comb tm then
                    let val (opp,args) = strip_comb tm
                        val _ = map check_high args
                        (* val _ = check_high opp *)
                    in () end
             else ();
             if is_rep_ty (type_of tm) then
                   raise HOL_ERR {
                         origin_structure = "quotient",
                         origin_function  = "check_high",
                         message = "Could not lift the term " ^
                             term_to_string tm ^ "\n" ^
                             "May be missing a constant to be lifted, " ^
                             "or a poly_preserves theorem."
                   }
             else ()
            )
            

        fun CHECK_HIGH th = (check_high (concl th); th)

        fun RENAME_ABS_CONV name tm =
            let val ty = (#Ty o dest_var o #Bvar o dest_abs) tm
                val x = mk_var{Name=name, Ty=ty}
            in ALPHA_CONV x tm
            end

        fun HO_PURE_REWRITE_CONV ths tm =
            (CHANGED_CONV (Ho_Rewrite.GEN_REWRITE_CONV I ths) THENC
             (if is_abs (rand tm) then
                let val name = (#Name o dest_var o #Bvar o dest_abs o rand) tm
                in
                   RENAME_ABS_CONV name
                end
              else ALL_CONV)) tm

        val REPAIRED_HO_PURE_REWRITE_RULE =
               CONV_RULE o TOP_DEPTH_CONV o HO_PURE_REWRITE_CONV

(*
val tm4a =
    ``(term_REP --> I)
        (\u.
           HEIGHT1
             (term_REP
                (term_ABS
                   (App1 (term_REP (term_ABS t))
                      (term_REP (term_ABS u))))) =
           SUC
             (HEIGHT1 (term_REP (term_ABS t)) MAX
              HEIGHT1 (term_REP (term_ABS u))))``;

Ho_Rewrite.GEN_REWRITE_CONV I LAM_APP_DEFS tm4a
LAM_APP_DEFS_CONV tm4a handle e => Raise e;
REPAIRED_HO_PURE_REWRITE_RULE(LAM_APP_DEFS) th4;
PURE_REWRITE_RULE (map GSYM DEFs) it;
*)


        val LIFT =
              (fn th => let val tm = concl th
                            val ops = mk_set (findops tm)
                            val abs = mk_set (findabs tm)
                            val aps = mk_set (findaps tm)
                            val DEF_OPs = ADD_HIGHER_DEFS (map MK_DEF_OP ops)
                            val DEF_LAMs = map LAMBDA_PRS abs
                            val DEF_APPs = ADD_HIGHER_DEFS (map APPLIC_PRS aps)
                            val LAM_APP_DEFS = map GSYM (DEF_LAMs @ DEF_APPs)
                            val DEFs = DEF_OPs @ higher_newdefs
                        in
                         (CHECK_HIGH o
                          PURE_REWRITE_RULE (map GSYM DEFs) o
                          REPAIRED_HO_PURE_REWRITE_RULE(LAM_APP_DEFS) o
                      (*  Ho_Rewrite.PURE_REWRITE_RULE(LAM_APP_DEFS) o *)
                          QUOT_REWRITE_RULE [GSYM EQUALS_PRS] o
                          CONV_RULE TRANSFORM_CONV) th
                         handle e => raise HOL_ERR {
                                   origin_structure = "quotient",
                                   origin_function  = "LIFT_RULE",
                                   message = "Could not lift the theorem\n" ^
                                       thm_to_string th ^ "\n" ^
                                       exn_to_string e
                                  }
                         end)

        val LIFT_RULE = LIFT o REGULARIZE_RULE o
                        REWRITE_RULE (FUN_REL_EQ :: tyop_simps) o GEN_ALL

    in
       
       LIFT_RULE
    end;
(* end of lift_theorem_by_quotients1 *)


(* Returns a list of types present in the "respects" theorems but  *)
(* not directly mentioned in the "quot_ths" list, but which can be *)
(* built from them.                                                *)

fun enrich_types quot_ths tyops respects =
    let val qtys = map (hd o #Args o dest_type o type_of o hd o tl
                            o snd o strip_comb o concl) quot_ths
        fun resp_ty rth =
            let val body = (snd o strip_forall o concl) rth
                val base = (#conseq o dest_imp) body handle _ => body
            in (#Ty o dest_const o fst o strip_comb o #Rand o dest_comb) base
            end
        (* Checks there is a substitution theta s.t. ty2 theta = ty1: *)
        fun test ty1 ty2 = (match_type ty2 ty1; true) handle _ => false
        fun tintersect [] tys2 = []
          | tintersect (ty::tys) tys2 =
               if exists (test ty) tys2 then ty::tintersect tys tys2
                                        else     tintersect tys tys2
        fun tsubtract [] tys2 = []
          | tsubtract (ty::tys) tys2 =
               if exists (test ty) tys2 then     tsubtract tys tys2
                                        else ty::tsubtract tys tys2
        val rbods = map (snd o strip_forall o concl) respects
        val atys = mk_set (flatten (map (fun_tys o resp_ty) respects))
        val ltys = filter (fn ty =>
                           not (null (tintersect (sub_tys ty) qtys))) atys
        val natys = tsubtract ltys qtys
        val nstys = filter (fn ty =>
                           not (null (tintersect (sub_tys ty) qtys)))
                        (flatten (map sub_tys natys))
        val ntys = mk_set (tsubtract nstys qtys)
(*    val quot_ths' = quot_ths @ map (make_quotient (quot_ths @ tyops)) ntys *)
    in
        ntys
    end;





fun define_quotient_types_rule {types, defs,
                                tyop_equivs, tyop_quotients, tyop_simps,
                                respects, poly_preserves, poly_respects} =
  let
      val equivs = map #equiv (filter (not o is_partial_equiv o #equiv) types)

      fun print_thm' th = if !chatting then (print_thm th; print "\n"; th)
                                       else th
      val quotients = map (fn {name, equiv} =>
            define_quotient_type name (name^"_ABS") (name^"_REP") equiv)
                          types
      val _ = if !chatting then print "Quotients:\n" else ()
      val _ = if !chatting then map print_thm' quotients else []

      val fn_defns =
          map (define_quotient_lifted_function
                     quotients tyop_quotients tyop_simps) defs
      val _ = if !chatting then print "\nDefinitions:\n" else ()
      val _ = if !chatting then map print_thm' fn_defns else []

      val ntys = enrich_types quotients tyop_quotients respects
      val equivs = equivs @ map (make_equiv (equivs @ tyop_equivs)) ntys
      val quotients =
          quotients @ map (make_quotient (quotients @ tyop_quotients)) ntys

      val LIFT_RULE =
             lift_theorem_by_quotients quotients equivs
                                       tyop_quotients tyop_simps
                                       fn_defns
                                       respects poly_preserves poly_respects
             handle e => Raise e
  in
    LIFT_RULE
  end;



fun define_quotient_types {types, defs, tyop_equivs, tyop_quotients,tyop_simps,
                           respects, poly_preserves, poly_respects, old_thms} =
  let fun print_thm' th = if !chatting then (print_thm th; print "\n"; th)
                                       else th

      val LIFT_RULE =
          define_quotient_types_rule
              {types=types,
               defs=defs,
               tyop_equivs=tyop_equivs,
               tyop_quotients=tyop_quotients,
               tyop_simps=tyop_simps,
               respects=respects,
               poly_preserves=poly_preserves, poly_respects=poly_respects}

      val _ = if !chatting then print "\nLifted theorems:\n" else ()
      val new_thms = map (print_thm' o LIFT_RULE)
                         old_thms   handle e => Raise e
  in
    new_thms
  end;


(*
fun define_quotient_types {types, defs, tyop_equivs, tyop_quotients,
                           respects, poly_preserves, poly_respects, old_thms} =
  let
      val equivs = map #equiv (filter (not o is_partial_equiv o #equiv) types)

      fun print_thm' th = if !chatting then (print_thm th; print "\n"; th)
                                       else th
      val quotients = map (fn {name, equiv} =>
            define_quotient_type name (name^"_ABS") (name^"_REP") equiv)
                          types
      val _ = if !chatting then print "Quotients:\n" else ()
      val _ = if !chatting then map print_thm' quotients else []

      val fn_defns =
          map (define_quotient_lifted_function
                     quotients tyop_quotients tyop_simps) defs
      val _ = if !chatting then print "\nDefinitions:\n" else ()
      val _ = if !chatting then map print_thm' fn_defns else []

      val ntys = enrich_types quotients tyop_quotients respects
      val equivs = equivs @ map (make_equiv (equivs @ tyop_equivs)) ntys
      val quotients =
          quotients @ map (make_quotient (quotients @ tyop_quotients)) ntys

      val LIFT_RULE =
             lift_theorem_by_quotients quotients equivs tyop_quotients fn_defns
                                       respects poly_preserves poly_respects
             handle e => Raise e
      val _ = if !chatting then print "\nLifted theorems:\n" else ()
      val new_thms = map (print_thm' o LIFT_RULE)
                         old_thms   handle e => Raise e
  in
    new_thms
  end;
*)


fun define_equivalence_type {name, equiv, defs, welldefs, old_thms} =
    define_quotient_types {types=[{name=name, equiv=equiv}],
                           defs=defs,
                           tyop_equivs=[],
                           tyop_quotients=[FUN_QUOTIENT],
                           tyop_simps=[FUN_REL_EQ,FUN_MAP_I],
                           respects=welldefs,
                           poly_preserves=[FORALL_PRS,EXISTS_PRS],
                           poly_respects=[RES_FORALL_RSP,RES_EXISTS_RSP],
                           old_thms=old_thms};



end;  (* of structure quotient *)
