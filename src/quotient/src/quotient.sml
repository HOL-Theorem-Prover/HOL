(* ===================================================================== *)
(*                                                                       *)
(* FILE          : quotient.sml                                          *)
(* VERSION       : 2.2                                                   *)
(* DESCRIPTION   : Functions for creating a quotient type.               *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : April 15, 2005                                        *)
(* COPYRIGHT     : Copyright (c) 2005 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


(* ===================================================================== *)
(*            Q U O T I E N T   T Y P E S   D E F I N E D                *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* This file defines the function "define_quotient_types", which takes   *)
(* one or more existing types with partial equivalence relations defined *)
(* on them, and creates new types which are isomorphic to the            *)
(* equivalence classes of the old types.                                 *)
(*                                                                       *)
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
open quotient_listTheory;
open quotient_pairTheory;
open quotient_sumTheory;
open quotient_optionTheory;
open Rsyntax;

structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars(quotient_option_grammars)
  fun == q _ = Type q
  fun -- q _ = Term q
end
open Parse


(* In interactive sessions, omit the chatting section below. *)

val chatting = ref false;  (* When chatting is false,
                                 gives no output of lifting.
                              When chatting is true, then
                                 every type, constant, and theorem lifted
                                 is printed. *)

val _ = register_btrace("quotient", chatting);

(* End of chatting section. *)


val caching = ref true; (* should be pure efficiency gain *)


structure Map = Redblackmap

(* Redblackmap has the same signature as Binarymap. *)

val quotient_cache = ref ((Map.mkDict Type.compare) :(hol_type, thm) Map.dict);

val hits = ref 0;
val misses = ref 0;

fun reset_cache () =
      (quotient_cache := (Map.mkDict Type.compare : (hol_type, thm)Map.dict);
       hits := 0; misses := 0)

fun list_cache () = (if !chatting andalso !caching then (
                     print (    "Hits = " ^ Int.toString (!hits) ^
                            ", Misses = " ^ Int.toString (!misses) ^
                            ", Cache size = " ^
                             Int.toString (Map.numItems (!quotient_cache))
                              ^ "\n"))
                     else ();
                     Map.listItems (!quotient_cache))



local
     val tm = Term `!P:'a list -> bool.
                       P [] /\ (!t. P t ==> !x. P (x::t)) ==> !l. P l`
     val eq = Thm.ALPHA (concl listTheory.list_induction) tm
     val list_induction' = EQ_MP eq listTheory.list_induction
in
val LIST_INDUCT_TAC =INDUCT_THEN list_induction' ASSUME_TAC
end;

fun del_imps tm = if is_imp tm then (del_imps o #conseq o dest_imp) tm
                               else tm;

fun get_ants tm =
    let val {ant,conseq} = (dest_imp o snd o strip_forall) tm
    in
        ant :: get_ants conseq
    end
    handle _ => []

fun GEN_QUOT_TYVARS th =
    (* need to move type vars in tyop ants to genvars,
       to avoid clashes with type vars external to "th" *)
    let val ants = get_ants (concl th)
        val vs = mk_set (flatten (map type_vars_in_term ants))
        val sub = map (fn v => (v |-> Type.gen_tyvar())) vs
    in INST_TYPE sub th
    end

fun CAREFUL_INST_TYPE sub th =
(* e.g., sub = [{redex = ``:'a``, residue = ``:'a term1``},
                {redex = ``:'c``, residue = ``:'b``}] :
                {redex : hol_type, residue : hol_type} list *)
(* e.g., sub = [{redex = ``:'b`, residue = ``:'a term1``}] :
                {redex : hol_type, residue : hol_type} list *)
   let val tyvars = type_varsl (map #residue sub)
       val redexs = map #redex sub
       val (asl,con) = dest_thm th
       val th_tyvars = U (map type_vars_in_term (con::asl))
       val old = subtract (intersect tyvars th_tyvars) redexs
       val newsub = map (fn v => (v |-> gen_tyvar())) old
   in
       INST_TYPE (sub @ newsub) th
   end;


fun C_MATCH_MP imp th =
    let val imp1 = GEN_QUOT_TYVARS imp
        val ant = (#ant o dest_imp o snd o strip_forall o concl) imp1
        val subj = (snd o strip_forall o concl) th
        val (_, ty_sub) = match_term ant subj
        val imp' = (*CAREFUL_*)INST_TYPE ty_sub imp1
    in
        MATCH_MP imp' th
    end;

fun C_MATCH_MP2 imp th1 th2 =
    let val imp1 = GEN_QUOT_TYVARS imp
        val {ant=ant1, conseq} = (dest_imp o snd o strip_forall o concl) imp1
        val {ant=ant2, conseq} = (dest_imp o snd o strip_forall) conseq
        val subj1 = (snd o strip_forall o concl) th1
        val subj2 = (snd o strip_forall o concl) th2
        val (_, ty_sub1) = match_term ant1 subj1
        val (_, ty_sub2) = match_term ant2 subj2
        val imp' = (*CAREFUL_*)INST_TYPE (ty_sub1 @ ty_sub2) imp1
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

(* Partial equivalence test case:

val R = --`\x y:'a. Q x /\ Q y /\ (f x = f y :'b)`--;

val FUN_PEQUIV = store_thm
  ("FUN_PEQUIV",
   (--`!(f:'a->'b) Q.
         (?x. Q x) ==>
         (?x. ^R x x) /\
         (!x y. ^R x y =
                ^R x x /\
                ^R y y /\
                (^R x = ^R y))`--),
   PROVE_TAC[]
  );

val NONZERO_EXISTS = store_thm
  ("NONZERO_EXISTS",
   (--`?n. (\n. ~(n = 0)) n`--),
   RW_TAC arith_ss []
  );

val tyname = "mod7";
val abs    = "mod7_ABS";
val rep    = "mod7_REP";
val equiv  = ISPEC ``\n. n MOD 7`` (MATCH_MP FUN_PEQUIV NONZERO_EXISTS);

*)


fun define_partial_quotient_type tyname abs rep equiv =
    let

   (* Extract the existing type, ty, and the equivalence relation, REL. *)
        val equiv = PURE_REWRITE_RULE[PARTIAL_EQUIV_def] equiv
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

(* We will now define the new type, and call it nty here.  We represent
   nty values as (isomorphic to) equivalence classes of ty objects.
   The classes are functions from ty to bool.  However, not all such
   functions are also suitable equivalence classes.  We must restrict
   the type ty->bool by a predicate.

   We take the predicate P to be

     P : (ty -> bool) -> bool
     P = \c. ?r. REL r r /\ (c = REL r)

   That is, consider the sets of ty-values which are REL-equivalent.
   Let each such set be represented by its characteristic function,
   of type ty -> bool.  Then any set of ty-values c is such an equivalence
   set if and only if there is some ty-value, r, which is reflexive on REL
   and the set of its equivalents is the same as that of the given set c.

   If P c, then c is a suitable function to represent an nty.
*)

(* First we show that there is such a set of objects, that the
   predicate P is non-empty.  *)

        val r = Term.variant (free_vars REL) (mk_var{Name="r", Ty=ty})
        val rcl = mk_comb{Rator=REL, Rand=r}
        val Rrr = mk_comb{Rator=rcl, Rand=r}
        val cty = type_of rcl
        val c = Term.variant (free_vars rcl) (mk_var{Name="c", Ty=cty})
        val c' = prim_variant (c::free_vars rcl) c
        val P = (--`\ ^c. ?^r. ^Rrr /\ (^c = ^rcl)`--)
        val x = Term.variant (free_vars P) (mk_var{Name="x", Ty=ty})
        val xcl = mk_comb{Rator=REL, Rand=x}
        val Rxx = mk_comb{Rator=xcl, Rand=x}
        val ty_exists =
            CHOOSE (x,exist)
              (EXISTS (--`?^c. ^P ^c`--, xcl)
                 (EQ_MP (SYM (BETA_CONV (mk_comb{Rator=P, Rand=xcl})))
                        (EXISTS (--`?^r. ^Rrr /\ (^xcl = ^rcl)`--, x)
                           (CONJ (ASSUME Rxx) (REFL xcl)))))
            handle e => Raise e

(* or, alternatively,
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
(* This actually creates the new quotient type.                     *)

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
            THEN PURE_REWRITE_TAC[GSYM REP_ABS]
            THEN EXISTS_TAC r
            THEN ASM_REWRITE_TAC[])

        fun DISCH_EQN th =
            case List.find is_eq (rev (hyp th)) of
              SOME t => DISCH t th
            | NONE => raise Fail "quotient.DISCH_EQN: This should never happen"
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
                val th4 = DISCH_EQN th3
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
             PURE_REWRITE_RULE[ABS_REP] o
             CHOOSE (r, SPEC atm ty_REP_REL) o
             UNDISCH o CONV_RULE (REWR_CONV AND_IMP_INTRO) o
             DISCH_ALL o DISCH_EQN o
             PURE_REWRITE_RULE[SYM inst] o
             PURE_REWRITE_RULE[UNDISCH (SPEC r ty_REL_SELECT_REL)] o
             PURE_REWRITE_RULE[inst])
               (PURE_REWRITE_CONV[ty_ABS_def,ty_REP_def] ABS_REP_tm)

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
            THEN PURE_REWRITE_TAC[ty_ABS_def]
            THEN EQ_TAC
            THEN STRIP_TAC
            THEN REPEAT CONJ_TAC
            THEN TRY (FIRST_ASSUM ACCEPT_TAC)
            THEN FIRST_ASSUM REWRITE_THM
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

(*
val equiv_tm =
    --`!(x:'a) (y:'a). R x y = (R x = R y)`--;

val partial_equiv_tm =
    --`(?(x:'a). R x x) /\
       (!(x:'a) (y:'a). R x y = R x x /\ R y y /\ (R x = R y))`--;
*)

val equiv_tm =
    --`EQUIV (R :'a -> 'a -> bool)`--;

val partial_equiv_tm =
    --`PARTIAL_EQUIV (R :'a -> 'a -> bool)`--;

fun is_equiv th = is_match_term equiv_tm (concl th);

fun is_partial_equiv th = is_match_term partial_equiv_tm (concl th);

fun check_equiv th =
    is_equiv th orelse is_partial_equiv th orelse
         raise HOL_ERR {
                  origin_structure = "quotient",
                  origin_function  = "check_equiv",
                  message = "The following is neither an equivalence nor a partial equivalence theorem:\n" ^
                                       thm_to_string th ^ "\n"
                       }

fun distinct [] = true
  | distinct (x::xs) = not (mem x xs) andalso distinct xs

fun dest_EQUIV_cond tm =
            let val (vrs, body) = strip_forall tm
                val {ant, conseq} = Rsyntax.dest_imp body
                val (E, R) = strip_comb ant
                val Ename = #Name (Rsyntax.dest_const E)
                val _ = assert (curry op = "EQUIV") Ename
                val _ = assert (curry op = 1) (length R)
                val R = el 1 R
                val tau = fst (dom_rng (type_of R))
            in
                (tau,R,conseq)
            end

fun strip_EQUIV_cond tm =
            let val (tau,R,conseq) = dest_EQUIV_cond tm
                val (taus,Rs,conseq) = strip_EQUIV_cond conseq
            in
                (tau::taus, R::Rs, conseq)
            end
            handle _ => ([],[],tm)

fun check_tyop_equiv th =
   let val (taus, Rs, uncond_tm) = strip_EQUIV_cond (concl th)
       val _ = assert (all is_vartype) taus
       val _ = assert distinct taus
       val _ = assert distinct Rs
   in
       Term.free_vars (concl th) = [] andalso
       is_match_term equiv_tm uncond_tm  orelse raise Match
   end
   handle e => raise HOL_ERR {
                  origin_structure = "quotient",
                  origin_function  = "check_tyop_equiv",
                  message = "The following does not have the form of a type quotient extension theorem:\n" ^
                                       thm_to_string th ^ "\n"
                       }


fun dest_QUOTIENT_cond tm =
            let val (vrs, body) = strip_forall tm
                val {ant, conseq} = Rsyntax.dest_imp body
                val (Q, R_abs_rep) = strip_comb ant
                val Qname = #Name (Rsyntax.dest_const Q)
                val _ = assert (curry op = "QUOTIENT") Qname
                val _ = assert (curry op = vrs) R_abs_rep
                val _ = assert (curry op = 3) (length R_abs_rep)
                val R = el 1 R_abs_rep
                val abs = el 2 R_abs_rep
                val rep = el 3 R_abs_rep
                val (tau,ksi) = dom_rng (type_of abs)
            in
                (tau,ksi,R,abs,rep,conseq)
            end

fun strip_QUOTIENT_cond tm =
            let val (tau,ksi,R,abs,rep,conseq) = dest_QUOTIENT_cond tm
                val (taus,ksis,Rs,abss,reps,conseq) = strip_QUOTIENT_cond conseq
            in
                (tau::taus, ksi::ksis, R::Rs, abs::abss, rep::reps, conseq)
            end
            handle _ => ([],[],[],[],[],tm)

val quotient_tm = --`QUOTIENT R (abs:'a -> 'b) rep`--;

fun check_tyop_quotient th =
   let val (taus, ksis, Rs, abss, reps, uncond_tm) =
                                           strip_QUOTIENT_cond (concl th)
       val _ = assert (all is_vartype) (append taus ksis)
       val _ = assert distinct (append taus ksis)
       val _ = assert distinct (append (append Rs abss) reps)
   in
       Term.free_vars (concl th) = [] andalso
       is_match_term quotient_tm uncond_tm  orelse raise Match
   end
   handle e => raise HOL_ERR {
                  origin_structure = "quotient",
                  origin_function  = "check_tyop_quotient",
                  message = "The following does not have the form of a quotient type extension theorem:\n" ^
                                       thm_to_string th ^ "\n"
                       }

fun check_tyop_simp th =
   let val tm = concl th
       val (l,r) = Psyntax.dest_eq tm
       val (name,rty) = Psyntax.dest_const r
       val (cn,args) = strip_comb l
       val _ = assert (all (curry op = name o fst o Psyntax.dest_const)) args
       val atys = map (fst o dom_rng o type_of) args
       val tys = (snd o Psyntax.dest_type o fst o dom_rng) rty
       val _ = assert (curry op = []) (set_diff atys tys)
   in
      true
   end
   handle e => raise HOL_ERR {
                  origin_structure = "quotient",
                  origin_function  = "check_tyop_simp",
                  message = "The following does not have the form of a simplification theorem for either\nrelation extension simplification or map function extension simplification:\n" ^
                                       thm_to_string th ^ "\n"
                       }


fun define_quotient_type tyname abs rep equiv =
    let val equiv = PURE_REWRITE_RULE (map GSYM [EQUIV_def,PARTIAL_EQUIV_def]) equiv
    in
        define_partial_quotient_type tyname abs rep
           (if is_partial_equiv equiv
              then equiv
              else MATCH_MP EQUIV_IMP_PARTIAL_EQUIV equiv)
    end


(* This section is code to construct a quotient from a normal equivalence;
   It is now superceeded by the more general code for a partial equivalance.


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
    end
    end;

End of code for a quotient from a normal equivalence. *)



(* Equivalence theorems have the form:
     EQUIV R
   which can be translated into the equivalent
     !x y. R x y = (R x = R y)

   Here are routines to create equivalence theorems,
   and to convert them into theorems of
   reflexivity, symmetry, and transitivity.              *)

fun equiv_refl equiv =
    CONJUNCT1 (CONV_RULE (REWRITE_CONV[EQUIV_def]
                          THENC REWR_CONV EQUIV_REFL_SYM_TRANS) equiv)

fun equiv_sym equiv =
    CONJUNCT1 (CONJUNCT2 (CONV_RULE (REWRITE_CONV[EQUIV_def]
                          THENC REWR_CONV EQUIV_REFL_SYM_TRANS) equiv))

fun equiv_trans equiv =
    CONJUNCT2 (CONJUNCT2 (CONV_RULE (REWRITE_CONV[EQUIV_def]
                          THENC REWR_CONV EQUIV_REFL_SYM_TRANS) equiv))

fun refl_sym_trans_equiv refl sym trans =
    CONV_RULE (REWR_CONV (GSYM EQUIV_REFL_SYM_TRANS)
               THENC ONCE_REWRITE_CONV[GSYM EQUIV_def] )
              (CONJ refl (CONJ sym trans))


fun mkRELty ty = ty --> ty --> bool;


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
    (fst o dom_rng o type_of o rand o find_base o concl) th
 (*   (#Ty o dest_var o #Bvar o dest_forall o find_base o concl) th *)
                  handle e => raise HOL_ERR {
                     origin_structure = "quotient",
                     origin_function  = "equiv_type",
                     message ="Invalid structure of equivalence theorem:\n"
                                ^ thm_to_string th ^ "\n"
                  }

fun make_equiv equivs tyop_equivs ty =
    let val base_tys = map equiv_type equivs
        val all_equivs = equivs @ tyop_equivs
        val etys = map equiv_type all_equivs
        val etys_equivs = zip etys all_equivs

        fun contains_base ty =
          if is_vartype ty then false
          else if mem ty base_tys then true
               else exists contains_base (#Args (dest_type ty))

        fun prim_make_equiv ty =
            tryfind (fn (ety, equiv) =>
                        CAREFUL_INST_TYPE (match_type ety ty) equiv)
                    etys_equivs

        fun main_make_equiv ty =
               if not (contains_base ty) then identity_equiv ty
               else
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

fun make_hyp_quotient hyp_quots quots tyop_quots ty =
    let val base_tys = map quotient_type quots
        val hqtys = map quotient_type hyp_quots
        val hqty_quots = zip hqtys hyp_quots
        val all_quots = quots @ tyop_quots
        val qtys = map quotient_type all_quots
        val qty_quots = zip qtys all_quots
        fun contains_base ty =
          if is_vartype ty then false
          else if (*mem ty base_tys*) exists (can (match_type ty)) base_tys then true
               else exists contains_base (#Args (dest_type ty))
        fun prim_make_quotient ty =
            assoc ty hqty_quots
            handle e =>
            tryfind (fn (rty,qth) => CAREFUL_INST_TYPE (match_type rty ty) qth)
                    qty_quots
        fun main_make_quotient ty =
              (if is_vartype ty then assoc ty hqty_quots
               else
               if not (contains_base ty) then identity_quotient ty
               else
               let val {Tyop, Args} = dest_type ty
                   val ths = map main_make_quotient Args
               in
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
               end)
               handle _ => identity_quotient ty
    in
       main_make_quotient ty
    end;

fun make_quotient quots tyop_quots ty = make_hyp_quotient [] quots tyop_quots ty


(*
structure Parse:
datatype fixity = RF of term_grammar.rule_fixity | Binder

structure term_grammar:
datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | Prefix of int

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


fun form_hyp_abs_rep_functions hyp_quot_ths quot_ths tyops tyop_simps =

  let val hargs = map (snd o strip_comb o concl) hyp_quot_ths
      val hRELs = map hd hargs
      val habss = map (hd o tl) hargs
      val hreps = map (hd o tl o tl) hargs
      val hratys = map (#Args o dest_type o type_of) habss
      val hrtys = map hd hratys
      val hatys = map (hd o tl) hratys

      val hrtys_atys = zip hrtys hatys
      val hatys_rtys = zip hatys hrtys
      val hrtys_abss = zip hrtys habss
      val hatys_reps = zip hatys hreps
      val hrtys_RELs = zip hrtys hRELs

      val args = map (snd o strip_comb o concl) quot_ths
      val RELs = map hd args
      val abss = map (hd o tl) args
      val reps = map (hd o tl o tl) args
      val ratys = map (#Args o dest_type o type_of) abss
      val rtys = map hd ratys
      val atys = map (hd o tl) ratys

      val rtys_atys = zip rtys atys
      val rtys_abss = zip rtys abss
      val atys_reps = zip atys reps
      val rtys_RELs = zip rtys RELs

      (* we use ML op = to match types for hrtys, hatys *)
      (* we use Type.match_type, Type.type_subst to match types for rtys, atys *)

      fun prim_absty ty = assoc ty hrtys_atys
                          handle _ =>
                          tryfind (fn (rty,aty) =>
                                      type_subst (match_type rty ty) aty)
                                  rtys_atys
                          handle _ => ty

      fun prim_repty ty = assoc ty hatys_rtys
                          handle _ =>
                          tryfind (fn (rty,aty) =>
                                      type_subst (match_type aty ty) rty)
                                  rtys_atys
                          handle _ => ty

      fun absty ty = if is_vartype ty then prim_absty ty
                     else
                       let val {Tyop, Args} = dest_type ty
                           val Args' = map absty Args
                       in prim_absty (mk_type{Tyop=Tyop, Args=Args'})
                       end

      fun repty ty = if is_vartype ty then prim_repty ty
                     else
                       let val {Tyop, Args} = dest_type ty
                           val Args' = map repty Args
                       in prim_repty (mk_type{Tyop=Tyop, Args=Args'})
                       end

      fun prim_is_abs_ty ty = mem ty hatys orelse
                              (tryfind (C match_type ty) atys; true)
                              handle _ => false

      fun prim_is_rep_ty ty = mem ty hrtys orelse
                              (tryfind (C match_type ty) rtys; true)
                              handle _ => false

      fun is_abs_ty ty = if is_vartype ty then mem ty hatys
                         else
                           prim_is_abs_ty ty orelse
                           exists is_abs_ty (#Args (dest_type ty))

      fun is_rep_ty ty = if is_vartype ty then mem ty hrtys
                         else
                           prim_is_rep_ty ty orelse
                           exists is_rep_ty (#Args (dest_type ty))


      fun get_abs ty =
          let val qth = make_hyp_quotient hyp_quot_ths quot_ths tyops ty
          in (rand o rator o concl o PURE_REWRITE_RULE tyop_simps) qth
          end

      fun get_rep ty =
          let val qth = make_hyp_quotient hyp_quot_ths quot_ths tyops (repty ty)
          in (rand o concl o PURE_REWRITE_RULE tyop_simps) qth
          end

      fun tyREL ty =
          let val qth = make_hyp_quotient hyp_quot_ths quot_ths tyops ty
              val qth' = REWRITE_RULE tyop_simps qth
          in (hd o snd o strip_comb o concl) qth'
          end


      fun mkabs tm = let val ty = type_of tm in
                       if not (is_rep_ty ty) then tm
                       else mk_comb{Rator=get_abs ty, Rand=tm}
                     end

      fun mkrep tm = let val ty = type_of tm in
                       if not (is_abs_ty ty) then tm
                       else mk_comb{Rator=get_rep ty, Rand=tm}
                     end

  in
    (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep, mkabs, mkrep, tyREL)
  end;

fun form_abs_rep_functions quot_ths tyops tyop_simps =
    form_hyp_abs_rep_functions [] quot_ths tyops tyop_simps


fun tyop_rec th =
    let val args = snd (strip_comb (find_base (concl th)))
        val R = hd args
        val abs = (hd o tl) args
        val rep = (hd o tl o tl) args
        val rty = (hd o #Args o dest_type o type_of) abs
        val Tyop = (#Tyop o dest_type) rty
        val Relop = (#Name o dest_const o fst o strip_comb) R
        val Funop = (#Name o dest_const o fst o strip_comb) abs
     in {Tyop=Tyop, Relop=Relop, Funop=Funop}
     end


fun check_quotient_ty tys_quot_ths ty =
   if is_vartype ty then ty
   else let val {Tyop, Args} = dest_type ty
         (* val arg_quots = check_quotient_tys Args *)
            fun is_ty_qth (rty,qth) = CAREFUL_INST_TYPE (match_type rty ty) qth
                                      (* (#Tyop(dest_type rty) = Tyop) *)
            val ty_qty = tryfind is_ty_qth tys_quot_ths
                         handle HOL_ERR e =>
                          raise HOL_ERR {
                           origin_structure = "quotient",
                           origin_function  = "check_quotient_ty",
                           message = "Could not lift the type `" ^
                               type_to_string ty ^ "`;\n" ^
                               "Missing quotient extension theorem for type constructor " ^
                               "\"" ^ Tyop ^ "\".\n" ^
                               "Please prove and add to \"tyop_quotients\" inputs for quotient package.\n " (* ^
                               exn_to_string (HOL_ERR e) *)
                          }
         in ty
         end

and check_quotient_tys tys_quot_ths tys = map (check_quotient_ty tys_quot_ths) tys


fun define_quotient_lifted_function quot_ths tyops tyop_simps =
    let
        (* no refls *)
        val syms  = map (MATCH_MP QUOTIENT_SYM)   quot_ths
        val trans = map (MATCH_MP QUOTIENT_TRANS) quot_ths

        val unp_quot_ths = map (PURE_REWRITE_RULE[QUOTIENT_def]) quot_ths
        val (ABS_REP, (REP_REFL, ABS11)) = ((I ## unzip) o unzip)
                   (map ((I ## CONJ_PAIR) o CONJ_PAIR) unp_quot_ths)
        val (abss, rep_as) = unzip (map
              (Psyntax.dest_comb o lhs o #Body o dest_forall o concl) ABS_REP)
        val reps = map (#Rator o dest_comb) rep_as
        val RELs = map (hd o snd o strip_comb o concl) quot_ths
        val tys = map (hd o #Args o dest_type o type_of) RELs
        val ntys = map (hd o #Args o dest_type o type_of) reps

        val tys_quot_ths = zip tys quot_ths
        val tyop_tys = map quotient_type tyops
        val tyop_ty_ths = zip tyop_tys tyops


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

(*
        val _ = print "Currently loaded quotient theorems:\n"
        val _ = map (print_thm o snd) tys_quot_ths
        val _ = print "\n"

        val _ = print "Currently loaded quotient type extension theorems:\n"
        val _ = map (print_thm o snd) tyop_ty_ths
        val _ = print "\n"
*)

(* The function findtys returns a list of the types in the term
   which is being lifted.
*)
        fun findtys tm =
           if is_abs tm then
              let val ty = type_of tm
                  val {Bvar, Body} = dest_abs tm
                  val btys = findtys Body
              in if is_rep_ty ty then insert ty btys else btys
              end
           else if is_comb tm then
              let val (opr, args) = strip_comb tm in
                 (findtys opr) @ flatten (map findtys args)
              end
           else if is_var tm then
                let val {Name=nm, Ty= ty} = dest_var tm
                in if is_rep_ty ty then [ty] else []
                end
           else let val {Name=nm, Ty= ty} = dest_const tm
                in if is_rep_ty ty then [ty] else []
                end

        fun alltys ty =
           if is_vartype ty then [ty]
           else let val {Tyop,Args} = dest_type ty
                    val atys = alltysl Args
                in ty :: atys
                end
        and alltysl [] = []
          | alltysl (ty::tys) = alltys ty @ alltysl tys

              val tys = mk_set (findtys tm)
              val tys = mk_set (filter is_rep_ty (alltysl tys))
              val _ = check_quotient_tys (tys_quot_ths @ tyop_ty_ths) tys
                      handle HOL_ERR e => Raise (HOL_ERR e)
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
datatype fixity = RF of term_grammar.rule_fixity | Binder

structure term_grammar:
datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | Prefix of int

structure HOLgrammars :
datatype associativity = LEFT | RIGHT | NONASSOC
*)

            case fixity of
              NONE =>
                    new_definition(def_name, def)
            | SOME Binder =>
                    new_binder_definition(def_name, def)
            | SOME (RF rule_fixity) =>
               (case rule_fixity of
                  term_grammar.Infix (associativity, priority) =>
                    Definition.new_definition(def_name, def)
                     before
                    Parse.add_infix(nam, priority, associativity)
                | term_grammar.Prefix priority =>
                    Definition.new_definition(def_name, def)
                     before
                    Parse.add_rule{term_name=nam,
                                   fixity=Prefix priority,
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
        val unp_quot_th = (PURE_REWRITE_RULE[QUOTIENT_def]) QUOTIENT
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


fun lift_theorem_by_quotients quot_ths equivs tyop_equivs
                              tyops tyop_simps newdefs
                              respects polydfs polywfs =
    let
        val refls = map equiv_refl equivs
        val syms  = map (MATCH_MP QUOTIENT_SYM)   quot_ths
        val trans = map (MATCH_MP QUOTIENT_TRANS) quot_ths

        val _ = reset_cache()

(* We unpack the quotient theorems into their parts, which consist of
   three properties:
     ABS_REP:    !a. abs (rep a) = a
     REP_REFL:   !a. ?r. R r r /\ (rep a = r)
     ABS11:      !r s. R r s = R r r /\ R s s /\ (abs r = abs s)
*)
        val unp_quot_ths = map (PURE_REWRITE_RULE[QUOTIENT_def]) quot_ths
        val quot_parts = map ((I ## CONJ_PAIR) o CONJ_PAIR) unp_quot_ths
        val (ABS_REP, (REP_REFL, ABS11)) = ((I ## unzip) o unzip) quot_parts

(* From these parts we extract the relations RELs, abstraction functions abss,
   representation functions reps, lower types tys and quotient types ntys.
*)
        val Rars = map (snd o strip_comb o concl) quot_ths
        val RELs = map hd Rars
        val abss = map (hd o tl) Rars
        val reps = map (hd o tl o tl) Rars
        val tys  = map (hd o #Args o dest_type o type_of) RELs
        val ntys = map (hd o #Args o dest_type o type_of) reps
        val tys_quot_ths = zip tys quot_ths;

(* Check that for each quotient theorem in "tyops", the corresponding relation *)
(* and map simplification theorems are present in  "tyop_simps".               *)

        fun check_simp tm = exists (fn th => (Term.match_term tm (concl th); true)
                                             handle HOL_ERR _ => false
                               )   tyop_simps
                            orelse
                          Raise (HOL_ERR {
                           origin_structure = "quotient",
                           origin_function  = "check_simp",
                           message =
                               "Missing quotient simplification theorem:\n" ^
                               with_flag (show_types, true)
                                   thm_to_string (mk_oracle_thm "quotient" ([],tm)) ^ "\n" ^
                               "Please prove and add to \"tyop_simps\" inputs for quotient package.\n "
                          })

        fun check_tyop_simps_present tyop =
            let val (taus,ksis,Rs,abss,reps,conseq) = strip_QUOTIENT_cond (concl tyop)
                val Rar = (snd o strip_comb) conseq
                val REL = hd Rar
                val abs = hd (tl Rar)
                val rep = hd (tl (tl Rar))
                fun strip_comb_list1 [] (tm,args) = (tm,args)
                  | strip_comb_list1 (x::xs) (tm,args) =
                       let val (tm',a) = Term.dest_comb tm
                       in strip_comb_list1 xs (tm', a::args)
                       end
                fun strip_comb_list lst tm = strip_comb_list1 lst (tm,[])
                val (R,Rargs) = strip_comb_list taus REL
                val eqargs = map (fn Rarg => Term.mk_const("=", type_of Rarg)) Rargs
                val REL' = list_mk_comb(R,eqargs)
                val REL_simp = mk_eq{lhs=REL', rhs=Term.mk_const("=", type_of REL')}
                val _ = check_simp REL_simp
                val theta = map (op |->) (zip ksis taus)
                val (amap,aargs) = strip_comb_list taus abs
                val Iaargs = map (fn tau => Term.mk_const("I", tau --> tau)) taus
                val abs' = list_mk_comb(inst theta amap, Iaargs)
                val abs_simp = mk_eq{lhs=abs', rhs=Term.mk_const("I", type_of abs')}
                val _ = check_simp abs_simp
                val (rmap,rargs) = strip_comb_list taus rep
                val Irargs = map (fn tau => Term.mk_const("I", tau --> tau)) taus
                val rep' = list_mk_comb(inst theta rmap,Irargs)
                val rep_simp = mk_eq{lhs=rep', rhs=Term.mk_const("I", type_of rep')}
                val _ = check_simp rep_simp
            in ()
            end

        val _ = map check_tyop_simps_present tyops

(* The following functions are created in relation to the given quotient
   theorems and  type operator quotient theorems:

           is_abs_ty : hol_type -> bool
                       true iff the given type contains a lifted, quotient type
           is_rep_ty : hol_type -> bool
                       true iff the given type contains a type being lifted
           absty     : hol_type -> hol_type
                       lifts the given type to the quotient level
           repty     : hol_type -> hol_type
                       lowers the given tupe from the quotient level
           get_abs   : hol_type -> term
                       returns the abstraction function for the lower type
           get_rep   : hol_type -> term
                       returns the representation function for the lifted type
           mkabs     : term -> term
                       wraps the given term with an application of the
                       abstraction function for its type
           mkrep     : term -> term
                       wraps the given term with an application of the
                       representation function for its type
           tyREL     : hol_type -> term
                       returns the partial equivalence relation for the type
*)
        val (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep,
              mkabs, mkrep, tyREL) =
                     form_abs_rep_functions quot_ths tyops tyop_simps;


(* Determine the constants being lifted. *)

      fun get_deffunc newdef =
        let val (vs,b) = (strip_forall o concl) newdef
            val r = rhs  b
            val c = if is_abs_ty (type_of r) then rand r else r
        in funpow (length vs) rator c
        end

      val funcs = map get_deffunc newdefs
      val newdeffuncs = funcs

      fun match_ty_term ob pat =
        let val (tmtheta,tytheta) = match_term pat ob
            val pat' = inst tytheta pat
        in if pat' = ob then (tmtheta,tytheta)
           else raise raise HOL_ERR {
                               origin_structure = "quotient",
                               origin_function  = "match_ty_term",
                               message = "not a match"
                                    }
        end

(* For each constant being lifted, check that its respectfulness theorem
   is present.  If not, then if the theorem is trivial, create it.
   If it is missing and not trivial, fail with an error message.
*)
      fun add_trivial_respects funcs equivs tyop_equivs =
        let val get_func = fst o strip_comb o rand o rator
                            o find_base o snd o strip_forall o concl
            val rfuncs = map get_func respects
            val missing = (*subtract funcs rfuncs*)
                          filter (fn f => not (exists (can (match_ty_term f)) rfuncs)) funcs
            fun check_not_rep_ty margty = if is_rep_ty margty then raise Match
                                                              else ()

            fun fake_respects tm =
               let val ty = type_of tm
                   val (margtys,mresty) = strip_fun ty
                   val xargs = map (fn (n,ty) =>
                                       mk_var{Name="x"^Int.toString n, Ty=ty})
                                   (enumerate 1 margtys)
                   val yargs = map (fn (n,ty) =>
                                       mk_var{Name="y"^Int.toString n, Ty=ty})
                                   (enumerate 1 margtys)
                   val xyargs = zip xargs yargs
                   val xterm = list_mk_comb(tm,xargs)
                   val yterm = list_mk_comb(tm,yargs)
                   val conc  = list_mk_comb (tyREL (type_of xterm), [xterm,yterm])
                   val hyps  = map (fn (x,y) => list_mk_comb (tyREL (type_of x), [x,y]))
                                   xyargs
                   val body  = if length hyps > 0
                               then mk_imp{ant=list_mk_conj hyps,conseq=conc}
                               else conc
               in
                   List.foldr (fn ((x,y),tm) => list_mk_forall([x,y],tm)) body xyargs
               end

            fun make_missing_respects mfunc =
               let val (margtys,mresty) = strip_fun (type_of mfunc)
                   val _ = map check_not_rep_ty margtys
                   val margs = map (fn (n,ty) =>
                                       mk_var{Name="T"^Int.toString n, Ty=ty})
                                   (enumerate 1 margtys)
                   val mterm = list_mk_comb(mfunc,margs)
                   val mrefl = equiv_refl (make_equiv equivs tyop_equivs mresty)
               in
                   GENL margs (SPEC mterm mrefl)
               end
               handle e => raise HOL_ERR
                            { origin_structure = "quotient",
                              origin_function  = "make_missing_respects",
                              message = "Missing respectfulness theorem for " ^
                                        term_to_string mfunc ^ ".\n" ^
                               with_flag (show_types, true)
                                   thm_to_string (mk_oracle_thm "quotient" ([], fake_respects mfunc)) ^ "\n" ^
                               "Please prove and add to \"respects\" inputs for quotient package.\n "
                            }
        in
           map make_missing_respects missing @ respects
        end

        val all_respects = add_trivial_respects funcs equivs tyop_equivs


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

(* EQ_APs holds theorems that equality implies reflexivity for those
   partial equivalence relations which are reflexive.
   This is only true now for equivalence relations,
   not partial equivalence relations in general:
*)
        val EQ_APs =
          let fun prove_EQ_AP refl =
                let val R = (rator o rator o #Body o dest_forall o concl) refl
                in  prove
                      ((--`!p q. (p = q) ==> ^R p q`--),
                       REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
                       MATCH_ACCEPT_TAC refl)
                end
          in map prove_EQ_AP refls
          end

(*
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
*)

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
              val asm = mk_eq{lhs=lx, rhs=ry}
              val th1 = CONV_RULE (RAND_CONV (RAND_CONV
                                       (REWR_CONV (ASSUME asm)))) th
              val th2 = GEN lx (GEN ry (DISCH asm th1))
          in
              REWRITE_RULE[FUN_REL_EQ]
                 (CONV_RULE (REWR_CONV (GSYM FUN_REL)) th2)
          end


(* The GEN_DISCH_ONE rule expects the top assumption of the hypothesis
   to be a quotient condition.  It discharges the top assumption from the
   hypotheses of the given theorem, and generalizes the three free variables
   of the assumption. *)

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

        val ho_respects = map prove_ho_respects all_respects
        val ho_polywfs  = map prove_ho_respects polywfs


(* The prove_ALL_HIGHER_DEFs function takes a definition theorem def,
   lowers it to the least possible order (higher possible arity), and
   then generates all higher order versions.  All versions generated
   are returned, from the least to the highest order. *)

        fun prove_ALL_HIGHER_DEFs def =
          let

(* The function MAKE_LOWER_DEF converts a given definition theorem to
   the version of one lower order, if possible, and otherwise throws
   an exception. *)

              fun MAKE_LOWER_DEF def =
                let val (vrs,df) = (strip_forall o concl) def
                    val {lhs=l,rhs=r} = dest_eq df
                    val _ = assert is_rep_ty (type_of l)
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

(* The function MAKE_LOWEST_DEF converts a given definition theorem to
   the version of least possible order. *)

              fun MAKE_LOWEST_DEF def =
                MAKE_LOWEST_DEF (MAKE_LOWER_DEF def) handle _ => def

(* The function prove_HIGHER_DEF proves and returns a version of a definition
   theorem of the next higher order, if possible, and otherwise throws
   an exception. *)

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

(* The function MAKE_HIGHER_DEFS proves and returns a list of all versions
   of a given definition theorem of equal or higher order. *)

              fun MAKE_HIGHER_DEFS def =
                def :: MAKE_HIGHER_DEFS (prove_HIGHER_DEF def)
                handle _ => [def]
           in
                MAKE_HIGHER_DEFS (MAKE_LOWEST_DEF def)
           end

        val ADD_HIGHER_DEFS = flatten o (map prove_ALL_HIGHER_DEFs)

        val higher_newdefs = ADD_HIGHER_DEFS newdefs


(* The function strip_type takes a type and returns a pair, consisting of
   a list of the types of the arguments of the function type (or [] if the
   type is not a function type), and the result type of the function type
   (or the type itself if it is not a function type).
*)
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

        fun del_imps tm = snd (strip_imp tm)
(*
                    if is_imp tm then (del_imps o #conseq o dest_imp) tm
                                 else tm
*)

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

(* The function findtys returns a list of the types in the term
   which is being lifted.
*)
        fun findtys tm =
           if is_abs tm then
              let val ty = type_of tm
                  val {Bvar, Body} = dest_abs tm
                  val btys = findtys Body
              in if is_rep_ty ty then insert ty btys else btys
              end
           else if is_comb tm then
              let val (opr, args) = strip_comb tm in
                 (findtys opr) @ flatten (map findtys args)
              end
           else if is_var tm then
                let val {Name=nm, Ty= ty} = dest_var tm
                in if is_rep_ty ty then [ty] else []
                end
           else let val {Name=nm, Ty= ty} = dest_const tm
                in if is_rep_ty ty then [ty] else []
                end

        fun alltys ty =
           if is_vartype ty then [ty]
           else let val {Tyop,Args} = dest_type ty
                    val atys = alltysl Args
                in ty :: atys
                end
        and alltysl [] = []
          | alltysl (ty::tys) = alltys ty @ alltysl tys

        fun findalltys tm = filter is_rep_ty (alltysl (findtys tm))


(* The function findops returns a list of the polymorphic operators in the term
   which have types being lifted.
*)
        val RELnms = map (#Name o dest_const) (filter is_const RELs)
        fun get_tyop_REL tyop =
            let val (taus,ksis,Rs,abss,reps,conseq) = strip_QUOTIENT_cond (concl tyop)
                val Rar = (snd o strip_comb) conseq
                val REL = hd Rar
                val abs = hd (tl Rar)
                val rep = hd (tl (tl Rar))
                fun strip_comb_list1 [] (tm,args) = (tm,args)
                  | strip_comb_list1 (x::xs) (tm,args) =
                       let val (tm',a) = Term.dest_comb tm
                       in strip_comb_list1 xs (tm', a::args)
                       end
                fun strip_comb_list lst tm = strip_comb_list1 lst (tm,[])
                val (R,Rargs) = strip_comb_list taus REL
            in R
            end
        val tyop_RELs = map get_tyop_REL tyops
        val tyop_RELnms = map (#Name o dest_const) tyop_RELs

        fun match_higher_th tm th = (* where th ranges over ho_polywfs *)
            let val (taus,ksis,Rs,abss,reps,base) = strip_QUOTIENT_cond (concl th)
                val opr = fst (strip_comb (rand (rator base)))
            in #Name(dest_const tm) = #Name (dest_const opr)
            end

        fun match_higher_df tm = (* where th ranges over polydfs *)
            mem (#Name(dest_const tm)) poly_lifted_names

        fun orig_const c =
         let val {Name,Thy,...} = dest_thy_const c
         in prim_mk_const{Name=Name,Thy=Thy}
         end

        fun orig_type_of c = type_of (orig_const c)

        fun mk_ksi usedtvs tau =
          let val used = map dest_vartype usedtvs
              val nm = dest_vartype tau
              fun new_name nm =
                 if mem nm used then new_name (nm ^ "1") else nm
          in trace ("Vartype Format Complaint",0) mk_vartype (new_name nm)
          end

        fun mk_ksis taus =
           let fun mk_ksis1 usedtvs [] = []
                 | mk_ksis1 usedtvs (tau::taus) =
                      let val ksi = mk_ksi usedtvs tau
                      in ksi :: mk_ksis1 (ksi :: usedtvs) taus
                      end
           in mk_ksis1 taus taus
           end

        fun base_vartype tyv =
           let val cs = explode (dest_vartype tyv)
               val _ = assert not (length cs = 0)
               val _ = assert (curry op = #"'") (hd cs)
           in implode (tl cs)
           end

        fun mk_R_tm tau = mk_var {Name="R" ^ base_vartype tau,
                                  Ty=  tau --> tau --> bool}

        fun mk_abs_tm (tau,ksi) = mk_var {Name="abs" ^ base_vartype tau,
                                          Ty=  tau --> ksi}

        fun mk_rep_tm (tau,ksi) = mk_var {Name="rep" ^ base_vartype tau,
                                          Ty=  ksi --> tau}

        val quotient_tm = (fst o strip_comb o lhs o snd o strip_forall o concl) QUOTIENT_def

        fun mk_quotient_tm (tau,ksi) = inst [alpha |-> tau, beta |-> ksi] quotient_tm

        fun mk_quotient_phrase ((tau,ksi),(R,abs,rep)) =
            list_mk_comb(mk_quotient_tm(tau,ksi), [R,abs,rep])

        fun fake_poly_respects tm =
           let val otm = orig_const tm
               val ty = type_of otm
               val taus = type_vars ty
               val ksis = mk_ksis taus
               val tau_ksis = zip taus ksis
               val Rs = map mk_R_tm taus
               val abss = map mk_abs_tm tau_ksis
               val reps = map mk_rep_tm tau_ksis
               val R_abs_reps = map (fn (R,(abs,rep)) => (R,abs,rep)) (zip Rs (zip abss reps))
               val quot_phrases = map mk_quotient_phrase (zip tau_ksis R_abs_reps)
               val hyp_quot_ths = map ASSUME quot_phrases
               val (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep,
                     mkabs, mkrep, tyREL) =
                            form_abs_rep_functions (hyp_quot_ths @ quot_ths) tyops tyop_simps

               (* form the base of the fake polymorphic respectfulness theorem *)
               val (margtys,mresty) = strip_fun ty
               val xargs = map (fn (n,ty) =>
                                   mk_var{Name="x"^Int.toString n, Ty=ty})
                               (enumerate 1 margtys)
               val yargs = map (fn (n,ty) =>
                                   mk_var{Name="y"^Int.toString n, Ty=ty})
                               (enumerate 1 margtys)
               val xyargs = zip xargs yargs
               val xterm = list_mk_comb(otm,xargs)
               val yterm = list_mk_comb(otm,yargs)
               val conc  = list_mk_comb (tyREL (type_of xterm), [xterm,yterm])
               val hyps  = map (fn (x,y) => list_mk_comb (tyREL (type_of x), [x,y]))
                               xyargs
               val body  = if length hyps > 0
                           then mk_imp{ant=list_mk_conj hyps,conseq=conc}
                           else conc
               val base = List.foldr (fn ((x,y),tm) => list_mk_forall([x,y],tm)) body xyargs
           in (* Add quotient theorem hypotheses *)
               List.foldr (fn (((R,abs,rep),qtm),tm) =>
                              list_mk_forall([R,abs,rep], mk_imp{ant=qtm, conseq=tm}))
                          base (zip R_abs_reps quot_phrases)
           end

        fun fake_poly_preserves tm =
           let val otm = orig_const tm
               val ty = type_of otm
               val taus = type_vars ty
               val ksis = mk_ksis taus
               val tau_ksis = zip taus ksis
               val Rs = map mk_R_tm taus
               val abss = map mk_abs_tm tau_ksis
               val reps = map mk_rep_tm tau_ksis
               val R_abs_reps = map (fn (R,(abs,rep)) => (R,abs,rep)) (zip Rs (zip abss reps))
               val quot_phrases = map mk_quotient_phrase (zip tau_ksis R_abs_reps)
               val hyp_quot_ths = map ASSUME quot_phrases
               val (is_abs_ty, is_rep_ty, absty, repty, get_abs, get_rep,
                     mkabs, mkrep, tyREL) =
                            form_hyp_abs_rep_functions hyp_quot_ths quot_ths tyops tyop_simps

               (* form the base of the fake polymorphic respectfulness theorem *)
               val (margtys,mresty) = strip_fun ty
               val theta = map (op |->) tau_ksis
               val abs_argtys = map (type_subst theta) margtys
                             (* map absty margtys *)
               val xargs = map (fn (n,ty) => mk_var{Name="x"^Int.toString n, Ty=ty})
                               (enumerate 1 abs_argtys)
               val rep_args = map (fn tm => mkrep tm handle _ => tm) xargs
               val repterm = list_mk_comb(otm, rep_args)
               val absterm = mkabs repterm
               val absdef = list_mk_comb(inst (map (op |->) tau_ksis) otm, xargs)
               val body  = mk_eq{lhs=absdef, rhs=absterm}
               val base = list_mk_forall(xargs, body)
           in (* Add quotient theorem hypotheses *)
               List.foldr (fn (((R,abs,rep),qtm),tm) =>
                              list_mk_forall([R,abs,rep], mk_imp{ant=qtm, conseq=tm}))
                          base (zip R_abs_reps quot_phrases)
           end

        fun findops tm =
           if is_abs tm then (findops o #Body o dest_abs) tm
           else if is_comb tm then
              let val (opr, args) = strip_comb tm in
                 (findops opr) @ flatten (map findops args)
              end
           else if is_var tm then []
           else let val {Name=nm, Ty= ty} = dest_const tm
                    val (atys,rty) = strip_type ty
                    fun err1 () = HOL_ERR {
                           origin_structure = "quotient",
                           origin_function  = "findops",
                           message = "Missing polymorphic respectfulness theorem for `" ^
                                         term_to_string tm ^ "`.\n" ^
                               with_flag (show_types, true)
                                   thm_to_string (mk_oracle_thm "quotient" ([], fake_poly_respects tm)) ^ "\n" ^
                               "Please prove and add to \"poly_respects\" inputs for quotient package.\n "
                        }
                    fun err2 () = HOL_ERR {
                           origin_structure = "quotient",
                           origin_function  = "findops",
                           message = "Missing polymorphic preservation theorem for `" ^
                                         term_to_string tm ^ "`.\n" ^
                               with_flag (show_types, true)
                                   thm_to_string (mk_oracle_thm "quotient" ([], fake_poly_preserves tm)) ^ "\n" ^
                               "Please prove and add to \"poly_preserves\" inputs for quotient package.\n "
                        }
                in if is_rep_ty ty
                   then if mem (#Name(dest_const tm)) ("respects" :: RELnms @ tyop_RELnms)
                                orelse exists (can (match_ty_term tm)) newdeffuncs
                             then []
                        else      if not (exists (match_higher_th tm) ho_polywfs) then raise (err1())
                             else if not (match_higher_df tm) then raise (err2())
                             else if poly_liftedf tm then [tm] else []
                   else []
                end


(* The function findaps returns a list of the types of function variables
   in the term which contain types being lifted.
*)
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

(* The function findabs returns a list of types of abstraction terms
   in the given term which contain types being lifted.
*)
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



(*
So we need a function to lift polymorphic already-defined functions
to operate on lifted types as well, and to deal with these functions
appearing in definitions of theorems being lifted:

It should take as arguments a list of specifications of each
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


(* QUOTIENT THEOREM CREATION AND CACHING SECTION *)

        fun prim_get_quotient ty =
            tryfind (fn (rty,qth) => CAREFUL_INST_TYPE (match_type rty ty) qth)
                    tys_quot_ths

        val tyop_tys = map quotient_type tyops

        val tyop_ty_ths = zip tyop_tys tyops

        fun prim_get_tyop_quotient ty =
            tryfind (fn (rty,qth) => CAREFUL_INST_TYPE (match_type rty ty) qth)
                    tyop_ty_ths

        fun insert_cache ty qth =
            (quotient_cache := Map.insert(!quotient_cache, ty, qth); qth)

(* The function get_quotient produces the quotient theorem for type ty. *)

        fun get_quotient ty =
            if not (is_rep_ty ty) then identity_quotient ty
            else
            prim_get_quotient ty
            handle _ =>
            let val {Tyop,Args} = dest_type ty
                val ths = map get_quotient Args
            in
                  let val tyop = prim_get_tyop_quotient ty
                         (* this may be one of the base quotient theorems,
                            or one of the tyop conditional quotient ths. *)
                         (* may need to move type vars in tyop ants to genvars,
                            to avoid clashes with type vars in "ths" *)
                      val tyop' = GEN_QUOT_TYVARS tyop
                      val qth = foldl (fn (arg,qth) => MATCH_MP qth arg
                                             (**) handle _ => qth (**) )
                                      tyop' ths
                  in qth
                  end
               handle _ => identity_quotient ty
            end

(* We wrap caching around the get_quotient function. *)

        fun get_quotient1 ty =
           if !caching then
              case Map.peek(!quotient_cache, ty) of
                 SOME th => (hits := !hits + 1; th)
               | NONE    => (misses := !misses + 1;
                             insert_cache ty (get_quotient ty))
           else get_quotient ty

        val get_quotient = get_quotient1

(*
        val _ = print "Currently loaded quotient theorems:\n"
        val _ = map (print_thm o snd) tys_quot_ths
        val _ = print "\n"

        val _ = print "Currently loaded quotient type extension theorems:\n"
        val _ = map (print_thm o snd) tyop_ty_ths
        val _ = print "\n"
*)

(* The function resolve_quotient, given a theorem conditioned on a quotient
   theorem, constructs the appropriate quotient theorem for the type present,
   and discharges that condition from the given theorem, returning the
   simplified theorem.  In general, this "resolution" may need to be repeated.
*)
        fun resolve_quotient th =
            let val qtm = (#ant o dest_imp o snd o strip_forall o concl) th
                val (Q,Rar) = strip_comb qtm
                val _ = assert (curry op = "QUOTIENT") ((#Name o dest_const) Q)
                val rty = (hd o #Args o dest_type o type_of o hd o tl) Rar
                val qth = get_quotient rty
            in
               (MATCH_MP th) qth
            end

        fun dest_QUOTIENT_imp tm =
            let val {ant, conseq} = dest_imp tm
                val (Q,_) = strip_comb ant
                val Qname = #Name (dest_const Q)
                val _ = assert (curry op = "QUOTIENT") Qname
            in
                conseq
            end

(* The function get_higher_wf_base strips off all quotient conditions from
   the given theorem, and then regarding it as a respectfulness theorem,
   strips off any remaining antecedent, returning the consequent as the "base".
*)
        fun get_higher_wf_base th =
            let val tm1 = (concl) th
                val tm2 = repeat (dest_QUOTIENT_imp o snd o strip_forall) tm1
                val tm3 = (snd o strip_forall) tm2
            in  #conseq(dest_imp tm3)
                handle _ => tm3
            end

(* The function match_higher_wf matches the base of a given conditional
   respectfulness theorem to a goal, and then uses that match to instantiate
   the types of the respectfulness theorem, which is then "resolved" by
   "resolve_quotient" until all the conditions are gone.  This resolved
   version of the respectfulness theorem is the result returned.
   This function intentionally fails if the rand of the goal does not
   contain a type being lifted.
*)
        fun match_higher_wf th gl =
            let val _ = assert is_rep_ty (type_of (rand gl))
                val th' = (*GEN_QUOT_TYVARS*) th
                val base = get_higher_wf_base th'
                val types = snd (match_term base gl)
                val ith = CAREFUL_INST_TYPE types th'
                val wf = repeat resolve_quotient ith
            in  REWRITE_RULE tyop_simps wf
            end

        fun match_higher_half_wf th gl =
            let val th' = GEN_QUOT_TYVARS th
                val base = get_higher_wf_base th'
                val types = snd (match_term (rand base) (rand gl))
                val ith = (*CAREFUL_*)INST_TYPE types th'
                val wf = repeat resolve_quotient ith
            in  REWRITE_RULE tyop_simps wf
            end


(* The function get_higher_eq_base strips off all quotient conditions from
   the given theorem, and then regarding it as a preservation theorem,
   strips off the right hand side if it is an equality, and returns the
   remaining term as the "base".
*)
        fun get_higher_eq_base tm =
            let val tm1 = repeat (dest_QUOTIENT_imp o snd o strip_forall) tm
                val tm2 = (snd o strip_forall) tm1
            in  #lhs(dest_eq tm2)
                handle _ => tm2
            end

(* The function match_higher_eq matches the base of a given conditional
   preservation theorem to a goal, and then uses that match to instantiate
   the types of the preservation theorem, which is then "resolved" by
   "resolve_quotient" until all the conditions are gone.  This resolved
   version of the preservation theorem is the result returned.
*)
        fun match_higher_eq th gl =
            let val th' = (*GEN_QUOT_TYVARS*) th
                val base = get_higher_eq_base (concl th')
                val types = snd (match_term base gl)
                val ith = CAREFUL_INST_TYPE types th'
                val eq = repeat resolve_quotient ith
            in  eq
            end

(* When applied to a (conditional) respectfulness theorem of the form

    |- !R1 abs1 rep1. QUOTIENT R1 abs1 rep1 ==> ...
       !Rn absn repn. QUOTIENT Rn absn repn ==>
         !x1 y1 ... xn yn. R_i_1 x1 y1 /\ ... /\ R_i_n xn yn ==>
                           R (C x1 ... xn) (C y1 ... yn)

HIGHER_RSP_TAC produces a tactic that reduces a goal whose conclusion
is a substitution and/or type instance of R (C x1 ... xn) (C y1 ... yn)
to a set of n subgoals which are the corresponding instances of
R_i_1 x1 y1 through R_i_n xn yn, IF for that substitution/type instance the
corresponding quotient theorem antecedents are resolvable.
*)
        fun cname tm = #Name (dest_const (fst (strip_comb (rand (rator tm)))))

        fun HIGHER_RSP_TAC th (asl,gl) =
            let val base = get_higher_wf_base th
                val _ = assert (curry op = (cname gl)) (cname base)
                        (* for fast elimination of inapplicable th's *)
                val wf = match_higher_half_wf th gl
            in ((MATCH_ACCEPT_TAC wf handle _ => MATCH_MP_TAC wf)
                 THEN REPEAT CONJ_TAC) (asl,gl)
            end

(* The function get_higher_df_op takes a term which is a polymorphic operator,
   and a conditional preservation theorem for that operator, and attempts to
   instantiate the theorem according to the type of the term, and then
   resolve the preservation theorem by proving and discharging the quotient
   antecedents.  The resulting simplified preservation theorem is returned.

   In the special case where some of the quotient theorem resolvents may
   have been identity quotients, the result may have to be simplified by
   rewriting with theorems FUN_MAP_I and/or I_THM.  Of course, rewriting
   with I_THM is not helpful if the operator being preserved is I itself.
*)

        fun get_higher_df_op tm th =
            let val th' = (*GEN_QUOT_TYVARS*) th
                val tm1 = (concl) th'
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
                val ith = CAREFUL_INST_TYPE types th'
                val df = repeat resolve_quotient ith
                val df' = REWRITE_RULE[FUN_MAP_I] df
            in  if #Name (dest_const opr) = "I" then df'
                else REWRITE_RULE (I_THM::tyop_simps) df'
            end

(* The function MK_DEF_OP takes a term which is a polymorphic operator,
   and searches the list of polymorphic conditional preservation theorems
   for one corresponding to that operator.  If found, the theorem is
   instantiated for the particular type of that term and its quotient
   antecedents are resolved and discharged, leaving a simplified preservation
   theorem which is returned.  If not found, an exception is raised.
*)
        fun MK_DEF_OP tm =
          let val {Name=nm, Ty=ty} = dest_const tm
          in
            tryfind (get_higher_df_op tm) polydfs
          end
          handle e => raise HOL_ERR {
                  origin_structure = "quotient",
                  origin_function  = "MK_DEF_OP",
                  message = "Missing polymorphic preservation theorem for " ^
                                term_to_string tm ^ ".\n"
                }

(* The tactic LAMBDA_RSP_TAC:

        A |- (R1 ===> R2) (\x. f[x]) (\y. g[y])
        =======================================
         A U {R1 x' y'} |- R2 (f[x']) (g[y'])

This tactic simplifies a goal which is a partial equivalence between
two abstractions into a goal where a new hypothesis is added, being
the R1 relation between two new variables x' and y', and the goal is
now the R2 relation between the bodies of the two abstractions, with
x' and y' substituted for their bound variables, respectively.

The variables x' and y' are chosen to be new, but will often be the same
as the abstraction variables x and y, if there are no other conflicts.

The new hypothesis R1 x' y' may be used later to prove subgoals of
R2 (f[x']) (g[y']).
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
                (*val _ = assert (curry op = "===>") (#Name (dest_const Rop))*)
            in
               (CONV_TAC (REWR_CONV FUN_REL)
                THEN X_GEN_TAC x THEN X_GEN_TAC y THEN DISCH_TAC
                THEN CONV_TAC (LAND_CONV BETA_CONV
                               THENC RAND_CONV BETA_CONV)) (asl,gl)
            end;


(* The following set of tactics create a facility to use respectfulness
   and preservation theorems which are conditioned by quotient antecedents
   almost as easily as if they were simple implications or equations.
*)

        fun QUOT_MATCH_ACCEPT_TAC th =
            W(MATCH_ACCEPT_TAC o (match_higher_wf th) o snd)

        fun QUOT_MATCH_MP_TAC th =
            W(MATCH_MP_TAC o (match_higher_wf th) o snd)

        fun QUOT_REWR_CONV th =
            W(REWR_CONV o (match_higher_eq th))

        fun QUOT_REWRITE_CONV thl =
            EVERY_CONV (map (TOP_DEPTH_CONV o QUOT_REWR_CONV) thl)

        fun QUOT_REWRITE_RULE thl = CONV_RULE (QUOT_REWRITE_CONV thl)

        fun QUOT_REWRITE_TAC thl = CONV_TAC (QUOT_REWRITE_CONV thl)

(* Here are some possible extensions to higher order rewriting,
   which are currently not needed:

        fun SPEC_UNDISCH_ALL th =
              let val th' = UNDISCH_ALL (SPEC_ALL th)
              in if concl th = concl th' then th
                 else SPEC_UNDISCH_ALL th'
              end

        fun QUOT_HO_REWR_CONV th =
            W(Conv.HO_REWR_CONV o pthm o REWRITE_RULE[I_THM] o pthm
                  o repeat resolve_quotient o pthm o UNDISCH_ALL
                  o HO_PART_MATCH I (SPEC_UNDISCH_ALL th)
                (* o ptm "part_match " *) )

        fun QUOT_HO_REWRITE_CONV thl =
            EVERY_CONV (map (TOP_DEPTH_CONV o QUOT_HO_REWR_CONV) thl)

        fun QUOT_HO_REWRITE_RULE thl = CONV_RULE (QUOT_HO_REWRITE_CONV thl)
*)

(* The EQUALS_RSP_TAC tactic:

                      ?-  R x1 x2  /\  R x2 y2
                ====================================
                       ?-  R x1 y1 = R x2 y2

   R must be the partial equivalence relation of some quotient.
*)

        fun EQUALS_RSP_TAC (asl,gl) =
            let val tms1 = rand (rator gl)
                val _ = assert is_rep_ty (type_of (rand tms1))
                val wf = match_higher_half_wf EQUALS_RSP gl
            in ((MATCH_MP_TAC wf handle _ => MATCH_ACCEPT_TAC wf)
                 THEN REPEAT STRIP_TAC) (asl,gl)
            end

(* The APPLY_RSP_TAC tactic:

               ?-  (R1 ===> R2) f g  /\  R1 x y
             ====================================
                      ?-  R2 (f x) (g y)

   The type of f must contain a type being lifted.  Furthermore,
   f must be of the form (v a1 ... an) with 0 <= n, where v is a variable.

   This is intended to apply where the "head"s of f and g are variables,
   not constants.  In this case the two variables should be related in the
   assumption list.
*)

        fun APPLY_RSP_TAC (asl,gl) =
            let val tms1 = rand (rator gl)
                val opp = rator tms1
                val _ = assert is_rep_ty (type_of opp)
                val wf = match_higher_half_wf APPLY_RSP gl
            in ((MATCH_MP_TAC wf handle _ => MATCH_ACCEPT_TAC wf)
                 THEN REPEAT STRIP_TAC) (asl,gl)
            end

(* The ABSTRACT_RES_ABSTRACT_TAC tactic implements two complimentary rules
   for dealing with RES_ABSTRACT:

                          ?-  (R1 ===> R2) f g
            =================================================
            ?-  (R1 ===> R2) (RES_ABSTRACT (respects R1) f) g

                          ?-  (R1 ===> R2) f g
            =================================================
            ?-  (R1 ===> R2) f (RES_ABSTRACT (respects R1) g)

   This will get rid of the RES_ABSTRACT on either the left or right,
   and when repeated on both, so that the other tactics can apply to
   the (perhaps) abstractions f and g.
*)
        val ABSTRACT_RES_ABSTRACT_TAC =
            QUOT_MATCH_MP_TAC ABSTRACT_RES_ABSTRACT ORELSE
            QUOT_MATCH_MP_TAC RES_ABSTRACT_ABSTRACT

        val ABS_REP_RSP_TAC : tactic =
             QUOT_MATCH_MP_TAC REP_ABS_RSP


(* The LAMBDA_PRS function creates a preservation theorem for an abstraction.
   It takes a function type fty = ty1 -> ty2 and returns a theorem of the form

                !f. (\x. f x) = (rep1 --> abs2) (\x. rep2 (f (abs1 x)))

   for the appropriate abs and rep functions for ty1 and ty2.
*)
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


(* The APPLIC_PRS function creates a preservation theorem for an application.
   It takes a function type fty = ty1 -> ty2 and returns a theorem of the form

                !f. f x = abs2 ((abs1 --> rep2) f (rep1 x))

   for the appropriate abs and rep functions for ty1 and ty2.
*)
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
            prove (gl,
            REPEAT GEN_TAC
            THEN REWRITE_TAC[FUN_MAP,FUN_MAP_I,(*SET_MAP_def,*)I_THM,PAIR_MAP]
            THEN REPEAT (CHANGED_TAC
                   (CONV_TAC (DEPTH_CONV BETA_CONV)
                    THEN REWRITE_TAC[]))
            THEN QUOT_REWRITE_TAC[QUOTIENT_ABS_REP]
            THEN REWRITE_TAC [ETA_AX]
            )
            end;

        fun MATCH_MP0_TAC th = (MATCH_MP_TAC th
                                handle _ => MATCH_ACCEPT_TAC th)


(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* R_MK_COMB_TAC tactic:                                                     *)
(*                                                                           *)
(*    The R_MK_COMB_TAC tactic is key to the correct processing of theorems  *)
(* being lifted up according to the equivalence relations.  It repeatedly    *)
(* breaks down a goal to be proved into subgoals, and then analyzes each     *)
(* subgoal, until all are resolved.  Each goal must be of the form           *)
(*                                                                           *)
(* RELATION term1 term2                                                      *)
(*                                                                           *)
(* where term1 and term2 are terms in the HOL OL of some type, say 'a,       *)
(* and where RELATION is a partial equivalence relation relating values      *)
(* of 'a.                                                                    *)
(* If 'a is not a type being lifted, then RELATION will be normal equality.  *)
(*                                                                           *)
(* Currently R_MK_COMB_TAC consists of 12 tactics, tried in order until      *)
(* one works.  The order of these tactics is very important.  For some       *)
(* goals, several of the tactics may apply, but they should be tried in      *)
(* order until the first one is found that works.                            *)
(*                                                                           *)
(* This tactic is called from two places: the most important of these is     *)
(* the call from TRANSFORM_CONV, which proves the expansion of the given,    *)
(* lower version of the theorem into a version with "rep o abs" "oil"        *)
(* injected between operator results and their uses.  This oil will be used  *)
(* in the collapse of the lower operators into their higher versions in      *)
(* subsequent rewriting.  This is part of the actual lifting of the theorem. *)
(*                                                                           *)
(* The other place which calls this tactic is from REGULARIZE_TAC, where     *)
(* this is used to solve subgoals of the form RELATION term1 term2.          *)
(* To work in this context, the tactic ABSTRACT_RES_ABSTRACT_TAC is present, *)
(* which would not be needed otherwise.  This is part of the attempt to      *)
(* reshape the given theorem into a regular form which can be lifted, which  *)
(* may or may not succeed.                                                   *)
(*                                                                           *)
(* We now list the 12 Individual tactics of R_MK_COMB_TAC:                   *)
(*                                                                           *)
(*                                                                           *)
(* 1. W(C (curry op THEN) (GEN_TAC THEN CONV_TAC                             *)
(*                 (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)) o        *)
(*              CONV_TAC o X_FUN_EQ_CONV o #Bvar o dest_abs o lhs o snd)     *)
(*                                                                           *)
(* This takes a goal of the form (\x. F(x)) = (\y. G(y))                     *)
(* and transforms it into the form F(x) = G(x).  I'll represent this as      *)
(*                                                                           *)
(*                         ?-  F(x) = G(x)                                   *)
(*                   ===========================                             *)
(*                   ?-  (\x. F(x)) = (\y. G(y))                             *)
(*                                                                           *)
(* The free variable "x" in the new goal is taken from the bound variable    *)
(* in the left-hand-side of the original goal.  This obviously only works    *)
(* if the type of the function (\x. F(x)) is not a type being lifted.        *)
(*                                                                           *)
(*                                                                           *)
(* 2.  ABSTRACT_RES_ABSTRACT_TAC                                             *)
(*                                                                           *)
(* This implements two complimentary rules for dealing with RES_ABSTRACT:    *)
(*                                                                           *)
(*                           ?-  (R1 ===> R2) f g                            *)
(*             =================================================             *)
(*             ?-  (R1 ===> R2) (RES_ABSTRACT (respects R1) f) g             *)
(*                                                                           *)
(*                           ?-  (R1 ===> R2) f g                            *)
(*             =================================================             *)
(*             ?-  (R1 ===> R2) f (RES_ABSTRACT (respects R1) g)             *)
(*                                                                           *)
(* This will get rid of the RES_ABSTRACT on either the left or right,        *)
(* and when repeated on both, so that the other tactics can apply to         *)
(* the (perhaps) abstractions f and g.                                       *)
(*                                                                           *)
(*                                                                           *)
(* 3.  LAMBDA_RES_TAC                                                        *)
(*                                                                           *)
(*                A U {R1 x y}  ?-  R2 (F(x)) (G(y))                         *)
(*             =========================================                     *)
(*             A  ?-  (R1 ===> R2) (\x. F(x)) (\y. G(y))                     *)
(*                                                                           *)
(* The free variable "x" is chosen to be not in the free variables of        *)
(* (\x. F(x)), and "y" is chosen to be not "x" or free in (\y. G(y)).        *)
(* If possible, they are chosed to be a close as possible to the bound       *)
(* variables.                                                                *)
(*                                                                           *)
(* The new assumption R1 x y is propogated for possible use later in         *)
(* solving subgoals of R2 (F(x)) (G(y)), where it may well be necessary      *)
(* to know that R1 x y.  This use of the assumption is accomplished by       *)
(* FIRST_ASSUM MATCH_ACCEPT_TAC mentioned below.                             *)
(*                                                                           *)
(*                                                                           *)
(* 4.  EQUALS_RSP_TAC                                                        *)
(*                                                                           *)
(*                    ?-  R x1 x2  /\  R x2 y2                               *)
(*              ====================================                         *)
(*                     ?-  R x1 y1 = R x2 y2                                 *)
(*                                                                           *)
(* R must be the partial equivalence relation of some quotient.              *)
(*                                                                           *)
(*                                                                           *)
(* 5.  FIRST (map HIGHER_RSP_TAC ho_polywfs)                                 *)
(*                                                                           *)
(* This tries the given generic constant respectfulness theorems until       *)
(* one fits (if any).  Then the goal is replaced by the corresponding        *)
(* antecedents, as by MATCH_MP_TAC.  The LET constant is a good example:     *)
(*                                                                           *)
(*                 ?-  (R1 ===> R2) f g  /\  R1 x y                          *)
(*                ==================================                         *)
(*                    ?-  R2 (LET f x) (LET g y)                             *)
(*                                                                           *)
(* The respectfulness theorems in ho_polywfs will have been converted to     *)
(* the highest order possible, e.g., for the LET respectfulness theorem,     *)
(*                                                                           *)
(*                ==================================                         *)
(*            ?-  ((R1 ===> R2) ===> R1 ===> R2) LET LET                     *)
(*                                                                           *)
(*                                                                           *)
(* 6.  FIRST(map MATCH_ACCEPT_TAC ho_respects)                               *)
(*                                                                           *)
(* The "ho_respects" are the respectfulness theorems generated for           *)
(* all newly defined functions, converted to the highest order, such as:     *)
(*                                                                           *)
(*      |- ($= ===> ALPHA) Con1 Con1                                         *)
(*      |- ($= ===> ALPHA) Var1 Var1                                         *)
(*      |- ($= ===> $= ===> LIST_REL ($= ### ALPHA)) $// $//                 *)
(*      |- (ALPHA ===> ALPHA ===> ALPHA) App1 App1                           *)
(*      |- ($= ===> ALPHA ===> ALPHA) Lam1 Lam1                              *)
(*      |- (($= ===> ALPHA) ===> ALPHA) Abs1 Abs1                            *)
(*      |- (ALPHA ===> $=) HEIGHT1 HEIGHT1                                   *)
(*      |- (ALPHA ===> $=) FV1 FV1                                           *)
(*      |- (LIST_REL ($= ### ALPHA) ===> $= ===> ALPHA) SUB1 SUB1            *)
(*      |- (LIST_REL ($= ### ALPHA) ===> $=) FV_subst1 FV_subst1             *)
(*      |- (ALPHA ===> LIST_REL ($= ### ALPHA) ===> ALPHA) $<[ $<[           *)
(*      |- ($= ===> LIST_REL ($= ### ALPHA) ===> LIST_REL ($= ### ALPHA)     *)
(*             ===> $=) ALPHA_subst ALPHA_subst                              *)
(*                                                                           *)
(*                                                                           *)
(* 7.  ABS_REP_RSP_TAC                                                       *)
(*                                                                           *)
(*                            ?-  R f g                                      *)
(*      =======================================================              *)
(*                       ?-  R f (rep (abs g)                                *)
(*                                                                           *)
(*                                                                           *)
(* 9.  APPLY_RSP_TAC                                                         *)
(*                                                                           *)
(*                ?-  (R1 ===> R2) f g  /\  R1 x y                           *)
(*              ====================================                         *)
(*                       ?-  R2 (f x) (g y)                                  *)
(*                                                                           *)
(* The type of f must contain a type being lifted.  Furthermore,             *)
(* f must be of the form (v a1 ... an) with 0 <= n, where v is a variable.   *)
(*                                                                           *)
(* This is intended to apply where the "head"s of f and g are variables      *)
(* or constants.  In the variables case, the two variables should be related *)
(* in the assumption list.                                                   *)
(*                                                                           *)
(*                                                                           *)
(* 9.  REFL_TAC                                                              *)
(*                                                                           *)
(*              ====================================                         *)
(*                          ?-  x = x                                        *)
(*                                                                           *)
(* 10.  MK_COMB_TAC                                                          *)
(*                                                                           *)
(*                    ?-  (f = g)  /\  (x = y)                               *)
(*              ====================================                         *)
(*                         ?-  f x = g y                                     *)
(*                                                                           *)
(*                                                                           *)
(* 11. FIRST_ASSUM MATCH_ACCEPT_TAC                                          *)
(*                                                                           *)
(* Finds the first assumption which matches the goal (if any).               *)
(*                                                                           *)
(*                                                                           *)
(*                     ====================                                  *)
(*                           A  ?-  A                                        *)
(*                                                                           *)
(* This makes use of the assumptions created by the tactic LAMBDA_RES_TAC    *)
(* mentioned above.                                                          *)
(*                                                                           *)
(*                                                                           *)
(* 12. FIRST (map MATCH_MP_TAC EQ_APs) (* for REGULARIZE later *)            *)
(*                                                                           *)
(* Reduces equivalence relations to equality relations.  An equality always  *)
(* implies equivalence, but not the reverse; so these may not be the right   *)
(* thing to do.  Nevertheless, sometimes it is easier to prove the equality. *)
(* Note that this ONLY works for relations which are full equivalence        *)
(* relations; partial equivalence relations are not in general reflexive.    *)
(*                                                                           *)
(*     [|- !p q. (p = q) ==> ALPHA p q,                                      *)
(*      |- !p q. (p = q) ==> ($= ### ALPHA) p q,                             *)
(*      |- !p q. (p = q) ==> LIST_REL ($= ### ALPHA) p q,                    *)
(*      |- !p q. (p = q) ==> (ALPHA +++ LIST_REL ($= ### ALPHA)) p q]        *)
(*                                                                           *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

        val R_MK_COMB_TAC = FIRST
          [W(C (curry op THEN) (GEN_TAC THEN CONV_TAC
                (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)) o
             CONV_TAC o X_FUN_EQ_CONV o #Bvar o dest_abs o lhs o snd)
           ,
           ABSTRACT_RES_ABSTRACT_TAC, (* slow to die? *)
           LAMBDA_RSP_TAC,
           EQUALS_RSP_TAC,
           FIRST (map HIGHER_RSP_TAC ho_polywfs)                 (* slow *)
           ,
           FIRST (map MATCH_ACCEPT_TAC ho_respects),
           ABS_REP_RSP_TAC, (* before MATCH_MP_RSP_TAC APPLY_RSP *)
           APPLY_RSP_TAC (* after MATCH_ACCEPT_TAC ho_respects,
                            before MK_COMB_TAC *)                (* slow *)
           ,
           REFL_TAC,
           MK_COMB_TAC
           ,
           FIRST_ASSUM MATCH_ACCEPT_TAC
           ,
           FIRST (map MATCH_MP_TAC EQ_APs) (* for REGULARIZE later *)
          ]

(* For testing purposes: *)
(* REPEAT R_MK_COMB_TAC  *)

        fun prim_liftedf opp =
          exists (fn func => (match_term func opp; true) handle _ => false)
              funcs

        fun liftedf opp =
          prim_liftedf opp orelse poly_liftedf opp

(* ------------------------------------------------------------------------- *)
(* The transconv function takes a term which is a statement to be lifted,    *)
(* and "inflates" the term by injecting "rep (abs _)" oil around every       *)
(* operator that yields a value being lifted.                                *)
(*                                                                           *)
(* The particular abs and rep functions used depend, of course, on the       *)
(* particular type of the value returned by the operator.                    *)
(*                                                                           *)
(* The new term is not necessarily equal to the old one; this equality is    *)
(* proven by the conversion TRANSCONV, using transconv and R_MK_COMB_TAC.    *)
(* ------------------------------------------------------------------------- *)

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
              else if (liftedf opp andalso is_rep_ty ty) then
                   mkrep(mkabs(list_mk_comb(opp,tms)))
              else if (is_var opp andalso length tms > 0
                                  andalso is_rep_ty ty) then
                   mkrep(mkabs(list_mk_comb(opp,tms)))
              else if tms = [] then opp
              else list_mk_comb(opp, tms)
            end

(* ------------------------------------------------------------------------- *)
(* The TRANSCONV conversion takes a term which is a statement to be lifted,  *)
(* "inflates" the term by injecting "rep (abs _)" oil around every operator  *)
(* that yields a value being lifted, and proves that the original term is    *)
(* equal to the inflated term, using transconv and R_MK_COMB_TAC.            *)
(* ------------------------------------------------------------------------- *)

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


(* ------------------------------------------------------------------------- *)
(* The regularize function takes a term which is a statement to be lifted,   *)
(* and converts it to a similar term which is "regular", as defined in the   *)
(* documentation for the quotient package.                                   *)
(*                                                                           *)
(* Instances of equality between two types being lifted are converted to     *)
(* instances of the appropriate partial equivalence relation.                *)
(* Instances of universal and existstential quantification for types being   *)
(* lifted are converted to "RES_FORALL R" or "RES_EXISTS R" for the          *)
(* appropriate partial equivalence relation R.                               *)
(* Several other more specialized conversions are performed as well.         *)
(*                                                                           *)
(* That the original theorem implies the regularized version is proved       *)
(* by the REGULARIZE function, using regularize and REGULARIZE_TAC.          *)
(* ------------------------------------------------------------------------- *)

        val domain = fst o dom_rng

        fun regularize tm =
          let val ty = type_of tm
              val regularize_abs = (pairLib.mk_pabs o (I ## regularize)
                                                   o pairLib.dest_pabs)
          in
            (* abstraction *)
            if is_abs tm then
              let val tm1 = regularize_abs tm
                  val dom = domain ty
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
            else if is_comb tm orelse is_const tm then
              let val (opp,args) = strip_comb tm
              in
                if is_const opp andalso is_rep_ty (type_of opp) then
                  let val name = #Name (dest_const opp) in
                    if name = "=" then
                      list_mk_comb(tyREL (type_of (hd args)), map regularize args)
                    else if mem name ["!","?","?!"] then
                      let val ty1 = (domain o type_of) opp
                          val tm1 = hd args
                          val tm1r = regularize_abs tm1
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
                      let val ty1 = (domain o domain o type_of) opp
                          val elemREL = tyREL ty1
                      in
                        if name = "SUBSET" then
                             list_mk_comb(--`SUBSETR ^elemREL`--, map regularize args)
                        else if name = "PSUBSET" then
                             list_mk_comb(--`PSUBSETR ^elemREL`--, map regularize args)
                        else
                             list_mk_comb(opp, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["INSERT"] then
                      let val ty1 = (domain o type_of) opp
                          val elemREL = tyREL ty1
                      in
                        list_mk_comb(--`INSERTR ^elemREL`--, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["DELETE","DISJOINT"] then
                      let val ty1 = (domain o domain o type_of) opp
                          val elemREL = tyREL ty1
                      in
                        if name = "DELETE" then
                             list_mk_comb(--`DELETER ^elemREL`--, map regularize args)
                        else if name = "DISJOINT" then
                             list_mk_comb(--`DISJOINTR ^elemREL`--, map regularize args)
                        else
                             list_mk_comb(opp, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["FINITE"] then
                      let val ty1 = (domain o domain o type_of) opp
                          val elemREL = tyREL ty1
                      in
                        list_mk_comb(--`FINITER ^elemREL`--, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["GSPEC"] then
                      let val ty1 = (domain o type_of) opp
                          val (dom,rng) = dom_rng ty1
                          val tya = hd (#Args (dest_type rng))
                          val bREL = tyREL tya
                          val aREL = tyREL dom
                      in
                        list_mk_comb(--`GSPECR ^aREL ^bREL`--, map regularize args)
                      end
                      handle _ => list_mk_comb(opp, map regularize args)
                    else if mem name ["IMAGE"] then
                      let val ty1 = (domain o type_of) opp
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
                         list_mk_comb(opp, [hd args,
                                         regularize_abs (hd (tl args)) ])
                      handle _ => list_mk_comb(opp, map regularize args)
                    else
                          list_mk_comb(opp, map regularize args)
                  end
                else
                     list_mk_comb(opp, map regularize args)
              end
            (* var *)
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


(* ------------------------------------------------------------------------- *)
(* The REGULARIZE_TAC tactic attempts to prove the equality of a term with   *)
(* its "regularized" version.  Similar to R_MK_COMB_TAC, it consists of a    *)
(* list of 18 tactics which are tried successively and repeatedly to find    *)
(* the first one that succeeds.  Unlike R_MK_COMB_TAC, success is not always *)
(* expected.                                                                 *)
(*                                                                           *)
(* The first seven tactics deal with various versions of quantification.     *)
(*                                                                           *)
(* This tactic is used by the REGULARIZE function to prove the regularized   *)
(* version of a given theorem.                                               *)
(* ------------------------------------------------------------------------- *)

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


(* ------------------------------------------------------------------------- *)
(* The REGULARIZE_RULE function attempts to prove the regularized version of *)
(* a given theorem.    It does this by calling "regularize" to generate the  *)
(* regularized version of the theorem's conclusion, and then by using        *)
(* REGULARIZE_TAC to prove that the regular version is implied by the        *)
(* original version.                                                         *)
(* ------------------------------------------------------------------------- *)

        fun REGULARIZE_RULE th =
               let val tm = concl th
                   val tm' = regularize tm
               in
                  if tm = tm' then th
                  else
                    (* REGULARIZE th *)
                    let
                        val rmp = mk_imp{ant=tm, conseq=tm'}
                        val rth = prove(rmp, REWRITE_TAC er_rws
                                             THEN REPEAT REGULARIZE_TAC)
                    in
                      MP rth th
                    end
                    handle _ => raise HOL_ERR {
                         origin_structure = "quotient",
                         origin_function  = "REGULARIZE",
                         message = "Could not lift the irregular theorem\n" ^
                             thm_to_string th ^ "\n" ^
                             "May try proving and then lifting\n" ^
                             term_to_string tm'
                   }
               end


(* ------------------------------------------------------------------------- *)
(* The check_high function verifies if the given term is completely formed   *)
(* of quotient-level constants and types, without any remaining elements     *)
(* from the lower, representational level.  Such elements might persist if   *)
(* for some reason the preservation theorem for some constant in the theorem *)
(* being lifted was not available to be used in the lifting process.         *)
(* ------------------------------------------------------------------------- *)

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


(* ------------------------------------------------------------------------- *)
(* In HOL4, version Kananaskis-3, it was discovered that higher order        *)
(* rewriting was damaged from before.  Previously a rewrite of the form      *)
(*  (\x. F x) = (\x. G x) would maintain the bound variable name.            *)
(* But the current version does not, changing the \x. to a gensym variable.  *)
(*                                                                           *)
(* REPAIRED_HO_PURE_REWRITE_RULE repairs this, and keeps the original        *)
(* variable name.                                                            *)
(* ------------------------------------------------------------------------- *)
(*
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
*)
(*
        fun HO_REWR_CONV th tm =
            (Ho_Rewrite.GEN_REWRITE_CONV TOP_DEPTH_CONV ths THENC
             (if is_abs (rand tm) then
                let val name = (#Name o dest_var o #Bvar o dest_abs o rand) tm
                in
                   RENAME_ABS_CONV name
                end
              else ALL_CONV)) tm

        fun HO_PURE_REWRITE_CONV1 ths tm =
            (Ho_Rewrite.GEN_REWRITE_CONV TOP_DEPTH_CONV ths THENC
             (if is_abs (rand tm) then
                let val name = (#Name o dest_var o #Bvar o dest_abs o rand) tm
                in
                   RENAME_ABS_CONV name
                end
              else ALL_CONV)) tm

        val REPAIRED_HO_PURE_REWRITE_RULE1 =
               CONV_RULE o HO_PURE_REWRITE_CONV1
*)


(* ------------------------------------------------------------------------- *)
(* Here we define LIFT_RULE, which is the function that lifts theorems from  *)
(* the original, lower level to the higher, quotient level.                  *)
(*                                                                           *)
(* LIFT_RULE has several phases:                                             *)
(*    1. Preliminary cleaning by GEN_ALL and tyop_simps;                     *)
(*    2. Conversion to regularized form by REGULARIZE_RULE;                  *)
(*    3. Check that all types within the theorem are supported by the        *)
(*          available quotient type extension theorems, and that all         *)
(*          operators within the theorem are supported by the available      *)
(*          respectfulness and preservation theorems.                        *)
(*    4. Extraction of the operators, abstractions, and applications         *)
(*          contained within the theorem to be lifted;                       *)
(*    5. Creation of the preservation theorems for the operators,            *)
(*          abstractions, and applications;                                  *)
(*    6. Transformation of the regular theorem to its "inflated" form;       *)
(*          ( This is the phase with the highest failure rate. )             *)
(*    7. Conversion of R (rep x) (rep y) to (x = y);                         *)
(*    8. Rewriting by all preservation theorems to collapse inflated forms;  *)
(*    9. Checking that the result has no remaining lower-level terms.        *)
(*                                                                           *)
(* If anything fails, LIFT_RULE wraps the exception with an error message    *)
(* containing the actual original theorem which was given to be lifted.      *)
(* ------------------------------------------------------------------------- *)

        val LIFT_RULE =
              (fn th => let val thr = (REGULARIZE_RULE o
                                        REWRITE_RULE (FUN_REL_EQ :: tyop_simps)
                                         o GEN_ALL) th
                            val tm = concl thr
                            val tys = mk_set (findalltys tm)
                            val _ = check_quotient_tys (tys_quot_ths @ tyop_ty_ths) tys
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
                          Ho_Rewrite.PURE_REWRITE_RULE LAM_APP_DEFS o
                          QUOT_REWRITE_RULE [GSYM EQUALS_PRS] o
                          CONV_RULE TRANSFORM_CONV) thr
                         handle e => raise HOL_ERR {
                                   origin_structure = "quotient",
                                   origin_function  = "LIFT_RULE",
                                   message = "Could not lift the theorem\n" ^
                                       thm_to_string th ^ "\n" ^
                                       exn_to_string e
                                  }
                         end)

    in

       LIFT_RULE
    end;
(* end of lift_theorem_by_quotients *)



(* --------------------------------------------------------------- *)
(* Check to see if a purported respectfulness theorem is actually  *)
(* of the right form.                                              *)
(* --------------------------------------------------------------- *)

fun check_respects_tm tm =
   let val (vrs,body) = strip_forall tm
       val (ants, base) = if is_imp body then
               let val {ant, conseq} = Rsyntax.dest_imp body
                in (strip_conj ant, conseq) end
          else ([],body)
       val ant_args = map (fn ant => (rand (rator ant), rand ant)) ants
       val _ = assert distinct (uncurry append (unzip ant_args))
       val ((Rc,t1),t2) = ((Psyntax.dest_comb ## I) o Psyntax.dest_comb) base
       val (c1,args1) = strip_comb t1
       val (c2,args2) = strip_comb t2
       val _ = assert (curry op = c1) c2
       val _ = assert distinct args1
       val _ = assert distinct args2
       val argpairs = zip args1 args2
       fun check_arg (a12 as (a1,a2)) =
               ((mem a12 ant_args andalso mem a1 vrs andalso mem a2 vrs
                 orelse (a1 = a2))
                 andalso type_of a1 = type_of a2)
       fun check_ant (ant12 as (ant1,ant2)) =
                (mem ant12 argpairs
                 andalso mem ant1 vrs andalso mem ant2 vrs
                 andalso type_of ant1 = type_of ant2)
       fun check_var vr = mem vr args1 orelse mem vr args2
   in
       all check_arg argpairs  andalso  all check_ant ant_args
       andalso  all check_var vrs
       orelse raise Match
   end;

fun check_respects th =
   Term.free_vars (concl th) = [] andalso
   check_respects_tm (concl th)
   handle e => raise HOL_ERR {
                        origin_structure = "quotient",
                        origin_function  = "check_respects",
                        message = "The following theorem is not of the right form for a respectfulness theorem:\n" ^
                                       thm_to_string th ^ "\n"
                                  };


(* --------------------------------------------------------------- *)
(* Check to see if a purported polymorphic respectfulness theorem  *)
(* is actually of the right form.                                  *)
(* --------------------------------------------------------------- *)

fun check_poly_respects th =
   let val (taus, ksis, Rs, abss, reps, uncond_tm) =
                                           strip_QUOTIENT_cond (concl th)
       val _ = assert (all is_vartype) (append taus ksis)
       val _ = assert distinct (append taus ksis)
       val _ = assert distinct (append (append Rs abss) reps)
   in
       Term.free_vars (concl th) = [] andalso
       check_respects_tm uncond_tm
   end
   handle e => raise HOL_ERR {
                        origin_structure = "quotient",
                        origin_function  = "check_poly_respects",
                        message = "The following theorem is not of the right form for a polymorphic respectfulness\ntheorem:\n" ^
                                       thm_to_string th ^ "\n"
                                  };

local
       fun any_type_var_in tyl ty = exists (C type_var_in ty) tyl
       fun un_abs_rep tyl tm = if any_type_var_in tyl (type_of tm)
                               then rand tm else tm
       fun check_strip_comb [] tm = (tm,[])
         | check_strip_comb (x::xs) tm =
             let val (tm', y) = Psyntax.dest_comb tm
                 val (c,ys) = check_strip_comb xs tm'
             in (c, y::ys) end
       fun dest_psv_rhs args tm =
             let val (c, ys) = check_strip_comb (rev args) tm
             in (c, rev ys) end

in
fun check_poly_preserves th =
   let val (taus, ksis, Rs, abss, reps, uncond_tm) =
                                           strip_QUOTIENT_cond (concl th)
       val _ = assert (all is_vartype) (append taus ksis)
       val _ = assert distinct (append taus ksis)
       val _ = assert distinct (append (append Rs abss) reps)
       val (vrs,body) = strip_forall uncond_tm
       val (tm1,tm2) = Psyntax.dest_eq body
       val (c1,args1) = strip_comb tm1
        (* Next line is for ABSTRACT_PRS, but not for APPLY_PRS: *)
       val args1' = if is_var c1 then c1::args1 else args1
       val _ = assert (all (C mem args1')) vrs
       val _ = assert (all (C mem vrs)) args1'
       val tm2' = un_abs_rep ksis tm2
       val (c2,args2) = dest_psv_rhs args1' tm2'
       val tysubst = map (op |->) (zip taus ksis)
       val _ = assert (curry op = (type_of tm1))
                      (type_subst tysubst (type_of tm2'))
       val args2' = map (un_abs_rep taus) args2
       val _ = assert (all (op =)) (zip args1' args2')
       val _ = assert (all (op =))
                      (zip (map type_of args1')
                           (map (type_subst tysubst o type_of) args2))
   in
           true
   end
   handle e => raise HOL_ERR {
                        origin_structure = "quotient",
                        origin_function  = "check_poly_preserves",
                        message = "The following theorem is not of the right form for a polymorphic preservation\ntheorem:\n" ^
                                       thm_to_string th ^ "\n"
                                  }
end;




(* --------------------------------------------------------------- *)
(* Returns a list of types present in the "respects" theorems but  *)
(* not directly mentioned in the "quot_ths" list, but for which    *)
(* quotient theorems can be built from the existing ones.          *)
(* --------------------------------------------------------------- *)

fun enrich_types quot_ths tyops respects =
     (* qtys holds the base types of the new quotients formed. *)
    let val qtys = map (hd o #Args o dest_type o type_of o hd o tl
                            o snd o strip_comb o concl) quot_ths
        fun resp_ty rth =
            let val body = (snd o strip_forall o concl) rth
                val base = (#conseq o dest_imp) body handle _ => body
            in (#Ty o dest_const o fst o strip_comb o #Rand o dest_comb) base
            end
        (* test checks there is a substitution theta s.t. ty2 theta = ty1: *)
        fun test ty1 ty2 = (match_type ty2 ty1; true) handle _ => false
        fun tintersect [] tys2 = []
          | tintersect (ty::tys) tys2 =
               if exists (test ty) tys2 then ty::tintersect tys tys2
                                        else     tintersect tys tys2
        fun tsubtract [] tys2 = []
          | tsubtract (ty::tys) tys2 =
               if exists (test ty) tys2 then     tsubtract tys tys2
                                        else ty::tsubtract tys tys2

     (* being_lifted ty is true iff ty contains a subtype being lifted *)
        fun being_lifted ty = not (null (tintersect (sub_tys ty) qtys))

     (* atys holds the types of arguments and results of the operators
           described in the "respects" theorems.
           These are used as suggestions for types of new quotient theorems
           that may be frequently needed in the later phase of lifting old
           theorems to the quotient level. *)
        val atys = mk_set (flatten (map (fun_tys o resp_ty) respects))

     (* ltys holds those types from atys which contain a type being lifted *)
        val ltys = filter being_lifted atys

     (* natys holds those types from ltys which are new, not in qtys *)
        val natys = tsubtract ltys qtys

     (* nstys holds all subtypes of the types in natys which contain a type
           being lifted *)
        val nstys = filter being_lifted (flatten (map sub_tys natys))

     (* ntys holds all types from nstys which are new, not in qtys *)
        val ntys = mk_set (tsubtract nstys qtys)

(*    val quot_ths' = quot_ths @ map (make_quotient quot_ths tyops) ntys *)
    in
        ntys
    end;




(* ------------------------ *)
(* ALTERNATIVE ENTRY POINT. *)
(* ------------------------ *)

fun define_quotient_types_rule {types, defs,
                                tyop_equivs, tyop_quotients, tyop_simps,
                                respects, poly_preserves, poly_respects} =
  let
      val equivs = map (PURE_REWRITE_RULE (map GSYM [EQUIV_def,PARTIAL_EQUIV_def])
                        o #equiv) types
      val _ = map check_equiv equivs
      val _ = map check_tyop_equiv tyop_equivs
      val _ = map check_tyop_quotient tyop_quotients
      val _ = map check_tyop_simp tyop_simps

      val equivs = filter is_equiv equivs
      val all_equivs = equivs @ tyop_equivs

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

      val _ = map check_respects respects
      val _ = map check_poly_preserves poly_preserves
      val _ = map check_poly_respects poly_respects

      val ntys = enrich_types quotients tyop_quotients respects
      val nequivs = map (make_equiv equivs tyop_equivs) ntys
      fun is_ident_equiv th =
             (curry op = "=" o #Name o dest_const o rand o concl
                             o PURE_REWRITE_RULE[GSYM EQUIV_def]) th
             handle _ => false
      val pequivs = equivs @ filter (not o is_ident_equiv) nequivs
      fun is_ident_quot th =
             (curry op = "=" o #Name o dest_const o rand o rator o rator o concl) th
             handle _ => false
      val quotients =
          quotients @ filter (not o is_ident_quot) (map (make_quotient quotients tyop_quotients) ntys)

      val LIFT_RULE =
             lift_theorem_by_quotients quotients pequivs tyop_equivs
                                       tyop_quotients tyop_simps fn_defns
                                       respects poly_preserves poly_respects
             handle e => Raise e
  in
    LIFT_RULE
  end;



(* ----------------- *)
(* MAIN ENTRY POINT. *)
(* ----------------- *)

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


fun define_quotient_types_full_rule {types, defs, tyop_equivs, tyop_quotients,
               tyop_simps, respects, poly_preserves, poly_respects} =
  let
      val tyop_equivs = tyop_equivs @
                        [LIST_EQUIV, PAIR_EQUIV, SUM_EQUIV, OPTION_EQUIV]
      val tyop_quotients = tyop_quotients @
                        [LIST_QUOTIENT, PAIR_QUOTIENT,
                            SUM_QUOTIENT, OPTION_QUOTIENT, FUN_QUOTIENT]
      val tyop_simps = tyop_simps @
                       [LIST_MAP_I, LIST_REL_EQ, PAIR_MAP_I, PAIR_REL_EQ,
                        SUM_MAP_I, SUM_REL_EQ, OPTION_MAP_I, OPTION_REL_EQ,
                        FUN_MAP_I, FUN_REL_EQ]
      val poly_preserves = poly_preserves @
                           [CONS_PRS, NIL_PRS, MAP_PRS, LENGTH_PRS, APPEND_PRS,
                            FLAT_PRS, REVERSE_PRS, FILTER_PRS, NULL_PRS,
                            SOME_EL_PRS, ALL_EL_PRS, FOLDL_PRS, FOLDR_PRS,
                            FST_PRS, SND_PRS, COMMA_PRS, CURRY_PRS,
                            UNCURRY_PRS, PAIR_MAP_PRS,
                            INL_PRS, INR_PRS, ISL_PRS, ISR_PRS, SUM_MAP_PRS,
                            NONE_PRS, SOME_PRS, IS_SOME_PRS, IS_NONE_PRS,
                            OPTION_MAP_PRS,
                            FORALL_PRS, EXISTS_PRS,
                            EXISTS_UNIQUE_PRS, ABSTRACT_PRS,
                            COND_PRS, LET_PRS, literal_case_PRS,
                            I_PRS, K_PRS, o_PRS, C_PRS, W_PRS]
      val poly_respects  = poly_respects @
                           [CONS_RSP, NIL_RSP, MAP_RSP, LENGTH_RSP, APPEND_RSP,
                            FLAT_RSP, REVERSE_RSP, FILTER_RSP, NULL_RSP,
                            SOME_EL_RSP, ALL_EL_RSP, FOLDL_RSP, FOLDR_RSP,
                            FST_RSP, SND_RSP, COMMA_RSP, CURRY_RSP,
                            UNCURRY_RSP, PAIR_MAP_RSP,
                            INL_RSP, INR_RSP, ISL_RSP, ISR_RSP, SUM_MAP_RSP,
                            NONE_RSP, SOME_RSP, IS_SOME_RSP, IS_NONE_RSP,
                            OPTION_MAP_RSP,
                            RES_FORALL_RSP, RES_EXISTS_RSP,
                            RES_EXISTS_EQUIV_RSP, RES_ABSTRACT_RSP,
                            COND_RSP, LET_RSP, literal_case_RSP,
                            I_RSP, K_RSP, o_RSP, C_RSP, W_RSP]
(* ?? EQUALS, LAMBDA, RES_FORALL, RES_EXISTS, APPLY ?? *)
  in
    define_quotient_types_rule
          {types=types, defs=defs,
           tyop_equivs=tyop_equivs, tyop_quotients=tyop_quotients,
           tyop_simps=tyop_simps,
           respects=respects,
           poly_preserves=poly_preserves, poly_respects=poly_respects}
  end;



fun define_quotient_types_full {types, defs, tyop_equivs, tyop_quotients,
               tyop_simps, respects, poly_preserves, poly_respects, old_thms} =
  let fun print_thm' th = if !chatting then (print_thm th; print "\n"; th)
                                       else th

      val LIFT_RULE =
          define_quotient_types_full_rule
              {types=types, defs=defs,
               tyop_equivs=tyop_equivs, tyop_quotients=tyop_quotients,
               tyop_simps=tyop_simps,
               respects=respects,
               poly_preserves=poly_preserves, poly_respects=poly_respects}

      val _ = if !chatting then print "\nLifted theorems:\n" else ()
      val new_thms = map (print_thm' o LIFT_RULE)
                         old_thms   handle e => Raise e
  in
    new_thms
  end;


fun define_quotient_types_std_rule {types, defs, respects} =
    define_quotient_types_full_rule
          {types=types, defs=defs,
           tyop_equivs=[], tyop_quotients=[],
           tyop_simps=[],
           respects=respects,
           poly_preserves=[], poly_respects=[]};



fun define_quotient_types_std {types, defs, respects, old_thms} =
    define_quotient_types_full
          {types=types, defs=defs,
           tyop_equivs=[], tyop_quotients=[],
           tyop_simps=[],
           respects=respects,
           poly_preserves=[], poly_respects=[],
           old_thms=old_thms};



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
