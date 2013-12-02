(* File: enumTacs.sml. Author: F. Lockwood Morris. Begun 6 Aug 2013.    *)

(* Basic conversions and conversionals, and inference rules for         *)    
(* sorting lists, building ENUMERALS, look-up and converting them to    *)
(* OWL's, performing merge-based opns. on OWL's, recovering ENUMERALS.  *)

structure enumTacs :> enumTacs =
struct
(* comment out load before Holmaking *)
(* app load ["totoTheory", "pred_setLib",
"reduceLib", "relationTheory", "enumeralTheory",
"stringLib", "totoTacs", "bossLib", "finite_mapTheory"]; *)

open Parse HolKernel boolLib;

val _ = set_trace "Unicode" 0;
open totoTheory reduceLib bossLib
 relationTheory listTheory pairTheory optionTheory enumeralTheory pred_setLib
 stringLib totoTacs finite_mapTheory;

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val ERR = mk_HOL_ERR "enumTacs";

val _ = intLib.deprecate_int ();

(* ********************************************************************* *)
(* The style of writing conversions here is modeled on that expounded    *)
(* by Lawrence Paulson in "A higher-order implementation of rewriting".  *)
(* It takes REWR_CONV (which he in that paper called "REWRITE_CONV")     *)
(* as the workhorse, leaving to it the work of matching terms and types, *)
(* but avoiding searching.  As an easily grasped example of the style,   *)
(* here is an equivalent of the listLib's REVERSE_CONV:                  *)
(* ********************************************************************* *)

(* REVERSE_REV = |- !L. REVERSE L = REV L [] *)

val [rev_nil, rev_rec] = CONJUNCTS REV_DEF;

(* rev_nil = |- !acc. REV [] acc = acc
   rev_rec = |- !h t acc. REV (h::t) acc = REV t (h::acc) *)

val REVERS_CONV =
let fun rev_conv t = ((REWR_CONV rev_rec THENC rev_conv) ORELSEC
                      REWR_CONV rev_nil) t
in REWR_CONV REVERSE_REV THENC rev_conv end;

(* ******************************************************************* *)
(*                EQ_LESS_CONV, COND_EQ_LESS_CONV                      *)
(* ******************************************************************* *)

(* EQ_LESS_CONV converts cpn = LESS to one of T, F *)

val LESS_T = SPEC ``LESS`` (INST_TYPE [alpha |-> ``:cpn``] REFL_CLAUSE);
val GREATER_F = prove (``(GREATER = LESS) = F``,REWRITE_TAC [all_cpn_distinct]);
val EQUAL_F = prove (``(EQUAL = LESS) = F``,REWRITE_TAC [all_cpn_distinct]);

val EQ_LESS_CONV = REWR_CONV LESS_T ORELSEC REWR_CONV GREATER_F ORELSEC
                   REWR_CONV EQUAL_F ORELSEC
(fn _ => Raise (mk_HOL_ERR "enumTacs" "EQ_LESS_CONV" "not a ... = LESS"));

(* A replacement for cpn_REWR_CONV when instead of case <cpn> of LESS => ...
   we have  if <cpn> = LESS then ... else ... .*)

val EQ_LESS_REWR = prove (``!v0 v1:'a. (if LESS = LESS then v0 else v1) = v0``,
RW_TAC bool_ss []);

val EQ_GREATER_REWR = prove (``!v0 v1:'a.
(if GREATER = LESS then v0 else v1) = v1``, RW_TAC bool_ss []);

val EQ_EQUAL_REWR = prove (``!v0 v1:'a.
(if EQUAL = LESS then v0 else v1) = v1``, RW_TAC bool_ss []);

val COND_EQ_LESS_CONV = REWR_CONV EQ_LESS_REWR ORELSEC REWR_CONV EQ_GREATER_REWR
                   ORELSEC REWR_CONV EQ_EQUAL_REWR ORELSEC
(fn _ => Raise (mk_HOL_ERR "enumTacs" "COND_EQ_LESS_CONV" "not if ... = LESS"));

(* ********************************************************************** *)
(*             Conversions for sorting lists with constant keys           *)
(* ********************************************************************** *)

val [none_none, some_none, none_some, some_some] = CONJUNCTS smerge;

(* none_none = |- !cmp. smerge cmp [] [] = []
   none_some = |- !y m cmp. smerge cmp [] (y::m) = y::m
   some_none = |- !x l cmp. smerge cmp (x::l) [] = x::l
   some_some = |- !y x m l cmp. smerge cmp (x::l) (y::m) =
     case apto cmp x y of
       LESS => x::smerge cmp l (y::m)
     | EQUAL => x::smerge cmp l m
     | GREATER => y::smerge cmp (x::l) m *)

fun smerge_CONV key_conv =
let fun merge_c t =
((REWR_CONV some_some THENC RAND_CONV key_conv THENC
         cpn_REWR_CONV THENC RAND_CONV merge_c) ORELSEC
REWR_CONV none_some ORELSEC REWR_CONV some_none ORELSEC REWR_CONV none_none) t
in merge_c end;


val [im_lengthen, im_zero, im_one]  = CONJUNCTS incr_smerge;

(* im_lengthen = |- !l cmp. incr_smerge cmp l [] = [SOME l]
   im_zero = |- !lol l cmp. incr_smerge cmp l (NONE::lol) = SOME l::lol
   im_one = |- !m lol l cmp.
     incr_smerge cmp l (SOME m::lol) =
     NONE::incr_smerge cmp (smerge cmp l m) lol *)

fun incr_smerge_CONV key_conv =
let fun im_c t = ((REWR_CONV im_one THENC
                   RAND_CONV (RATOR_CONV (RAND_CONV (smerge_CONV key_conv))
                              THENC im_c))
                  ORELSEC REWR_CONV im_zero ORELSEC REWR_CONV im_lengthen) t
in im_c end;

val [ib_base, ib_rec] = CONJUNCTS incr_sbuild;

(* ib_base = |- !cmp. incr_sbuild cmp [] = []
   ib_rec =
   |- !cmp x l.
     incr_sbuild cmp (x::l) = incr_smerge cmp [x] (incr_sbuild cmp l) *)

fun incr_sbuild_CONV key_conv =
let fun ib_c t = ((REWR_CONV ib_rec THENC RAND_CONV ib_c THENC
                   incr_smerge_CONV key_conv)
                 ORELSEC REWR_CONV ib_base) t
in ib_c end;

val [mo_base, mo_none, mo_some] = CONJUNCTS smerge_out;

(* mo_base = |- !l cmp. smerge_out cmp l [] = l
   mo_none =
   |- !lol l cmp. smerge_out cmp l (NONE::lol) = smerge_out cmp l lol
   mo_some =
   |- !m lol l cmp.
     smerge_out cmp l (SOME m::lol) =
     smerge_out cmp (smerge cmp l m) lol *)

fun smerge_out_CONV key_conv =
let fun mo_c t = ((REWR_CONV mo_some THENC
                   RATOR_CONV (RAND_CONV (smerge_CONV key_conv)) THENC
                   mo_c) ORELSEC
                  (REWR_CONV mo_none THENC mo_c) ORELSEC
                  REWR_CONV mo_base) t
in mo_c end;

fun incr_ssort_CONV key_conv =
    (REWR_CONV incr_ssort THENC RAND_CONV (incr_sbuild_CONV key_conv) THENC
     smerge_out_CONV key_conv) ORELSEC
(fn _ => Raise (mk_HOL_ERR "enumTacs" "incr_ssort_CONV"
                           "not an explicit list"));

(* ******************************************************************** *)
(*              BL_ACCUM_CONV, BL_CONS_CONV, bt_rev_CONV                *)
(* ******************************************************************** *)

val [umnbl, umzer, umone] = CONJUNCTS BL_ACCUM;

(* umnbl = |- !a ac. BL_ACCUM a ac nbl = onebl a ac nbl
   umzer = |- !a ac bl. BL_ACCUM a ac (zerbl bl) = onebl a ac bl
   umone =
    |- !a ac r rft bl.
         BL_ACCUM a ac (onebl r rft bl) =
         zerbl (BL_ACCUM a (node ac r rft) bl) *)

fun BL_ACCUM_CONV t =
((REWR_CONV umone THENC RAND_CONV BL_ACCUM_CONV) ORELSEC
 REWR_CONV umzer ORELSEC
 REWR_CONV umnbl) t;

val BL_CONS_CONV = (REWR_CONV BL_CONS THENC BL_ACCUM_CONV) ORELSEC
(fn _ => Raise (mk_HOL_ERR "rbtTacs" "BL_CONS_CNV" "bad call of BL_CONS"));

val [rnt, rnode] = CONJUNCTS bt_rev;

(* rnt = |- !bl. bt_rev nt bl = bl
   rnode = |- !lft r rft bl.
         bt_rev (node lft r rft) bl = bt_rev lft (onebl r rft bl) *)

fun bt_rev_CONV t =
((REWR_CONV rnode THENC bt_rev_CONV) ORELSEC REWR_CONV rnt) t;

(* ****************************************************************** *)
(*      bt_to_list_CONV (used by bt_to_ol_CONV);                      *)
(*      bl_to_bt_CONV, list_to_bl_CONV, list_to_bt_CONV               *)
(* ****************************************************************** *)

(* bt_to_list_CONV works out terms of the form bt_to_list_ac t [] *)

val [bt_list_nt, bt_list_node] = CONJUNCTS bt_to_list_ac;

(* bt_list_nt = |- !m. bt_to_list_ac nt m = m
   bt_list_node = |- !l x r m.
     bt_to_list_ac (node l x r) m =
     bt_to_list_ac l (x::bt_to_list_ac r m) *)

val bt_to_list_CONV =
let fun btl t = ((REWR_CONV bt_list_node THENC
                  RAND_CONV (RAND_CONV btl) THENC btl) ORELSEC
                 REWR_CONV bt_list_nt) t
in btl end;

(* bt_to_list_CONV ``bt_to_list_ac
     (node (node nt 1 nt) 2 (node (node nt 3 nt) 4 (node nt 5 nt))) []``; *)

val [lb_nil, lb_rec] = CONJUNCTS list_to_bl;

(* lb_nil = |- list_to_bl [] = nbl
   lb_rec = |- !a l. list_to_bl (a::l) = BL_CONS a (list_to_bl l) *)

fun list_to_bl_CONV t =
((REWR_CONV lb_rec THENC RAND_CONV list_to_bl_CONV THENC BL_CONS_CONV)
 ORELSEC REWR_CONV lb_nil ORELSEC
 (fn _ => Raise (mk_HOL_ERR "rbtTacs" "list_to_bl" "not an explicit list"))) t;

val [blr_nbl, blr_zer, blr_one] = CONJUNCTS bl_rev;

(* blr_nbl = |- !ft. bl_rev ft nbl = ft
   blr_zer = |- !ft b. bl_rev ft (zerbl b) = bl_rev ft b
   blr_one = |- !ft a f b. bl_rev ft (onebl a f b) = bl_rev (node ft a f) b *)

fun bl_rev_CONV t = 
((REWR_CONV blr_one THENC bl_rev_CONV) ORELSEC
 (REWR_CONV blr_zer THENC bl_rev_CONV) ORELSEC
 REWR_CONV blr_nbl) t;

val bl_to_bt_CONV = RATOR_CONV (REWR_CONV bl_to_bt) THENC bl_rev_CONV;

val list_to_bt_CONV = REWR_CONV list_to_bt THENC
                      RAND_CONV list_to_bl_CONV THENC bl_to_bt_CONV;

(* list_to_bt_CONV (Term`list_to_bt [(1,()); (2,()); (3,()); (4,())]`); *)

(* ******************************************************************* *)
(* set_TO_ENUMERAL_CONV, DISPLAY_TO_set_CONV, DISPLAY_TO_ENUMERAL_CONV *)
(* ******************************************************************* *)

(* Convert ``set l`` to ``ENUMERAL ...`` *)

fun set_TO_ENUMERAL_CONV keyconv cmp =
REWR_CONV (ISPEC cmp ENUMERAL_set) THENC
RAND_CONV (RAND_CONV (incr_ssort_CONV keyconv)) THENC
RAND_CONV list_to_bt_CONV;

val LIST_TO_SET_NIL = prove (
``{} = set ([]:'a list)``, REWRITE_TAC [LIST_TO_SET_THM]);

val LIST_TO_SET_CONS = prove (
``!a:'a l s. (s = set l) ==> (a INSERT s = set (a :: l))``,
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LIST_TO_SET_THM]);

(* DISPLAY_TO_set_CONV { ... } proves { ... } = set [ ... ] *)

fun DISPLAY_TO_set_CONV t =
if is_const t then
let val (s, ty) = dest_const t;
    val ety = hd (snd (dest_type ty))
in INST_TYPE [alpha |-> ety] LIST_TO_SET_NIL end
else
let val (elem, st) = dest_binop (Term`($INSERT):'a->('a->bool)->'a->bool`) 
             (ERR "DISPLAY_TO_set_CONV" "not a finite set extension") t;
    val ety = type_of elem
in SPEC elem (MATCH_MP (INST_TYPE [alpha |-> ety] LIST_TO_SET_CONS)
            (DISPLAY_TO_set_CONV st)) end;

fun DISPLAY_TO_ENUMERAL_CONV keyconv cmp =
               DISPLAY_TO_set_CONV THENC set_TO_ENUMERAL_CONV keyconv cmp;

(* ******************************************************************* *)
(* The one pure conversion working on directly on sets of the form     *)
(* ENUMERAL cmp ... is IN_CONV, which we allow to fall back on         *)
(* pred_setLib.IN_CONV in case it is given an equality-decider and     *)
(* a { ... } set in place of a cmp-evaluator and ENUMERAL cmp ... set. *)
(* ******************************************************************* *)

(* IN_node = |- !cmp x l y r. x IN ENUMERAL cmp (node l y r) <=>
     case apto cmp x y of
       LESS => x IN ENUMERAL cmp l
     | EQUAL => T
     | GREATER => x IN ENUMERAL cmp r

   NOT_IN_nt = |- !cmp y. y IN ENUMERAL cmp nt <=> F *)

fun IN_CONV key_conv =
let fun apf_c t = ((REWR_CONV IN_node THENC RAND_CONV key_conv THENC
                    cpn_REWR_CONV THENC (apf_c ORELSEC ALL_CONV)) ORELSEC
                   REWR_CONV NOT_IN_nt) t
                  handle _ => pred_setLib.IN_CONV key_conv t
in apf_c end;

(* ******************************************************************* *)
(* To perform binary operations on sets efficiently, we shall deal not *)
(* in equations, as with proper conversions, but with conjunctions of  *)
(* the form |- (<set expn> = set l) /\ OL cmp l, where l is an expli-  *)
(* citly displayed list. We now give conversion-like functions to go   *)
(* back and forth between such conjunctions -- strictly abbreviations  *)
(* of them as OWL cmp <set expn> l -- and ENUMERAL cmp ... sets.       *)
(* ******************************************************************* *)

(* Translate |- OWL cmp s l   to   |- s = ENUMERAL cmp ... . *)

fun OWL_TO_ENUMERAL owl =
let val (eqn, ol) = CONJ_PAIR (CONV_RULE (REWR_CONV OWL) owl);
    val raw_ans = TRANS eqn (MATCH_MP OL_ENUMERAL ol)
in CONV_RULE (RAND_CONV (RAND_CONV list_to_bt_CONV)) raw_ans end;

(* We need bt_to_ol_CONV, with _lb, _ub, _lb_ub variants, using _ac thms. *)

(* Remember that the ... = LESS comparisons will in practice always come out
   true. I can see no harm, however, in making bt_to_ol_CONV work correctly
   for arbitrary trees. *)

val [lb_ub_ac_nt, lb_ub_ac_node] = CONJUNCTS bt_to_ol_lb_ub_ac;

(* lb_ub_ac_nt = |- !cmp lb ub m. bt_to_ol_lb_ub_ac cmp lb nt ub m = m
   lb_ub_ac_node =
   |- !cmp lb l x r ub m.
     bt_to_ol_lb_ub_ac cmp lb (node l x r) ub m =
     if apto cmp lb x = LESS then
       if apto cmp x ub = LESS then
         bt_to_ol_lb_ub_ac cmp lb l x
           (x::bt_to_ol_lb_ub_ac cmp x r ub m)
       else bt_to_ol_lb_ub_ac cmp lb l ub m
     else bt_to_ol_lb_ub_ac cmp lb r ub m *)

fun bt_to_ol_lb_ub_CONV keyconv =
let fun oluc t =
(REWR_CONV lb_ub_ac_nt ORELSEC
 (REWR_CONV lb_ub_ac_node THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
  COND_EQ_LESS_CONV THENC
  ((RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
    COND_EQ_LESS_CONV THENC
    ((RAND_CONV (RAND_CONV oluc) THENC oluc) ORELSEC
     oluc)) ORELSEC oluc))) t
in oluc end;

val [ub_ac_nt, ub_ac_node] = CONJUNCTS bt_to_ol_ub_ac;

(* ub_ac_nt = |- !cmp ub m. bt_to_ol_ub_ac cmp nt ub m = m
   ub_ac_node = |- !cmp l x r ub m.
     bt_to_ol_ub_ac cmp (node l x r) ub m =
     if apto cmp x ub = LESS then
       bt_to_ol_ub_ac cmp l x (x::bt_to_ol_lb_ub_ac cmp x r ub m)
     else bt_to_ol_ub_ac cmp l ub m *)

fun bt_to_ol_ub_CONV keyconv =
let fun ouc t =
(REWR_CONV ub_ac_nt ORELSEC
 (REWR_CONV ub_ac_node THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
  COND_EQ_LESS_CONV THENC
  ((RAND_CONV (RAND_CONV (bt_to_ol_lb_ub_CONV keyconv)) THENC ouc)
   ORELSEC ouc))) t
in ouc end;

val [lb_ac_nt, lb_ac_node] = CONJUNCTS bt_to_ol_lb_ac;

(* lb_ac_nt = |- !cmp lb m. bt_to_ol_lb_ac cmp lb nt m = m
   lb_ac_node = |- !cmp lb l x r m.
     bt_to_ol_lb_ac cmp lb (node l x r) m =
     if apto cmp lb x = LESS then
       bt_to_ol_lb_ub_ac cmp lb l x (x::bt_to_ol_lb_ac cmp x r m)
     else bt_to_ol_lb_ac cmp lb r m *)

fun bt_to_ol_lb_CONV keyconv =
let fun olc t =
(REWR_CONV lb_ac_nt ORELSEC
 (REWR_CONV lb_ac_node THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
  COND_EQ_LESS_CONV THENC
  ((RAND_CONV (RAND_CONV olc) THENC bt_to_ol_lb_ub_CONV keyconv)
   ORELSEC olc))) t
in olc end;

(* Top-level conversion works on a bt_to_ol, not a bt_to_ol_ac, term. 
   Improved to check OL_bt first, and if this comes out T, as it always
   should, to used bt_to_list_CONV in place of bt_to_ol_lb/ub_CONV. *)

val [aTT, aTF, aFT, aFF] = CONJUNCTS (prove (
``(T/\T=T) /\ (T/\F=F) /\ (F/\T=F) /\ (F/\F=F)``,
REWRITE_TAC [AND_CLAUSES]));

val AND_CONV = REWR_CONV aTT ORELSEC REWR_CONV aTF ORELSEC 
               REWR_CONV aFT ORELSEC REWR_CONV aFF;

val [OL_lu_nt, OL_lu_node] = CONJUNCTS OL_bt_lb_ub;

(* OL_lu_nt =
   |- !cmp lb ub. OL_bt_lb_ub cmp lb nt ub <=> (apto cmp lb ub = LESS)
   OL_lu_node = |- !cmp lb l x r ub.
     OL_bt_lb_ub cmp lb (node l x r) ub <=>
     OL_bt_lb_ub cmp lb l x /\ OL_bt_lb_ub cmp x r ub *)

fun OL_bt_lb_ub_CONV keyconv = 
let fun olu t =
((REWR_CONV OL_lu_nt THENC LAND_CONV keyconv THENC EQ_LESS_CONV) ORELSEC
 (REWR_CONV OL_lu_node THENC
  LAND_CONV olu THENC RAND_CONV olu THENC AND_CONV)) t
in olu end;

val [OL_l_nt, OL_l_node] = CONJUNCTS OL_bt_lb;

(* OL_l_nt = |- !cmp lb. OL_bt_lb cmp lb nt <=> T
   OL_l_node =
   |- !cmp lb l x r. OL_bt_lb cmp lb (node l x r) <=>
     OL_bt_lb_ub cmp lb l x /\ OL_bt_lb cmp x r *)

fun OL_bt_lb_CONV keyconv = 
let fun ol t =
((REWR_CONV OL_l_node THENC
  LAND_CONV (OL_bt_lb_ub_CONV keyconv) THENC RAND_CONV ol THENC AND_CONV)
 ORELSEC REWR_CONV OL_l_nt) t
in ol end;

val [OL_u_nt, OL_u_node] = CONJUNCTS OL_bt_ub;

(* OL_u_nt = |- !cmp ub. OL_bt_ub cmp nt ub <=> T
   OL_u_node = |- !cmp l x r ub.
     OL_bt_ub cmp (node l x r) ub <=>
     OL_bt_ub cmp l x /\ OL_bt_lb_ub cmp x r ub *)

fun OL_bt_ub_CONV keyconv = 
let fun ou t =
((REWR_CONV OL_u_node THENC
  LAND_CONV ou THENC RAND_CONV (OL_bt_lb_ub_CONV keyconv) THENC AND_CONV)
 ORELSEC REWR_CONV OL_u_nt
 ) t
in ou end;

val [OL_nt, OL_node] = CONJUNCTS OL_bt;

(* OL_nt = |- !cmp. OL_bt cmp nt <=> T
   OL_node = |- !cmp l x r.
     OL_bt cmp (node l x r) <=> OL_bt_ub cmp l x /\ OL_bt_lb cmp x r *)

fun OL_bt_CONV keyconv =
(REWR_CONV OL_node THENC LAND_CONV (OL_bt_ub_CONV keyconv) THENC
                         RAND_CONV (OL_bt_lb_CONV keyconv) THENC AND_CONV)
ORELSEC REWR_CONV OL_nt;

val [ac_nt, ac_node] = CONJUNCTS bt_to_ol_ac;

(* ac_nt = |- !cmp m. bt_to_ol_ac cmp nt m = m
   ac_node = |- !cmp l x r m.
     bt_to_ol_ac cmp (node l x r) m =
     bt_to_ol_ub_ac cmp l x (x::bt_to_ol_lb_ac cmp x r m) *)

fun bt_to_ol_CONV keyconv =
let fun oc t =
(REWR_CONV ac_nt ORELSEC
 (REWR_CONV ac_node THENC
  RAND_CONV (RAND_CONV (bt_to_ol_lb_CONV keyconv)) THENC
  bt_to_ol_ub_CONV keyconv)) t
in REWR_CONV better_bt_to_ol THENC
   RATOR_CONV (RATOR_CONV (RAND_CONV (OL_bt_CONV keyconv))) THENC
   COND_CONV THENC
   (bt_to_list_CONV ORELSEC oc)
end;

fun ENUMERAL_TO_OWL keyconv et =
let val (cmp, bt)  =
 dest_binop ``ENUMERAL:'a toto -> 'a bt -> 'a set``
            (ERR "ENUMERAL_TO_OWL" "Not an ENUMERAL term") et
in CONV_RULE (RAND_CONV (bt_to_ol_CONV keyconv))
             (ISPECL [cmp, bt] OWL_bt_to_ol)
end;

(* ***************************************************************** *)
(* **** set_TO_DISPLAY_CONV, an inverse to DISPLAY_TO_set_CONV ***** *)
(* **** ENUMERAL_TO_set_CONV, an inverse to set_TO_ENUMERAL_CONV *** *)
(* ENUMERAL_TO_DISPLAY_CONV, an inverse to DISPLAY_TO_ENUMERAL_CONV  *)
(* TO_set_CONV, converts ENUMERAL, { ... }, set [... ] to set [... ] *)
(* ***************************************************************** *)

fun ENUMERAL_TO_set_CONV keyconv t =
 CONJUNCT1 (CONV_RULE (REWR_CONV OWL) (ENUMERAL_TO_OWL keyconv t));

fun set_TO_DISPLAY_CONV t =
let val iet = rand (concl (REWRITE_CONV [FOLDR]
                           ``FOLDR $INSERT {} ^(rand t)``))
in SYM (DISPLAY_TO_set_CONV iet) end;

fun ENUMERAL_TO_DISPLAY_CONV keyconv = ENUMERAL_TO_set_CONV keyconv
                                       THENC set_TO_DISPLAY_CONV;

fun TO_set_CONV keyconv = (* keyconv not used if we are converting from
                             { ... } or leaving set [ ... ] alone.     *)
ENUMERAL_TO_set_CONV keyconv ORELSEC DISPLAY_TO_set_CONV ORELSEC REFL;

(* ***************************************************************** *)
(*                     OWL_UNION, UNION_CONV                         *)
(* ***************************************************************** *)

(* OWL_UNION_THM = |- !cmp s l t m.
     OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s UNION t) (smerge cmp l m) *)

fun OWL_UNION keyconv owsl owtm =
CONV_RULE (RAND_CONV (smerge_CONV keyconv))
          (MATCH_MP OWL_UNION_THM (CONJ owsl owtm));

fun UNION_CONV keyconv ust =
let val (s, t)  =
 dest_binop ``$UNION:'a set -> 'a set -> 'a set``
            (ERR "UNION_CONV" "Not a UNION term") ust
in OWL_TO_ENUMERAL (OWL_UNION keyconv (ENUMERAL_TO_OWL keyconv s)
                                      (ENUMERAL_TO_OWL keyconv t))
   handle _ => pred_setLib.UNION_CONV keyconv ust
end;

(* ***************************************************************** *)
(*                     OWL_INTER, INTER_CONV                         *)
(* ***************************************************************** *)

val [inone_none, isome_none, inone_some, isome_some] = CONJUNCTS sinter;

(* inone_none = |- !cmp. sinter cmp [] [] = []
   inone_some = |- !y m cmp. sinter cmp [] (y::m) = []
   isome_none = |- !x l cmp. sinter cmp (x::l) [] = []
   isome_some = |- !y x m l cmp. sinter cmp (x::l) (y::m) =
     case apto cmp x y of
       LESS => sinter cmp l (y::m)
     | EQUAL => x::sinter cmp l m
     | GREATER => sinter cmp (x::l) m *)

fun sinter_CONV key_conv =
let fun inter_c t =
((REWR_CONV isome_some THENC RAND_CONV key_conv THENC
         cpn_REWR_CONV THENC (RAND_CONV inter_c ORELSEC inter_c)) ORELSEC
REWR_CONV inone_some ORELSEC REWR_CONV isome_none ORELSEC REWR_CONV inone_none)
t in inter_c end;

(* OWL_INTER_THM = |- !cmp s l t m.
     OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s INTER t) (sinter cmp l m) *)

fun OWL_INTER keyconv owsl owtm =
CONV_RULE (RAND_CONV (sinter_CONV keyconv))
          (MATCH_MP OWL_INTER_THM (CONJ owsl owtm));

fun INTER_CONV keyconv ist =
let val (s, t)  =
 dest_binop ``$INTER:'a set -> 'a set -> 'a set``
            (ERR "INTER_CONV" "Not a INTER term") ist
in OWL_TO_ENUMERAL (OWL_INTER keyconv (ENUMERAL_TO_OWL keyconv s)
                                      (ENUMERAL_TO_OWL keyconv t))
end;

(* ***************************************************************** *)
(*                     OWL_DIFF, SET_DIFF_CONV                      *)
(* ***************************************************************** *)

val [dnone_none, dsome_none, dnone_some, dsome_some] = CONJUNCTS sdiff;

(* dnone_none = |- !cmp. sdiff cmp [] [] = []
   dnone_some = |- !y m cmp. sdiff cmp [] (y::m) = []
   dsome_none = |- !x l cmp. sdiff cmp (x::l) [] = x::l
   dsome_some =
   |- !y x m l cmp.
     sdiff cmp (x::l) (y::m) =
     case apto cmp x y of
       LESS => x::sdiff cmp l (y::m)
     | EQUAL => sdiff cmp l m
     | GREATER => sdiff cmp (x::l) m *)

fun sdiff_CONV key_conv =
let fun diff_c t =
((REWR_CONV dsome_some THENC RAND_CONV key_conv THENC
         cpn_REWR_CONV THENC (RAND_CONV diff_c ORELSEC diff_c)) ORELSEC
REWR_CONV dnone_some ORELSEC REWR_CONV dsome_none ORELSEC REWR_CONV dnone_none)
t in diff_c end;

(* OWL_DIFF_THM = |- !cmp s l t m.
     OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s DIFF t) (sdiff cmp l m) *)

fun OWL_DIFF keyconv owsl owtm =
CONV_RULE (RAND_CONV (sdiff_CONV keyconv))
          (MATCH_MP OWL_DIFF_THM (CONJ owsl owtm));

fun SET_DIFF_CONV keyconv ist =
let val (s, t)  =
 dest_binop ``$DIFF:'a set -> 'a set -> 'a set``
            (ERR "SET_DIFF_CONV" "Not a DIFF term") ist
in OWL_TO_ENUMERAL (OWL_DIFF keyconv (ENUMERAL_TO_OWL keyconv s)
                                      (ENUMERAL_TO_OWL keyconv t))
end;

(* ******************************************************************* *)
(*                           SET_EXPR_CONV                             *)
(* ******************************************************************* *)

(* The purpose of SET_EXPR_CONV is to reduce expressions consisting of *)
(* more than one UNION, INTER, and/or DIFF applied to ENUMERAL terms,  *)
(* avoiding the overhead of repeated conversion to (mainly) and from   *)
(* the form of OWL theorems.                                           *)

fun SET_EXPR_TO_OWL keyconv t =
let val c = rator (rator t)
in if is_const c then
   let val d = fst (dest_const c)
   in if d = "ENUMERAL" then ENUMERAL_TO_OWL keyconv t
      else let val (owl1, owl2) = (SET_EXPR_TO_OWL keyconv (rand (rator t)),
                                   SET_EXPR_TO_OWL keyconv (rand t))
           in if d = "UNION" then OWL_UNION keyconv owl1 owl2
              else if d = "INTER" then OWL_INTER keyconv owl1 owl2
              else if d = "DIFF" then OWL_DIFF keyconv owl1 owl2
              else raise (ERR "SET_EXPR_TO_OWL" "unrecognized binary operator")
           end
   end
   else raise (ERR "SET_EXPR_TO_OWL" "not a binary operation")
end;

fun SET_EXPR_CONV keyconv t = OWL_TO_ENUMERAL (SET_EXPR_TO_OWL keyconv t);

(* ********************* sorting: set_TO_OWL **************************** *)
(* The function set_TO_OWL accepts either a set [ ... ] or a { ... } term *)
(* and returns the corresponding OWL theorem.                             *)
(* ********************************************************************** *)

fun set_TO_OWL keyconv cmp setl =
let val eqn = (DISPLAY_TO_set_CONV ORELSEC REFL) setl;
    val th = ISPECL [cmp, rand (rand (concl eqn))] set_OWL_thm
in CONV_RULE (RAND_CONV (incr_ssort_CONV keyconv) THENC
              RATOR_CONV (RAND_CONV (REWR_CONV (SYM eqn)))) th end;

(* Test Cases: ******************************************************
REVERS_CONV (Term`REVERSE [1; 2; 3; 4; 5]`);
(* val it = |- REVERSE [1; 2; 3; 4; 5] = [5; 4; 3; 2; 1] : thm *)

val mg = Term`smerge numto [1; 2; 5] [1; 3]`;
smerge_CONV numto_CONV mg;

val img = Term`incr_smerge numto [1; 5]
                                  [SOME [2; 3]]`;
val imz = Term`incr_smerge numto [3]
                                  [NONE; SOME [2; 3]]`;
incr_smerge_CONV numto_CONV img;
incr_smerge_CONV numto_CONV imz;

val ibl = Term`incr_sbuild numto [3; 1; 3; 4; 2; 1]`;
incr_sbuild_CONV numto_CONV ibl;
                
val mo5 = Term`smerge_out numto [5]
      [NONE; SOME [1; 3]; SOME [1; 2; 3; 4]]`;
smerge_out_CONV numto_CONV mo5;

val blco = Term`BL_CONS 5 (onebl 7 nt (zerbl (onebl 11
                   (node (node nt 8 nt) 9 (node nt 10 nt)) nbl)))`;
BL_CONS_CONV blco;

val ltb = Term`list_to_bl [(1,()); (2,()); (3,()); (4,())]`;
list_to_bl_CONV ltb;

set_TO_ENUMERAL_CONV numto_CONV ``numto``
                                ``set [10; 9; 8; 7; 6; 5; 4; 3; 2; 1]``;

val bltt = Term`bl_to_bt (onebl (1,()) nt
         (zerbl
            (onebl (3,())
               (node (node nt (5,()) nt) (7,()) (node nt (9,()) nt))
               nbl)))`;
bl_to_bt_CONV bltt;

DISPLAY_TO_set_CONV (Term`{5; 4; 6; 3; 3; 2}`);

DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto`` ``{3; 4; 6; 7; 7; 7; 7; 3; 3}``;

DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto`` ``{5; 6; 4; 8; 8; 8; 3; 1}``;

val s100 = Term`{0;1;2;3;4;5;6;7;8;9;10;19;18;17;16;15;14;13;12;11;
       20;22;24;26;28;30;29;27;25;23;21;39;38;37;36;35;34;33;32;31;
       40;41;42;43;44;45;56;57;48;49;50;59;58;57;56;55;54;53;52;51;
       60;63;66;69;61;64;67;62;65;68;79;75;71;78;74;70;77;73;76;72;
       99;98;96;93;89;84;80;82;85;88;92;95;97;81;83;87;92;91;90;94}`;

val s50 = Term`{10;19;18;17;16;15;14;13;12;11;
       40;41;42;43;44;45;56;57;48;49;50;59;58;57;56;55;54;53;52;51;
       99;98;96;93;89;84;80;82;85;88;92;95;97;81;83;87;92;91;90;94}`;

val t50 = DISPLAY_TO_ENUMERAL_CONV numto_CONV (Term`numto`) s50;
 (* 13270 infs. 0.064s *)
val qt50 = DISPLAY_TO_ENUMERAL_CONV qk_numto_CONV (Term`qk_numto`) s50;
 (* 12416 infs 0.064s *)
val t100 = DISPLAY_TO_ENUMERAL_CONV numto_CONV (Term`numto`) s100;
 (* 27315 infs. 0.140s *)
val qt100 = DISPLAY_TO_ENUMERAL_CONV qk_numto_CONV (Term`qk_numto`) s100;
 (* 27774 infs 0.148s*)

val apft = Term`5 IN ENUMERAL numto (node nt 5 nt)`;
IN_CONV numto_CONV apft;
val apgt = Term`6 IN ENUMERAL numto (node nt 5 nt)`;
IN_CONV numto_CONV apgt;
IN_CONV REDUCE_CONV ``5 IN {3; 5; 2}``; (* fall-back to pred_setLib *)
IN_CONV REDUCE_CONV ``6 IN {3; 5; 2}``;

val fake = ASSUME ``OWL numto {5; 4; 3} [3; 4; 5]``;
   OWL_TO_ENUMERAL fake;

val cmp = ``numto``;
val tbt = rand (rand (concl (DISPLAY_TO_ENUMERAL_CONV
                             numto_CONV ``numto`` ``{1;2;3;4;5}``)));
val bolt =  ``bt_to_ol_lb_ub_ac ^cmp 0 ^tbt 4 []``;
val bolt' =  ``bt_to_ol_lb_ub_ac ^cmp 0 ^tbt 8 []``;
val bolt'' =  ``bt_to_ol_lb_ub_ac ^cmp 2 ^tbt 5 []``;
bt_to_ol_lb_ub_CONV numto_CONV bolt;

val bult =  ``bt_to_ol_ub_ac ^cmp ^tbt 4 []``;
val bult' =  ``bt_to_ol_ub_ac ^cmp ^tbt 8 []``;
bt_to_ol_ub_CONV numto_CONV bult;

val bllt =  ``bt_to_ol_lb_ac ^cmp 2 ^tbt []``;
val bllt' =  ``bt_to_ol_lb_ac ^cmp 0 ^tbt []``;
bt_to_ol_lb_CONV numto_CONV bllt;

val blt =  ``bt_to_ol numto ^tbt``;
bt_to_ol_CONV numto_CONV blt;
val badbt = ``node (node nt 1 nt) 3 (node (node nt 3 nt) 4 (node nt 1 nt))``;
val badblt = ``bt_to_ol numto ^badbt``;
bt_to_ol_CONV numto_CONV badblt;

val tet = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                       numto_CONV ``numto`` ``{4;1;3;5;2}``));
val owa = ENUMERAL_TO_OWL numto_CONV tet;

set_TO_DISPLAY_CONV ``set [5;4;3;2;1]``;
ENUMERAL_TO_set_CONV numto_CONV tet;
ENUMERAL_TO_DISPLAY_CONV numto_CONV tet;

TO_set_CONV numto_CONV tet;
TO_set_CONV NO_CONV ``{5; 4; 3; 2; 1}``;
TO_set_CONV NO_CONV ``set [5; 4; 3; 2; 1]``;

val owb = ENUMERAL_TO_OWL numto_CONV (rand (concl
          (DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto`` ``{0;3;1;8}``)));
OWL_UNION numto_CONV owa owb;
OWL_UNION numto_CONV owb owa;

val wet = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                       numto_CONV ``numto`` ``{8;3;1;0}``));
val utwet = ``^tet UNION ^wet``;
UNION_CONV numto_CONV utwet;
UNION_CONV REDUCE_CONV ``{1;5} UNION {3;2}``;

val ig = Term`sinter numto [1; 2; 5] [1; 3]`;
sinter_CONV numto_CONV ig;

OWL_INTER numto_CONV owa owb;

val itwet = ``^tet INTER ^wet``;
INTER_CONV numto_CONV itwet;

val ig' = Term`sdiff numto [1; 2; 5] [1; 3]`;
sdiff_CONV numto_CONV ig';

OWL_DIFF numto_CONV owa owb;

val itwet' = ``^tet DIFF ^wet``;
SET_DIFF_CONV numto_CONV itwet';

val ta = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                      numto_CONV ``numto`` ``{4;1;3;5;2}``));
val tb = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                      numto_CONV ``numto`` ``{3; 4; 6; 7; 3}``)); 
val tc = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                      numto_CONV ``numto``
                                               ``{5; 6; 4; 8; 3; 1}``));

SET_EXPR_TO_OWL numto_CONV ``(^ta) UNION (^tb) INTER (^tc)``;

SET_EXPR_CONV numto_CONV ``(^ta) UNION (^tb) INTER (^tc)``;
SET_EXPR_CONV numto_CONV ``(^tb) UNION (^tc) DIFF (^ta)``;
SET_EXPR_CONV numto_CONV ta; (* expensive identity function, though
   it would prune unreachable parts of the tree if there could be any. *)

set_TO_OWL numto_CONV ``numto`` ``set [5; 3; 3; 3; 4; 2; 3; 1]``;
set_TO_OWL numto_CONV ``numto`` ``{5; 3; 3; 3; 4; 2; 3; 1}``;
********************************************************************* *)
end;
