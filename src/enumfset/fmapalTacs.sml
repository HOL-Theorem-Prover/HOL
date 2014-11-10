(* File: fmapalTacs.sml. Author: F. Lockwood Morris. Begun 6 Aug 2013.    *)

(* Basic conversions and conversionals, and inference rules for         *)    
(* sorting lists, building FMAPALS, look-up and converting them to      *)
(* lists and uniting and restricting them.                              *)

structure fmapalTacs :> fmapalTacs =
struct
(* comment out load before Holmaking *)
(* app load ["totoTheory", "pred_setLib",
"reduceLib", "relationTheory", "enumeralTheory", "fmapalTheory", "enumTacs",
"totoTacs", "bossLib", "finite_mapTheory", "listLib"]; *)

open Parse HolKernel boolLib bossLib;

val _ = set_trace "Unicode" 0;
open  totoTheory reduceLib bossLib
 relationTheory listTheory pairTheory optionTheory enumeralTheory pred_setLib
 totoTacs finite_mapTheory fmapalTheory enumTacs listLib;

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val ERR = mk_HOL_ERR "fmapalTacs";

(* **************************************************************** *)
(* See introductory comment in enumTacs.sml.                        *)
(* **************************************************************** *)

(* ********************************************************************** *)
(*             Conversions for sorting lists with constant keys           *)
(* ********************************************************************** *)

val [none_any, some_none, some_some] = CONJUNCTS merge;

(* none_any = |- !l cmp. merge cmp [] l = l: thm
   some_none = |- !v5 v4 cmp. merge cmp (v4::v5) [] = v4::v5: thm
   some_some = |- !l2 l1 cmp b2 b1 a2 a1.
     merge cmp ((a1,b1)::l1) ((a2,b2)::l2) =
     case apto cmp a1 a2 of
       LESS => (a1,b1)::merge cmp l1 ((a2,b2)::l2)
     | EQUAL => (a1,b1)::merge cmp l1 l2
     | GREATER => (a2,b2)::merge cmp ((a1,b1)::l1) l2 *)

fun merge_CONV key_conv =
let fun merge_c t =
((REWR_CONV some_some THENC
  RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV key_conv))) THENC
         cpn_REWR_CONV THENC RAND_CONV merge_c) ORELSEC
REWR_CONV none_any ORELSEC REWR_CONV some_none) t
in merge_c end;

val [im_lengthen, im_zero, im_one]  = CONJUNCTS incr_merge;

(* im_lengthen = |- !l cmp. incr_merge cmp l [] = [SOME l]
   im_zero = |- !lol l cmp. incr_merge cmp l (NONE::lol) = SOME l::lol
   im_one = |- !m lol l cmp.
         incr_merge cmp l (SOME m::lol) =
         NONE::incr_merge cmp (merge cmp l m) lol *)

fun incr_merge_CONV key_conv =
let fun im_c t = ((REWR_CONV im_one THENC
                   RAND_CONV (RATOR_CONV (RAND_CONV (merge_CONV key_conv))
                              THENC im_c))
                  ORELSEC REWR_CONV im_zero ORELSEC REWR_CONV im_lengthen) t
in im_c end;

val [ib_base, ib_rec] = CONJUNCTS incr_build;

(* ib_base = |- !cmp. incr_build cmp [] = [] : thm
  val ib_rec = |- !cmp ab l.
         incr_build cmp (ab::l) = incr_merge cmp [ab] (incr_build cmp l) *)

fun incr_build_CONV key_conv =
let fun ib_c t = ((REWR_CONV ib_rec THENC RAND_CONV ib_c THENC
                   incr_merge_CONV key_conv)
                 ORELSEC REWR_CONV ib_base) t
in ib_c end;

val [mo_base, mo_none, mo_some] = CONJUNCTS merge_out;

(* mo_base = |- !l cmp. merge_out cmp l [] = l
   mo_none = |- !lol l cmp. merge_out cmp l (NONE::lol) = merge_out cmp l lol
   mo_some = |- !m lol l cmp.
         merge_out cmp l (SOME m::lol) = merge_out cmp (merge cmp l m) lol *)

fun merge_out_CONV key_conv =
let fun mo_c t = ((REWR_CONV mo_some THENC
                   RATOR_CONV (RAND_CONV (merge_CONV key_conv)) THENC
                   mo_c) ORELSEC
                  (REWR_CONV mo_none THENC mo_c) ORELSEC
                  REWR_CONV mo_base) t
in mo_c end;

fun incr_sort_CONV keyconv =
    (REWR_CONV incr_sort THENC RAND_CONV (incr_build_CONV keyconv) THENC
     merge_out_CONV keyconv) ORELSEC
(fn _ => Raise (mk_HOL_ERR "fmapalTacs" "incr_sort_CONV"
                           "not a list of explicit pairs"));

(* ****************************************************************** *)
(*         fmap_TO_FMAPAL_CONV, FUN_fmap_CONV, FUN_FMAPAL_CONV        *)
(* ****************************************************************** *)

(* fmap_TO_FMAPAL_CONV: convert ``fmap l`` to ``FMAPAL ...`` *)

fun fmap_TO_FMAPAL_CONV keyconv cmp =
REWR_CONV (ISPEC cmp FMAPAL_fmap) THENC
RAND_CONV (RAND_CONV (incr_sort_CONV keyconv)) THENC
RAND_CONV list_to_bt_CONV;

(* There seems to be no pre-provided explicit notation for a finite map
   in extension than is provided by fmap; hence we supply here only
   fmap_TO_FMAPAL_CONV, analogous to set_TO_ENUMERAL_CONV, but no analogue for
   DISPLAY_TO_ENUMERAL_CONV. *)

(* FUN_fmap_CONV: convert FUN_FMAP f [ ... ] to fmap [ ... ], given a  *)
(* conversion for working out applications of f.                       *)

fun FUN_fmap_CONV elemconv =
REWR_CONV (GSYM FUN_fmap_thm) THENC
RAND_CONV (MAP_CONV (BETA_CONV THENC RAND_CONV elemconv));

(* FUN_FMAPAL_CONV: convert FUN_FMAP f [ ... ] to FMAPAL cmp ...,      *)
(* given a conversion for evaluating applications of cmp, and cmp, and *)
(* another conversion for working out applications of f.               *)

fun FUN_FMAPAL_CONV keyconv cmp elemconv =
FUN_fmap_CONV elemconv THENC fmap_TO_FMAPAL_CONV keyconv cmp;

(* ******************************************************************* *)
(* The one pure conversion working on directly on fmaps of the form    *)
(* FMAPAL cmp ... is FAPPLY_CONV. Analogously to IN_CONV, it will      *)
(* do linear search in an fmap [ ... ] term with an equality-deciding  *)
(* conversion if it does not get the toto-evaluating conversion and    *)
(* FMAPAL cmp ... ' x  term it expects.                                *)
(* ******************************************************************* *)

(* FAPPLY_node = |- !cmp x l a b r.
     FMAPAL cmp (node l (a,b) r) ' x =  case apto cmp x a of
     LESS => FMAPAL cmp l ' x | EQUAL => b | GREATER => FMAPAL cmp r ' x

   FAPPLY_nt = |- !cmp x. FMAPAL cmp nt ' x = FEMPTY ' x *)

fun FAPPLY_CONV keyconv =
let fun apf_c t = ((REWR_CONV FAPPLY_node THENC RATOR_CONV
                    (RATOR_CONV (RATOR_CONV (RAND_CONV keyconv))) THENC
                    cpn_REWR_CONV THENC (apf_c ORELSEC ALL_CONV)) ORELSEC
                   REWR_CONV FAPPLY_nt) t;
    fun apf_i t = ((REWR_CONV FAPPLY_fmap_CONS THENC
                    RATOR_CONV (RATOR_CONV (RAND_CONV keyconv)) THENC
                    COND_CONV THENC
                    TRY_CONV apf_i) ORELSEC REWR_CONV FAPPLY_fmap_NIL) t
in apf_c ORELSEC apf_i end; (* I don't seem able to report an exception. *)

(* ******************************************************************* *)
(* To perform binary operations on fmaps, or between fmaps and sets,   *)
(* efficiently, we shall deal not in equations, as with proper         *)
(* conversions, but with terms of the form ORWL cmp <fmap expn> l,     *)
(* abbreviating (<fmap expn> = fmap l) /\ ORL l, and the form OWL s m, *)
(* abbreviating (s = set m) /\ OL m, s a <set expn>. We now give       *)
(* conversion-like functions to go back and forth between ORWL theorems*)
(* and FMAPAL terms. enumTacs has the same for OWL and ENUMERAL.       *)
(* ******************************************************************* *)

(* ***************************************************************** *)
(*        ORWL_TO_FMAPAL, FMAPAL_TO_ORWL, FMAPAL_TO_fmap_CONV        *)
(* ***************************************************************** *)

(* Translate |- ORWL cmp f l   to   |- f = FMAPAL cmp ... . *)

fun ORWL_TO_FMAPAL orwl =
let val (eqn, orwl) = CONJ_PAIR (CONV_RULE (REWR_CONV ORWL) orwl);
    val raw_ans = TRANS eqn (MATCH_MP ORL_FMAPAL orwl)
in CONV_RULE (RAND_CONV (RAND_CONV list_to_bt_CONV)) raw_ans end;

(* We need bt_to_orl_CONV, with _lb, _ub, _lb_ub variants, using _ac thms. *)

(* Remember that the ... = LESS comparisons will in practice always come out
   true. I can see no harm, however, in making bt_to_orl_CONV work correctly
   for arbitrary trees. *)

(* EQ_LESS_CONV converts cpn = LESS to one of T, F *)
(* COND_EQ_LESS_CONV coverts if cpn = LESS then a else b to one of a, b *)

val [lb_ub_acf_nt, lb_ub_acf_node] = CONJUNCTS bt_to_orl_lb_ub_ac;

(* lb_ub_acf_nt = |- !ub m lb cmp. bt_to_orl_lb_ub_ac cmp lb nt ub m = m
   lb_ub_acf_node = |- !y x ub r m lb l cmp.
     bt_to_orl_lb_ub_ac cmp lb (node l (x,y) r) ub m =
     if apto cmp lb x = LESS then
       if apto cmp x ub = LESS then
         bt_to_orl_lb_ub_ac cmp lb l x
           ((x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)
       else bt_to_orl_lb_ub_ac cmp lb l ub m
     else bt_to_orl_lb_ub_ac cmp lb r ub m *)

fun bt_to_orl_lb_ub_CONV keyconv =
let fun orluc t =
(REWR_CONV lb_ub_acf_nt ORELSEC
 (REWR_CONV lb_ub_acf_node THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
  COND_EQ_LESS_CONV THENC
  ((RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
    COND_EQ_LESS_CONV THENC
    ((RAND_CONV (RAND_CONV orluc) THENC orluc) ORELSEC
     orluc)) ORELSEC orluc))) t
in orluc end;

val [ub_acf_nt, ub_acf_node] = CONJUNCTS bt_to_orl_ub_ac;

(* ub_acf_nt = |- !ub m cmp. bt_to_orl_ub_ac cmp nt ub m = m
   ub_acf_node = |- !y x ub r m l cmp.
     bt_to_orl_ub_ac cmp (node l (x,y) r) ub m =
     if apto cmp x ub = LESS then
       bt_to_orl_ub_ac cmp l x ((x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)
     else bt_to_orl_ub_ac cmp l ub m *)

fun bt_to_orl_ub_CONV keyconv =
let fun oruc t =
(REWR_CONV ub_acf_nt ORELSEC
 (REWR_CONV ub_acf_node THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
  COND_EQ_LESS_CONV THENC
  ((RAND_CONV (RAND_CONV (bt_to_orl_lb_ub_CONV keyconv)) THENC oruc)
   ORELSEC oruc))) t
in oruc end;

val [lb_acf_nt, lb_acf_node] = CONJUNCTS bt_to_orl_lb_ac;

(* lb_acf_nt = |- !m lb cmp. bt_to_orl_lb_ac cmp lb nt m = m
   lb_acf_node = |- !y x r m lb l cmp.
     bt_to_orl_lb_ac cmp lb (node l (x,y) r) m =
     if apto cmp lb x = LESS then
       bt_to_orl_lb_ub_ac cmp lb l x ((x,y)::bt_to_orl_lb_ac cmp x r m)
     else bt_to_orl_lb_ac cmp lb r m *)

fun bt_to_orl_lb_CONV keyconv =
let fun orlc t =
(REWR_CONV lb_acf_nt ORELSEC
 (REWR_CONV lb_acf_node THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (LAND_CONV keyconv))) THENC
  COND_EQ_LESS_CONV THENC
  ((RAND_CONV (RAND_CONV orlc) THENC bt_to_orl_lb_ub_CONV keyconv)
   ORELSEC orlc))) t
in orlc end;

(* Top-level conversion works on a bt_to_orl, not a bt_to_orl_ac, term.
   Improved, imitating enumTacs, to check ORL_bt first. *)

val [ORL_lu_nt, ORL_lu_node] = CONJUNCTS ORL_bt_lb_ub;

(* ORL_lu_nt =
   |- !ub lb cmp. ORL_bt_lb_ub cmp lb nt ub <=> (apto cmp lb ub = LESS)
   ORL_lu_node = |- !y x ub r lb l cmp.
     ORL_bt_lb_ub cmp lb (node l (x,y) r) ub <=>
     ORL_bt_lb_ub cmp lb l x /\ ORL_bt_lb_ub cmp x r ub *)

fun ORL_bt_lb_ub_CONV keyconv = 
let fun olu t =
((REWR_CONV ORL_lu_nt THENC LAND_CONV keyconv THENC EQ_LESS_CONV) ORELSEC
 (REWR_CONV ORL_lu_node THENC
  LAND_CONV olu THENC RAND_CONV olu THENC AND_CONV)) t
in olu end;

val [ORL_l_nt, ORL_l_node] = CONJUNCTS ORL_bt_lb;

(* ORL_l_nt = |- !lb cmp. ORL_bt_lb cmp lb nt <=> T
   ORL_l_node = |- !y x r lb l cmp.
     ORL_bt_lb cmp lb (node l (x,y) r) <=>
     ORL_bt_lb_ub cmp lb l x /\ ORL_bt_lb cmp x r *)

fun ORL_bt_lb_CONV keyconv = 
let fun ol t =
((REWR_CONV ORL_l_node THENC
  LAND_CONV (ORL_bt_lb_ub_CONV keyconv) THENC RAND_CONV ol THENC AND_CONV)
 ORELSEC REWR_CONV ORL_l_nt) t
in ol end;

val [ORL_u_nt, ORL_u_node] = CONJUNCTS ORL_bt_ub;

(* ORL_u_nt = |- !ub cmp. ORL_bt_ub cmp nt ub <=> T
   ORL_u_node = |- !y x ub r l cmp.
     ORL_bt_ub cmp (node l (x,y) r) ub <=>
     ORL_bt_ub cmp l x /\ ORL_bt_lb_ub cmp x r ub *)

fun ORL_bt_ub_CONV keyconv = 
let fun ou t =
((REWR_CONV ORL_u_node THENC
  LAND_CONV ou THENC RAND_CONV (ORL_bt_lb_ub_CONV keyconv) THENC AND_CONV)
 ORELSEC REWR_CONV ORL_u_nt
 ) t
in ou end;

val [ORL_nt, ORL_node] = CONJUNCTS ORL_bt;

(* ORL_nt = |- ORL_bt cmp nt <=> T
   ORL_node = |- ORL_bt cmp (node l (x,y) r) <=>
   ORL_bt_ub cmp l x /\ ORL_bt_lb cmp x r *)

fun ORL_bt_CONV keyconv =
(REWR_CONV ORL_node THENC LAND_CONV (ORL_bt_ub_CONV keyconv) THENC
                          RAND_CONV (ORL_bt_lb_CONV keyconv) THENC AND_CONV)
ORELSEC REWR_CONV ORL_nt;

val [acf_nt, acf_node] = CONJUNCTS bt_to_orl_ac;

(*  acf_nt = |- bt_to_orl_ac cmp nt m = m
    acf_node = |- bt_to_orl_ac cmp (node l (x,y) r) m =
                  bt_to_orl_ub_ac cmp l x ((x,y)::bt_to_orl_lb_ac cmp x r m) *)

fun bt_to_orl_CONV keyconv =
let fun oc t =
(REWR_CONV acf_nt ORELSEC
 (REWR_CONV acf_node THENC
  RAND_CONV (RAND_CONV (bt_to_orl_lb_CONV keyconv)) THENC
  bt_to_orl_ub_CONV keyconv)) t
in REWR_CONV better_bt_to_orl THENC
   RATOR_CONV (RATOR_CONV (RAND_CONV (ORL_bt_CONV keyconv))) THENC
   COND_CONV THENC
   (bt_to_list_CONV ORELSEC oc)
end;

fun FMAPAL_TO_ORWL keyconv ft =
let val (cmp, bt)  =
 dest_binop ``FMAPAL:'a toto -> ('a#'b)bt -> ('a|->'b)``
            (ERR "FMAPAL_TO_ORWL" "Not a FMAPAL term") ft
in CONV_RULE (RAND_CONV (bt_to_orl_CONV keyconv))
             (ISPECL [cmp, bt] ORWL_bt_to_orl)
end;

fun FMAPAL_TO_fmap_CONV keyconv t =
 CONJUNCT1 (CONV_RULE (REWR_CONV ORWL) (FMAPAL_TO_ORWL keyconv t));

(* ***************************************************************** *)
(*                     ORWL_FUNION, FUNION_CONV                      *)
(* ***************************************************************** *)

(* ORWL_FUNION_THM = |- !cmp s l t m.
     ORWL cmp s l /\ ORWL cmp t m ==> ORWL cmp (s FUNION t) (merge cmp l m) *)

fun ORWL_FUNION keyconv orwsl orwtm =
CONV_RULE (RAND_CONV (merge_CONV keyconv))
          (MATCH_MP ORWL_FUNION_THM (CONJ orwsl orwtm));

fun FUNION_CONV keyconv ust =
let val (s, t)  =
 dest_binop ``$FUNION:('a|->'b) -> ('a|->'b) -> ('a|->'b)``
            (ERR "FUNION_CONV" "Not a FUNION term") ust
in ORWL_TO_FMAPAL (ORWL_FUNION keyconv (FMAPAL_TO_ORWL keyconv s)
                                        (FMAPAL_TO_ORWL keyconv t))
end;

(* ***************************************************************** *)
(*                         ORWL_DRESTRICT                            *)
(* ***************************************************************** *)

val [imnone_none, imsome_none, imnone_some,imsome_some] = CONJUNCTS inter_merge;

(* imnone_none = |- !cmp. inter_merge cmp [] [] = []
   imnone_some = |- !y m cmp. inter_merge cmp [] (y::m) = []
   imsome_none = |- !l cmp b a. inter_merge cmp ((a,b)::l) [] = []
   imsome_some = |- !y m l cmp b a.
     inter_merge cmp ((a,b)::l) (y::m) =
     case apto cmp a y of
       LESS => inter_merge cmp l (y::m)
     | EQUAL => (a,b)::inter_merge cmp l m
     | GREATER => inter_merge cmp ((a,b)::l) m *)

fun inter_merge_CONV keyconv =
let fun interm_c t =
((REWR_CONV imsome_some THENC
  RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV keyconv))) THENC
         cpn_REWR_CONV THENC (RAND_CONV interm_c ORELSEC interm_c)) ORELSEC
REWR_CONV imnone_some ORELSEC REWR_CONV imsome_none
                      ORELSEC REWR_CONV imnone_none)
t in interm_c  end;

(* ORWL_DRESTRICT_THM = |- !cmp s l t m. ORWL cmp s l /\ OWL cmp t m ==>
     ORWL cmp (DRESTRICT s t) (inter_merge cmp l m) *)

fun ORWL_DRESTRICT keyconv orwsl owtm =
CONV_RULE (RAND_CONV (inter_merge_CONV keyconv))
          (MATCH_MP ORWL_DRESTRICT_THM (CONJ orwsl owtm));

(* See below for DRESTRICT_CONV *)

(* ***************************************************************** *)
(*              ORWL_DRESTRICT_COMPL, DRESTRICT_CONV                 *)
(* ***************************************************************** *)

val [dmnone_none, dmsome_none, dmnone_some, dmsome_some] = CONJUNCTS diff_merge;

(* dmnone_none = |- !cmp. diff_merge cmp [] [] = []
   dmnone_some = |- !y m cmp. diff_merge cmp [] (y::m) = []
   dmsome_none = |- !l cmp b a. diff_merge cmp ((a,b)::l) [] = (a,b)::l
   dmsome_some =
   |- !y m l cmp b a.
     diff_merge cmp ((a,b)::l) (y::m) =
     case apto cmp a y of
       LESS => (a,b)::diff_merge cmp l (y::m)
     | EQUAL => diff_merge cmp l m
     | GREATER => diff_merge cmp ((a,b)::l) m *)

fun diff_merge_CONV keyconv =
let fun diffm_c t =
((REWR_CONV dmsome_some THENC
 RATOR_CONV (RATOR_CONV (RATOR_CONV  (RAND_CONV keyconv))) THENC
         cpn_REWR_CONV THENC (RAND_CONV diffm_c ORELSEC diffm_c)) ORELSEC
REWR_CONV dmnone_some ORELSEC REWR_CONV dmsome_none
                      ORELSEC REWR_CONV dmnone_none)
t in diffm_c  end;

(* ORWL_DRESTRICT_COMPL_THM = |- !cmp s l t m.
     ORWL cmp s l /\ OWL cmp t m ==>
     ORWL cmp (DRESTRICT s (COMPL t)) (diff_merge cmp l m) *)

fun ORWL_DRESTRICT_COMPL keyconv orwsl owtm =
CONV_RULE (RAND_CONV (diff_merge_CONV keyconv))
          (MATCH_MP ORWL_DRESTRICT_COMPL_THM (CONJ orwsl owtm));

(* One conversion, DRESTRICT_CONV, serves for both
 DRESTRICT ... (ENUMERAL ... ) and DRESTRICT ... (COMPL (ENUMERAL ... ))
 terms, and even cancels multiple COMPL's. *)

fun DRESTRICT_CONV keyconv mst =
let val (s, t)  =
 dest_binop ``DRESTRICT:('a|->'b) -> 'a set -> ('a|->'b)``
            (ERR "DRESTRICT_CONV" "Not a DRESTRICT term") mst
in if is_comb t andalso is_const (rator t) andalso
   fst (dest_const (rator t)) = "COMPL"
   then if is_comb (rand t) andalso is_const (rator (rand t)) andalso
        fst (dest_const (rator (rand t))) = "COMPL"
        then (RAND_CONV (REWR_CONV pred_setTheory.COMPL_COMPL) THENC
              DRESTRICT_CONV keyconv) mst
        else ORWL_TO_FMAPAL (ORWL_DRESTRICT_COMPL keyconv
              (FMAPAL_TO_ORWL keyconv s) (ENUMERAL_TO_OWL keyconv (rand t)))
   else ORWL_TO_FMAPAL (ORWL_DRESTRICT keyconv
              (FMAPAL_TO_ORWL keyconv s) (ENUMERAL_TO_OWL keyconv t))
end;

(* **************************************************************** *)
(*            MAP_ELEM_CONV, MAP_CONV, FDOM_CONV, o_f_CONV          *)
(* **************************************************************** *)

(* Following function maps a conversion over an explicit list term
   (blindly assuming any constant term is [] and any other is a :: l).
   ONCE_DEPTH_CONV seems to do just as well. *)

fun MAP_ELEM_CONV elemconv =
let fun mec t =
if is_const t then REFL t else (LAND_CONV elemconv THENC RAND_CONV mec) t
in mec end;

(* We also need listLib.MAP_CONV, simplifying a (MAP f [ ... ]) term. *)

(* bt_FST_FDOM = |- !cmp t. FDOM (FMAPAL cmp t) = ENUMERAL cmp (bt_map FST t)*)

(* bt_map = |- (!f. bt_map f nt = nt) /\
   !f l x r. bt_map f (node l x r) = node (bt_map f l) (f x) (bt_map f r) *)

val [bm_nft, bm_node] = CONJUNCTS bt_map;

fun bt_map_CONV fconv ft =
let val f = rator (rand ft);
    fun bmn t =
    (REWR_CONV bm_nft ORELSEC
     (REWR_CONV bm_node THENC (RATOR_CONV (RAND_CONV fconv)) THENC
      RAND_CONV bmn THENC
      RATOR_CONV (RATOR_CONV (RAND_CONV bmn)))) t
in bmn ft end;

val FDOM_CONV = (REWR_CONV bt_FST_FDOM THENC
                 RAND_CONV (bt_map_CONV (REWR_CONV FST))) ORELSEC
                (REWR_CONV fmap_FDOM THENC
                 RAND_CONV (MAP_CONV (REWR_CONV FST)));

(* We may save work with a separate IN_FDOM_CONV, also made to *)
(* work (slowly) for fmap [ .... ] too.                                 *)

val [in_fdom_nt, in_fdom_node] = CONJUNCTS FMAPAL_FDOM_THM;

(* in_fdom_nt = |- !cmp x. x IN FDOM (FMAPAL cmp nt) <=> F
   in_fdom_node = |- !cmp x a b l r.
     x IN FDOM (FMAPAL cmp (node l (a,b) r)) <=>
     case apto cmp x a of
       LESS => x IN FDOM (FMAPAL cmp l)
     | EQUAL => T
     | GREATER => x IN FDOM (FMAPAL cmp r) *)

val [notinfdomnil,infdomcons] = CONJUNCTS fmap_FDOM_rec;

(* notinfdomnil = |- !x. x IN FDOM (fmap []) <=> F
   infdomcons = |- !x w z l.
     x IN FDOM (fmap ((w,z)::l)) <=> (x = w) \/ x IN FDOM (fmap l) *)

val [T_OR, F_OR] = CONJUNCTS (prove (``(!p. T \/ p = T) /\ (!p. F \/ p = p)``,
 REWRITE_TAC [OR_CLAUSES]));

fun IN_FDOM_CONV keyconv =
let fun ifc t =
((REWR_CONV in_fdom_node THENC
  RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV keyconv))) THENC
  cpn_REWR_CONV THENC (ifc ORELSEC ALL_CONV)) ORELSEC
 REWR_CONV in_fdom_nt) t;
fun ifl t = ((REWR_CONV infdomcons THENC RATOR_CONV (RAND_CONV keyconv) THENC
              ((REWR_CONV F_OR THENC ifl) ORELSEC REWR_CONV T_OR))
             ORELSEC REWR_CONV notinfdomnil) t
in ifc ORELSEC ifl end;

(* o_f_CONV works out terms of the form f o_f FMAPAL ... to FMAPAL ...., given
   a conversion for working out f, also terms of the form
   f o_f fmap [ ... ] to fmap [ ......... ].                             *)

fun o_f_CONV fconv =
 (REWR_CONV o_f_bt_map THENC
  RAND_CONV (bt_map_CONV (REWR_CONV AP_SND THENC (RAND_CONV fconv)))) ORELSEC
 (REWR_CONV o_f_fmap THENC (RAND_CONV
   (MAP_CONV (REWR_CONV AP_SND THENC (RAND_CONV fconv)))));

(* **************************************************************** *)
(*             fmap_FUPDATE_CONV, FMAPAL_FUPDATE_CONV               *)
(* **************************************************************** *)

val [lrc_NIL, lrc_CONS] = CONJUNCTS list_rplacv_cn;

fun list_rplacv_CONV eqconv =
let fun lrcn t =
((REWR_CONV lrc_CONS THENC RATOR_CONV (RATOR_CONV (RAND_CONV eqconv)) THENC
  COND_CONV THENC TRY_CONV lrcn) ORELSEC
 REWR_CONV lrc_NIL) t
in lrcn THENC REPEATC BETA_CONV end;

(* Following conversion reduces terms of the form fmap [ ... ] |+ (x,y),
   provided a pair (x,w) already occurs in [ ... ]. *)

val NOT_CONS_NIL_EQN = prove (``!ab:'a#'b l. ((ab::l) = []) = F``,
REWRITE_TAC [NOT_CONS_NIL]);

fun fmap_FUPDATE_CONV eqconv t =
let val (fm, pair) = dest_binop
       ``FUPDATE:('a |-> 'b) -> 'a # 'b -> ('a |-> 'b)``
       (ERR "FUPDATE_CONV" "Not a FUPDATE term") t;
    val (x,y) = dest_binop ``$, : 'a -> 'b -> 'a # 'b``
       (ERR "FUPDATE_CONV" "Not an explicit pair") pair;
    val l = dest_monop ``fmap: ('a#'b)list -> ('a|->'b)``
       (ERR "FUPDATE_CONV" "not an fmap [ .. ] term") fm;
    val th = ISPECL [x, y, l] list_rplacv_thm;
    val th' = CONV_RULE (RAND_CONV (list_rplacv_CONV eqconv) THENC
                         REWR_CONV LET_THM THENC BETA_CONV) th;
    val th'' = (CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV
                             (REWR_CONV NOT_CONS_NIL_EQN))) THENC
                           COND_CONV) th')
               handle _ => raise (ERR "FUPDATE_CONV"
                           "FUPDATE_CONV will not extend the domain");
in CONJUNCT2 th'' end;

(* *** now FMAPAL_FUPDATE_CONV, treatment modeled on fmap_FUPDATE_CONV *** *)

val [brc_nt, brc_node] = CONJUNCTS bt_rplacv_cn;

(* brc_nt = |- !y x cn cmp. bt_rplacv_cn cmp (x,y) nt cn = nt
   brc_node = |- !z y x w r l cn cmp.
     bt_rplacv_cn cmp (x,y) (node l (w,z) r) cn =
     case apto cmp x w of
       LESS => bt_rplacv_cn cmp (x,y) l (\m. cn (node m (w,z) r))
     | EQUAL => cn (node l (x,y) r)
     | GREATER => bt_rplacv_cn cmp (x,y) r (\m. cn (node l (w,z) m)) *)

fun bt_rplacv_CONV keyconv =
let fun brcn t =
((REWR_CONV brc_node THENC
  RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV keyconv))) THENC
  cpn_REWR_CONV THENC TRY_CONV brcn) ORELSEC
 REWR_CONV brc_nt) t
in brcn THENC REPEATC BETA_CONV end;

(* Following conversion reduces terms of the form
   FMAPAL cmp ... |+ (x,y),
   provided a pair (x,w) already occurs in  ... . *)

val NOT_node_nt_EQN = prove (``!ab:'a#'b l r. ((node l ab r) = nt) = F``,
REWRITE_TAC [GSYM bt_distinct]);

fun FMAPAL_FUPDATE_CONV keyconv t =
let val (fm, pair) = dest_binop
       ``FUPDATE:('a |-> 'b) -> 'a # 'b -> ('a |-> 'b)``
       (ERR "FUPDATE_CONV" "Not a FUPDATE term") t;
    val (x,y) = dest_binop ``$, : 'a -> 'b -> 'a # 'b``
       (ERR "FUPDATE_CONV" "Not an explicit pair") pair;
    val (cmp, bt) = dest_binop ``FMAPAL: 'a toto -> ('a#'b)bt -> ('a|->'b)``
       (ERR "FUPDATE_CONV" "not a FMAPAL  ... term") fm;
    val th = ISPECL [cmp, x, y, bt] bt_rplacv_thm;
    val th' = CONV_RULE (RAND_CONV (bt_rplacv_CONV keyconv) THENC
                         REWR_CONV LET_THM THENC BETA_CONV) th;
    val th'' = (CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV
                             (REWR_CONV NOT_node_nt_EQN))) THENC
                           COND_CONV) th')
               handle _ => raise (ERR "FUPDATE_CONV"
                           "FMAPAL_FUPDATE_CONV will not extend the domain");
in CONJUNCT2 th'' end;

fun FUPDATE_CONV keyconv t =
if is_const (rator (rand (rator t))) (* should then be fmap *)
then fmap_FUPDATE_CONV keyconv t
else FMAPAL_FUPDATE_CONV keyconv t;

(* ******************************************************************* *)
(*                           FMAP_EXPR_CONV                            *)
(* ******************************************************************* *)

fun FMAPAL_EXPR_TO_ORWL keyconv t =
let val c = rator (rator t) 
in if is_const c then
   let val d = fst (dest_const c)
   in if d = "FMAPAL" then FMAPAL_TO_ORWL keyconv t
      else if d = "FUNION" then ORWL_FUNION keyconv
                                (FMAPAL_EXPR_TO_ORWL keyconv (rand (rator t)))
                                (FMAPAL_EXPR_TO_ORWL keyconv (rand t))
      else if d = "DRESTRICT" then
              if is_const (rator (rand t)) andalso
                 fst (dest_const (rator (rand t))) = "COMPL" then
                 ORWL_DRESTRICT_COMPL keyconv
                   (FMAPAL_EXPR_TO_ORWL keyconv (rand (rator t)))
                   (ENUMERAL_TO_OWL keyconv (rand (rand t)))
              else 
                 ORWL_DRESTRICT keyconv
                   (FMAPAL_EXPR_TO_ORWL keyconv (rand (rator t)))
                   (ENUMERAL_TO_OWL keyconv (rand t))
      else raise (ERR "FMAPAL_EXPR_TO_ORWL" "not a recognized binary operator")
   end
   else raise (ERR "FMAPAL_EXPR_TO_ORWL" "not a binary operation")
end;

fun FMAP_EXPR_CONV keyconv t = ORWL_TO_FMAPAL (FMAPAL_EXPR_TO_ORWL keyconv t);


(* ********************* sorting: set_TO_ORWL ************************* *)
(* The function set_TO_ORWL accepts fmap [ ... ] term and returns the   *)
(* corresponding OWL theorem.                                           *)
(* ******************************************************************** *)

fun fmap_TO_ORWL keyconv cmp fmapl =
let val th = ISPECL [cmp, rand fmapl] fmap_ORWL_thm
in CONV_RULE (RAND_CONV (incr_sort_CONV keyconv)) th end;

(* Examples for debugging: *)
(* **************************************************

val mg = Term`merge numto [(1,T); (2,T); (5,T)] [(1,F); (3,F)]`;
merge_CONV numto_CONV mg;
val img = Term`incr_merge numto [(1,()); (5,())]
                                  [SOME [(2,()); (3,())]]`;
val imz = Term`incr_merge numto [(3,())]
                                  [NONE; SOME [(2,()); (3,())]]`;
incr_merge_CONV numto_CONV img;
incr_merge_CONV numto_CONV imz;

 val ibl = Term`incr_build numto
                  [(3,()); (1,()); (3,()); (4,()); (2,()); (1,())]`;
incr_build_CONV numto_CONV ibl;
                
val mo5 = Term`merge_out numto [(5,())]
      [NONE; SOME [(1,()); (3,())]; SOME [(1,()); (2,()); (3,()); (4,())]]`;
merge_out_CONV numto_CONV mo5;

incr_sort_CONV numto_CONV ``incr_sort numto [6,T;5,T;4,T;3,T;2,T;1,T]``;

fmap_TO_FMAPAL_CONV numto_CONV ``numto``
   ``fmap [(10,T); (9,F); (8,T); (7,F); (6,T); (5,F); (4,T); (3,F); (2,T)]``;

FUN_FMAPAL_CONV numto_CONV ``numto`` REDUCE_CONV ``FUN_FMAP SUC (set [1;3;5])``;

  val apft = Term`(FMAPAL numto (node nt (5,T) nt)) ' 5`;
  FAPPLY_CONV numto_CONV apft;
  val fpt =
      ``fmap [(10,T); (9,F); (8,T); (7,F); (6,T); (5,F); (4,T); (3,F); (2,T)]``;
  val fmt = rand (concl (fmap_TO_FMAPAL_CONV numto_CONV ``numto`` fpt));
  FAPPLY_CONV numto_CONV ``^fmt ' 8``;
  FAPPLY_CONV numto_CONV ``^fmt ' 9``;
  FAPPLY_CONV numto_CONV ``^fmt ' 1``;
  FAPPLY_CONV REDUCE_CONV ``^fpt ' 8``;
  FAPPLY_CONV REDUCE_CONV ``^fpt ' 9``;
  FAPPLY_CONV REDUCE_CONV ``^fpt ' 1``;

val fake = ASSUME ``ORWL numto (fmap [5,T; 4,F; 3,T]) [5,T; 4,F; 3,T]``;
ORWL_TO_FMAPAL fake;

val cmp = ``numto``;
val tbt = rand (rand (concl (fmap_TO_FMAPAL_CONV numto_CONV ``numto``
                             ``fmap [1,T;2,F;3,T;4,F;5,T]``)));
val bolt =  ``bt_to_orl_lb_ub_ac ^cmp 0 ^tbt 4 []``;
val bolt' =  ``bt_to_orl_lb_ub_ac ^cmp 0 ^tbt 8 []``;
val bolt'' =  ``bt_to_orl_lb_ub_ac ^cmp 2 ^tbt 5 []``;
bt_to_orl_lb_ub_CONV numto_CONV bolt;

val bult =  ``bt_to_orl_ub_ac ^cmp ^tbt 4 []``;
val bult' =  ``bt_to_orl_ub_ac ^cmp ^tbt 8 []``;
bt_to_orl_ub_CONV numto_CONV bult;

val bllt =  ``bt_to_orl_lb_ac ^cmp 2 ^tbt []``;
val bllt' =  ``bt_to_orl_lb_ac ^cmp 0 ^tbt []``;
bt_to_orl_lb_CONV numto_CONV bllt;

val blt =  ``bt_to_orl numto ^tbt``;
bt_to_orl_CONV numto_CONV blt;
val badbt = ``node (node nt (1,T) nt) (3,T) (node (node nt (3,F) nt)
              (4,F) (node nt (1,F) nt))``;
val badblt = ``bt_to_orl numto ^badbt``;
bt_to_orl_CONV numto_CONV badblt;

val tft = rand (concl (fmap_TO_FMAPAL_CONV numto_CONV ``numto``
                       ``fmap [4,F;1,T;3,T;5,T;2,F]``));
val orwa = FMAPAL_TO_ORWL numto_CONV tft;

val orwb = FMAPAL_TO_ORWL numto_CONV
          (rand (concl (fmap_TO_FMAPAL_CONV numto_CONV ``numto``
                        ``fmap [0,F;3,T;1,T;8,F]``)));
ORWL_FUNION numto_CONV orwa orwb;

val wft = rand (concl (fmap_TO_FMAPAL_CONV numto_CONV ``numto``
                       ``fmap [8,F;3,T;1,T;0,F]``));
val utwft = ``^tft FUNION ^wft``;
val u = FUNION_CONV numto_CONV utwft;
FMAPAL_TO_fmap_CONV numto_CONV (rand (concl u));

val ig = Term`inter_merge numto [1,T; 2,F; 5,T] [1; 3]`;
inter_merge_CONV numto_CONV ig;

val owb = ENUMERAL_TO_OWL numto_CONV
   (rand (concl (DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto`` ``{0;3;1;8}``)));
ORWL_DRESTRICT numto_CONV orwa owb;

val dg = Term`diff_merge numto [1,T; 2,F; 5,T] [1; 3]`;
diff_merge_CONV numto_CONV dg;

ORWL_DRESTRICT_COMPL numto_CONV orwa owb;

val wet =
 rand (concl (DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto`` ``{8;3;1;0}``));
val dtweft = ``DRESTRICT ^tft ^wet``;
DRESTRICT_CONV numto_CONV dtweft;
val dctweft = ``DRESTRICT ^tft (COMPL ^wet)``;
DRESTRICT_CONV numto_CONV dctweft;
val dccccctweft =
 ``DRESTRICT ^tft (COMPL (COMPL (COMPL (COMPL (COMPL ^wet)))))``;
DRESTRICT_CONV numto_CONV dccccctweft;

MAP_ELEM_CONV (RAND_CONV (DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto``))
   ``[(2, {4; 3}); (3, {2}); (4, {3; 1}); (1, {})]``;

FDOM_CONV
 ``FDOM (FMAPAL numto (node nt (4,F) (node (node nt (3,T) nt) (5,T) nt)))``;
FDOM_CONV ``FDOM (fmap [(4, F); (3, T); (5, T)])``;

o_f_CONV REDUCE_CONV ``$~ o_f ^tft``;
o_f_CONV REDUCE_CONV
``$~ o_f (FMAPAL numto (node nt (4,F) (node (node nt (3,T) nt) (5,T) nt)))``;
o_f_CONV REDUCE_CONV
``$~ o_f (fmap [(4, F);  (3, T); (5, T)])``;

IN_FDOM_CONV numto_CONV ``5 IN FDOM ^tft``;
IN_FDOM_CONV numto_CONV ``6 IN FDOM ^tft``;
IN_FDOM_CONV REDUCE_CONV ``3 IN FDOM (fmap [(4, F); (3, T); (5, T)])``;
IN_FDOM_CONV REDUCE_CONV ``2 IN FDOM (fmap [(4, F); (3, T); (5, T)])``;

list_rplacv_CONV REDUCE_CONV
    ``list_rplacv_cn (3,T) [(1,F); (2,F); (3,F); (4,F); (5,F)] (\m.m)``;
list_rplacv_CONV REDUCE_CONV ``list_rplacv_cn (3,T) [(1,F); (2,F)] (\m.m)``;

val t = ``fmap [(1,F); (2,F); (3,F); (4,F); (5,F)] |+ (3,T)``;
val tbad = ``fmap [(1,F); (2,F)] |+ (3,T)``;
val eqconv = REDUCE_CONV;
fmap_FUPDATE_CONV eqconv t;
(* Deliberately gives "will not extend domain" error: *)
fmap_FUPDATE_CONV eqconv tbad;

val tf = rand (concl (fmap_TO_FMAPAL_CONV numto_CONV ``numto``
                             ``fmap [(1,F); (2,F); (3,F); (4,F); (5,F)]``));
FMAPAL_FUPDATE_CONV numto_CONV ``FUPDATE ^tf (3,T)``;
(* Deliberately gives "will not extend domain" error: *)
FMAPAL_FUPDATE_CONV numto_CONV ``FUPDATE ^tf (6,T)``;

bt_rplacv_CONV numto_CONV ``bt_rplacv_cn numto (3,T) ^(rand tf) (\m.m)``;
bt_rplacv_CONV numto_CONV ``bt_rplacv_cn numto (0,T) ^(rand tf) (\m.m)``;

val wet =
 rand (concl (DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto`` ``{8;3;1;0}``));
val dtweft = ``DRESTRICT ^tft ^wet``;
FMAPAL_EXPR_TO_ORWL numto_CONV ``^tft FUNION (DRESTRICT ^wft ^wet)``;
FMAPAL_EXPR_TO_ORWL numto_CONV ``^tft FUNION (DRESTRICT ^wft (COMPL ^wet))``;
val dctweft = ``DRESTRICT ^tft (COMPL ^wet)``;
FMAPAL_EXPR_TO_ORWL numto_CONV ``^dctweft FUNION ^tft``;

FMAP_EXPR_CONV numto_CONV ``(^tft) FUNION DRESTRICT (^wft) (^wet)``;
FMAP_EXPR_CONV numto_CONV ``(^tft) FUNION DRESTRICT (^wft) (COMPL ^wet)``;

fmap_TO_ORWL numto_CONV ``numto`` ``fmap [(5,T); (3,F); (3,T)]``;
********************** *)
end;
