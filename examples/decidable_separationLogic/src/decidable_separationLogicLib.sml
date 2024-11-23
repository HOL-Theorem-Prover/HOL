structure decidable_separationLogicLib :> decidable_separationLogicLib =
struct

open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath :=
            (concat Globals.HOLDIR "/examples/decidable_separationLogic/src") ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "decidable_separationLogicTheory", "listLib",
   "decidable_separationLogicLibTheory", "optionLib", "stringLib"];
show_assums := true;
*)

open finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory decidable_separationLogicTheory listLib
   decidable_separationLogicLibTheory listSyntax;


(*
quietdec := false;
*)


val INFINITE_UNIV___THMs = ref ([]:thm list);


fun DUMMY_CONV t =
   let
      val v = mk_var("XXXX", type_of t);
      val thm = mk_thm ([], mk_eq (t, v))
   in
      thm
   end;



val swap_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [SWAP_REWRITES, APPEND]
   swap_cs;

val ds_direct_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [MAP, PF_TURN_EQ_def, SAFE_MAP_THM]
   ds_direct_cs;


(*
val sf_points_to_list_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [SF_POINTS_TO_LIST_def, SAFE_FILTER_THM, MAP, APPEND,
   DISJOINT_LIST_PRODUCT_def, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND]
   sf_points_to_list_cs;
*)

val SMALLFOOT_ERR s = raise mk_HOL_ERR "decidable_separationLogicLib" "" s


(************************************************************
 Term consts
*************************************************************)

val LIST_DS_ENTAILS_term = ``LIST_DS_ENTAILS``;
val pf_true_term = ``pf_true``;
val pf_equal_term = ``pf_equal``;
val pf_unequal_term = ``pf_unequal``;

val sf_star_term = ``sf_star``;
val sf_emp_term = ``sf_emp``;;
val sf_ls_term = ``sf_ls``;
val sf_points_to_term = ``sf_points_to``;
val sf_tree_term = ``sf_tree``;
val sf_bin_tree_term = ``sf_bin_tree``;

val dse_var_term = ``dse_var``;
val dse_const_term = ``dse_const``;
val dsv_nil_term = ``dsv_nil``;
val dse_nil_term = ``dse_nil``;


(************************************************************
 destructors
************************************************************)
local
   fun strip_cons_int l t =
      if not (listSyntax.is_cons t) then (l, t) else
      let
         val (e, t') = listSyntax.dest_cons t
      in
         strip_cons_int (l@[e]) t'
      end
in
   val strip_cons = strip_cons_int []
end;

fun list_mk_cons [] b  = b |
      list_mk_cons (t::tL) b  =
      listSyntax.mk_cons (t, list_mk_cons tL b);


fun dest_LIST_DS_ENTAILS t =
   let
      val (f, args) = strip_comb t;
      val _ = if same_const f LIST_DS_ENTAILS_term then () else
                  (SMALLFOOT_ERR "NO DEST_LIST_ENTAILS!");
      val _ = if (length args = 3) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
      val (pre, ante, cons) = (el 1 args, el 2 args, el 3 args);
      val (c1, c2) = pairLib.dest_pair pre;
      val (ante_pf, ante_sf) = pairLib.dest_pair ante;
      val (cons_pf, cons_sf) = pairLib.dest_pair cons;
   in
      (c1, c2, ante_pf, ante_sf, cons_pf, cons_sf)
   end;



fun dest_pf_equal pf =
   let
      val (f, args) = strip_comb pf;
      val _ = if same_const f pf_equal_term then () else
                  (SMALLFOOT_ERR "NO PF_EQUAL!");
      val _ = if (length args = 2) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
   in
      (hd args, hd (tl args))
   end;


fun dest_pf_unequal pf =
   let
      val (f, args) = strip_comb pf;
      val _ = if same_const f pf_unequal_term then () else
                  (SMALLFOOT_ERR "NO PF_UNEQUAL!");
      val _ = if (length args = 2) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
   in
      (hd args, hd (tl args))
   end;


(*
   val sf = ``sf_ls f e1 e2``
*)
fun dest_sf_ls sf =
   let
      val (f, args) = strip_comb sf;
      val _ = if same_const f sf_ls_term then () else
                  (SMALLFOOT_ERR "NO SF_LIST!");
      val _ = if (length args = 3) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
   in
      (el 1 args, el 2 args, el 3 args)
   end


(*
   val sf = ``sf_bin_tree (f1,f2) e``
   val sf = ``sf_bin_tree fL e``
*)
fun dest_sf_bin_tree sf =
   let
      val (f, args) = strip_comb sf;
      val _ = if same_const f sf_bin_tree_term then () else
                  (SMALLFOOT_ERR "NO SF_BIN_TREE!");
      val _ = if (length args = 2) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
      val (f1,f2) = pairLib.dest_pair (el 1 args)
      val _ = if f1 = f2 then (SMALLFOOT_ERR "NO SF_BIN_TREE!") else ();
   in
      (f1,f2, el 2 args, el 1 args)
   end


(*
   val sf = ``sf_tree (f1::f2::l) e1 e2``
   val sf = ``sf_ls f e1 e2``
   val sf = ``sf_bin_tree (f1,f2) e``
   val sf = ``sf_bin_tree fL e``
*)
fun dest_sf_tree sf =
   let
      val (f, args) = strip_comb sf;
      val _ = if same_const f sf_tree_term then () else
                  (SMALLFOOT_ERR "NO SF_TREE!");
      val _ = if (length args = 3) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
      val p = strip_cons (el 1 args)

   in
      (p, el 2 args, el 3 args)
   end


fun dest_sf_tree_ext sf =
   let
      val (p, es, e) = dest_sf_tree sf;
   in
      (sf, p, es, e)
   end handle _ =>
   let
      val (f1, f2, e, _) = dest_sf_bin_tree sf;
      val (_, typeL) = (dest_type (type_of e));
      val es = inst [alpha |-> el 1 typeL, beta |-> el 2 typeL] ``dse_nil:('a, 'b) ds_expression``;
   in
      (sf, ([f1,f2], mk_list ([], type_of f1)), es, e)
   end handle _ =>
   let
      val (f, e, es) = dest_sf_ls sf;
   in
      (sf, ([f], mk_list ([], type_of f)), es, e)
   end;


(*
   val sf = ``sf_points_to e ((f1, e1)::(f2,e2)::l)``
*)
fun dest_sf_points_to sf =
   let
      val (f, args) = strip_comb sf;
      val _ = if same_const f sf_points_to_term then () else
                  (SMALLFOOT_ERR "NO POINTS_TO!");
      val _ = if (length args = 2) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
      val (l1, l2) = strip_cons (el 2 args);
      val l1' = map pairLib.dest_pair l1;
   in
      (el 1 args, el 2 args, l1', l2)
   end


fun dest_dse_var t =
   let
      val (f, args) = strip_comb t;
      val _ = if same_const f dse_var_term then () else
                  (SMALLFOOT_ERR "NO VAR!");
      val _ = if (length args = 1) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
   in
      (hd args)
   end;

fun dest_dse_const t =
   let
      val (f, args) = strip_comb t;
      val _ = if same_const f dse_const_term then () else
                  (SMALLFOOT_ERR "NO CONST!");
      val _ = if (length args = 1) then () else
                  (SMALLFOOT_ERR "Wrong No. of ARGS!");
   in
      (hd args)
   end;

val is_pf_true = same_const pf_true_term;
val is_sf_emp = same_const sf_emp_term;
val is_pf_equal = can dest_pf_equal;
val is_pf_unequal = can dest_pf_unequal;
val is_sf_ls = can dest_sf_ls;
val is_sf_points_to = can dest_sf_points_to;
val is_sf_tree = can dest_sf_tree;
val is_sf_bin_tree = can dest_sf_bin_tree;
val is_sf_tree_ext = can dest_sf_tree_ext;

val is_dse_var = can dest_dse_var;
val is_dse_const = can dest_dse_const;
fun is_dse_nil ex = same_const ex dse_nil_term;


fun is_uneq_2 e1 e2 pf =
   let
      val (e1', e2') = dest_pf_unequal pf;
   in
      ((e1 = e1') andalso (e2 = e2')) orelse
      ((e2 = e1') andalso (e1 = e2'))
   end handle _ => false;

fun is_eq_2 e1 e2 pf =
   let
      val (e1', e2') = dest_pf_equal pf;
   in
      ((e1 = e1') andalso (e2 = e2')) orelse
      ((e2 = e1') andalso (e1 = e2'))
   end handle _ => false;

fun is_uneq_nil ex pf =
   let
      val (e1, e2) = dest_pf_unequal pf;
   in
      ((e1 = ex) andalso (is_dse_nil e2)) orelse
      ((e2 = ex) andalso (is_dse_nil e1))
   end;


fun is_pf_equal_refl pf =
   (let
      val (e1, e2) = dest_pf_equal pf;
   in
      e1 = e2
   end) handle _ => false


fun is_pf_unequal_refl pf =
   (let
      val (e1, e2) = dest_pf_unequal pf;
   in
      e1 = e2
   end) handle _ => false


fun is_sf_ls_eq sf =
   (let
      val (f, e1, e2) = dest_sf_ls sf;
   in
      e1 = e2
   end) handle _ => false


fun is_sf_trivial_list sf =
   let
      val (f, e1, e2) = dest_sf_ls sf
   in
      (e1 = e2)
   end handle _ => false;


fun is_sf_trivial_bin_tree sf =
   let
      val (_, _, e, _) = dest_sf_bin_tree sf
   in
      is_dse_nil e
   end handle _ => false;


fun is_sf_trivial_tree sf =
   let
      val (_, e1, e2) = dest_sf_tree sf
   in
      (e1 = e2)
   end handle _ => false;



fun is_sf_trivial sf =
   is_sf_trivial_list sf orelse
   is_sf_trivial_bin_tree sf orelse
   is_sf_trivial_tree sf orelse
   is_sf_emp sf;


fun is_pf_trivial pf =
   is_pf_equal_refl pf orelse
   is_pf_true pf;


fun is_points_to_nil t =
   let
      val (e, _, _, _) = dest_sf_points_to t;
   in
      is_dse_nil e
   end handle _ => false;


fun pf_eq pf1 pf2 =
   (if (pf1 = pf2) then (true, false) else
   if (is_pf_equal pf1) then (
      let
         val (e1, e2) = dest_pf_equal pf1;
         val (e1', e2') = dest_pf_equal pf2;
      in
         ((e1 = e2') andalso (e2 = e1'), true) (*e1 = e1' ... => pf1 = pf2*)
      end
   ) else
   if (is_pf_unequal pf1) then (
      let
         val (e1, e2) = dest_pf_unequal pf1;
         val (e1', e2') = dest_pf_unequal pf2;
      in
         ((e1 = e2') andalso (e2 = e1'), true) (*e1 = e1' ... => pf1 = pf2*)
      end
   ) else (false, false))
   handle _ => (false, false)



fun is_dse_nil_list t =
   let
      val (_, e1, _) = dest_sf_ls t;
   in
      is_dse_nil e1
   end;

fun is_sf_points_to_ex ex h =
   let
      val (ex', _, _, _) = dest_sf_points_to h;
   in
      ex' = ex
   end;


(* too strong
fun is_dse_nil ex = (
   (same_const ex dse_nil_term) orelse
   let
      val n = dest_dse_const ex;
   in
      (same_const n dsv_nil_term)
   end) handle _ => false;
*)







(* general helper functions *)
local
   fun fun_in_list_help n P [] = NONE
   |   fun_in_list_help n P (e::l) =
         let
            val c = (P e) handle _ => false;
         in
            if c then (SOME (n, e)) else fun_in_list_help (n+1) P l
         end
in
   fun find_in_list P l = fun_in_list_help 0 P l;
end


local
   fun fun_in_list_help n P [] = NONE
   |   fun_in_list_help n P (e::l) =
         let
            val c = (P e) handle _ => NONE;
         in
            if isSome c then (SOME (n, e, valOf c)) else fun_in_list_help (n+1) P l
         end
in
   fun find_in_list_val P l = fun_in_list_help 0 P l;
end








(********************************************
 swapping
*********************************************)
fun GEN_SWAP_CONV n1 m1 n2 m2 n3 m3 n4 m4 n5 m5 n6 m6 =
   let
      val argsL = [n1, m1, n2, m2, n3, m3, n4, m4, n5, m5, n6, m6];
      val argTL = map (numSyntax.term_of_int) argsL;
(*    slightly more efficient, but reordering may be confusing when used manually

      val rewrite_thm = ISPECL argTL LIST_DS_ENTAILS___PERM_SWAP_ELEMENTS
*)
      val rewrite_thm = ISPECL argTL LIST_DS_ENTAILS___PERM_SWAP_TO_POS
   in
      (ONCE_REWRITE_CONV [rewrite_thm] THENC
               computeLib.CBV_CONV swap_cs)
   end


fun SWAP_CONV p n m =
   if (p = 0) then GEN_SWAP_CONV n m 0 0 0 0 0 0 0 0 0 0 else
   if (p = 1) then GEN_SWAP_CONV 0 0 n m 0 0 0 0 0 0 0 0 else
   if (p = 2) then GEN_SWAP_CONV 0 0 0 0 n m 0 0 0 0 0 0 else
   if (p = 3) then GEN_SWAP_CONV 0 0 0 0 0 0 n m 0 0 0 0 else
   if (p = 4) then GEN_SWAP_CONV 0 0 0 0 0 0 0 0 n m 0 0 else
   if (p = 5) then GEN_SWAP_CONV 0 0 0 0 0 0 0 0 0 0 n m else
   SMALLFOOT_ERR "Wrong Parameter"




(* EXAMPLE

val t = ``LIST_DS_ENTAILS ([e3;e4], [(e5,e6);(e8,e8)]) ((pf_equal e1 e2::pf_unequal dse_nil e2::pf_equal e1 e2::l),[]) ((pf_equal e1 e2::pf_unequal e1 e2::pf_equal e1 e2::l),[])``

SWAP_CONV 4 0 1 t

val l1 = [true, false, false];
val l2 = [false, true];
*)

fun should_turn (pf1, pf2) =
   if pf1 = pf2 then false else
   if (is_dse_nil pf1) then (not (is_dse_nil pf2)) else
   if (is_dse_var pf2) then (not (is_dse_var pf1)) else
   if (is_dse_const pf1) then (not (is_dse_const pf2)) else
   (term_to_string pf1 > term_to_string pf2);


fun bool_list2term l =
   let
      val l' = map (fn b => if b then T else F) l;
   in
      mk_list (l', bool)
   end


fun ds_TURN_EQUATIONS_CONV l1 l2 t =
   let
      val thm1 = SPECL [bool_list2term l1, bool_list2term l2] LIST_DS_ENTAILS___PF_TURN_EQ
      val thm2 = PART_MATCH (fst o dest_eq) thm1 t;
      val thm3 = CONV_RULE (RHS_CONV (computeLib.CBV_CONV ds_direct_cs)) thm2
   in
      thm3
   end

fun ds_TURN_EQUATIONS_TAC l1 l2 =
   CONV_TAC (ds_TURN_EQUATIONS_CONV l1 l2);

fun ds_AUTO_DIRECT_EQUATIONS_CONV t =
   let
      val (_, _, pf, _,pf', _) = dest_LIST_DS_ENTAILS t;
      val (pfL, _) = strip_cons pf;
      val (pfL', _) = strip_cons pf';

      fun dest_eq_uneq sf = dest_pf_unequal sf handle _ => dest_pf_equal sf;

      val l1 = map (fn sf => (should_turn (dest_eq_uneq sf) handle _ => false)) pfL;
      val l2 = map (fn sf => (should_turn (dest_eq_uneq sf) handle _ => false)) pfL';
   in
      ds_TURN_EQUATIONS_CONV l1 l2 t
   end;





(* Example


val t = ``LIST_DS_ENTAILS ([], [(e1,e2);(e9,e9)]) ((pf1::pf_equal e e::pf_true::pf2::pf_equal e' e'::pf3::l),(sf1::sf2::(sf_ls f e e) ::sf3::(sf_points_to e [(f, e)])::(sf_bin_tree (f1, f2) dse_nil)::(sf_tree fL e2 e2)::(sf_ls f e1 e2)::l2)) ((pf1::pfx::pf_equal e e::pf2::pf_equal e' e'::pf3::l),(sf1::sf2::(sf_ls f e2 e2) ::sf3::sf_emp::(sf_points_to e [(f, e)])::(sf_bin_tree (f1, f2) e)::(sf_tree fL e1 e2)::(sf_ls f e e)::l3))``


val t = ``LIST_DS_ENTAILS ([], [])  ([], []) ([], [sf_ls f e e])``;

val t3 =
    ``LIST_DS_ENTAILS ([dse_var 0; dse_var 2],[(dse_var 3,dse_nil)])
        ([pf_unequal (dse_var 0) (dse_var 3);
          pf_unequal (dse_var 4) (dse_var 5);
          pf_unequal (dse_var 3) (dse_var 2)],[])
        ([],[sf_ls "f" (dse_var 2) (dse_var 2)])``
*)

fun bool_list2term_list___filter [] (l1, l2) = (l1, l2) |
    bool_list2term_list___filter (true::l) (l1, l2) =
      bool_list2term_list___filter l (T::(append l2 l1), []) |
    bool_list2term_list___filter (false::l) (l1, l2) =
      bool_list2term_list___filter l (l1, F::l2);


fun bool_list2term___filter l =
   let
      val (l1, _) = bool_list2term_list___filter l ([], []);
      val l2 = rev l1;
   in
      (mk_list (l2, bool), l2 = [])
   end;






fun is_pre_trivial t =
   let
      val (e1, e2) = pairLib.dest_pair t;
   in
      (e1 = e2)
   end handle _ => false;


fun get_pf_trival_filter pf =
let
   val (pfL, _) = strip_cons pf;
   val fL = map is_pf_trivial pfL;
in
   bool_list2term___filter fL
end;

fun get_sf_trival_filter sf =
let
   val (sfL, _) = strip_cons sf;
   val fL = map is_sf_trivial sfL;
in
   bool_list2term___filter fL
end;

fun get_pre_trival_filter c2 =
let
   val (pre, _) = strip_cons c2;
   val fL = map is_pre_trivial pre;
in
   bool_list2term___filter fL
end;



val reflexive_cs = computeLib.bool_compset();
val _ = computeLib.add_thms [POS_FILTER_THM, PF_TRIVIAL_FILTER_PRED_def,
   SF_TRIVIAL_FILTER_PRED_THM, pairTheory.FST, pairTheory.SND] reflexive_cs;


fun ds_inference_REMOVE_TRIVIAL___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;

      val (f1, p1) = get_pre_trival_filter c2;
      val (f2, p2) = get_pf_trival_filter pf;
      val (f3, p3) = get_sf_trival_filter sf;
      val (f4, p4) = get_pf_trival_filter pf';
      val (f5, p5) = get_sf_trival_filter sf';

      val _ = if p1 andalso p2 andalso p3 andalso p4 andalso p5 then SMALLFOOT_ERR "Nothing trivial found!" else ();

      val thm = ISPECL [f1, f2,f3,f4, f5, c1, c2, pf, sf, pf', sf'] INFERENCE_TRIVIAL_FILTER;
      val thm2 = CONV_RULE (RHS_CONV (computeLib.CBV_CONV reflexive_cs)) thm;
   in
      thm2
   end





(* Example
val t = ``LIST_DS_ENTAILS (e1::c1,c2) ([pf1;pf_unequal e3 e;pf2],[sf_points_to e1 []; sf_points_to dse_nil []]) ([],[])``
val t = ``LIST_DS_ENTAILS (e1::e45::e6::e45::dse_nil::c1,c2) ([pf1;pf_unequal e e;pf2],[sf_points_to e3 []; sf_points_to dse_nil [];sf_bin_tree (f1, f2) e1]) ([],[])``
*)

val inconsistent_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [SWAP_REWRITES] inconsistent_cs;

fun ds_inference_INCONSISTENT___CONV___UNEQUAL t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (pfL, _) = strip_cons pf;
      val pfOption = find_in_list is_pf_unequal_refl pfL
      val _ = if isSome pfOption then () else SMALLFOOT_ERR "No disequation (e = e) found!";
      val (n, uneq) = valOf pfOption;
      val (e, _) = dest_pf_unequal uneq;

      val thm = ISPECL [numLib.term_of_int n, e, c1, c2, pf, sf, pf', sf'] INFERENCE_INCONSISTENT_UNEQUAL___EVAL;
      val thm2 = CONV_RULE (computeLib.CBV_CONV inconsistent_cs) thm;
      val _ = if ((concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      EQT_INTRO thm2
   end


fun ds_inference_INCONSISTENT___CONV___NIL_POINTS_TO t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val pfOption = find_in_list is_points_to_nil sfL
      val _ = if isSome pfOption then () else SMALLFOOT_ERR "Nothing found!";
      val (n, uneq) = valOf pfOption;
      val (_, a, _, _) = dest_sf_points_to uneq;

      val thm = ISPECL [numLib.term_of_int n, a, c1, c2, pf, sf, pf', sf'] INFERENCE_INCONSISTENT___NIL_POINTS_TO___EVAL;
      val thm2 = CONV_RULE (computeLib.CBV_CONV inconsistent_cs) thm;
      val _ = if ((concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      EQT_INTRO thm2
   end


fun find_entry n e [] = NONE |
    find_entry n e (h::l) = if (e = h) then (SOME n) else
                            find_entry (n+1) e l;

fun find_double_entry n [] = NONE |
    find_double_entry n (h::l) =
      let
         val mOpt = (find_entry (n+1) h l);
      in
         if (isSome mOpt) then (SOME (n, valOf mOpt, h)) else find_double_entry (n+1) l
      end;

fun find_match n cL [] = NONE |
    find_match n cL (h::l) =
      let
         val (i, ex, d) =
            let
               val (ex, a, _, _) = dest_sf_points_to h;
            in
               (0, ex, a)
            end handle _ =>
            let
               val (_, _, ex, fL) = dest_sf_bin_tree h;
            in
               (1, ex, fL)
            end;
         val cOpt = find_entry 0 ex cL;
      in
         if (isSome cOpt) then SOME (n, valOf cOpt, i, ex, d) else
         find_match (n+1) cL l
      end handle _ => find_match (n+1) cL l;



fun ds_inference_INCONSISTENT___CONV___precondition_POINTS_TO_BIN_TREE t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val (c1L, _) = strip_cons c1;
      val _ = if ((c1L = []) orelse (sfL = [])) then SMALLFOOT_ERR "Nothing found!" else ();


      val resOption = find_match 0 c1L sfL;
      val _ = if isSome resOption then () else SMALLFOOT_ERR "Nothing found!";
      val (n, m, i, e, d) = valOf resOption;

      val inf = if i = 0 then
                  INFERENCE_INCONSISTENT___precondition_POINTS_TO___EVAL
                else
                  INFERENCE_INCONSISTENT___precondition_BIN_TREE___EVAL;

      val thm = ISPECL [numLib.term_of_int m, numLib.term_of_int n, e, d, c1, c2, pf, sf, pf', sf'] inf;
      val thm2 = CONV_RULE (computeLib.CBV_CONV inconsistent_cs) thm;
      val _ = if ((concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      EQT_INTRO thm2
   end;


fun ds_inference_INCONSISTENT___CONV___precondition_dse_nil t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (c1L, _) = strip_cons c1;


      val cOption = find_in_list is_dse_nil c1L;
      val _ = if isSome cOption then () else SMALLFOOT_ERR "Nothing found!";
      val (n, _) = valOf cOption;

      val thm = ISPECL [numLib.term_of_int n, c1, c2, pf, sf, pf', sf']
         INFERENCE_INCONSISTENT___precondition_dse_nil;
      val thm2 = CONV_RULE (computeLib.CBV_CONV inconsistent_cs) thm;
      val _ = if ((concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      EQT_INTRO thm2
   end;


fun ds_inference_INCONSISTENT___CONV___precondition_not_all_distinct t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (c1L, _) = strip_cons c1;


      val cOption = find_double_entry 0 c1L;
      val _ = if isSome cOption then () else SMALLFOOT_ERR "Nothing found!";
      val (n, m, x) = valOf cOption;

      val thm = ISPECL [numLib.term_of_int n, numLib.term_of_int m, x, c1, c2, pf, sf, pf', sf']
         INFERENCE_INCONSISTENT___precondition_distinct;
      val thm2 = CONV_RULE (computeLib.CBV_CONV inconsistent_cs) thm;
      val _ = if ((concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      EQT_INTRO thm2
   end;


val ds_inference_INCONSISTENT___CONV =
   ds_inference_INCONSISTENT___CONV___UNEQUAL ORELSEC
   ds_inference_INCONSISTENT___CONV___NIL_POINTS_TO ORELSEC
   ds_inference_INCONSISTENT___CONV___precondition_dse_nil ORELSEC
   ds_inference_INCONSISTENT___CONV___precondition_POINTS_TO_BIN_TREE ORELSEC
   ds_inference_INCONSISTENT___CONV___precondition_not_all_distinct;



(* Example
val t = ``LIST_DS_ENTAILS ([pf1;pf_unequal e e;pf2],[]) ([],[])``
set_goal ([], t)
*)

fun ds_inference_AXIOM___CONV t = EQT_INTRO (PART_MATCH (I) INFERENCE_AXIOM t);




(* Example
val t = ``LIST_DS_ENTAILS ([dse_var 4], [(dse_var 1, dse_var 4)]) ([pf_unequal (dse_var 4) dse_nil;pf_equal x1 (dse_var 1); pf_equal (dse_var 1) (dse_var 2)],sfL) ([pf_equal (dse_var 4) (dse_var 2)],[sf_points_to (dse_var 5) [(f, (dse_var 1))]])``

*)




val subst_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [PF_SUBST_def, MAP, SF_SUBST_THM, DS_VAR_SUBST_def, DS_VAR_SUBST_NIL,
   SWAP_REWRITES, pairTheory.FST, pairTheory.SND]
   subst_cs;


fun is_pf_equal_subst pf =
   (let
      val (e1, e2) = dest_pf_equal pf;
   in
      (not (e1 = e2)) andalso ((is_dse_var e1) orelse (is_dse_var e2))
   end) handle _ => false

fun ds_inference_SUBSTITUTION___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (pfL, _) = strip_cons pf;
      val pfOption = find_in_list is_pf_equal_subst pfL
      val _ = if isSome pfOption then () else SMALLFOOT_ERR "No equation (var s = e) found!";
      val (n, uneq) = valOf pfOption;
      val (e1, e2) = dest_pf_equal uneq;
      val (inf, e1, e2) = if (is_dse_var e1) then (INFERENCE_SUBSTITUTION___EVAL1, e1, e2) else
                              (INFERENCE_SUBSTITUTION___EVAL2, e2, e1);

      val thm = ISPECL [numLib.term_of_int n, e2, dest_dse_var e1, c1, c2, pf, sf, pf', sf'] inf;
      val thm2 = CONV_RULE (computeLib.CBV_CONV subst_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end;






(*example
val t = ``LIST_DS_ENTAILS ([e7;e5;e4;e6], []) ([pf_unequal e1 e2;pf1;pf_unequal dse_nil e5;pf2;pf_unequal e1 e2],sfL) ([pf5;pf_unequal e6 e7;pf4;pf1;pf_equal e2 e1;pf_unequal dse_nil e4;pf_unequal e2 e1],pfL')``
*)


fun find_sf_eq_in_list n ex [] = NONE |
    find_sf_eq_in_list n ex (h::l) =
      let
         val (p1, p2) = pf_eq ex h;
      in
         if p1 then (SOME (n, p2)) else
         find_sf_eq_in_list (n+1) ex l
      end


local

   fun check_in_pre_pf l1 h =
      let
         val cOpt = find_sf_eq_in_list 0 h l1;
         val (n, turn) = valOf cOpt;
         val cond = (list_mk_comb (``hyp_in_precond``, [if turn then T else F, numLib.term_of_int n]));
      in
         SOME cond
      end handle _ => NONE;


   fun check_in_self_pf n l2 h =
      let
         val cOpt = find_sf_eq_in_list 0 h l2;
         val (m, turn) = valOf cOpt;
         val _ = if (m < n) then () else SMALLFOOT_ERR "To late";
         val cond = (list_mk_comb (``hyp_in_self``, [if turn then T else F, numLib.term_of_int m]));
      in
         SOME cond
      end handle _ => NONE;


   fun check_c_dse_nil cL h =
      let
         val (e1, e2) = dest_pf_unequal h;
         val (e1, turn) = if is_dse_nil e2 then (e1, true) else
                          if is_dse_nil e1 then (e2, false) else
                          SMALLFOOT_ERR "no dse_nil found";

         val cOpt = find_entry 0 e1 cL;
         val n = valOf cOpt;
      in
         SOME (list_mk_comb (``hyp_c_dse_nil``, [if turn then T else F, numLib.term_of_int n]))
      end  handle _ => NONE;


   fun check_c_unequal cL h =
      let
         val (e1, e2) = dest_pf_unequal h;
         val _ = if (e1 = e2) then SMALLFOOT_ERR "preserve for inconsistence" else ();

         val n1 = valOf (find_entry 0 e1 cL);
         val n2 = valOf (find_entry 0 e2 cL);
      in
         SOME (list_mk_comb (``hyp_c_unequal``, [numLib.term_of_int n1, numLib.term_of_int n2]))
      end  handle _ => NONE;



   fun get_hypothesis_filter_helper c1 l1 l2 n [] = [] |
      get_hypothesis_filter_helper c1 l1 l2 n (h::l) =
         let
            val condOpt = check_in_pre_pf l1 h;
            val condOpt = if isSome (condOpt) then condOpt else
                          check_in_self_pf n l2 h;
            val condOpt = if isSome (condOpt) then condOpt else
                          check_c_dse_nil c1 h;
            val condOpt = if isSome (condOpt) then condOpt else
                          check_c_unequal c1 h;
            val cond = if isSome condOpt then valOf condOpt else ``hyp_keep``;
         in
            cond::(get_hypothesis_filter_helper c1 l1 l2 (n+1) l)
         end;

   fun remove_keep l1 l2 [] = l1 |
       remove_keep l1 l2 (h::l) =
         if (same_const ``hyp_keep`` h) then
            remove_keep l1 (h::l2) l
         else
            remove_keep (h::(append l2 l1)) [] l


in
   fun get_hypothesis_filter c1 l1 l2 =
      let
         val f = get_hypothesis_filter_helper c1 l1 l2 0 l2;
         val rf = remove_keep [] [] f;
         val fL = rev rf;
         val p = (fL = []);
         val ft = mk_list (fL, ``:hypothesis_rule_cases``);
      in
         (ft, p)
      end
end;



val hypothesis_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [HYPOTHESIS_RULE_MAP_def, SWAP_REWRITES, PF_TURN_EQ_def, HYPOTHESIS_RULE_COND_THM]
   hypothesis_cs;

fun ds_inference_HYPOTHESIS___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (cL, _) = strip_cons c1;
      val (pfL, _) = strip_cons pf;
      val (pfL', _) = strip_cons pf';
      val (f1, p1) = get_hypothesis_filter cL [] pfL;
      val (f2, p2) = get_hypothesis_filter cL pfL pfL';

      val _ = if (p1 andalso p2) then SMALLFOOT_ERR "No common formulas found!" else ();

      val thm = ISPECL [f1, f2, c1, c2, pf, sf, pf', sf']
         INFERENCE_HYPOTHESIS___EVAL;
      val thm2 = CONV_RULE (RHS_CONV (computeLib.CBV_CONV hypothesis_cs)) thm;
   in
      thm2
   end;








(*example
val t = ``LIST_DS_ENTAILS ([], []) (pfL,[sf1;sf2;sf_points_to e1 [("f", b);("g", c)];sf_points_to e2 [("f", b)];sf_bin_tree ("f", "g") e3; sf_bin_tree ("g", "f") e4;sf_points_to e3 [("f", b);("g", c)];sf5;sf_ls "f" e1 e3]++sfL) (pfL',[sf5;sf_points_to e1 [("g", c);("f", b)];sf_points_to e1 [("f", b);("h", c)];sf_points_to e2 [("f", b)];sf_ls "f" e1 e3;sf_points_to e3 [("f", b);("g", c)];sf4;sf_bin_tree ("f", "g") e3; sf_bin_tree ("f", "g") e4;sf1]++sfL)``

val t = rhs (concl (SIMP_CONV list_ss [] t))
*)

local
   fun find_pairs_helper P n1 n2 l [] l2 r = r
   | find_pairs_helper P n1 n2 l (e::l1) [] r =
      find_pairs_helper P (n1+1) 0 l l1 l r
   | find_pairs_helper P n1 n2 l (e1::l1) (e2::l2) r =
         if ((P e1 e2) handle _ => false) then
            find_pairs_helper P n1 (n2+1) l (e1::l1) l2 ((n1, e1, n2, e2)::r)
         else
            find_pairs_helper P n1 (n2+1) l (e1::l1) l2 r
in
   fun find_pairs P l1 l2 =
       find_pairs_helper P 0 0 l2 l1 l2 [];
end


local
   fun adapt_pair_list_to_deletes___map n1 n2 [] = [] |
       adapt_pair_list_to_deletes___map n1 n2 ((n1', e1, n2', e2)::l) =
         let val l' = adapt_pair_list_to_deletes___map n1 n2 l in
         if (n1 = n1') orelse (n2 = n2') then
            l'
         else
            (if n1' > n1 then (n1'-1) else n1', e1,
             if n2' > n2 then (n2'-1) else n2', e2)::l'
         end;

   fun adapt_pair_list_to_deletes___helper l1 [] = l1 |
       adapt_pair_list_to_deletes___helper l1 ((n1, e1, n2, e2)::l) =
       adapt_pair_list_to_deletes___helper ((n1, e1, n2, e2)::l1) (adapt_pair_list_to_deletes___map n1 n2 l);
in

fun adapt_pair_list_to_deletes l = rev (adapt_pair_list_to_deletes___helper [] l);

end;


fun pred_frame___points_to sf1 sf2 =
   let
      val (e1, _, a1, aL1) = dest_sf_points_to sf1;
      val (e2, _, a2, aL2) = dest_sf_points_to sf2;
   in
      (e1 = e2) andalso (aL1 = aL2) andalso
      (all (fn x => mem x a1) a2)
   end;


val frame_cs = reduceLib.num_compset ();
val _ = listSimps.list_rws frame_cs;
val _ = computeLib.add_thms [SWAP_REWRITES, pairTheory.FST, listTheory.ALL_DISTINCT] frame_cs;
val _ = computeLib.add_conv (``$=``, 2, stringLib.string_EQ_CONV) frame_cs;
val _ = computeLib.add_conv (``$=``, 2, stringLib.char_EQ_CONV) frame_cs;



fun ds_inference_FRAME___SINGLE_CONV___sf_points_to (n1, sf1, n2, sf2) t =
   let
      val (e1, a1, _, _) = dest_sf_points_to sf1;
      val (_, a2, _, _) = dest_sf_points_to sf2;
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;

      val thm = ISPECL [e1, numLib.term_of_int n1, a1, numLib.term_of_int n2, a2, c1, c2, pf, sf, pf', sf']
         INFERENCE_STAR_INTRODUCTION___points_to___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV frame_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No conversion";
   in
      thm2
   end;


fun ds_inference_FRAME___CONV___sf_points_to t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';

      val pairList = find_pairs pred_frame___points_to sfL sfL';
      val _ = if (pairList = []) then SMALLFOOT_ERR "Nothing found" else ();

      val adapt_pairList = adapt_pair_list_to_deletes (rev pairList)
   in
      EVERY_CONV (map ds_inference_FRAME___SINGLE_CONV___sf_points_to adapt_pairList) t
   end;


fun pred_frame___list sf1 sf2 =
   (sf1 = sf2) andalso (is_sf_ls sf1);


fun ds_inference_FRAME___SINGLE_CONV___sf_ls (n1, sf1, n2, sf2) t =
   let
      val (f, e1, e2) = dest_sf_ls sf1;
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;

      val thm = ISPECL [f, e1, e2, numLib.term_of_int n1, numLib.term_of_int n2, c1, c2, pf, sf, pf', sf']
         INFERENCE_STAR_INTRODUCTION___list___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV frame_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No conversion";
   in
      thm2
   end;


fun ds_inference_FRAME___CONV___sf_ls t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';

      val pairList = find_pairs pred_frame___list sfL sfL';
      val _ = if (pairList = []) then SMALLFOOT_ERR "Nothing found" else ();

      val adapt_pairList = adapt_pair_list_to_deletes (rev pairList);
   in
      EVERY_CONV (map ds_inference_FRAME___SINGLE_CONV___sf_ls adapt_pairList) t
   end;



fun pred_frame___bin_tree sf1 sf2 =
   let
      val (f11, f12, e1, _) = dest_sf_bin_tree sf1;
      val (f21, f22, e2, _) = dest_sf_bin_tree sf2;
   in
      (e1 = e2) andalso
      (((f11 = f21) andalso (f12 = f22)) orelse
       ((f12 = f21) andalso (f11 = f22)))
   end;



fun ds_inference_FRAME___SINGLE_CONV___sf_bin_tree (n1, sf1, n2, sf2) t =
   let
      val (f11, f12, e1, _) = dest_sf_bin_tree sf1;
      val (f21, f22, _, _) = dest_sf_bin_tree sf2;
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;

      val thm = ISPECL [e1, f11, f12, f21, f22, numLib.term_of_int n1, numLib.term_of_int n2, c1, c2, pf, sf, pf', sf']
         INFERENCE_STAR_INTRODUCTION___bin_tree___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV frame_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No conversion";
   in
      thm2
   end;

fun ds_inference_FRAME___CONV___sf_bin_tree t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';

      val pairList = find_pairs pred_frame___bin_tree sfL sfL';
      val _ = if (pairList = []) then SMALLFOOT_ERR "Nothing found" else ();

      val adapt_pairList = adapt_pair_list_to_deletes (rev pairList);
   in
      EVERY_CONV (map ds_inference_FRAME___SINGLE_CONV___sf_bin_tree adapt_pairList) t
   end;


val ds_inference_FRAME___CONV =
   (TRY_CONV ds_inference_FRAME___CONV___sf_points_to) THENC
   (TRY_CONV ds_inference_FRAME___CONV___sf_ls) THENC
   (TRY_CONV ds_inference_FRAME___CONV___sf_bin_tree)




fun ds_inference_FRAME___IMPL_CONV___tail t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, sfLr) = strip_cons sf;
      val (sfL', sfLr') = strip_cons sf';

      val _ = if (is_nil sfLr orelse not (sfLr = sfLr')) then SMALLFOOT_ERR "Nothing found" else ();

      val list_type = dest_list_type (type_of sfLr)
      val sfLt = mk_list (sfL, list_type);
      val sfLt' = mk_list (sfL', list_type);

      val thm = ISPECL [sfLr, c1,c2, pf, sfLt, pf', sfLt'] INFERENCE_STAR_INTRODUCTION___EVAL1
      val thm2 = CONV_RULE (computeLib.CBV_CONV frame_cs) thm;
      val _ = if (snd (dest_imp (concl thm2)) = t) then () else SMALLFOOT_ERR "No imp-conversion";
   in
      thm2
   end;


fun ds_inference_FRAME___IMPL_CONV___single_step ((n1, x, n2, _),in_thm) =
let
   val (t1, t2) = dest_imp (concl in_thm);

   val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t1;

   val thm = ISPECL [x, numLib.term_of_int n1, numLib.term_of_int n2, c1, c2, pf, sf, pf', sf'] INFERENCE_STAR_INTRODUCTION___EVAL2;
   val thm2 = CONV_RULE (computeLib.CBV_CONV frame_cs) thm;
   val thm3 = IMP_TRANS thm2 in_thm
in
   thm3
end;

val imp_thm = prove (``!a. a ==> a``, SIMP_TAC std_ss []);

fun ds_inference_FRAME___IMPL_CONV___pair t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';

      val pairList = find_pairs (fn x => fn y => x = y) sfL sfL';
      val _ = if (pairList = []) then SMALLFOOT_ERR "Nothing found" else ();
      val adapt_pairList = adapt_pair_list_to_deletes (rev pairList);

      val in_thm = ISPEC t imp_thm;
      val thm = foldl ds_inference_FRAME___IMPL_CONV___single_step in_thm adapt_pairList;
   in
      thm
   end;


fun ds_inference_FRAME___IMPL_CONV t =
   let
      val eq_thm = (SOME (ds_inference_FRAME___CONV t)) handle _ => NONE
      val t2 = if isSome eq_thm then (rhs (concl (valOf eq_thm))) else t;
      val imp1_thm = (SOME (ds_inference_FRAME___IMPL_CONV___tail t2)) handle _ => NONE;
      val t3 = if isSome imp1_thm then (fst (dest_imp (concl (valOf imp1_thm)))) else t2;
      val imp2_thm = (SOME (ds_inference_FRAME___IMPL_CONV___pair t3)) handle _ => NONE;

      val imp_thm = if not (isSome imp2_thm) then imp1_thm else
                    if not (isSome imp1_thm) then imp2_thm else
                    SOME (IMP_TRANS (valOf imp2_thm) (valOf imp1_thm));

      val thm = if not (isSome imp_thm) then eq_thm else
               if not (isSome eq_thm) then imp_thm else
               SOME (CONV_RULE (REWRITE_CONV [GSYM (valOf eq_thm)]) (valOf imp_thm))
   in
      valOf thm
   end;


(*example
val t = ``LIST_DS_ENTAILS ([e6], []) ([pf_unequal e1 dse_nil; pf_unequal dse_nil e3;pf_unequal e3 e2],[sf_points_to e1 [("g", e5)];sf_points_to e3 [];sf_ls f e1 e2;sf_ls f e2 e3;sf_points_to e4 []]) ([],[])``
*)


val pointsto_skip_term = ``pointsto_skip``;
val pointsto_pointsto_term = ``pointsto_pointsto``;
val pointsto_tree_term = ``pointsto_tree``;


fun get_points_to_list_cond_filter pfL sf =
   if is_sf_points_to sf then pointsto_pointsto_term else
   let
      val (_, _, es, e) = dest_sf_tree_ext sf;
      val (n, uneqt) = valOf (find_in_list (is_uneq_2 es e) pfL)
      val (e', es') = dest_pf_unequal uneqt
      val turn = not (es' = es);
   in
      list_mk_comb (pointsto_tree_term, [if turn then T else F, numLib.term_of_int n])
   end handle _ => pointsto_skip_term;


fun check_unequal_dse_nil_is_necessary cL pfL ex =
   not (isSome (find_in_list (is_uneq_nil ex) pfL)) andalso
   not (isSome (find_entry 0 ex cL));

fun get_points_to_list_cond_exp sf =
   let
      val (e1, _, _, _) = dest_sf_points_to sf;
   in
   e1
   end handle _ =>
   let
      val (_, _, _, e1) = dest_sf_tree_ext sf;
   in
      e1
   end;


fun map_restrict_points_to_list_cond_filter pfL cL [] _ = [] |
    map_restrict_points_to_list_cond_filter pfL cL (f::fL) [] = [] |
    map_restrict_points_to_list_cond_filter pfL cL (f::fL) (sf::sfL) =
   let
      val ex = get_points_to_list_cond_exp sf;
      val f' = if check_unequal_dse_nil_is_necessary cL pfL ex then f else pointsto_skip_term;
   in
      (f' :: (map_restrict_points_to_list_cond_filter pfL (ex::cL) fL sfL))
   end;




val sf_points_to_list_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms
[SF_POINTS_TO_LIST_def,
   SAFE_FILTER_THM, SF_POINTS_TO_LIST_COND_FILTER_def, SF_POINTS_TO_LIST_COND_THM,
   SWAP_REWRITES] sf_points_to_list_cs;
val _ = listSimps.list_rws sf_points_to_list_cs;


fun ds_inference_NIL_NOT_LVAL___CONV___overeager over t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (cL, _) = strip_cons c1;
      val (pfL, _) = strip_cons pf;
      val (sfL, _) = strip_cons sf;

      val f = map (get_points_to_list_cond_filter pfL) sfL;
      val f = if over then f else
              map_restrict_points_to_list_cond_filter pfL cL f sfL;

      val p = exists (fn x => not (x = pointsto_skip_term)) f;
      val _ = if not p then SMALLFOOT_ERR "No new facts!" else ()

      val ft = mk_list (f, type_of (hd f));

      val thm = ISPECL [ft, c1, c2, pf, sf, pf', sf'] INFERENCE_NIL_NOT_LVAL___EVAL
      val thm2 = CONV_RULE (RHS_CONV (computeLib.CBV_CONV sf_points_to_list_cs)) thm;
   in
      thm2
   end;


val ds_inference_NIL_NOT_LVAL___CONV =
   ds_inference_NIL_NOT_LVAL___CONV___overeager false;






(*example
val t = ``LIST_DS_ENTAILS ([e2;e1;e4;e6;e5], []) ([pf_unequal e3 e2],[sf_points_to e1 x;sf_points_to e2 x;sf_points_to e3 x;sf_points_to e4 x;sf_ls f e3 e2]) ([],[])``
*)


val product_term = ``
                 (LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL)
                    c1) ++
                  DISJOINT_LIST_PRODUCT
                    (SF_POINTS_TO_LIST_COND_FILTER pfL f2 (sfL:('c, 'b, 'a) ds_spatial_formula list))``;

val partial_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [SF_POINTS_TO_LIST_def,
   SAFE_FILTER_THM, LIST_PRODUCT_def, DISJOINT_LIST_PRODUCT_def, pairTheory.UNCURRY_DEF,
   SF_POINTS_TO_LIST_COND_FILTER_def, SF_POINTS_TO_LIST_COND_THM, SWAP_REWRITES] partial_cs
val _ = listSimps.list_rws partial_cs;



fun EVAL___DISJOINT_LIST_PRODUCT c1 pf sf f2 =
   let
      val (_, typeL) = dest_type (dest_list_type (type_of sf))
      val product_term = inst [alpha |-> el 3 typeL,
                               beta |-> el 2 typeL,
                               gamma |-> el 1 typeL] product_term;
      val t = subst [mk_var("pfL",type_of pf) |-> pf,
             mk_var("c1",type_of c1) |-> c1,
             mk_var("f2",type_of f2) |-> f2,
             mk_var("sfL",type_of sf) |-> sf] product_term;
   in
      computeLib.CBV_CONV partial_cs t
   end;


fun check_unequal_is_necessary cL pfL (e1, e2) =
   not (isSome (find_in_list (is_uneq_2 e1 e2) pfL)) andalso
   ((e1 = e2) orelse
      not (isSome (find_entry 0 e1 cL)) orelse
      not (isSome (find_entry 0 e2 cL)));



fun get_uneq_filter overeager cL pfL r l' [] = r |
    get_uneq_filter overeager cL pfL r l' ((e1,e2)::l) =
    let
      val necessary =
         overeager orelse (
         (not (mem (e1,e2) l')) andalso
         (not (mem (e2,e1) l')) andalso
         check_unequal_is_necessary cL pfL (e1,e2));
    in
      (get_uneq_filter overeager cL pfL (necessary::r) (if necessary then (e1,e2)::l' else l') l)
    end;



fun ds_inference_PARTIAL___CONV___overeager over t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (cL, _) = strip_cons c1;
      val (pfL, _) = strip_cons pf;
      val (sfL, _) = strip_cons sf;

      val f2L = map (get_points_to_list_cond_filter pfL) sfL;
      val f2 = mk_list (f2L, Type `:pointsto_cases`);


      val SF_POINTS_TO_LIST___THM = EVAL___DISJOINT_LIST_PRODUCT c1 pf sf f2;
      val (points_list, _) = dest_list (rhs (concl SF_POINTS_TO_LIST___THM));
      val points_list = map pairLib.dest_pair points_list;

      val pre_f = get_uneq_filter over cL pfL [] [] points_list;
      val (f, p) = bool_list2term___filter (rev pre_f);
      val _ = if p then SMALLFOOT_ERR "No new facts!" else ()

      val thm = ISPECL [f, f2, c1, c2, pf, sf, pf', sf'] INFERENCE_PARTIAL___EVAL
      val thm2 = CONV_RULE (RHS_CONV (REWRITE_CONV [SF_POINTS_TO_LIST___THM])) thm;
      val thm3 = CONV_RULE (RHS_CONV (computeLib.CBV_CONV partial_cs)) thm2;
   in
      thm3
   end;


val ds_inference_PARTIAL___CONV = ds_inference_PARTIAL___CONV___overeager false;









(*example
val t = ``LIST_DS_ENTAILS ([e1;e2],[(e2,e3);(e3,e4);(e4,e2);(e9,e10);(e4,e2);(e9,e10)]) ([pf_unequal e3 e4;pf1;pf_unequal e2 e4; pf3],[sf1;sf_ls "f" e1 e2;sf2]) ([],[])``
*)

fun find_strengthen_uneq_pairs___helper accu n1 n2 pfLorg [] pfL = accu
  | find_strengthen_uneq_pairs___helper accu n1 n2 pfLorg ((e1,e2)::cL) [] =
    find_strengthen_uneq_pairs___helper accu (n1+1) 0 pfLorg cL pfLorg
  | find_strengthen_uneq_pairs___helper accu n1 n2 pfLorg ((e1,e2)::cL) (pf::pfL) =
    let val accu' = (let
      val (e1', e2') = dest_pf_unequal pf;
    in
      if ((e1 = e1') andalso (e2 = e2')) then (n1,n2,false,e1,e2)::accu else
      if ((e2 = e1') andalso (e1 = e2')) then (n1,n2,true,e1,e2)::accu else
      accu
    end handle _ => accu) in
      find_strengthen_uneq_pairs___helper accu' n1 (n2+1) pfLorg ((e1,e2)::cL) pfL
    end;

fun find_strengthen_uneq_pairs cL pfL =
   find_strengthen_uneq_pairs___helper [] 0 0 pfL cL pfL;

val strengthen_cs = reduceLib.num_compset ();
val _ = computeLib.add_thms [SWAP_REWRITES] strengthen_cs;


fun ds_inference_PRECONDITION_STRENGTHEN___SINGLE_CONV (n1,n2,turn,e1,e2) t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;

      val inf = if turn then INFERENCE___precondition_STRENGTHEN_2 else
                  INFERENCE___precondition_STRENGTHEN_1;

      val thm = ISPECL [numLib.term_of_int n2, numLib.term_of_int n1, e1, e2, c1, c2, pf, sf, pf', sf'] inf;
      val thm2 = CONV_RULE (computeLib.CBV_CONV strengthen_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No conversion";
   in
      thm2
   end;


fun ds_inference_PRECONDITION_STRENGTHEN___CONV___unequal t =
   let
      val (_, c2, pf, _, _, _) = dest_LIST_DS_ENTAILS t;
      val (cL, _) = strip_cons c2;
      val cL = map pairLib.dest_pair cL;
      val (pfL, _) = strip_cons pf;

      (*notice the reverse order*)
      val pairs_list = find_strengthen_uneq_pairs cL pfL;
   in
      EVERY_CONV (map ds_inference_PRECONDITION_STRENGTHEN___SINGLE_CONV pairs_list) t
   end;





fun find_strengthen_eq_pair___helper n1 n2 pfL [] cfL = NONE
  | find_strengthen_eq_pair___helper n1 n2 pfL ((e1,e2)::cL) [] =
    find_strengthen_eq_pair___helper (n1+1) (n1+2) pfL cL (tl cL)
  | find_strengthen_eq_pair___helper n1 n2 pfL ((e1,e2)::cL) ((e1',e2')::cL') =
    let
      val cond = (e1 = e1') andalso (e2 = e2') andalso
                 not (isSome (find_in_list (is_eq_2 e1 e2) pfL)) handle _ => false;
    in
      if cond then SOME (n1, n2, e1, e2) else
         find_strengthen_eq_pair___helper n1 (n2+1) pfL ((e1,e2)::cL) cL'
    end;

fun find_strengthen_eq_pair cL pfL =
   valOf (find_strengthen_eq_pair___helper 0 1 pfL cL (tl cL));

fun ds_inference_PRECONDITION_STRENGTHEN___CONV___equal t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (cL, _) = strip_cons c2;
      val cL = map pairLib.dest_pair cL;
      val (pfL, _) = strip_cons pf;


      val (n1,n2,e1,e2) = find_strengthen_eq_pair cL pfL handle _ =>
         SMALLFOOT_ERR "Not applicable";

      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, e1, e2, c1, c2, pf, sf, pf', sf']
         INFERENCE___precondition_NOT_DISTINCT_EQ___EVAL;
      val thm2 = CONV_RULE (computeLib.CBV_CONV strengthen_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end


fun find_strengthen_eq_precondition___helper n cL1 [] = NONE
  | find_strengthen_eq_precondition___helper n cL1 ((e1,e2)::cL2) =
    let
      val n1 = valOf (find_entry 0 e1 cL1);
    in
      SOME (n1, n, e1, e2)
    end handle _ =>
      find_strengthen_eq_precondition___helper (n+1) cL1 (cL2);

fun find_strengthen_eq_precondition cL1 cL2 =
   valOf (find_strengthen_eq_precondition___helper 0 cL1 cL2);


fun ds_inference_PRECONDITION_STRENGTHEN___CONV___precondition t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (cL1, _) = strip_cons c1;
      val (cL2, _) = strip_cons c2;
      val cL2 = map pairLib.dest_pair cL2;


      val (n1,n2,e1,e2) = find_strengthen_eq_precondition cL1 cL2 handle _ =>
         SMALLFOOT_ERR "Not applicable";


      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, e1, e2, c1, c2, pf, sf, pf', sf']
         INFERENCE___precondition_precondition_EQ___EVAL;
      val thm2 = CONV_RULE (computeLib.CBV_CONV strengthen_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end

val ds_inference_PRECONDITION_STRENGTHEN___CONV =
    ds_inference_PRECONDITION_STRENGTHEN___CONV___unequal THENC
    (REPEATC ds_inference_PRECONDITION_STRENGTHEN___CONV___equal) THENC
    (REPEATC ds_inference_PRECONDITION_STRENGTHEN___CONV___precondition);



(*example
val t = ``LIST_DS_ENTAILS ([e1],[(e2,e3);(e3,e4);(e4,e2);(e9,e10);(e4,e2);(e9,e10)]) ([pf_unequal e3 e4;pf1;pf_unequal e2 e4; pf3],[sf_ls "g" e5 e7; sf_ls "f" dse_nil e3;sf1;sf_ls "f" e1 e2;sf2]) ([],[])``
*)

val unroll_cs = reduceLib.num_compset ();
val _ = listSimps.list_rws unroll_cs;
val _ = computeLib.add_thms [SWAP_REWRITES, pairTheory.FST, listTheory.ALL_DISTINCT] unroll_cs;
val _ = computeLib.add_conv (``$=``, 2, stringLib.string_EQ_CONV) unroll_cs;
val _ = computeLib.add_conv (``$=``, 2, stringLib.char_EQ_CONV) unroll_cs;





fun ds_inference_SIMPLE_UNROLL___CONV___list_dse_nil t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;


      val sfOpt = find_in_list is_dse_nil_list sfL;
      val _ = if (isSome sfOpt) then () else SMALLFOOT_ERR "Not dse_nil list found!";
      val (n, lsf) = valOf sfOpt;
      val (f, e1, e2) = dest_sf_ls lsf;


      val thm = ISPECL [numLib.term_of_int n, f, e2, c1, c2, pf, sf, pf', sf']
         INFERENCE___NIL_LIST_EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end;




fun find_list_precond n cL [] = NONE |
    find_list_precond n cL (h::l) =
      let
         val (f, e1, e2) = dest_sf_ls h;
         val cOpt = find_entry 0 e1 cL;
      in
         if (isSome cOpt) then SOME (n, valOf cOpt, f, e1, e2) else
         find_list_precond (n+1) cL l
      end handle _ => find_list_precond (n+1) cL l;


fun ds_inference_SIMPLE_UNROLL___CONV___precondition_list t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (cL, _) = strip_cons c1;
      val (sfL, _) = strip_cons sf;


      val sfOpt = find_list_precond 0 cL sfL
      val _ = if (isSome sfOpt) then () else SMALLFOOT_ERR "Not suitable list found!";
      val (n, m, f, e1, e2) = valOf sfOpt;

      val thm = ISPECL [numLib.term_of_int m, numLib.term_of_int n, f, e1, e2, c1, c2, pf, sf, pf', sf']
         INFERENCE___precondition_LIST_EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end


(*
val t = ``LIST_DS_ENTAILS ([e1],[(e2,e3)]) ([pf_unequal e1 e3;pf1;pf_unequal e2 e4; pf3],[sf_ls "g" e5 e7; sf_ls "f" dse_nil e3;sf_points_to e1 [("g", x); ("f", y)]; sf1;sf2]) ([],[sf432;sf_ls "f" e1 e3;sf4])``

val t = ``LIST_DS_ENTAILS ([e1],[(e2,e3)]) ([pf_unequal e3 e1;pf1;pf_unequal e2 e4; pf3],[sf_ls "g" e5 e7; sf_ls "f" dse_nil e3;sf_points_to e1 [("g", x); ("f", y)]; sf1;sf2]) ([],[sf_ls "f" e1 e3])``

val t = ``LIST_DS_ENTAILS ([e1],[(e2,e3)]) ([pf_unequal e3 e1;pf1;pf_unequal e2 e4; pf3],[sf_ls "g" e5 e7; sf_ls "f" dse_nil e3;sf_points_to e1 [("g", x); ("f", y)]; sf1;sf2]) ([],[sf_bin_tree ("f1","f2") e1])``

val t = ``LIST_DS_ENTAILS ([e1],[(e2,e3)]) ([pf_unequal e3 e1;pf1;pf_unequal e2 e4; pf3],[sf_ls "g" e5 e7;sf_points_to e1 [("g", x); ("f", y)]; sf1;sf2]) ([],[sf_bin_tree ("g","fa") e1])``

*)


fun find_list_unroll_right n sfL pfL [] = NONE |
    find_list_unroll_right n sfL pfL (h::l) =
      let
         val (f, e1, e3) = dest_sf_ls h;
         val (n3, pointer) = valOf (find_in_list (is_sf_points_to_ex e1) sfL);
         val (_, a, pointer_list, _) = dest_sf_points_to pointer;
         val e2 = snd (first (fn (x,y) => x = f) pointer_list);
         val (n2, uneq) = valOf (find_in_list (is_uneq_2 e1 e3) pfL);
         val (e1',e2') = dest_pf_unequal uneq;
         val turn = (e1 = e2');
      in
         SOME (n, n2, n3, turn, e1, e2,e3, f, a)
      end handle _ => find_list_unroll_right (n+1) sfL pfL l;

fun find_bin_tree_unroll_right n sfL [] = NONE |
    find_bin_tree_unroll_right n sfL (h::l) =
      let
         val (f1,f2, ex, _) = dest_sf_bin_tree h;
         val (n2, pointer) = valOf (find_in_list (is_sf_points_to_ex ex) sfL);
         val (_, a, pointer_list, _) = dest_sf_points_to pointer;
         val e1 = snd (first (fn (x,y) => x = f1) pointer_list);
         val e2 = snd (first (fn (x,y) => x = f2) pointer_list);
      in
         SOME (n, n2, ex, e1, e2, f1, f2, a)
      end handle _ => find_bin_tree_unroll_right (n+1) sfL l;


fun ds_inference_SIMPLE_UNROLL___CONV___points_to_list t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (pfL, _) = strip_cons pf;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';


      val searchOpt = find_list_unroll_right 0 sfL pfL sfL';
      val _ = if (isSome searchOpt) then () else SMALLFOOT_ERR "Not suitable list found!";
      val (n1, n2, n3, turn, e1, e2,e3, f, a) = valOf searchOpt;

      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, numLib.term_of_int n3,
            if turn then F else T, e1, e2, e3, f, a, c1, c2, pf, sf, pf', sf']
         INFERENCE___NON_EMPTY_LS___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end



fun ds_inference_SIMPLE_UNROLL___CONV___points_to_bin_tree t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';


      val searchOpt = find_bin_tree_unroll_right 0 sfL sfL';
      val _ = if (isSome searchOpt) then () else SMALLFOOT_ERR "Not suitable tree found!";
      val (n, n2, ex, e1, e2, f1, f2, a) = valOf searchOpt;
      val thm = ISPECL [numLib.term_of_int n, numLib.term_of_int n2,
            ex, e1, e2, f1, f2, a, c1, c2, pf, sf, pf', sf']
         INFERENCE___NON_EMPTY_BIN_TREE___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val _ = if (lhs (concl thm2) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm2
   end


val ds_inference_SIMPLE_UNROLL___CONV =
   (REPEATC ds_inference_SIMPLE_UNROLL___CONV___list_dse_nil) THENC
   (REPEATC ds_inference_SIMPLE_UNROLL___CONV___precondition_list) THENC
   (REPEATC ds_inference_SIMPLE_UNROLL___CONV___points_to_list) THENC
   (REPEATC ds_inference_SIMPLE_UNROLL___CONV___points_to_bin_tree);





(*example
val t = ``LIST_DS_ENTAILS (c1,c2) ([],[sf1;sf3;sf_bin_tree ("f1","f2") e;sf2]) ([],[])``
val t = ``LIST_DS_ENTAILS (c1,c2) ([pf_unequal e1 e2],[sf1;sf3;sf_ls "f" e1 e2;sf2]) ([],[])``
val t = ``LIST_DS_ENTAILS (c1,c2) ([pf2;pf_unequal e2 e1],[sf1;sf3;sf_ls "f" e1 e2;sf2]) ([],[])``

*)


fun prove_infinite_univ_ante thm =
   let
      val (inf_univ_t, _)  = dest_imp (concl thm);
      val inf_univ_thm = (prove (inf_univ_t, SIMP_TAC std_ss (append (!INFINITE_UNIV___THMs) [INFINITE_UNIV___NUM,INFINITE_UNIV___STRING]))) handle _ =>
         (let
            val _ = print "Could not deduce \"INFINITE UNIV\"!. It is added as an assumption.\nPlease add this theorem to INFINITE_UNIV___THMs.\n\n";
         in
            ASSUME inf_univ_t
         end);
   in
      MP thm inf_univ_thm
   end;


fun find_list_uneq_unroll_left n pfL [] = NONE |
    find_list_uneq_unroll_left n pfL (h::l) =
      let
         val (f, e1, e2) = dest_sf_ls h;
         val (n2, uneq) = valOf (find_in_list (is_uneq_2 e1 e2) pfL);
         val (e1',e2') = dest_pf_unequal uneq;
         val turn = (e1 = e2');
      in
         SOME (n, n2, turn, e1, e2, f)
      end handle _ => find_list_uneq_unroll_left (n+1) pfL l;


fun ds_inference_UNROLL_LIST___NON_EMPTY___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (pfL, _) = strip_cons pf;
      val (sfL, _) = strip_cons sf;


      val searchOpt = find_list_uneq_unroll_left 0 pfL sfL;
      val _ = if (isSome searchOpt) then () else SMALLFOOT_ERR "Not suitable list found!";
      val (n, n2, turn, e1, e2, f) = valOf searchOpt;

      val thm = ISPECL [numLib.term_of_int n, numLib.term_of_int n2,
            if turn then T else F, e1, e2, f, c1, c2, pf, sf, pf', sf']
         INFERENCE_UNROLL_COLLAPSE_LS___NON_EMPTY___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val thm3 = prove_infinite_univ_ante thm2;
      val _ = if (lhs (concl thm3) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm3
   end

val ds_inference_PRECONDITION_CASES___CONV =
   REWR_CONV INFERENCE_UNROLL_COLLAPSE_PRECONDITION___EVAL;



fun ds_inference_UNROLL_LIST___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;


      val searchOpt = find_in_list is_sf_ls sfL;
      val _ = if (isSome searchOpt) then () else SMALLFOOT_ERR "Not suitable list found!";
      val (n, list_term) = valOf searchOpt;
      val (f, e1, e2) = dest_sf_ls list_term;

      val thm = ISPECL [numLib.term_of_int n,
            e1, e2, f, c1, c2, pf, sf, pf', sf']
         INFERENCE_UNROLL_COLLAPSE_LS___EVAL
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val thm3 = prove_infinite_univ_ante thm2;
      val _ = if (lhs (concl thm3) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm3
   end


fun ds_inference_UNROLL_BIN_TREE___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (sfL, _) = strip_cons sf;


      val searchOpt = find_in_list is_sf_bin_tree sfL;
      val _ = if (isSome searchOpt) then () else SMALLFOOT_ERR "Not suitable binary tree found!";
      val (n, tree_term) = valOf searchOpt;
      val (f1,f2, e1, _) = dest_sf_bin_tree tree_term;

      val thm = ISPECL [numLib.term_of_int n,
            e1, f1, f2, c1, c2, pf, sf, pf', sf']
         INFERENCE_UNROLL_COLLAPSE_BIN_TREE___EVAL;
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val thm3 = prove_infinite_univ_ante thm2;
      val _ = if (lhs (concl thm3) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm3
   end




(*
val t = ``LIST_DS_ENTAILS (c1,c2) ([pf_equal e2 e1],[sf1;sf3;sf2]) ([],[sf_ls f e1 e2;sf_tree fL es e])``
*)
fun is_tree_case_candidate pfL t =
   let
      val (_, e2, e1) = dest_sf_tree t;
   in
      not (isSome (find_in_list (is_uneq_2 e1 e2) pfL)) andalso
      not (isSome (find_in_list (is_eq_2 e1 e2) pfL))
   end;

fun ds_inference_UNROLL_RIGHT_CASES___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val sf'' = rhs (concl (((REWRITE_CONV [sf_ls_def, sf_bin_tree_def] sf') handle _ => REFL sf')));
      val (pfL, _) = strip_cons pf;
      val (sfL', _) = strip_cons sf'';

      val searchOpt = find_in_list (is_tree_case_candidate pfL) sfL';
      val _ = if (isSome searchOpt) then () else SMALLFOOT_ERR "Not suitable tree found!";

      val (n, tree_term) = valOf searchOpt;
      val (_, e1, e2) = dest_sf_tree tree_term;

      val thm = ISPECL [e1, e2, c1, c2, pf, sf, pf', sf']
         (GSYM INFERENCE_EXCLUDED_MIDDLE);
      val _ = if (lhs (concl thm) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm
   end;










(*
val t = ``LIST_DS_ENTAILS ([],[]) ([pf1;pf2],[sf4;sf_ls f e1 e2; sf5;sf6]) ([],[sf2;sf_ls f e1 dse_nil;sf1])``

val t = ``LIST_DS_ENTAILS ([e3],[]) ([pf1;pf2;pf_unequal e3 e1],[sf4;sf_ls f e1 e2; sf5;sf6]) ([],[sf2;sf_ls f e1 e3;sf1])``


val t = ``LIST_DS_ENTAILS ([],[]) ([pf1;pf2;pf_unequal e3 e1],[sf_points_to e3 [(f,e2)];sf4;sf_ls f e1 e2; sf5;sf6]) ([],[sf2;sf_ls f e1 e3;sf1])``


val t = ``LIST_DS_ENTAILS ([],[]) ([pf1;pf_unequal e2 e3;pf2;pf_unequal e3 e1],[sf_points_to e3 [(f,e2)];sf4;sf_ls f e1 e2; sf5;sf_ls g e3 e2;sf6]) ([],[sf2;sf_ls f e1 e3;sf1])``

*)



fun get_uneq_index_turn pfL e1 e3 = let
      val (n, pf) = valOf (find_in_list (is_uneq_2 e1 e3) pfL);
      val (e1', e3') = dest_pf_unequal pf;
      val turn = not (e1' = e1);
   in
      (n, turn)
   end;

fun find_list_append_instance_nil n1 n2 e1 e2 e3 f =
   let
      val _ = if (is_dse_nil e3) then () else SMALLFOOT_ERR "Not applicable!";
      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, e1, e2, f] INFERENCE_APPEND_LIST___nil___EVAL
   in
      thm
   end;

fun find_list_append_instance_precond n1 n2 e1 e2 e3 f n3 b1 c1L =
   let
      val n4 = valOf (find_entry 0 e3 c1L)
      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, e1, e2, f, e3, numLib.term_of_int n4, numLib.term_of_int n3, if b1 then T else F] INFERENCE_APPEND_LIST___precond___EVAL
   in
      thm
   end;


fun find_list_append_instance_points_to n1 n2 e1 e2 e3 f n3 b1 sfL =
   let
      val (n4, pt) = valOf (find_in_list (is_sf_points_to_ex e3) sfL);
      val (_, a, _, _) = dest_sf_points_to pt;

      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, e1, e2, f, e3, numLib.term_of_int n4, a, numLib.term_of_int n3, if b1 then T else F] INFERENCE_APPEND_LIST___points_to___EVAL
   in
      thm
   end;


fun del_el l n =
   List.take(l, n) @ List.drop(l, n+1)


fun find_list_append_instance_tree n1 n2 e1 e2 e3 f n3 b1 pfL sfL =
   let
      fun pred sf =
         let
            val (_, (fL, l), es, e3') = dest_sf_tree_ext sf;
            val _ = if (e3 = e3') then () else raise SMALLFOOT_ERR "Not suitable!";
            val fLt = list_mk_cons fL l;
            val (n5, b2) = get_uneq_index_turn pfL es e3';
         in
            SOME (fLt, n5, b2, es)
         end;
      val (n4, pt, (fLt, n5, b2,es)) = valOf (find_in_list_val pred (del_el sfL n1));
      val n4 = if (n4 < n1) then n4 else (n4 + 1);

      val thm = ISPECL [numLib.term_of_int n1, numLib.term_of_int n2, e1, e2,
         numLib.term_of_int n4, e3, fLt, es,
         numLib.term_of_int n3, if b1 then T else F,
         numLib.term_of_int n5, if b2 then T else F, f] INFERENCE_APPEND_LIST___tree___EVAL
   in
      thm
   end;


fun find_list_append_instance n2 c1L pfL sfL [] = NONE |
    find_list_append_instance n2 c1L pfL sfL (sf'::sfL') =
    let
      val (f, e1, e3) = dest_sf_ls sf';
      val (n1, sf) = valOf (find_in_list (fn sf => (let val (f', e1', e2') = dest_sf_ls sf in (f = f') andalso (e1' = e1) end)) sfL);
      val (_, _, e2) = dest_sf_ls sf;
      val thm = find_list_append_instance_nil n1 n2 e1 e2 e3 f handle _ =>
                let
                   val (n3,b1) = get_uneq_index_turn pfL e1 e3;
                in
                   find_list_append_instance_precond n1 n2 e1 e2 e3 f n3 b1 c1L handle _ =>
                   find_list_append_instance_points_to n1 n2 e1 e2 e3 f n3 b1 sfL handle _ =>
                   find_list_append_instance_tree n1 n2 e1 e2 e3 f n3 b1 pfL sfL
                end;
    in
      SOME thm
    end handle _ => find_list_append_instance (n2+1) c1L pfL sfL sfL';



fun ds_inference_APPEND_LIST___CONV t =
   let
      val (c1, c2, pf, sf, pf', sf') = dest_LIST_DS_ENTAILS t;
      val (c1L, _) = strip_cons c1;
      val (pfL, _) = strip_cons pf;
      val (sfL, _) = strip_cons sf;
      val (sfL', _) = strip_cons sf';

      val inferenceOpt = find_list_append_instance 0 c1L pfL sfL sfL';
      val _ = if (isSome inferenceOpt) then () else SMALLFOOT_ERR "No suitable lists found!";

      val thm = ISPECL [c1, c2, pf, sf, pf', sf'] (valOf inferenceOpt);
      val thm2 = CONV_RULE (computeLib.CBV_CONV unroll_cs) thm;
      val thm3 = prove_infinite_univ_ante thm2;
      val _ = if (lhs (concl thm3) = t) then () else SMALLFOOT_ERR "No CONVERSION";
   in
      thm3
   end











val ds_inference_NO_SPLIT_CONV =
   TRY_CONV ds_inference_SUBSTITUTION___CONV THENC
   TRY_CONV ds_inference_REMOVE_TRIVIAL___CONV THENC
   TRY_CONV ds_inference_HYPOTHESIS___CONV THENC
   TRY_CONV ds_inference_FRAME___CONV THENC
   TRY_CONV ds_inference_NIL_NOT_LVAL___CONV THENC
   TRY_CONV ds_inference_PARTIAL___CONV THENC
   (REPEATC ds_inference_APPEND_LIST___CONV) THENC
   TRY_CONV ds_inference_PRECONDITION_STRENGTHEN___CONV THENC
   (REPEATC ds_inference_SIMPLE_UNROLL___CONV) THENC
   TRY_CONV ds_inference_INCONSISTENT___CONV THENC
   TRY_CONV ds_inference_AXIOM___CONV;


val ds_inference_SPLIT_CONV =
   ds_inference_UNROLL_RIGHT_CASES___CONV ORELSEC
   ds_inference_PRECONDITION_CASES___CONV ORELSEC
   (CHANGED_CONV (REPEATC ds_inference_UNROLL_LIST___NON_EMPTY___CONV)) ORELSEC
   ds_inference_UNROLL_LIST___CONV ORELSEC
   ds_inference_UNROLL_BIN_TREE___CONV;


fun ds_inference_CHECK_LIST_DS_ENTAILS_CONV t =
    let
      val _ = dest_LIST_DS_ENTAILS t;
    in
      raise UNCHANGED
    end

val ds_DECIDE_CONV =
   (REDEPTH_CONV (CHANGED_CONV (
      ds_inference_CHECK_LIST_DS_ENTAILS_CONV THENC
      (REPEATC ds_inference_NO_SPLIT_CONV) THENC
      TRY_CONV ds_inference_SPLIT_CONV)
   )) THENC REWRITE_CONV[];


fun ds_DECIDE t = EQT_ELIM (ds_DECIDE_CONV t);



end;
