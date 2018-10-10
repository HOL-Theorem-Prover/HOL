structure congToolsLib :> congToolsLib =
struct

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/tools") :: !loadPath;

map load
 ["congLib", "congToolsLibTheory", "Trace", "Traverse", "Travrules"];
*)

open HolKernel boolLib bossLib
     congLib congToolsLibTheory Traverse Travrules Trace

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val IMP_REFL = prove (``!x. x ==> x``, SIMP_TAC std_ss []);

fun extract_preorder_trans (Travrules.PREORDER(_,TRANS,_)) = TRANS;
fun extract_preorder_refl (Travrules.PREORDER(_,_,REFL)) = REFL;
fun extract_preorder_const (Travrules.PREORDER(t,_,_)) = t


fun preorder_refl_thm preorder =
  let
    val preorderTerm = extract_preorder_const preorder
    val hol_type = hd (#2 (dest_type (type_of preorderTerm)))
    val var = mk_var ("x", hol_type)
    val refl = extract_preorder_refl preorder;
    val reflThm = refl {Rinst=preorderTerm,arg=var}
  in
    GEN_ALL reflThm
  end;

fun preorder_trans_thm preorder =
  let
    val preorderTerm = extract_preorder_const preorder
    val hol_type = hd (#2 (dest_type (type_of preorderTerm)))

    val var1 = mk_var ("x1", hol_type)
    val var2 = mk_var ("x2", hol_type)
    val var3 = mk_var ("x3", hol_type)
    val a1 = mk_comb ((mk_comb(preorderTerm,var1)), var2)
    val a2 = mk_comb ((mk_comb(preorderTerm,var2)), var3)
    val a1Thm = UNDISCH (ISPEC a1 IMP_REFL)
    val a2Thm = UNDISCH (ISPEC a2 IMP_REFL)
    val thm = extract_preorder_trans preorder a1Thm a2Thm
    val thm = DISCH a2 thm
    val thm = DISCH a1 thm
    val thm = REWRITE_RULE [AND_IMP_INTRO] thm
    val thm = GEN var3 thm
    val thm = GEN var2 thm
    val thm = GEN var1 thm
  in
    thm
  end;


fun mk_list_as_set_congruence_relation_cs def preorder =
  let
    val rel = rand (rhs (concl (def)));

    val refl_thm = LIST_AS_SET_CONGRUENCE_RELATION_REFL
    val refl_thm = ISPEC rel refl_thm
    val refl_thm = MP refl_thm (preorder_refl_thm preorder)
    val refl_thm = REWRITE_RULE [GSYM def] refl_thm

    val trans_thm = LIST_AS_SET_CONGRUENCE_RELATION_TRANS
    val trans_thm = ISPEC rel trans_thm
    val trans_thm = MP trans_thm (preorder_trans_thm preorder)
    val trans_thm = REWRITE_RULE [GSYM def] trans_thm

    val new_preorder = mk_preorder (trans_thm, refl_thm)

    val cong_thm = LIST_AS_SET_CONGRUENCE_RELATION_CONG;
    val cong_thm = ISPEC rel cong_thm
    val cong_thm = REWRITE_RULE [GSYM def] cong_thm

    val rwrts_thm = LIST_AS_SET_CONGRUENCE_RELATION_REWRITES;
    val rwrts_thm = ISPEC rel rwrts_thm
    val rwrts_thm = REWRITE_RULE [GSYM def] rwrts_thm

  in
   CSFRAG {rewrs  = [rwrts_thm],
    relations = [new_preorder],
    dprocs = [],
    congs  = [cong_thm]}
  end





(*For debugging

val TESTX_def = Define `
  TESTX = LIST_AS_SET_CONGRUENCE_RELATION $=`

val equalityPreorder = PREORDER(("=","min"),TRANS,REFL);

mk_list_as_set_congruence_relation_cs TESTX_def equalityPreorder

*)

end
