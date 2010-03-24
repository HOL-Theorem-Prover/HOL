structure holfootParser :> holfootParser =
struct

(*
quietdec := true;
loadPath := 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) :: 
            !loadPath;

map load ["finite_mapTheory", "holfootTheory",
     "Parsetree", "AssembleHolfootParser"];
show_assums := true;
*)

open HolKernel Parse boolLib finite_mapTheory 
open Parsetree;
open separationLogicSyntax
open vars_as_resourceSyntax
open holfootSyntax

(*
quietdec := false;
*)


exception holfoot_unsupported_feature_exn of string;

fun mk_el_list 0 v = []
  | mk_el_list n v =
       (listSyntax.mk_hd v)::(mk_el_list (n-1) (listSyntax.mk_tl v))
    
fun mk_list [] = Absyn.mk_ident "NIL"
  | mk_list (e::es) =
      Absyn.mk_app (Absyn.mk_app (Absyn.mk_ident "CONS", e), mk_list es)

fun absyn2term a = absyn_to_term (term_grammar ()) a

fun string_to_label s = mk_var (s, markerSyntax.label_ty);

val parse = AssembleHolfootParser.raw_read_file;


(*
val file = "/home/tuerk/Downloads/holfoot/EXAMPLES/business2.sf";
val file = "/home/tt291/Downloads/holfoot/EXAMPLES/business2.sf";

val prog = parse file;
*)


fun map_ident (s,f) l = case l of
    Absyn.AQ    (locn,t)   => (s, Absyn.AQ (locn,t))
  | Absyn.IDENT (locn,i)   => 
         let
            val (s', a) = f s locn i
         in
            (s', a)
         end
  | Absyn.QIDENT(locn,t,i) => (s, Absyn.QIDENT(locn,t,i))
  | Absyn.APP   (locn,a1,a2) => 
         let
            val (s',  a1') = map_ident (s,f)   a1
            val (s'', a2') = map_ident (s',f) a2
         in
            (s'', Absyn.APP (locn,a1',a2'))
         end
  | Absyn.LAM   (locn,v,a) => 
         let
            val (s',  a') = map_ident (s,f) a
         in
            (s', Absyn.LAM (locn,v,a'))
         end
  | Absyn.TYPED (locn,a,p) => 
         let
            val (s',  a') = map_ident (s,f) a
         in
            (s', Absyn.TYPED (locn,a',p))
         end


fun collect_ident l =
let
   val is = Redblackset.empty String.compare
   fun col set l s = (Redblackset.add (set,s), Absyn.IDENT (l, s))
   val (set, _) = map_ident (is, col) l
in
   set
end;


fun string_list2set sL =
   Redblackset.addList(Redblackset.empty String.compare, sL);


fun is_holfoot_ex_ident i =
   ((String.size i > 1) andalso
    (String.sub (i,0) = #"_") andalso
      not (String.sub (i,1) = #" "));
fun norm_holfoot_ex_ident i = String.substring(i, 1, (String.size i) - 1);

local
   fun subst_qv_ident qv l i =
       if (is_holfoot_ex_ident i) then
       let
          val i' = norm_holfoot_ex_ident i;
          val qv' = Redblackset.add (qv, i')
       in
          (qv', Absyn.IDENT (l, i'))
       end else (qv, Absyn.IDENT (l, i))

in

fun remove_qv a =
      map_ident (Redblackset.empty String.compare, subst_qv_ident) a

end;


fun HOL_Absyn h =
  let
     val h' = String.translate (fn #"#" => "" | c => String.str c) h
     val ha = Absyn [QUOTE h'];
  in
     ha
  end;

fun absyn_extract_vars vL a =
  let
     val eL_v = genvar (Type `:num list`);
     val eL_L = mk_el_list (length vL) eL_v;
     val substL = zip vL eL_L;
     fun a_subst () l i =
        ((), Absyn.mk_AQ (assoc i substL)) handle HOL_ERR _ => ((), Absyn.IDENT (l, i))
     val (_, a') = map_ident ((), a_subst) a
     val qa = Absyn.mk_lam (Absyn.VAQ (locn.Loc_None, eL_v), a')

     val vL' = map (fn v => mk_comb(holfoot_exp_var_term, string2holfoot_var v)) vL;
     val vLt = listSyntax.mk_list (vL', holfoot_a_expression_ty);
  in
     (qa, vLt)
  end;


fun holfoot_expression2absyn vs (Aexp_ident x) =
   if (String.sub (x, 0) = #"#") then  
      Absyn.mk_app (Absyn.mk_AQ holfoot_exp_const_term, 
          Absyn.mk_ident (String.substring(x, 1, (String.size x) - 1)))
   else if (is_holfoot_ex_ident x) orelse (Redblackset.member (snd vs, x)) then 
      Absyn.mk_app (Absyn.mk_AQ holfoot_exp_const_term, 
          Absyn.mk_ident x)
   else 
      let
         val var_term = string2holfoot_var x;
         val term = mk_comb(holfoot_exp_var_term, var_term) 
      in 
         Absyn.mk_AQ term
      end
| holfoot_expression2absyn vs (Aexp_num n) =
     Absyn.mk_AQ (mk_comb (holfoot_exp_const_term, numLib.term_of_int n))
| holfoot_expression2absyn vs (Aexp_infix (opstring, e1, e2)) =
   let
      val opterm = if (opstring = "-") then holfoot_exp_sub_term else
                   if (opstring = "+") then holfoot_exp_add_term else
                   if (opstring = "*") then holfoot_exp_mult_term else
                   if (opstring = "/") then holfoot_exp_div_term else
                   if (opstring = "%") then holfoot_exp_mod_term else
                   if (opstring = "^") then holfoot_exp_exp_term else
                       Raise (holfoot_unsupported_feature_exn ("Pexp_infix "^opstring));
      val t1 = holfoot_expression2absyn vs e1;
      val t2 = holfoot_expression2absyn vs e2;
   in
      (Absyn.list_mk_app (Absyn.mk_AQ opterm, [t1, t2]))
   end
| holfoot_expression2absyn vs (Aexp_hol h) =
      let
        val ha = HOL_Absyn h;
        val used_vars = Redblackset.listItems (Redblackset.intersection (collect_ident ha, fst vs))        
      in
        if (null used_vars) then
           Absyn.mk_app (Absyn.mk_AQ holfoot_exp_const_term, ha)
        else
           let
             val (qha, vLt) = absyn_extract_vars used_vars ha
           in
             Absyn.list_mk_app (Absyn.mk_AQ holfoot_exp_op_term, [qha, Absyn.mk_AQ vLt])
           end
      end;



fun holfoot_p_condition2absyn vs Pcond_false =
   Absyn.mk_AQ holfoot_pred_false_term
| holfoot_p_condition2absyn vs Pcond_true =
   Absyn.mk_AQ holfoot_pred_true_term
| holfoot_p_condition2absyn vs (Pcond_neg c1) =
   let
      val t1 = holfoot_p_condition2absyn vs c1
   in
      (Absyn.mk_app (Absyn.mk_AQ holfoot_pred_neg_term, t1))
   end
| holfoot_p_condition2absyn vs (Pcond_and (c1,c2)) =
   let
      val t1 = holfoot_p_condition2absyn vs c1
      val t2 = holfoot_p_condition2absyn vs c2
   in
      (Absyn.list_mk_app (Absyn.mk_AQ holfoot_pred_and_term, [t1, t2]))
   end
| holfoot_p_condition2absyn vs (Pcond_or (c1,c2)) =
   let
      val t1 = holfoot_p_condition2absyn vs c1
      val t2 = holfoot_p_condition2absyn vs c2
   in
      (Absyn.list_mk_app (Absyn.mk_AQ holfoot_pred_or_term, [t1, t2]))
   end
| holfoot_p_condition2absyn vs (Pcond_compare (opstring, e1, e2)) =
   let
      val opterm = if (opstring = "==") then holfoot_pred_eq_term else
                   if (opstring = "!=") then holfoot_pred_neq_term else
                   if (opstring = "<")  then holfoot_pred_lt_term else
                   if (opstring = "<=") then holfoot_pred_le_term else
                   if (opstring = ">")  then holfoot_pred_gt_term else
                   if (opstring = ">=") then holfoot_pred_ge_term else
                      Raise (holfoot_unsupported_feature_exn ("Pcond_compare "^opstring));
      val t1 = holfoot_expression2absyn vs e1;
      val t2 = holfoot_expression2absyn vs e2;
   in
      (Absyn.list_mk_app (Absyn.mk_AQ opterm, [t1, t2]))
   end
| holfoot_p_condition2absyn vs (Pcond_hol h) =
      let
        val ha = HOL_Absyn h;
        val used_vars = Redblackset.listItems (Redblackset.intersection (collect_ident ha, fst vs))        
      in
        let
          val (qha, vLt) = absyn_extract_vars used_vars ha
        in
          Absyn.list_mk_app (Absyn.mk_AQ holfoot_pred_term, [qha, Absyn.mk_AQ vLt])
        end
      end;



val tag_a_expression_fmap_emp_term = ``FEMPTY:(holfoot_tag |-> holfoot_a_expression)``;
val tag_a_expression_fmap_update_term = ``FUPDATE:(holfoot_tag |-> holfoot_a_expression)->
(holfoot_tag # holfoot_a_expression)->(holfoot_tag |-> holfoot_a_expression)``;


fun tag_a_expression_list2absyn vs [] = (Absyn.mk_AQ tag_a_expression_fmap_emp_term) |
    tag_a_expression_list2absyn vs ((tag,exp1)::l) =
      let
         val tag_term = string2holfoot_tag tag;
         val exp_absyn = holfoot_expression2absyn vs exp1;
         val a = Absyn.mk_pair (Absyn.mk_AQ tag_term, exp_absyn)
         val rest = tag_a_expression_list2absyn vs l;
      in
         Absyn.list_mk_app (Absyn.mk_AQ tag_a_expression_fmap_update_term, [rest, a])
      end;


val holfoot_data_list___EMPTY_tm = ``[]:(holfoot_tag # num list) list``;

fun holfoot_a_space_pred2absyn vs (Aspred_empty) =
   Absyn.mk_AQ holfoot_stack_true_term
| holfoot_a_space_pred2absyn vs (Aspred_list (tag,exp1)) =
  holfoot_a_space_pred2absyn vs (Aspred_listseg (tag,exp1, Aexp_num 0))
| holfoot_a_space_pred2absyn vs (Aspred_listseg (tag,exp1, exp2)) = 
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_list_seg_term, [
             Absyn.mk_AQ (string2holfoot_tag tag),
             exp1, Absyn.mk_AQ holfoot_data_list___EMPTY_tm, exp2]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_queue (tag,exp1, exp2)) = 
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_queue_term, [
             Absyn.mk_AQ (string2holfoot_tag tag),
             exp1, Absyn.mk_AQ holfoot_data_list___EMPTY_tm, exp2]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_data_list (tag,exp1,data_tag,data)) =
  holfoot_a_space_pred2absyn vs (Aspred_data_listseg (tag, exp1, data_tag, data, Aexp_num 0))
| holfoot_a_space_pred2absyn vs (Aspred_data_listseg (tag,exp1,data_tag,data,exp2)) =
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val data_a = HOL_Absyn data;
     val data_tag_term = string2holfoot_tag data_tag;
     val data2_a = mk_list [Absyn.mk_pair (Absyn.mk_AQ data_tag_term, data_a)];
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_list_seg_term, [
             Absyn.mk_AQ (string2holfoot_tag tag),
             exp1, data2_a, exp2]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_data_queue (tag,exp1,data_tag,data,exp2)) =
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val data_a = HOL_Absyn data;
     val data_tag_term = string2holfoot_tag data_tag;
     val data2_a = mk_list [Absyn.mk_pair (Absyn.mk_AQ data_tag_term, data_a)];
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_queue_term, [
             Absyn.mk_AQ (string2holfoot_tag tag),
             exp1, data2_a, exp2]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_array (exp1, exp2)) = 
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_array_term, [
             exp1, exp2, Absyn.mk_AQ holfoot_data_list___EMPTY_tm]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_data_array (exp1, exp2, tag, data)) = 
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val data_a = HOL_Absyn data;
     val data_tag_term = string2holfoot_tag tag;
     val data2_a = mk_list [Absyn.mk_pair (Absyn.mk_AQ data_tag_term, data_a)];
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_array_term, [
             exp1, exp2, data2_a]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_interval (exp1, exp2)) = 
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_interval_term, [
             exp1, exp2, Absyn.mk_AQ holfoot_data_list___EMPTY_tm]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_data_interval (exp1, exp2, tag, data)) = 
  let
     val exp1 = holfoot_expression2absyn vs exp1;
     val exp2 = holfoot_expression2absyn vs exp2;
     val data_a = HOL_Absyn data;
     val data_tag_term = string2holfoot_tag tag;
     val data2_a = mk_list [Absyn.mk_pair (Absyn.mk_AQ data_tag_term, data_a)];
     val c = Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_interval_term, [
             exp1, exp2, data2_a]);
  in
     c
  end
| holfoot_a_space_pred2absyn vs (Aspred_data_tree (tagL,exp,dtagL,data)) =
  let
     val exp = holfoot_expression2absyn vs exp;
     val data_a = HOL_Absyn data;
     val tree_dtag_t = listSyntax.mk_list (
                 (map string2holfoot_tag dtagL), Type `:holfoot_tag`)
     val data2_a = Absyn.mk_pair (Absyn.mk_AQ tree_dtag_t, data_a)
     val tree_tag_t = listSyntax.mk_list (
                 (map string2holfoot_tag tagL), Type `:holfoot_tag`)
     val comb_a = Absyn.list_mk_app(Absyn.mk_AQ holfoot_ap_data_tree_term, [
                Absyn.mk_AQ tree_tag_t, exp, data2_a]);
  in
     comb_a
  end
| holfoot_a_space_pred2absyn vs (Aspred_tree (tagL,tagR,exp)) =
  let
     val exp = holfoot_expression2absyn vs exp;
     val comb_a = Absyn.list_mk_app(Absyn.mk_AQ holfoot_ap_bintree_term, [
                      Absyn.mk_pair (Absyn.mk_AQ (string2holfoot_tag tagL), 
                               Absyn.mk_AQ (string2holfoot_tag tagR)), 
                      exp])
  in
     comb_a
  end
| holfoot_a_space_pred2absyn vs (Aspred_hol s) =
  Absyn.mk_app (Absyn.mk_AQ holfoot_bool_proposition_term, HOL_Absyn s)
| holfoot_a_space_pred2absyn vs (Aspred_pointsto (exp, pl)) =
  let
     val a1 = holfoot_expression2absyn vs exp;
     val a2 = tag_a_expression_list2absyn vs pl;
  in
     Absyn.list_mk_app(Absyn.mk_AQ holfoot_ap_points_to_term, [a1, a2])
  end;



fun invariant2a_proposition NONE =
    Aprop_spred Aspred_empty
  | invariant2a_proposition (SOME p) = p


val holfoot_map_absyn = Absyn ([QUOTE 
      "var_res_map DISJOINT_FMAP_UNION"])

fun holfoot_a_proposition2absyn_context vs (Aprop_infix (opString, exp1, exp2)) =
  let
    val op_term = if (opString = "<") then holfoot_ap_lt_term else
                  if (opString = "<=") then holfoot_ap_le_term else
                  if (opString = ">") then holfoot_ap_gt_term else
                  if (opString = ">=") then holfoot_ap_ge_term else
                  if (opString = "==") then holfoot_ap_equal_term else
                  if (opString = "!=") then holfoot_ap_unequal_term else
                     Raise (holfoot_unsupported_feature_exn ("Aexp_infix "^opString))
    val t1 = holfoot_expression2absyn vs exp1;
    val t2 = holfoot_expression2absyn vs exp2;
  in
    (Absyn.list_mk_app (Absyn.mk_AQ op_term, [t1, t2]))
  end
| holfoot_a_proposition2absyn_context vs (Aprop_false) =
     Absyn.mk_AQ holfoot_ap_false_term
| holfoot_a_proposition2absyn_context vs (Aprop_ifthenelse (Aprop_infix (opString,exp1,exp2),ap1,ap2)) =
  let
      val (ap1,ap2) = if opString = "==" then (ap1,ap2) else 
                      if opString = "!=" then (ap2,ap1) else
                      Raise (holfoot_unsupported_feature_exn "Currently only equality checks are allowed as conditions in propositions")

      val exp1 = holfoot_expression2absyn vs exp1;
      val exp2 = holfoot_expression2absyn vs exp2;
      val prop1 = holfoot_a_proposition2absyn_context vs ap1;
      val prop2 = holfoot_a_proposition2absyn_context vs ap2;
   in
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_eq_cond_term, [exp1, exp2, prop1, prop2])
   end
| holfoot_a_proposition2absyn_context vs (Aprop_ifthenelse _) =
     Raise (holfoot_unsupported_feature_exn "Currently only equality checks are allowed as conditions in propositions")
| holfoot_a_proposition2absyn_context vs (Aprop_star (ap1, ap2)) =
     Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_star_term,
                  [holfoot_a_proposition2absyn_context vs ap1,
                   holfoot_a_proposition2absyn_context vs ap2])
| holfoot_a_proposition2absyn_context vs (Aprop_map (vL, ap, l)) =
  let
      val vs2 = (fst vs, Redblackset.addList (snd vs, vL))
      val ap_a = holfoot_a_proposition2absyn_context vs2 ap;
      val pair_vs = end_itlist (fn v1 => fn v2 => Absyn.VPAIR (locn.Loc_None, v1, v2))
                    (map (fn v => Absyn.VIDENT (locn.Loc_None, v)) vL)
      val ap_la = Absyn.mk_lam (pair_vs,ap_a) 
      val l_a = HOL_Absyn l;
  in
     Absyn.list_mk_app (holfoot_map_absyn,[ap_la, l_a])
  end
| holfoot_a_proposition2absyn_context vs (Aprop_spred sp) =
     holfoot_a_space_pred2absyn vs sp;


fun holfoot_a_proposition2absyn vs x =
let
   val a1 = holfoot_a_proposition2absyn_context vs x;
   val (s, a2) = remove_qv a1
   val ex_vars = Redblackset.listItems s;

   val a3 = foldr (fn (v,a) => 
       let
          val a_lam = Absyn.mk_lam (Absyn.VIDENT (locn.Loc_None, v), a);
          val a' = Absyn.mk_app (Absyn.mk_ident "asl_exists", a_lam);
       in a' end) a2 ex_vars
in
   a3
end;


fun mk_holfoot_prop_input_absyn wp rp ap =
 let
   val rp = Redblackset.difference (rp, wp);

   val rL = map string2holfoot_var (Redblackset.listItems rp);
   val wL = map string2holfoot_var (Redblackset.listItems wp);
   val dL = append rL wL

   val da = mk_list(map Absyn.mk_AQ dL);
   val rp_term = pred_setSyntax.prim_mk_set (rL, Type `:holfoot_var`);
   val wp_term = pred_setSyntax.prim_mk_set (wL, Type `:holfoot_var`);
   val wp_rp_pair_term = pairLib.mk_pair (wp_term, rp_term);
 in
   if length dL < 2 then
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_prop_input_ap_term, [Absyn.mk_AQ wp_rp_pair_term, ap])
   else
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_prop_input_ap_distinct_term, [Absyn.mk_AQ wp_rp_pair_term, da, ap])
 end;

fun mk_holfoot_prop_input wp rp t =
  absyn2term (mk_holfoot_prop_input_absyn wp rp (Absyn.mk_AQ t));


fun holfoot_fcall_get_read_write_var_sets funL (funname:string) args =
let
  val (pL, rpe, wpe) = assoc funname funL handle HOL_ERR _ => Feedback.failwith (
          "Unknown function '"^funname^"'")
  val wL = map fst (filter (fn (_, do_write) => do_write) (zip args pL));
in
  (rpe:string list, (wpe@wL):string list)
end;


fun holfoot_fcall2absyn_internal funL vs (name, (rp,vp)) =
let
   val name_term = stringLib.fromMLstring name;

   val var_list = map string2holfoot_var rp;
   val rp_term = listSyntax.mk_list (var_list, Type `:holfoot_var`);

   val vp_a = mk_list (map (holfoot_expression2absyn vs) vp);

   val arg_a = Absyn.mk_pair (Absyn.mk_AQ rp_term, vp_a);
   val _ = ((assoc name funL);()) handle HOL_ERR _ =>
           let
              val _ = AssembleHolfootParser.print_parse_error (
                  "Call of undeclared function '"^name^"' found!");
           in
              Feedback.fail()
           end;

   val (_,wL) = holfoot_fcall_get_read_write_var_sets funL name rp;
   val funcalls = [(name, rp)];
in
   (name_term, arg_a, wL, funcalls)
end;



fun holfoot_fcall2absyn funL vs (name, (rp, vp)) =
let
   val (name_term, arg_a, wL, funcalls) =
       holfoot_fcall2absyn_internal funL vs (name, (rp,vp));
in
   (Absyn.list_mk_app(Absyn.mk_AQ holfoot_prog_procedure_call_term, [
    Absyn.mk_AQ name_term, arg_a]), wL, funcalls)
end;


fun holfoot_parallel_fcall2absyn funL vs (name1, (rp1, vp1), name2, (rp2,vp2)) =
let
   val (name1_term, arg1_a, wL1, funcalls1) =
       holfoot_fcall2absyn_internal funL vs (name1, (rp1,vp1));

   val (name2_term, arg2_a, wL2, funcalls2) =
       holfoot_fcall2absyn_internal funL vs (name2, (rp2,vp2));
in
   (Absyn.list_mk_app(Absyn.mk_AQ holfoot_prog_parallel_procedure_call_term, [
       Absyn.mk_AQ name1_term, arg1_a,Absyn.mk_AQ name2_term, arg2_a]),
       wL1@wL2, funcalls1@funcalls2)
end;



val unit_var_term = mk_var("uv", Type `:unit`);

fun mk_list_pabs l = 
  let
    val pairTerm = if null l then unit_var_term else
                   (pairLib.list_mk_pair l);
  in
     fn t => pairLib.mk_pabs (pairTerm,t) 
  end;

fun mk_list_plam l = 
  let
    val pair_vs = if null l then Absyn.VAQ (locn.Loc_None, unit_var_term) else
          end_itlist (fn v1 => fn v2 => Absyn.VPAIR (locn.Loc_None, v1, v2))
             (map (fn v => Absyn.VAQ (locn.Loc_None, v)) l)
  in
     fn a => Absyn.mk_lam (pair_vs,a) 
  end;


fun decode_rwOpt rwOpt = if isSome rwOpt then
       (let val (force, wL, rL) = valOf rwOpt in
       (force, wL, rL) end) else
       (false, [], []);

fun find_used_holvars res_varL ts t =
  case (dest_term t) of
     VAR (_, ty) => ts
   | CONST _ => ts
   | LAMB (t1, t2) => 
      let
         val emp_s = Redblackset.empty String.compare;
         val ts1 = find_used_holvars res_varL emp_s t1
         val ts2 = find_used_holvars res_varL emp_s t2
         val ts12 = Redblackset.difference (ts2, ts1);
      in
         Redblackset.union (ts, ts12)
      end
   | COMB (t1, t2) => if (is_holfoot_var t) then Redblackset.add (ts, holfoot_var2string t) else
     if (is_holfoot_prog_with_resource t) then
     let
        val (res_nt, p, b) = dest_holfoot_prog_with_resource t;
        val tp = find_used_holvars res_varL (Redblackset.empty String.compare) p;
        val tpb = find_used_holvars res_varL tp b;

        val res_n = stringLib.fromHOLstring res_nt;
        val res_vars = assoc res_n res_varL;
        val tpbr = Redblackset.difference (tpb, string_list2set res_vars);
     in
         Redblackset.union (ts, tpbr)
     end else
     let
        val ts'  = find_used_holvars res_varL ts  t1;
        val ts'' = find_used_holvars res_varL ts' t2;
     in
        ts''
     end


fun get_read_write_var_set res_varL rwOpt wL aL =
let
   val (force_user_wr, wL1, rL1) = decode_rwOpt rwOpt;

   val (wL2, rL2) = if force_user_wr then (wL1, rL1) else
       let
          val t = absyn2term (Absyn.list_mk_pair aL);
          val rs = find_used_holvars res_varL (Redblackset.empty String.compare) t;
          val rL3 = Redblackset.listItems rs;
       in
          (wL1 @ wL, rL1@rL3)
       end

   val write_var_set = string_list2set wL2;
   val read_var_set  = string_list2set rL2;

   val read_var_set' = Redblackset.difference (read_var_set, write_var_set);
in
   (write_var_set, read_var_set')
end;




(*returns the abstract syntax of the statement as well as set of variables, that need write permissions.
  The set of variables that are read is figured out independently later. 
  Function calls might add to both sets by either their call-by-reference parameters or by
  accessing global variables. Therefore, function calls and their call-by-reference parameters
  are recorded as well *)
fun holfoot_p_statement2absyn funL resL vs (Pstm_assign (v, expr)) =
  let
     val var_term = string2holfoot_var v;
     val exp = holfoot_expression2absyn vs expr;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_assign_term, [Absyn.mk_AQ var_term, exp]);
  in
     (comb_a, [v], [])
  end
| holfoot_p_statement2absyn funL resL vs (Pstm_fldlookup (v, expr, tag)) =
  let
     val var_term = string2holfoot_var v;
     val exp_a = holfoot_expression2absyn vs expr;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_field_lookup_term, 
          [Absyn.mk_AQ var_term, exp_a, Absyn.mk_AQ (string2holfoot_tag tag)]);
  in
     (comb_a, [v], [])
  end
| holfoot_p_statement2absyn funL resL vs (Pstm_fldassign (expr1, tag, expr2)) =
  let
     val exp1 = holfoot_expression2absyn vs expr1;
     val exp2 = holfoot_expression2absyn vs expr2;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_field_assign_term, [
          exp1, Absyn.mk_AQ (string2holfoot_tag tag), exp2]);
  in
     (comb_a, [], [])
  end
| holfoot_p_statement2absyn funL resL vs (Pstm_new (v, expr, tl)) =
  let
     val var_term = string2holfoot_var v;
     val exp = holfoot_expression2absyn vs expr;
     val tl_L = map string2holfoot_tag tl;
     val tl_t = listSyntax.mk_list (tl_L, holfoot_tag_ty);
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_new_term, [exp, Absyn.mk_AQ var_term, Absyn.mk_AQ tl_t]);
  in
     (comb_a, [v], [])
  end  
| holfoot_p_statement2absyn funL resL vs (Pstm_dispose (expr1, expr2)) =
  let
     val exp1 = holfoot_expression2absyn vs expr1;
     val exp2 = holfoot_expression2absyn vs expr2;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_dispose_term, [exp2,exp1]);
  in
     (comb_a, [], [])
  end  
| holfoot_p_statement2absyn funL resL vs (Pstm_block stmL) =
  let
     val l0 = map (holfoot_p_statement2absyn funL resL vs) stmL;      
     val (aL, wL, fL) = foldr (fn ((a, wL', fL'), (aL, wL, fL)) =>
          (a::aL, wL'@wL, fL'@fL)) ([],[],[]) l0;
     val comb_a = Absyn.mk_app (Absyn.mk_AQ holfoot_prog_block_term, mk_list aL);
   in
     (comb_a, wL, fL)
   end
| holfoot_p_statement2absyn funL resL vs (Pstm_if (cond, stm1, stm2)) =
   let
      val c_a = holfoot_p_condition2absyn vs cond;
      val (stm1, wL1, fL1) = holfoot_p_statement2absyn funL resL vs stm1;
      val (stm2, wL2, fL2) = holfoot_p_statement2absyn funL resL vs stm2;

      val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_cond_term, 
             [c_a, stm1, stm2]);
   in
      (comb_a, wL1@wL2, fL1@fL2)
   end
| holfoot_p_statement2absyn funL resL vs (Pstm_while (rwOpt, i, cond, stm1)) =
   let
      val (use_inv, i_a) = if isSome i then
              (true, holfoot_a_proposition2absyn vs (valOf i))
          else (false, Absyn.mk_AQ holfoot_stack_true_term)

      val (stm1_a, wL, fL) = holfoot_p_statement2absyn funL resL vs stm1;
      val c_a = holfoot_p_condition2absyn vs cond;
      val while_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_while_term, [c_a,stm1_a]); 

      val (write_var_set, read_var_set) = get_read_write_var_set resL rwOpt wL [i_a, while_a]

      val full_a = if not use_inv then while_a else
         let
            val prop_a = mk_holfoot_prop_input_absyn write_var_set read_var_set i_a;
            val cond_free_var_list = free_vars (absyn2term prop_a);
            val abs_prop_a = mk_list_plam cond_free_var_list prop_a
         in
            Absyn.list_mk_app (Absyn.IDENT (locn.Loc_None, "fasl_comment_loop_invariant"), [
               abs_prop_a, while_a])
         end
   in
      (full_a, wL, fL)
   end
| holfoot_p_statement2absyn funL resL vs (Pstm_block_spec (loop, rwOpt, pre, stm1, post)) =
   let
      val pre_a  = holfoot_a_proposition2absyn vs pre;
      val post_a = holfoot_a_proposition2absyn vs post;
      val (force_user_wr, write_var_set_user, read_var_set_user) = decode_rwOpt rwOpt;

      val (stm1_a, wL, fL) = holfoot_p_statement2absyn funL resL vs stm1;

      val (write_var_set, read_var_set) = get_read_write_var_set resL rwOpt wL [
         pre_a, post_a, stm1_a]

      val (pre_a2, post_a2) = 
         let
            val pre_a3 =  mk_holfoot_prop_input_absyn write_var_set read_var_set pre_a
            val post_a3 = mk_holfoot_prop_input_absyn write_var_set read_var_set post_a
            val cond_free_var_list = HOLset.listItems (FVL [absyn2term pre_a3, absyn2term post_a3] empty_tmset);
            val abs_pre_a = mk_list_plam cond_free_var_list pre_a3
            val abs_post_a = mk_list_plam cond_free_var_list post_a3
         in
            (abs_pre_a, abs_post_a)
         end
      val stm1_a = if not loop then stm1_a else
          let
             fun isPstm_block (Pstm_block _) = true
               | isPstm_block _ = false;
             val stm1_a' = if isPstm_block stm1 then stm1_a else 
                 (Absyn.mk_app (Absyn.mk_AQ holfoot_prog_block_term, mk_list [stm1_a]));
          in
             stm1_a'
          end;
      val spec_a = Absyn.list_mk_app (
          Absyn.IDENT (locn.Loc_None, if loop then "fasl_comment_loop_spec" else
                "fasl_comment_block_spec"),
          [Absyn.mk_pair (pre_a2, post_a2), stm1_a]);
   in
      (spec_a, wL, fL)
   end
| holfoot_p_statement2absyn funL resL vs (Pstm_withres (res, cond, stm1)) =
   let
      val c_a = holfoot_p_condition2absyn vs cond;
      val (stm1_a,wL,fL) = holfoot_p_statement2absyn funL resL vs stm1;
      val res_term = stringLib.fromMLstring res;
      val res_varL = assoc res resL handle HOL_ERR _ => 
           let
              val _ = AssembleHolfootParser.print_parse_error (
                  "Undeclared resource '"^res^"' used!");
           in
              Feedback.fail()
           end;
      val wL' = filter (fn v => not (mem v res_varL)) wL;
      val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_with_resource_term, [
              Absyn.mk_AQ res_term, c_a, stm1_a]);
   in
      (comb_a, wL', fL)
   end
| holfoot_p_statement2absyn funL resL vs (Pstm_fcall(name,args)) =
       holfoot_fcall2absyn funL vs (name, args)
| holfoot_p_statement2absyn funL resL vs (Pstm_parallel_fcall(name1,args1,name2,args2)) =
       holfoot_parallel_fcall2absyn funL vs (name1, args1, name2, args2);



(*
val dummy_fundecl =
Pfundecl("proc", ([], ["x", "y"]),
                       SOME(Aprop_spred(Aspred_pointsto(Aexp_ident "x", []))),
                       [],
                       [Pstm_fldassign(Pexp_ident "x", "tl", Pexp_ident "y")],
                       SOME(Aprop_spred(Aspred_pointsto(Aexp_ident "x",
                                                        [("tl",
                                                          Aexp_ident "y")]))))


fun destPfundecl (Pfundecl(funname, (ref_args, val_args), preCond, localV, 
   fun_body, postCond)) =
   (funname, (ref_args, val_args), preCond, localV, 
   fun_body, postCond);

val (funname, (ref_args, val_args), preCondOpt, localV, 
   fun_body, postCondOpt) = destPfundecl dummy_fundecl;

val var = "y";
val term = fun_body_term; 
*)







(*
   fun dest_Presource (Presource(resname, varL, invariant)) =
        (resname, varL, invariant);


   val (resname, varL, invariant) = dest_Presource ((el 2 (program_item_decl)));

*)


fun Presource2hol vs (Presource(resname, varL, invariant)) =
let
   val write_varL = map string2holfoot_var varL;
   val i_a = holfoot_a_proposition2absyn vs invariant;
in
   (resname, (absyn2term i_a, write_varL))
end |
 Presource2hol _ _ = Raise (holfoot_unsupported_feature_exn ("-"));



(*
   fun dest_Pfundecl (Pfundecl(funname, (ref_args, val_args), preCondOpt, localV, 
   fun_body, postCondOpt)) = (funname, (ref_args, val_args), preCondOpt, localV, 
   fun_body, postCondOpt);


   val (funname, (ref_args, val_args), preCondOpt, localV, 
   fun_body, postCondOpt) = dest_Pfundecl ((el 2 (program_item_decl)));

   val resL = resource_parseL
   val resL = []
   val funL = []
*)

fun extend_set_if_necessary b (s1, s2) =
  let
     val s' = Redblackset.difference (s2, s1);
  in
     if Redblackset.isEmpty s' then (s1, b) else
          (Redblackset.union (s1, s'), true)
  end;


fun Pfundecl_preprocess resL (funL, vs, 
   Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV, 
   fun_body, postCondOpt)) = 
let
   val (fun_body_a, wL, funcalls) = 
        holfoot_p_statement2absyn funL resL vs (Pstm_block fun_body)
   val pre_a  = holfoot_a_proposition2absyn vs (invariant2a_proposition preCondOpt);
   val post_a = holfoot_a_proposition2absyn vs (invariant2a_proposition postCondOpt);

   val aL_t = absyn2term (Absyn.list_mk_pair [fun_body_a, pre_a, post_a]);
   val (ws, rs) = get_read_write_var_set resL rwOpt wL [Absyn.mk_AQ aL_t];
   val vs' = Redblackset.union (ws, rs);
   val local_vars = val_args@localV;
   val ws' = Redblackset.difference (ws, string_list2set local_vars)
   val rs' = Redblackset.difference (rs, string_list2set local_vars)

   val (vs_vars2, changed) = extend_set_if_necessary false (fst vs, vs');
   val vs2 = (vs_vars2, snd vs);
   val (pL, rpe, wpe) = assoc funname funL handle HOL_ERR _ => Feedback.failwith (
          "Unknown function '"^funname^"'")
   val pL2 = map (fn s => Redblackset.member (ws', s)) ref_args;
   val changed = changed orelse not (pL2 = pL);
 
   val (rps2, changed) = extend_set_if_necessary changed
         (string_list2set rpe, Redblackset.difference (rs', string_list2set ref_args))
   val (wps2, changed) = extend_set_if_necessary changed
         (string_list2set wpe, Redblackset.difference (ws', string_list2set ref_args))
   val rpe2 = Redblackset.listItems rps2;
   val wpe2 = Redblackset.listItems wps2;
in
   (changed, funname, pre_a, fun_body_a, post_a, ws', rs', vs2, pL2, rpe2, wpe2)
end;

fun Pfundecl2hol_final (funname, assume_opt, ref_args, val_args, localV, 
   pre_t, fun_body_t, post_t, ws, rs) = 
   let
   val fun_body_local_var_term = foldr holfoot_mk_local_var fun_body_t localV;

   val used_vars = ref (free_vars fun_body_local_var_term);
   fun mk_new_var x = let
                    val v = variant (!used_vars) (mk_var x);
                    val _ = used_vars := v::(!used_vars);
                 in v end;
   val arg_ref_term = mk_new_var ("arg_refL", Type `:holfoot_var list`);
   val arg_val_term = mk_new_var ("arg_valL", Type `:num list`);
   val arg_valL = mk_el_list (length val_args) arg_val_term;

   val fun_body_val_args_term = foldr holfoot_mk_call_by_value_arg fun_body_local_var_term (zip val_args arg_valL);

   val arg_refL = mk_el_list (length ref_args) arg_ref_term;
   val arg_ref_varL = map string2holfoot_var ref_args;
   val arg_ref_subst = map (fn (vt, s) => (vt |-> s)) (zip arg_ref_varL arg_refL)
   val fun_body_final_term = subst arg_ref_subst fun_body_val_args_term;
   val fun_term = pairLib.mk_pabs (pairLib.mk_pair(arg_ref_term, arg_val_term), fun_body_final_term);

   val arg_val_varL = map (fn s => mk_comb (holfoot_exp_var_term, string2holfoot_var s)) val_args;
   val arg_val_expL = map (fn c => mk_comb (holfoot_exp_const_term, c)) arg_valL;
   val arg_val_subst1 = map (fn (vt, s) => (vt |-> s)) (zip arg_val_varL arg_val_expL);

   val arg_val_numL = map (fn s => mk_var (s, numLib.num)) val_args;
   val arg_val_subst2 = map (fn (vt, s) => (vt |-> s)) (zip arg_val_numL arg_valL);
   val arg_val_subst = append arg_val_subst1 arg_val_subst2;

   val preCond2 = mk_holfoot_prop_input ws rs pre_t;
   val postCond2 = mk_holfoot_prop_input ws rs post_t;

   val preCond3 = subst (append arg_val_subst arg_ref_subst) preCond2;
   val postCond3 = subst (append arg_val_subst arg_ref_subst) postCond2;


   val cond_free_var_list = 
       let
          val set1 = HOLset.addList(empty_tmset, free_vars preCond3);
          val set2 = HOLset.addList(set1, free_vars postCond3);
          val set3 = HOLset.delete (set2, arg_ref_term) handle HOLset.NotFound => set2;
          val set4 = HOLset.delete (set3, arg_val_term) handle HOLset.NotFound => set3;
          val set5 = HOLset.delete (set4, fun_body_final_term) handle HOLset.NotFound => set4;
       in
          HOLset.listItems set5
       end;
   
   val ref_arg_names = listSyntax.mk_list (map string_to_label ref_args, markerSyntax.label_ty);
   val val_args_const = map (fn s => s ^ "_const") val_args;
   val val_arg_names = listSyntax.mk_list (map string_to_label val_args_const, markerSyntax.label_ty);

   val wrapped_preCond = list_mk_icomb (fasl_procedure_call_preserve_names_wrapper_term,
      [ref_arg_names, val_arg_names,
       pairLib.mk_pabs (pairLib.mk_pair(arg_ref_term, arg_val_term), preCond3),
       pairLib.mk_pair(arg_ref_term, arg_val_term)]);

   val abstr_prog = 
       list_mk_icomb (holfoot_prog_quant_best_local_action_term, [mk_list_pabs cond_free_var_list wrapped_preCond, mk_list_pabs cond_free_var_list postCond3])
   val abstr_prog_val_args_term = pairLib.mk_pabs (pairLib.mk_pair(arg_ref_term, arg_val_term), abstr_prog);
in
   (assume_opt, funname, fun_term, abstr_prog_val_args_term)
end;


fun Pfundecl_list2hol res_varL fun_decl_list =
let
   fun initPfundecl (Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV, 
   fun_body, postCondOpt)) =
      (funname, ((map (K false) ref_args), []:string list, []:string list))
   val init_funL = map initPfundecl fun_decl_list;		    
   val emp_s = Redblackset.empty String.compare
   val init = map (fn p => (init_funL, (emp_s,emp_s), p)) fun_decl_list

   fun internal l =
   let
      val l' = map (Pfundecl_preprocess res_varL) l;
      val changed = exists (#1) l';
   in
      if changed then
         let
           fun iter_funL (changed, funname, pre_a, fun_body_a, post_a, ws', rs', vs2, pL2, rpe2, wpe2) =
               (funname, (pL2, rpe2, wpe2))
           val funL' = map iter_funL l';
           fun iter_fin (p, (changed, funname, pre_a, fun_body_a, post_a, ws', rs', vs2, pL2, rpe2, wpe2)) =
               (funL', vs2, p)
           val l'' = map iter_fin (zip fun_decl_list l')
         in
           internal l''
         end
      else
        let
           fun fin (changed, funname, pre_a, fun_body_a, post_a, ws', rs', vs2, pL2, rpe2, wpe2) =
               (funname, pre_a, fun_body_a, post_a, ws', rs')
        in
           map fin l'
        end
   end;

   fun extract (Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV, 
      fun_body, postCondOpt), (funname2, pre_a, fun_body_a, post_a, ws, rs)) =
      let
         val tp = absyn2term (Absyn.list_mk_pair [pre_a, fun_body_a, post_a]);
         val tL = pairSyntax.strip_pair tp;
         val pre_t = el 1 tL
         val fun_body_t = el 2 tL
         val post_t = el 3 tL
      in
      (funname, assume_opt, ref_args, val_args, localV, 
       pre_t, fun_body_t, post_t, ws, rs)
      end;
   val finalL = map extract (zip fun_decl_list (internal init))
 
in
   map Pfundecl2hol_final finalL
end;



fun add_init_spec init_post_prop (Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV, 
   fun_body, postCondOpt)) =
   if (not (funname = "init")) then
      Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV, 
          fun_body, postCondOpt) (*unchanged*)
   else
      let
         val _ = if isSome preCondOpt orelse isSome postCondOpt orelse
                    isSome rwOpt orelse
                    not (ref_args = []) orelse not (val_args = []) then
                    raise holfoot_unsupported_feature_exn ("init function must not have parameters or pre- / postconditions") else ();                   
         val preCondOpt' = SOME (Aprop_spred Aspred_empty)
         val postCondOpt' = SOME init_post_prop
      in
         Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt', localV, 
             fun_body, postCondOpt') 
      end;


(*

val (funname, (ref_args, write_var_set, read_var_set, local_var_set,
        funcalls, done_funcalls),
        (fun_body_term, val_args, localV, preCond, postCond)) = 
 hd fun_decl_parse_read_writeL3;
*)



fun p_item___is_fun_decl (Pfundecl _) = true |
     p_item___is_fun_decl _ = false;


fun p_item___is_resource (Presource _) = true |
     p_item___is_resource _ = false;

(*
val examplesDir = Globals.HOLDIR  ^ "/examples/separationLogic/src/holfoot/EXAMPLES/";
val file = examplesDir ^ "mem.sf" ; 


val examplesDir = Globals.HOLDIR  ^ "/examples/separationLogic/src/holfoot/EXAMPLES/";
val file = examplesDir ^ "/automatic/entailments.ent" ; 

val prog2 = parse file
val t = parse_holfoot_file file


fun dest_Pprogram (Pprogram (ident_decl, program_item_decl)) = 
   (ident_decl, program_item_decl);

val (ident_decl, program_item_decl) = dest_Pprogram prog2;

val Pentailments ((comment, p1, p2)::_) = prog2
*)


fun Pprogram2hol procL_opt (Pprogram (ident_decl, program_item_decl)) =
   let
      (*ignore ident_decl*)

      (*parse resources*)
      val resource_list = filter p_item___is_resource program_item_decl;
      val emp_s = (Redblackset.empty String.compare);
      val resource_parseL = map (Presource2hol (emp_s, emp_s)) resource_list;
      val resource_parse_termL =map (fn (name, (prop, vars)) =>
          let
             val name_term = stringLib.fromMLstring name;
             val varL = listSyntax.mk_list (vars, Type `:holfoot_var`);
          in
             pairLib.mk_pair(name_term, pairLib.mk_pair(varL, prop))
          end) resource_parseL
      val resource_parseL_term = listSyntax.mk_list (resource_parse_termL,
                         Type `:string # holfoot_var list # holfoot_a_proposition`);
      val resource_term = mk_comb (HOLFOOT_LOCK_ENV_MAP_term, resource_parseL_term);


      (*parse procedure specs*)
      val fun_decl_list = filter p_item___is_fun_decl program_item_decl;
      val res_varL = map (fn Presource (n, vL, _) => (n, vL)) resource_list;
      val res_propL = map (fn Presource (_, _, p) => p) resource_list;
      val init_post_prop = if null res_propL then Aprop_spred Aspred_empty else
             (end_itlist (curry Aprop_star) res_propL)
      val fun_decl_list_init = map (add_init_spec init_post_prop) fun_decl_list
      val fun_decl_parseL = Pfundecl_list2hol res_varL fun_decl_list_init

      fun assume_proc_spec assume_opt proc =
         if (not assume_opt) then F else
         if (not (isSome procL_opt)) then T else
         if (mem proc (valOf procL_opt)) then T else F;

      fun mk_pair_terms (assume_opt, s, fun_body, spec) =
         pairLib.list_mk_pair [assume_proc_spec assume_opt s, stringLib.fromMLstring s, fun_body, spec];
      val fun_decl_parse_pairL = map mk_pair_terms fun_decl_parseL;

      val input = listSyntax.mk_list (fun_decl_parse_pairL, type_of (hd fun_decl_parse_pairL));

   in
      (list_mk_icomb (HOLFOOT_SPECIFICATION_term, [resource_term, input]))
   end;




fun mk_entailment (comment, p1, p2) =
let
   val empty_vs = (Redblackset.empty String.compare, Redblackset.empty String.compare);
   val a1 = holfoot_a_proposition2absyn empty_vs p1
   val a2 = holfoot_a_proposition2absyn empty_vs p2
   val (write_var_set, read_var_set) = get_read_write_var_set [] NONE [] [a1, a2]
   val varL = Redblackset.listItems (Redblackset.union (write_var_set, read_var_set))
   val var_tL = map string2holfoot_var varL
   val r_bag = bagSyntax.mk_bag (var_tL, holfoot_var_ty);
   val w_bag = bagSyntax.mk_bag ([], holfoot_var_ty);
   val bag_t = pairSyntax.mk_pair (w_bag, r_bag)

   val sr_t = pairSyntax.mk_pair (F, optionSyntax.mk_some 
        (listSyntax.mk_list ([string_to_label comment], markerSyntax.label_ty)))

   val a12_t = absyn2term (Absyn.mk_pair (a1, a2));
   val b1 = bagSyntax.mk_bag (strip_asl_star (rand (rator a12_t)),
         holfoot_a_proposition_ty)
   val b2 = bagSyntax.mk_bag (strip_asl_star (rand a12_t), holfoot_a_proposition_ty);

   val t0 = list_mk_comb (HOLFOOT_VAR_RES_FRAME_SPLIT_term, [sr_t, bag_t]);
   val t1 = mk_comb (t0, inst [alpha |-> holfoot_var_ty] bagSyntax.EMPTY_BAG_tm)
   val t2 = mk_comb (t1, inst [alpha |-> holfoot_a_proposition_ty] bagSyntax.EMPTY_BAG_tm)
   val t3 = list_mk_comb (t2, [b1,b2, HOLFOOT_VAR_RES_FRAME_SPLIT___EMP_PRED_term]);
in
   t3
end;


fun Pentailments2hol res_opt (Pentailments eL) =
   let
      val eL' = if isSome (res_opt) then
             filter (fn (c, p1, p2) => mem c (valOf res_opt)) eL else eL
      val tL = map mk_entailment eL'
   in
      (list_mk_conj tL)
   end;

fun Ptop2hol res_opt (Pentailments x) =
    Pentailments2hol res_opt (Pentailments x)
  | Ptop2hol res_opt (Pprogram x) =
    Pprogram2hol res_opt (Pprogram x);

val parse_holfoot_file = (Ptop2hol NONE) o parse;
fun parse_holfoot_file_restrict procL = (Ptop2hol (SOME procL)) o parse;

fun print_file_contents file =
   let
      val is = Portable.open_in file
      val _ = print ("\nContents of file \""^file^"\":\n\n");
      val _ = print "--------------------------------------------\n";
      val _ = while (not (Portable.end_of_stream is)) do
        (print (Portable.input_line is));
      val _ = Portable.close_in is;
      val _ = print "--------------------------------------------\n\n";
   in
      ()
   end

end
