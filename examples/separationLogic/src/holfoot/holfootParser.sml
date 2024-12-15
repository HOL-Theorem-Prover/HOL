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

use (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/hfheader.sml")

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

val list_data_tag = ref "hd";
val data_list_tag = ref "dta";
val array_data_tag = ref "dta";
val list_link_tag = ref "tl"
val tree_data_tag = ref "dta"
val tree_link_tags = ref ("l", "r")


fun mk_el_list 0 v = []
  | mk_el_list n v =
       (listSyntax.mk_hd v)::(mk_el_list (n-1) (listSyntax.mk_tl v))

fun mk_list [] = Absyn.mk_ident "NIL"
  | mk_list (e::es) =
      Absyn.mk_app (Absyn.mk_app (Absyn.mk_ident "CONS", e), mk_list es)

fun absyn2term a = absyn_to_term (#2 holfootTheory.holfoot_grammars) a

fun string_to_label s = mk_var (s, markerSyntax.label_ty);

val parse = AssembleHolfootParser.raw_read_file;


(*
val file = "/home/tuerk/Downloads/holfoot/EXAMPLES/business2.sf";
val file = "/home/tt291/Downloads/holfoot/EXAMPLES/business2.sf";

val prog = parse file;
*)

fun vstruct_idents s (Absyn.VAQ _) = s
  | vstruct_idents s (Absyn.VIDENT (_, i)) = Redblackset.add (s, i)
  | vstruct_idents s (Absyn.VPAIR (_, vs1, vs2)) =
       vstruct_idents (vstruct_idents s vs1) vs2
  | vstruct_idents s (Absyn.VTYPED (_, vs, _)) =
       vstruct_idents s vs;


fun map_ident (s,f,f2_opt,f3_opt) l = case l of
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
            val (s',  a1') = map_ident (s,f,f2_opt,f3_opt)   a1
            val (s'', a2') = map_ident (s',f,f2_opt,f3_opt) a2
         in
            (s'', Absyn.APP (locn,a1',a2'))
         end
  | Absyn.LAM   (locn,v,a) =>
         let
            val is = vstruct_idents (Redblackset.empty String.compare) v;
            val s' = if isSome f2_opt then (valOf f2_opt) s locn is else s;
            val (s'',  a') = map_ident (s',f,f2_opt, f3_opt) a
            val s''' = if isSome f3_opt then (valOf f3_opt) s'' locn is else s'';
         in
            (s''', Absyn.LAM (locn,v,a'))
         end
  | Absyn.TYPED (locn,a,p) =>
         let
            val (s',  a') = map_ident (s,f,f2_opt,f3_opt) a
         in
            (s', Absyn.TYPED (locn,a',p))
         end

fun collect_ident l =
let
   val is = Redblackset.empty String.compare
   fun col set l s = (Redblackset.add (set,s), Absyn.IDENT (l, s))
   fun del set l is = Redblackset.difference (set,is)
   val (set, _) = map_ident (is, col,NONE, SOME del) l
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
      map_ident (Redblackset.empty String.compare, subst_qv_ident, NONE, NONE) a

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
     fun a_subst set l i = (if Redblackset.member (set, i) then Feedback.fail() else
        (set, Absyn.mk_AQ (assoc i substL))) handle HOL_ERR _ => (set, Absyn.IDENT (l, i))
     fun my_union set l is = Redblackset.union (set, is);
     val (_, a') = map_ident (Redblackset.empty String.compare, a_subst, SOME my_union, NONE) a
     val qa = Absyn.mk_lam (Absyn.VAQ (locn.Loc_None, eL_v), a')

     val vL' = map (fn v => mk_comb(holfoot_exp_var_term, string2holfoot_var v)) vL;
     val vLt = listSyntax.mk_list (vL', holfoot_a_expression_ty);
  in
     (qa, vLt)
  end;


fun replace_old os_opt l = case l of
    Absyn.AQ    (locn,t)   => (os_opt, l)
  | Absyn.IDENT (locn,i)   => (os_opt, l)
  | Absyn.QIDENT(locn,t,i) => (os_opt, l)
  | Absyn.APP   (locn,Absyn.IDENT(_,"old"),Absyn.IDENT(_,v)) =>
    let
       val os = if isSome os_opt then valOf os_opt else
                  Feedback.failwith ("No old value of "^v^" available here!");
       val nv_opt = Redblackmap.peek (os, v);
       val (nv, os') = if isSome (nv_opt) then (valOf nv_opt, os) else
                       let
                          val nv = mk_var ("old_"^v, numLib.num);
                          val os' = Redblackmap.insert(os,v,nv);
                       in
                          (nv,os')
                       end;
    in
       (SOME os', Absyn.IDENT (locn,(fst o dest_var) nv))
    end
  | Absyn.APP   (locn,a1,a2) =>
         let
            val (os_opt, a1') = replace_old os_opt a1
            val (os_opt, a2') = replace_old os_opt a2
         in
            (os_opt, Absyn.APP (locn,a1',a2'))
         end
  | Absyn.LAM   (locn,v,a) =>
         let
            val (os_opt,  a') = replace_old os_opt a
         in
            (os_opt, Absyn.LAM (locn,v,a'))
         end
  | Absyn.TYPED (locn,a,p) =>
         let
            val (os_opt,  a') = replace_old os_opt a
         in
            (os_opt, Absyn.TYPED (locn,a',p))
         end


fun HOL_Absyn_old_vars vs (os_opt, cs_opt) h =
let
   val ha = HOL_Absyn h

   val (os_opt, ha) = replace_old os_opt ha;

   val (ha, cs_opt) = if (not (isSome cs_opt)) then (ha, NONE) else
       let
          val used_vars = Redblackset.intersection (collect_ident ha, fst vs);
          fun const_name v = v^"_lc";
          fun my_union set l is = Redblackset.union (set, is);
          fun my_work set l i =
            let
               val i' =  if not (Redblackset.member (used_vars, i)) orelse
                            Redblackset.member (set,i) then i else
                    ("_"^(const_name i))
             in
                (set, Absyn.IDENT (l, i'))
             end

          val (_, ha') = map_ident (Redblackset.empty String.compare,
               my_work, SOME my_union, NONE) ha;
          val used_varsL = Redblackset.listItems used_vars
          val cs_opt' = SOME (
               List.foldl (fn (k,d) => Redblackmap.insert (d, k,
                   mk_var(const_name k, numLib.num))) (valOf cs_opt) used_varsL)
       in
          (ha', cs_opt')
       end;
in
   ((os_opt, cs_opt), ha)
end;


fun holfoot_expression2absyn vs os_opt (Aexp_ident x) =
   if (String.sub (x, 0) = #"#") then
      (os_opt, Absyn.mk_app (Absyn.mk_AQ holfoot_exp_const_term,
          Absyn.mk_ident (String.substring(x, 1, (String.size x) - 1))))
   else if (is_holfoot_ex_ident x) orelse (Redblackset.member (snd vs, x)) then
      (os_opt, Absyn.mk_app (Absyn.mk_AQ holfoot_exp_const_term,
          Absyn.mk_ident x))
   else
      let
         val var_term = string2holfoot_var x;
         val term = mk_comb(holfoot_exp_var_term, var_term)
      in
         (os_opt, Absyn.mk_AQ term)
      end
| holfoot_expression2absyn vs os_opt (Aexp_old_ident x) =
   let
       val os = if isSome os_opt then valOf os_opt else
                  Feedback.failwith ("No old value of "^x^" available here!");
       val nv_opt = Redblackmap.peek (os, x);
       val (nv, os') = if isSome (nv_opt) then (valOf nv_opt, os) else
                       let
                          val nv = mk_var ("old_"^x, numLib.num);
                          val os' = Redblackmap.insert(os,x,nv);
                       in
                          (nv,os')
                       end;
       val et = mk_comb (holfoot_exp_const_term, nv);
   in
       (SOME os', Absyn.mk_AQ et)
   end
| holfoot_expression2absyn vs os_opt (Aexp_num n) =
     (os_opt, Absyn.mk_AQ (mk_comb (holfoot_exp_const_term, numLib.term_of_int n)))
| holfoot_expression2absyn vs os_opt (Aexp_infix (opstring, e1, e2)) =
   let
      val opterm = if (opstring = "-") then holfoot_exp_sub_term else
                   if (opstring = "+") then holfoot_exp_add_term else
                   if (opstring = "*") then holfoot_exp_mult_term else
                   if (opstring = "/") then holfoot_exp_div_term else
                   if (opstring = "%") then holfoot_exp_mod_term else
                   if (opstring = "^") then holfoot_exp_exp_term else
                       Raise (holfoot_unsupported_feature_exn ("Pexp_infix "^opstring));
      val (os_opt' , t1) = holfoot_expression2absyn vs os_opt  e1;
      val (os_opt'', t2) = holfoot_expression2absyn vs os_opt' e2;
   in
      (os_opt'', Absyn.list_mk_app (Absyn.mk_AQ opterm, [t1, t2]))
   end
| holfoot_expression2absyn vs os_opt (Aexp_hol h) =
      let
        val ((os_opt,_), ha) = HOL_Absyn_old_vars vs (os_opt,NONE) h;
        val used_vars = Redblackset.listItems (Redblackset.intersection (collect_ident ha, fst vs))
      in
        if (null used_vars) then
           (os_opt, Absyn.mk_app (Absyn.mk_AQ holfoot_exp_const_term, ha))
        else
           let
             val (qha, vLt) = absyn_extract_vars used_vars ha
           in
             (os_opt, Absyn.list_mk_app (Absyn.mk_AQ holfoot_exp_op_term, [qha, Absyn.mk_AQ vLt]))
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
      val (_, t1) = holfoot_expression2absyn vs NONE e1;
      val (_, t2) = holfoot_expression2absyn vs NONE e2;
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


fun tag_a_expression_list2absyn vs rvm [] = (rvm, Absyn.mk_AQ tag_a_expression_fmap_emp_term) |
    tag_a_expression_list2absyn vs rvm ((tag,exp1)::l) =
      let
         val tag_term = string2holfoot_tag tag;
         val (rvm', exp_absyn) = holfoot_expression2absyn vs rvm exp1;
         val a = Absyn.mk_pair (Absyn.mk_AQ tag_term, exp_absyn)
         val (rvm'', rest) = tag_a_expression_list2absyn vs rvm' l;
      in
         (rvm'', Absyn.list_mk_app (Absyn.mk_AQ tag_a_expression_fmap_update_term, [rest, a]))
      end;


val genpredMap = ref (Redblackmap.mkDict String.compare)
fun add_genpred (name:string, argL:Parsetree.a_genpredargType list, mk:Absyn.absyn list -> Absyn.absyn) =
let
   val map = (!genpredMap);
   val oldEntry = Redblackmap.find (map, name) handle Redblackmap.NotFound => [];
   val newEntry = (length argL, argL, mk)::oldEntry;
   val map = Redblackmap.insert (map, name, newEntry);
   val _ = genpredMap := map;
in
   ()
end;

fun reset_genpreds () =
let
   val _ = genpredMap := (Redblackmap.mkDict String.compare);
in
   ()
end;


fun lookup_genpredL name len =
let
   val l = Redblackmap.find ((!genpredMap), name);
   val l' = filter (fn (len', _, _) => (len = len')) l;
in
   List.map (fn (_, argL, mk) => (argL, mk)) l'
end handle Redblackmap.NotFound => [];


local
   exception arg_exception;

   fun arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_tag (Aspred_arg_exp (Aexp_ident arg)) =
         (os_opt, cs_opt, SOME (Absyn.mk_AQ (string2holfoot_tag arg)))
     | arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_exp (Aspred_arg_exp arg_exp) =
         let
            val (os_opt, exp) = holfoot_expression2absyn vs os_opt arg_exp
         in
            (os_opt, cs_opt, SOME exp)
         end
     | arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_hol (Aspred_arg_exp (Aexp_hol arg)) =
         let
            val ((os_opt, cs_opt), hol) = HOL_Absyn_old_vars vs (os_opt, cs_opt) arg;
         in
            (os_opt, cs_opt, SOME hol)
         end
     | arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_hol (Aspred_arg_exp (Aexp_ident arg)) =
       arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_hol (Aspred_arg_exp (Aexp_hol arg))
     | arg2absyn vs (os_opt, cs_opt) (Aspred_arg_ty_list Aspred_arg_ty_tag) (Aspred_arg_string_list argL) =
         let
            val tag_t = listSyntax.mk_list (
                 (map string2holfoot_tag argL), Type `:holfoot_tag`);
         in
            (os_opt, cs_opt, SOME (Absyn.mk_AQ tag_t))
         end
     | arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_comma Aspred_arg_comma =
         (os_opt, cs_opt, NONE)
     | arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_colon Aspred_arg_colon =
         (os_opt, cs_opt, NONE)
     | arg2absyn vs (os_opt, cs_opt) Aspred_arg_ty_semi Aspred_arg_semi =
         (os_opt, cs_opt, NONE)
     | arg2absyn _ _ _ _ = raise arg_exception;


   fun args2absyn vs (os_opt, cs_opt) [] [] = (os_opt, cs_opt, [])
     | args2absyn vs (os_opt, cs_opt) (ty::tys) (arg::args) =
       let
          val (os_opt, cs_opt, r_opt)  = arg2absyn  vs (os_opt, cs_opt) ty arg;
          val (os_opt, cs_opt, rs) = args2absyn vs (os_opt, cs_opt) tys args;

          val rs' = case r_opt of SOME r => r::rs | NONE => rs;
       in
          (os_opt, cs_opt, rs')
       end;

in

fun holfoot_a_genpred2absyn vs (os_opt, cs_opt) name args line =
   let
      val candidates = lookup_genpredL name (length args);
      fun try_canditate (arg_tys, c) =
      let
          val (os_opt, cs_opt, absynArgs) = args2absyn vs (os_opt, cs_opt) arg_tys args
      in
         ((os_opt, cs_opt), c absynArgs)
      end handle arg_exception => Feedback.fail ()
   in
      tryfind try_canditate candidates handle HOL_ERR _ =>
         let
         val _ = AssembleHolfootParser.print_parse_error (
                  "Undefined predicate '"^name^"' found in line "^
                  (Int.toString (line+1))^"!")
         in
         ((os_opt, cs_opt), Absyn.mk_typed(Absyn.mk_ident ("!!!ERROR "^name^"!!!"),
                            Pretype.fromType holfoot_a_proposition_ty)) end
   end;
end




fun holfoot_a_space_pred2absyn vs (os_opt, cs_opt) (Aspred_empty) =
   ((os_opt, cs_opt), Absyn.mk_AQ holfoot_stack_true_term)
| holfoot_a_space_pred2absyn vs (os_opt, cs_opt) (Aspred_genpred (name,args,(_,line))) =
  holfoot_a_genpred2absyn vs (os_opt, cs_opt) name args line
| holfoot_a_space_pred2absyn vs (os_opt, cs_opt) (Aspred_boolhol h) =
      let
        val ((os_opt, _), ha) = HOL_Absyn_old_vars vs (os_opt, NONE) h;
        val used_vars = Redblackset.listItems (Redblackset.intersection (collect_ident ha, fst vs))
      in
        if (null used_vars) then
           ((os_opt, cs_opt), Absyn.mk_app (Absyn.mk_AQ holfoot_bool_proposition_term, ha))
        else
           let
              val (qha, vLt) = absyn_extract_vars used_vars ha
           in
              ((os_opt, cs_opt), Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_expression_term, [qha, Absyn.mk_AQ vLt]))
           end
      end
| holfoot_a_space_pred2absyn vs (os_opt, cs_opt) (Aspred_hol s) =
  HOL_Absyn_old_vars vs (os_opt, cs_opt) s
| holfoot_a_space_pred2absyn vs (os_opt, cs_opt) (Aspred_pointsto (exp, pl)) =
  let
     val (os_opt, a1) = holfoot_expression2absyn vs os_opt exp;
     val (os_opt, a2) = tag_a_expression_list2absyn vs os_opt pl;
  in
     ((os_opt, cs_opt), Absyn.list_mk_app(Absyn.mk_AQ holfoot_ap_points_to_term, [a1, a2]))
  end;



fun invariant2a_proposition NONE =
    Aprop_spred Aspred_empty
  | invariant2a_proposition (SOME p) = p


val holfoot_map_absyn = Absyn ([QUOTE
      "var_res_map DISJOINT_FMAP_UNION"])

fun holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_infix (opString, exp1, exp2)) =
  let
    val op_term = if (opString = "<") then holfoot_ap_lt_term else
                  if (opString = "<=") then holfoot_ap_le_term else
                  if (opString = ">") then holfoot_ap_gt_term else
                  if (opString = ">=") then holfoot_ap_ge_term else
                  if (opString = "==") then holfoot_ap_equal_term else
                  if (opString = "!=") then holfoot_ap_unequal_term else
                     Raise (holfoot_unsupported_feature_exn ("Aexp_infix "^opString))
    val (os_opt, t1) = holfoot_expression2absyn vs os_opt exp1;
    val (os_opt, t2) = holfoot_expression2absyn vs os_opt exp2;
  in
    ((os_opt,cs_opt), Absyn.list_mk_app (Absyn.mk_AQ op_term, [t1, t2]))
  end
| holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_false) =
    ((os_opt,cs_opt), Absyn.mk_AQ holfoot_ap_false_term)
| holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_ifthenelse (Aprop_infix (opString,exp1,exp2),ap1,ap2)) =
  let
      val (ap1,ap2) = if opString = "==" then (ap1,ap2) else
                      if opString = "!=" then (ap2,ap1) else
                      Raise (holfoot_unsupported_feature_exn "Currently only equality checks are allowed as conditions in propositions")

      val (os_opt, exp1)  = holfoot_expression2absyn vs os_opt exp1;
      val (os_opt, exp2)  = holfoot_expression2absyn vs os_opt exp2;
      val ((os_opt,cs_opt), prop1) = holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) ap1;
      val ((os_opt,cs_opt), prop2) = holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) ap2;
   in
      ((os_opt,cs_opt), Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_eq_cond_term, [exp1, exp2, prop1, prop2]))
   end
| holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_ifthenelse _) =
     Raise (holfoot_unsupported_feature_exn "Currently only equality checks are allowed as conditions in propositions")
| holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_star (ap1, ap2)) =
  let
     val ((os_opt,cs_opt), prop1) = holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) ap1;
     val ((os_opt,cs_opt), prop2) = holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) ap2;
  in
     ((os_opt,cs_opt), Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_star_term, [prop1, prop2]))
  end
| holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_map (vL, ap, l)) =
  let
      val vs2 = (fst vs, Redblackset.addList (snd vs, vL))
      val ((os_opt,cs_opt), ap_a) = holfoot_a_proposition2absyn_context vs2 (os_opt,cs_opt) ap;
      val pair_vs = end_itlist (fn v1 => fn v2 => Absyn.VPAIR (locn.Loc_None, v1, v2))
                    (map (fn v => Absyn.VIDENT (locn.Loc_None, v)) vL)
      val ap_la = Absyn.mk_lam (pair_vs,ap_a)
      val l_a = HOL_Absyn l;
  in
     ((os_opt,cs_opt), Absyn.list_mk_app (holfoot_map_absyn,[ap_la, l_a]))
  end
| holfoot_a_proposition2absyn_context vs (os_opt,cs_opt) (Aprop_spred sp) =
     holfoot_a_space_pred2absyn vs (os_opt,cs_opt) sp;


exception NothingToDo;
fun add_var_equations m a =
let
   val L = Redblackmap.listItems m;
   val _ = if null L then raise NothingToDo else ();
   fun mk_old_eq (hv, v) =
       list_mk_comb (holfoot_ap_equal_term, [
           mk_comb(holfoot_exp_var_term, string2holfoot_var hv),
           mk_comb(holfoot_exp_const_term, v)])
   val eqL = List.map mk_old_eq L
   val eq_star = end_itlist (fn t => fn ts =>
         list_mk_comb (holfoot_ap_star_term, [t, ts])) eqL;

   val a' =  Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_star_term,
      [Absyn.mk_AQ eq_star, a])
in
   a'
end handle NothingToDo => a;


fun holfoot_a_proposition2absyn vs os_opt x =
let
   val ((os_opt,cs_opt), a1) = holfoot_a_proposition2absyn_context vs
       (os_opt, SOME (Redblackmap.mkDict String.compare)) x;

   val a2 = if isSome cs_opt then add_var_equations (valOf cs_opt) a1 else a1;

   val (s, a3) = remove_qv a2
   val cs_opt = SOME (Redblackmap.mkDict String.compare)
   val s' = if not (isSome cs_opt) then s else
                let
                   val vL = List.map (fst o dest_var o snd) (Redblackmap.listItems (valOf cs_opt))
                in
                   Redblackset.addList (s, vL)
                end
   val ex_vars = Redblackset.listItems s';

   val a4 = foldr (fn (v,a) =>
       let
          val a_lam = Absyn.mk_lam (Absyn.VIDENT (locn.Loc_None, v), a);
          val a' = Absyn.mk_app (Absyn.mk_ident "asl_exists", a_lam);
       in a' end) a3 ex_vars
in
   (os_opt, a4)
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

   val vp_a = mk_list (map (fn t => snd (holfoot_expression2absyn vs NONE t)) vp);

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


fun rewrite_old_var os pre_a post_a =
let
   val pre_a' = add_var_equations os pre_a;
in
   (pre_a', post_a)
end


fun global_vars_restrict global_vars =
 filter (fn v =>
    not (Redblackset.member (global_vars, fst (dest_var v))));


fun free_vars_restrict global_vars t =
let
   val fv_list = free_vars t;
in
   global_vars_restrict global_vars fv_list
end


(*returns the abstract syntax of the statement as well as set of variables, that need write permissions.
  The set of variables that are read is figured out independently later.
  Function calls might add to both sets by either their call-by-reference parameters or by
  accessing global variables. Therefore, function calls and their call-by-reference parameters
  are recorded as well *)
fun holfoot_p_statement2absyn funL resL gv vs (Pstm_assign (v, expr)) =
  let
     val var_term = string2holfoot_var v;
     val (_, exp) = holfoot_expression2absyn vs NONE expr;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_assign_term, [Absyn.mk_AQ var_term, exp]);
  in
     (comb_a, [v], [])
  end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_fldlookup (v, expr, tag)) =
  let
     val var_term = string2holfoot_var v;
     val (_, exp_a) = holfoot_expression2absyn vs NONE expr;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_field_lookup_term,
          [Absyn.mk_AQ var_term, exp_a, Absyn.mk_AQ (string2holfoot_tag tag)]);
  in
     (comb_a, [v], [])
  end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_fldassign (expr1, tag, expr2)) =
  let
     val (_, exp1) = holfoot_expression2absyn vs NONE expr1;
     val (_, exp2) = holfoot_expression2absyn vs NONE expr2;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_field_assign_term, [
          exp1, Absyn.mk_AQ (string2holfoot_tag tag), exp2]);
  in
     (comb_a, [], [])
  end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_new (v, expr, tl)) =
  let
     val var_term = string2holfoot_var v;
     val (_, exp) = holfoot_expression2absyn vs NONE expr;
     val tl_L = map string2holfoot_tag tl;
     val tl_t = listSyntax.mk_list (tl_L, holfoot_tag_ty);
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_new_term, [exp, Absyn.mk_AQ var_term, Absyn.mk_AQ tl_t]);
  in
     (comb_a, [v], [])
  end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_dispose (expr1, expr2)) =
  let
     val (_, exp1) = holfoot_expression2absyn vs NONE expr1;
     val (_, exp2) = holfoot_expression2absyn vs NONE expr2;
     val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_dispose_term, [exp2,exp1]);
  in
     (comb_a, [], [])
  end
| holfoot_p_statement2absyn funL resL gv vs Pstm_diverge =
     (Absyn.mk_AQ holfoot_prog_diverge_term, [], [])
| holfoot_p_statement2absyn funL resL gv vs Pstm_fail =
     (Absyn.mk_AQ holfoot_prog_fail_term, [], [])
| holfoot_p_statement2absyn funL resL gv vs (Pstm_block stmL) =
  let
     val l0 = map (holfoot_p_statement2absyn funL resL gv vs) stmL;
     val (aL, wL, fL) = foldr (fn ((a, wL', fL'), (aL, wL, fL)) =>
          (a::aL, wL'@wL, fL'@fL)) ([],[],[]) l0;
     val comb_a = Absyn.mk_app (Absyn.mk_AQ holfoot_prog_block_term, mk_list aL);
   in
     (comb_a, wL, fL)
   end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_if (cond, stm1, stm2)) =
   let
      val c_a = holfoot_p_condition2absyn vs cond;
      val (stm1, wL1, fL1) = holfoot_p_statement2absyn funL resL gv vs stm1;
      val (stm2, wL2, fL2) = holfoot_p_statement2absyn funL resL gv vs stm2;

      val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_cond_term,
             [c_a, stm1, stm2]);
   in
      (comb_a, wL1@wL2, fL1@fL2)
   end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_ndet (stm1, stm2)) =
   let
      val (stm1, wL1, fL1) = holfoot_p_statement2absyn funL resL gv vs stm1;
      val (stm2, wL2, fL2) = holfoot_p_statement2absyn funL resL gv vs stm2;

      val comb_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_choice_term,
             [stm1, stm2]);
   in
      (comb_a, wL1@wL2, fL1@fL2)
   end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_while (unroll, rwOpt, i, cond, stm1)) =
   let
      val (use_inv, i_a) = if isSome i then
              (true, snd (holfoot_a_proposition2absyn vs NONE (valOf i)))
          else (false, Absyn.mk_AQ holfoot_stack_true_term)

      val (stm1_a, wL, fL) = holfoot_p_statement2absyn funL resL gv vs stm1;
      val c_a = holfoot_p_condition2absyn vs cond;
      val while_a = Absyn.list_mk_app (Absyn.mk_AQ holfoot_prog_while_term, [c_a,stm1_a]);

      val (write_var_set, read_var_set) = get_read_write_var_set resL rwOpt wL [i_a, while_a]

      val full_a = if not use_inv then while_a else
         let
            val prop_a = mk_holfoot_prop_input_absyn write_var_set read_var_set i_a;
            val cond_free_var_list = free_vars_restrict gv (absyn2term prop_a);
            val abs_prop_a = mk_list_plam cond_free_var_list prop_a
         in
            Absyn.list_mk_app (Absyn.IDENT (locn.Loc_None, "asl_comment_loop_invariant"), [
               abs_prop_a, while_a])
         end
      val unroll_a = if unroll = 0 then full_a else
            Absyn.list_mk_app (Absyn.IDENT (locn.Loc_None, "asl_comment_loop_unroll"), [
                Absyn.mk_AQ (numLib.term_of_int unroll), full_a])

   in
      (unroll_a, wL, fL)
   end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_block_spec (loop, unroll, rwOpt, pre, stm1, post)) =
   let
      val (_, pre_a)  = holfoot_a_proposition2absyn vs NONE pre;
      val (SOME os, post_a) = holfoot_a_proposition2absyn vs (SOME (Redblackmap.mkDict String.compare)) post;
      val (pre_a, post_a) = rewrite_old_var os pre_a post_a;
      val (force_user_wr, write_var_set_user, read_var_set_user) = decode_rwOpt rwOpt;

      val (stm1_a, wL, fL) = holfoot_p_statement2absyn funL resL gv vs stm1;

      val (write_var_set, read_var_set) = get_read_write_var_set resL rwOpt wL [
         pre_a, post_a, stm1_a]

      val (pre_a2, post_a2) =
         let
            val pre_a3 =  mk_holfoot_prop_input_absyn write_var_set read_var_set pre_a
            val post_a3 = mk_holfoot_prop_input_absyn write_var_set read_var_set post_a
            val cond_free_var_list = global_vars_restrict gv (
                HOLset.listItems (FVL [absyn2term pre_a3, absyn2term post_a3] empty_tmset));
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
          Absyn.IDENT (locn.Loc_None, if loop then "asl_comment_loop_spec" else
                "asl_comment_block_spec"),
          [Absyn.mk_pair (pre_a2, post_a2), stm1_a]);
      val unroll_a = if unroll = 0 then spec_a else
            Absyn.list_mk_app (Absyn.IDENT (locn.Loc_None, "asl_comment_loop_unroll"), [
                Absyn.mk_AQ (numLib.term_of_int unroll), spec_a])
   in
      (unroll_a, wL, fL)
   end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_withres (res, cond, stm1)) =
   let
      val c_a = holfoot_p_condition2absyn vs cond;
      val (stm1_a,wL,fL) = holfoot_p_statement2absyn funL resL gv vs stm1;
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
| holfoot_p_statement2absyn funL resL gv vs (Pstm_assert p) =
   let
      val (_, p_a)  = holfoot_a_proposition2absyn vs NONE p;
      val abs_p_a =
         let
            val cond_free_var_list = global_vars_restrict gv (
                HOLset.listItems (FVL [absyn2term p_a] empty_tmset));
            val abs_p_a = mk_list_plam cond_free_var_list p_a
         in
            abs_p_a
         end
      val comb_a =  Absyn.mk_app (
          Absyn.IDENT (locn.Loc_None, "asl_comment_assert"), abs_p_a);
   in
      (comb_a, [], [])
   end
| holfoot_p_statement2absyn funL resL gv vs (Pstm_fcall(name,args)) =
       holfoot_fcall2absyn funL vs (name, args)
| holfoot_p_statement2absyn funL resL gv vs (Pstm_parallel_fcall(name1,args1,name2,args2)) =
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
   val (_, i_a) = holfoot_a_proposition2absyn vs NONE invariant;
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


fun Pfundecl_preprocess resL global_vars (funL, vs,
   Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV,
   fun_body, postCondOpt)) =
let
   val (fun_body_a, wL, funcalls) =
        holfoot_p_statement2absyn funL resL global_vars vs (Pstm_block fun_body)

   val vs_na = (List.foldl (fn (v,vs) => Redblackset.delete (vs, v) handle NotFound => vs) (fst vs) val_args, snd vs);
   val (_, pre_a)  = holfoot_a_proposition2absyn vs_na NONE (invariant2a_proposition preCondOpt);
   val (SOME os, post_a) = holfoot_a_proposition2absyn vs_na (SOME (Redblackmap.mkDict String.compare))
        (invariant2a_proposition postCondOpt);
   val (pre_a, post_a) = rewrite_old_var os pre_a post_a;

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
   global_vars, pre_t, fun_body_t, post_t, ws, rs) =
   let
   val fun_body_local_var_term = foldr holfoot_mk_local_var fun_body_t localV;

   val used_vars = ref (free_vars_restrict global_vars fun_body_local_var_term);
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
          val set1 = HOLset.addList(empty_tmset, free_vars_restrict global_vars preCond3);
          val set2 = HOLset.addList(set1, free_vars_restrict global_vars postCond3);
          val set3 = HOLset.delete (set2, arg_ref_term) handle HOLset.NotFound => set2;
          val set4 = HOLset.delete (set3, arg_val_term) handle HOLset.NotFound => set3;
          val set5 = HOLset.delete (set4, fun_body_final_term) handle HOLset.NotFound => set4;
          val fv_list = HOLset.listItems set5;
       in
         fv_list
       end;

   val ref_arg_names = listSyntax.mk_list (map string_to_label ref_args, markerSyntax.label_ty);
   val val_args_const = map (fn s => s ^ "_const") val_args;
   val val_arg_names = listSyntax.mk_list (map string_to_label val_args_const, markerSyntax.label_ty);

   val wrapped_preCond = list_mk_icomb (asl_procedure_call_preserve_names_wrapper_term,
      [ref_arg_names, val_arg_names,
       pairLib.mk_pabs (pairLib.mk_pair(arg_ref_term, arg_val_term), preCond3),
       pairLib.mk_pair(arg_ref_term, arg_val_term)]);

   val abstr_prog =
       list_mk_icomb (holfoot_prog_quant_best_local_action_term, [mk_list_pabs cond_free_var_list wrapped_preCond, mk_list_pabs cond_free_var_list postCond3])
   val abstr_prog_val_args_term = pairLib.mk_pabs (pairLib.mk_pair(arg_ref_term, arg_val_term), abstr_prog);

   (*access to global variables*)
   val global_vars = Redblackset.listItems (Redblackset.difference (Redblackset.union (ws, rs),
      string_list2set (ref_args @ val_args @ localV)))
in
   (assume_opt, funname, fun_term, abstr_prog_val_args_term, global_vars)
end;


fun Pfundecl_list2hol global_vars res_varL fun_decl_list =
let
   fun initPfundecl (Pfundecl(assume_opt, funname, (ref_args, val_args), rwOpt, preCondOpt, localV,
   fun_body, postCondOpt)) =
      (funname, ((map (K false) ref_args), []:string list, []:string list))
   val init_funL = map initPfundecl fun_decl_list;
   val emp_s = Redblackset.empty String.compare
   val init = map (fn p => (init_funL, (emp_s,emp_s), p)) fun_decl_list

   fun internal l =
   let
      val l' = map (Pfundecl_preprocess res_varL global_vars) l;
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
      (funname, assume_opt, ref_args, val_args, localV, global_vars,
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

fun find_duplicates [] = []
  | find_duplicates (x::xs) =
    let
       val (xL,xs') = partition (fn y => (x = y)) xs;
       val dL = find_duplicates xs';
    in
       if null xL then dL else ((hd xL)::dL)
    end;


fun Pprogram2hol procL_opt (Pprogram (ident_decl, global_decl, program_item_decl)) =
   let
      (*ignore ident_decl*)

      (*parse resources*)
      val resource_list = filter p_item___is_resource program_item_decl;
      val resource_names = map (fn Presource (name,_,_) => name) resource_list;
      val resource_names_dL = find_duplicates resource_names;
      val _ = if null resource_names_dL then () else
              (AssembleHolfootParser.print_parse_error (String.concat (
                  "Multiple resource definition found for:\n"::
                   (map (fn n => (" - '"^n^"'\n")) resource_names_dL)));Feedback.fail ());

      val emp_s = (Redblackset.empty String.compare);
      val resource_parseL = map (Presource2hol (emp_s, emp_s)) resource_list;
      val resource_parse_termL = map (fn (name, (prop, vars)) =>
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
      val fun_names = map (fn Pfundecl (_,name,_,_,_,_,_,_) => name) fun_decl_list;
      val fun_names_dL = find_duplicates fun_names;
      val _ = if null fun_names_dL then () else
              (AssembleHolfootParser.print_parse_error (String.concat (
                  "Multiple procedure definition found for:\n"::
                   (map (fn n => (" - '"^n^"'\n")) fun_names_dL)));Feedback.fail ());

      val res_varL = map (fn Presource (n, vL, _) => (n, vL)) resource_list;
      val res_propL = map (fn Presource (_, _, p) => p) resource_list;
      val init_post_prop = if null res_propL then Aprop_spred Aspred_empty else
             (end_itlist (curry Aprop_star) res_propL)
      val fun_decl_list_init = map (add_init_spec init_post_prop) fun_decl_list
      val global_vars = string_list2set global_decl;
      val fun_decl_parseL = Pfundecl_list2hol global_vars res_varL fun_decl_list_init

      fun assume_proc_spec assume_opt proc =
         if (not assume_opt) then F else
         if (not (isSome procL_opt)) then T else
         if (mem proc (valOf procL_opt)) then T else F;

      fun mk_pair_terms (assume_opt, s, fun_body, spec, _) =
         pairLib.list_mk_pair [assume_proc_spec assume_opt s, stringLib.fromMLstring s, fun_body, spec];
      val fun_decl_parse_pairL = map mk_pair_terms fun_decl_parseL;

      val input = listSyntax.mk_list (fun_decl_parse_pairL, type_of (hd fun_decl_parse_pairL));


      (* check for problems with variables protected by locks being used *)
      fun check_vars (_, fname, _, _, gvs) (Presource (rname, rvs, _)) =
         let
            val il = Lib.intersect gvs rvs;
         in
            if null il orelse (fname = "init") then NONE else SOME (fname, rname, il)
         end;
      val error_list = map valOf (filter isSome (flatten (map (fn fd => map (check_vars fd) resource_list) fun_decl_parseL)));
      val _ = if null error_list then () else
              let
                  fun error_report (fname, rname, vl) =
                    String.concat ["The function '", fname, "' accesses the variables [",
                    String.concat (Lib.commafy vl), "] which are protected by resource '", rname, "'!\n"];
              in
                 (AssembleHolfootParser.print_parse_error (String.concat (
                     map error_report error_list));Feedback.fail ())
              end;
   in
      (list_mk_icomb (HOLFOOT_SPECIFICATION_term, [resource_term, input]))
   end;


fun mk_entailment (comment, p1, p2) =
let
   val empty_vs = (Redblackset.empty String.compare, Redblackset.empty String.compare);
   val (_, a1) = holfoot_a_proposition2absyn empty_vs NONE p1
   val (_, a2) = holfoot_a_proposition2absyn empty_vs NONE p2
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
      val tL = List.map mk_entailment eL'
   in
      (boolSyntax.list_mk_conj tL)
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
