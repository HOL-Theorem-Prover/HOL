(*=====================================================================  *)
(* FILE          : quantHeuristicsLib.sml                                *)
(* DESCRIPTION   : some code to find instantations for quantified        *)
(*                 variables                                             *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : December 2008                                         *)
(* ===================================================================== *)


structure quantHeuristicsArgsLib :> quantHeuristicsArgsLib =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
load "ConseqConv"
show_assums := true;
quietdec := true;
*)

open HolKernel Parse boolLib Drule ConseqConv quantHeuristicsLib
     rich_listTheory quantHeuristicsTheory
(*
quietdec := false;
*)


(* quantHeuristicsLib contains the core functionality to eliminate
   quantifiers. However the heuristics contained in this lib are just
   concerned with equations and basic boolean expressions. This
   file contains heuristics for common construcs like lists, pairs,
   option-types, etc.
*)



(*******************************************************************
 * Pairs
 *******************************************************************)


(* val v = ``x:('a # 'b)``;
   val fv = [``y:'a``]:term list;
   val t = ``FST (x:('a # 'b)) = y``
   fun P v (t:term) = SOME (enumerate_pair true v)
   val given = ["aaaa"]
 *)

fun enumerate_pair do_rec v =
if not ((can pairSyntax.dest_prod) (type_of v)) then v else
let
   val (vn,vt) = dest_var v
   val tL = pairSyntax.spine_prod vt;

   val ntL = enumerate 1 tL
   val vars = map (fn (n, ty) => (mk_var (vn^"_"^(Int.toString n), ty))) ntL
   val vars' = if do_rec then (map (enumerate_pair do_rec) vars) else vars
   val p = (pairSyntax.list_mk_pair vars')
in
   p
end;

val GUESS_PAIR_THM = prove (
``!P. GUESS_EXISTS_STRONG (\x:'a. x) P /\ GUESS_FORALL_STRONG (\x. x) P``,
simpLib.SIMP_TAC numLib.std_ss [GUESS_REWRITES])


fun QUANT_INSTANTIATE_HEURISTIC___SPLIT_PAIR_GEN PL (sys:quant_heuristic) v t =
let
   (*check whether something should be done*)
   val _ = pairSyntax.dest_prod (type_of v) handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   fun P v t = first_opt (fn x => fn p => (p v t)) PL
   val vars = case (P v t) of NONE => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp
                            | some => valOf some;
   val fvL = rev (free_vars vars)
 
   val gthmL = CONJUNCTS (ISPEC (mk_abs (v, t)) GUESS_PAIR_THM)   
in
  {rewrites            = [],
   general             = [],
   true                = [],
   false               = [],
   forall              = [],
   exists              = [],
   forall_strong       = [guess_thm (gty_forall_strong, vars, fvL, el 2 gthmL)],
   exists_strong       = [guess_thm (gty_exists_strong, vars, fvL, el 1 gthmL)]}
end;


fun split_pair___FST_SND___pred depth_split v t =
let
   val t1 = pairSyntax.mk_fst v;
   val t2 = pairSyntax.mk_snd v;

   val do_split = not (null (find_terms (fn t' => (t' = t1) orelse (t' = t2)) t))
in
   if do_split then (SOME (enumerate_pair depth_split v)) else NONE
end;


(* val v = ``x:('a # 'b # 'c)``;
   val t = ``(\ (a,b,c). P a b c) ^v``
 *)
local
   fun is_var_pabs v t =
   let
      val (b,v') = dest_comb t;
   in
      (v = v') andalso (pairSyntax.is_pabs b)
   end handle HOL_ERR _ => false;
in

fun split_pair___PABS___pred v t =
let
   val p = hd (find_terms (is_var_pabs v) t);
   val vars = fst (pairSyntax.dest_pabs (fst (dest_comb p)))
in
   (SOME vars)
end handle Empty => NONE
         | HOL_ERR _ => NONE;
end;


fun split_pair___ALL___pred v = K (SOME (enumerate_pair true v));



(* val v = ``x:('a # 'b # 'c)``
   val fv = []:term list;
   val t = ``(\ (a1, a2, a3). P a1 a2 a3) (x:('a # 'b # 'c))``
 *)

fun pair_qp pL =
  {distinct_thms = [],
   cases_thms =    [],
   rewrite_thms =  [PAIR_EQ_EXPAND, pairTheory.FST, pairTheory.SND],
   convs =         [],
   heuristics =    [QUANT_INSTANTIATE_HEURISTIC___SPLIT_PAIR_GEN pL],
   inference_thms= [],
   filter       =  [],
   top_heuristics =[],
   final_rewrite_thms = [pairTheory.FST,  pairTheory.SND,
                         PAIR_EQ_SIMPLE_EXPAND]
  }:quant_param


val pair_default_qp = pair_qp [split_pair___PABS___pred,
        split_pair___FST_SND___pred false]


(*
val PAIR_QUANT_INSTANTIATE_CONV = QUANT_INSTANTIATE_CONV [pair_default_qp]

val t = ``?p. (x = FST p) /\ Q p``;
val thm = PAIR_QUANT_INSTANTIATE_CONV t;

val t = ``?p. (7 = (SND p)) /\ Q p``
val thm = PAIR_QUANT_INSTANTIATE_CONV t;

val t = ``?p1 p2. (p1 = 7) /\ Q (p1,p2)``
val thm = PAIR_QUANT_INSTANTIATE_CONV t


val t = ``?v. (v,X) = Z``
val thm = PAIR_QUANT_INSTANTIATE_CONV t;

val t = ``!x. a /\ (\ (a1, t3, a2). P a1 a2 t3) x /\ b x``
val thm = PAIR_QUANT_INSTANTIATE_CONV t

val t = ``?x. (x = 2) /\ P x``;
val thm = PAIR_QUANT_INSTANTIATE_CONV t

val t = ``!x. ((f t = x) /\ P x) ==> Q x``;
val thm = PAIR_QUANT_INSTANTIATE_CONV t

val t = ``?v. (v,X) = (a,9)``;
val thm = PAIR_QUANT_INSTANTIATE_CONV t

*)


val stateful_qp = quantHeuristicsLib.stateful_qp;
val pure_stateful_qp = quantHeuristicsLib.pure_stateful_qp;
val TypeBase_qp = quantHeuristicsLib.TypeBase_qp;


(*******************************************************************
 * Option types
 *******************************************************************)

val option_qp =
  {distinct_thms      = [optionTheory.NOT_NONE_SOME],
   cases_thms         = [optionTheory.option_nchotomy],
   rewrite_thms       = [optionTheory.SOME_11, optionTheory.IS_NONE_EQ_NONE,
                         optionTheory.IS_NONE_EQ_NONE,
                         IS_SOME_EQ_NOT_NONE],
   convs              = [],
   heuristics         = [],
   inference_thms     = [],
   filter             = [],
   top_heuristics     = [],
   final_rewrite_thms = [optionTheory.option_CLAUSES]
  }:quant_param



(*******************************************************************
 * Nums
 *******************************************************************)

val num_qp =
  {distinct_thms = [prim_recTheory.SUC_ID],
   cases_thms =    [arithmeticTheory.num_CASES],
   rewrite_thms =  [prim_recTheory.INV_SUC_EQ,
      arithmeticTheory.EQ_ADD_RCANCEL,arithmeticTheory.EQ_ADD_LCANCEL,
      arithmeticTheory.ADD_CLAUSES],
   convs =         [],
   heuristics =    [],
   filter       =  [],
   top_heuristics =[],
   inference_thms     = [],
   final_rewrite_thms = [numTheory.NOT_SUC, GSYM numTheory.NOT_SUC]
  }:quant_param



(*******************************************************************
 * Lists
 *******************************************************************)

val list_qp =
  {distinct_thms = [rich_listTheory.NOT_CONS_NIL],
   cases_thms =    [listTheory.list_CASES],
   rewrite_thms =  [listTheory.CONS_11,
                    listTheory.NULL_EQ,
                    listTheory.APPEND_11,
                    listTheory.APPEND_eq_NIL],
   convs =         [],
   inference_thms= [],
   filter       =  [],
   top_heuristics =[],
   heuristics =    [],
   final_rewrite_thms = [listTheory.NULL_DEF,
                         listTheory.TL, listTheory.HD,
                         rich_listTheory.NOT_CONS_NIL,
                         GSYM rich_listTheory.NOT_CONS_NIL]
  }:quant_param


(*******************************************************************
 * Records
 *******************************************************************)


fun get_record_type_rewrites ty =
let
   fun type_rewrites ty = 
       let
          val ty_info = valOf (TypeBase.fetch ty)
          val (thyname,typename) = TypeBasePure.ty_name_of ty_info
       in           
          if null (TypeBasePure.fields_of ty_info) then [] else
          (map (fn s => (DB.fetch thyname (typename^"_"^(fst s))))
             (TypeBasePure.fields_of ty_info)) @
          (map (fn s => (DB.fetch thyname (typename^s))) [
           "_fupdfupds_comp", "_accessors", "_fn_updates",
            "_literal_11", "_component_equality",
            "_accfupds"])@
          ((valOf (TypeBasePure.one_one_of ty_info))::
          ((TypeBasePure.case_def_of ty_info)::
          ((TypeBasePure.accessors_of ty_info)@(TypeBasePure.updates_of ty_info))))          
       end;

  val constructor = hd (TypeBase.constructors_of ty)
  val (typ, types) = let
    fun domtys acc ty = let
      val (d1, rty) = dom_rng ty
    in
      domtys (d1::acc) rty
    end handle HOL_ERR _ => (ty, List.rev acc)
  in
    domtys [] (type_of constructor)
  end
in
  [combinTheory.K_THM, combinTheory.o_THM]@
  (flatten (map type_rewrites (typ::types)))
end;


fun QUANT_INSTANTIATE_HEURISTIC___RECORDS do_rewrites P (sys:quant_heuristic) v t =
let
   (*check whether something should be done*)
   val v_info = case TypeBase.fetch (type_of v) of NONE   => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp
                                                 | SOME x => x
   val _ = if null (TypeBasePure.fields_of v_info) orelse not (P v t) then 
              raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp else ()
   val (thyname,typename) = TypeBasePure.ty_name_of v_info

   val vars = let
      val (v_name,_) = dest_var v 
      fun mk_new_var (s, ty) = mk_var (v_name ^ "_" ^ s, ty);
      in
         map mk_new_var (TypeBasePure.fields_of v_info)
      end;

   val thm0 = 
        let
           val xthm0 = DB.fetch thyname (typename^"_literal_nchotomy")

           val xthm1 = ISPEC v xthm0;
           val xthm2 =  CONV_RULE (RENAME_VARS_CONV (map (fst o dest_var) vars)) xthm1
        in xthm2
        end;
   val gc = QUANT_INSTANTIATE_HEURISTIC___one_case thm0 sys v t
in
   if do_rewrites then
        (guess_collection_append gc
              (guess_list2collection (get_record_type_rewrites (type_of v), [])))
   else gc
end

fun record_qp do_rewrites P =
  {distinct_thms = [],
   cases_thms =    [],
   rewrite_thms =  [],
   convs =         [],
   filter =        [],
   top_heuristics =[],
   inference_thms= [],
   heuristics =    [QUANT_INSTANTIATE_HEURISTIC___RECORDS do_rewrites P],
   final_rewrite_thms = []
  }:quant_param

val record_default_qp = record_qp false (K (K true))



(*******************************************************************
 * Combinations
 *******************************************************************)

val std_qp = combine_qps [
   num_qp, option_qp, pair_default_qp, list_qp, record_default_qp]

end
