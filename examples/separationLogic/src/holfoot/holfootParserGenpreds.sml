structure holfootParserGenpreds :> holfootParserGenpreds =
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
open holfootParser

(*
quietdec := false;
*)


val reset_genpreds = holfootParser.reset_genpreds;

fun add_default_genpreds () =
let
   fun mk_list [] = Absyn.mk_ident "NIL"
     | mk_list (e::es) =
       Absyn.mk_app (Absyn.mk_app (Absyn.mk_ident "CONS", e), mk_list es)

   val holfoot_data_list___EMPTY_tm = ``[]:(holfoot_tag # num list) list``;

   fun mk_holfoot_ap_list_seg_absyn (tag, exp1, exp2) =
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_list_seg_term, [
          tag, exp1, Absyn.mk_AQ holfoot_data_list___EMPTY_tm, exp2]);

   (* list(x) *)
   val _ = add_genpred ("list", [Aspred_arg_ty_exp], 
                 fn [exp1] => mk_holfoot_ap_list_seg_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (!list_link_tag)), 
                     exp1, 
                     Absyn.mk_AQ (holfoot_exp_null_term)));
   (* lseg(x,y) *)
   val _ = add_genpred ("lseg", [Aspred_arg_ty_exp,Aspred_arg_ty_comma,Aspred_arg_ty_exp], 
                 fn [exp1,exp2] => mk_holfoot_ap_list_seg_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (!list_link_tag)), 
                     exp1, 
                     exp2));

   (* lseg(tag;x,y) *)
   val _ = add_genpred ("lseg", [Aspred_arg_ty_tag, Aspred_arg_ty_semi, Aspred_arg_ty_exp, Aspred_arg_ty_comma, Aspred_arg_ty_exp], 
                 fn [tag,exp1,exp2] => mk_holfoot_ap_list_seg_absyn (
                     tag, 
                     exp1, 
                     exp2));


   fun mk_holfoot_ap_data_list_seg_absyn (tag, exp1, dtag, data, exp2) =
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_list_seg_term, [
          tag, exp1, mk_list [Absyn.mk_pair (dtag, data)], exp2]);


   (* data_list(x,data) *)
   val _ = add_genpred ("data_list", [Aspred_arg_ty_exp, Aspred_arg_ty_comma, Aspred_arg_ty_hol], 
                 fn [exp1,data] => mk_holfoot_ap_data_list_seg_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (!list_link_tag)), 
                     exp1, 
                     Absyn.mk_AQ (string2holfoot_tag (!data_list_tag)),
                     data, 
                     Absyn.mk_AQ (holfoot_exp_null_term)));


   (* data_lseg(x,data,y) *)
   val _ = add_genpred ("data_lseg", [Aspred_arg_ty_exp,Aspred_arg_ty_comma,Aspred_arg_ty_hol,Aspred_arg_ty_comma,Aspred_arg_ty_exp], 
                 fn [exp1,data,exp2] => mk_holfoot_ap_data_list_seg_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (!list_link_tag)), 
                     exp1, 
                     Absyn.mk_AQ (string2holfoot_tag (!data_list_tag)),
                     data, 
                     exp2));

   (* data_lseg(tag;x,dtag:data,y) *)
   val _ = add_genpred ("data_lseg", [Aspred_arg_ty_tag, Aspred_arg_ty_semi, 
                                      Aspred_arg_ty_exp, Aspred_arg_ty_comma,
                                      Aspred_arg_ty_tag, Aspred_arg_ty_colon,
                                      Aspred_arg_ty_hol, Aspred_arg_ty_comma, 
                                      Aspred_arg_ty_exp], 
                 fn [tag,exp1,dtag,data,exp2] => mk_holfoot_ap_data_list_seg_absyn (
                     tag, 
                     exp1, dtag,data,
                     exp2));


   fun mk_holfoot_ap_tree_absyn (tagL, tagR, exp) =
      Absyn.list_mk_app(Absyn.mk_AQ holfoot_ap_bintree_term, [
                      Absyn.mk_pair (tagL, tagR), exp])

   (* tree(x) *)
   val _ = add_genpred ("tree", [Aspred_arg_ty_exp], 
                 fn [exp] => mk_holfoot_ap_tree_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (#1 (!tree_link_tags))),
                     Absyn.mk_AQ (string2holfoot_tag (#2 (!tree_link_tags))),
                     exp));

   (* tree(tagL,tagR,x) *)
   val _ = add_genpred ("tree", [Aspred_arg_ty_tag, Aspred_arg_ty_comma, Aspred_arg_ty_tag, Aspred_arg_ty_comma, Aspred_arg_ty_exp], 
                 fn [tagL, tagR, exp] => mk_holfoot_ap_tree_absyn (
                     tagL,tagR,exp));


   fun mk_holfoot_ap_data_tree_absyn (tagL, exp, dtagL, data) =
      Absyn.list_mk_app(Absyn.mk_AQ holfoot_ap_data_tree_term, [
                tagL, exp, 
                Absyn.mk_pair (dtagL, data)]);

   (* data_tree(x,data) *)
   val _ = add_genpred ("data_tree", [Aspred_arg_ty_exp, Aspred_arg_ty_comma, Aspred_arg_ty_hol], 
                 fn [exp,data] => mk_holfoot_ap_data_tree_absyn (
                     mk_list [Absyn.mk_AQ (string2holfoot_tag (#1 (!tree_link_tags))),
                      Absyn.mk_AQ (string2holfoot_tag (#2 (!tree_link_tags)))],
                     exp, 
                     mk_list [Absyn.mk_AQ (string2holfoot_tag (!tree_data_tag))],
                     data))

   (* data_tree(x,dtagL:data) *)
   val _ = add_genpred ("data_tree", [Aspred_arg_ty_exp, Aspred_arg_ty_comma, Aspred_arg_ty_list Aspred_arg_ty_tag, Aspred_arg_ty_colon, Aspred_arg_ty_hol], 
                 fn [exp,dtagL,data] => mk_holfoot_ap_data_tree_absyn (
                     mk_list [Absyn.mk_AQ (string2holfoot_tag (#1 (!tree_link_tags))),
                      Absyn.mk_AQ (string2holfoot_tag (#2 (!tree_link_tags)))],
                     exp, 
                     dtagL,
                     data))

   (* data_tree(tagL;x,dtagL:data) *)
   val _ = add_genpred ("data_tree", [
              Aspred_arg_ty_list Aspred_arg_ty_tag, Aspred_arg_ty_semi,
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_list Aspred_arg_ty_tag, Aspred_arg_ty_colon,
              Aspred_arg_ty_hol], 
                 fn [tagL,exp,dtagL,data] => mk_holfoot_ap_data_tree_absyn (
                     tagL,
                     exp, 
                     dtagL,
                     data))


   fun mk_holfoot_ap_array_absyn (exp1, exp2) =
        Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_array_term, [
                 exp1, exp2, Absyn.mk_AQ holfoot_data_list___EMPTY_tm]);

   (* array(b,n) *)
   val _ = add_genpred ("array", [
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_exp], 
                 fn [exp1,exp2] => mk_holfoot_ap_array_absyn (
                     exp1, 
                     exp2))


   fun mk_holfoot_ap_data_array_absyn (exp1, exp2, dtag, data) =
        Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_array_term, [
                 exp1, exp2, mk_list [Absyn.mk_pair (dtag, data)]]);


   (* data_array(b,n,data) *)
   val _ = add_genpred ("data_array", [
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_hol], 
                 fn [exp1,exp2,data] => mk_holfoot_ap_data_array_absyn (
                     exp1, 
                     exp2,
                     Absyn.mk_AQ (string2holfoot_tag (!array_data_tag)),
                     data))

   (* data_array(b,n,dtag:data) *)
   val _ = add_genpred ("data_array", [
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_tag, Aspred_arg_ty_colon,
              Aspred_arg_ty_hol], 
                 fn [exp1,exp2,dtag,data] => mk_holfoot_ap_data_array_absyn (
                     exp1, 
                     exp2,
                     dtag,
                     data))

   fun mk_holfoot_ap_interval_absyn (exp1, exp2) =
        Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_interval_term, [
                 exp1, exp2, Absyn.mk_AQ holfoot_data_list___EMPTY_tm]);

   (* interval(b,e) *)
   val _ = add_genpred ("interval", [
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_exp], 
                 fn [exp1,exp2] => mk_holfoot_ap_interval_absyn (
                     exp1, 
                     exp2))

   fun mk_holfoot_ap_data_interval_absyn (exp1, exp2, dtag, data) =
        Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_interval_term, [
                 exp1, exp2, mk_list [Absyn.mk_pair (dtag, data)]]);


   (* data_interval(b,e,data) *)
   val _ = add_genpred ("data_interval", [
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_hol], 
                 fn [exp1,exp2,data] => mk_holfoot_ap_data_interval_absyn (
                     exp1, 
                     exp2,
                     Absyn.mk_AQ (string2holfoot_tag (!array_data_tag)),
                     data))

   (* data_interval(b,n,dtag:data) *)
   val _ = add_genpred ("data_interval", [
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_exp, Aspred_arg_ty_comma,
              Aspred_arg_ty_tag, Aspred_arg_ty_colon,
              Aspred_arg_ty_hol], 
                 fn [exp1,exp2,dtag,data] => mk_holfoot_ap_data_interval_absyn (
                     exp1, 
                     exp2,
                     dtag,
                     data))



   fun mk_holfoot_ap_queue_absyn (tag, exp1, exp2) =
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_queue_term, [
          tag, exp1, Absyn.mk_AQ holfoot_data_list___EMPTY_tm, exp2]);

   (* queue(f,r) *)
   val _ = add_genpred ("queue", [Aspred_arg_ty_exp, Aspred_arg_ty_comma, Aspred_arg_ty_exp], 
                 fn [exp1,exp2] => mk_holfoot_ap_queue_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (!list_link_tag)), 
                     exp1, exp2));


   fun mk_holfoot_ap_data_queue_absyn (tag, exp1, dtag, data, exp2) =
      Absyn.list_mk_app (Absyn.mk_AQ holfoot_ap_data_queue_term, [
          tag, exp1, mk_list [Absyn.mk_pair (dtag, data)], exp2]);


   (* data_queue(x,data,r) *)
   val _ = add_genpred ("data_queue", [Aspred_arg_ty_exp, Aspred_arg_ty_comma, Aspred_arg_ty_hol, Aspred_arg_ty_comma, Aspred_arg_ty_exp], 
                 fn [exp1,data,exp2] => mk_holfoot_ap_data_queue_absyn (
                     Absyn.mk_AQ (string2holfoot_tag (!list_link_tag)), 
                     exp1, 
                     Absyn.mk_AQ (string2holfoot_tag (!data_list_tag)),
                     data, 
                     exp2));


   (* data_queue(tl;x,dta:data,r) *)
   val _ = add_genpred ("data_queue", [
                 Aspred_arg_ty_tag, Aspred_arg_ty_semi,
                 Aspred_arg_ty_exp, Aspred_arg_ty_comma, 
                 Aspred_arg_ty_tag, Aspred_arg_ty_colon,
                 Aspred_arg_ty_hol, Aspred_arg_ty_comma,
                 Aspred_arg_ty_exp], 
                 fn [tag,exp1,dtag,data,exp2] => mk_holfoot_ap_data_queue_absyn (
                     tag,
                     exp1, 
                     dtag,
                     data, 
                     exp2));
in
   ()
end;

fun init_genpreds () =
let
   val _ = reset_genpreds ();
   val _ = add_default_genpreds ();
in
   ()
end; 


val _ = init_genpreds ();


(*
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/automatic/list.sf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/interactive/mergesort.dsf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/automatic/tree.sf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/automatic/tree_copy.dsf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/automatic/array_copy-shape.dsf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/interactive/array-inc.dsf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/automatic/quicksort-shape.dsf"
val file = "/home/tt291/hol98/examples/separationLogic/src/holfoot/EXAMPLES/interactive/queue.dsf2"


parse_holfoot_file file
*)

end
