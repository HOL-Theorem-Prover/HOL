structure temporal_deep_simplificationsLib :> temporal_deep_simplificationsLib =
struct

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["congLib", "temporal_deep_simplificationsLibTheory",
  "prop_logicTheory", "xprop_logicTheory", "full_ltlTheory", "Travrules",
  "congToolsLib", "Traverse", "tuerk_tacticsLib"];
*)

open HolKernel boolLib bossLib temporal_deep_simplificationsLibTheory
  congLib prop_logicTheory xprop_logicTheory full_ltlTheory Travrules congToolsLib
  Traverse tuerk_tacticsLib

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)

(* Works but much too slow. However, I'm not sure, if it is really usefull

fun prop_logic_equivalent_and_conv t =
  let
    val (func, args) = dest_comb t
    val _ = if same_const func ``P_AND:'a prop_logic # 'a prop_logic -> 'a prop_logic`` then T else raise ERR "NOT_APPLICALBE" "";

    val l = rand (rator (args));
    val r = rand(args);

    val l_is_neg = can (match_term ``(P_NOT x):'a prop_logic``) l
    val replacement = if l_is_neg then ``P_FALSE:'a prop_logic`` else
                      ``P_TRUE:'a prop_logic``;
    val t_type = hd (snd (dest_type (type_of t)));
    val replacement = inst [alpha |-> t_type] replacement;
    val replacement_lhs = if l_is_neg then (rand l) else l;

    val new_r = subst [replacement_lhs |-> replacement] r
    val _ = if (new_r = r) then raise UNCHANGED else T;

    val resultTerm = ``PROP_LOGIC_EQUIVALENT (x:'a prop_logic) (P_AND (y, z))``
    val resultTerm = inst [alpha |-> t_type] resultTerm;
    val resultTerm = subst [mk_var("x", type_of t) |-> t,
                            mk_var("y", type_of t) |-> l,
                            mk_var("z", type_of t) |-> new_r] resultTerm
    val thm = prove (resultTerm,
      REWRITE_TAC[PROP_LOGIC_EQUIVALENT_def, P_SEM_THM] THEN
                  REPEAT GEN_TAC THEN
                  REPEAT BOOL_EQ_STRIP_TAC);
  in
    thm
  end;


fun prop_logic_equivalent_or_conv t =
  let
    val (func, args) = dest_comb t
    val _ = if same_const func ``P_OR:'a prop_logic # 'a prop_logic -> 'a prop_logic`` then T else raise ERR "NOT_APPLICALBE" "";

    val l = rand (rator (args));
    val r = rand(args);

    val l_is_neg = can (match_term ``(P_NOT x):'a prop_logic``) l
    val replacement = if l_is_neg then ``P_TRUE:'a prop_logic`` else
                      ``P_FALSE:'a prop_logic``;
    val t_type = hd (snd (dest_type (type_of t)));
    val replacement = inst [alpha |-> t_type] replacement;
    val replacement_lhs = if l_is_neg then (rand l) else l;
    val new_r = subst [replacement_lhs |-> replacement] r
    val _ = if (new_r = r) then raise UNCHANGED else T;


    val resultTerm = ``PROP_LOGIC_EQUIVALENT (x:'a prop_logic) (P_OR (y, z))``
    val resultTerm = inst [alpha |-> t_type] resultTerm;
    val resultTerm = subst [mk_var("x", type_of t) |-> t,
                            mk_var("y", type_of t) |-> l,
                            mk_var("z", type_of t) |-> new_r] resultTerm
    val thm = prove (resultTerm,
      REWRITE_TAC[PROP_LOGIC_EQUIVALENT_def, P_SEM_THM] THEN
                  REPEAT GEN_TAC THEN
                  REPEAT BOOL_EQ_STRIP_TAC);
  in
    thm
  end;


exception reducer_empty_context;
fun simple_conv_reducer conv' =
  let
      fun addcontext (context,thms) = reducer_empty_context
      fun apply {solver,conv, context,stack,relation} tm = conv' tm;
  in REDUCER {addcontext=addcontext, apply=apply,
              initial=reducer_empty_context}
  end;

*)


val prop_logic_equivalent_preorder =
    mk_preorder (PROP_LOGIC_EQUIVALENT_TRANS, PROP_LOGIC_EQUIVALENT_REFL);

val xprop_logic_equivalent_preorder =
    mk_preorder (XPROP_LOGIC_EQUIVALENT_TRANS, XPROP_LOGIC_EQUIVALENT_REFL);


val ltl_equivalent_preorder =
    mk_preorder (LTL_EQUIVALENT_TRANS, LTL_EQUIVALENT_REFL);


val prop_logic_CS = merge_cs [CSFRAG
   {rewrs  = [PROP_LOGIC_EQUIVALENT_rewrites,
      PROP_LOGIC_EQUIVALENT___EXISTS___rewrites],
    relations = [prop_logic_equivalent_preorder],
    dprocs = [],
    congs  = [PROP_LOGIC_EQUIVALENT_congs, PROP_LOGIC_EQUIVALENT_list_congs]},

    mk_list_as_set_congruence_relation_cs PROP_LOGIC_EQUIVALENT_LIST_AS_SET_def prop_logic_equivalent_preorder];

val prop_logic_nnf_CS = add_csfrag_rewrites prop_logic_CS [PROP_LOGIC_EQUIVALENT_nnf_rewrites];

val prop_logic_dnf_CS = add_csfrag_rewrites prop_logic_nnf_CS [PROP_LOGIC_EQUIVALENT_dnf_rewrites, P_EQUIV_def, P_IMPL_def, P_COND_def];

val prop_logic_cs = mk_congset [prop_logic_CS];
val prop_logic_nnf_cs = mk_congset [prop_logic_nnf_CS];
val prop_logic_dnf_cs = mk_congset [prop_logic_dnf_CS];






val xprop_logic_CS = merge_cs [CSFRAG
   {rewrs  = [XPROP_LOGIC_EQUIVALENT_rewrites,
              XPROP_LOGIC_EQUIVALENT___EXISTS___rewrites],
    relations = [xprop_logic_equivalent_preorder],
    dprocs = [],
    congs  = [XPROP_LOGIC_EQUIVALENT_congs, XPROP_LOGIC_EQUIVALENT_list_congs]},

    mk_list_as_set_congruence_relation_cs XPROP_LOGIC_EQUIVALENT_LIST_AS_SET_def xprop_logic_equivalent_preorder];

val xprop_logic_nnf_CS = add_csfrag_rewrites xprop_logic_CS [XPROP_LOGIC_EQUIVALENT_nnf_rewrites];

val xprop_logic_dnf_CS = add_csfrag_rewrites xprop_logic_nnf_CS [XPROP_LOGIC_EQUIVALENT_dnf_rewrites, XP_EQUIV_def, XP_IMPL_def, XP_COND_def];


val xprop_logic_cs = mk_congset [xprop_logic_CS];
val xprop_logic_nnf_cs = mk_congset [xprop_logic_nnf_CS];
val xprop_logic_dnf_cs = mk_congset [xprop_logic_dnf_CS];










val ltl_CS = CSFRAG
   {rewrs  = [LTL_EQUIVALENT_bool_rewrites, LTL_EQUIVALENT_true_false_rewrites,
      GSYM LTL_TRUE_def, GSYM LTL_FALSE_def, LTL_EQUIVALENT_homogeneous_conj_disj_rewrites],
    relations = [ltl_equivalent_preorder],
    dprocs = [],
    congs  = [LTL_EQUIVALENT_congs]};

val ltl_nnf_CS = add_csfrag_rewrites ltl_CS [LTL_EQUIVALENT_nnf_rewrites, LTL_SWHILE_def,
LTL_WHILE_def, LTL_PSWHILE_def, LTL_PWHILE_def];


val ltl_cs = cs_addfrag prop_logic_cs ltl_CS;
val ltl_nnf_cs = cs_addfrag prop_logic_nnf_cs ltl_nnf_CS;

end
