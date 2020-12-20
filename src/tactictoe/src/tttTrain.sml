(* ========================================================================= *)
(* FILE          : tttTrain.sml                                              *)
(* DESCRIPTION   : Training tree neural networks for the policy and value    *)
(*                 guiding TacticToe search algorithm                        *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttTrain :> tttTrain =
struct

open HolKernel boolLib Abbrev aiLib mlNeuralNetwork smlLexer smlParser
  mlTacticData mlTreeNeuralNetwork mlThmData tttToken

val ERR = mk_HOL_ERR "tttTrain"

(* -------------------------------------------------------------------------
   Mask unknown operators
   ------------------------------------------------------------------------- *)

val mask_var = mk_var ("tactictoe_mask",alpha)

fun mask_unknown tnn tm =
  let val (oper,argl) = strip_comb tm in
    if dmem oper tnn
    then list_mk_comb (oper, map (mask_unknown tnn) argl)
    else mask_var
  end

val mask_unknown_val = mask_unknown
val mask_unknown_pol = mask_unknown
val mask_unknown_arg = mask_unknown

val vhead = mk_var ("head_val", rpt_fun_type 2 alpha)
val phead = mk_var ("head_pol", rpt_fun_type 2 alpha)
val ahead = mk_var ("head_arg", rpt_fun_type 2 alpha)

fun add_mask dim tnn =
  dadd mask_var (random_nn (idactiv,didactiv) [0,dim]) tnn
  
fun add_mask_val tnn = add_mask (dimin_nn (dfind vhead tnn)) tnn
fun add_mask_pol tnn = add_mask (dimin_nn (dfind phead tnn)) tnn
fun add_mask_arg tnn = add_mask (dimin_nn (dfind ahead tnn)) tnn

(* -------------------------------------------------------------------------
   Convert a goal to a neural network term
   ------------------------------------------------------------------------- *)

val asm_cat = mk_var ("asm_cat", rpt_fun_type 3 alpha)
val hyp_cat = mk_var ("hyp_cat", rpt_fun_type 3 alpha)
val goal_cat = mk_var ("goal_cat", rpt_fun_type 3 alpha)

fun flatten_goal (asm,w) =
  if null asm
  then w
  else (list_mk_comb (hyp_cat,[list_mk_binop asm_cat asm,w])
       handle HOL_ERR _ => raise ERR "flatten_goal" (string_of_goal (asm,w)))

fun lambda_term fullty (v,bod) =
  let
    val ty1 = type_of v
    val ty2 = type_of bod
    val ty3 = mk_type ("fun",[ty1, mk_type ("fun", [ty2,fullty])])
  in
    list_mk_comb (mk_var ("lambda",ty3), [v,bod])
  end
  handle HOL_ERR _ => raise ERR "lambda_term" (term_to_string bod)

fun add_lambda tm = case dest_term tm of
    COMB(Rator,Rand) => mk_comb (add_lambda Rator, add_lambda Rand)
  | LAMB(Var,Bod) => lambda_term (type_of tm) (Var, add_lambda Bod)
  | _ => tm

fun add_arity tm =
  let
    val (oper,argl) = strip_comb tm
    val a = length argl
    val newname =
      if is_var oper then
        let val prefix = if null argl then "V" else "v" in
          escape (prefix ^ fst (dest_var oper) ^ "." ^ its a)
        end
      else
        let val {Thy,Name,Ty} = dest_thy_const oper in
          escape ("c" ^ Thy ^ "." ^ Name ^ "." ^ its a)
        end
    val newoper = mk_var (newname, rpt_fun_type (a+1) alpha)
  in
    list_mk_comb (newoper, map add_arity argl)
  end
  handle HOL_ERR _ => raise ERR "add_arity" (term_to_string tm)


fun nntm_of_goal (asm,w) = flatten_goal
  (map (add_arity o add_lambda) asm, (add_arity o add_lambda) w)

fun nntm_of_stateval g = mk_comb (vhead, nntm_of_goal g)

(* -------------------------------------------------------------------------
   Convert a tactic to a neural network term
   ------------------------------------------------------------------------- *)

val apply_cat = mk_var ("apply_cat", rpt_fun_type 3 alpha);
val gstac_cat = mk_var ("gstac_cat", rpt_fun_type 3 alpha);

fun nntm_of_applyexp e = case e of
    ApplyExp (e1,e2) =>
      mk_binop apply_cat (nntm_of_applyexp e1, nntm_of_applyexp e2)
  | ApplyUnit (s,_) =>
    (
    if mem #" " (explode s)
    then mk_var (escape ("sml." ^ its (hash_string s)), alpha)
    else mk_var (escape ("sml." ^ s), alpha)
    )

val stacnntmd = ref (dempty String.compare)

fun nntm_of_stac stac =
  dfind stac (!stacnntmd) handle NotFound =>
  let
    fun f x = if mem x [termarg_placeholder,thmlarg_placeholder]
              then "tttToken." ^ x
              else x
    val newstac = String.concatWith " " (map f (partial_sml_lexer stac))
    val r = nntm_of_applyexp (extract_applyexp (extract_smlexp newstac))
  in
    stacnntmd := dadd stac r (!stacnntmd); r
  end

fun nntm_of_gstac (g,stac) =
  mk_binop gstac_cat (nntm_of_goal g, nntm_of_stac stac)

fun nntm_of_statepol (g,stac) =
  mk_comb (phead, nntm_of_gstac (g,stac))

(* -------------------------------------------------------------------------
   Convert an argument to a neural network term
   ------------------------------------------------------------------------- *)

val gstacarg_cat = mk_var ("gstacarg_cat", rpt_fun_type 3 alpha);

val thm_cache = ref (dempty String.compare)

fun thm_of_name_cached x = 
  dfind x (!thm_cache) handle NotFound => 
  let val r = thm_of_name x in thm_cache := dadd x r (!thm_cache); r end

(* todo: lookup a dictionary of preparsed theorems necessary to speed up
   looking up the namespace *)
fun nntm_of_arg arg = case arg of
    Sthml [s] => ((nntm_of_goal o dest_thm o snd o valOf o 
      thm_of_name_cached) s
      handle Option => raise ERR "nntm_of_arg" "option")
  | _ => raise ERR "nntm_of_arg" "not supported"

fun nntm_of_statearg ((g,stac),arg) =
  mk_comb (ahead,
    mk_binop gstacarg_cat (nntm_of_gstac (g,stac), nntm_of_arg arg))

(* ignores stac for now *)
fun nntm_of_statearg ((g,stac),arg) =
  mk_comb (ahead, mk_binop gstacarg_cat (nntm_of_goal g, nntm_of_arg arg))

(* ------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------ *)

fun train_fixed pct exl =
  let
    val (train,test) = part_pct pct (shuffle exl)
    fun operl_of_tnnex exl =
      List.concat (map operl_of_term (map fst (List.concat exl)))
    val operl = operl_of_tnnex exl
    val operset = mk_fast_set (cpl_compare Term.compare Int.compare) operl
    val operdiml = map (fn x => (fst x, dim_std_arity (1,8) x)) operset
    val randtnn = random_tnn operdiml
    val schedule =
      [{ncore = 4, verbose = true,
       learning_rate = 0.02, batch_size = 8, nepoch = 50}];
    val tnn = train_tnn schedule randtnn (train,test)
  in
    tnn
  end

end (* struct *)
