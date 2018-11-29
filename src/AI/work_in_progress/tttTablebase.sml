(* ========================================================================= *)
(* FILE          : tttTablebase.sml                                          *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttTablebase :> tttTablebase =
struct

open HolKernel boolLib Abbrev tttTools tttSynt tttRobberType

val ERR = mk_HOL_ERR "tttTablebase"
val dbg = dbg_file "debug_tttTablebase"

fun negate x = if is_neg x then dest_neg x else mk_neg x

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)

datatype axiom = Refl | Inst of term

datatype proofstep =
  Sym of term |
  NegSym of term |
  Ap of term |
  Inj of term |
  Sub of ((int list * term) * term)

fun dest_stepsub step = case step of Sub y => y | _ => raise ERR "" "";

val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``0 <> SUC x``;
val ax4' = ``0 + x = x``;
val ax5' = ``SUC y + x  = SUC (x + y)``;
val axl_glob = [ax4,ax5,ax4',ax5',ax6];

fun is_refl tm =
  let val (a,b) = dest_eq tm in a = b end handle HOL_ERR _ => false

fun is_inst a b = can (match_term a) b

fun match_axiom tm =
  let val instl = filter (fn x => is_inst x tm) axl_glob in
    if is_refl tm then [Refl] else [] @ map Inst instl
  end

(* -------------------------------------------------------------------------
   Depth 0
   ------------------------------------------------------------------------- *)

fun all_posred_aux curpos tm =
  let
    val (oper,argl) = strip_comb tm
    fun f i x = all_posred_aux (i :: curpos) x
    val posl = List.concat (mapi f argl)
  in
    (curpos,tm) :: posl
  end

fun all_posred tm = map_fst rev (all_posred_aux [] tm);

fun all_tactic_output cut_dict tm =
  let
    val posredl = all_posred tm
    fun f (pos,red) = (pos, dfind red cut_dict)
    val posresll = mapfilter f posredl
    val posresl = distrib posresll
  in
    (if can sym_tac tm then [Sym (sym_tac tm)] else []) @
    (if can negsym_tac tm then [NegSym (negsym_tac tm)] else []) @
    (if can ap_tac tm then [Ap (ap_tac tm)] else []) @
    (if can inj_tac tm then [Inj (inj_tac tm)] else []) @
    map Sub (map_assoc (sub_at_pos tm) posresl)
  end

fun init_tablebase tmsize =
  let
    val cj   = ``(SUC 0) + 0``
    val cset = mk_fast_set Term.compare (find_terms is_const cj)
    fun nofilterf l = l
    val terml1 = synthetize nofilterf (10000000,tmsize) (``:num``,cset)
    val terml2 = cartesian_product terml1 terml1;
    val terml3 = map mk_eq terml2
    val cut_dict = dregroup Term.compare (map dest_eq terml3)
    val terml4 = map mk_neg terml3
    val terml5 = terml3 @ terml4
    val proofl = map_assoc match_axiom terml5
    val p0 = filter (not o null o snd) proofl
    val pdict0 = dset Term.compare (map fst p0)
    fun test x = not (dmem x pdict0) andalso not (dmem (negate x) pdict0)
    val terml6 = filter test terml5
    val ante0 = map_assoc (all_tactic_output cut_dict) terml6;
  in
    (pdict0, ante0)
  end

val tmsize = 6;
val (pdict0, ante0) = init_tablebase tmsize;

(* -------------------------------------------------------------------------
   Extract the path to the residue from a residue
   ------------------------------------------------------------------------- *)

fun match_subtm subtm (tm1,tm2) =
  if tm1 = subtm then tm2 else
  let
    val (oper1,argl1) = strip_comb tm1
    val (oper2,argl2) = strip_comb tm2
    val _ = if oper1 <> oper2 then raise ERR "match_subtm" "" else ()
    val argl = combine (argl1,argl2)
    fun f (a,_) = is_subtm subtm a
    val (newtm1,newtm2) = valOf (List.find f argl)
  in
    match_subtm subtm (newtm1,newtm2)
  end

fun term_path_aux acc (partres,fullres) =
  if not (is_subtm active_var partres) then rev acc else
  let
    val subtm = match_subtm active_var (partres,fullres)
    val imit =
      if subtm = zero then ImitZero
      else if can dest_suc subtm then ImitSuc
      else if can dest_add subtm then ImitAdd
      else raise ERR "term_path" ""
    val newpartres = apply_imit imit partres
  in
    term_path_aux ((partres,imit) :: acc) (newpartres,fullres)
  end

fun term_path tm = term_path_aux [] active_var tm

(* -------------------------------------------------------------------------
   Check if the tactic output is proven
   ------------------------------------------------------------------------- *)

fun find_proof (pdict,antel) =
  let
    fun g (tm,x) = case x of
       StepSub y =>
         dmem (snd y) pdict andalso dmem (recover_cut tm (fst y)) pdict
     | StepSym ante    => dmem ante pdict
     | StepNegSym ante => dmem ante pdict
     | StepAp ante     => dmem ante pdict
     | StepInj ante    => dmem ante pdict

    fun f (tm,l) = (tm, filter (fn x => g (tm,x)) l)
  in
    map f antel
  end

fun onestep (pdict,antel) =
  let
    val pl = filter (fn x => not (null (snd x))) (find_proof (pdict,antel))
    val newpdict = daddset (map fst pl) pdict
    fun test (x,_) =
      not (dmem x newpdict) andalso not (dmem (negate x) newpdict)
    val newantel = filter test antel
  in
    (pl,(newpdict,newantel))
  end

fun nstep n acc (pdict,antel) =
  if n <= 0 orelse null antel then rev acc else
  let val (pl,(newpdict,newantel)) = onestep (pdict,antel) in
    nstep (n - 1) (pl :: acc) (newpdict,newantel)
  end

val nstepl = nstep 10 [] (pdict0,ante0)

(* -------------------------------------------------------------------------
   Extract policy examples
   ------------------------------------------------------------------------- *)

fun value_of_step step = case step of
    StepSym _    => 1.0
  | StepNegSym _ => 2.0
  | StepAp _     => 3.0
  | StepInj _    => 4.0
  | StepSub (_,ante) => 5.0 + Real.fromInt (term_size ante)

fun step_choice stepl =
  let val (step,_) =
    hd (dict_sort compare_rmin (map_assoc value_of_step stepl))
  in
    step
  end

fun poli_of_step step = case step of
    StepSym _    => [1.0,0.0,0.0,0.0,0.0]
  | StepNegSym _ => [0.0,1.0,0.0,0.0,0.0]
  | StepAp _     => [0.0,0.0,1.0,0.0,0.0]
  | StepInj _    => [0.0,0.0,0.0,1.0,0.0]
  | StepSub _    => [0.0,0.0,0.0,0.0,1.0]

(* -------------------------------------------------------------------------
   Choosing the position
   ------------------------------------------------------------------------- *)

fun tag_term tm =
  let val ty = type_of tm in
    mk_comb (mk_var ("tag_var", mk_type ("fun",[ty,ty])), tm)
  end

fun tag_position (tm,pos) =
  if null pos then tag_term tm else
  let
    val (oper,argl) = strip_comb tm
    fun f i arg =
      if i = hd pos
      then tag_position (arg,tl pos)
      else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

fun all_prefix acc l = case l of
    [] => [rev acc]
  | a :: m => rev acc :: all_prefix (a :: acc) m

datatype descent = Stop | Continue

datatype descent_arg = Left | Right

fun two_arg tm = length (snd (strip_comb tm)) = 2;

fun mk_choice pos =
  if null pos then NONE else SOME (butlast pos, last pos)

fun sc_descent x = case x of Stop => 0.0 | Continue => 1.0
fun sc_descarg x = case x of Left => 0.0 | Right => 1.0

fun choice_of_pos (tm,((pos,res),ante)) =
  let
    val posl = all_prefix [] pos
    val choicel0 = List.mapPartial mk_choice posl
    val descentl =
      map_assoc (fn _ => Continue) (butlast posl) @ [(last posl, Stop)]
    val nn1 = map_fst (fn x => tag_position (tm,x)) descentl
    fun g (locpos,i) =
      if two_arg (subtm_at_pos locpos tm)
      then if i = 0 then SOME (locpos,Left) else SOME (locpos,Right)
      else NONE
    val choicel1 = List.mapPartial g choicel0
    val nn2 = map_fst (fn x => tag_position (tm,x)) choicel1
  in
    (map_snd sc_descent nn1, map_snd sc_descarg nn2)
  end

(* -------------------------------------------------------------------------
   Choosing the residue
   ------------------------------------------------------------------------- *)

fun policy_of_res imit = case imit of
    ImitZero => [1.0,0.0,0.0]
  | ImitSuc  => [0.0,1.0,0.0]
  | ImitAdd  => [0.0,0.0,1.0]

fun choice_of_res (tm,((pos,res),ante)) =
  let
    val tagtm = tag_position (tm,pos)
    val red = subtm_at_pos pos tm
    fun f x = mk_conj (tagtm, mk_eq (red,x))
    val l0 = term_path res
    val l1 = map_snd policy_of_res l0
    val l2 = map_fst f l1
  in
    l2
  end

(* -------------------------------------------------------------------------
   All in one : policy
   ------------------------------------------------------------------------- *)

fun all_in_one nstepl =
  let
    val prepoll0 = List.concat nstepl
    val prepoll1 = map_snd step_choice prepoll0
    (* choosing the tactic *)
    val tacchoice_exl = map_snd poli_of_step prepoll1
    val prepoll3 =
      mapfilter (fn (tm,step) => (tm, dest_stepsub step)) prepoll1
    (* choosing the position *)
    val (stop_exl, lr_exl) = split (map choice_of_pos prepoll3)
   (* choosing the residue *)
    val reschoice_exl = List.concat (map choice_of_res prepoll3)
  in
    (tacchoice_exl, List.concat stop_exl, List.concat lr_exl, reschoice_exl)
  end

val (tacchoice_exl, stop_exl, lr_exl, reschoice_exl) = all_in_one nstepl;

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

load "tttNNtree"; open tttNNtree;

fun trainset_info trainset =
  let
    val mean = average_real (map snd trainset)
    val dev = standard_deviation (map snd trainset)
  in
    "  length: " ^ int_to_string (length trainset) ^ "\n" ^
    "  mean: " ^ Real.toString mean ^ "\n" ^
    "  standard deviation: " ^ Real.toString dev
  end

fun wrap_train_treenn (dim,cal) trainset =
  let
    val info     = trainset_info trainset
    val _        = print_endline info
    val bsize    = 16
    val schedule = [(50,0.1),(50,0.01)]
    val prepset  = prepare_trainsetone trainset
    val treenn   = random_treenn dim cal
    val ((treenn,loss), nn_tim) =
      add_time (train_treenn_schedule dim treenn bsize prepset) schedule
  in
    print_endline ("  NN Time: " ^ Real.toString nn_tim);
    print_endline ("  Last loss: " ^ Real.toString loss);
    treenn
  end

fun fo_terms tm =
  let val (oper,argl) = strip_comb tm in
    tm :: List.concat (map fo_terms argl)
  end

fun operl_of_term tm =
  let
    val tml = mk_fast_set Term.compare (fo_terms tm)
    fun f x = let val (oper,argl) = strip_comb x in (oper, length argl) end
  in
    mk_fast_set (cpl_compare Term.compare Int.compare) (map f tml)
  end

(* -------------------------------------------------------------------------
   Simplest eval.
   to do: figure out how to eval other nodes.
   Maybe initially give a reward of 0.0 for the other nodes.
   ------------------------------------------------------------------------- *)

val tmdist0 = map fst pl0;
val tmdistl = tmdist0 :: map (map fst) nstepl;
val decay = 0.95;

fun mk_eval i l =
  let val coeff = Math.pow (decay, Real.fromInt i) in
    map (fn x => (x,1.0)) l
  end

val eval_exl1 = List.concat (mapi mk_eval tmdistl);
val eval_exl2 = map (fn (a,b) => (negate a, 0.0)) eval_exl1;
val eval_exl = eval_exl1 @ eval_exl2;

(* Do one-step look ahead for negative there *)
val poseval_pexl = map_snd (fn x => 1.0) stop_exl;
val reseval_pexl = map_snd (fn x => 1.0) reschoice_exl;

(* parameters of treenns *)
val cj   = ``SUC 0 + 0 <> 0`` ;
val cal  = operl_of_term cj;
val cset = mk_fast_set Term.compare (find_terms is_const cj);
val dim  = 10;

(* training *)
val trainset = eval_exl;
val treenn = wrap_train_treenn (dim,cal) trainset;

val sc = eval_treenn treenn ``SUC 0 + SUC 0 = SUC (SUC (SUC 0))``;

val sc = eval_treenn treenn ``0 = 0 + 0``;


end (* struct *)

(* test
load "tttNNtree"; open tttNNtree;

todo:

  1) human readable  1 = SUC 0

load "holyHammer"; open holyHammer;
val eq1 = ``SUC 0 = 1``;
val eq2 = ``SUC 1 = 2``;
val eq3 = ``SUC 2 = 3``;
val eq4 = ``SUC 3 = 4``;
val eq5 = ``SUC 4 = 5``;
val eql = [eq1,eq2,eq3,eq4,eq5];
fun eq_to_sub eq = [{redex = lhs eq, residue = rhs eq}];
val subl = map eq_to_sub eql;

val tm = ``SUC (SUC 0) + SUC 0 = SUC (SUC (SUC 0))``;

fun human_readable subl tm =
  let fun f (sub,x) = subst sub x in
    foldl f tm subl
  end

val readable = human_readable subl tm;

*)



