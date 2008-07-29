structure bagSimps :> bagSimps =
struct

open HolKernel Parse boolLib simpLib boolSimps bagSyntax bagTheory;

type cache = Cache.cache;

infixr -->
infix |-> THENC

val ERR = mk_HOL_ERR "bagSimps";

val BAG_AC_ss = simpLib.SSFRAG {name=SOME"BAG_AC",
    convs = [], rewrs = [], dprocs = [], congs = [],
    ac = [(SPEC_ALL ASSOC_BAG_UNION, SPEC_ALL COMM_BAG_UNION)],
    filter = NONE
};

(* remove x xs removes one instance of x from xs *)
fun remove x [] = raise ERR "remove" "no such element"
  | remove x (y::xs) = if x = y then xs else y::(remove x xs)

fun remove_list [] l2 = l2
  | remove_list (x::xs) l2 = remove_list xs (remove x l2)

fun buac_prover ty = let
  fun type_inst ty = INST_TYPE [alpha |-> ty]
in
  AC_CONV (type_inst ty ASSOC_BAG_UNION, type_inst ty COMM_BAG_UNION)
end

val SUB_BAG_UNION_eliminate' =
  hd (CONJUNCTS
      (CONV_RULE (SIMP_CONV bool_ss [FORALL_AND_THM])
       SUB_BAG_UNION_eliminate))
val BAG_DIFF_UNION_eliminate' =
  hd (CONJUNCTS
      (CONV_RULE (SIMP_CONV bool_ss [FORALL_AND_THM])
       BAG_DIFF_UNION_eliminate))
val BU_EMPTY_R = hd (CONJUNCTS BAG_UNION_EMPTY)

fun CANCEL_CONV tm = let
  val (mk_rel, thm, (arg1, arg2)) =
    (mk_sub_bag, SUB_BAG_UNION_eliminate', dest_sub_bag tm)
    handle HOL_ERR _ =>
      (mk_diff, BAG_DIFF_UNION_eliminate', dest_diff tm)
      handle HOL_ERR _ => (mk_eq, BAG_UNION_LEFT_CANCEL, dest_eq tm)
  val basetype = base_type arg1
  val bag_type = basetype --> numSyntax.num
  val arg1_ts = strip_union arg1 and arg2_ts = strip_union arg2
  fun common [] _ = []  (* like intersect but no setifying *)
    | common _ [] = []
    | common (x::xs) y = x::common xs (remove x y)
    handle _ => common xs y
  val common_part = common arg1_ts arg2_ts
  val _ = not (null common_part) orelse
    raise ERR "CANCEL_CONV" "No common parts to eliminate"
  val rem1 = remove_list common_part arg1_ts
  val rem2 = remove_list common_part arg2_ts
  val cpt = list_mk_union common_part
  val ac1 = mk_eq(arg1, if null rem1 then cpt
                        else mk_union (cpt, list_mk_union rem1))
  val ac2 = mk_eq(arg2, if null rem2 then cpt
                        else mk_union (cpt, list_mk_union rem2))
  val ac1thm = EQT_ELIM (buac_prover basetype ac1)
  val ac2thm = EQT_ELIM (buac_prover basetype ac2)
  fun add_emptybag thm = let
    val r = rhs (concl thm)
  in
    TRANS thm
    (SYM (REWR_CONV BU_EMPTY_R (mk_union(cpt, mk_bag([], basetype)))))
  end
  val thm1 = if null rem1 then add_emptybag ac1thm else ac1thm
  val thm2 = if null rem2 then add_emptybag ac2thm else ac2thm
  val v1 = genvar bag_type and v2 = genvar bag_type
  val template = mk_rel (v1, v2)
in
  SUBST_CONV [v1 |-> thm1, v2 |-> thm2] template THENC
  REWR_CONV thm
end tm

val x = mk_var("x", bag_ty)
val y = mk_var("y", bag_ty)
fun mk_cancelconv (t, s) =
  {conv = K (K (CHANGED_CONV CANCEL_CONV)),
   key = SOME ([], list_mk_comb(t, [x, y])),
   name = "CANCEL_CONV ("^s^")", trace = 2}

val BAG_EQ_tm = mk_const("=", bag_ty --> bag_ty --> bool);

val BAG_ss = SSFRAG
  {name=SOME"BAG",
   ac = [], congs = [],
   convs = map mk_cancelconv [(BAG_DIFF_tm, "DIFF"),
                              (SUB_BAG_tm, "SUB_BAG"),
                              (BAG_EQ_tm, "=")],
   filter = NONE, dprocs = [],
   rewrs = [BAG_UNION_EMPTY, BAG_DIFF_EMPTY, SUB_BAG_REFL,
            SUB_BAG_EMPTY,FINITE_EMPTY_BAG,
            NOT_IN_EMPTY_BAG]};

fun transform t =
  ((if is_sub_bag t then
      REWR_CONV SUB_BAG_LEQ
    else if is_eq t then
      FUN_EQ_CONV
    else NO_CONV) THENC
   PURE_REWRITE_CONV [BAG_UNION] THENC DEPTH_CONV BETA_CONV) t

fun SBAG_SOLVE thms tm = let
  val newgoal_thm = transform tm
  val newgoal_tm = rhs (concl newgoal_thm)
  val (gvar, gbody) = dest_forall newgoal_tm
  val newasms = mapfilter (SPEC gvar o CONV_RULE transform) thms
  val newasms_tm = list_mk_conj (map concl newasms)
  val goal_thm0 = numLib.ARITH_PROVE (mk_imp(newasms_tm, gbody))
  val goal_thm1 = MP goal_thm0 (LIST_CONJ newasms)
  val goal_thm2 = EQT_INTRO (GEN gvar goal_thm1)
  val thm = TRANS newgoal_thm goal_thm2
  val _  =  Trace.trace(1,Trace.PRODUCE(tm,"SBAG_SOLVE",thm))
in
  thm
end

val diff_free = not o can (find_term is_diff)
fun is_ok t =
  (is_sub_bag t orelse (is_eq t andalso is_bag_ty (type_of (rand t)))) andalso
  diff_free t
val (CACHED_SBAG_SOLVE, sbag_cache) =
    Cache.RCACHE(free_vars, is_ok, SBAG_SOLVE)


val SBAG_SOLVER = let
  exception CTXT of thm list;
  fun get_ctxt e = (raise e) handle CTXT c => c
  fun add_ctxt(ctxt, newthms) = let
    val addthese = filter (is_ok o concl) (flatten (map CONJUNCTS newthms))
  in
    CTXT (addthese @ get_ctxt ctxt)
  end
in
  Traverse.REDUCER
  {name=SOME"SBAG_SOLVER",
   addcontext = add_ctxt,
   apply = fn args => CACHED_SBAG_SOLVE (get_ctxt (#context args)),
   initial = CTXT []}
end;

val SBAG_SOLVE_ss = SSFRAG
  {name=SOME"SBAG_SOLVE",
   ac = [], convs = [], filter = NONE, rewrs = [],
   dprocs = [SBAG_SOLVER], congs = []}

end
