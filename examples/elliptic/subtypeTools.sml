(* ========================================================================= *)
(* PREDICATE SUBTYPE PROVER                                                  *)
(* ========================================================================= *)

structure subtypeTools :> subtypeTools =
struct

open HolKernel Parse boolLib bossLib res_quanTools;

val ERR = mk_HOL_ERR "subtypeTools";
val Bug = mlibUseful.Bug;
val Error = ERR "";

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

fun bool_compare (true,false) = LESS
  | bool_compare (false,true) = GREATER
  | bool_compare _ = EQUAL;

val dest_in = dest_binop pred_setSyntax.in_tm (ERR "dest_in" "");

val is_in = can dest_in;

val abbrev_tm = ``Abbrev``;

fun dest_abbrev tm =
    let
      val (c,t) = dest_comb tm
      val () = if same_const c abbrev_tm then () else raise ERR "dest_abbrev" ""
    in
      dest_eq t
    end;

val is_abbrev = can dest_abbrev;

val norm_rule =
    SIMP_RULE (simpLib.++ (pureSimps.pure_ss, resq_SS))
      [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
       AND_IMP_INTRO, GSYM CONJ_ASSOC];

fun match_tac th =
    let
      val th = norm_rule th
      val (_,tm) = strip_forall (concl th)
    in
      (if is_imp tm then MATCH_MP_TAC else MATCH_ACCEPT_TAC) th
    end;

fun flexible_solver solver cond =
    let
      val cond_th = solver cond
      val cond_tm = concl cond_th
    in
      if cond_tm = cond then cond_th
      else if cond_tm = mk_eq (cond,T) then EQT_ELIM cond_th
      else raise Bug "flexible_solver: solver didn't prove condition"
    end;

fun cond_rewr_conv rewr =
    let
      val rewr = SPEC_ALL (norm_rule rewr)
      val rewr_tm = concl rewr
      val (no_cond,eq) =
          case total dest_imp_only rewr_tm of
            NONE => (true,rewr_tm)
          | SOME (_,eq) => (false,eq)
      val pat = lhs eq
    in
      fn solver => fn tm =>
      let
        val sub = match_term pat tm
        val th = INST_TY_TERM sub rewr
      in
        if no_cond then th
        else MP th (flexible_solver solver (rand (rator (concl th))))
      end
    end;

fun cond_rewrs_conv ths =
    let
      val solver_convs = map cond_rewr_conv ths
      fun mk_conv solver solver_conv = solver_conv solver
    in
      fn solver => FIRST_CONV (map (mk_conv solver) solver_convs)
    end;

local
  type cache = (term,thm) Binarymap.dict ref;

  fun in_cache cache (asl,g) =
      case Binarymap.peek (cache,g) of
        NONE => NONE
      | SOME th =>
        if List.all (fn h => mem h asl) (hyp th) then SOME th else NONE;
in
  fun cache_new () = ref (Binarymap.mkDict compare);

  fun cache_tac (cache : cache) (goal as (_,g)) =
      case in_cache (!cache) goal of
        SOME th => ([], fn [] => th | _ => raise Fail "cache_tac: hit")
      | NONE =>
        ([goal],
         fn [th] => (cache := Binarymap.insert (!cache, g, th); th)
          | _ => raise Fail "cache_tac: miss");
end;

fun print_tac s goal = (print s; ALL_TAC goal);

(* ------------------------------------------------------------------------- *)
(* Solver conversions.                                                       *)
(* ------------------------------------------------------------------------- *)

type solver_conv = Conv.conv -> Conv.conv;

fun binop_ac_conv info =
    let
      val {term_compare,
           dest_binop,
           dest_inv,
           dest_exp,
           assoc_th,
           comm_th,
           comm_th',
           id_ths,
           simplify_ths,
           combine_ths,
           combine_ths'} = info

      val is_binop = can dest_binop
      and is_inv = can dest_inv
      and is_exp = can dest_exp

      fun dest tm =
          let
            val (pos,tm) =
                case total dest_inv tm of
                  NONE => (true,tm)
                | SOME (_ : term, tm) => (false,tm)
            val (sing,tm) =
                case total dest_exp tm of
                  NONE => (true,tm)
                | SOME (_ : term, tm, _ : term) => (false,tm)
          in
            (tm,pos,sing)
          end

      fun cmp (x,y) =
          let
            val (xt,xp,xs) = dest x
            and (yt,yp,ys) = dest y
          in
            case term_compare (xt,yt) of
              LESS => (true,false)
            | EQUAL =>
              (case bool_compare (xp,yp) of
                 LESS => (true,true)
               | EQUAL =>
                 (case bool_compare (xs,ys) of
                    LESS => (true,true)
                  | EQUAL => (true,true)
                  | GREATER => (false,true))
               | GREATER => (false,true))
            | GREATER => (false,false)
          end

      val assoc_conv = cond_rewr_conv assoc_th

      val comm_conv = cond_rewr_conv comm_th

      val comm_conv' = cond_rewr_conv comm_th'

      val id_conv = cond_rewrs_conv id_ths

      val term_simplify_conv = cond_rewrs_conv simplify_ths

      val term_combine_conv =
          let
            val conv = cond_rewrs_conv combine_ths
          in
            fn solver =>
               conv solver THENC
               reduceLib.REDUCE_CONV THENC
               TRY_CONV (term_simplify_conv solver)
          end

      val term_combine_conv' =
          let
            val conv = cond_rewrs_conv combine_ths'
          in
            fn solver =>
               conv solver THENC
               LAND_CONV
                 (reduceLib.REDUCE_CONV THENC
                  TRY_CONV (term_simplify_conv solver)) THENC
               TRY_CONV (id_conv solver)
          end

      fun push_conv solver tm =
          TRY_CONV
          let
            val (_,a,b) = dest_binop tm
          in
            case total dest_binop b of
              NONE =>
              let
                val (ok,eq) = cmp (a,b)
              in
                (if ok then ALL_CONV else comm_conv solver) THENC
                (if eq then TRY_CONV (term_combine_conv solver) else ALL_CONV)
              end
            | SOME (_,b,_) =>
              let
                val (ok,eq) = cmp (a,b)
              in
                (if ok then ALL_CONV else comm_conv' solver) THENC
                ((if eq then term_combine_conv' solver else NO_CONV) ORELSEC
                 (if ok then ALL_CONV else push_conv' solver))
              end
          end tm
      and push_conv' solver =
          RAND_CONV (push_conv solver) THENC TRY_CONV (id_conv solver)

      (* Does not raise an exception *)
      fun ac_conv solver tm =
          (case total dest_binop tm of
             NONE => TRY_CONV (term_simplify_conv solver THENC ac_conv solver)
           | SOME (_,a,b) =>
             if is_binop a then
               TRY_CONV (assoc_conv solver THENC ac_conv solver)
             else
               ((id_conv solver ORELSEC
                 LAND_CONV (term_simplify_conv solver)) THENC
                ac_conv solver) ORELSEC
               (if is_binop b then
                  RAND_CONV (ac_conv solver) THENC push_conv solver
                else
                  (RAND_CONV (term_simplify_conv solver) THENC
                   ac_conv solver) ORELSEC
                  push_conv solver)) tm
    in
      (***trace_conv "alg_binop_ac_conv" o***) CHANGED_CONV o ac_conv
    end;

(* ------------------------------------------------------------------------- *)
(* Named conversions.                                                        *)
(* ------------------------------------------------------------------------- *)

type named_conv = {name : string, key : Term.term, conv : solver_conv};

fun named_conv_to_simpset_conv solver_conv =
    let
      val {name : string, key : term, conv : conv -> conv} = solver_conv
      val key = SOME ([] : term list, key)
      and conv = fn c => fn tms : term list => conv (c tms)
      and trace = 2
    in
      {name = name, key = key, conv = conv, trace = trace}
    end;

(* ------------------------------------------------------------------------- *)
(* Subtype contexts.                                                         *)
(* ------------------------------------------------------------------------- *)

val ORACLE = ref false;

fun ORACLE_solver goal =
    EQT_INTRO (mk_oracle_thm "algebra_dproc" ([],goal));

type named_conv = {name : string, key : term, conv : conv -> conv};

datatype context =
    Context of {rewrites : thm list,
                conversions :  named_conv list,
                reductions : thm list,
                judgements : thm list,
                dproc_cache : (term,thm) Binarymap.dict ref};

fun pp p context =
    let
      val Context {rewrites,conversions,reductions,judgements,...} = context
      val rewrites = length rewrites
      and conversions = length conversions
      and reductions = length reductions
      and judgements = length judgements
    in
      PP.begin_block p PP.INCONSISTENT 1;
      PP.add_string p ("<" ^ int_to_string rewrites ^ "r" ^ ",");
      PP.add_break p (1,0);
      PP.add_string p (int_to_string conversions ^ "c" ^ ",");
      PP.add_break p (1,0);
      PP.add_string p (int_to_string reductions ^ "r" ^ ",");
      PP.add_break p (1,0);
      PP.add_string p (int_to_string judgements ^ "j>");
      PP.end_block p
    end;

fun to_string context = PP.pp_to_string (!Globals.linewidth) pp context;

val empty =
    Context {rewrites = [], conversions = [],
             reductions = [], judgements = [],
             dproc_cache = cache_new ()};

fun add_rewrite x context =
    let
      val Context {rewrites = r, conversions = c, reductions = d,
                   judgements = j, dproc_cache = m} = context
    in
      Context {rewrites = r @ [x], conversions = c, reductions = d,
               judgements = j, dproc_cache = ref (!m)}
    end;

fun add_conversion x context =
    let
      val Context {rewrites = r, conversions = c, reductions = d,
                   judgements = j, dproc_cache = m} = context
    in
      Context {rewrites = r, conversions = c @ [x], reductions = d,
               judgements = j, dproc_cache = ref (!m)}
    end;

fun add_reduction x context =
    let
      val Context {rewrites = r, conversions = c, reductions = d,
                   judgements = j, dproc_cache = m} = context
    in
      Context {rewrites = r, conversions = c, reductions = d @ [x],
               judgements = j, dproc_cache = ref (!m)}
    end;

fun add_judgement x context =
    let
      val Context {rewrites = r, conversions = c,reductions = d,
                   judgements = j, dproc_cache = m} = context
    in
      Context {rewrites = r, conversions = c, reductions = d,
               judgements = j @ [x], dproc_cache = ref (!m)}
    end;

local
  exception State of
    {assumptions : term list,
     reductions : tactic list,
     judgements : tactic list};

  local
    val abbrev_rule = prove
        (``!v t. Abbrev (v = t) ==> (!s. t IN s ==> v IN s)``,
         RW_TAC std_ss [markerTheory.Abbrev_def]);

    fun reduce_tac th = match_tac th THEN REPEAT CONJ_TAC;

    fun assume_reduction th (State {assumptions,reductions,judgements}) =
        let
(***
          val () = (print "assume_reduction: "; print_thm th; print "\n")
***)
        in
          State {assumptions = concl th :: assumptions,
                 reductions = reduce_tac th :: reductions,
                 judgements = judgements}
        end
      | assume_reduction _ _ = raise Fail "assume_reduction";

    fun assume_judgement th (State {assumptions,reductions,judgements}) =
        let
(***
          val () = (print "assume_judgement: "; print_thm th; print "\n")
***)
        in
          State {assumptions = concl th :: assumptions,
                 reductions = reductions,
                 judgements = reduce_tac th :: judgements}
        end
      | assume_judgement _ _ = raise Fail "assume_judgement";
  in
    fun initial_state reductions judgements =
        State {assumptions = [],
               reductions = map reduce_tac reductions,
               judgements = map reduce_tac judgements};

    fun state_add (s,[]) = s
      | state_add (s, th :: ths) =
        let
          val tm = concl th
        in
          if is_in tm then state_add (assume_reduction th s, ths)
          else if is_abbrev tm then
            state_add (assume_judgement (MATCH_MP abbrev_rule th) s, ths)
          else if is_conj tm then state_add (s, CONJUNCTS th @ ths)
          else state_add (s,ths)
        end;
  end;

  fun state_apply_dproc dproc_cache dproc_context goal =
      if not (is_in goal) then
        raise ERR "algebra_dproc" "not of form X IN Y"
      else if !ORACLE then ORACLE_solver goal
      else
        let
          val {context, solver = _, relation = _, stack = _} = dproc_context
          val {assumptions,reductions,judgements} =
              case context of
                State state => state
              | _ => raise Bug "state_apply_dproc: wrong exception type"

          fun dproc_tac goal =
              (REPEAT (cache_tac dproc_cache
                       THEN print_tac "-"
                       THEN FIRST reductions)
               THEN (FIRST (map (fn tac => tac THEN dproc_tac) judgements)
                     ORELSE reduceLib.REDUCE_TAC)
               THEN NO_TAC) goal

(***
          val _ = (print "algebra_dproc: "; print_term goal; print "\n")
***)
          val th = TAC_PROOF ((assumptions,goal), dproc_tac)
        in
          EQT_INTRO th
        end;

  fun algebra_dproc reductions judgements dproc_cache =
      Traverse.REDUCER {name = NONE,
                        initial = initial_state reductions judgements,
                        addcontext = state_add,
                        apply = state_apply_dproc dproc_cache};
in
  fun simpset_frag context =
      let
        val Context {rewrites, conversions, reductions,
                     judgements, dproc_cache} = context
        val convs = map named_conv_to_simpset_conv conversions
        val dproc = algebra_dproc reductions judgements dproc_cache
      in
        simpLib.SSFRAG
          {name = NONE, ac = [], congs = [], convs = convs, rewrs = rewrites,
           dprocs = [dproc], filter = NONE}
      end;

  fun simpset context = simpLib.++ (std_ss, simpset_frag context);
end;

(* ------------------------------------------------------------------------- *)
(* Subtype context pairs: one for simplification, the other for              *)
(* normalization.                                                            *)
(*                                                                           *)
(* By convention add_X2 adds to both contexts, add_X2' adds to just the      *)
(* simplify context, and add_X2'' adds to just the normalize context.        *)
(* ------------------------------------------------------------------------- *)

datatype context2 = Context2 of {simplify : context, normalize : context};

fun pp2 pp alg =
    let
      val Context2 {simplify,normalize} = alg
    in
      PP.begin_block pp PP.INCONSISTENT 1;
      PP.add_string pp ("{simplify = " ^ to_string simplify ^ ",");
      PP.add_break pp (1,0);
      PP.add_string pp ("normalize = " ^ to_string normalize ^ "}");
      PP.end_block pp
    end;

fun to_string2 context2 = PP.pp_to_string (!Globals.linewidth) pp2 context2;

fun dest2 (Context2 info) = info;

val empty2 =
    Context2 {simplify = empty, normalize = empty};

fun add_rewrite2' r (Context2 {simplify,normalize}) =
    Context2 {simplify = add_rewrite r simplify, normalize = normalize};

fun add_rewrite2'' r (Context2 {simplify,normalize}) =
    Context2 {simplify = simplify, normalize = add_rewrite r normalize};

fun add_rewrite2 r = add_rewrite2' r o add_rewrite2'' r;

fun add_conversion2' r (Context2 {simplify,normalize}) =
    Context2 {simplify = add_conversion r simplify, normalize = normalize};

fun add_conversion2'' r (Context2 {simplify,normalize}) =
    Context2 {simplify = simplify, normalize = add_conversion r normalize};

fun add_conversion2 c = add_conversion2' c o add_conversion2'' c;

fun add_reduction2' d (Context2 {simplify,normalize}) =
    Context2 {simplify = add_reduction d simplify, normalize = normalize};

fun add_reduction2'' d (Context2 {simplify,normalize}) =
    Context2 {simplify = simplify, normalize = add_reduction d normalize};

fun add_reduction2 d = add_reduction2' d o add_reduction2'' d;

fun add_judgement2' r (Context2 {simplify,normalize}) =
    Context2 {simplify = add_judgement r simplify, normalize = normalize};

fun add_judgement2'' r (Context2 {simplify,normalize}) =
    Context2 {simplify = simplify, normalize = add_judgement r normalize};

fun add_judgement2 j = add_judgement2' j o add_judgement2'' j;

fun simpset_frag2 (Context2 {simplify,normalize}) =
    {simplify = simpset_frag simplify,
     normalize = simpset_frag normalize};

fun simpset2 (Context2 {simplify,normalize}) =
    {simplify = simpset simplify, normalize = simpset normalize};

end
