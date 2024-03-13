structure IndDefLib :> IndDefLib =
struct

local open IndDefRules in end;

open HolKernel boolLib Abbrev;

type monoset = InductiveDefinition.monoset;

val ERR = mk_HOL_ERR "IndDefLib";
val ERRloc = mk_HOL_ERRloc "IndDefLib";

local open Absyn
      fun head clause =
         let val appl = last (strip_imp (snd(strip_forall clause)))
         in fst(strip_app appl)
         end
      fun determ M =
          fst(Term.dest_var M handle HOL_ERR _ => Term.dest_const M)
           handle HOL_ERR _ => raise ERR "determ" "Non-atom in antiquote"
      fun dest (AQ (_,tm)) = determ tm
        | dest (IDENT (_,s)) = s
        | dest other = raise ERRloc "names_of.reln_names.dest"
                                    (locn_of_absyn other) "Unexpected structure"
in
fun term_of_absyn absyn = let
  val clauses   = strip_conj absyn
  fun checkcl a = let
    val nm = dest (head a)
  in
    if mem nm ["/\\", "\\/", "!", "?", "LET",
               UnicodeChars.conj, UnicodeChars.disj, UnicodeChars.forall,
               UnicodeChars.exists]
    then
      raise ERRloc "term_of_absyn" (locn_of_absyn a)
                   ("Abstract syntax looks to be trying to redefine "^nm^". "^
                     "\nThis is probably an error.\nIf you must, define with \
                     \another name and use overload_on")
    else nm
  end
  val names     = mk_set (map checkcl clauses)
  val resdata   = List.map (fn s => (s, Parse.hide s)) names
  fun restore() =
      List.app (fn (s,d) => Parse.update_overload_maps s d) resdata
  val tm =
      Parse.absyn_to_term (Parse.term_grammar()) absyn
      handle e => (restore(); raise e)
in
  restore();
  (tm, map locn_of_absyn clauses)
end

fun term_of q = term_of_absyn (Parse.Absyn q)

end;

(* ----------------------------------------------------------------------
    Store all rule inductions
   ---------------------------------------------------------------------- *)

type rule_induction_map = ({Thy:string,Name:string},thm list) Binarymap.dict

fun listdict_add (d, k, e) =
    case Binarymap.peek(d, k) of
      NONE => Binarymap.insert(d,k,[e])
    | SOME l => Binarymap.insert(d,k,e::l)

fun ind_thm_to_consts thm = let
  open boolSyntax
  val c = concl thm
  val (_, bod) = strip_forall c
  val (_, con) = dest_imp bod
  val cons = strip_conj con
  fun to_kname {Name,Thy,...} = {Name = Name, Thy = Thy}
in
  map (fn t => t |> strip_forall |> #2 |> dest_imp |> #1 |> strip_comb |> #1
                 |> dest_thy_const |> to_kname)
      cons
end

fun add_rule_induction0 th tmap = let
  val ts = ind_thm_to_consts th
in
  List.foldl (fn (t,d) => listdict_add(d,t,th)) tmap ts
end

fun apply_delta (ThmSetData.ADD(_, th)) tmap = add_rule_induction0 th tmap
  | apply_delta _ tmap = tmap

(* making it exportable *)
val {update_global_value = rule_ind_apply_global_update,
     record_delta = rule_ind_record_delta,
     get_deltas = rule_ind_get_deltas,
     get_global_value = rule_induction_map,
     DB = rule_induction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "rule_induction",
      delta_ops = {apply_to_global = apply_delta,
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = Binarymap.mkDict KernelSig.name_compare,
                   apply_delta = apply_delta}
    }

fun add_rule_induction th =
    rule_ind_apply_global_update (add_rule_induction0 th)
fun export_rule_induction s =
    let val d = ThmSetData.mk_add s
    in
      rule_ind_record_delta d;
      rule_ind_apply_global_update (apply_delta d)
    end

fun thy_rule_inductions thyname = let
  open ThmSetData
in
  rule_ind_get_deltas {thyname = thyname} |> added_thms
end

(* ----------------------------------------------------------------------
    the built-in monoset, that users can update as they prove new
    monotonicity results about their constants
   ---------------------------------------------------------------------- *)

val the_monoset = ref InductiveDefinition.bool_monoset

fun mono_name th = let
  open boolLib
  val (_, con) = dest_imp (concl th)
in
  #1 (dest_const (#1 (strip_comb (#1 (dest_imp con)))))
end

fun add_mono_thm th = the_monoset := (mono_name th, th) :: (!the_monoset)

(* making it exportable *)
val {export = export_mono, ...} =
    ThmSetData.new_exporter {
      settype = "mono",
      efns = {
        add = fn {named_thm,...} => add_mono_thm (#2 named_thm),
        remove = fn _ => ()
      }
    }

fun thy_monos thyname =
    let
      open ThmSetData
    in
      theory_data {settype = "mono", thy = thyname} |> added_thms
    end

(*---------------------------------------------------------------------------
  given a case theorem of the sort returned by new_inductive_definition
  return the name of the first new constant mentioned
  form is
        (!x y z.  (C x y z = ...)) /\
        (!u v w.  (D u v w = ...))
   in which case we return ["C", "D"]
 ---------------------------------------------------------------------------*)

open InductiveDefinition

fun names_from_casethm thm = let
  open HolKernel boolSyntax
  val forallbod = #2 o strip_forall
  val eqns = thm |> concl |> forallbod |> strip_conj |> map forallbod
  val cnsts = map (#1 o strip_comb o lhs) eqns
in
  map (#1 o dest_const) cnsts
end

val derive_mono_strong_induction = IndDefRules.derive_mono_strong_induction;
fun derive_strong_induction (rules,ind) =
    IndDefRules.derive_mono_strong_induction (!the_monoset) (rules, ind)

fun save_theorems name (rules, indn, strong_ind, cases) = let
in
  save_thm(name^"_rules", rules);
  save_thm(name^"_ind", indn);
  save_thm(name^"_strongind", strong_ind);
  save_thm(name^"_cases", cases);
  export_rule_induction (name ^ "_strongind")
end

fun find_double_implications (tm,locs) =
    let fun rule_has_double_imp conj =
            let val (_, body) = strip_forall conj
                val (lhs, _) = strip_imp body
            in
                length lhs > 1
            end
        fun process_conjs i cs =
            case cs of
                [] => NONE
              | c::rest => if rule_has_double_imp c
                           then SOME (i, List.nth(locs,i))
                           else process_conjs (i+1) rest
    in
      process_conjs 0 (strip_conj tm)
    end

fun Hol_mono_reln name monoset tm = let
  val _ = Lexis.ok_sml_identifier (name ^ !boolLib.def_suffix) orelse
          raise ERR "Hol_mono_reln"
                    ("Bad name for definition: "^ Lib.mlquote name^
                     " (use xHol_reln to specify a better)")
  val _ = case find_double_implications tm of
              NONE => ()
           |  SOME (idx,loc) => raise ERRloc "Hol_mono_reln" loc
                                ("Clause #" ^ Int.toString idx ^
                                 " has a double implication (use conjunctions instead)")
  val (rules, indn, cases) = new_inductive_definition monoset name tm
      (* not! InductiveDefinition.bool_monoset tm *)
  val strong_ind = derive_strong_induction (rules, indn)
in
  save_theorems name (rules, indn, strong_ind, cases);
  (rules, indn, cases)
end
handle e => raise (wrap_exn "IndDefLib" "Hol_mono_reln" e);

(* ----------------------------------------------------------------------
    utility to isolate term being inducted on
   ---------------------------------------------------------------------- *)

local
  val p = mk_var("p", bool) and q = mk_var("q", bool) and r = mk_var("r", bool)
in
val SWITCH_HYPS = tautLib.TAUT_PROVE
                    (mk_eq(list_mk_imp([p,q],r),list_mk_imp([q,p],r)))
val SWITCH_HYPS_NEG =
    tautLib.TAUT_PROVE (mk_eq(mk_imp(p, mk_neg q), mk_imp(q, mk_neg p)))
val NOT_EQ_IMPF = tautLib.TAUT_PROVE (mk_eq(mk_neg p, mk_imp(p,F)))
end (* local *)

val AND_IMP_INTRO' = GSYM AND_IMP_INTRO
val CONJ_ASSOC' = GSYM CONJ_ASSOC
fun LEFT_IMP_EXISTS_CONV' t =
    if is_neg t then NOT_EXISTS_CONV t
    else LEFT_IMP_EXISTS_CONV t
fun liftLeftImp vs =
    (* t is of form (?v1 .. vn. t0) ==> R, where v1 .. vn is vs (can be
       empty), and t0 is either an "isolated" term, or a conjunction where
       the term of interest is the left conjunct *)
    let
      fun finish t =
          let val (l,r) = dest_imp t
          in
            if is_conj l then REWR_CONV AND_IMP_INTRO' t
            else ALL_CONV t
          end
      fun doQs [] = finish
        | doQs (v::vs) = LEFT_IMP_EXISTS_CONV' THENC QUANT_CONV (doQs vs)
    in
      doQs vs
    end
fun liftRightImp vs =
    let
    (* t is of form “L ==> !v1 .. vn. t0 ==> R”, where t0 is the term
       of interest. *)
      fun doQs [] = REWR_CONV SWITCH_HYPS ORELSEC REWR_CONV SWITCH_HYPS_NEG
        | doQs (_ :: rest) = RIGHT_IMP_FORALL_CONV THENC QUANT_CONV (doQs rest)
    in
      doQs vs
    end

fun liftLeftConj vs t =
    (* t of form (?v1 .. vn. t0) /\ tR where vs = v1 .. vn, and if t0 is
       conjunction then term of interest is left conjunct, otherwise t-o-i is
       all of t0 *)
    let
      fun doQs [] = (fn t => if is_conj (lhand t) then REWR_CONV CONJ_ASSOC' t
                             else ALL_CONV t)
        | doQs (v::vs) = LEFT_AND_EXISTS_CONV THENC QUANT_CONV (doQs vs)
    in
      doQs vs t
    end
fun liftRightConj vs t =
    (* t of form tL /\ (?v1 .. vn. t0) where vs = v1.. vn and if t0 is a
       conjunction then term of interest is left conjunct, otherwise t-o-i is
       all of t0 *)
    let
      fun doQs [] = (fn t => if is_conj (rand t) then
                               (REWR_CONV CONJ_ASSOC THENC
                                LAND_CONV (REWR_CONV CONJ_COMM) THENC
                                REWR_CONV CONJ_ASSOC') t
                             else REWR_CONV CONJ_COMM t)
        | doQs (v::vs) = RIGHT_AND_EXISTS_CONV THENC QUANT_CONV (doQs vs)
    in
      doQs vs t
    end


val nobest = (0, NO_CONV, [] : term list, boolSyntax.T)
fun LIMP_CONV c t =
    if is_neg t then RAND_CONV c t
    else LAND_CONV c t
fun find_bestneg wfn t =
    if is_conj t then
      let
        val (l,r) = dest_conj t
        val (bestw_L, move_L, vs_L, tL) = find_bestneg wfn l
        val (bestw_R, move_R, vs_R, tR) = find_bestneg wfn r
      in
        if bestw_L < bestw_R then (* prefers left if possible *)
          (bestw_R, RAND_CONV move_R THENC liftRightConj vs_R, vs_R, tR)
        else if bestw_L = 0 then nobest
        else
          (bestw_L, LAND_CONV move_L THENC liftLeftConj vs_L, vs_L, tL)
      end
    else if is_exists t then
      let
        val (bvs, bod) = strip_exists t
        val (bestw, move, vs, best_t) = find_bestneg wfn bod
      in
        if bestw = 0 then nobest
        else
          let
            val fvs = free_vars best_t
            val vars_to_push_down = op_set_diff aconv bvs fvs
            fun push t =
                IFC SWAP_VARS_CONV (QUANT_CONV push)
                    (EXISTS_AND_CONV ORELSEC REWR_CONV EXISTS_SIMP) t
            fun search_then_push v t =
                let val (v', t') = dest_exists t
                in
                  if v ~~ v' then push t
                  else QUANT_CONV (search_then_push v) t
                end
            fun all_searches [] = ALL_CONV
              | all_searches (v::vs) = all_searches vs THENC search_then_push v
          in
            (bestw,STRIP_QUANT_CONV move THENC all_searches vars_to_push_down,
             op_union aconv vs (op_intersect aconv fvs bvs), best_t)
          end
      end
    else if wfn t > 0 then (wfn t, ALL_CONV, [], t)
    else nobest
fun find_best wfn t =
    if is_imp t then
      let val (l,r) = dest_imp t
          val (bestweight_L,move_L,vs_L,tL) = find_bestneg wfn l
          val (bestweight_R,move_R,vs_R,tR) = find_best wfn r
      in
        if bestweight_L < bestweight_R then (* prefers left match if possible *)
          (bestweight_R, RAND_CONV move_R THENC liftRightImp vs_R, vs_R, tR)
        else if bestweight_L = 0 then nobest
        else
          (bestweight_L, LIMP_CONV move_L THENC liftLeftImp vs_L, vs_L, tL)
      end
    else if is_forall t then
      let val (vs, t0) = strip_forall t
          val (bestw,move,vs',best_t) = find_best wfn t0
      in
        if bestw = 0 then nobest
        else
          let
            val fvs = free_vars best_t
            val vars_to_push_down = op_set_diff aconv vs fvs
            fun push t =
                IFC SWAP_VARS_CONV (QUANT_CONV push)
                    (FORALL_IMP_CONV ORELSEC REWR_CONV FORALL_SIMP) t
            fun search_then_push v t =
                let val (v', t') = dest_forall t
                in
                  if v ~~ v' then push t
                  else QUANT_CONV (search_then_push v) t
                end
            fun all_searches [] = ALL_CONV
              | all_searches (v::vs) = all_searches vs THENC search_then_push v
          in
            (bestw,STRIP_QUANT_CONV move THENC all_searches vars_to_push_down,
             op_union aconv vs' (op_intersect aconv fvs vs), best_t)
          end
      end
    else nobest

fun numargs t = length (#2 (strip_comb t))
fun strip_ncomb n t =
    let
      fun recurse A n t =
          if n <= 0 then (t, A)
          else let val (f,x) = dest_comb t
               in
                 recurse (x::A) (n - 1) f
               end
    in
      recurse [] n t
    end

(* assume t is of form “!vs... Rt ==> Q”. Now find (non-schematic)
   arguments in Rt that are not variables and introduce fresh
   variables for each, and add equations for them, making eventual
   term

           !vs evs. Rt ==> (ev1 = t1) /\ (ev2 = t2) ==> Q
*)
fun introduce_vars ns t =
    let
      val (vs, imp_t) = strip_forall t
      val (l, r) = dest_imp imp_t
      val (R, args) = strip_ncomb (numargs l - ns) l
      fun foldthis (a, (prevvars, avoids, eqns, t)) =
          if is_var a andalso not (tmem a prevvars) then
            (a::prevvars, a::avoids, eqns, mk_comb(t,a))
          else
            let val newvar =
                    case free_vars a of
                        [] => variant avoids (mk_var("x", type_of a))
                      | v::_ => variant avoids
                                        (mk_var(#1 (dest_var v), type_of a))
            in
              (prevvars, newvar::avoids, (a, newvar) :: eqns, mk_comb(t,newvar))
            end
      val (_, _, eqns, new_lt) = foldl foldthis ([],free_vars imp_t,[],R) args
    in
      if null eqns then ALL_CONV t
      else let
        val eqns = List.rev eqns
        val new_vs = map #2 eqns
        val eqns_c = list_mk_conj (map mk_eq eqns)
        val newt = list_mk_forall (new_vs, mk_imp(new_lt, mk_imp(eqns_c, r)))
        val th = REPEATC Unwind.UNWIND_FORALL_CONV newt |> SYM
      in
        STRIP_QUANT_CONV (K th) t
      end
    end

(* t is of form “!vs. R v1 .. vm ==> Q vs”, where v1 through vm may be a
   proper subset of v1 .. vm. Push all elements of vs that are not arguments
   of R down to scope only over Q vs
*)
fun push_old_vars t =
    let
      val (_, bod) = strip_forall t
      val (l,r) = dest_imp bod
      val keepvs = free_vars l
      fun push1 t =
          let val (v,_) = dest_forall t
          in
            if tmem v keepvs then NO_CONV
            else (SWAP_VARS_CONV THENC QUANT_CONV push1) ORELSEC
                 FORALL_IMP_CONV
          end t
      fun pushmany t = (TRY_CONV (QUANT_CONV pushmany) THENC TRY_CONV push1) t
    in
      pushmany t
    end


val NEG_EQ_IMP = IMP_CLAUSES |> SPEC_ALL |> CONJUNCTS |> last |> SYM
fun weight pat t =
    if pat ~~ t then 2 else if can (match_term pat) t then 1 else 0
fun isolate_to_front numSchematics Rt (G as (_, gt)) =
    let
      val (_, c, vs, _) = find_best (weight Rt) gt
      val fix_neg = TRY_CONV (REWR_CONV NOT_EQ_IMPF)
      val conv1 = c THENC fix_neg THENC introduce_vars numSchematics THENC
                  push_old_vars THENC
                  TRY_CONV (STRIP_QUANT_CONV (REWR_CONV NOT_EQ_IMPF))
      fun pull_to_front v t =
          let
            val (v', t') = dest_forall t
          in
            if v' ~~ v then ALL_CONV
            else QUANT_CONV (pull_to_front v) THENC SWAP_VARS_CONV
          end t
      fun sort_vars_conv vs =
          (* quadratic selection sort, blergh *)
          case vs of
              [] => ALL_CONV
            | v::rest => pull_to_front v THENC QUANT_CONV (sort_vars_conv rest)
      fun genify_tac (G as (_,w)) =
          let val (vs, imp_t) = strip_forall w
              val (l,r) = dest_imp imp_t
              val (_, args0) = strip_comb l
              val args = List.drop(args0, numSchematics)
              val un_qfied = op_set_diff aconv args vs
          in
            MAP_EVERY SPEC_TAC (map (fn t => (t,t)) un_qfied) THEN
            CONV_TAC (sort_vars_conv args)
          end G
    in
      CONV_TAC conv1 THEN genify_tac
    end G

(* ----------------------------------------------------------------------
    the standard entry-points
   ---------------------------------------------------------------------- *)

(* turn off verbiage because Raise will redisplay any exceptions *)
val parse =
    term_of |> trace ("syntax_error", 0)
            |> trace ("show_typecheck_errors", 0)

fun xHol_reln name q =
    Hol_mono_reln name (!the_monoset) (parse q)
    handle e => Raise (wrap_exn "IndDefLib" "Hol_reln" e)

fun name_from_def t = let
  open boolSyntax
  val cs = strip_conj t
in
  hd cs |> strip_forall |> #2 |> strip_imp |> #2 |> strip_comb |> #1 |>
  dest_var |> #1
end

fun Hol_reln q = let
  val def as (def_t,_) = parse q
  val name = name_from_def def_t
in
  Hol_mono_reln name (!the_monoset) def
end handle e => Raise (wrap_exn "IndDefLib" "Hol_reln" e);

end
