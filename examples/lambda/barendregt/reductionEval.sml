structure reductionEval :> reductionEval =
struct

open HolKernel boolLib simpLib Traverse BasicProvers

structure Parse = struct
open Parse
val (Type,Term) = parse_from_grammars normal_orderTheory.normal_order_grammars
end

fun ERR f msg = mk_HOL_ERR "reductionEval" f msg

open chap3Theory normal_orderTheory

exception redExn of thm Net.net

val congs = [betastar_APPlr, SPEC_ALL betastar_LAM_I,
             betastar_eq_cong]

val initial_net = let
  open Net
in
  insert(lhand (concl beta_betastar), beta_betastar) empty
end

val initial_ctxt = redExn initial_net

val betastar_t = ``(-b->*)``
val normorderstar_t = ``(-n->*)``
val beta_t = ``(-b->)``
val term_ty = ``:term``

fun dest_binop t = let
  val (fx,y) = dest_comb t
  val (f,x) = dest_comb fx
in
  (f,x,y)
end

fun munge (thlistlist, n) =
    case thlistlist of
      [] => n
    | [] :: rest => munge (rest, n)
    | (th :: ths) :: rest => let
      in
        case CONJUNCTS (SPEC_ALL th) of
          [] => raise Fail "munge: Can't happen"
        | [th] => let
            open Net relationTheory
          in
            case total dest_binop (concl th) of
              SOME (R,from,to) =>
              if aconv R betastar_t then
                munge (ths :: rest, insert (from,th) n)
              else if aconv R normorderstar_t then
                munge (ths :: rest, insert (from,MATCH_MP nstar_betastar th) n)
              else if aconv R beta_t then
                munge (ths :: rest, insert (from,MATCH_MP RTC_SINGLE th) n)
              else munge (ths :: rest, n)
            | NONE => munge (ths :: rest, n)
          end
        | thlist => munge (thlist :: ths :: rest, n)
      end

fun addcontext (ctxt, thms) = let
  val n = case ctxt of redExn n => n
                     | _ => raise ERR "addcontext" "Wrong sort of ctxt"
in
  redExn (munge([thms], n))
end

fun applythm t th = PART_MATCH lhand th t

fun apply {solver,context,stack,relation} t = let
  val n = case context of redExn n => n
                        | _ => raise ERR "apply" "Wrong sort of ctxt"
  val matches = Net.match t n
in
  tryfind (applythm t) matches
end

val reducer = Traverse.REDUCER {name = SOME "beta-reduction reducer",
                                addcontext = addcontext,
                                apply = apply,
                                initial = initial_ctxt}

val betastar_po = let
  open relationTheory Travrules
  infix |> fun x |> f = f x
  fun rwt th = th |> REWRITE_RULE [reflexive_def, transitive_def]
                  |> Q.ISPEC `compat_closure beta`
in
  mk_preorder (rwt transitive_RTC, rwt reflexive_RTC)
end

val equality_po = let
  open Travrules
  val TRAVRULES {relations,...} = EQ_tr
in
  hd relations
end

fun betafy ss =
    simpLib.add_weakener ([betastar_po, equality_po], congs, reducer) ss ++
    rewrites [termTheory.lemma14b, normal_orderTheory.nstar_betastar_bnf]

fun goalnames (asl, w) = let
  val fvs = FVL (w::asl) empty_tmset
  fun foldthis(t,acc) = HOLset.add(acc, #1 (dest_var t))
in
  HOLset.listItems (HOLset.foldl foldthis (HOLset.empty String.compare) fvs)
end
val SUB_t = ``term$SUB``
val VAR_t = ``term$VAR``

fun unvarify_tac (w as (asl,g)) = let
  val (f,x,y) = dest_binop g
  val y_fvs = free_vars y
  val y_fvs = filter (fn t => type_of t = term_ty) y_fvs
  val (strs, sets) =
      List.foldl binderLib.find_avoids (empty_tmset, empty_tmset) (g::asl)
  val finite_sets = List.mapPartial (total pred_setSyntax.dest_finite) asl
  fun filterthis t = not (is_var t) orelse mem t finite_sets
  val sets = List.filter filterthis (HOLset.listItems sets)
  val sets = List.filter (fn t => not (mem (rand t) y_fvs)) sets
  fun do_them (strs,sets) ys (w as (asl,g)) =
      case ys of
        [] => ALL_TAC w
      | y::rest => let
          val avoid_t = let
            open pred_setSyntax
          in
            List.foldl mk_union (mk_set (HOLset.listItems strs)) sets
          end
          val newname = Lexis.gen_variant Lexis.tmvar_vary
                                          (goalnames w)
                                          (#1 (dest_var y) ^ "s")
          val newname_t = mk_var(newname, stringSyntax.string_ty)
          val inst1 = [y |-> mk_comb(VAR_t, newname_t)]
          val x'_base = Term.subst inst1 x
          val y'_base = Term.subst inst1 y
          val x' = list_mk_comb(SUB_t, [y,newname_t,x'_base])
          val y' = list_mk_comb(SUB_t, [y,newname_t,y'_base])
          val g' = list_mk_comb(f, [x',y'])
        in
          binderLib.NEW_TAC newname avoid_t THEN
          SUBGOAL_THEN (mk_eq(g,g')) SUBST1_TAC THENL [
            ASM_SIMP_TAC (srw_ss()) [termTheory.lemma14b],
            MATCH_MP_TAC chap3Theory.reduction_beta_subst THEN
            do_them (HOLset.add(strs,newname_t), sets) rest
          ]
        end w
in
  do_them (strs,sets) y_fvs
end w


end
