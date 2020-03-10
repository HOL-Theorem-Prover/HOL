(*---------------------------------------------------------------------------
       Some proof automation, which moreover has few theory
       dependencies, and so can be used in places where bossLib
       is overkill.
 ---------------------------------------------------------------------------*)

structure BasicProvers :> BasicProvers =
struct

type simpset = simpLib.simpset;

open HolKernel boolLib markerLib;

val op++ = simpLib.++;
val op&& = simpLib.&&;
val op-* = simpLib.-*;

val ERR = mk_HOL_ERR "BasicProvers";

local val EXPAND_COND_CONV =
           simpLib.SIMP_CONV (pureSimps.pure_ss ++ boolSimps.COND_elim_ss) []
      val EXPAND_COND_TAC = CONV_TAC EXPAND_COND_CONV
      val EXPAND_COND = CONV_RULE EXPAND_COND_CONV
      val NORM_RULE = CONV_RULE (EXPAND_COND_CONV THENC
                                 REWRITE_CONV [markerTheory.Abbrev_def])
in
fun PROVE thl tm = Tactical.prove (tm,
  EXPAND_COND_TAC THEN mesonLib.MESON_TAC (map NORM_RULE thl))

fun PROVE_TAC thl (asl, w) = let
  val working = LLABEL_RESOLVE thl asl
in
  EXPAND_COND_TAC THEN CONV_TAC (DEST_LABELS_CONV) THEN
  mesonLib.MESON_TAC (map NORM_RULE working)
end (asl, w)
val prove_tac = PROVE_TAC

fun GEN_PROVE_TAC x y z thl (asl, w) = let
  val working = LLABEL_RESOLVE thl asl
in
  EXPAND_COND_TAC THEN CONV_TAC (DEST_LABELS_CONV) THEN
  mesonLib.GEN_MESON_TAC x y z (map NORM_RULE working)
end (asl, w)

end; (* local *)


(*---------------------------------------------------------------------------*
 * A simple aid to reasoning by contradiction.                               *
 *---------------------------------------------------------------------------*)

fun SPOSE_NOT_THEN ttac =
  CCONTR_TAC THEN
  POP_ASSUM (fn th => ttac (simpLib.SIMP_RULE boolSimps.bool_ss
                                     [GSYM boolTheory.IMP_DISJ_THM] th))
val spose_not_then = SPOSE_NOT_THEN

(*===========================================================================*)
(* Case analysis and induction tools that index the TypeBase.                *)
(*===========================================================================*)

fun name_eq s M = ((s = fst(dest_var M)) handle HOL_ERR _ => false)

(*---------------------------------------------------------------------------*
 * Mildly altered STRUCT_CASES_TAC, so that it does a SUBST_ALL_TAC instead  *
 * of a SUBST1_TAC.                                                          *
 *---------------------------------------------------------------------------*)

val VAR_INTRO_TAC = REPEAT_TCL STRIP_THM_THEN
                      (fn th => SUBST_ALL_TAC th ORELSE ASSUME_TAC th);

val TERM_INTRO_TAC =
 REPEAT_TCL STRIP_THM_THEN
     (fn th => TRY (SUBST_ALL_TAC th) THEN ASSUME_TAC th);

fun away gfrees0 bvlist =
  rev(fst
    (rev_itlist (fn v => fn (plist,gfrees) =>
       let val v' = prim_variant gfrees v
       in ((v,v')::plist, v'::gfrees)
       end) bvlist ([], gfrees0)));

(*---------------------------------------------------------------------------*)
(* Make free whatever bound variables would prohibit the case split          *)
(* or induction. This is not trivial, since the act of freeing up a variable *)
(* can change its name (if another with same name already occurs free in     *)
(* hypotheses). Then the term being split (or inducted) on needs to be       *)
(* renamed as well.                                                          *)
(*---------------------------------------------------------------------------*)

fun FREEUP [] M g = (ALL_TAC,M)
  | FREEUP tofree M (g as (asl,w)) =
     let val (V,_) = strip_forall w   (* ignore renaming here : idleness! *)
         val Vmap = away (free_varsl (w::asl)) V
         val theta = filter (fn (v,_) => op_mem aconv v tofree) Vmap
         val rebind =
             map snd (filter (fn (v,_) => not (op_mem aconv v tofree)) Vmap)
     in
       ((MAP_EVERY X_GEN_TAC (map snd Vmap)
          THEN MAP_EVERY ID_SPEC_TAC (rev rebind)),
        subst (map op|-> theta) M)
     end;

(*---------------------------------------------------------------------------*)
(* Do case analysis on given term. The quotation is parsed into a term M that*)
(* must match a subterm in the goal (or the assumptions). If M is a variable,*)
(* then the match of the names must be exact. Once the term to split over is *)
(* known, its type and the associated facts are obtained and used to do the  *)
(* split with. Variables of M might be quantified in the goal. If so, we try *)
(* to unquantify the goal so that the case split has meaning.                *)
(*                                                                           *)
(* It can happen that the given term is not found anywhere in the goal. If   *)
(* the term is boolean, we do a case-split on whether it is true or false.   *)
(*---------------------------------------------------------------------------*)

datatype tmkind
    = Free of term
    | Bound of term list * term  (* in Bound(V,M), V = vars to be freed up *)
    | Alien of term;

fun dest_tmkind (Free M)      = M
  | dest_tmkind (Bound (_,M)) = M
  | dest_tmkind (Alien M)     = M;

fun prim_find_subterm FVs tm (asl,w) =
 if is_var tm
 then let val name = fst(dest_var tm)
      in Free (Lib.first(name_eq name) FVs)
         handle HOL_ERR _
         => Bound(let val (BV,_) = strip_forall w
                      val v = Lib.first (name_eq name) BV
                  in ([v], v)
                  end)
      end
 else if List.exists (free_in tm) (w::asl) then Free tm
 else let val (V,body) = strip_forall w
      in if free_in tm body
          then Bound(op_intersect aconv (free_vars tm) V, tm)
          else Alien tm
      end

fun find_subterm qtm (g as (asl,w)) =
  let val FVs = free_varsl (w::asl)
      val tm = Parse.parse_in_context FVs qtm
  in
    prim_find_subterm FVs tm g
  end;

(*---------------------------------------------------------------------------*)
(* Support for pairs copied from coretypes/pairSyntax to be self-contained.  *)
(*---------------------------------------------------------------------------*)

val strip_prod =
 let fun dest_prod ty =
   case total dest_thy_type ty of
      SOME{Tyop = "prod", Thy = "pair", Args = [ty1, ty2]} => (ty1, ty2)
    | other => raise ERR "dest_prod" "not a product type"
 in
    strip_binop (total dest_prod)
 end

fun mk_prod(ty1,ty2) = mk_thy_type{Thy="pair",Tyop="prod",Args=[ty1,ty2]}

fun mk_pair (t1,t2) =
 let val pair_const = prim_mk_const {Name=",",Thy="pair"}
     val pair_const' = inst [alpha |-> type_of t1, beta |-> type_of t2] pair_const
 in list_mk_comb(pair_const',[t1,t2])
 end

(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*      Gamma, (x = pat[v1,...,vn]) |- M[x]                                  *)
(*    ------------------------------------------------------------------     *)
(*      Gamma, ?v1 ... vn. (x = pat[v1,...,vn]) |- M[x]                      *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun CHOOSER v (tm,thm) =
 let val ex_tm = mk_exists(v,tm)
 in (ex_tm, CHOOSE(v, ASSUME ex_tm) thm)
 end;

fun LEFT_EXISTS_INTRO veq thm =
  let val (_,pat) = dest_eq veq
  in snd (itlist CHOOSER (free_vars_lr pat) (veq,thm))
  end;

fun listpair [a,b] = (a,b)
  | listpair l = raise ERR "listpair"
                       ("List of wrong length (" ^Int.toString (length l) ^ ")")

(*---------------------------------------------------------------------------*)
(* Prove a theorem for "deep" case analysis on a term with an (iterated)     *)
(* product type.                                                             *)
(*                                                                           *)
(*   tupleCases ["a", "b", "c"] (v : ty1 # ty2 # ty3) =                      *)
(*      |- !v. ?a b c. v = (a,b,c)                                           *)
(*---------------------------------------------------------------------------*)


val rename =   (* create names for underscored inputs *)
  let val prefix = "_gv"
     fun num2name i = prefix^Int.toString i
  in fn slist =>
       let val num_stream = Portable.make_counter{init=0,inc=1}
           fun gname() = num2name(num_stream())
           fun transform s = if mem s ["_","-"] then gname() else s
       in map transform slist
       end
  end

fun tupleCases names0 v =
 let val pthm = TypeBasePure.nchotomy_of
                  (Option.valOf (TypeBase.read{Thy="pair",Tyop="prod"}))
     val names = rename names0
     val (vname,vty) = dest_var v
     val tys = strip_prod vty
     val vars = Lib.map2 (curry mk_var) names tys
     fun tmpvar_types 0 ty = [ty]
       | tmpvar_types n ty =
          case dest_thy_type ty
           of {Thy="pair",Tyop="prod",Args=[ty1,ty2]} => ty::tmpvar_types (n-1) ty2
            | otherwise => [ty]
     val tmp_vars = map genvar (tl (tmpvar_types (length tys - 2) vty))
     val left_vars = List.take (vars,length vars - 2)
     val last2_vars = listpair(List.drop (vars,length vars - 2))
     val rpairs = zip left_vars tmp_vars @ [last2_vars]
     val rpair_tms = map mk_pair rpairs
     val eqns = map2 (curry mk_eq) (v::tmp_vars) rpair_tms
     val thlist = map ASSUME eqns
     val thm = REWRITE_RULE (tl thlist) (hd thlist)
     fun step eqn th =
      let val th1 = LEFT_EXISTS_INTRO eqn th
          val V = free_vars_lr (rhs eqn)
          val th2 = DISCH (list_mk_exists(V,eqn)) th1
          val th3 = ISPEC (lhs eqn) pthm
      in MP th2 th3
      end
 in
    GEN v (itlist step eqns (itlist SIMPLE_EXISTS vars thm))
 end
 handle e => raise wrap_exn "BasicProvers" "primCases_on (tupleCases)" e


(*---------------------------------------------------------------------------*)
(* Set specified existentially quantified names in nchotomy thm. The input   *)
(* thm0 is direct from the TypeBase and therefore not instantiated to the    *)
(* full type being case-split on. This matters for iterated pair case        *)
(* analysis.                                                                 *)
(*---------------------------------------------------------------------------*)

fun envar s v = if mem s ["_","-"] then v else mk_var(s,snd(dest_var v));

fun set_names names ty thm0 =
 let val vty0 = type_of (fst(dest_forall(concl thm0)))
     val thm = INST_TYPE (match_type vty0 ty) thm0
     val tm = concl thm
     val (v,body) = dest_forall (concl thm)
     val vty = type_of v
     val namelists = List.map (String.tokens Char.isSpace) names
 in
 if null names then thm
 else
  case dest_thy_type vty
   of {Thy="pair",Tyop="prod",...} => tupleCases (hd namelists) v
    | otherwise =>
     let val clauses = zip namelists (strip_disj body)
         fun rename (slist,clause) =
          let val (bvs,M) = strip_exists clause
          in if length bvs <> length slist then
                clause (* fail in such a way that tactic can still be applied. *)
             else
             let val vlist = map2 envar slist bvs
                 val theta = map2 (curry (op |->)) bvs vlist
                 val M' = subst theta M
             in list_mk_exists(vlist,M')
             end
          end
         val tm' = mk_forall(v,list_mk_disj(map rename clauses))
     in
       EQ_MP (Thm.ALPHA tm tm') thm
     end
 end
 handle e => raise wrap_exn "BasicProvers" "primCases_on (set_names)" e
;

fun primCases_on names st (g as (_,w)) =
 let val ty = type_of (dest_tmkind st)
 in case TypeBase.fetch ty
     of SOME facts =>
        let val thm = TypeBasePure.nchotomy_of facts
            val thm' = set_names names ty thm
        in case st
           of Free M =>
               if (is_var M) then VAR_INTRO_TAC (ISPEC M thm') else
               if ty=bool then ASM_CASES_TAC M
               else TERM_INTRO_TAC (ISPEC M thm')
            | Bound(V,M) => let val (tac,M') = FREEUP V M g
                            in (tac THEN VAR_INTRO_TAC (ISPEC M' thm')) end
            | Alien M    => if ty=bool then ASM_CASES_TAC M
                            else TERM_INTRO_TAC (ISPEC M thm')
        end
      | NONE =>
          let val {Thy,Tyop,...} = dest_thy_type ty
          in raise ERR "primCases_on"
                ("No cases theorem found for type: "^Lib.quote (Thy^"$"^Tyop))
          end
 end g;

fun Cases_on qtm g = primCases_on [] (find_subterm qtm g) g
  handle e => raise wrap_exn "BasicProvers" "Cases_on" e;

fun namedCases_on qtm names g =
  primCases_on names (find_subterm qtm g) g
  handle e => raise wrap_exn "BasicProvers" "namedCases_on" e;

fun Cases (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases" "not a forall")
  in primCases_on [] (Bound([Bvar],Bvar)) g
  end
  handle e => raise wrap_exn "BasicProvers" "Cases" e;

fun namedCases names (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "namedCases" "not a forall")
  in primCases_on names (Bound([Bvar],Bvar)) g
  end
  handle e => raise wrap_exn "BasicProvers" "Cases" e;

(*---------------------------------------------------------------------------*)
(* Do induction on a given term.                                             *)
(*---------------------------------------------------------------------------*)

fun primInduct st ind_tac (g as (asl,c)) =
 let fun ind_non_var V M =
       let val (tac,M') = FREEUP V M g
           val Mfrees = free_vars M'
           val Mfset = HOLset.addList(empty_tmset, Mfrees)
           fun has_vars tm =
             not(HOLset.isEmpty
                   (HOLset.intersection(Mfset, FVL [tm] empty_tmset)))
           val tms = filter has_vars asl
           val newvar = variant (free_varsl (c::asl))
                                (mk_var("v",type_of M'))
           val tm = mk_exists(newvar, mk_eq(newvar, M'))
           val th = EXISTS(tm,M') (REFL M')
        in
          tac
            THEN MAP_EVERY UNDISCH_TAC tms
            THEN CHOOSE_THEN MP_TAC th
            THEN MAP_EVERY ID_SPEC_TAC Mfrees
            THEN ID_SPEC_TAC newvar
            THEN ind_tac
        end
 in case st
     of Free M =>
         if is_var M
         then let val tms = filter (free_in M) asl
              in (MAP_EVERY UNDISCH_TAC tms THEN ID_SPEC_TAC M THEN ind_tac) g
              end
         else ind_non_var [] M g
      | Bound(V,M) =>
         if is_var M
           then let val (tac,M') = FREEUP V M g
                in (tac THEN ID_SPEC_TAC M' THEN ind_tac) g
                end
         else ind_non_var V M g
      | Alien M =>
         if is_var M then raise ERR "primInduct" "Alien variable"
         else ind_non_var (free_vars M) M g
 end

(*---------------------------------------------------------------------------*)
(* Induct on a quoted term. First determine the term, then use that to       *)
(* select the induction theorem to use. There are 3 kinds of induction       *)
(* supported: (1) on datatypes; (2) on inductively defined relations from    *)
(* IndDefLib; (3) on ad-hoc inductive objects (e.g. finite maps, finite sets,*)
(* and finite multisets). The latter two are similar but differ in where the *)
(* induction theorem is fetched from (IndDefLib.rule_induction_map or        *)
(* TypeBase.theTypeBase).                                                    *)
(*---------------------------------------------------------------------------*)

fun induct_on_type st ty g =
    case TypeBase.fetch ty of
        SOME facts =>
        let
          val is_mutind_thm = is_conj o snd o strip_imp o snd o strip_forall o
                              concl
        in
          case total TypeBasePure.induction_of facts of
              NONE =>
                raise ERR "induct_on_type"
                      (String.concat ["Type :",Hol_pp.type_to_string ty,
                                      " is registered in the types database, ",
                                      "but there is no associated induction \
                                      \theorem"])
            | SOME thm => (* now select induction tactic *)
              if null (TypeBasePure.constructors_of facts) then
                (* not a datatype*)
                primInduct st (HO_MATCH_MP_TAC thm)
              else if is_mutind_thm thm then
                Mutual.MUTUAL_INDUCT_TAC thm
              else
                primInduct st (Prim_rec.INDUCT_THEN thm ASSUME_TAC) ORELSE
                (primInduct st (HO_MATCH_MP_TAC thm) THEN REPEAT CONJ_TAC)
        end g
      | NONE =>
        raise ERR "induct_on_type"
              (String.concat ["Type: ",Hol_pp.type_to_string ty,
                              " is not registered in the types database"]);

fun checkind th =
    (* if the purported theorem fails to pass muster according to this
       check, we can still let it pass through to the HO_MATCH_MP_TAC, but
       we won't attempt to be clever with it and call isolate_to_front. *)
    let
      val (_, bod) = strip_forall (concl th)
      val (_, what_matches_a_goal) = dest_imp bod
      val (gvs, gimp) = strip_forall what_matches_a_goal
      val (indR, con) = dest_imp gimp
    in
      if List.all is_var (#2 (strip_comb indR)) then ALL_TAC
      else NO_TAC
    end

fun Induct_on qtm g =
 let val st = find_subterm qtm g
     val tm = dest_tmkind st
     val ty = type_of (dest_tmkind st)
     val (_, rngty) = strip_fun ty
 in
  if rngty = Type.bool then (* inductive relation *)
    let
      val (c, _) = strip_comb tm
      fun mkpat t =
          let val (d,_) = dom_rng (type_of t)
          in
            mkpat (mk_comb(t, genvar d))
          end handle HOL_ERR _ => t
      val pat = mkpat tm
      open IndDefLib
    in
      case Lib.total dest_thy_const c of
          SOME {Thy,Name,...} =>
          let
            val indths =
                Binarymap.find (rule_induction_map(), {Thy=Thy,Name=Name})
                handle NotFound => []
            fun numSchematics th =
                let
                  val (_,base) = th |> concl |> strip_forall |> #2 |> dest_imp
                  val (vs, c) = strip_forall base
                  val (l, _) = dest_imp c
                  val numargs = l |> strip_comb |> #2 |> length
                in
                  numargs - length vs
                end
            fun tryind th =
                TRY (checkind th >> isolate_to_front (numSchematics th) pat) >>
                HO_MATCH_MP_TAC th
          in
            MAP_FIRST tryind indths ORELSE induct_on_type st ty
          end g
        | NONE => induct_on_type st ty g
   end
  else
    induct_on_type st ty g
 end
 handle e => raise wrap_exn "BasicProvers" "Induct_on" e;

(*---------------------------------------------------------------------------*)
(* Induct on leading quantified variable.                                    *)
(*---------------------------------------------------------------------------*)

fun grab_var M =
  if is_forall M then fst(dest_forall M) else
  if is_conj M then fst(dest_forall(fst(dest_conj M)))
  else raise ERR "Induct" "expected a forall or a conjunction of foralls";

fun Induct (g as (_,w)) =
 let val v = grab_var w
     val (_,ty) = dest_var (grab_var w)
 in induct_on_type (Bound([v],v)) ty g
 end
 handle e => raise wrap_exn "BasicProvers" "Induct" e


(*---------------------------------------------------------------------------
     Assertional style reasoning
 ---------------------------------------------------------------------------*)

fun chop_at n frontacc l =
  if n <= 0 then (List.rev frontacc, l)
  else
    case l of
      [] => raise Fail "chop_at"
    | (h::t) => chop_at (n-1) (h::frontacc) t


infix gTHEN1 (* "gentle" THEN1 : doesn't fail if the tactic for the
                head goal doesn't completely solve the subgoal. *)
fun ((tac1:tactic) gTHEN1 (tac2:tactic)) (asl:term list,w:term) = let
  val (subgoals, vf) = tac1 (asl,w)
in
  case subgoals of
    [] => ([], vf)
  | (h::hs) => let
      val (sgoals2, vf2) = tac2 h
    in
      (sgoals2 @ hs,
       (fn thmlist => let
          val (firstn, back) = chop_at (length sgoals2) [] thmlist
        in
          vf (vf2 firstn :: back)
       end))
    end
end


fun eqTRANS new old = let
  (* allow for possibility that old might be labelled *)
  open markerLib markerSyntax
  val s = #1 (dest_label (concl old))
in
  ASSUME_NAMED_TAC s (TRANS (DEST_LABEL old) new)
end handle HOL_ERR _ => ASSUME_TAC (TRANS old new)

fun is_labeq t = (* term is a possibly labelled equality *)
 let open markerSyntax
 in is_eq t orelse is_label t andalso is_eq (#2 (dest_label t))
 end;

fun labrhs t = (* term is a possibly labelled equality *)
 let open markerSyntax
 in if is_eq t then rhs t else rhs (#2 (dest_label t))
 end;

fun qlinenum q =
  case q |> qbuf.new_buffer |> qbuf.current |> #2 of
      locn.Loc(locn.LocA(line, _), _) => SOME (line+1)
    | _ => NONE

fun by0 k (q, tac) (g as (asl,w)) = let
  val a = trace ("syntax_error", 0) Parse.Absyn q
  open errormonad
  val (goal_pt, finisher) =
      case Lib.total Absyn.dest_eq a of
        SOME (Absyn.IDENT(_,"_"), r) =>
          if not (null asl) andalso is_labeq (hd asl) then
            (Parse.absyn_to_preterm
               (Absyn.mk_eq(Absyn.mk_AQ (labrhs (hd asl)), r)),
             POP_ASSUM o eqTRANS)
          else
            raise ERR "by" "Top assumption must be an equality"
      | x => (Parse.absyn_to_preterm a, STRIP_ASSUME_TAC)
  val tm = trace ("show_typecheck_errors", 0)
                 (Preterm.smash
                     (goal_pt >-
                      TermParse.ctxt_preterm_to_term
                        Parse.stdprinters
                        (SOME bool)
                        (free_varsl (w::asl))))
                 Pretype.Env.empty
  fun mk_errmsg () =
    case qlinenum q of
        SOME l => " on line "^Int.toString l
      | NONE => ": "^term_to_string tm
in
  (SUBGOAL_THEN tm finisher gTHEN1 (tac THEN k)) g
   handle HOL_ERR _ =>
    raise ERR "by" ("by's tactic failed to prove subgoal"^mk_errmsg())
end

val op by = by0 NO_TAC
val byA = by0 ALL_TAC

fun (q suffices_by tac) g =
  (Q_TAC SUFF_TAC q gTHEN1 (tac THEN NO_TAC)) g
  handle e as HOL_ERR {origin_function,...} =>
         if origin_function = "Q_TAC" then raise e
         else
           case qlinenum q of
               SOME l => raise ERR "suffices_by"
                               ("suffices_by's tactic failed to prove goal on \
                                \line "^Int.toString l)
             | NONE => raise ERR "suffices_by"
                             "suffices_by's tactic failed to prove goal"



fun subgoal q = Q.SUBGOAL_THEN q STRIP_ASSUME_TAC
val sg = subgoal


infix on
fun ((ttac:thm->tactic) on (q:term frag list, tac:tactic)) : tactic =
  (fn (g as (asl:term list, w:term)) => let
    val tm = Parse.parse_in_context (free_varsl (w::asl)) q
  in
    (SUBGOAL_THEN tm ttac gTHEN1 tac) g
  end)

(*===========================================================================*)
(*  General-purpose case-splitting tactics.                                  *)
(*===========================================================================*)

fun case_find_subterm p =
  let
    val f = find_term p
    fun g t =
      if is_comb t then
        g (f (rator t))
        handle HOL_ERR _ => (g (f (rand t)) handle HOL_ERR _ => t)
      else if is_abs t then
        g (f (body t)) handle HOL_ERR _ => t
      else t
  in
    fn t => g (f t)
  end;

fun first_term f tm = f (find_term (can f) tm);

fun first_subterm f tm = f (case_find_subterm (can f) tm);

(*---------------------------------------------------------------------------*)
(* If tm is a fully applied conditional or case expression and the           *)
(* scrutinized subterm of tm is free, return the scrutinized subterm.        *)
(* Otherwise raise an exception.                                             *)
(*---------------------------------------------------------------------------*)

fun scrutinized_and_free_in tm =
 let fun free_case t =
        let val (_, examined, _) = TypeBase.dest_case t
        in if free_in examined tm
              then examined else raise ERR "free_case" ""
        end
 in
    free_case
 end;

fun PURE_TOP_CASE_TAC (g as (_, tm)) =
 let val t = first_term (scrutinized_and_free_in tm) tm
 in Cases_on `^t` end g;

fun PURE_CASE_TAC (g as (_, tm)) =
 let val t = first_subterm (scrutinized_and_free_in tm) tm
 in Cases_on `^t` end g;

fun PURE_FULL_CASE_TAC (g as (asl,w)) =
 let val tm = list_mk_conj(w::asl)
     val t = first_subterm (scrutinized_and_free_in tm) tm
 in Cases_on `^t` end g;

local
  fun tot f x = f x handle HOL_ERR _ => NONE
in
fun case_rws tyi =
    List.mapPartial I
       [Lib.total TypeBasePure.case_def_of tyi,
        tot TypeBasePure.distinct_of tyi,
        tot TypeBasePure.one_one_of tyi]

fun case_rwlist () =
 itlist (fn tyi => fn rws => case_rws tyi @ rws)
        (TypeBase.elts()) [];

(* Add the rewrites into a simpset to avoid re-processing them when
 * (PURE_CASE_SIMP_CONV rws) is called multiple times by EVERY_CASE_TAC.  This
 * has an order of magnitude speedup on developments with large datatypes *)
fun PURE_CASE_SIMP_CONV rws =
    simpLib.SIMP_CONV (boolSimps.bool_ss++simpLib.rewrites rws) []

fun CASE_SIMP_CONV tm = PURE_CASE_SIMP_CONV (case_rwlist()) tm
end;

(*---------------------------------------------------------------------------*)
(* Q: what should CASE_TAC do with literal case expressions?                 *)
(*---------------------------------------------------------------------------*)

fun is_refl tm =
 let val (l,r) = dest_eq tm
 in aconv l r
 end handle HOL_ERR _ => false;

fun TRIV_LET_CONV tm =
 let val (_,a) = boolSyntax.dest_let tm
 in if is_var a orelse is_const a
        orelse Literal.is_literal a
    then (REWR_CONV LET_THM THENC BETA_CONV) tm
    else NO_CONV tm
 end;

fun SIMP_OLD_ASSUMS (orig as (asl1,_)) (gl as (asl2,_)) =
 let val new = op_set_diff aconv asl2 asl1
 in if null new then ALL_TAC
    else let val thms = map ASSUME new
          in MAP_EVERY (Lib.C UNDISCH_THEN (K ALL_TAC)) new THEN
              RULE_ASSUM_TAC (REWRITE_RULE thms) THEN
              MAP_EVERY ASSUME_TAC thms
          end
 end gl;

fun USE_NEW_ASSUM orig_goal cgoal =
 (TRY (WEAKEN_TAC is_refl) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_OLD_ASSUMS orig_goal THEN
  CONV_TAC (DEPTH_CONV TRIV_LET_CONV)) cgoal;

(*---------------------------------------------------------------------------*)
(* Do a case analysis in the conclusion of the goal, then simplify a bit.    *)
(*---------------------------------------------------------------------------*)

fun CASE_TAC gl =
 (PURE_CASE_TAC THEN USE_NEW_ASSUM gl THEN CONV_TAC CASE_SIMP_CONV) gl;

fun TOP_CASE_TAC gl =
 (PURE_TOP_CASE_TAC THEN USE_NEW_ASSUM gl THEN CONV_TAC CASE_SIMP_CONV) gl;


(*---------------------------------------------------------------------------*)
(* Do a case analysis anywhere in the goal, then simplify a bit.             *)
(*---------------------------------------------------------------------------*)

fun FULL_CASE_TAC goal =
 let val rws = case_rwlist()
     val case_conv = PURE_CASE_SIMP_CONV rws
     val asm_rule = Rewrite.REWRITE_RULE rws
 in PURE_FULL_CASE_TAC THEN USE_NEW_ASSUM goal
    THEN RULE_ASSUM_TAC asm_rule
    THEN CONV_TAC case_conv
 end goal;
val full_case_tac = FULL_CASE_TAC

(*---------------------------------------------------------------------------*)
(* Repeatedly do a case analysis anywhere in the goal. Avoids re-computing   *)
(* case info from the TypeBase each time around the loop, so more efficient  *)
(* than REPEAT FULL_CASE_TAC.                                                *)
(*---------------------------------------------------------------------------*)

fun EVERY_CASE_TAC goal =
 let val rws = case_rwlist()
     val case_conv = PURE_CASE_SIMP_CONV rws
     val asm_rule = BETA_RULE o Rewrite.REWRITE_RULE rws
     fun tac a = (PURE_FULL_CASE_TAC THEN USE_NEW_ASSUM a THEN
                  RULE_ASSUM_TAC asm_rule THEN
                  CONV_TAC case_conv) a
 in REPEAT tac
 end goal;
val every_case_tac = EVERY_CASE_TAC

(*===========================================================================*)
(* Rewriters                                                                 *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*
 * When invoked, we know that th is an equality, at least one side of which  *
 * is a variable.                                                            *
 *---------------------------------------------------------------------------*)

fun is_bool_atom tm =
  is_var tm andalso (type_of tm = bool)
  orelse is_neg tm andalso is_var (dest_neg tm);


fun orient th =
 let val c = concl th
 in if is_bool_atom c
    then (if is_neg c then EQF_INTRO th else EQT_INTRO th)
    else let val (lhs,rhs) = dest_eq c
         in if is_var lhs
            then if is_var rhs
                 then case Term.compare (lhs, rhs)
                       of LESS  => SYM th
                        | other => th
                 else th
            else SYM th
         end
 end;

fun VSUBST_TAC tm = UNDISCH_THEN tm (SUBST_ALL_TAC o orient);

fun var_eq tm =
   let val (lhs,rhs) = dest_eq tm
   in
       aconv lhs rhs
     orelse
       (is_var lhs andalso not (free_in lhs rhs))
     orelse
       (is_var rhs andalso not (free_in rhs lhs))
   end
   handle HOL_ERR _ => is_bool_atom tm


fun grab P f v =
  let fun grb [] = v
        | grb (h::t) = if P h then f h else grb t
  in grb
  end;

fun ASSUM_TAC f P = W (fn (asl,_) => grab P f NO_TAC asl)

val VAR_EQ_TAC = ASSUM_TAC VSUBST_TAC var_eq;
val var_eq_tac = VAR_EQ_TAC

fun ASSUMS_TAC f P = W (fn (asl,_) =>
  case filter P asl
   of []     => NO_TAC
    | assums => MAP_EVERY f (List.rev assums));

fun CONCL_TAC f P = W (fn (_,c) => if P c then f else NO_TAC);

fun LIFT_SIMP ss tm =
  UNDISCH_THEN tm (STRIP_ASSUME_TAC o simpLib.SIMP_RULE ss []);

local
  fun DTHEN ttac = fn (asl,w) =>
   let val (ant,conseq) = dest_imp_only w
       val (gl,prf) = ttac (ASSUME ant) (asl,conseq)
   in (gl, Thm.DISCH ant o prf)
   end
in
val BOSS_STRIP_TAC = Tactical.FIRST [GEN_TAC,CONJ_TAC, DTHEN STRIP_ASSUME_TAC]
end;

fun add_simpls tyinfo ss =
    (ss ++ simpLib.tyi_to_ssdata tyinfo) handle HOL_ERR _ => ss;

fun is_dneg tm = 1 < snd(strip_neg tm);

val notT = mk_neg T
val notF = mk_neg F;

fun breakable tm =
    is_exists tm  orelse
    is_conj tm    orelse
    is_disj tm    orelse
    is_dneg tm    orelse
    aconv notT tm orelse
    aconv notF tm orelse
    aconv T tm    orelse
    aconv F tm

(* ----------------------------------------------------------------------
    LET_ELIM_TAC

    eliminates lets by pulling them up, turning them into universal
    quantifiers, and eventually moving new abbreviations into the
    assumption list.
   ---------------------------------------------------------------------- *)

val let_movement_thms = let
  open combinTheory
in
  ref [o_THM, o_ABS_R, C_ABS_L, C_THM,
       GEN_literal_case_RAND, GEN_literal_case_RATOR,
       GEN_LET_RAND, GEN_LET_RATOR, S_ABS_R]
end

val IMP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL IMP_CONG)

fun ABBREV_CONV tm = let
  val t = rand tm
  val (l,r) = dest_eq t
in
  if not (is_var l) orelse is_var r then
    REWR_CONV markerTheory.Abbrev_def THENC
    REWR_CONV EQ_SYM_EQ
  else ALL_CONV
end tm

val ABBREV_ss =
    simpLib.SSFRAG {name=SOME"ABBREV",
                    ac = [], congs = [],
                      convs = [{conv = K (K ABBREV_CONV),
                                key = SOME ([], ``marker$Abbrev x``),
                                trace = 2, name = "ABBREV_CONV"}],
                      dprocs = [], filter = NONE, rewrs = []}

(*---------------------------------------------------------------------------*)
(* The staging of first two successive calls to SIMP_CONV ensure that the    *)
(* LET_FORALL_ELIM theorem is applied after all the movement is possible.    *)
(*---------------------------------------------------------------------------*)

fun LET_ELIM_TAC goal =
 let open simpLib pureSimps boolSimps
 in
  CONV_TAC
    (QCHANGED_CONV
       (SIMP_CONV pure_ss (!let_movement_thms) THENC
        SIMP_CONV pure_ss (combinTheory.LET_FORALL_ELIM ::
                           combinTheory.literal_case_FORALL_ELIM ::
                           !let_movement_thms) THENC
        SIMP_CONV (pure_ss ++ ABBREV_ss ++ UNWIND_ss) [Cong IMP_CONG'])) THEN
  REPEAT BOSS_STRIP_TAC THEN markerLib.REABBREV_TAC
 end goal

fun new_let_thms thl = let_movement_thms := thl @ !let_movement_thms


(*---------------------------------------------------------------------------
      STP_TAC (Simplify then Prove)

   The following is a straightforward but quite helpful simplification
   procedure. It treats the rewrite rules for all declared datatypes as
   being built-in, so that the user does not have to mention them.

   0. Build a simpset from the given ss and the rewrites coming from
      any constructors that are found in TypeBase.

   1. Remove all universal quantifiers and break down all conjunctions

   2. Eliminate all "var-equalities" from the assumptions

   3. Simplify the goal with respect to the assumptions and the given
      simplification set.

   4. Case split on conditionals as much as possible.

   5. Strip as much as possible to the assumptions.

   6. Until there is no change in the complete goal, attempt to do one
      of the following:

         * eliminate a var-equality

         * break up an equation between constructors in the assumptions

         * break up an equation between constructors in the goal

         * break up conjunctions, disjunctions, existentials, or
           double negations occurring in the assumptions

         * eliminate occurrences of T (toss it away) and F (prove the goal)
           in the assumptions

         * eliminate lets in the goal, by lifting into the assumptions as
           abbreviations (using LET_ELIM_TAC)

    7. Apply the finishing tactic.

 ---------------------------------------------------------------------------*)

fun tyinfol() = TypeBasePure.listItems (TypeBase.theTypeBase());

fun mkCSET () =
 let val CSET = (HOLset.empty
                  (inv_img_cmp (fn {Thy,Name,Ty} => (Thy,Name))
                          (pair_compare(String.compare,String.compare))))
     fun add_const (c,CSET) = HOLset.add(CSET, dest_thy_const c)
     fun add_tyinfo (tyinfo,CSET) =
       List.foldl add_const CSET (TypeBasePure.constructors_of tyinfo)
     val CSET = List.foldl add_tyinfo CSET (tyinfol())
     fun inCSET t = HOLset.member(CSET, dest_thy_const t)
     fun constructed tm =
      let val (lhs,rhs) = dest_eq tm
      in aconv lhs rhs orelse
         let val maybe1 = fst(strip_comb lhs)
             val maybe2 = fst(strip_comb rhs)
         in is_const maybe1 andalso is_const maybe2
            andalso
            inCSET maybe1 andalso inCSET maybe2
         end
      end handle HOL_ERR _ => false
  in
    Lib.can (find_term constructed)
 end;

val leave_lets_var = mk_var("__leave_lets_alone__", bool)
val LEAVE_LETS = ASSUME leave_lets_var

fun PRIM_STP_TAC ss finisher =
 let val has_constr_eqn = mkCSET ()
     val ASM_SIMP = simpLib.ASM_SIMP_TAC ss []
     (* we don't have access to any theorem list that might have been passed
        to RW_TAC or SRW_TAC at this point, but we can look for the effect of
        the LEAVE_LETS theorem by attempting to rewrite something that only it
        should affect; if the simplifier doesn't change the leave_lets_var,
        then LEAVE_LETS is not part of the ss, so we should do LET_ELIM_TAC,
        otherwise, we shouldn't.

        Also, if there are no lets about then
        don't attempt LET_ELIM_TAC at all.  This is because LET_ELIM_TAC
        includes rewrites like |- f o (\x. g x) = \x. f (g x) and these
        can alter goals that don't have any lets in them at all, possibly
        against user expectations.  A less sledge-hammer implementation of
        LET_ELIM_TAC might not have this problem... *)
     val do_lets = (simpLib.SIMP_CONV ss [] leave_lets_var ; false)
                   handle Conv.UNCHANGED => true
     val LET_ELIM_TAC =
        if do_lets then
          (fn g as (_,w) =>
                if can (find_term is_let) w
                   then LET_ELIM_TAC g
                   else NO_TAC g)
        else NO_TAC
  in
    REPEAT (GEN_TAC ORELSE CONJ_TAC)
     THEN REPEAT VAR_EQ_TAC
     THEN ASM_SIMP
     THEN TRY (IF_CASES_TAC THEN REPEAT IF_CASES_TAC THEN ASM_SIMP)
     THEN REPEAT BOSS_STRIP_TAC
     THEN REPEAT (CHANGED_TAC
            (VAR_EQ_TAC
               ORELSE ASSUMS_TAC (LIFT_SIMP ss) has_constr_eqn
               ORELSE ASSUM_TAC (LIFT_SIMP ss) breakable
               ORELSE CONCL_TAC ASM_SIMP has_constr_eqn
               ORELSE LET_ELIM_TAC))
     THEN TRY finisher
  end

(*---------------------------------------------------------------------------
    PRIM_NORM_TAC: preliminary attempt at keeping the goal in a
    fully constructor-reduced format. The idea is that there should
    be no equations between constructor terms anywhere in the goal.
    (This is what PRIM_STP_TAC already does.)

    Also, no conditionals should occur in the resulting goal.
    This seems to be an expensive test, especially since the work
    in detecting the conditional is replicated in IF_CASES_TAC.

    Continuing in this light, it seems possible to eliminate all
    case expressions in the goal, but that hasn't been implemented yet.
 ---------------------------------------------------------------------------*)

fun splittable w =
 Lib.can (find_term (fn tm => (is_cond tm orelse TypeBase.is_case tm)
                              andalso free_in tm w)) w;

fun LIFT_SPLIT_SIMP ss simp tm =
   UNDISCH_THEN tm
     (fn th => MP_TAC (simpLib.SIMP_RULE ss [] th)
                 THEN CASE_TAC
                 THEN simp
                 THEN REPEAT BOSS_STRIP_TAC);

fun SPLIT_SIMP simp = TRY (IF_CASES_TAC ORELSE CASE_TAC) THEN simp ;

fun PRIM_NORM_TAC ss =
 let val has_constr_eqn = mkCSET()
     val ASM_SIMP = simpLib.ASM_SIMP_TAC ss []
  in
    REPEAT (GEN_TAC ORELSE CONJ_TAC)
     THEN REPEAT VAR_EQ_TAC
     THEN ASM_SIMP
     THEN TRY (IF_CASES_TAC THEN REPEAT IF_CASES_TAC THEN ASM_SIMP)
     THEN REPEAT BOSS_STRIP_TAC
     THEN REPEAT (CHANGED_TAC
            (VAR_EQ_TAC
               ORELSE ASSUMS_TAC (LIFT_SIMP ss) has_constr_eqn
               ORELSE ASSUM_TAC (LIFT_SIMP ss) breakable
               ORELSE CONCL_TAC ASM_SIMP has_constr_eqn
               ORELSE ASSUM_TAC (LIFT_SPLIT_SIMP ss ASM_SIMP) splittable
               ORELSE CONCL_TAC (SPLIT_SIMP ASM_SIMP) splittable
               ORELSE LET_ELIM_TAC))
  end


(*---------------------------------------------------------------------------
    Adding simplification sets in for all datatypes each time
    STP_TAC is invoked can be slow. In such cases, use
    PRIM_STP tac instead.
 ---------------------------------------------------------------------------*)

fun STP_TAC ss finisher
  = PRIM_STP_TAC (rev_itlist add_simpls (tyinfol()) ss) finisher

fun RW_TAC ss thl g = markerLib.ABBRS_THEN
                          (markerLib.mk_require_tac
                             (fn thl => STP_TAC (ss && thl) NO_TAC))
                          thl
                          g
val rw_tac = RW_TAC

fun NORM_TAC ss thl g =
    markerLib.ABBRS_THEN
      (fn thl => PRIM_NORM_TAC (rev_itlist add_simpls (tyinfol()) (ss && thl)))
      thl
      g

val bool_ss = boolSimps.bool_ss;

(*---------------------------------------------------------------------------
       Stateful version of RW_TAC: doesn't load the constructor
       simplifications into the simpset at each invocation, but
       just when a datatype is declared.
 ---------------------------------------------------------------------------*)

val (srw_ss : simpset ref) = ref (bool_ss ++ combinSimps.COMBIN_ss
                          ++ boolSimps.NORMEQ_ss);

val srw_ss_initialised = ref false;

datatype update = ADD_SSFRAG of simpLib.ssfrag | REMOVE_RWT of string
val pending_updates = ref ([]: update list);

fun apply_update (ADD_SSFRAG ssf, ss) = ss ++ ssf
  | apply_update (REMOVE_RWT n, ss) = ss -* [n]

fun initialise_srw_ss() =
  if !srw_ss_initialised then !srw_ss
  else let in
     HOL_PROGRESS_MESG ("Initialising SRW simpset ... ", "done")
     (fn () =>
         (srw_ss := rev_itlist add_simpls (tyinfol()) (!srw_ss) ;
          srw_ss := foldl apply_update (!srw_ss) (!pending_updates) ;
          srw_ss_initialised := true)) () ;
     !srw_ss
  end;

fun augment_srw_ss ssdl =
    if !srw_ss_initialised then
      srw_ss := foldl (fn (ssd,ss) => ss ++ ssd) (!srw_ss) ssdl
    else
      pending_updates := !pending_updates @ map ADD_SSFRAG ssdl;

fun diminish_srw_ss names =
    if !srw_ss_initialised then
      let
        val (frags, rest) = (!srw_ss) |> simpLib.ssfrags_of
                                      |> List.rev
                                      |> simpLib.partition_ssfrags names
        val _ = srw_ss := simpLib.mk_simpset rest
      in
        frags
      end
    else
      let
        open simpLib
        fun foldthis (upd, (keep,drop)) =
            case upd of
                ADD_SSFRAG ssf =>
                (case frag_name ssf of
                     NONE => (upd::keep,drop)
                   | SOME n => if mem n names then (keep,ssf::drop)
                               else (upd::keep,drop))
              | _ => (upd::keep, drop)
        val (keep, drop) = foldl foldthis ([], []) (!pending_updates)
        val _ = pending_updates := keep
      in
        drop
      end;

fun temp_delsimps names =
    if !srw_ss_initialised then
      srw_ss := ((!srw_ss) -* names)
    else
      pending_updates := !pending_updates @ map REMOVE_RWT names

fun update_fn tyi =
  augment_srw_ss ([simpLib.tyi_to_ssdata tyi] handle HOL_ERR _ => [])

val () =
  TypeBase.register_update_fn (fn tyinfos => (app update_fn tyinfos; tyinfos))

fun srw_ss () = initialise_srw_ss();

fun SRW_TAC ssdl thl g = let
  val ss = foldl (fn (ssd, ss) => ss ++ ssd) (srw_ss()) ssdl
in
  markerLib.ABBRS_THEN
    (markerLib.mk_require_tac (fn thl => PRIM_STP_TAC (ss && thl) NO_TAC)) thl
end g;
val srw_tac = SRW_TAC

val Abbr = markerSyntax.Abbr

(* ----------------------------------------------------------------------
    Make some additions to the srw_ss persistent
   ---------------------------------------------------------------------- *)

open LoadableThyData

(* store a database of per-theory simpset fragments *)
val thy_ssfrags = ref (Binarymap.mkDict String.compare)
fun thy_ssfrag s = Binarymap.find(!thy_ssfrags, s)

fun add_rewrites thyname (thms : (KernelSig.kernelname * thm) list) = let
  val ssfrag = simpLib.named_rewrites_with_names thyname thms
  open Binarymap
in
  augment_srw_ss [ssfrag];
  case peek(!thy_ssfrags, thyname) of
    NONE => thy_ssfrags := insert(!thy_ssfrags, thyname, ssfrag)
  | SOME sf' => let
      val sf = simpLib.named_merge_ss thyname [sf', ssfrag]
    in
      thy_ssfrags := insert(!thy_ssfrags, thyname, sf)
    end
end

val {export,delete} =
    ThmSetData.new_exporter {
      settype = "simp",
      efns = {
        add = fn {thy,named_thms} => add_rewrites thy named_thms,
        remove = fn {removes, ...} => temp_delsimps removes
      }
    }

fun export_rewrites slist = List.app export slist

fun delsimps names = List.app delete names

end
