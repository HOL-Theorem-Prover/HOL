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
            handle HOL_ERR _ =>
                   raise ERR "find_subterm"
                         ("No var with name \"" ^ name ^
                          "\" free in goal, or in outer universal quantifiers")
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
    strip_binop dest_prod
 end

fun mk_prod(ty1,ty2) = mk_thy_type{Thy="pair",Tyop="prod",Args=[ty1,ty2]}

fun mk_pair (t1,t2) =
    let
      val pair_const = prim_mk_const {Name=",",Thy="pair"}
      val pair_const' =
          inst [alpha |-> type_of t1, beta |-> type_of t2] pair_const
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
          case dest_thy_type ty of
              {Thy="pair",Tyop="prod",Args=[ty1,ty2]} =>
                ty::tmpvar_types (n-1) ty2
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
                clause (* fail in such a way that tactic can still be applied.*)
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
    let
      val ty = type_of (dest_tmkind st)
      fun gen() =
          case TypeBase.fetch ty of
              SOME facts => [TypeBasePure.nchotomy_of facts]
            | NONE => let val {Thy,Tyop,...} = dest_thy_type ty
                      in
                        raise ERR "primCases_on"
                              ("No cases theorem found for type: "^
                               Lib.quote (Thy^"$"^Tyop))
                      end
      fun ttac thm =
          let
            val thm' = set_names names ty thm
          in
            case st of
                Free M =>
                if is_var M then VAR_INTRO_TAC (ISPEC M thm') else
                if ty=bool then ASM_CASES_TAC M
                else TERM_INTRO_TAC (ISPEC M thm')
              | Bound(V,M) => let val (tac,M') = FREEUP V M g
                                  in (tac THEN VAR_INTRO_TAC (ISPEC M' thm'))
                              end
              | Alien M    => if ty=bool then ASM_CASES_TAC M
                              else TERM_INTRO_TAC (ISPEC M thm')
          end
    in
      markerLib.maybe_using gen ttac g
    end

fun Cases_on qtm g = primCases_on [] (find_subterm qtm g) g
  handle e => raise wrap_exn "BasicProvers" "Cases_on" e;

fun tmCases_on tm names (g as (asl,w)) =
    let
      val fvs = FVL (w::asl) empty_tmset |> HOLset.listItems
    in
      primCases_on names (prim_find_subterm fvs tm g) g
    end handle e => raise wrap_exn "BasicProvers" "tmCases_on" e;

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
    let
      val is_mutind_thm = is_conj o snd o strip_imp o snd o
                          strip_forall o concl
      val facts_opt = TypeBase.fetch ty
      fun gen() =
          case facts_opt of
              SOME facts =>
              let
              in
                case total TypeBasePure.induction_of facts of
                    NONE =>
                    raise ERR "induct_on_type"
                          (String.concat ["Type :",Hol_pp.type_to_string ty,
                                          " is registered in the types \
                                          \database, but there is no associated\
                                          \induction theorem"])
                  | SOME thm => (* now select induction tactic *) [thm]
              end
            | NONE =>
              raise ERR "induct_on_type"
                    (String.concat ["Type: ",Hol_pp.type_to_string ty,
                                    " is not registered in the types database"])
      fun ttac thm =
          case Option.map TypeBasePure.constructors_of facts_opt of
              SOME [] => (* not a datatype*) primInduct st (HO_MATCH_MP_TAC thm)
            | _ => if is_mutind_thm thm then
                     Mutual.MUTUAL_INDUCT_TAC thm
                   else
                     primInduct st (Prim_rec.INDUCT_THEN thm ASSUME_TAC) ORELSE
                     (primInduct st (HO_MATCH_MP_TAC thm) THEN REPEAT CONJ_TAC)
    in
      maybe_using gen ttac g
    end

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
            fun indths() =
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
            markerLib.maybe_using indths tryind ORELSE induct_on_type st ty
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


(* deliberately masking what is in TypeBase as we may instead update
   something stored for an inductive relation *)
fun update_induction th =
    let
      val (_, body) = strip_forall $ concl $ th
      val (_, c) = strip_imp body
      val cs = strip_conj c (* possibility of mutual recursion *)
      fun looks_typeish c =
          let val (cvs, cbody) = strip_forall c
          in
            length cvs = 1 andalso is_var (rator cbody)
          end handle HOL_ERR _ => false
    in
      if List.all looks_typeish cs then TypeBase.update_induction th
      else IndDefLib.add_rule_induction th
    end

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


val var_eq = Tactic.eliminable
fun ASSUM_TAC f P = first_x_assum (f o assert (P o concl))

val old_behaviour = ref false
val tracename = "BasicProvers.var_eq_old"
val _ = Feedback.register_btrace(tracename, old_behaviour)
val behaviour_value = get_tracefn tracename
fun VAR_EQ_TAC (g as (asl,_)) =
    let
      val tidy = if behaviour_value() = 1 then ALL_TAC
                 else markerLib.TIDY_ABBREVS
    in
      (ASSUM_TAC VSUBST_TAC var_eq THEN tidy) g
    end
val var_eq_tac = VAR_EQ_TAC

fun ASSUMS_TAC f P = W (fn (asl,_) =>
  case filter P asl
   of []     => NO_TAC
    | assums => MAP_EVERY (fn t => UNDISCH_THEN t f) (List.rev assums))

fun CONCL_TAC f P = W (fn (_,c) => if P c then f else NO_TAC);

fun LIFT_SIMP ss = STRIP_ASSUME_TAC o simpLib.SIMP_RULE ss []

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

fun LIFT_SPLIT_SIMP ss simp th =
    MP_TAC (simpLib.SIMP_RULE ss [] th) THEN CASE_TAC THEN simp THEN
    REPEAT BOSS_STRIP_TAC

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

datatype srw_update = ADD_SSFRAG of simpLib.ssfrag | REMOVE_RWT of string
type srw_state = simpset * bool * srw_update list
  (* simpset, initialised-flag, update list (most recent first) *)

val initial_simpset = bool_ss ++ combinSimps.COMBIN_ss
                              ++ boolSimps.NORMEQ_ss
                              ++ boolSimps.ABBREV_ss
                              ++ boolSimps.LABEL_CONG_ss
                              ++ boolSimps.HIDE_ss

fun ssf1 nth = simpLib.empty_ssfrag |> simpLib.add_named_rwt nth

val state0 : srw_state = (initial_simpset, false, [])
fun apply_delta d ((sset,initp,upds):srw_state) : srw_state =
    case d of
        ThmSetData.ADD nth =>
        (sset ++ ssf1 nth, true, [])
      | ThmSetData.REMOVE s => (sset -* [s], true, [])

fun apply_srw_update (ADD_SSFRAG ssf, ss) = ss ++ ssf
  | apply_srw_update (REMOVE_RWT n, ss) = ss -* [n]

fun init_state (st as (sset,initp,upds)) =
    if initp then st
    else
      let fun init() =
              (List.foldl apply_srw_update sset (List.rev upds)
                          |> rev_itlist add_simpls (tyinfol()),
               true, [])
      in
        HOL_PROGRESS_MESG ("Initialising SRW simpset ... ", "done") init ()
      end
fun opt_partition f g ls =
    let
      fun recurse As Bs ls =
          case ls of
              [] => (List.rev As, List.rev Bs)
            | h::t => (case f h of
                           SOME a => recurse (a::As) Bs t
                         | NONE => (case g h of
                                        SOME b => recurse As (b::Bs) t
                                     | NONE => recurse As Bs t))
    in
      recurse [] [] ls
    end

(* stale-ness is important for derived values. Derived values will get
   re-calculated if their flag is true when the value is requested.
*)
val stale_flags = Sref.new ([] : bool Sref.t list)
fun notify () =
    List.app (fn br => Sref.update br (K true)) (Sref.value stale_flags)

fun apply_to_global d (st as (sset,initp,upds):srw_state) : srw_state =
    if not initp then
      case d of
          ThmSetData.ADD nth =>
          let
            open simpLib
            val upds' =
                case upds of
                    ADD_SSFRAG ssf :: rest =>
                    ADD_SSFRAG (add_named_rwt nth ssf) :: rest
                  | _ => ADD_SSFRAG (ssf1 nth) :: upds
          in
            (sset, initp, upds')
          end
        | ThmSetData.REMOVE s => (sset, initp, REMOVE_RWT s :: upds)
    else
      apply_delta d st before notify()

fun finaliser {thyname} deltas (sset,initp,upds) =
    let
      fun toNamedAdd (ThmSetData.ADD p) = SOME p | toNamedAdd _ = NONE
      fun toRM (ThmSetData.REMOVE s) = SOME s | toRM _ = NONE
      val (adds,rms) = opt_partition toNamedAdd toRM deltas
      val ssfrag = simpLib.named_rewrites_with_names thyname (List.rev adds)
        (* List.rev here preserves old behaviour wrt to the way theorems were
           added to the global simpset; it will only make a difference when
           overall rewrite system is not confluent *)
      val new_upds = ADD_SSFRAG ssfrag :: map REMOVE_RWT rms
    in
      if initp then
        (List.foldl apply_srw_update sset new_upds, true, []) before notify()
      else (sset, false, List.revAppend(new_upds, upds))
    end

val adresult as {DB,get_global_value,record_delta,update_global_value,...} =
    ThmSetData.export_with_ancestry {
      delta_ops = {
        apply_delta = apply_delta,
        apply_to_global = apply_to_global,
        thy_finaliser = SOME finaliser,
        initial_value = state0, uptodate_delta = K true
      },
      settype = "simp"
    };
fun updnote_global_value f = (update_global_value f; notify())
val get_deltas = #get_deltas adresult
fun merge_simpsets ps =
    case Option.map (#1 o quiet_messages init_state) (#merge adresult ps) of
        NONE => simpLib.empty_ss
      | SOME sset => sset

fun augment_srw_ss0 ssdl ((sset, initp, upds):srw_state):srw_state =
    if initp then (foldl (fn (ssd,ss) => ss ++ ssd) sset ssdl, true, [])
    else
      (sset, false, List.revAppend(map ADD_SSFRAG ssdl, upds))

val augment_srw_ss = updnote_global_value o augment_srw_ss0

fun diminish_srw_ss0 names st0 =
    let val st' as (sset, _, _) = init_state st0
    in
      (simpLib.remove_ssfrags names sset, true, [])
    end
val diminish_srw_ss = updnote_global_value o diminish_srw_ss0

fun temp_delsimps0 names (sset, initp, upds) =
    if initp then (sset -* names, true, [])
    else
      (sset, false, List.revAppend (map REMOVE_RWT names, upds))
val temp_delsimps = updnote_global_value o temp_delsimps0;

fun tyi_update tyi sset = sset ++ simpLib.tyi_to_ssdata tyi
fun update_fn tyi =
  augment_srw_ss ([simpLib.tyi_to_ssdata tyi] handle HOL_ERR _ => [])
fun augment_with_typebase tyb =
    rev_itlist tyi_update $ TypeBasePure.listItems tyb

val () = TypeBase.register_update_fn (fn tyi => (update_fn tyi; tyi))

fun srw_ss () =
    (update_global_value init_state;
     #1 (get_global_value()))

fun with_simpset_updates f g x =
    (notify();
     AncestryData.with_temp_value adresult (f (srw_ss()), true, []) g x)

val update_log =
    Sref.new (Symtab.empty : (simpset -> simpset) list Symtab.table)
fun ap13 f (x,y,z) = (f x, y, z)
fun logged_update {thyname} f =
    (updnote_global_value (ap13 f);
     Sref.update update_log (Symtab.cons_list (thyname,f)))

fun logged_addfrags thy fgs =
    List.app (fn f => logged_update thy (fn s => s ++ f)) fgs

fun apply_logged_updates {theories} simpset =
    let
      open Binaryset
      val allancs = List.foldl
                      (fn (thy,s) => addList (add(s,thy), ancestry thy))
                      (empty String.compare)
                      theories
      val G = SymGraph.make (map (fn s => ((s,()), Theory.parents s))
                                 (Binaryset.listItems allancs))
      val sorted_thys = List.rev (SymGraph.topological_order G)
      fun app1 thy simpset =
          case Symtab.lookup (Sref.value update_log) thy of
              NONE => simpset
            | SOME fs => List.foldr (fn (f,ss) => f ss) simpset fs
    in
      rev_itlist app1 sorted_thys simpset
    end

fun do_logged_updates thys =
    updnote_global_value (ap13 (apply_logged_updates thys) o init_state)

fun option_fold f NONE x = x
  | option_fold f (SOME a) x = f a x

fun PRIM_SRW_TAC ss0 ssdl thl g =
    let
      val ss = foldl (fn (ssd,ss) => ss ++ ssd) ss0 ssdl
    in
      markerLib.ABBRS_THEN
        (markerLib.mk_require_tac (fn thl => PRIM_STP_TAC (ss && thl) NO_TAC))
        thl
    end g;
fun SRW_TAC ssdl thms g =
    PRIM_SRW_TAC (srw_ss()) ssdl thms g (* don't eta-reduce *)
val srw_tac = SRW_TAC

fun export_rewrites slist =
    let val ds = map ThmSetData.mk_add slist
    in
      List.app record_delta ds;
      update_global_value (rev_itlist apply_to_global ds)
    end

fun delsimps names =
    (List.app (record_delta o ThmSetData.REMOVE) names;
     temp_delsimps names)

(* assume that there aren't any removes for things added in this theory;
   it's not rational to do that; one should add it locally only, or not
   add it at all
*)
fun mkfrag_from thy setdeltas =
    let fun recurse ADDs [] = ADDs
          | recurse ADDs (ThmSetData.ADD p :: rest) = recurse (p::ADDs) rest
          | recurse ADDs (_ :: rest) = recurse ADDs rest
        val ADDs = recurse [] setdeltas
          (* order of addition is flipped; see above for why this is
             "reasonable" *)
    in
      simpLib.named_rewrites_with_names thy ADDs
    end
fun thy_ssfrag s = get_deltas {thyname=s} |> mkfrag_from s

fun thy_simpset s = Option.map (#1 o init_state) (DB {thyname=s})

fun temp_set_simpset_ancestry sl =
    case #merge adresult sl of
        NONE => HOL_WARNING "BasicProvers" "temp_set_simpset_ancestry"
                            "Merge of parental values produces no value; \
                            \nothing done"
      | SOME v => updnote_global_value (K v)

fun set_simpset_ancestry sl =
    case #set_parents adresult sl of
        NONE => HOL_WARNING "BasicProvers" "set_simpset_ancestry"
                            "Merge of parental values produces no value; \
                            \nothing done"
      | SOME _ => notify()

fun temp_setsimpset ss = updnote_global_value (K (ss, true, []))
val simpset_state = get_global_value
fun recreate_sset_at_parentage ps =
    ps |> merge_simpsets
       |> option_fold augment_with_typebase (TypeBase.merge_typebases ps)
       |> apply_logged_updates {theories = ps}
       |> temp_setsimpset


fun make_simpset_derived_value (deriver : simpset -> 'a -> 'a) init =
    let
      val _ = update_global_value init_state
      val vref = Sref.new (deriver (srw_ss()) init)
      val stale_flag = Sref.new false
      val _ = Sref.update stale_flags (cons stale_flag)
      fun get() =
          (if Sref.value stale_flag then
             (Sref.update vref (deriver (srw_ss()));
              Sref.update stale_flag (K false))
           else ();
           Sref.value vref)
      fun set v = (Sref.update vref (K v); Sref.update stale_flag (K false))
    in
      {get=get,set=set}
    end

fun mk_tacmod s =
    let
      open AttributeSyntax
      val (_, attrs0) = dest_name_attrs s
      val alist = key_vallist attrs0
      fun key_to_f k =
          case k of
              "exclude_simps" => simpLib.remove_simps
            | "exclude_frags" => simpLib.remove_ssfrags
            | _ => (fn vs => fn ss => ss)
      val f =
          gen_mktm { values = (fn vs => vs),
                     combine = (fn (f1,f2) => f1 o f2),
                     null = (fn x => x),
                     perkey = (fn k => fn vs => key_to_f k vs) }
                   alist
    in
      {tacm = with_simpset_updates f, ltacm = with_simpset_updates f}
    end

end
