structure SingleStep :> SingleStep =
struct

open HolKernel Parse boolLib pairSyntax PairedLambda;

infix THEN THENL ORELSE |-> ##;   infixr -->;

val ERR = mk_HOL_ERR "SingleStep";

fun name_eq s M = ((s = fst(dest_var M)) handle HOL_ERR _ => false)

fun tm_free_eq M N P = 
  (aconv N P andalso free_in N M) orelse raise ERR "tm_free_eq" ""

(*---------------------------------------------------------------------------*
 * Mildly altered STRUCT_CASES_TAC, so that it does a SUBST_ALL_TAC instead  *
 * of a SUBST1_TAC.                                                          *
 *---------------------------------------------------------------------------*)

val VAR_INTRO_TAC = REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC;

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
         val theta = gather (fn (v,_) => mem v tofree) Vmap
         val rebind = map snd (gather (fn (v,_) => not (mem v tofree)) Vmap)
     in
       ((MAP_EVERY X_GEN_TAC (map snd Vmap)
          THEN MAP_EVERY ID_SPEC_TAC (rev rebind)),
        subst (map op|-> theta) M)
     end;

(*---------------------------------------------------------------------------*
 * Do case analysis on given term. The quotation is parsed into a term M that*
 * must match a subterm in the goal (or the assumptions). If M is a variable,*
 * then the match of the names must be exact. Once the term to split over is *
 * known, its type and the associated facts are obtained and used to do the  *
 * split with. Variables of M might be quantified in the goal. If so, we try *
 * to unquantify the goal so that the case split has meaning.                *
 *                                                                           *
 * It can happen that the given term is not found anywhere in the goal. If   *
 * the term is boolean, we do a case-split on whether it is true or false.   *
 *---------------------------------------------------------------------------*)

datatype category 
    = Free of term
    | Bound of term list * term  (* in Bound(V,M), V = vars to be freed up *)
    | Alien of term;

fun cat_tyof (Free M)      = type_of M
  | cat_tyof (Bound (_,M)) = type_of M
  | cat_tyof (Alien M)     = type_of M

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
 else Free (tryfind(fn x => find_term (can(tm_free_eq x tm)) x) (w::asl))
      handle HOL_ERR _
      => Bound(let val (V,body) = strip_forall w
                   val M = find_term (can (tm_free_eq body tm)) body
               in (intersect (free_vars M) V, M)
               end)
      handle HOL_ERR _ 
      => Alien tm;

fun find_subterm qtm (g as (asl,w)) =
  let val FVs = free_varsl (w::asl)
      val tm = parse_in_context FVs qtm
  in
    prim_find_subterm FVs tm g
  end;


fun primCases_on st (g as (_,w)) =
 let val ty = cat_tyof st
     val (Tyop,_) = dest_type ty
 in case TypeBase.read Tyop
     of SOME facts =>
        let val thm = TypeBasePure.nchotomy_of facts
        in case st
           of Free M =>
               if (is_var M) then VAR_INTRO_TAC (ISPEC M thm) g else
               if ty=bool then ASM_CASES_TAC M g
               else TERM_INTRO_TAC (ISPEC M thm) g
            | Bound(V,M) => let val (tac,M') = FREEUP V M g
                            in (tac THEN VAR_INTRO_TAC (ISPEC M' thm)) g end
            | Alien M    => if ty=bool then ASM_CASES_TAC M g
                            else TERM_INTRO_TAC (ISPEC M thm) g
        end
      | NONE => raise ERR "primCases_on"
                   ("No cases theorem found for type: "^Lib.quote Tyop)
 end

fun Cases_on qtm g = primCases_on (find_subterm qtm g) g
  handle e => raise wrap_exn "SingleStep" "Cases_on" e;

fun Cases (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases" "not a forall")
  in primCases_on (Bound([Bvar],Bvar)) g
  end
  handle e => raise wrap_exn "SingleStep" "Cases" e;

fun primInduct st ind_tac (g as (asl,c)) =
 let fun ind_non_var V M =
       let val (tac,M') = FREEUP V M g
           val Mfrees = free_vars M'
           fun has_vars tm = not(null_intersection (free_vars tm) Mfrees)
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

val is_mutind_thm = is_conj o snd o strip_imp o snd o strip_forall o concl;

fun induct_on_type st ty =
 let val (Tyop,_) = with_exn dest_type ty (ERR "induct_on_type"
                     "No induction theorems available for variable types")
 in case TypeBase.read Tyop
     of SOME facts =>
        let val thm = TypeBasePure.induction_of facts
        in if is_mutind_thm thm
              then Mutual.MUTUAL_INDUCT_TAC thm
              else primInduct st (Prim_rec.INDUCT_THEN thm ASSUME_TAC)
        end
      | NONE => raise ERR "induct_on_type"
                    ("No induction theorem found for type: "^Lib.quote Tyop)
 end

fun Induct_on qtm g =
 let val st = find_subterm qtm g
 in induct_on_type st (cat_tyof st) g
 end
 handle e => raise wrap_exn "SingleStep" "Induct_on" e


fun grab_var M =
  if is_forall M then fst(dest_forall M) else
  if is_conj M then fst(dest_forall(fst(dest_conj M)))
  else raise ERR "Induct" "expected a forall or a conjunction of foralls";

fun Induct (g as (_,w)) =
 let val v = grab_var w
     val (_,ty) = dest_var (grab_var w)
 in induct_on_type (Bound([v],v)) ty g
 end
 handle e => raise wrap_exn "SingleStep" "Induct" e

fun completeInduct_on qtm g =
 let val st = find_subterm qtm g
     val ind_tac = Prim_rec.INDUCT_THEN
                     arithmeticTheory.COMPLETE_INDUCTION ASSUME_TAC
 in
     primInduct st ind_tac g
 end
 handle e => raise wrap_exn "SingleStep" "completeInduct_on" e


(*---------------------------------------------------------------------------
    Invoked e.g. measureInduct_on `LENGTH L` or
                 measureInduct_on `(\(x,w). x+w) (M,N)`
 ---------------------------------------------------------------------------*)

local open relationTheory prim_recTheory
      val mvar = mk_var("m", alpha --> numSyntax.num)
      val measure_tm = prim_mk_const{Name="measure",Thy="prim_rec"}
      val measure_m = mk_comb(measure_tm,mvar)
      val ind_thm0 = GEN mvar
          (BETA_RULE
             (REWRITE_RULE[WF_measure,measure_def,inv_image_def]
                 (MATCH_MP (SPEC measure_m WF_INDUCTION_THM)
                         (SPEC_ALL WF_measure))))
in
fun measureInduct_on q (g as (asl,w)) =
 let val FVs = free_varsl (w::asl)
     val tm = parse_in_context FVs q
     val (meas, arg) = dest_comb tm
     val (d,r) = dom_rng (type_of meas)  (* r should be num *)
     val st = prim_find_subterm FVs arg g
     val st_type = cat_tyof st
     val meas' = inst (match_type d st_type) meas
     val ind_thm1 = INST_TYPE [Type.alpha |-> st_type] ind_thm0
     val ind_thm2 = GEN_BETA_RULE (SPEC meas' ind_thm1)
     val ind_tac = Prim_rec.INDUCT_THEN ind_thm2 ASSUME_TAC
 in
     primInduct st ind_tac g
 end
 handle e => raise wrap_exn "SingleStep" "measureInduct_on" e
end


(*---------------------------------------------------------------------------
         Recursion induction tactic. Taken from tflLib.
 ---------------------------------------------------------------------------*)


fun mk_vstrl [] V A = rev A
  | mk_vstrl (ty::rst) V A =
      let val (vstr,V1) = unstrip_pair ty V
      in mk_vstrl rst V1 (vstr::A)
      end;

fun recInduct thm =
  let val (prop,Body) = dest_forall(concl thm)
      val parg_tyl = #1(strip_fun (type_of prop))
      val n = (length o #1 o strip_forall o #2 o strip_imp) Body
      fun ndest_forall trm =
          let fun dest (0,tm,V) = (rev V,tm)
                | dest (n,tm,V) =
                    let val (Bvar,Body) = dest_forall tm
                    in dest(n-1,Body, Bvar::V) end
          in dest(n,trm,[])
          end
      fun tac (asl,w) =
       let val (V,body) = ndest_forall w
(*           val P = list_mk_pabs(mk_vstrl parg_tyl V [],body) *)
           val P = list_mk_abs(V,body)
           val thm' = GEN_BETA_RULE (ISPEC P thm)
       in MATCH_MP_TAC thm' (asl,w)
       end
  in tac
  end
  handle e => raise wrap_exn "SingleStep" "recInduct" e


(*---------------------------------------------------------------------------*
 * A simple aid to reasoning by contradiction.                               *
 *---------------------------------------------------------------------------*)

fun SPOSE_NOT_THEN ttac =
  CCONTR_TAC THEN
  POP_ASSUM (fn th => ttac (simpLib.SIMP_RULE boolSimps.bool_ss [] th))

(*---------------------------------------------------------------------------
     Assertional style reasoning
 ---------------------------------------------------------------------------*)

infix 8 by;
infix on

fun (q by tac) (g as (asl,w)) =
  let val tm = parse_in_context (free_varsl (w::asl)) q
  in Tactic.via(tm,tac) g
  end
  handle e => raise (wrap_exn "SingleStep" "by" e);

fun chop_at n frontacc l =
  if n <= 0 then (List.rev frontacc, l)
  else
    case l of
      [] => raise Fail "chop_at"
    | (h::t) => chop_at (n - 1) (h::frontacc) t

infix THEN1
fun ((tac1:tactic) THEN1 (tac2:tactic)) (asl:term list,w:term) = let
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

infix on
fun ((ttac:thm->tactic) on (q:term frag list, tac:tactic)) : tactic =
  (fn (g as (asl:term list, w:term)) => let
    val tm = parse_in_context (free_varsl (w::asl)) q
  in
    (SUBGOAL_THEN tm ttac THEN1 tac) g
  end)


end;
