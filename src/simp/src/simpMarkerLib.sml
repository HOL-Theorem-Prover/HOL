structure simpMarkerLib :> simpMarkerLib =
struct
open HolKernel boolLib markerLib markerSyntax
val ERR = mk_HOL_ERR "simpMarkerLib"
val Split_tm = prim_mk_const {Thy="simpMarker",Name="Split"}
val ExclX_tm = prim_mk_const {Thy="simpMarker",Name="ExcludeX"}
val IgnAsm_tm = prim_mk_const {Thy="marker",Name="IgnAsm"}
fun Split th = EQ_MP (SYM (SPEC (concl th) simpMarkerTheory.Split_def)) th
fun destSplit th = PURE_REWRITE_RULE [simpMarkerTheory.Split_def] th
fun ExclX name =
  EQT_ELIM (SPEC (mk_var (name,alpha)) simpMarkerTheory.ExcludeX_def)
fun destExclX th =
  (if same_const ExclX_tm (rator (concl th)) then
    SOME (#1 (dest_var (rand (concl th))))
  else NONE)
  handle HOL_ERR _ => NONE

datatype directive =
    Legacy of markerLib.directive | DSplit of thm | DExclX of string
fun dest_directive th =
  case markerLib.dest_directive th of
      SOME d => SOME (Legacy d)
    | NONE =>
        if (same_const Split_tm (#1 (strip_comb (concl th)))
            handle HOL_ERR _ => false) then SOME (DSplit (destSplit th))
        else Option.map DExclX (destExclX th)
val is_directive = Option.isSome o dest_directive
fun strip_wrappers th =
  case markerLib.dest_directive th of
      SOME (DReq0 p) => strip_wrappers p
    | SOME (DReqD p) => strip_wrappers p
    | SOME (DBounded (p,_)) => strip_wrappers p
    | _ => th

fun req0_modify tacf th =
  case dest_Req0 th of NONE => (tacf,th)
    | SOME th => (Ho_Rewrite.REQUIRE0_TAC th o tacf, th)
fun reqD_modify tacf th =
  case dest_ReqD th of NONE => (tacf,th)
    | SOME th => (Ho_Rewrite.REQUIRE_DECREASE_TAC th o tacf, th)

fun require_split thl =
    let
      fun recurse (accths,acctacf) ths =
          case ths of
              [] => (List.rev accths, acctacf)
            | th::rest =>
              let
                val (tacf,th) = req0_modify acctacf th
                val (tacf,th) = reqD_modify tacf th
              in
                recurse (th::accths,tacf) rest
              end
    in
      recurse ([], I) thl
    end

datatype tacoptions = TO_NoAsms | TO_IgnAsm of string |
                      TO_Abbr of string | TO_Label of string |
                      TO_thm of thm
datatype aslP = AP_NoAsms | AP_Ign of string

fun dest_tacmarked th =
    case dest_directive th of
        SOME (Legacy DNoAsms) => TO_NoAsms
      | SOME (Legacy (DIgnAsm s)) => TO_IgnAsm s
      | SOME (Legacy (DAbbr s)) => TO_Abbr s
      | SOME (Legacy (DLabel s)) => TO_Label s
      | _ => TO_thm th

(* Option wrappers live in hypotheses, so option heads can be classified
   without decoding/constructing their payload proofs a second time. *)
fun dest_bound_tacmarked th =
    case dest_tacmarked th of
        TO_thm _ =>
          if aconv (concl th) (concl NoAsms) then TO_NoAsms
          else if same_const IgnAsm_tm (#1 (strip_comb (concl th))) then
            TO_IgnAsm (#1 (dest_var (rand (concl th))))
          else if is_abbr th then TO_Abbr (dest_abbr th)
          else (case total dest_label_ref th of
                    SOME s => TO_Label s | NONE => TO_thm th)
      | option => option

fun optcons NONE l = l
  | optcons (SOME x) xs = x::xs

fun matching_asm lnm t =
    (#1 (dest_label t) = lnm) handle HOL_ERR _ => false

fun process_tacoption to asl =
    case to of
        TO_thm th => (NONE, NONE, SOME th)
      | TO_NoAsms => (NONE, SOME AP_NoAsms, NONE)
      | TO_IgnAsm s => (NONE, SOME (AP_Ign s), NONE)
      | TO_Abbr s => (SOME (UNABBREV_TAC s), NONE, NONE)
      | TO_Label s => (NONE, NONE,
                       case List.find (matching_asm s) asl of
                           NONE => raise ERR "process_taclist"
                                         ("No assumption with label "^s)
                         | SOME t => SOME (DEST_LABEL (ASSUME t)))

fun asl_match ctxt s =
    let
      val q0 = [QUOTE s]
      val (q, comment_opt) = apsnd (Option.map Portable.remove_wspace)
                                   (HOLquotation.dest_last_comment q0)
      val pat = Parse.parse_in_context ctxt q
      val ctxt_s = HOLset.fromList Term.compare ctxt
      fun basematch t = Term.raw_match [] ctxt_s pat t ([],[])
    in
      case comment_opt of
          NONE => can basematch
        | SOME "sa" => can (find_term (can basematch))
        | SOME s => can basematch
    end

fun apply_aslPs ctxt aps asl =
    case aps of
        [] => asl
      | (AP_NoAsms :: _) => []
      | (AP_Ign s :: rest) =>
        apply_aslPs ctxt rest (List.filter (not o asl_match ctxt s) asl)

fun process_tacoptions tos asl pretacs aslPs asms =
    case tos of
        [] => {pre = EVERY (List.rev pretacs), asms = List.rev asms,
               aslPs = aslPs}
      | to::rest =>
        let val (tac_opt, aslP_opt, asm_opt) = process_tacoption to asl
        in
          process_tacoptions rest asl
                             (optcons tac_opt pretacs)
                             (optcons aslP_opt aslPs)
                             (optcons asm_opt asms)
        end

fun filter_then asms aslPs thltac (gl as (asl0,g)) =
    let
      val asl = apply_aslPs (free_varsl (g::asl0)) aslPs
                            (filter (not o is_label) asl0)
    in
      thltac (map ASSUME asl @ asms) gl
    end

(* Decode markers and run pretactics once.  The callback's [recur] closure
   reapplies only the saved assumption policy to a later subgoal.  The
   Req0/ReqD stripping is done here rather than by mk_require_tac inside
   filter_then, because [recur] must hand the later subgoal the stripped
   theorems too: they are the same theorems, and one that still carried
   its marker would take the marker$ hypothesis into the recursive pass's
   justification. *)
fun process_taclist_then_recur {arg} thltac (gl as (asl,g)) =
    let
      val tacoptions = map dest_tacmarked arg
      val {pre,asms,aslPs} = process_tacoptions tacoptions asl [] [] []
      val (asms, require_tacf) = require_split asms
      fun recur (next : thm list -> tactic) : tactic =
        filter_then asms aslPs next
    in
      Tactical.THEN
        (pre, require_tacf (filter_then asms aslPs (thltac recur))) gl
    end

(* Bind supplied rules separately from the changing assumption context.
   Requirements and pretactics run once; only assumption selection recurs.
   Bounds on tactic options qualify the option, not a rewrite allowance. *)
fun process_taclist_then_bind {arg} thltac (gl as (asl,g)) =
    let
      val tacoptions = map dest_bound_tacmarked arg
      val {pre,asms,aslPs} = process_tacoptions tacoptions asl [] [] []
      (* Resolve labels before building requirements, but retain checks on
         options too: classifying NoAsms must not discard its ReqD. *)
      val (_, require_tacf) = require_split arg
      fun plain th =
        let val th = case dest_Req0 th of SOME p => p | NONE => th
        in case dest_ReqD th of SOME p => p | NONE => th end
      val asms = map plain asms
      fun recur next = filter_then [] aslPs next
    in
      (* Construct the bound continuation after [pre] succeeds, not while
         composing THEN. In particular a failing Abbr must precede FRAG
         lookup and any rule-compilation callbacks in [thltac]. *)
      Tactical.THEN
        (pre, require_tacf (fn goal => recur (thltac asms recur) goal)) gl
    end

end
