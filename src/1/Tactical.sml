(* ===================================================================== *)
(* FILE          : Tactical.sml                                          *)
(* DESCRIPTION   : Functions that glue tactics together. From LCF, and   *)
(*                 added to through the years. Translated from hol88.    *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* Updated       : 1997 (to treat validity checking as an oracle) (KLS)  *)
(* ===================================================================== *)

structure Tactical :> Tactical =
struct

open Feedback HolKernel Drule boolSyntax Abbrev;

val ERR = mk_HOL_ERR "Tactical"

fun empty th [] = th
  | empty th _ = raise ERR "empty" "Bind Error"

(*---------------------------------------------------------------------------
 * TAC_PROOF (g,tac) uses tac to prove the goal g. An alpha conversion
 * step needs to be done if the proof returns a theorem that is
 * alpha-equivalent but not equal to the goal. To be really precise,
 * we should do this check in the hypotheses of the goal as well.
 *---------------------------------------------------------------------------*)

local
   val unsolved_list = ref ([]: goal list)
in
   fun unsolved () = !unsolved_list
   fun TAC_PROOF (g, tac) =
      case tac g of
         ([], p) =>
             (let
                 val thm = p []
                 val c = concl thm
                 val () = unsolved_list := []
              in
                 if c = snd g then thm else EQ_MP (ALPHA c (snd g)) thm
              end
              handle e => raise ERR "TAC_PROOF" "Can't alpha convert")
       | (l, _) => (unsolved_list := l; raise ERR "TAC_PROOF" "unsolved goals")
end

fun default_prover (t, tac) = TAC_PROOF (([], t), tac)

local
   val mesg = Lib.with_flag (Feedback.MESG_to_string, Lib.I) Feedback.HOL_MESG
   fun provide_feedback f (t, tac: tactic) =
      f (t, tac)
      handle (e as HOL_ERR {message = m, origin_function = f, ...}) =>
           (mesg ("Proof of \n\n" ^ Parse.term_to_string t ^ "\n\nfailed.\n")
            ; (case (m, f, unsolved ()) of
                  ("unsolved goals", "TAC_PROOF", (_, u)::_) =>
                      if Term.term_eq u t
                         then ()
                      else mesg ("First unsolved sub-goal is\n\n" ^
                                 Parse.term_to_string u ^ "\n\n")
                | _ => ())
            ; raise e)
   val internal_prover =
      ref (provide_feedback default_prover: Term.term * tactic -> Thm.thm)
in
   fun set_prover f = internal_prover := provide_feedback f
   fun restore_prover () = set_prover default_prover
   fun prove (t, tac) = !internal_prover (t, tac)
end

fun store_thm (name, tm, tac) =
   Theory.save_thm (name, prove (tm, tac))
   handle e =>
     (print ("Failed to prove theorem " ^ name ^ ".\n");
      Raise e)

(*---------------------------------------------------------------------------
 * tac1 THEN_LT ltac2:
 * A tactical that applies ltac2 to the list of subgoals resulting from tac1
 * tac1 may be a tactic or a list_tactic
 *---------------------------------------------------------------------------*)
fun op THEN_LT (tac1, ltac2 : list_tactic) =
   fn g =>
      let
         val (gl1, vf1) = tac1 g
         val (gl2, vf2) = ltac2 gl1 ;
      in
         (gl2, vf1 o vf2)
      end

val op >>> = op THEN_LT

(* first argument can be a tactic or a list-tactic *)
val _ = op THEN_LT : tactic * list_tactic -> tactic ;
val _ = op THEN_LT : list_tactic * list_tactic -> list_tactic ;

(*---------------------------------------------------------------------------
 * fun ALLGOALS (tac2:tactic) : list_tactic = fn gl =>
 *    let
 *        val (gll,pl) = unzip(map tac2 gl)
 *    in
 *       (flatten gll, mapshape(map length gll)pl)
 *    end;
 * A list_tactic which applies a given tactic to all goals
 *---------------------------------------------------------------------------*)

fun ALLGOALS tac2 gl =
         case itlist
                (fn goal => fn (G, V, lengths) =>
                  case tac2 goal of
                     ([], vfun) => let
                                      val th = vfun []
                                   in
                                      (G, empty th :: V, 0 :: lengths)
                                   end
                   | (goals, vfun) =>
                        (goals @ G, vfun :: V, length goals :: lengths))
                gl ([], [], []) of
            ([], V, _) =>
                ([], let val ths = map (fn f => f []) V in empty ths end)
          | (G, V, lengths) => (G, mapshape lengths V)

(*---------------------------------------------------------------------------
 * fun (tac1:tactic) THEN (tac2:tactic) : tactic = fn g =>
 *    let val (gl,p) = tac1 g
 *        val (gll,pl) = unzip(map tac2 gl)
 *    in
 *       (flatten gll, (p o mapshape(map length gll)pl))
 *    end;
 *---------------------------------------------------------------------------*)

fun tac1 THEN tac2 = tac1 THEN_LT ALLGOALS tac2 ;
val op >> = op THEN
val op \\ = op THEN

(* first argument can be a tactic or a list-tactic *)
val _ = op THEN : tactic * tactic -> tactic ;
val _ = op THEN : list_tactic * tactic -> list_tactic ;

(*---------------------------------------------------------------------------
 * fun TACS_TO_LT (tac2l: tactic list) : list_tactic = fn gl =>
 *    let
 *        val tac2gl = zip tac2l gl
 *        val (gll,pl) = unzip (map (fn (tac2,g) => tac2 g) tac2gl)
 *    in
 *       (flatten gll, mapshape(map length gll) pl)
 *    end
 * Converts a list of tactics to a single list_tactic
 *---------------------------------------------------------------------------*)

fun TACS_TO_LT (tacl: tactic list) : list_tactic =
   fn gl =>
      let
         val (G, V, lengths) =
            itlist2
               (fn goal => fn tac => fn (G, V, lengths) =>
                 case tac goal of
                    ([], vfun) => let
                                     val th = vfun []
                                  in
                                     (G, (empty th) :: V, 0 :: lengths)
                                  end
                  | (goals, vfun) =>
                      (goals @ G, vfun :: V, length goals :: lengths))
               gl tacl ([], [], [])
      in
         case G of
            [] => ([], let val ths = map (fn f => f []) V in empty ths end)
          | _  => (G, mapshape lengths V)
      end

(*---------------------------------------------------------------------------
 * NULL_OK_LT ltac: A list-tactical like ltac but succeeds with no effect
 *                  when applied to an ampty goal list
 *---------------------------------------------------------------------------*)

fun NULL_OK_LT ltac [] = ([], Lib.I)
  | NULL_OK_LT ltac gl = ltac gl ;

(*---------------------------------------------------------------------------
 * fun (tac1:tactic) THENL (tac2l: tactic list) : tactic = fn g =>
 *    let val (gl,p) = tac1 g
 *        val tac2gl = zip tac2l gl
 *        val (gll,pl) = unzip (map (fn (tac2,g) => tac2 g) tac2gl)
 *    in
 *       (flatten gll, p o mapshape(map length gll) pl)
 *    end
 * BUT - if gl is empty, just return (gl, p)
 *---------------------------------------------------------------------------*)

fun tac1 THENL tacs2 = tac1 THEN_LT NULL_OK_LT (TACS_TO_LT tacs2) ;
val op >| = op THENL

(* first argument can be a tactic or a list-tactic *)
val _ = op THENL : tactic * tactic list -> tactic ;
val _ = op THENL : list_tactic * tactic list -> list_tactic ;

fun (tac1 ORELSE tac2) g = tac1 g handle HOL_ERR _ => tac2 g
fun (ltac1 ORELSE_LT ltac2) gl = ltac1 gl handle HOL_ERR _ => ltac2 gl

(*---------------------------------------------------------------------------
 * tac1 THEN1 tac2: A tactical like THEN that applies tac2 only to the
 *                  first subgoal of tac1
 *---------------------------------------------------------------------------*)

fun op THEN1 (tac1: tactic, tac2: tactic) : tactic =
   fn g =>
      let
         val (gl, jf) = tac1 g
         val (h_g, t_gl) =
            case gl of
               [] => raise ERR "THEN1" "goal completely solved by first tactic"
             | h :: t => (h, t)
         val (h_gl, h_jf) = tac2 h_g
         val _ =
            if null h_gl then ()
            else raise ERR "THEN1" "first subgoal not solved by second tactic"
      in
         (t_gl, fn thl => jf (h_jf [] :: thl))
      end

val op >- = op THEN1

(*---------------------------------------------------------------------------
 * NTH_GOAL tac n: A list_tactic that applies tac to the nth goal
   (counting goals from 1)
 *---------------------------------------------------------------------------*)
fun NTH_GOAL tac n gl1 =
  let
    val (gl_before, ggl_after) = Lib.split_after (n-1) gl1
      handle _ => raise ERR "NTH_GOAL" "no nth subgoal in list" ;
    val (g, gl_after) = valOf (List.getItem ggl_after)
      handle _ => raise ERR "NTH_GOAL" "no nth subgoal in list" ;
    val (gl2, vf2) = tac g ;
    val gl_result = gl_before @ gl2 @ gl_after ;
    fun vf thl =
      let val (th_before, th_rest) = Lib.split_after (n-1) thl ;
        val (th2, th_after) = Lib.split_after (length gl2) th_rest ;
        val th_result = th_before @ vf2 th2 :: th_after ;
      in th_result end ;
  in (gl_result, vf) end ;

fun LASTGOAL tac gl1 = NTH_GOAL tac (length gl1) gl1 ;
fun HEADGOAL tac gl1 = NTH_GOAL tac 1 gl1 ;

(*---------------------------------------------------------------------------
 * SPLIT_LT n (ltaca, ltacb) : A list_tactic that applies ltaca to the
   first n goals, and ltacb to the rest
 *---------------------------------------------------------------------------*)
fun SPLIT_LT n (ltaca, ltacb) gl =
  let val fixn = if n >= 0 then n else length gl + n ;
    val (gla, glb) = Lib.split_after fixn gl ;
    val (glra, vfa) = ltaca gla ;
    val (glrb, vfb) = ltacb glb ;
    fun vf ths =
      let val (thsa, thsb) = Lib.split_after (length glra) ths ;
      in vfa thsa @ vfb thsb end ;
  in (glra @ glrb, vf) end ;

(*---------------------------------------------------------------------------
 * ROTATE_LT n :
 * A list_tactic that moves the first n goals to the end of the goal list
 * first n goals
 *---------------------------------------------------------------------------*)
fun ROTATE_LT n [] = ([], Lib.I)
  | ROTATE_LT n gl =
    let val lgl = length gl ;
      val fixn = Int.mod (n, lgl) ;
      val (gla, glb) = Lib.split_after fixn gl ;
      fun vf ths =
	let val (thsb, thsa) = Lib.split_after (lgl - fixn) ths ;
	in thsa @ thsb end ;
    in (glb @ gla, vf) end ;

(*---------------------------------------------------------------------------
 * REVERSE tac: A tactical that reverses the list of subgoals of tac.
 *              Intended for use with THEN1 to pick the `easy' subgoal, e.g.:
 *              - CONJ_TAC THEN1 SIMP_TAC
 *                  if the first conjunct is easily dispatched
 *              - REVERSE CONJ_TAC THEN1 SIMP_TAC
 *                  if it is the second conjunct that yields.
 *---------------------------------------------------------------------------*)

fun REVERSE tac g =
   let
      val (gl, jf) = tac g
   in
      (rev gl, jf o rev)
   end
val reverse = REVERSE

(*---------------------------------------------------------------------------
 * REVERSE_LT: A list_tactic that reverses a list of subgoals
 *---------------------------------------------------------------------------*)

fun REVERSE_LT gl = (rev gl, rev) ;

(* for testing, redefine REVERSE
fun REVERSE tac = tac THEN_LT REVERSE_LT ;
*)

(*---------------------------------------------------------------------------
 * Fail with the given token.  Useful in tactic programs to check that a
 * tactic produces no subgoals.  Write
 *
 *      TAC  THEN  FAIL_TAC "TAC did not solve the goal"
 *---------------------------------------------------------------------------*)

fun FAIL_TAC tok (g: goal) = raise ERR "FAIL_TAC" tok
fun FAIL_LT tok (gl: goal list) = raise ERR "FAIL_LT" tok

(*---------------------------------------------------------------------------
 * Tactic that succeeds on no goals;  identity for ORELSE.
 *---------------------------------------------------------------------------*)

fun NO_TAC g = FAIL_TAC "NO_TAC" g
fun NO_LT gl = FAIL_LT "NO_LT" gl

(* for testing, redefine THEN1
fun tac1 THEN1 tac2 = tac1 THEN_LT NTH_GOAL (tac2 THEN NO_TAC) 1 ;
fun tac1 THEN1 tac2 = tac1 THEN_LT REVERSE_LT THEN_LT
  LASTGOAL (tac2 THEN NO_TAC) THEN_LT REVERSE_LT ;
*)

(*---------------------------------------------------------------------------
 * Tactic that succeeds on all goals;  identity for THEN
 *---------------------------------------------------------------------------*)

val ALL_TAC: tactic = fn (g: goal) => ([g], hd)
val ALL_LT: list_tactic = fn (gl: goal list) => (gl, Lib.I)
val all_tac = ALL_TAC

fun TRY tac = tac ORELSE ALL_TAC
fun TRY_LT ltac = ltac ORELSE_LT ALL_LT
fun TRYALL tac = ALLGOALS (TRY tac) ;

(*---------------------------------------------------------------------------
 * The abstraction around g is essential to avoid looping, due to applicative
 * order semantics.
 *---------------------------------------------------------------------------*)

fun REPEAT tac g = ((tac THEN REPEAT tac) ORELSE ALL_TAC) g
fun REPEAT_LT ltac gl = ((ltac THEN_LT REPEAT_LT ltac) ORELSE_LT ALL_LT) gl
val rpt = REPEAT

(*---------------------------------------------------------------------------
 * Add extra subgoals, which may be needed to make a tactic valid;
 * similar to VALIDATE, but you can control the order of the extra goals
 *---------------------------------------------------------------------------*)
fun ADD_SGS_TAC (tms : term list) (tac : tactic) (g as (asl, w) : goal) =
  let val (glist, prf) = tac g ;
    val extra_goals = map (fn tm => (asl, tm)) tms ;
    val nextra = length extra_goals ;
    (* new validation: apply the theorems proving the additional goals to
      eliminate the extra hyps in the theorem proved by the given validation *)
    fun eprf ethlist =
      let val (extra_thms, thlist) = split_after nextra ethlist ;
      in itlist PROVE_HYP extra_thms (prf thlist) end ;
  in (extra_goals @ glist, eprf) end ;

(*---------------------------------------------------------------------------
 * Tacticals to make any tactic or list_tactic valid.
 *
 *    VALID tac
 *
 * is the same as "tac", except it will fail in the cases where "tac"
 * returns an invalid proof.
 *
 *    VALID_LT ltac
 *
 * is the same as "ltac", except it will fail in the cases where "ltac"
 * returns an invalid proof.
 *---------------------------------------------------------------------------*)

local
   val validity_tag = "ValidityCheck"
   fun masquerade goal = Thm.mk_oracle_thm validity_tag goal
   fun achieves th (asl, w) =
      Term.aconv (concl th) w andalso
      Lib.all (fn h => Lib.exists (aconv h) asl) (hyp th)
in
   fun VALID (tac: tactic) : tactic =
      fn g: goal =>
         let
            val (result as (glist, prf)) = tac g
         in
            if achieves (prf (map masquerade glist)) g
               then result
            else raise ERR "VALID" "Invalid tactic"
         end

   fun VALID_LT (ltac: list_tactic) : list_tactic =
      fn gl: goal list =>
         let
            val (result as (glist, prf)) = ltac gl
         in
            if Lib.all2 achieves (prf (map masquerade glist)) gl
               then result
            else raise ERR "VALID_LT" "Invalid list-tactic"
         end
end

(*---------------------------------------------------------------------------
 * Tacticals to include proofs of necessary hypotheses for an invalid
 * tactic or list_tactic valid.
 *
 *    VALIDATE tac
 *    GEN_VALIDATE true tac
 *
 * is the same as "tac", except that where "tac" returns a proof which is
 * invalid because it proves a theorem with extra hypotheses,
 * it returns those hypotheses as extra goals
 *
 *    VALIDATE_LT ltac
 *    GEN_VALIDATE_LT true ltac
 *
 * is the same as "ltac", except it will return extra goals where this is
 * necessary to make a valid list-tactic
 *
 *    GEN_VALIDATE(_LT) false always returns extra goals corresponding
 * to the hypotheses of the theorem proved
 *
 *---------------------------------------------------------------------------*)
local val validity_tag = "ValidityCheck"
      fun masquerade goal = Thm.mk_oracle_thm validity_tag goal ;
      fun achieves_concl th (asl, w) = Term.aconv (concl th) w ;
      fun hyps_not_in_goal th (asl, w) =
        Lib.filter (fn h => not (Lib.exists (aconv h) asl)) (hyp th) ;
      fun extra_goals_tbp flag th (asl, w) =
        List.map (fn eg => (asl, eg))
	  (case flag of true => hyps_not_in_goal th (asl, w)
	    | false => hyp th) ;
in
(* GEN_VALIDATE : bool -> tactic -> tactic *)
fun GEN_VALIDATE (flag : bool) (tac : tactic) (g as (asl, w) : goal) =
  let val (glist, prf) = tac g ;
    (* pretend new goals are theorems, and apply validation to them *)
    val thprf = (prf (map masquerade glist)) ;
    val _ = if achieves_concl thprf g then ()
      else raise ERR "GEN_VALIDATE" "Invalid tactic - wrong conclusion" ;
    val extra_goals = extra_goals_tbp flag thprf g ;
    val nextra = length extra_goals ;
    (* new validation: apply the theorems proving the additional goals to
      eliminate the extra hyps in the theorem proved by the given validation *)
    fun eprf ethlist =
      let val (extra_thms, thlist) = split_after nextra ethlist ;
      in itlist PROVE_HYP extra_thms (prf thlist) end ;
  in (extra_goals @ glist, eprf) end ;

(* split_lists : int list -> 'a list -> 'a list list * 'a list *)
fun split_lists (n :: ns) ths =
    let val (nths, rest) = split_after n ths ;
      val (nsths, left) = split_lists ns rest ;
    in (nths :: nsths, left) end
  | split_lists [] ths = ([], ths) ;

(* GEN_VALIDATE_LT : bool -> list_tactic -> list_tactic *)
fun GEN_VALIDATE_LT (flag : bool) (ltac : list_tactic) (gl : goal list) =
  let val (glist, prf) = ltac gl ;
    (* pretend new goals are theorems, and apply validation to them *)
    val thsprf = (prf (map masquerade glist)) ;
    val _ = if Lib.all2 achieves_concl thsprf gl then ()
      else raise ERR "GEN_VALIDATE_LT"
          "Invalid list-tactic - some wrong conclusion" ;
    val extra_goal_lists = Lib.map2 (extra_goals_tbp flag) thsprf gl ;
    val nextras = map length extra_goal_lists ;
    (* new validation: apply the theorems proving the additional goals to
      eliminate the extra hyps in the theorems proved by the given validation *)
    fun eprf ethlist =
      let val (extra_thm_lists, thlist) = split_lists nextras ethlist ;
      in Lib.map2 (itlist PROVE_HYP) extra_thm_lists (prf thlist) end ;
  in (List.concat extra_goal_lists @ glist, eprf) end ;

end;

val VALIDATE = GEN_VALIDATE true ;
val VALIDATE_LT = GEN_VALIDATE_LT true ;

(* could avoid duplication of code in the above by the following
fun GEN_VALIDATE flag tac =
  ALL_TAC THEN_LT GEN_VALIDATE_LT flag (TACS_TO_LT [tac]) ;
*)

(*---------------------------------------------------------------------------
 * Provide a function (tactic) with the current assumption list.
 *---------------------------------------------------------------------------*)

fun ASSUM_LIST aslfun (g as (asl, _)) = aslfun (map ASSUME asl) g

(*---------------------------------------------------------------------------
 * Pop the first assumption and give it to a function (tactic)
 *---------------------------------------------------------------------------*)

fun POP_ASSUM thfun (a :: asl, w) = thfun (ASSUME a) (asl, w)
  | POP_ASSUM   _   ([], _) = raise ERR "POP_ASSUM" "no assum"
val pop_assum = POP_ASSUM

(*---------------------------------------------------------------------------
 * Pop off the entire assumption list and give it to a function (tactic)
 *---------------------------------------------------------------------------*)

fun POP_ASSUM_LIST asltac (asl, w) = asltac (map ASSUME asl) ([], w)

(*---------------------------------------------------------------------------
 * Pop the first assumption satisying the given predictae and give it to
 * a function (tactic).
 *---------------------------------------------------------------------------*)

fun PRED_ASSUM pred thfun (asl, w) =
   case Lib.total (Lib.pluck pred) asl of
      SOME (ob, asl') => thfun (ASSUME ob) (asl', w)
    | NONE => raise ERR "PRED_ASSUM" "No suitable assumption found."

(*---------------------------------------------------------------------------
 * Pop the first assumption matching (higher-order match) the given term
 * and give it to a function (tactic).
 *---------------------------------------------------------------------------*)

local
   fun match_with_constants constants pat ob =
      let
         val (tm_inst, ty_inst) = ho_match_term [] empty_tmset pat ob
         val bound_vars = map #redex tm_inst
      in
         null (intersect constants bound_vars)
      end
      handle HOL_ERR _ => false
in
   fun PAT_ASSUM pat thfun (asl, w) =
     case List.filter (can (ho_match_term [] empty_tmset pat)) asl of
        [] => raise ERR "PAT_ASSUM" "No assumptions match the given pattern"
      | [x] => let
                  val (ob, asl') = Lib.pluck (Lib.equal x) asl
               in
                  thfun (ASSUME ob) (asl', w)
               end
      |  _ => let
                 val fvars = free_varsl (w :: asl)
                 val (ob, asl') = Lib.pluck (match_with_constants fvars pat) asl
              in
                 thfun (ASSUME ob) (asl', w)
              end
end

(*-- Tactical quantifiers -- Apply a list of tactics in succession. -------*)

(*---------------------------------------------------------------------------
 * Uses every tactic (similarly EVERY_LT for list_tactics)
 *    EVERY [TAC1;...;TACn] =  TAC1  THEN  ...  THEN  TACn
 *---------------------------------------------------------------------------*)

fun EVERY tacl = List.foldr (op THEN) ALL_TAC tacl
fun EVERY_LT ltacl = List.foldr (op THEN_LT) ALL_LT ltacl

(*---------------------------------------------------------------------------
 * Uses first tactic that succeeds.
 *    FIRST [TAC1;...;TACn] =  TAC1  ORELSE  ...  ORELSE  TACn
 *---------------------------------------------------------------------------*)

fun FIRST [] g = NO_TAC g
  | FIRST (tac :: rst) g = tac g handle HOL_ERR _ => FIRST rst g

fun MAP_EVERY tacf lst = EVERY (map tacf lst)
val map_every = MAP_EVERY
fun MAP_FIRST tacf lst = FIRST (map tacf lst)

(*---------------------------------------------------------------------------
 * Uses first tactic that proves the goal.
 *    FIRST_PROVE [TAC1;...;TACn] =
 *      (TAC1 THEN NO_TAC)  ORELSE  ...  ORELSE  (TACn THEN NO_TAC)
 * Fails if no tactic proves the goal.
 *---------------------------------------------------------------------------*)

fun FIRST_PROVE tacl =
   itlist (fn a => fn b => (a THEN NO_TAC) ORELSE b) tacl NO_TAC

(*---------------------------------------------------------------------------
 * Call a thm-tactic for every assumption.
 *---------------------------------------------------------------------------*)

val EVERY_ASSUM = ASSUM_LIST o MAP_EVERY

(*---------------------------------------------------------------------------
 * Call a thm-tactic for the first assumption at which it succeeds.
 *---------------------------------------------------------------------------*)

val shut_parser_up =
   trace ("notify type variable guesses", 0) o
   trace ("syntax_error", 0) o
   trace ("show_typecheck_errors", 0)

local
  fun find ttac name goal [] = raise ERR name  ""
    | find ttac name goal (a :: L) =
      ttac (ASSUME a) goal handle HOL_ERR _ => find ttac name goal L
in
  fun FIRST_ASSUM ttac (A, g) =
        shut_parser_up (find ttac "FIRST_ASSUM" (A, g)) A
  fun LAST_ASSUM ttac (A, g) =
        shut_parser_up (find ttac "LAST_ASSUM" (A, g)) (List.rev A)
  val first_assum = FIRST_ASSUM
  val last_assum = LAST_ASSUM
end


(*---------------------------------------------------------------------------
 * Call a thm-tactic for the first assumption at which it succeeds and
 * remove that assumption from the list.
 * Note that  UNDISCH_THEN is actually defined for public consumption
 * in Thm_cont.sml, but we can't use that here because Thm_cont builds
 * on this module. Arguably all of the ASSUM tactics are not tacticals
 * at all, and shouldn't be here along with THEN etc.
 *---------------------------------------------------------------------------*)

local
   fun UNDISCH_THEN tm ttac (asl, w) =
      let val (_, A) = Lib.pluck (equal tm) asl in ttac (ASSUME tm) (A, w) end
   fun f ttac th = UNDISCH_THEN (concl th) ttac
in
   val FIRST_X_ASSUM = FIRST_ASSUM o f
   val LAST_X_ASSUM = LAST_ASSUM o f
   val first_x_assum = FIRST_X_ASSUM
   val last_x_assum = LAST_X_ASSUM
end

(*---------------------------------------------------------------------------
 * Split off a new subgoal and provide it as a theorem to a tactic
 *
 *     SUBGOAL_THEN wa (\tha. tac)
 *
 * makes a subgoal of wa, and also assumes wa for proving the original goal.
 * Most convenient when the tactic solves the original goal, leaving only the
 * new subgoal wa.
 *---------------------------------------------------------------------------*)

fun SUBGOAL_THEN wa ttac (asl, w) =
   let
      val (gl, p) = ttac (ASSUME wa) (asl, w)
   in
      ((asl, wa) :: gl,
       (fn (tha :: thl) => PROVE_HYP tha (p thl) | _ => raise Match))
   end

(*---------------------------------------------------------------------------
 * Use another subgoal, providing it as a theorem to a tactic
 *
 *     USE_SG_THEN ttac nu np
 *
 * assumes subgoal number nu for proving subgoal number np
 *---------------------------------------------------------------------------*)

(* USE_SG_VAL : int -> int -> list_validation *)
fun USE_SG_VAL nu np thl =
  let val thu = List.nth (thl, nu - 1) ;
  in apnth (PROVE_HYP thu) (np - 1) thl end ;

(* USE_SG_THEN : thm_tactic -> int -> int -> list_tactic *)
fun USE_SG_THEN ttac nu np gl =
  let
    val (_, wu) = List.nth (gl, nu - 1) ;
    val ltac = NTH_GOAL (ttac (ASSUME wu)) np ;
    val (glr, v) = ltac gl ;
    val vp = USE_SG_VAL nu np ;
  in (glr, vp o v) end ;

(* USE_SG_TAC : int -> int -> list_tactic
val USE_SG_TAC = USE_SG_THEN ASSUME_TAC ;
*)

(*---------------------------------------------------------------------------
 * A tactical that makes a tactic fail if it has no effect.
 *---------------------------------------------------------------------------*)

fun CHANGED_TAC tac g =
   let
      val (gl, p) = tac g
   in
      if set_eq gl [g] then raise ERR "CHANGED_TAC" "no change" else (gl, p)
   end

(*---------------------------------------------------------------------------
 * A tactical that parses in the context of a goal, a la the Q library.
 *---------------------------------------------------------------------------*)

fun parse_with_goal t (asms, g) =
   let
      val ctxt = free_varsl (g :: asms)
   in
      Parse.parse_in_context ctxt t
   end

val Q_TAC = fn tac => fn g => W (tac o parse_with_goal g)

end (* Tactical *)
