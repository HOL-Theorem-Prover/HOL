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

open Feedback HolKernel Drule Conv boolSyntax Abbrev

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
                 if identical c (snd g) then thm
                 else EQ_MP (ALPHA c (snd g)) thm
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
 *                  when applied to an empty goal list
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
fun op>>-(tac1, n) tac2 g =
  op>- (tac1, tac2) g
  handle e as HOL_ERR (er as {message,...}) =>
         if is_substring "THEN1" message then raise e
         else
           raise HOL_ERR (set_message
             (message ^ " (THEN1 on line "^Int.toString n^")") er)
fun (f ?? x) = f x


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
   datatype validity_failure = Concl of term | Hyp of term
   fun bad_prf th (asl, w) =
       if concl th !~ w then SOME (Concl (concl th))
       else
         case List.find (fn h => List.all (not o aconv h) asl) (hyp th) of
             NONE => NONE
           | SOME h => SOME (Hyp h)
   fun error f t e =
       let
         val pfx = "Invalid " ^ t ^ ": theorem has "
         val (desc, t) =
             case e of
                 Hyp h => ("bad hypothesis", h)
               | Concl c => ("wrong conclusion", c)
       in
         raise ERR f (pfx ^ desc ^ " " ^ Parse.term_to_string t)
       end
in
   fun VALID (tac: tactic) : tactic =
      fn g: goal =>
         let
            val (result as (glist, prf)) = tac g
         in
           case bad_prf (prf (map masquerade glist)) g of
               NONE => result
             | SOME e => error "VALID" "tactic" e
         end

   fun VALID_LT (ltac: list_tactic) : list_tactic =
      fn gl: goal list =>
         let
            val (result as (glist, prf)) = ltac gl
            val wrongnum_msg = "Invalid list-tactic: wrong number of results\
                               \ from justification"
            fun check ths gls =
                case (ths, gls) of
                    ([], []) => result
                  | (_, []) => raise ERR "VALID_LT" wrongnum_msg
                  | ([], _) => raise ERR "VALID_LT" wrongnum_msg
                  | (th::ths0,gl::gls0) =>
                    (case bad_prf th gl of
                         NONE => check ths0 gls0
                       | SOME e => error "VALID_LT" "list-tactic" e)
         in
            check (prf (map masquerade glist)) gl
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
        Lib.filter (fn h => not (Lib.exists (aconv h) asl)) (hyp th)
      fun extra_goals flag th g =
          if flag then hyps_not_in_goal th g else hyp th
      fun extra_goals_tbp flag th (g as (asl, w)) =
        List.map (fn eg => (asl, eg)) (extra_goals flag th g)
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


val VALIDATE = GEN_VALIDATE true ;
val VALIDATE_LT = GEN_VALIDATE_LT true ;

(* ----------------------------------------------------------------------
    CONJ_VALIDATE : tactic -> tactic

    Applies tactic argument to goal and guarantees validity by adding
    required extra hypotheses to head of new subgoal if only one is
    generated, or as one extra goal as a big conjunction if there are
    already multiple goals, or if there are no goals at all.
   ---------------------------------------------------------------------- *)
fun sing f [x] = f x
  | sing f _ = raise ERR "sing" "Bind Error"
fun CONJ_VALIDATE tac (g as (asl,_)) =
    let val tacresult as (sgs, vfn) = tac g
        val thprf = vfn (map masquerade sgs)
        val _ = if achieves_concl thprf g then ()
                else raise ERR "CONJ_VALIDATE"
                           "Invalid tactic - wrong conclusion"
        val newgoals = extra_goals true thprf g
        val nextra = length newgoals
        fun nullvfn th =
            let val ths = CONJ_LIST nextra th
            in
              itlist PROVE_HYP ths thprf
            end
        fun singvfn th =
            let val (th1, th2) = CONJ_PAIR th
            in
              itlist PROVE_HYP (CONJ_LIST nextra th1) (vfn [th2])
            end
        fun vfn' ths =
            case ths of
                [] => raise ERR "CONJ_VALIDATE" "Can't happen"
              | th1 :: rest =>
                itlist PROVE_HYP (CONJ_LIST nextra th1) (vfn rest)
    in
      if nextra = 0 then tacresult
      else
        case sgs of
            [] => ([(asl, list_mk_conj newgoals)], sing nullvfn)
          | [(asl',sg)] =>
            if List.all (C tmem asl) asl' then
              ([(asl',mk_conj(list_mk_conj newgoals, sg))], sing singvfn)
            else
              ((asl, list_mk_conj newgoals) :: sgs, vfn')
          | _ => ((asl, list_mk_conj newgoals) :: sgs, vfn')
    end

end (* local *)
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

(* ----------------------------------------------------------------------
    pop the last assumption and give it to a function
   ---------------------------------------------------------------------- *)

fun POP_LAST_ASSUM thfun (asl, w) =
    let
      val (front, last) = front_last asl
    in
      thfun (ASSUME last) (front, w)
    end handle Empty => raise ERR "POP_LAST_ASSUM" "no assum"
val pop_last_assum = POP_LAST_ASSUM

(*---------------------------------------------------------------------------
 * Pop off the entire assumption list and give it to a function (tactic)
 *---------------------------------------------------------------------------*)

fun POP_ASSUM_LIST asltac (asl, w) = asltac (map ASSUME asl) ([], w)

(*---------------------------------------------------------------------------
 * Pop the first assumption satisying the given predicate and give it to
 * a function (tactic).
 *---------------------------------------------------------------------------*)

fun PRED_ASSUM pred thfun (asl, w) =
   case Lib.total (Lib.pluck pred) asl of
      SOME (ob, asl') => thfun (ASSUME ob) (asl', w)
    | NONE => raise ERR "PRED_ASSUM" "No suitable assumption found."


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

(* ----------------------------------------------------------------------
    FIRST_LT : tactic -> list_tactic

    Given a list of goals, tries to apply tactic argument to all of
    them in turn until it succeeds. This generates a new list of goals
    consisting of the output of the successful tactic concatenated
    with the remaining original goals.
   ---------------------------------------------------------------------- *)

fun FIRST_LT tac gs =
    let
      fun recurse pfx gs =
          case gs of
              [] => raise ERR "FIRST_LT" "No goal on which tactic succeeds"
            | g::rest =>
              case Lib.total tac g of
                  NONE => recurse (g::pfx) rest
                | SOME (sgs, vf) =>
                  let
                    fun V ths =
                        let val (ms, rest) = Lib.split_after (length sgs) ths
                            val (p,s) = Lib.split_after (length pfx) rest
                        in
                          p @ [vf ms] @ s
                        end
                  in
                    (sgs @ List.revAppend(pfx,rest), V)
                  end
    in
      recurse [] gs
    end

(* ----------------------------------------------------------------------
    SELECT_LT_THEN : tactic -> tactic -> list_tactic

    Given a list of goals, tries to apply the first tactic argument to all of
    them in turn. This generates a new list of goals consisting of the output
    of the successful tactic applications concatenated with the remaining
    original goals. The second tactic is then applied to goals resulting from
    the successful tactic applications.
    This is similar to FIRST_LT, but:
      - if there are multiple goals for which the first tactic succeeds,
        SELECT_LT_THEN will apply the tactic to all these goals;
      - if there is no goal for which the first tactic succeeds, SELECT_LT_THEN
        will not give an error - instead the goal state will simply remain
        unchanged;
      - SELECT_LT allows a second tactic to be applied *only* to the selected
        goals.

    SELECT_LT : tactic -> list_tactic
    Like SELECT_LT_THEN, but does not apply a second tactic.
   ---------------------------------------------------------------------- *)

fun SELECT_LT_THEN select_tac cont_tac goals =
  let fun recurse failed goals =
    case goals of
      [] => ([], List.rev failed, fn v => v)
    | g::gs =>
      (case Lib.total select_tac g of
        NONE => recurse (g::failed) gs
      | SOME (sgoals, valid) =>
          let val (success, failed', vld) = recurse [] gs
              fun validation thms =
                let val (sgs, rest) = Lib.split_after (length sgoals) thms
                    val (succ, rest) = Lib.split_after (length success) rest
                    val (fail, rest) = Lib.split_after (length failed) rest
                    val (fail', _) = Lib.split_after (length failed') rest
                in fail @ [valid sgs] @ (vld (succ @ fail')) end
          in
            (sgoals @ success, List.revAppend(failed, failed'), validation)
          end)
      val (selected, failed, select_validation) = recurse [] goals
      val (successful, cont_validation) = ALLGOALS cont_tac selected
        handle e => raise ERR "SELECT_LT_THEN"
                              "Could not apply second tactic"
      fun validation thms =
        let val (succ,fail) = Lib.split_after (length successful) thms
        in select_validation (cont_validation succ @ fail) end
  in (successful @ failed, validation) end

fun SELECT_LT tac goals = SELECT_LT_THEN tac all_tac goals

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
      let val (_, A) = Lib.pluck (aconv tm) asl in ttac (ASSUME tm) (A, w) end
   fun f ttac th = UNDISCH_THEN (concl th) ttac
in
   val FIRST_X_ASSUM = FIRST_ASSUM o f
   val LAST_X_ASSUM = LAST_ASSUM o f
   val first_x_assum = FIRST_X_ASSUM
   val last_x_assum = LAST_X_ASSUM
end

(*---------------------------------------------------------------------------
 * Pop the first assumption matching (higher-order match) the given term
 * and give it to a function (tactic).
 *---------------------------------------------------------------------------*)

local
  fun can_match_with_constants fixedtys constants pat ob =
    let
      val (tm_inst, _) = ho_match_term fixedtys empty_tmset pat ob
      val bound_vars = map #redex tm_inst
    in
      null (op_intersect aconv constants bound_vars)
    end handle HOL_ERR _ => false

 (* you might think that one could simply pass the free variable set
    to ho_match_term, and do without this bogus looking
    can_match_with_constants function. Unfortunately, this doesn't
    quite work because the match is higher-order, meaning that a
    pattern like ``_ x``, where x is a "constant" will match something
    like ``f y``, where y is of the right type, but manifestly not x.
    This is because

      ho_match_term [] (some set including x) ``_ x`` ``f y``

    will return an instantiation where _ maps to (\x. y). This
    respects the request not to bind x, but the intention is bypassed.
 *)

   fun gen tcl pat thfun (g as (asl,w)) =
     let
       val fvs = free_varsl (w::asl)
       val patvars = free_vars pat
       val in_both = op_intersect aconv fvs patvars
       val fixedtys = itlist (union o type_vars_in_term) in_both []
     in
       tcl (thfun o assert (can_match_with_constants fixedtys fvs pat o concl))
     end g
in
   val PAT_X_ASSUM = gen FIRST_X_ASSUM
   val PAT_ASSUM = gen FIRST_ASSUM
end


local
fun hdsym t = (t |> lhs |> strip_comb |> #1)
              handle HOL_ERR _ => t |> strip_comb |> #1
fun hdsym_check tm ttac = ttac o assert (same_const tm o hdsym o concl)
in
fun hdtm_assum tm ttac = first_assum (hdsym_check tm ttac)
fun hdtm_x_assum tm ttac = first_x_assum (hdsym_check tm ttac)
end

fun sing f [x] = f x
  | sing f _ = raise ERR "sing" "Bind Error"

fun CONV_TAC (conv: conv) : tactic =
   fn (asl, w) =>
      let
         val th = conv w
         val (_, rhs) = dest_eq (concl th)
      in
         if aconv rhs T then ([], empty (EQ_MP (SYM th) boolTheory.TRUTH))
         else ([(asl, rhs)], sing (EQ_MP (SYM th)))
      end
      handle UNCHANGED =>
        if aconv w T (* special case, can happen! *)
          then ([], empty boolTheory.TRUTH)
        else ALL_TAC (asl, w)

(*---------------------------------------------------------------------------
 * Call a thm-tactic on the "assumption" obtained by negating the goal, i.e.,
   turn an existential goal into a universal assumption. Fix up the resulting
   new goal if necessary.
 *---------------------------------------------------------------------------*)

local
  fun DISCH_THEN ttac (asl,w) =
   let
      val (ant, conseq) = dest_imp w
      val (gl, prf) = ttac (ASSUME ant) (asl, conseq)
   in
      (gl, (if is_neg w then NEG_DISCH ant else DISCH ant) o prf)
   end
   handle HOL_ERR {message,origin_function, ...} =>
          raise ERR "DISCH_THEN" (origin_function ^ ":" ^ message)
  val NOT_NOT_E = boolTheory.NOT_CLAUSES |> CONJUNCT1
  val NOT_NOT_I = NOT_NOT_E |> GSYM
  val NOT_IMP_F = IMP_ANTISYM_RULE (SPEC_ALL boolTheory.F_IMP)
                                   (SPEC_ALL boolTheory.IMP_F)
  val IMP_F_NOT = NOT_IMP_F |> GSYM
  val P_IMP_P = boolTheory.IMP_CLAUSES |> SPEC_ALL |> CONJUNCTS |> el 4
  val NOT_IMP_F_elim =
      TRANS (AP_TERM boolSyntax.negation (SYM NOT_IMP_F))
            (boolTheory.NOT_CLAUSES |> CONJUNCT1 |> SPEC_ALL)
  fun EX_IMP_F_CONV tm =
    (IFC NOT_EXISTS_CONV (BINDER_CONV EX_IMP_F_CONV) (REWR_CONV NOT_IMP_F)) tm
  fun undo_conv tm =
    (IFC NOT_FORALL_CONV
         (BINDER_CONV undo_conv)
         (REWR_CONV NOT_IMP_F_elim ORELSEC TRY_CONV (REWR_CONV NOT_NOT_E))) tm
in
  fun goal_assum ttac : tactic =
    CONV_TAC (REWR_CONV NOT_NOT_I THENC RAND_CONV EX_IMP_F_CONV) THEN
    DISCH_THEN ttac THEN
    (CONV_TAC (REWR_CONV P_IMP_P) ORELSE
     TRY (CONV_TAC (REWR_CONV IMP_F_NOT THENC undo_conv)))
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

fun goaleq ((asms1,g1),(asms2,g2)) =
  ListPair.allEq (fn (t1,t2) => aconv t1 t2) (asms1,asms2) andalso
  aconv g1 g2

fun CHANGED_TAC tac g =
  let
    val (gl, p) = tac g
   in
     if ListPair.allEq goaleq (gl, [g]) then raise ERR "CHANGED_TAC" "no change"
     else (gl, p)
  end

fun check_delta exn P tac g =
    let
      val result as (gl,p) = tac g
    in
      if P (g, gl) then result else raise exn
    end

fun count0 m (g, gl) = List.all (fn (_, w) => m w = 0) gl
fun count_decreases m ((_,w), gl) =
    let val c0 = m w
    in
      List.all (fn (_,w') => m w' < c0) gl
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

fun Q_TAC0 {traces} tyopt (tac : term -> tactic) q (g as (asl,w)) =
  let
    open Parse
    val ctxt = free_varsl (w::asl)
    val ab =
        case tyopt of
            NONE => Absyn
          | SOME ty =>
            fn q => Absyn.TYPED(locn.Loc_None, Absyn q, Pretype.fromType ty)
    val s = TermParse.prim_ctxt_termS ab (term_grammar()) ctxt q
    fun cases s = List.foldl
                    (fn (trpair,f) => Feedback.trace trpair f)
                    seq.cases
                    traces
                    s
  in
    case cases s of
        NONE => raise ERR "Q_TAC" "No parse for quotation"
      | SOME _ =>
        (case cases (seq.mapPartial (fn t => total (tac t) g) s) of
             NONE => raise ERR "Q_TAC" "No parse of quotation leads to success"
           | SOME (res,_) => res)
  end

val Q_TAC = Q_TAC0 {traces = []} NONE
fun QTY_TAC ty = Q_TAC0 {traces = []} (SOME ty)

end (* Tactical *)
