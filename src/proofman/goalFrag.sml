structure goalFrag :> goalFrag =
struct

open Abbrev Lib Feedback

val ERR = mk_HOL_ERR "goalFrag"

datatype stash_kind
  = Then1 of goal list * list_validation
  | TacsToLT of (goal list * list_validation) list * goal list * list_validation
  | NthGoal of goal list * goal list * list_validation

datatype 'a handled = Running of 'a | Failed of exn

fun mapHandled f (Running a) = (Running (f a) handle e as HOL_ERR _ => Failed e)
  | mapHandled _ (Failed e) = Failed e

datatype goaltree
  = Base of goal list * list_validation
  | Parallel of goaltree list * list_validation
  | Stashed of goaltree * stash_kind
  | Try of goaltree handled * (goal list * list_validation)
  | Repeat of goaltree handled *
    (goal list * list_validation -> goaltree handled) *
    (goal list * list_validation)
  | Done of goal list * list_validation

type goalstate = int * goaltree
type frag_tactic = goalstate -> goalstate

fun apply1 _ g (Base gs) = g gs
  | apply1 f _ (Parallel (gs, v)) = Parallel (map f gs, v)
  | apply1 f _ (Stashed (gs, k)) = Stashed (f gs, k)
  | apply1 f _ (Try (gs, k)) = Try (mapHandled f gs, k)
  | apply1 f _ (Repeat (gs, log, k)) = Repeat (mapHandled f gs, mapHandled f o log, k)
  | apply1 _ _ (t as Done _) = t

fun asBase (Base gs) = gs
  | asBase _ = raise Bind

fun apply f gs = apply1 (apply f) f gs

fun applyN f 0 gs = f gs
  | applyN f n gs = apply1 (applyN f (n-1)) (fn _ => raise Bind) gs

fun splitAtV n f g ths = let
  val (ths1, ths2) = Lib.split_after n ths
  in f ths1 @ g ths2 end
fun concatMapV f (ls, v: list_validation) = let
  fun go [] = ([], I)
    | go (a :: ls) = let
      val (g, v1: list_validation) = f a
      val (gs, vs) = go ls
      in (g @ gs, splitAtV (length g) v1 vs) end
  val (gs, v1) = go ls
  in (gs, v o v1: list_validation) end

fun expandf (tac:tactic) (n, g) =
  (n, apply (fn (gs, v) =>
    Base (concatMapV ((fn (gs, v) => (gs, single o v)) o tac) (gs, v))) g)
val expand = expandf o Tactical.VALID

fun expand_listf (ltac:list_tactic) (n, g) =
  (n, apply (fn (gs, v) => (fn (gs', v') => Base (gs', v o v')) (ltac gs)) g)
val expand_list = expand_listf o Tactical.VALID_LT

fun top_goals (_, Base (gs, _)) = gs
  | top_goals (_, g) = let
    fun go (Base (gs, _)) acc = List.revAppend (gs, acc)
      | go (Parallel (gs, _)) acc = goList gs acc
      | go (Stashed (gs, _)) acc = go gs acc
      | go (Try (gs, _)) acc = goHandled gs acc
      | go (Repeat (gs, _, _)) acc = goHandled gs acc
      | go (Done _) acc = acc
    and goHandled (Running gs) acc = go gs acc
      | goHandled (Failed _) acc = acc
    and goList [] acc = acc
      | goList (g::gs) acc = goList gs (go g acc)
    in rev $ go g [] end

val top_goal = hd o top_goals

fun open_paren (n, g) = (n+1, apply (fn (gs, v) =>
  Parallel (map (fn g => Base ([g], I)) gs, v)) g)

fun close_paren (n, g) = let
  fun go (Base _) = raise Bind
    | go (Parallel gs) = Base (concatMapV asBase gs)
    | go (Stashed (gs, k)) =
      (case k of
        Then1 (ss, v') =>
        (case asBase gs of
          ([], v) => Base (ss, fn ths => v' (v [] @ ths))
        | _ => raise ERR "THEN1" "first subgoal not solved by second tactic")
      | TacsToLT (acc, [], v) => Base (concatMapV I (rev acc, v))
      | TacsToLT _ => raise ERR "TACS_TO_LT" "length mismatch"
      | NthGoal (lo, hi, v) => let
        val (gs', v') = asBase gs
        val n1 = length lo; val n2 = length gs'
        fun validation ths = let
          val (ths1, ths) = Lib.split_after n1 ths
          val (ths2, ths3) = Lib.split_after n2 ths
          in v (ths1 @ v' ths2 @ ths3) end
        in Base (lo @ gs' @ hi, validation) end)
    | go (Try (Running gs, _)) = Base (asBase gs)
    | go (Try (Failed e, _)) = Portable.reraise e
    | go (Repeat (Running gs, v, _)) = let
      fun repeat gs = case v (asBase gs) of Failed _ => gs | Running gs => repeat gs
      in repeat gs end
    | go (Repeat (Failed _, _, gs)) = Base gs
    | go (Done gs) = Base gs
  in (n-1, applyN go (n-1) g) end

fun new_goal_list gs = (0, Base (gs, I))
fun finish_list (n, g) =
  case funpow n close_paren (n, g) of
    (0, Base ([], v)) => v []
  | _ => raise ERR "finish" "proof contains unsolved subgoals"

val new_goal = new_goal_list o single
val finish = hd o finish_list

fun open_then1 (n, g) = (n+1, apply (fn
    ([], _) => raise ERR "THEN1" "goal completely solved by first tactic"
  | (g::gs, v) => Stashed (Base ([g], I), Then1 (gs, v))) g)

fun open_first (n, g) = (n+1, apply (fn gs => Try (Running (Base gs), gs)) g)

fun next_first (n, g) = let
  fun go (Try (Running (Base gs), _)) = Done gs
    | go (Try (Failed _, gs)) = Try (Running (Base gs), gs)
    | go (Done gs) = Done gs
    | go _ = raise Bind
  in (n, applyN go (n-1) g) end

fun close_first (n, g) = let
  fun go (Try (Running gs, _)) = Base (asBase gs)
    | go (Try (Failed e, _)) = Portable.reraise e
    | go (Done gs) = Base gs
    | go _ = raise Bind
  in (n-1, applyN go (n-1) g) end

fun open_repeat (n, g) = (n+1, apply (fn gs => Repeat (Running $ Base gs, Running o Base, gs)) g)
fun close_repeat (n, g) = let;
  fun go (Repeat (Running gs, log, _)) = let
      fun repeat [] (acc, v) = (acc, v)
        | repeat (g::gs) (acc, v) =
          case log ([g], I) of
            Failed _ => repeat gs (g::acc, (fn (th, thacc) => (hd thacc :: th, tl thacc)) o v)
          | Running g' => let
            val (g1, v1) = asBase g'
            val (acc, v2) = repeat g1 (acc, fn x => ([], x))
            fun v' (ths, thacc) = apfst (fn th1 => v1 th1 @ ths) (v2 thacc)
            in repeat gs (acc, v' o v) end
      val (gs', v) = asBase gs
      val (gs', v') = repeat gs' ([], fn x => ([], x))
      in Base (rev gs', v o rev o fst o v') end
    | go (Repeat (Failed _, _, gs)) = Base gs
    | go _ = raise Bind
  in (n-1, applyN go (n-1) g) end

fun open_tacs_to_lt (n, g) = (n+1, apply (fn
    ([], _) => raise ERR "TACS_TO_LT" "length mismatch"
  | (g::gs, v) => Stashed (Base ([g], I), TacsToLT ([], gs, v))) g)

fun next_tacs_to_lt (n, g) = let
  fun go (Stashed (_, TacsToLT (_, [], _))) = raise ERR "TACS_TO_LT" "length mismatch"
    | go (Stashed (gs, TacsToLT (acc, g::gs', v))) =
      Stashed (Base ([g], I), TacsToLT (asBase gs :: acc, gs', v))
    | go _ = raise Bind
  in (n, applyN go (n-1) g) end

fun open_null_ok (n, g) = (n+1, apply (fn
    gs as ([], _) => Done gs
  | gs => Parallel ([Base gs], I)) g)
fun open_nth_goal i (n, g) = (n+1, apply (fn (gs, v) => let
  val (lo, (g, hi)) = apsnd (valOf o List.getItem) $ Lib.split_after (i-1) gs
    handle _ => raise ERR "NTH_GOAL" "no nth subgoal in list"
  in Stashed (Base ([g], I), NthGoal (lo, hi, v)) end) g)

val open_head_goal = open_nth_goal 1
fun open_last_goal (n, g) = (n+1, apply (fn (gs, v) => let
  val (lo, g) = front_last gs
    handle _ => raise ERR "LAST_GOAL" "no subgoals"
  in Stashed (Base ([g], I), NthGoal (lo, [], v)) end) g)

fun open_split_lt i (n, g) = (n+1, apply (fn (gs, v) => let
  val i = if i >= 0 then i else length gs + i
  val (lo, hi) = Lib.split_after i gs handle _ => raise ERR "LAST_GOAL" "no subgoals"
  in Stashed (Base (lo, I), NthGoal ([], hi, v)) end) g)
fun next_split_lt (n, g) = let
  fun go (Stashed (Base (gs, vlo), NthGoal ([], hi, v))) =
      Stashed (Base (hi, I), NthGoal (gs, [], v o splitAtV (length gs) vlo I))
    | go _ = raise Bind
  in (n, applyN go (n-1) g) end

val open_select_lt = open_first o open_paren
fun next_select_lt (n, g) = let
  fun go [] success (failed: (goal list * list_validation) list) v = let
      val (gs1, v1) = concatMapV I (rev success, I)
      val (gs2, v2) = concatMapV I (rev failed, I)
      fun v' n ths = let
        val (ths1, ths2) = Lib.split_after n ths
        in v ([], v1 (rev ths1), v2 (rev ths2)) end
      in Stashed (Base (gs1, v2), NthGoal ([], gs2, v' (length gs1))) end
    | go (Try (Running gs, _) :: rest) success failed v =
      go rest (asBase gs :: success) failed (v o (fn (a,b,c) => (hd b::a,tl b,c)))
    | go (Try (Failed _, ([g], v')) :: rest) success failed v =
      go rest success (([g], v') :: failed) (v o (fn (a,b,c) => (hd c::a,b,tl c)))
    | go _ _ _ _ = raise Bind
  fun f (Parallel (gs, v)) = go gs [] [] (v o #1)
    | f _ = raise Bind
  in (n-1, applyN f (n-2) g) end

val open_first_lt = open_first o open_paren
fun close_first_lt (n, g) = let
  fun go [] _ = raise ERR "FIRST_LT" "No goal on which tactic succeeds"
    | go (Try (Running (Base (gs, v)), _) :: rest) acc = let
      val rest = map (fn Try (_, ([g], _)) => g | _ => raise Bind) rest
      val v = splitAtV (length acc) I $ splitAtV (length gs) v I
      in Base (List.revAppend (acc, gs @ rest), v) end
    | go (Try (Failed _, ([g], _)) :: rest) acc = go rest (g :: acc)
    | go _ _ = raise Bind
  fun f (Parallel (gs, _)) = go gs []
    | f _ = raise Bind
  in (n-2, applyN f (n-2) g) end

fun pp_goalstate gs = let
  open smpp
  val pr_goal = goalStack.pr_goal
  val show_nsubgoals = current_trace "Goalstack.howmany_printed_subgoals"
  val other_subgoals_pretty_limit =
    current_trace "Goalstack.other_subgoals_pretty_limit"
  val show_stack_subgoal_count =
    current_trace "Goalstack.show_stack_subgoal_count" = 1
  in
    case top_goals gs of
      [] =>
      (case total finish gs of
        SOME th =>
        block Portable.CONSISTENT 0 (
          add_string "Initial goal proved." >>
          add_newline >>
          lift Parse.pp_thm th)
      | NONE =>
        add_string "No subgoals but proof incomplete (try close_paren)." >>
        add_newline)
    | goals => let
      val (ellipsis_action, goals_to_print) =
        if length goals > show_nsubgoals then let
          val num_elided = length goals - show_nsubgoals
          in
            (add_string (
              "..." ^ Int.toString num_elided ^ " subgoal"^
              (if num_elided = 1 then "" else "s") ^ " elided...") >>
            add_newline >> add_newline,
            rev (List.take (goals, show_nsubgoals)))
          end
        else
          (add_newline, rev goals)
      val (pfx, lastg) = front_last goals_to_print
      fun start () = (
        ellipsis_action >>
        pr_list pr_goal (add_newline >> add_newline) pfx)
      val size = List.foldl (fn (g,acc) => goalStack.goal_size g + acc) 0 pfx
      in
        block Portable.CONSISTENT 0 (
          (if size > other_subgoals_pretty_limit then
            with_flag (Parse.current_backend, PPBackEnd.raw_terminal) start ()
          else start ()) >>
          (if not (null pfx) then add_newline >> add_newline else nothing) >>
          pr_goal lastg >>
          (if length goals > 1 andalso show_stack_subgoal_count then
            add_string ("\n\n" ^ Int.toString (length goals) ^ " subgoals") >>
            add_newline
          else add_newline >> add_newline))
      end
  end

val pp_goalstate = Parse.mlower o pp_goalstate

end
