structure TacticStep :> TacticStep =
struct

open TacticParse

(* Span extraction for FAtom types where topSpan returns NONE *)
fun altSpan (Subgoal (s, e)) = SOME (s, e)
  | altSpan (LSelectGoal p) = SOME p
  | altSpan (LSelectGoals p) = SOME p
  | altSpan _ = NONE

(* End offset for an FAtom fragment *)
fun fragEnd (FAtom a) =
      (case (topSpan a, altSpan a) of
         (SOME (_, r), _) => r
       | (NONE, SOME (_, r)) => r
       | _ => 0)
  | fragEnd _ = 0

(* Map tac_frag_open to goalFrag function name *)
fun openFragName FOpen = "open_paren"
  | openFragName FOpenThen1 = "open_then1"
  | openFragName FOpenFirst = "open_first"
  | openFragName FOpenRepeat = "open_repeat"
  | openFragName FOpenTacsToLT = "open_tacs_to_lt"
  | openFragName FOpenNullOk = "open_null_ok"
  | openFragName (FOpenNthGoal (i, _)) = "open_nth_goal " ^ Int.toString i
  | openFragName FOpenLastGoal = "open_last_goal"
  | openFragName FOpenHeadGoal = "open_head_goal"
  | openFragName (FOpenSplit (i, _)) = "open_split_lt " ^ Int.toString i
  | openFragName FOpenSelect = "open_select_lt"
  | openFragName FOpenFirstLT = "open_first_lt"

(* Map tac_frag_mid to goalFrag function name *)
fun midFragName FNextFirst = "next_first"
  | midFragName FNextTacsToLT = "next_tacs_to_lt"
  | midFragName FNextSplit = "next_split_lt"
  | midFragName FNextSelect = "next_select_lt"

(* Map tac_frag_close to goalFrag function name *)
fun closeFragName FClose = "close_paren"
  | closeFragName FCloseFirst = "close_first"
  | closeFragName FCloseRepeat = "close_repeat"
  | closeFragName FCloseFirstLT = "close_first_lt"

(* Fragment classification *)
fun frag_type (FAtom (LSelectGoal _)) = "select"
  | frag_type (FAtom (LSelectGoals _)) = "selects"
  | frag_type (FAtom _) = "expand"
  | frag_type (FFOpen _) = "open"
  | frag_type (FFMid _) = "mid"
  | frag_type (FFClose _) = "close"
  | frag_type _ = ""

(* Extract raw text from a fragment.
   Subgoal atoms with backtick-starting text get "sg " prefix. *)
fun frag_text proofBody (FAtom a) =
      let val raw = (case (topSpan a, altSpan a) of
                       (SOME (start, endPos), _) =>
                         String.substring(proofBody, start, endPos - start)
                     | (NONE, SOME (start, endPos)) =>
                         String.substring(proofBody, start, endPos - start)
                     | (NONE, NONE) => "")
      in case a of
           Subgoal _ =>
             if String.size raw > 0 andalso String.sub(raw, 0) = #"`"
             then "sg " ^ raw else raw
         | _ => raw
      end
  | frag_text _ (FFOpen opn) = openFragName opn
  | frag_text _ (FFMid mid) = midFragName mid
  | frag_text _ (FFClose cls) = closeFragName cls
  | frag_text _ _ = ""

(* Merge select/selects steps with their following bracket into expand_list.
   >~[`Foo`] >- simp[] is NOT decomposable into individual ef() steps
   because SELECT_GOAL_LT is a list_tactic. *)
fun isSelectKind "select" = true
  | isSelectKind "selects" = true
  | isSelectKind _ = false

fun merge_select_steps [] acc = rev acc
  | merge_select_steps ((endP, kind, patText) :: rest) acc =
      if isSelectKind kind then
        let
          fun collectSelects [] sels = (rev sels, [])
            | collectSelects ((ep, k, t) :: rest') sels =
                if isSelectKind k then collectSelects rest' (t :: sels)
                else (rev sels, (ep, k, t) :: rest')
          val (sels, afterSels) = collectSelects rest [patText]
          fun mkSelectPrefix [] = ""
            | mkSelectPrefix [p] = "Q.SELECT_GOAL_LT " ^ p
            | mkSelectPrefix (p :: ps) = "Q.SELECT_GOAL_LT " ^ p ^ " >>~ Q.SELECT_GOALS_LT " ^
                String.concatWith " >>~ Q.SELECT_GOALS_LT " ps
          val selectPrefix = mkSelectPrefix sels
          fun tryConsumeBracket [] = NONE
            | tryConsumeBracket ((_, "open", "open_then1") ::
                                (tacEnd, "expand", tacText) ::
                                (_, "close", _) :: rest') =
                SOME (selectPrefix ^ " >- " ^ tacText, tacEnd, rest')
            | tryConsumeBracket ((_, "open", "open_first") ::
                                (tacEnd, "expand", tacText) ::
                                (_, "close", _) :: rest') =
                SOME (selectPrefix ^ " >- " ^ tacText, tacEnd, rest')
            | tryConsumeBracket _ = NONE
        in
          case tryConsumeBracket afterSels of
            SOME (combinedText, tacEnd, rest') =>
              merge_select_steps rest' ((tacEnd, "expand_list", combinedText) :: acc)
          | NONE =>
              merge_select_steps afterSels acc
        end
      else
        merge_select_steps rest ((endP, kind, patText) :: acc)

(* step_plan: decompose a parsed tactic tree into navigable steps.
   Returns (end_offset, type, text) triples for every position.
   Re-expands ThenLT atoms left opaque by linearize, flattens the
   fragment tree, and merges select steps with their brackets. *)
fun step_plan proofBody tree =
  let
    fun isAtom e = Option.isSome (topSpan e)
    val rawFrags = linearize isAtom tree
    val reexpanded = reexpand_thenlt_frags rawFrags
    val flatFrags = flatten_frags reexpanded
    fun assignEnds [] _ acc = rev acc
      | assignEnds (f :: rest) lastAtomEnd acc =
          let
            val t = frag_type f
            val x = frag_text proofBody f
            val (endPos, newLast) = case f of
                FAtom _ => (let val e = fragEnd f in (e, e) end)
              | _ => (lastAtomEnd, lastAtomEnd)
          in
            if String.size x > 0
            then assignEnds rest newLast ((endPos, t, x) :: acc)
            else assignEnds rest lastAtomEnd acc
          end
    val rawSteps = assignEnds flatFrags 0 []
  in
    merge_select_steps rawSteps []
  end

end
