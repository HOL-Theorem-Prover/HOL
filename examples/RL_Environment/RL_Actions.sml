structure RL_Actions = struct

datatype 'a partial_list =
    Lcons of 'a * 'a partial_list option
  | Lnil

fun add_Lnil NONE = SOME Lnil
  | add_Lnil (SOME (Lcons (th,lso))) = SOME (Lcons (th, add_Lnil lso))
  | add_Lnil (SOME _) = RL_Lib.die("add_Lnil on completed list")

fun add_Lcons _ th NONE = SOME (Lcons (th,NONE))
  | add_Lcons assert th (SOME (Lcons (th',lso))) =
      (assert th'; SOME (Lcons (th', add_Lcons assert th lso)))
  | add_Lcons _ th (SOME Lnil) = RL_Lib.die("add_Lcons on completed list")

fun get_complete_list Lnil = SOME []
  | get_complete_list (Lcons (x,lso)) =
      Option.map (Lib.cons x)
        (Option.mapPartial get_complete_list lso)

fun partial_list_to_string f (NONE) = "{?}"
  | partial_list_to_string f (SOME Lnil) = "NIL"
  | partial_list_to_string f (SOME (Lcons (x, ntl))) = (f x) ^ "::" ^ partial_list_to_string f ntl

type named_thm = string * HolKernel.thm
val name_of : named_thm -> string = #1
val thm_of : named_thm -> HolKernel.thm = #2

val get_complete_named_thm_list = Option.map (List.map thm_of) o get_complete_list

datatype tactic =
    gen_tac
  (*
  qx_gen_tac tmq
  qx_genl_tac [tmq]
  *)

  | Induct
  (*
  Induct_on tmq
  *)

  | metis_tac of named_thm partial_list option
  | rw of named_thm partial_list option
  | fs of named_thm partial_list option
  | rfs of named_thm partial_list option
  (*
  srw_tac [ss] [thm]
  fsrw_tac [ss] [thm]
  *)

  | decide_tac

  | pairarg_tac

  | var_eq_tac

  | strip_tac

  | CCONTR_TAC
  (*
  spose_not_then thm_tactic
  *)
  | rpt of tactic option
  (*
  | reverse of tactic option -- probably useless given Rotate
  *)

  | Cases
  (*
  Cases_on tmq
  *)

  | mp_tac of named_thm partial_list option
  (*
  qexists_tac tmq

  assume_tac thm
  strip_assume_tac thm

  disch_then thm_tactic
  first_assum thm_tactic
  first_x_assum thm_tactic
  last_assum thm_tactic
  last_x_assum thm_tactic
  qpat_assum tmq thm_tactic
  qpat_x_assum tmq thm_tactic
  goal_assum thm_tactic

  mp_then Any thm_tactic thm thm
  mp_then (Pat tmq) thm_tactic thm thm
  mp_then (Pos <thm list -> thm>) thm_tactic thm thm
  mp_then Concl thm_tactic thm thm
    e.g., disch_then (first_assum o mp_then Any mp_tac)

  qmatch_abbrev_tac tmq
  qmatch_goalsub_abbrev_tac tmq
  qmatch_asmsub_abbrev_tac tmq
  qmatch_assum_abbrev_tac tmq
  qmatch_rename_tac tmq
  qmatch_goalsub_rename_tac tmq
  qmatch_asmsub_rename_tac tmq
  qmatch_assum_rename_tac tmq

  qspec_then tmq thm thm_tactic
  qspecl_then [tmq] thm thm_tactic
  qispec_then tmq thm thm_tactic
  qispecl_then [tmq] thm thm_tactic (maybe called qispl_then?)

  qx_choose_then tmq thm thm_tactic
  qx_choosel_thn [tmq] thm thm_tactic

  Q.SUBGOAL_THEN tmq thm_tactic

  all_tac (does nothing)
  kall_tac thm (does nothing)
  *)

fun get_complete_tactic t =
  case t of
    metis_tac lso =>
      Option.map bossLib.metis_tac (Option.mapPartial get_complete_named_thm_list lso)
  | rw lso =>
      Option.map bossLib.rw (Option.mapPartial get_complete_named_thm_list lso)
  | fs lso =>
      Option.map bossLib.fs (Option.mapPartial get_complete_named_thm_list lso)
  | rfs lso =>
      Option.map bossLib.rfs (Option.mapPartial get_complete_named_thm_list lso)
  | mp_tac lso =>
      Option.map (boolLib.mp_tac o List.hd) (Option.mapPartial get_complete_named_thm_list lso)
  | gen_tac => SOME boolLib.gen_tac
  | Induct => SOME bossLib.Induct
  | decide_tac => SOME bossLib.decide_tac
  | pairarg_tac => SOME bossLib.pairarg_tac
  | var_eq_tac => SOME BasicProvers.var_eq_tac
  | rpt to => Option.map boolLib.rpt (Option.mapPartial get_complete_tactic to)
  (*
  | reverse to => Option.map boolLib.reverse (Option.mapPartial get_complete_tactic to)
  *)
  | strip_tac => SOME boolLib.strip_tac
  | CCONTR_TAC => SOME boolLib.CCONTR_TAC
  | Cases => SOME bossLib.Cases

fun tactic_to_string t =
    case t of
      gen_tac => "gen_tac"
    | Induct  => "induct"
    | metis_tac ntlo => "metis_tac " ^ partial_list_to_string name_of ntlo
    | rw ntlo => "rw " ^ partial_list_to_string name_of ntlo
    | fs ntlo => "fs " ^ partial_list_to_string name_of ntlo
    | rfs ntlo => "rfs " ^ partial_list_to_string name_of ntlo
    | decide_tac => "decide_tac"
    | pairarg_tac => "pairarg_tac"
    | var_eq_tac => "var_eq_tac"
    | rpt NONE => "rpt {?}"
    | rpt (SOME t) => "rpt " ^ tactic_to_string t
    (*
    | reverse NONE => "reverse {?}"
    | reverse (SOME t) => "reverse " ^ tactic_to_string t
    *)
    | strip_tac => "strip_tac"
    | CCONTR_TAC => "CCONTR_TAC"
    | Cases => "Cases"
    | mp_tac ntlo => "mp_tac " ^ partial_list_to_string name_of ntlo

datatype action =
    Tactic of tactic
  | Rotate
  | Back

fun action_to_string(Back) = "Back"
  | action_to_string(Rotate) = "Rotate"
  | action_to_string(Tactic t) = tactic_to_string t

val top_level_tactics =
  [gen_tac
  ,Induct
  ,metis_tac NONE
  ,rw NONE
  ,fs NONE
  ,rfs NONE
  ,decide_tac
  ,pairarg_tac
  ,var_eq_tac
  ,rpt NONE
  (* ,reverse NONE *)
  ,strip_tac
  ,CCONTR_TAC
  ,Cases
  ,mp_tac NONE]

val top_level_actions =
  Back::Rotate::(List.map Tactic top_level_tactics)

local

val all_theorems = (* TODO: ... *)
   [("bool.TRUTH",boolTheory.TRUTH),
    ("list.dropWhile_APPEND_EVERY",listTheory.dropWhile_APPEND_EVERY),
    ("list.EVERY2_EVERY",listTheory.EVERY2_EVERY),
    ("list.EVERY2_cong",listTheory.EVERY2_cong),
    ("list.EVERY2_LENGTH",listTheory.EVERY2_LENGTH),
    ("list.EVERY2_MAP",listTheory.EVERY2_MAP),
    ("list.EVERY2_mono",listTheory.EVERY2_mono),
    ("list.EVERY2_REVERSE",listTheory.EVERY2_REVERSE),
    ("list.EVERY2_LUPDATE_same",listTheory.EVERY2_LUPDATE_same),
    ("list.EVERY2_MEM_MONO",listTheory.EVERY2_MEM_MONO),
    ("list.EVERY2_refl",listTheory.EVERY2_refl)]

fun add_theorem_if_new th =
  let
    exception Duplicate_named_theorem
    fun check_dup th' =
      if name_of th = name_of th'
      then raise Duplicate_named_theorem else ()
  in add_Lcons check_dup th end

fun generate_theorem_actions f lso =
  Lib.mapfilter (fn th => f (add_theorem_if_new th lso)) all_theorems
  @ [f (add_Lnil lso)]

fun generate_single_theorem_actions f NONE =
  List.map (fn th => f (SOME (Lcons (th, SOME Lnil)))) all_theorems
|  generate_single_theorem_actions f _ = RL_Lib.die("generate_single_theorem_actions: invariant failure")

in

fun tactic_actions goal_state t =
  case t of
    metis_tac lso => generate_theorem_actions metis_tac lso
  | rw lso => generate_theorem_actions rw lso
  | fs lso => generate_theorem_actions fs lso
  | rfs lso => generate_theorem_actions rfs lso
  | mp_tac lso => generate_single_theorem_actions mp_tac lso
  | rpt NONE => List.map (rpt o SOME) top_level_tactics
  | rpt (SOME t) => List.map (rpt o SOME) (tactic_actions goal_state t)
  | _ => RL_Lib.die("tactic_actions: invariant failure")

end

end
