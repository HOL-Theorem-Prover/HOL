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

fun get_partial_list NONE = []
  | get_partial_list (SOME (Lcons (x, pl))) = x::(get_partial_list pl)
  | get_partial_list _ = RL_Lib.die("get_partial_list on completed list")

fun partial_list_to_string _ (NONE) = "{?}"
  | partial_list_to_string f (SOME pl) =
    case get_complete_list pl of
      NONE => String.concat["[", String.concatWith ", " (List.map f (get_partial_list (SOME pl))), ", {?}"]
    | SOME ls => String.concat["[", String.concatWith ", " (List.map f ls), "]"]

(* fei add *)
datatype term_type = TypeOf of partial_tree option
and partial_tree =
    Comb of (partial_tree option) * (partial_tree option)
  | Abs  of string * (term_type) * (partial_tree option)
  | Atom of Abbrev.term

exception Add_To_Complete_Tree

fun add_term t (SOME (Comb (t1, t2))) = (SOME (Comb ((add_term t t1), t2))
                                        handle Add_To_Complete_Tree
                                        => SOME (Comb (t1, (add_term t t2))))
  | add_term t (SOME (Abs (t1, TypeOf t2, t3))) =
      (SOME (Abs (t1, TypeOf (add_term t t2), t3))
       handle Add_To_Complete_Tree
       => SOME (Abs (t1, TypeOf t2, add_term t t3)))
  | add_term t (SOME (Atom t1)) = raise Add_To_Complete_Tree
  | add_term t NONE = SOME t
(* note there is unhandled exception for the whole function *)

fun is_tree_complete (SOME (Comb (t1, t2))) =
      is_tree_complete(t1) andalso is_tree_complete(t2)
  | is_tree_complete (SOME (Abs (t1, TypeOf t2, t3))) =
      is_tree_complete(t2) andalso is_tree_complete(t3)
  | is_tree_complete (SOME (Atom a)) = true
  | is_tree_complete NONE = false

fun get_complete_tree (SOME (Comb (t1, t2))) =
       let val t1' = get_complete_tree t1
           val t2' = get_complete_tree t2
       in if (isSome t1' andalso isSome t2')
          then SOME ("(" ^ (valOf t1') ^ " " ^ (valOf t2') ^ ")")
          else NONE
       end
  | get_complete_tree (SOME (Abs (t1, TypeOf t2, t3))) =
       let val t2' = get_complete_tree t2
           val t3' = get_complete_tree t3
       in if (isSome t2' andalso isSome t3')
          then SOME ("\\" ^ (t1) ^ ":" ^ (valOf t2') ^ "->" ^ (valOf t3'))
          else NONE
       end
  | get_complete_tree (SOME (Atom a)) =
       SOME (Parse.term_to_string a)
  | get_complete_tree NONE = NONE

fun partial_tree_to_string f (SOME (Comb (t1, t2))) =
      let val t1' = partial_tree_to_string f t1
          val t2' = partial_tree_to_string f t2
      in "(" ^ t1' ^ " " ^ t2' ^ ")"
      end
  | partial_tree_to_string f (SOME (Abs (t1, TypeOf t2, t3))) =
      let val t2' = partial_tree_to_string f t2
          val t3' = partial_tree_to_string f t3
      in "\\" ^ (t1) ^ ":" ^ (t2') ^ "->" ^ t3'
      end
  | partial_tree_to_string f (SOME (Atom a)) = (f a)
  | partial_tree_to_string _ NONE = "?"

(* end fei add *)

(* fei modifies some definitions *)

datatype named_thm = FindThm of partial_tree option
                   | FoundThm of string * HolKernel.thm

(*
metis_tac NONE
metis_tac (SOME (Lcons (FindThm NONE, NONE)))  // not needed I think
metis_tac (SOME (Lcons (FindThm (SOME (Abs (NONE, NONE))), NONE)))
metis_tac (SOME (Lcons (FindThm (SOME (Abs (SOME (TypeOf NONE), NONE))), NONE)))
metis_tac (SOME (Lcons
  (FindThm (SOME (Abs (SOME (TypeOf (SOME (Atom xxx)), NONE)))),
   NONE)))
metis_tac (SOME (Lcons
  (FindThm (SOME (Abs (SOME (TypeOf (SOME (Atom xxx)), SOME (Atom yyy))))),
   NONE)))
metis_tac (SOME (Lcons
  (FoundThm (name,thm),
   NONE)))
metis_tac (SOME (Lcons
  (FoundThm (name,thm),
   SOME Lnil)))

*)

(*type named_thm = string * HolKernel.thm
val name_of : named_thm -> string = #1
val thm_of : named_thm -> HolKernel.thm = #2*)

fun name_of(FindThm tm) = "SEARCH_TERM: " ^ (partial_tree_to_string Parse.term_to_string tm)
  | name_of(FoundThm (st, th)) = st
fun thm_of(FindThm _) = RL_Lib.die("thm_of unknown theorem")
  | thm_of(FoundThm (st, th)) = th

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

  | metis_tac of (named_thm partial_list option)
  | rw of (named_thm partial_list option)
  | fs of (named_thm partial_list option)
  | rfs of (named_thm partial_list option)
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

  | mp_tac of (named_thm partial_list option)
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
(*
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
  *)

(* fei add here *)
(* TODO: need filtering non-Thm types? should I use DB.find, which is string->list *)
fun search_theorem_by_term NONE = RL_Lib.die("search_theorem with incomplete term")
  | search_theorem_by_term (SOME t) =
      let val term_string = partial_tree_to_string Parse.term_to_string (SOME t)
          val searches = DB.find(term_string)
          val len = List.length(searches)
      in if len < 10
         then
           (List.map (fn ((s1, s2),(thm,_,_)) => (s1 ^ "." ^ s2, thm)) searches)
           @ List.take(all_theorems, 10 - len)
         else
           List.map (fn ((s1, s2),(thm,_,_)) => (s1 ^ "." ^ s2, thm))
           (List.take(searches, 10))
      end

fun myterm_to_term (NONE) = RL_Lib.die("myterm_to_term on incomplete term")
  | myterm_to_term (SOME (Atom t)) = t
  | myterm_to_term (SOME (Comb (t1, t2))) =
      let val t1' = myterm_to_term t1
          val t2' = myterm_to_term t2
      in Term.mk_comb (t1', t2')
      end
  | myterm_to_term (SOME (Abs (s, TypeOf t1, t2))) =
      let val t1' = myterm_to_term t1
          val t2' = myterm_to_term t2
      in Term.mk_abs ((Term.mk_var (s, (Term.type_of t1'))), t2')
      end

(* TODO: generate unique string for var_name *)
fun generate_term_actions atoms tmo counter (k: partial_tree option -> tactic) =
  case tmo of
     NONE => List.map (fn t => k(SOME t)) (atoms @
         [Abs ("g_" ^ Int.toString(counter), TypeOf NONE, NONE), Comb (NONE, NONE)])
   | SOME (Abs (s, TypeOf tm1, tm2)) =>
       if is_tree_complete tm1
       then let val para = Atom (Term.mk_var(s, Term.type_of(myterm_to_term tm1)))
                val new_atoms = atoms @ [para]
            in generate_term_actions new_atoms tm2 (counter+1)
               (fn tm2' => k(SOME(Abs (s, TypeOf tm1, tm2'))))
            end
       else generate_term_actions atoms tm1 (counter+1)
            (fn tm1' => k(SOME(Abs (s, TypeOf tm1', tm2))))
   | SOME (Comb (tm1, tm2)) =>
       if is_tree_complete tm1
       then generate_term_actions atoms tm2 (counter+1)
            (fn tm2' => k(SOME(Comb (tm1, tm2'))))
       else generate_term_actions atoms tm1 (counter+1)
            (fn tm1' => k(SOME(Comb (tm1', tm2))))
   | SOME (Atom _) => RL_Lib.die("generate_term_actions reach complete leaf")

fun generate_single_theorem_actions atoms lso (k: named_thm partial_list option -> tactic) =
  case lso of
     NONE => (generate_term_actions atoms NONE 0
              (fn tmo => k(SOME(Lcons(FindThm tmo, SOME Lnil)))))
   | SOME Lnil => RL_Lib.die("tactic_actions for complete action")
   | SOME (Lcons (head, lso')) => case head of
        FoundThm _ => RL_Lib.die("tactic_actions for complete action")
      | FindThm tmo => if is_tree_complete tmo
                       then List.map (fn t => k(SOME(Lcons(FoundThm t, lso')))) (search_theorem_by_term tmo)
                       else generate_term_actions atoms tmo 0 (fn tmo' => k(SOME(Lcons(FindThm tmo', lso'))))

(* TODO filter out repeted theorems *)
fun generate_theorem_actions atoms lso (k: named_thm partial_list option -> tactic) =
  case lso of
     NONE => (generate_term_actions atoms NONE 0
              (fn tmo => k(SOME(Lcons(FindThm tmo, NONE))))) @ [k(SOME Lnil)]
   | SOME Lnil => RL_Lib.die("tactic_actions for complete action")
   | SOME (Lcons (head, lso')) => case head of
        FoundThm _ => generate_theorem_actions atoms lso' (fn t => k(SOME (Lcons (head, t))))
      | FindThm tmo => if is_tree_complete tmo
                       then List.map (fn t => k(SOME(Lcons(FoundThm t, lso')))) (search_theorem_by_term tmo)
                       else generate_term_actions atoms tmo 0 (fn tmo' => k(SOME(Lcons(FindThm tmo', lso'))))
in

fun tactic_actions goal_state t =
  let val terms = RL_Goal_manager.terms_of_current_goal goal_state
      val atoms = List.map (fn t => Atom t) terms
  in case t of
       metis_tac lso => generate_theorem_actions atoms lso metis_tac
     | rw lso => generate_theorem_actions atoms lso rw
     | fs lso => generate_theorem_actions atoms lso fs
     | rfs lso => generate_theorem_actions atoms lso rfs
     | mp_tac lso => generate_single_theorem_actions atoms lso mp_tac
     | rpt NONE => List.map (rpt o SOME) top_level_tactics
     | rpt (SOME t) => List.map (rpt o SOME) (tactic_actions goal_state t)
     | _ => RL_Lib.die("tactic_actions: invariant failure")
  end

end

(* fei add end here *)
(*
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
*)
end
