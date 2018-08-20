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

fun is_list_complete NONE = false
  | is_list_complete (SOME l) =
      case (get_complete_list l) of
           NONE => false
         | (SOME _) => true

fun get_partial_list NONE = []
  | get_partial_list (SOME (Lcons (x, pl))) = x::(get_partial_list pl)
  | get_partial_list _ = RL_Lib.die("get_partial_list on completed list")

fun partial_list_to_string _ (NONE) = "{?}"
  | partial_list_to_string f (SOME pl) =
    case get_complete_list pl of
      NONE => String.concat["[", String.concatWith ", " (List.map f (get_partial_list (SOME pl))), ", {?}"]
    | SOME ls => String.concat["[", String.concatWith ", " (List.map f ls), "]"]

(* begin fei addition *)
datatype term_type = TypeOf of partial_tree option
and partial_tree =
    Comb of (partial_tree option) * (partial_tree option)
  | Abs  of string * (term_type) * (partial_tree option)
  | Atom of Abbrev.term

(* exception Add_To_Complete_Tree
fun add_term t (SOME (Comb (t1, t2))) = (SOME (Comb ((add_term t t1), t2))
                                        handle Add_To_Complete_Tree
                                        => SOME (Comb (t1, (add_term t t2))))
  | add_term t (SOME (Abs (t1, TypeOf t2, t3))) =
      (SOME (Abs (t1, TypeOf (add_term t t2), t3))
       handle Add_To_Complete_Tree
       => SOME (Abs (t1, TypeOf t2, add_term t t3)))
  | add_term t (SOME (Atom t1)) = raise Add_To_Complete_Tree
  | add_term t NONE = SOME t
 note there is unhandled exception for the whole function *)

fun is_tree_complete (SOME (Comb (t1, t2))) =
      is_tree_complete(t1) andalso is_tree_complete(t2)
  | is_tree_complete (SOME (Abs (t1, TypeOf t2, t3))) =
      is_tree_complete(t2) andalso is_tree_complete(t3)
  | is_tree_complete (SOME (Atom a)) = true
  | is_tree_complete NONE = false

(* NOTE: this function may throw HOL_ERR for ill-typed terms,
  *      the exception is captured by observation() and next_actions() function in
  *      RL_Experiment.sml to show the error message *)
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

(*
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
          then SOME ("\\" ^ (t1) ^ ":(" ^ (valOf t2') ^ ")=>" ^ (valOf t3'))
          else NONE
       end
  | get_complete_tree (SOME (Atom a)) =
       SOME (Parse.term_to_string a)
  | get_complete_tree NONE = NONE
  *)

fun partial_tree_to_string f (SOME (Comb (t1, t2))) =
      let val t1' = partial_tree_to_string f t1
          val t2' = partial_tree_to_string f t2
      in "(" ^ t1' ^ " " ^ t2' ^ ")"
      end
  | partial_tree_to_string f (SOME (Abs (t1, TypeOf t2, t3))) =
      let val t2' = partial_tree_to_string f t2
          val t3' = partial_tree_to_string f t3
      in "\\" ^ (t1) ^ ":(" ^ (t2') ^ ")=>" ^ t3'
      end
  | partial_tree_to_string f (SOME (Atom a)) = (f a)
  | partial_tree_to_string _ NONE = "?"
(* end fei addition *)

(* fei modifies this definitions *)
datatype named_thm = FindThm of (partial_tree option) partial_list option
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

fun name_of(FindThm tm) = "SEARCH_TERM: " ^ (partial_list_to_string
  (partial_tree_to_string Parse.term_to_string) tm)
  | name_of(FoundThm (st, th)) = st
fun thm_of(FindThm _) = RL_Lib.die("thm_of unknown theorem")
  | thm_of(FoundThm (st, th)) = th

val get_complete_named_thm_list = Option.map (List.map thm_of) o get_complete_list

(* NOTE: alternatively, use tactics that takes a term directly, not a term quotation *)
datatype tactic =
    gen_tac
  | qx_gen_tac of (partial_tree option)
  | qx_genl_tac of (partial_tree option partial_list option)

  | Induct
  | Induct_on of (partial_tree option)
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
  | Cases_on of (partial_tree option)
  | mp_tac of (named_thm partial_list option)
  | qexists_tac of (partial_tree option)

  (*
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

datatype sexp = Symbo of string
              | Sexps of sexp list

fun sexp_of_type ht =
      if Type.is_vartype ht
      then Sexps ((Symbo "VarType") :: (Symbo (Type.dest_vartype ht)) :: nil)
      else let val res = Type.dest_thy_type ht
               val sexpl = List.map sexp_of_type (#Args res)
           in Sexps ((Symbo "Type") :: (Symbo (#Thy res)) :: (Symbo (#Tyop res)) :: sexpl)
           end

fun sexp_of_term term = case (Term.dest_term term) of
      Term.VAR (s, ht) => Sexps ((Symbo "VAR") :: (Symbo s) :: (sexp_of_type ht) :: nil)
    | Term.CONST res =>
        Sexps ((Symbo "CONST") :: (Symbo (#Name res)) :: (Symbo (#Thy res)) :: (sexp_of_type (#Ty res)) :: nil)
    | Term.COMB (tm1, tm2) => Sexps ((Symbo "COMB") :: (sexp_of_term tm1) :: (sexp_of_term tm2) :: nil)
    | Term.LAMB (tm1, tm2) => Sexps ((Symbo "LAMB") :: (sexp_of_term tm1) :: (sexp_of_term tm2) :: nil)

fun sexp_of_taco (SOME(gen_tac)) = Symbo "gen_tac"
  | sexp_of_taco (SOME(qx_gen_tac tmo)) = Sexps ((Symbo "qx_gen_tac")::(sexp_of_tmo tmo)::nil)
  | sexp_of_taco (SOME(qx_genl_tac tmlo)) = Sexps ((Symbo "qx_genl_tac")::(sexp_of_tmlo tmlo)::nil)
  | sexp_of_taco (SOME(Induct)) = Symbo "Induct"
  | sexp_of_taco (SOME(Induct_on tmo)) = Sexps ((Symbo "Induct_on")::(sexp_of_tmo tmo)::nil)
  | sexp_of_taco (SOME(metis_tac thmlo)) = Sexps ((Symbo "metis_tac")::(sexp_of_thmlo thmlo)::nil)
  | sexp_of_taco (SOME(rw thmlo)) = Sexps ((Symbo "rw")::(sexp_of_thmlo thmlo)::nil)
  | sexp_of_taco (SOME(fs thmlo)) = Sexps ((Symbo "fs")::(sexp_of_thmlo thmlo)::nil)
  | sexp_of_taco (SOME(rfs thmlo)) = Sexps ((Symbo "rfs")::(sexp_of_thmlo thmlo)::nil)
  | sexp_of_taco (SOME(decide_tac)) = Symbo "decide_tac"
  | sexp_of_taco (SOME(pairarg_tac)) = Symbo "pairarg"
  | sexp_of_taco (SOME(var_eq_tac)) = Symbo "var_eq_tac"
  | sexp_of_taco (SOME(strip_tac)) = Symbo "strip_tac"
  | sexp_of_taco (SOME(CCONTR_TAC)) = Symbo "CCONTR_TAC"
  | sexp_of_taco (SOME(rpt taco)) = Sexps ((Symbo "rpt")::(sexp_of_taco taco)::nil)
  | sexp_of_taco (SOME(Cases)) = Symbo "Cases"
  | sexp_of_taco (SOME(Cases_on tmo)) = Sexps ((Symbo "Cases_on")::(sexp_of_tmo tmo)::nil)
  | sexp_of_taco (SOME(mp_tac thmlo)) = Sexps ((Symbo "mp_tac")::(sexp_of_thmlo thmlo)::nil)
  | sexp_of_taco (SOME(qexists_tac tmo)) = Sexps ((Symbo "qexists_tac")::(sexp_of_tmo tmo)::nil)
  | sexp_of_taco NONE = Symbo "?"
and sexp_of_thmlo (SOME(Lcons(nthm, thmlo))) = Sexps ((sexp_of_nthm nthm)::(sexp_of_thmlo thmlo)::nil)
  | sexp_of_thmlo (SOME Lnil) = Symbo "]"
  | sexp_of_thmlo NONE = Symbo "?"
and sexp_of_nthm (FindThm tmlo) = Sexps ((Symbo "FindThm")::(sexp_of_tmlo tmlo)::nil)
  | sexp_of_nthm (FoundThm (s, thm)) =
      let val (terml, term) = Thm.dest_thm thm
          val sexpl = List.map sexp_of_term terml
      in Sexps ((Symbo "FoundThm") :: (Symbo s) :: (sexp_of_term term) :: sexpl)
      end
and sexp_of_tmlo (SOME(Lcons(tmo, tmlo))) = Sexps ((sexp_of_tmo tmo)::(sexp_of_tmlo tmlo)::nil)
  | sexp_of_tmlo (SOME Lnil) = Symbo "]"
  | sexp_of_tmlo NONE = Symbo "?"
and sexp_of_tmo (SOME(Comb(tm1, tm2))) = Sexps ((Symbo "Comb")::(sexp_of_tmo tm1)::(sexp_of_tmo tm2)::nil)
  | sexp_of_tmo (SOME(Abs(s, TypeOf tm1, tm2))) =
      Sexps (Sexps((Symbo s) :: (Symbo "TypeOf") :: (sexp_of_tmo tm1)::nil) ::
      (sexp_of_tmo tm2)::nil)
  | sexp_of_tmo (SOME(Atom tm)) = sexp_of_term tm
  | sexp_of_tmo NONE = Symbo "?"

fun sexp_encode(Symbo str) = "0 " ^ str
  | sexp_encode(Sexps lst) = Int.toString(List.length(lst)) ^ " " ^
  (String.concatWith " " (List.map sexp_encode lst))

local
  fun dec1 (nil) = RL_Lib.die("ERROR: dec1 in sexp_decode: dec1 on empty string list")
    | dec1 ("0" :: nil) = RL_Lib.die("ERROR: dec1 in sexp_decode: 0 followed by empty list")
    | dec1 ("0" :: sym :: rest) = ((Symbo sym), rest)
    | dec1 (num :: rest) =
        case (Int.fromString num) of
            NONE => RL_Lib.die("ERROR: dec1 in sexp_decode: num is not a number")
          | SOME n => let val (strlist, sexplist) = decn(n, rest, [])
                      in ((Sexps (List.rev sexplist)), strlist)
                      end
  and decn (n: int, strlist, sexplist) =
        if (Int.< (n, 0)) then RL_Lib.die("ERROR: decn in sexp_decode: n is negative")
        else (if (n = 0) then (strlist, sexplist)
              else let val (sexp, rest) = dec1 strlist
                   in decn(n-1, rest, sexp :: sexplist)
                   end)
in
  fun sexp_decode str =
    let val strlist = String.tokens (fn c => c = #" ") str
        val (sexp, rest) = dec1 strlist
    in case rest of
            nil => sexp
          | _ => RL_Lib.die("ERROR: sexp_decode: has unfinished work but sexp is finished")
    end
end

(*

val a = Symbo "a"
val b = sexp_encode a
val c = sexp_decode b

val aa = Sexps [Symbo "a", Symbo "b"]
val bb = sexp_encode aa
val cc = sexp_decode bb

val aaa = Sexps [Sexps [Symbo "a"], Sexps [Symbo "b", Symbo "c"], Symbo "d"]
val bbb = sexp_encode aaa
val ccc = sexp_decode bbb

*)

local
  fun get_tmq tmo = [(HOLPP.ANTIQUOTE (myterm_to_term tmo))]
in
  fun option_term_tactic f tmo =
    if is_tree_complete tmo
    then SOME(f (get_tmq tmo))
    else NONE

  fun option_term_list_tactic f tmlo =
    Option.map (f o (List.map get_tmq)) (Option.mapPartial get_complete_list tmlo)
end

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
  | qx_gen_tac tmo => option_term_tactic bossLib.qx_gen_tac tmo
  | qx_genl_tac tmlo => option_term_list_tactic bossLib.qx_genl_tac tmlo
  | Induct => SOME bossLib.Induct
  | Induct_on tmo => option_term_tactic bossLib.Induct_on tmo
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
  | Cases_on tmo => option_term_tactic bossLib.Cases_on tmo
  | qexists_tac tmo => option_term_tactic bossLib.qexists_tac tmo

fun tactic_to_string t =
    case t of
      gen_tac => "gen_tac"
    | qx_gen_tac tmo => "qx_gen_tac " ^ (partial_tree_to_string Parse.term_to_string tmo)
    | qx_genl_tac tmlo => "qx_genl_tac " ^ (partial_list_to_string
                          (partial_tree_to_string Parse.term_to_string) tmlo)
    | Induct  => "induct"
    | Induct_on tmo => "induct_on " ^ (partial_tree_to_string Parse.term_to_string tmo)
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
    | Cases_on tmo => "Cases_on " ^ (partial_tree_to_string Parse.term_to_string tmo)
    | mp_tac ntlo => "mp_tac " ^ partial_list_to_string name_of ntlo
    | qexists_tac tmo => "qexists_tac " ^ (partial_tree_to_string Parse.term_to_string tmo)

datatype action =
    Tactic of tactic
  | Rotate
  | Back

fun action_to_string(Back) = "Back"
  | action_to_string(Rotate) = "Rotate"
  | action_to_string(Tactic t) = tactic_to_string t

val top_level_tactics =
  [gen_tac
  ,qx_gen_tac NONE
  ,qx_genl_tac NONE
  ,Induct
  ,Induct_on NONE
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
  ,Cases_on NONE
  ,mp_tac NONE
  ,qexists_tac NONE]

val top_level_actions =
  Back::Rotate::(List.map Tactic top_level_tactics)

local

(*
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
  *)

(* start fei addition *)
(*
datatype Constraint = Tany
                    | Tarrow of int
                    | Thol of Abbrev.hol_type

fun arrow_layer ht = use strip_fun function

fun type_comply _ Tany = true
  | type_comply (Atom tm) (Tarrow n) = (arrow_layer (Term.type_of tm) >= n)
  | type_comply _ (Tarrow n) = True
  | type_comply (Atom tm) (Thol ht) = ((Term.type_of tm) = ht)
  | type_comply (Abs (s, tm1, tm2)) (Thol ht) =
*)

fun is_fun ht =
  let val (htl, _) = boolSyntax.strip_fun ht
  in not (List.null htl)
  end

fun generate_term_actions terms tmo (k: partial_tree option -> tactic) =
  case tmo of (* if we need constraint, filter them here *)
     NONE => List.map (fn t => k(SOME t))
             (Abs("x", TypeOf NONE, NONE) :: Comb(NONE, NONE) :: (List.map Atom terms))
   | SOME (Abs (s, TypeOf tm1, tm2)) =>
       if is_tree_complete tm1
       then let val tm1_type = Term.type_of(myterm_to_term tm1)
                val tm1' = Term.variant (List.filter Term.is_var terms)
                           (Term.mk_var (s, tm1_type))
                val new_terms = tm1' :: terms
                val (name, _) = Term.dest_var tm1'
                val res = generate_term_actions new_terms tm2
                          (fn tm2' => k(SOME(Abs(name, TypeOf tm1, tm2'))))
            in (* possible extra extensions of tm1  *)
               if (tm2 = NONE) andalso (is_fun tm1_type)
               then k(SOME(Comb(tm1, NONE))) :: res
               else res
            end
       else generate_term_actions terms tm1
            (fn tm1' => k(SOME(Abs(s, TypeOf tm1', tm2))))
   | SOME (Comb (tm1, tm2)) =>
       if is_tree_complete tm1
       then generate_term_actions terms tm2
            (fn tm2' => k(SOME(Comb (tm1, tm2'))))
       else generate_term_actions terms tm1
            (fn tm1' => k(SOME(Comb (tm1', tm2))))
   | SOME (Atom _) => RL_Lib.die("generate_term_actions reach complete leaf")

fun generate_term_list_actions terms tmlo (k: (partial_tree option) partial_list option -> tactic) =
  case tmlo of
     NONE => k(SOME Lnil) :: (generate_term_actions terms NONE (fn t => k(SOME(Lcons(t, NONE)))))
   | SOME Lnil => RL_Lib.die("generate_term_list_actions reach complete list")
   | SOME (Lcons (tmo, tmlo')) =>
       if is_tree_complete tmo
       then let val tmo_type = Term.type_of(myterm_to_term tmo)
                val res = generate_term_list_actions terms tmlo' (fn t => k(SOME(Lcons(tmo, t))))
            in (* possible extra extensions of tmo *)
               if (tmlo' = NONE) andalso (is_fun tmo_type)
               then k(SOME(Lcons(SOME(Comb(tmo, NONE)), tmlo'))) :: res
               else res
            end
       else generate_term_actions terms tmo (fn t => k(SOME(Lcons(t,tmlo'))))

(* need filtering non-Thm types?
fun search_theorem_by_term NONE = RL_Lib.die("search_theorem with incomplete term")
  | search_theorem_by_term (SOME t) =
      let val real_term = myterm_to_term (SOME t)
          val searches = DB.match [] real_term
          val len = List.length(searches)
      in if len < 10
         then
           (List.map (fn ((s1, s2),(thm,_)) => (s1 ^ "." ^ s2, thm)) searches)
         else
           List.map (fn ((s1, s2),(thm,_)) => (s1 ^ "." ^ s2, thm))
           (List.take(searches, 10))
      end
      *)

fun search_theorem_by_term_from NONE _ = RL_Lib.die("search_theorem with incomplete term")
  | search_theorem_by_term_from (SOME t) NONE =
      let val real_term = myterm_to_term (SOME t)
      in DB.match [] real_term
      end
  | search_theorem_by_term_from (SOME t) (SOME thml) =
      let val real_term = myterm_to_term (SOME t)
      in DB.apropos_in real_term thml
      end

fun search_theorem_by_term_list NONE _ _ = RL_Lib.die("search_theorem with incomplete list of terms")
  | search_theorem_by_term_list (SOME Lnil) NONE excl =
      (* this is searching with NO restrictions *)
      let val all_thms = DB.listDB()
      in search_theorem_by_term_list (SOME Lnil) (SOME all_thms) excl
      end
  | search_theorem_by_term_list (SOME Lnil) (SOME thml) excl =
      let val filter = fn (_,(_,c)) => case c of DB.Def => false | _ => true
              (* filtering Def types, only allow Thm and Axm *)
          val filter1 = fn ((s1, s2),_) => not (List.exists (fn n => n=s1^"."^s2) excl)
              (* filtering thms in excl, because they are already in theorem list *)
          val real_thml = List.filter (fn t => filter t andalso filter1 t) thml
          val len = List.length real_thml
          val mapper = (fn ((s1, s2),(thm,_)) => (s1 ^"."^ s2, thm))
      in if len < 10
         then List.map mapper real_thml
         else List.map mapper (List.take (real_thml, 10))
      end
  | search_theorem_by_term_list (SOME(Lcons(hd, tl))) thml excl =
      let val thml' = search_theorem_by_term_from hd thml
      in search_theorem_by_term_list tl (SOME thml') excl
      end

fun generate_single_theorem_actions terms lso excl (k: named_thm partial_list option -> tactic) =
  case lso of
     NONE => (generate_term_list_actions terms NONE
              (fn tmlo => k(SOME(Lcons(FindThm tmlo, NONE)))))
   | SOME Lnil => RL_Lib.die("tactic_actions for complete action")
   | SOME (Lcons (head, lso')) => case head of
      (*  FoundThm _ => RL_Lib.die("tactic_actions for complete action") *)
        FoundThm _ => [k(SOME(Lcons(head,SOME Lnil)))]
      | FindThm tmlo =>
          if is_list_complete tmlo
          then List.map (fn t => k(SOME(Lcons(FoundThm t, lso'))))
               (search_theorem_by_term_list tmlo NONE excl)
          else generate_term_list_actions terms tmlo
               (fn tmlo' => k(SOME(Lcons(FindThm tmlo', lso'))))

fun generate_theorem_actions terms lso excl (k: named_thm partial_list option -> tactic) =
  case lso of
     NONE => (k(SOME Lnil) :: (generate_term_list_actions terms NONE
                               (fn tmlo => k(SOME(Lcons(FindThm tmlo, NONE))))))
   | SOME Lnil => RL_Lib.die("generate_theorem_actions for complete action")
   | SOME (Lcons (head, lso')) => case head of
        FoundThm (thn, thm) => generate_theorem_actions terms lso' (thn :: excl)
                               (fn t => k(SOME (Lcons (head, t))))
      | FindThm tmlo =>
          if is_list_complete tmlo
          then List.map (fn t => k(SOME(Lcons(FoundThm t, lso'))))
               (search_theorem_by_term_list tmlo NONE excl)
          else generate_term_list_actions terms tmlo
               (fn tmlo' => k(SOME(Lcons(FindThm tmlo', lso'))))

(* generate unique string for var_name
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

(* filter out repeted theorems *)
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
                       *)
in

fun tactic_actions goal_state t excl =
  let val terms = RL_Goal_manager.terms_of_current_goal goal_state
  in case t of
       metis_tac lso => generate_theorem_actions terms lso excl metis_tac
     | rw lso => generate_theorem_actions terms lso excl rw
     | fs lso => generate_theorem_actions terms lso excl fs
     | rfs lso => generate_theorem_actions terms lso excl rfs
     | mp_tac lso => generate_single_theorem_actions terms lso excl mp_tac
     | rpt NONE => List.map (rpt o SOME) top_level_tactics
     | rpt (SOME t) => List.map (rpt o SOME) (tactic_actions goal_state t excl)
     | qx_gen_tac tmo => generate_term_actions terms tmo qx_gen_tac
     | qx_genl_tac tmlo => generate_term_list_actions terms tmlo qx_genl_tac
     | Induct_on tmo => generate_term_actions terms tmo Induct_on
     | Cases_on tmo => generate_term_actions terms tmo Cases_on
     | qexists_tac tmo => generate_term_actions terms tmo qexists_tac
     | _ => RL_Lib.die("tactic_actions: invariant failure")
  end

end

(* fei add end here *)

end
