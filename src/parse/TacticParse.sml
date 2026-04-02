structure TacticParse :> TacticParse =
struct

open Lib
open HOLSourceAST

fun identName (Ident {id = (_, s), ...}) = SOME s
  | identName _ = NONE

(* Flatten curried App chain: App(App(f,a1),a2) -> [f, a1, a2] *)
fun flattenApp e = let
  fun go (App (f, x)) acc = go f (x :: acc)
    | go e acc = e :: acc
  in go e [] end

(* Extract elements from a list expression *)
fun listElems (List {elems = {args, ...}, ...}) = SOME args
  | listElems _ = NONE

(* Extract elements from a tuple expression *)
fun tupleElems (Tuple {elems = {args, ...}, ...}) = SOME args
  | tupleElems _ = NONE

(* Check if parens/brackets are closed *)
fun isClosed (Parens {right, ...}) = Option.isSome right
  | isClosed (List {right, ...}) = Option.isSome right
  | isClosed (Tuple {right, ...}) = Option.isSome right
  | isClosed _ = true

(* Strip one layer of closed parens *)
fun stripParens (Parens {exp, right = SOME _, ...}) = SOME exp
  | stripParens _ = NONE

fun getPrec (ExpEmpty _) = 10
  | getPrec (Parens _) = 10
  | getPrec (Tuple _) = 10
  | getPrec (List _) = 10
  | getPrec (Ident _) = 10
  | getPrec (Infix {id = (_, s), ...}) =
    (case Binarymap.peek (HOLSourceParser.initialScope, s) of
      NONE => 0
    | SOME (prec, _) => prec)
  | getPrec (App _) = 9
  | getPrec _ = 0

(* --- tac_expr datatype (unchanged) --- *)

datatype 'a tac_expr
  = Then of 'a tac_expr list
  | ThenLT of 'a tac_expr * 'a tac_expr list
  | Subgoal of 'a
  | First of 'a tac_expr list
  | Try of 'a tac_expr
  | Repeat of 'a tac_expr
  | MapEvery of 'a * 'a tac_expr list
  | MapFirst of 'a * 'a tac_expr list
  | Rename of 'a
  | Opaque of int * 'a

  | LThen of 'a tac_expr * 'a tac_expr list
  | LThenLT of 'a tac_expr list
  | LThen1 of 'a tac_expr
  | LTacsToLT of 'a tac_expr
  | LNullOk of 'a tac_expr
  | LFirst of 'a tac_expr list
  | LFirstLT of 'a tac_expr
  | LSelectGoal of 'a
  | LSelectGoals of 'a
  | LAllGoals of 'a tac_expr
  | LNthGoal of 'a tac_expr * 'a
  | LLastGoal of 'a tac_expr
  | LHeadGoal of 'a tac_expr
  | LSplit of 'a * 'a tac_expr * 'a tac_expr
  | LReverse
  | LTry of 'a tac_expr
  | LRepeat of 'a tac_expr
  | LSelectThen of 'a tac_expr * 'a tac_expr
  | LOpaque of int * 'a

  | List of 'a * 'a tac_expr list
  | Group of bool * 'a * 'a tac_expr
  | RepairEmpty of bool * 'a * string
  | RepairGroup of 'a * string * 'a tac_expr * string
  | OOpaque of int * 'a

fun isTac (Then _) = true
  | isTac (ThenLT _) = true
  | isTac (Subgoal _) = true
  | isTac (First _) = true
  | isTac (Try _) = true
  | isTac (Repeat _) = true
  | isTac (MapEvery _) = true
  | isTac (MapFirst _) = true
  | isTac (Rename _) = true
  | isTac (Opaque _) = true
  | isTac (Group (_, _, e)) = isTac e
  | isTac (RepairEmpty (_, _, s)) = s = "ALL_TAC"
  | isTac (RepairGroup (_, _, e, _)) = isTac e
  | isTac _ = false

fun topSpan (LSelectGoal p) = SOME p
  | topSpan (LSelectGoals p) = SOME p
  | topSpan (List (p, _)) = SOME p
  | topSpan (Group (_, p, _)) = SOME p
  | topSpan (RepairEmpty (_, p, _)) = SOME p
  | topSpan (RepairGroup (p, _, _, _)) = SOME p
  | topSpan (Opaque (_, p)) = SOME p
  | topSpan (LOpaque (_, p)) = SOME p
  | topSpan (OOpaque (_, p)) = SOME p
  | topSpan _ = NONE

(* --- Tactic parsing from HOLSourceAST.exp --- *)

val parseTacticBlock: exp -> (int * int) tac_expr = let
  val tr = expSpan
  fun trPrec e = (getPrec e, tr e)
  fun group tac a b = if topSpan b = SOME a then b else Group (tac, a, b)
  fun grouped b f e = group b (tr e) (f e)
  fun paren e e' =
    if isClosed e then e'
    else RepairGroup (tr e, "", e', ")")

  (* Match an infix expression with a specific operator *)
  fun matchInfix (Infix {left, id = (_, s), right}) = SOME (left, s, right)
    | matchInfix _ = NONE

  (* Match App with a head identifier, returning args *)
  fun matchApp e = case flattenApp e of
      f :: args => Option.map (fn s => (s, args)) (identName f)
    | _ => NONE

  fun simplifys e acc = case stripParens e of
      SOME e' => simplifys e' acc
    | NONE => case matchInfix e of
      SOME (lhs, ">>", rhs) => simplifys lhs (simplifys rhs acc)
    | SOME (lhs, "++", rhs) => simplifys lhs (simplifys rhs acc)
    | SOME (lhs, "\\\\", rhs) => simplifys lhs (simplifys rhs acc)
    | SOME (lhs, "THEN", rhs) => simplifys lhs (simplifys rhs acc)
    | _ => case matchApp e of
      SOME ("EVERY", [le]) => (case listElems le of
        SOME args => foldr (uncurry simplifys) acc args
      | NONE => grouped true simplify e :: acc)
    | _ => grouped true simplify e :: acc

  and simplifyTacList e = case listElems e of
      SOME args => List (tr e, map (grouped true simplify) args)
    | NONE => OOpaque (trPrec e)

  and simplifyFirst e acc = case stripParens e of
      SOME e' => simplifyFirst e' acc
    | NONE => case matchInfix e of
      SOME (lhs, "ORELSE", rhs) => simplifyFirst lhs (simplifyFirst rhs acc)
    | _ => case matchApp e of
      SOME ("FIRST", [le]) => (case listElems le of
        SOME args => foldr (uncurry simplifyFirst) acc args
      | NONE => grouped true simplify e :: acc)
    | _ => grouped true simplify e :: acc

  and simplifyThenLT e acc = case e of
      Parens {exp = e', ...} => paren e (simplifyThenLT e' acc)
    | _ => case matchInfix e of
      SOME (lhs, ">>>", rhs) => simplifyThenLT lhs (simplifysLT rhs acc)
    | SOME (lhs, "THEN_LT", rhs) => simplifyThenLT lhs (simplifysLT rhs acc)
    | _ => ThenLT (simplify e, acc)

  and simplifyThenL lhs rhs =
    simplifyThenLT lhs [LNullOk $ LTacsToLT $ simplifyTacList rhs]

  and simplify e = case e of
    (* Try stripping parens first *)
      Parens {exp = e', ...} => paren e (simplify e')
    (* Empty expression *)
    | ExpEmpty _ => RepairEmpty (true, tr e, "ALL_TAC")
    (* Infix operators *)
    | _ => case matchInfix e of
      SOME (lhs, ">>", rhs) => Then (simplifys lhs (simplifys rhs []))
    | SOME (lhs, "++", rhs) => Then (simplifys lhs (simplifys rhs []))
    | SOME (lhs, "\\\\", rhs) => Then (simplifys lhs (simplifys rhs []))
    | SOME (lhs, "THEN", rhs) => Then (simplifys lhs (simplifys rhs []))
    | SOME (lhs, ">|", rhs) => group true (tr e) (simplifyThenL lhs rhs)
    | SOME (lhs, "THENL", rhs) => group true (tr e) (simplifyThenL lhs rhs)
    | SOME (lhs, ">-", rhs) => simplifyThenLT lhs [LThen1 (grouped true simplify rhs)]
    | SOME (lhs, "THEN1", rhs) => simplifyThenLT lhs [LThen1 (grouped true simplify rhs)]
    | SOME (lhs, ">>-", rhs) => (case tupleElems lhs of
        SOME [lhs', _] => simplifyThenLT lhs' [LThen1 (grouped true simplify rhs)]
      | _ => Opaque (trPrec e))
    | SOME (lhs, ">>>", rhs) => simplifyThenLT lhs (simplifysLT rhs [])
    | SOME (lhs, "THEN_LT", rhs) => simplifyThenLT lhs (simplifysLT rhs [])
    | SOME (lhs, "ORELSE", rhs) => First (simplifyFirst lhs (simplifyFirst rhs []))
    | SOME (lhs, ">~", pat) => simplifyThenLT lhs [LSelectGoal (tr pat)]
    | SOME (lhs, ">>~", pat) => simplifyThenLT lhs [LSelectGoals (tr pat)]
    | SOME (lhs, ">>~-", rhs) => (case tupleElems rhs of
        SOME [pat, rhs'] =>
          simplifyThenLT lhs [LSelectThen (
            group false (tr pat) (Rename (tr pat)),
            group true (tr rhs') $ Then (simplifys rhs' [First []]))]
      | _ => Opaque (trPrec e))
    | SOME (lhs, "by", rhs) =>
        ThenLT (Subgoal (tr lhs), [LThen1 (grouped true simplify rhs)])
    | SOME (lhs, "suffices_by", rhs) => let
        val p = tr lhs
        in ThenLT (
          group false p (ThenLT (Subgoal p, [LReverse])),
          [LThen1 (grouped true simplify rhs)]) end
    (* Application forms *)
    | _ => case matchApp e of
      SOME ("subgoal", [rhs]) => group true (tr e) (Subgoal (tr rhs))
    | SOME ("sg", [rhs]) => group true (tr e) (Subgoal (tr rhs))
    | SOME ("REVERSE", [rhs]) => group true (tr e) (simplifyThenLT rhs [LReverse])
    | SOME ("reverse", [rhs]) => group true (tr e) (simplifyThenLT rhs [LReverse])
    | SOME ("TRY", [rhs]) => group true (tr e) (Try (simplify rhs))
    | SOME ("REPEAT", [rhs]) => group true (tr e) (Repeat (simplify rhs))
    | SOME ("rpt", [rhs]) => group true (tr e) (Repeat (simplify rhs))
    | SOME ("EVERY", [le]) => (case listElems le of
        SOME args => Then (foldr (uncurry simplifys) [] args)
      | NONE => Opaque (trPrec e))
    | SOME ("FIRST", [le]) => (case listElems le of
        SOME args => First (foldr (uncurry simplifyFirst) [] args)
      | NONE => Opaque (trPrec e))
    | SOME ("MAP_EVERY", [f, le]) => (case listElems le of
        SOME args => MapEvery (tr f, map (fn e => OOpaque (trPrec e)) args)
      | NONE => Opaque (trPrec e))
    | SOME ("MAP_FIRST", [f, le]) => (case listElems le of
        SOME args => MapFirst (tr f, map (fn e => OOpaque (trPrec e)) args)
      | NONE => Opaque (trPrec e))
    | SOME ("RENAME_TAC", [pat]) => group true (tr e) (Rename (tr pat))
    | SOME ("ALL_TAC", []) => group true (tr e) (Then [])
    | SOME ("all_tac", []) => group true (tr e) (Then [])
    | _ => Opaque (trPrec e)

  and simplifyLThen e acc = case stripParens e of
      SOME e' => simplifyLThen e' acc
    | _ => case matchInfix e of
      SOME (lhs, ">>", rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
    | SOME (lhs, "++", rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
    | SOME (lhs, "\\\\", rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
    | SOME (lhs, "THEN", rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
    | _ => LThen (simplifyLT e, acc)

  and simplifyLFirst e acc = case stripParens e of
      SOME e' => simplifyLFirst e' acc
    | _ => case matchInfix e of
      SOME (lhs, "ORELSE_LT", rhs) => simplifyLFirst lhs (simplifyLFirst rhs acc)
    | _ => case matchApp e of
      SOME ("FIRST_LT", [le]) => (case listElems le of
        SOME args => foldr (uncurry simplifyLFirst) acc args
      | NONE => grouped true simplifyLT e :: acc)
    | _ => grouped true simplifyLT e :: acc

  and simplifysLT e acc = case e of
      ExpEmpty _ => RepairEmpty (true, tr e, "ALL_LT") :: acc
    | Parens {exp = e', right = SOME _, ...} => simplifysLT e' acc
    | Parens {exp = e', right = NONE, ...} => paren e (simplifyLT e') :: acc
    | _ => case matchInfix e of
      SOME (lhs, ">>", rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
    | SOME (lhs, "++", rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
    | SOME (lhs, "\\\\", rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
    | SOME (lhs, "THEN", rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
    | SOME (lhs, ">|", rhs) =>
        simplifysLT lhs (grouped false (LNullOk o LTacsToLT o simplifyTacList) rhs :: acc)
    | SOME (lhs, "THENL", rhs) =>
        simplifysLT lhs (grouped false (LNullOk o LTacsToLT o simplifyTacList) rhs :: acc)
    | SOME (lhs, ">>>", rhs) => simplifysLT lhs (simplifysLT rhs acc)
    | SOME (lhs, "THEN_LT", rhs) => simplifysLT lhs (simplifysLT rhs acc)
    | SOME (lhs, "ORELSE_LT", rhs) =>
        group true (tr e) (LFirst (simplifyLFirst lhs (simplifyLFirst rhs []))) :: acc
    | _ => case matchApp e of
      SOME ("TACS_TO_LT", [rhs]) =>
        group true (tr e) (LTacsToLT (simplifyTacList rhs)) :: acc
    | SOME ("NULL_OK_LT", [rhs]) =>
        group true (tr e) (LNullOk (simplifyLT rhs)) :: acc
    | SOME ("ALLGOALS", [rhs]) => group true (tr e) (LAllGoals (simplify rhs)) :: acc
    | SOME ("TRYALL", [rhs]) => group true (tr e) (LAllGoals $ Try (simplify rhs)) :: acc
    | SOME ("NTH_GOAL", [rhs, n]) => group true (tr e) (LNthGoal (simplify rhs, tr n)) :: acc
    | SOME ("LASTGOAL", [rhs]) => group true (tr e) (LLastGoal (simplify rhs)) :: acc
    | SOME ("HEADGOAL", [rhs]) => group true (tr e) (LHeadGoal (simplify rhs)) :: acc
    | SOME ("SPLIT_LT", [n, tup]) => (case tupleElems tup of
        SOME [lhs, rhs] =>
          group true (tr e) (LSplit (tr n, grouped true simplifyLT lhs, grouped true simplifyLT rhs)) :: acc
      | _ => LOpaque (trPrec e) :: acc)
    | SOME ("TRY_LT", [rhs]) => group true (tr e) (LTry (simplifyLT rhs)) :: acc
    | SOME ("REPEAT_LT", [rhs]) => group true (tr e) (LRepeat (simplifyLT rhs)) :: acc
    | SOME ("FIRST_LT", [rhs]) => group true (tr e) (LFirstLT (simplify rhs)) :: acc
    | SOME ("EVERY_LT", [le]) => (case listElems le of
        SOME args => foldr (uncurry simplifysLT) acc args
      | NONE => LOpaque (trPrec e) :: acc)
    | SOME ("SELECT_LT_THEN", [lhs, rhs]) =>
        group true (tr e) (LSelectThen (grouped true simplify lhs, grouped true simplify rhs)) :: acc
    | SOME ("SELECT_LT", [lhs]) =>
        group true (tr e) (LSelectThen (grouped true simplify lhs, Then [])) :: acc
    | SOME ("REVERSE_LT", []) => group true (tr e) LReverse :: acc
    | SOME ("ALL_LT", []) => group true (tr e) (LThenLT []) :: acc
    | _ => LOpaque (trPrec e) :: acc

  and simplifyLT e = LThenLT (simplifysLT e [])

  in simplify end

fun mapTacExpr {start, stop, repair} = let
  fun trF isTac a (f: unit -> 'd) = let
    val b = start isTac a
    val r = f ()
    in (stop isTac b, r) end
  fun tr isTac a = fst (trF isTac a I)
  fun go (RepairEmpty (tac, p, s)) = let
      val (a, ()) = trF tac p (fn () => repair p s)
      in RepairEmpty (tac, a, s) end
    | go (Then ls) = Then (map go ls)
    | go (ThenLT (e, ls)) = ThenLT (go e, map go ls)
    | go (Subgoal t) = Subgoal (tr false t)
    | go (First ls) = First (map go ls)
    | go (Try e) = Try (go e)
    | go (Repeat e) = Repeat (go e)
    | go (Rename p) = Rename (tr false p)
    | go (MapEvery (f, ls)) = MapEvery (tr false f, map go ls)
    | go (MapFirst (f, ls)) = MapFirst (tr false f, map go ls)
    | go (Opaque (prec, p)) = Opaque (prec, tr true p)
    | go (LThenLT ls) = LThenLT (map go ls)
    | go (LThen (e, ls)) = LThen (go e, map go ls)
    | go (LThen1 e) = LThen1 (go e)
    | go (LTacsToLT e) = LTacsToLT (go e)
    | go (LNullOk e) = LNullOk (go e)
    | go (LFirst ls) = LFirst (map go ls)
    | go (LSelectGoal p) = LSelectGoal (tr false p)
    | go (LSelectGoals p) = LSelectGoals (tr false p)
    | go (LAllGoals e) = LAllGoals (go e)
    | go (LNthGoal (e, n)) = LNthGoal (go e, tr false n)
    | go (LLastGoal e) = LLastGoal (go e)
    | go (LHeadGoal e) = LHeadGoal (go e)
    | go (LSplit (n, e1, e2)) = LSplit (tr false n, go e1, go e2)
    | go LReverse = LReverse
    | go (LTry e) = LTry (go e)
    | go (LRepeat e) = LRepeat (go e)
    | go (LFirstLT e) = LFirstLT (go e)
    | go (LSelectThen (e1, e2)) = LSelectThen (go e1, go e2)
    | go (List (p, ls)) = List (trF false p (fn () => map go ls))
    | go (LOpaque (prec, p)) = LOpaque (prec, tr true p)
    | go (Group (tac, p, e)) = let
      val (p', e') = trF tac p (fn () => go e)
      in Group (tac, p', e') end
    | go (RepairGroup (p, s1, e, s2)) = let
      val (p', (_, e', _)) = trF false p (fn () => (repair p s1, go e, repair p s2))
      in RepairGroup (p', s1, e', s2) end
    | go (OOpaque (prec, p)) = OOpaque (prec, tr false p)
  in go end

fun printTacsAsE s ls = let
  datatype tree
    = TAtom of string
    | TOpaque of int * string
    | TInfix of tree * string * tree
    | TApp of string * tree list
    | TList of tree list
    | TTuple of tree list
  val mkTree = let
    fun sub (start, stop) = String.concat [
      String.substring (s, start, stop-start)]
    fun mkInfixl _ acc [] = Option.valOf acc
      | mkInfixl s NONE (a::l) = mkInfixl s (SOME a) l
      | mkInfixl s (SOME t) (a::l) = mkInfixl s (SOME (TInfix (t, s, a))) l
    val mkInfixl = fn s => mkInfixl s NONE
    fun go (RepairEmpty (_, _, s)) = TAtom s
      | go (Then []) = TAtom "ALL_TAC"
      | go (Then ls) = mkInfixl ">>" (map go ls)
      | go (LThenLT []) = TAtom "ALL_LT"
      | go (LThenLT ls) = mkInfixl ">>>" (map go ls)
      | go (ThenLT (e, ls)) = mkInfixl ">>>" (map go (e::ls))
      | go (LThen1 e) = TApp ("THEN1_LT", [go e])
      | go (Subgoal t) = TApp ("sg", [TAtom (sub t)])
      | go (First []) = TAtom "NO_TAC"
      | go (First ls) = mkInfixl "ORELSE" (map go ls)
      | go (Try e) = TApp ("TRY", [go e])
      | go (Repeat e) = TApp ("rpt", [go e])
      | go (Rename p) = TApp ("RENAME_TAC", [TAtom (sub p)])
      | go (MapEvery (f, ls)) = TApp ("MAP_EVERY", [TAtom (sub f), TList (map go ls)])
      | go (MapFirst (f, ls)) = TApp ("MAP_FIRST", [TAtom (sub f), TList (map go ls)])
      | go (LThen (e, ls)) = mkInfixl ">>" (map go (e::ls))
      | go (LTacsToLT e) = TApp ("TACS_TO_LT", [go e])
      | go (LNullOk e) = TApp ("NULL_OK_LT", [go e])
      | go (LFirst []) = TAtom "NO_LT"
      | go (LFirst ls) = mkInfixl "ORELSE_LT" (map go ls)
      | go (LSelectGoal p) = TApp ("SELECT_GOAL_LT", [TAtom (sub p)])
      | go (LSelectGoals p) = TApp ("SELECT_GOALS_LT", [TAtom (sub p)])
      | go (LAllGoals e) = TApp ("ALLGOALS", [go e])
      | go (LNthGoal (e, n)) = TApp ("NTH_GOAL", [go e, TAtom (sub n)])
      | go (LLastGoal e) = TApp ("LASTGOAL", [go e])
      | go (LHeadGoal e) = TApp ("HEADGOAL", [go e])
      | go (LSplit (n, e1, e2)) = TApp ("SPLIT_LT", [TAtom (sub n), TTuple [go e1, go e2]])
      | go LReverse = TAtom "REVERSE_LT"
      | go (LTry e) = TApp ("TRY_LT", [go e])
      | go (LRepeat e) = TApp ("REPEAT_LT", [go e])
      | go (LFirstLT e) = TApp ("FIRST_LT", [go e])
      | go (LSelectThen (e1, e2)) = TApp ("SELECT_LT_THEN", [go e1, go e2])
      | go (List (_, ls)) = TList (map go ls)
      | go (Group (_, _, e)) = go e
      | go (RepairGroup (_, _, e, _)) = go e
      | go (Opaque (prec, p)) = TOpaque (prec, sub p)
      | go (LOpaque (prec, p)) = TOpaque (prec, sub p)
      | go (OOpaque (prec, p)) = TOpaque (prec, sub p)
    in go end
  val optTree = let
    fun go (TInfix (e1, ">>>", TApp ("NULL_OK_LT", [TApp ("TACS_TO_LT", [e2])]))) =
        TInfix (go e1, ">|", go e2)
      | go (TInfix (e1, ">>>", TAtom "REVERSE_LT")) = TApp ("reverse", [go e1])
      | go (TInfix (e1, ">>>", TApp ("THEN1_LT", [e2]))) =
        (case e1 of
          TApp ("sg", [p]) => TInfix (p, "by", go e2)
        | TInfix (TApp ("sg", [p]), ">>>", TAtom "REVERSE_LT") =>
          TInfix (p, "suffices_by", go e2)
        | _ => TInfix (go e1, ">-", go e2))
      | go (TInfix (e1, ">>>", TApp ("SELECT_GOAL_LT", [e2]))) =
        TInfix (go e1, ">~", go e2)
      | go (TInfix (e1, ">>>", TApp ("SELECT_GOALS_LT", [e2]))) =
        TInfix (go e1, ">>~", go e2)
      | go (TInfix (e1, ">>>", TApp ("SELECT_LT_THEN", [TApp ("RENAME_TAC", [p]), e2]))) =
        TInfix (go e1, ">>~-", TTuple [p, go e2])
      | go (TInfix (TAtom "NO_TAC", "ORELSE", e)) = go e
      | go (TInfix (e, "ORELSE", TAtom "NO_TAC")) = go e
      | go (TInfix (TAtom "NO_LT", "ORELSE_LT", e)) = go e
      | go (TInfix (e, "ORELSE_LT", TAtom "NO_LT")) = go e
      | go (TInfix (TAtom "ALL_TAC", ">>", e)) = go e
      | go (TInfix (e, ">>", TAtom "ALL_TAC")) = go e
      | go (TInfix (TAtom "ALL_LT", ">>>", e)) = go e
      | go (TInfix (e, ">>>", TAtom "ALL_LT")) = go e
      | go (TApp ("SELECT_LT_THEN", [e, TAtom "NO_TAC"])) = TApp ("SELECT_LT", [e])
      | go (TApp ("ALLGOALS", [TApp ("TRY", [e])])) = TApp ("TRYALL", [e])
      | go (t as TAtom _) = t
      | go (t as TOpaque _) = t
      | go (TInfix (e1, s, e2)) = TInfix (go e1, s, go e2)
      | go (TApp (s, es)) = TApp (s, map go es)
      | go (TList ls) = TList (map go ls)
      | go (TTuple ls) = TTuple (map go ls)
    in go end
  val r = ref []
  fun print s = r := s :: !r
  val indent = ref 1
  fun newline () = (print "\n"; funpow (!indent) (fn () => print "  ") ())
  fun parenIf b f = if b then
    (print "("; indent := !indent + 1; f (); indent := !indent - 1; print ")")
  else f ()
  val getPrec' = fn "by" => 8 | "suffices_by" => 8 | _ => 0
  fun printTree _ (TAtom s) = print s
    | printTree prec (TOpaque (p, s)) = parenIf (p < prec) (fn () => print s)
    | printTree prec (TInfix (e1, s, e2)) = let
      val p = getPrec' s
      val _ = parenIf (getPrec' s < prec) (fn () => (
        printTree p e1; newline (); app print [s, " "]; printTree (p+1) e2))
      in () end
    | printTree prec (TApp (s, args)) =
      parenIf (9 < prec) (fn () => (
        print s; app (fn e => (print " "; printTree 10 e)) args))
    | printTree _ (TList []) = print "[]"
    | printTree _ (TList (a::l)) = (
      print "["; printTree 0 a;
      app (fn e => (print ", "; printTree 0 e)) l; print "]")
    | printTree _ (TTuple []) = print "()"
    | printTree _ (TTuple (a::l)) = (
      print "("; printTree 0 a;
      app (fn e => (print ", "; printTree 0 e)) l; print ")")
  fun goL l = case optTree $ mkTree l of
      TAtom "ALL_TAC" => NONE
    | t => SOME t
  fun goT [] = ()
    | goT [t] = (print "e("; printTree 0 t; print ");\n")
    | goT (t::ts) = (print "val _ = e("; printTree 0 t; print ");\n"; goT ts)
  in goT (List.mapPartial goL ls); concat $ rev (!r) end

datatype tac_frag_open
  = FOpen
  | FOpenThen1
  | FOpenFirst
  | FOpenRepeat
  | FOpenTacsToLT
  | FOpenNullOk
  | FOpenNthGoal of int * int
  | FOpenLastGoal
  | FOpenHeadGoal
  | FOpenSplit of int * int
  | FOpenSelect
  | FOpenFirstLT

datatype tac_frag_mid
  = FNextFirst
  | FNextTacsToLT
  | FNextSplit
  | FNextSelect

datatype tac_frag_close
  = FClose
  | FCloseFirst
  | FCloseRepeat
  | FCloseFirstLT

datatype tac_frag
  = FFOpen of tac_frag_open
  | FFMid of tac_frag_mid
  | FFClose of tac_frag_close
  | FAtom of (int * int) tac_expr
  | FGroup of (int * int) * tac_frag list
  | FBracket of tac_frag_open * tac_frag list * tac_frag_close * (int * int) tac_expr
  | FMBracket of
    tac_frag_open * tac_frag_mid * tac_frag_close * tac_frag list list * (int * int) tac_expr

fun linearize isAtom e = let
  fun group a f (one, acc) = (fn (one, l) => (one, FGroup (a, rev l) :: acc)) (f (one, []))
  fun span e = case topSpan e of NONE => I | SOME sp => group sp
  fun goList [] acc = acc
    | goList (e::ls) acc = goList ls (go e acc)
  and go e (acc as (one, acc')) = if isAtom e then (false, FAtom e :: acc') else let
    fun bracket2 stop f start (one, acc) = (false, FBracket (start, rev (snd (f one)), stop, e) :: acc)
    val bracket = bracket2 FClose
    fun mbracket stop mid start f (one, acc) =
      (false, FMBracket (start, mid, stop, f one, e) :: acc)
    fun asTac f (true, acc) = f (true, acc)
      | asTac f acc = bracket (K $ f (true, [])) FOpen acc
    val r = case e of
      Then ls => goList ls acc
    | ThenLT (e, ls) => asTac (goList ls o go e) acc
    | First [] => (true, FAtom (First []) :: acc')
    | First (e::ls) =>
      asTac (mbracket FClose FNextFirst FOpenFirst (fn one =>
        map (fn e => snd (go e (one, []))) (e::ls))) acc
    | Try e => asTac (bracket (fn one => go e (one, [])) FOpenFirst) acc
    | Repeat e => asTac (bracket2 FCloseRepeat (fn one => go e (one, [])) FOpenRepeat) acc
    | MapEvery (_, []) => acc
    | MapFirst (_, []) => (true, FAtom (First []) :: acc')
    | LThenLT ls => goList ls acc
    | LThen (e, ls) => goList ls $ go e acc
    | LThen1 e => span e (bracket (fn _ => go e (true, [])) FOpenThen1) acc
    | LTacsToLT (List (p, e::ls)) =>
      group p (mbracket FClose FNextTacsToLT FOpenTacsToLT (fn _ =>
        map (fn e => snd (go e (true, []))) (e::ls))) acc
    | LNullOk e => bracket (fn one => go e (one, [])) FOpenNullOk acc
    | LFirst [] => (true, FAtom (LFirst []) :: acc')
    | LFirst (e::ls) =>
      mbracket FCloseFirst FNextFirst FOpenFirst (fn one =>
        map (fn e => snd (go e (one, []))) (e::ls)) acc
    | LAllGoals e => go e acc
    | LNthGoal (e, n) => bracket (fn _ => go e (false, [])) (FOpenNthGoal n) acc
    | LLastGoal e => bracket (fn _ => go e (false, [])) FOpenLastGoal acc
    | LHeadGoal e => bracket (fn _ => go e (false, [])) FOpenHeadGoal acc
    | LSplit (n, e1, e2) =>
      mbracket FClose FNextSplit (FOpenSplit n) (fn _ =>
        map (fn e => snd (go e (false, []))) [e1, e2]) acc
    | LReverse => (one, FAtom LReverse :: acc')
    | LTry e => bracket (fn one => go e (one, [])) FOpenFirst acc
    | LRepeat e => bracket (fn one => go e (one, [])) FOpenRepeat acc
    | LFirstLT e => bracket2 FCloseFirstLT (fn one => go e (one, [])) FOpenFirstLT acc
    | LSelectThen (e1, e2) =>
      mbracket FClose FNextSelect FOpenSelect (fn _ =>
        map (fn f => snd (f (false, []))) [
          go e1, span e2 $ bracket (fn _ => go e2 (false, [])) FOpen]) acc
    | List _ => raise Bind
    | RepairEmpty _ => acc
    | Group       (_, p, e)    => group p (go e) acc
    | RepairGroup (p, _, e, _) => group p (go e) acc
    | LTacsToLT _    => (false, FAtom e :: acc')
    | MapEvery _     => (false, FAtom e :: acc')
    | MapFirst _     => (false, FAtom e :: acc')
    | Rename _       => (false, FAtom e :: acc')
    | Subgoal _      => (false, FAtom e :: acc')
    | LSelectGoal _  => (false, FAtom e :: acc')
    | LSelectGoals _ => (false, FAtom e :: acc')
    | Opaque _       => (false, FAtom e :: acc')
    | LOpaque _      => (false, FAtom e :: acc')
    | OOpaque _      => (false, FAtom e :: acc')
    in r end
  in rev $ snd (go e (true, [])) end

val unlinearize = let
  fun go [] acc = acc
    | go (FFOpen e :: l) (stk, acc) = go l ((e, acc) :: stk, [])
    | go (FFMid _ :: _) _ = raise Bind
    | go (FFClose _ :: _) _ = raise Bind
    | go (FAtom a :: l) (s, acc) = go l (s, a :: acc)
    | go (FGroup (_, e) :: l) acc = go l (go e acc)
    | go (FBracket (_, _, _, a) :: l) (stk, acc) = go l (stk, a :: acc)
    | go (FMBracket (_, _, _, _, a) :: l) (stk, acc) = go l (stk, a :: acc)
  fun mkThen [] acc = Then (rev acc)
    | mkThen (e :: l) acc =
      if isTac e then mkThen l (e::acc) else mkThenL (Then (rev acc)) l [e]
  and mkThenL lhs [] acc = ThenLT (lhs, rev acc)
    | mkThenL lhs (e::l) acc =
      if isTac e then mkThen l [e, ThenLT (lhs, rev acc)] else mkThenL lhs l (e::acc)
  fun mkLThenL [] acc = LThenLT (rev acc)
    | mkLThenL (e :: l) acc =
      if isTac e then mkLThen (LThenLT (rev acc)) l [e] else mkLThenL l (e::acc)
  and mkLThen lhs [] acc = ThenLT (lhs, rev acc)
    | mkLThen lhs (e::l) acc =
      if isTac e then mkLThen lhs l (e::acc) else mkLThenL l [e, LThen (lhs, rev acc)]
  fun mkOpen FOpen acc = mkThen acc []
    | mkOpen FOpenThen1 acc = LHeadGoal (mkThen acc [])
    | mkOpen FOpenFirst acc = Try (mkThen acc [])
    | mkOpen FOpenRepeat acc = Repeat (mkThen acc [])
    | mkOpen FOpenTacsToLT acc = LHeadGoal (mkThen acc [])
    | mkOpen FOpenNullOk acc = LNullOk (mkLThenL acc [])
    | mkOpen (FOpenNthGoal n) acc = LNthGoal (mkThen acc [], n)
    | mkOpen FOpenLastGoal acc = LLastGoal (mkThen acc [])
    | mkOpen FOpenHeadGoal acc = LHeadGoal (mkThen acc [])
    | mkOpen (FOpenSplit n) acc = LSplit (n, mkLThenL acc [], LThenLT [])
    | mkOpen FOpenSelect acc = LAllGoals $ Try (mkThen acc [])
    | mkOpen FOpenFirstLT acc = LAllGoals $ Try (mkThen acc [])
  fun finish ([], acc) = mkThen (rev acc) []
    | finish ((e, acc') :: stk, acc) =
      finish (stk, mkOpen e (rev acc) :: acc')
  in fn ls => finish $ go ls ([], []) end

fun printFragsAsE s ls = printTacsAsE s (map unlinearize ls)

fun sliceTacticBlock start stop sliceClose sp e = let
  fun spanOf (FAtom a) = topSpan a
    | spanOf (FGroup (p, _)) = SOME p
    | spanOf _ = NONE
  fun spanOfL [a] = spanOf a
    | spanOfL _ = NONE
  fun isAtom a = case topSpan a of
    NONE => false
  | SOME (l, r) => stop <= l orelse r <= start orelse (start <= l andalso r <= stop)
  fun cons a (ll, l) = (ll,a::l)
  fun slice _ [] acc = acc
    | slice sp (a :: ls) acc = let
      val sp as (l, r) = Option.getOpt (spanOf a, sp)
      in
        if stop <= l then acc else
        if r <= start then slice sp ls acc else
        slice sp ls (slice1 sp (start <= l, r <= stop) a acc)
      end
  and separateE sp ls f = (fn (ll, l) => (rev l::ll, [])) o f o slice sp ls
  and join sp ls f = f o slice sp ls
  and slice1 _ (true, true) a acc = cons a acc
    | slice1 _ _ (FGroup (sp as (l, r), ls)) acc =
      if stop <= l orelse r <= start then acc else slice sp ls acc
    | slice1 sp (true, false) (FBracket (start, ls, _, _)) acc =
      slice sp ls $ cons (FFOpen start) acc
    | slice1 sp (false, false) (FBracket (_, ls, _, _)) acc = slice sp ls acc
    | slice1 sp (false, true) (FBracket (start, ls, stop, a)) acc =
      if sliceClose then cons (FFClose stop) $ slice sp ls acc else
        (case start of
          FOpen => separateE sp ls I acc
        | FOpenThen1 => separateE sp ls (cons (FAtom (First []))) acc
        | FOpenNullOk => join sp ls I acc
        | FOpenNthGoal _ => join sp ls I acc
        | FOpenLastGoal => join sp ls I acc
        | FOpenHeadGoal => join sp ls I acc
        | _ => cons (FAtom a) acc)
    | slice1 sp (inclStart, inclStop) (e as FMBracket (opn, mid, cls, ls, _)) acc =
      if sliceClose then let
        fun go [] acc = if inclStop then cons (FFClose cls) acc else acc
          | go (a::ls) acc = let
            val sp1 as (l, r) = Option.getOpt (spanOfL a, sp)
            in
              if stop <= l then acc else
              if r <= start then go ls acc else
              go ls $ (if null ls then cons (FFMid mid) else I) $
              slice sp1 a acc
            end
        in go ls (if inclStart then cons (FFOpen opn) acc else acc) end
      else let
        fun find [] = NONE
          | find (a::ls) =
            case spanOfL a of
              NONE => find ls
            | SOME (l, r) =>
              if stop <= l then NONE else
              if r <= start then find ls else
              if l <= start andalso stop <= r then SOME ((l,r), a) else NONE
        val _ = case find ls of
        NONE => cons e acc
        | SOME (sp, a) => slice sp a acc
        in acc end
    | slice1 _ _ a acc = cons a acc
  val (ll, l) = slice sp (linearize isAtom e) ([], [])
  in rev (rev l :: ll) end

end
