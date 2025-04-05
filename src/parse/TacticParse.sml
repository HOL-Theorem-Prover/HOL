structure TacticParse :> TacticParse =
struct

open Lib

type 'a delim = int * int * 'a
datatype expr
  = EmptyE
  | ParenE of expr delim * bool
  | TupleE of expr delim list * bool
  | ListE of expr delim list * bool
  | IdentE of string
  | OpaqueE
  | InfixE of expr delim * string delim * expr delim
  | AppE of expr delim list

val infixes =
  map (fn x => (x, 0, false)) ["++", "&&", "|->", "THEN", "THEN1",
    "THENL", "THEN_LT", "THENC", "ORELSE", "ORELSE_LT", "ORELSEC", "THEN_TCL",
    "ORELSE_TCL", "?>", "|>", "|>>", "||>", "||->",
    ">>", ">-", ">|", "\\\\", ">>>", ">>-", "??", ">~", ">>~", ">>~-"] @
  [("by", 8, false), ("suffices_by", 8, false), ("$", 1, true)]

fun getPrec EmptyE = 10
  | getPrec (ParenE _) = 10
  | getPrec (TupleE _) = 10
  | getPrec (ListE _) = 10
  | getPrec (IdentE _) = 10
  | getPrec OpaqueE = 0
  | getPrec (InfixE (_, (_, _, s), _)) =
    #2 (Option.valOf (List.find (fn x => #1 x = s) infixes))
  | getPrec (AppE _) = 9

fun parseSMLSimple body = let
  val pos = ref 0
  fun cur () = String.sub (body, !pos) handle Subscript => #"\000"
  fun next () = pos := !pos + 1
  fun takeWhile f = if f (cur ()) then (next (); takeWhile f) else ()
  fun ws () = takeWhile Char.isSpace
  fun isIdRest c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"
  val isIdSym = Char.contains "'_!%&$#+-/:<=>?@\\~`^|*"
  val _ = ws ()
  fun finishString () = case cur () of
    #"\000" => ()
  | #"\"" => next ()
  | #"\\" => (next (); case cur () of
      #"\n" => (next (); ws (); (case cur () of #"\\" => next () | _ => ()); finishString ())
    | _ => (next (); finishString ()))
  | _ => (next (); finishString ())
  fun finishComment () = case cur () of
    #"\000" => ()
  | #"*" => (next (); if cur () = #")" then next () else finishComment ())
  | #"(" => (next (); if cur () = #"*" then (next (); finishComment ()) else (); finishComment ())
  | _ => (next (); finishComment ())
  fun finishId () = if cur () <> #"." then () else let
    val c = (next (); cur ())
    in
      if isIdSym c then (takeWhile isIdSym; finishId ()) else
      if Char.isAlpha c then (takeWhile isIdRest; finishId ()) else
      pos := !pos - 1
    end

  datatype token = EOF | OpaqueTk | IdentTk | Symbol of char
  fun token () = (ws (); case cur () of
    #"\000" => (!pos, EOF)
  | #"\"" => (!pos, (next (); finishString (); OpaqueTk))
  | #"(" => let
    val start = !pos
    val _ = next ()
    in if cur () = #"*" then (next (); finishComment (); token ()) else (start, Symbol #"(") end
  | c => (!pos, (next ();
    if Char.contains ")[]{},;" c then Symbol c else
    if isIdSym c then (takeWhile isIdSym; finishId (); IdentTk) else
    if Char.isAlpha c then (takeWhile isIdRest; finishId (); IdentTk) else
    OpaqueTk)))
  fun ident start = String.substring (body, start, !pos - start)

  val lookahead = ref NONE
  val token = fn () => case !lookahead of
    NONE => token ()
  | SOME tk => (lookahead := NONE; tk)
  fun unread tk = lookahead := SOME tk

  fun opaqueDelimited ds = let
    val tk as (start, tk') = token ()
    fun pop _ [] = (unread tk; start)
      | pop tgt (d::ds) =
        if tgt = d then
          case ds of [] => !pos | _ => opaqueDelimited ds
        else pop tgt ds
    val r = case tk' of
      EOF => start
    | Symbol #"(" => opaqueDelimited (#")" :: ds)
    | Symbol #")" => pop #")" ds
    | Symbol #"[" => opaqueDelimited (#"]" :: ds)
    | Symbol #"]" => pop #"]" ds
    | Symbol #"{" => opaqueDelimited (#"}" :: ds)
    | Symbol #"}" => pop #"}" ds
    | IdentTk =>
      (case ident start of
        "let" => opaqueDelimited (#"E" :: ds)
      | "end" => pop #"E" ds
      | _ => opaqueDelimited ds)
    | _ => opaqueDelimited ds
    in r end

  fun peekInfix () = let
    val (start, tk) = token ()
    val r = case tk of
      IdentTk => let
      val s = ident start
      in List.find (fn x => #1 x = s) infixes end
    | _ => NONE
    in unread (start, tk); (start, r) end

  exception OpaqueUndelimited
  fun primaryExpr () =
    case token () of
      (start, Symbol #"(") => ((case (expression (), token ()) of
        ((_, _, EmptyE), (stop, Symbol #")")) => (start, stop+1, TupleE ([], true))
      | (e, (stop, Symbol #")")) => (start, stop+1, ParenE (e, true))
      | (e, (_, Symbol #",")) => finishTuple start [e]
      | (e, (stop, tk)) => (unread (stop, tk); (start, stop, ParenE (e, false))))
      handle OpaqueUndelimited => (start, opaqueDelimited [#")"], OpaqueE))
    | (start, Symbol #"[") => ((case (expression (), token ()) of
        ((_, _, EmptyE), (stop, Symbol #"]")) => (start, stop+1, ListE ([], true))
      | (e, (stop, Symbol #"]")) => (start, stop+1, ListE ([e], true))
      | (e, (_, Symbol #",")) => finishList start [e]
      | (e, (stop, tk)) => (unread (stop, tk); (start, stop, ListE ([e], false))))
      handle OpaqueUndelimited => (start, opaqueDelimited [#"]"], OpaqueE))
    | (start, Symbol #"{") => (start, opaqueDelimited [#"}"], OpaqueE)
    | (start, IdentTk) => (case ident start of
        "let" => (start, opaqueDelimited [#"E"], OpaqueE)
      | "fn" => raise OpaqueUndelimited
      | "handle" => raise OpaqueUndelimited
      | "case" => raise OpaqueUndelimited
      | "if" => raise OpaqueUndelimited
      | s =>
        if List.exists (fn x => #1 x = s) infixes then
          (unread (start, IdentTk); (start, start, EmptyE))
        else (start, !pos, IdentE s))
    | (start, OpaqueTk) => (start, !pos, OpaqueE)
    | (pos, tk) => (unread (pos, tk); (pos, pos, EmptyE))
  and finishTuple start rest =
    case (expression (), token ()) of
      (e, (stop, Symbol #")")) => (start, stop+1, TupleE (rev (e :: rest), true))
    | (e, (_, Symbol #",")) => finishTuple start (e :: rest)
    | (e, (stop, tk)) => (unread (stop, tk); (start, stop, TupleE (rev (e :: rest), false)))
  and finishList start rest =
    case (expression (), token ()) of
      (e, (stop, Symbol #"]")) => (start, stop+1, ListE (rev (e :: rest), true))
    | (e, (_, Symbol #",")) => finishList start (e :: rest)
    | (e, (stop, tk)) => (unread (stop, tk); (start, stop, ListE (rev (e :: rest), false)))
  and parseApp acc =
    case peekInfix () of
      (_, SOME _) => acc
    | (_, NONE) => (case primaryExpr () of
        (_, _, EmptyE) => acc
      | rhs => parseApp (rhs :: acc))
  and appExpr () = let
    val lhs = primaryExpr ()
    val r = case parseApp [] of
      [] => lhs
    | revargs as ((_,stop,_) :: _) => (#1 lhs, stop, AppE (lhs :: rev revargs))
    in r end
  and tail prec lhs =
    case peekInfix () of
      (start, SOME (opr, prec', _)) => if prec' < prec then lhs else let
      val stop = !pos
      val _ = token ()
      val rhs = tail2 prec' (appExpr ())
      in tail prec (#1 lhs, #2 rhs, InfixE (lhs, (start, stop, opr), rhs)) end
    | _ => lhs
  and tail2 prec rhs =
    case peekInfix () of
      (start, SOME (_, prec', rassoc)) =>
      if prec' + (if rassoc then 1 else 0) > prec then
        tail2 prec (tail (prec + (if prec' > prec then 1 else 0)) rhs)
      else rhs
    | _ => rhs
  and expression () = tail 0 (appExpr ())
  val tk as (start, _) = token ()
  val _ = unread tk
  val e = expression () handle OpaqueUndelimited =>
    (start, opaqueDelimited [#"\000"], OpaqueE)
  in e end

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

val parseTacticBlock: string -> (int * int) tac_expr = let
  fun tr (start,stop,_) = (start, stop)
  fun trPrec (p as (_, _, e)) = (getPrec e, tr p)
  fun group tac a b = if topSpan b = SOME a then b else Group (tac, a, b)
  fun grouped b f e = group b (tr e) (f e)
  fun paren true _ e' = e'
    | paren false e e' = RepairGroup (tr e, "", e', ")")
  fun simplifys (start, stop, e) acc = case e of
    ParenE (e', true) => simplifys e' acc
  | InfixE (lhs, (_, _, ">>"), rhs) => simplifys lhs (simplifys rhs acc)
  | InfixE (lhs, (_, _, "++"), rhs) => simplifys lhs (simplifys rhs acc)
  | InfixE (lhs, (_, _, "\\\\"), rhs) => simplifys lhs (simplifys rhs acc)
  | InfixE (lhs, (_, _, "THEN"), rhs) => simplifys lhs (simplifys rhs acc)
  | AppE [(_, _, IdentE "EVERY"), (_, _, ListE (args, _))] =>
    foldr (uncurry simplifys) acc args
  | _ => grouped true simplify (start, stop, e) :: acc

  and simplifyTacList e = case #3 e of
    ListE (rhs, _) => List (tr e, map (grouped true simplify) rhs)
  | _ => OOpaque (trPrec e)

  and simplifyFirst e acc = case #3 e of
    ParenE (e', true) => simplifyFirst e' acc
  | InfixE (lhs, (_, _, "ORELSE"), rhs) => simplifyFirst lhs (simplifyFirst rhs acc)
  | AppE [(_, _, IdentE "FIRST"), (_, _, ListE (args, _))] =>
    foldr (uncurry simplifyFirst) acc args
  | _ => grouped true simplify e :: acc

  and simplifyThenLT e acc = case #3 e of
    ParenE (e', p) => paren p e (simplifyThenLT e' acc)
  | InfixE (lhs, (_, _, ">>>"), rhs) => simplifyThenLT lhs (simplifysLT rhs acc)
  | InfixE (lhs, (_, _, "THEN_LT"), rhs) => simplifyThenLT lhs (simplifysLT rhs acc)
  | _ => ThenLT (simplify e, acc)

  and simplifyThenL lhs rhs =
    simplifyThenLT lhs [LNullOk $ LTacsToLT $ simplifyTacList rhs]

  and simplify e = case #3 e of
    EmptyE => RepairEmpty (true, tr e, "ALL_TAC")
  | ParenE (e', p) => paren p e (simplify e')
  | InfixE (lhs, (_, _, ">>"),   rhs) => Then (simplifys lhs (simplifys rhs []))
  | InfixE (lhs, (_, _, "++"),   rhs) => Then (simplifys lhs (simplifys rhs []))
  | InfixE (lhs, (_, _, "\\\\"), rhs) => Then (simplifys lhs (simplifys rhs []))
  | InfixE (lhs, (_, _, "THEN"), rhs) => Then (simplifys lhs (simplifys rhs []))
  | InfixE (lhs, (_, _, ">|"),    rhs) => group true (tr e) (simplifyThenL lhs rhs)
  | InfixE (lhs, (_, _, "THENL"), rhs) => group true (tr e) (simplifyThenL lhs rhs)
  | InfixE (lhs, (_, _, ">-"),    rhs) => simplifyThenLT lhs [LThen1 (grouped true simplify rhs)]
  | InfixE (lhs, (_, _, "THEN1"), rhs) => simplifyThenLT lhs [LThen1 (grouped true simplify rhs)]
  | InfixE ((_,_, TupleE ([lhs, _], _)), (_, _, ">>-"), rhs) =>
    simplifyThenLT lhs [LThen1 (grouped true simplify rhs)]
  | InfixE (lhs, (_, _, ">>>"),     rhs) => simplifyThenLT lhs (simplifysLT rhs [])
  | InfixE (lhs, (_, _, "THEN_LT"), rhs) => simplifyThenLT lhs (simplifysLT rhs [])
  | InfixE (lhs, (_, _, "ORELSE"), rhs) => First (simplifyFirst lhs (simplifyFirst rhs []))
  | InfixE (lhs, (_, _, ">~"),  pat) => simplifyThenLT lhs [LSelectGoal (tr pat)]
  | InfixE (lhs, (_, _, ">>~"), pat) => simplifyThenLT lhs [LSelectGoals (tr pat)]
  | InfixE (lhs, (_, _, ">>~-"), (_, _, TupleE ([pat, rhs], _))) =>
    simplifyThenLT lhs [LSelectThen (
      group false (tr pat) (Rename (tr pat)),
      group true (tr rhs) $ Then (simplifys rhs [First []]))]
  | InfixE (lhs, (_, _, "by"), rhs) =>
    ThenLT (Subgoal (tr lhs), [LThen1 (grouped true simplify rhs)])
  | InfixE (lhs, (_, _, "suffices_by"), rhs) => let
    val p = tr lhs
    val r = ThenLT (
      group false p (ThenLT (Subgoal p, [LReverse])),
      [LThen1 (grouped true simplify rhs)])
    in r end
  | AppE [(_, _, IdentE "subgoal"), rhs] => group true (tr e) (Subgoal (tr rhs))
  | AppE [(_, _, IdentE "sg"), rhs] => group true (tr e) (Subgoal (tr rhs))
  | AppE [(_, _, IdentE "REVERSE"), rhs] => group true (tr e) (simplifyThenLT rhs [LReverse])
  | AppE [(_, _, IdentE "reverse"), rhs] => group true (tr e) (simplifyThenLT rhs [LReverse])
  | AppE [(_, _, IdentE "TRY"), rhs] => group true (tr e) (Try (simplify rhs))
  | AppE [(_, _, IdentE "REPEAT"), rhs] => group true (tr e) (Repeat (simplify rhs))
  | AppE [(_, _, IdentE "rpt"), rhs] => group true (tr e) (Repeat (simplify rhs))
  | AppE [(_, _, IdentE "EVERY"), (_, _, ListE (args, _))] =>
    Then (foldr (uncurry simplifys) [] args)
  | AppE [(_, _, IdentE "FIRST"), (_, _, ListE (args, _))] =>
    First (foldr (uncurry simplifyFirst) [] args)
  | AppE [(_, _, IdentE "MAP_EVERY"), f, (_, _, ListE (args, _))] =>
    MapEvery (tr f, map (fn e => OOpaque (trPrec e)) args)
  | AppE [(_, _, IdentE "MAP_FIRST"), f, (_, _, ListE (args, _))] =>
    MapFirst (tr f, map (fn e => OOpaque (trPrec e)) args)
  | AppE [(_, _, IdentE "RENAME_TAC"), pat] => group true (tr e) (Rename (tr pat))
  | IdentE "ALL_TAC" => group true (tr e) (Then [])
  | IdentE "all_tac" => group true (tr e) (Then [])
  | _ => Opaque (trPrec e)

  and simplifyLThen (start, stop, e) acc = case e of
    ParenE (e, true) => simplifyLThen e acc
  | InfixE (lhs, (_, _, ">>"), rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
  | InfixE (lhs, (_, _, "++"), rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
  | InfixE (lhs, (_, _, "\\\\"), rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
  | InfixE (lhs, (_, _, "THEN"), rhs) => simplifyLThen lhs (grouped true simplify rhs :: acc)
  | _ => LThen (simplifyLT (start, stop, e), acc)

  and simplifyLFirst (start, stop, e) acc = case e of
    ParenE (e, true) => simplifyLFirst e acc
  | InfixE (lhs, (_, _, "ORELSE_LT"), rhs) => simplifyLFirst lhs (simplifyLFirst rhs acc)
  | AppE [(_, _, IdentE "FIRST_LT"), (_, _, ListE (args, _))] =>
    foldr (uncurry simplifyLFirst) acc args
  | _ => grouped true simplifyLT (start, stop, e) :: acc

  and simplifysLT e acc = case #3 e of
    EmptyE => RepairEmpty (true, tr e, "ALL_LT") :: acc
  | ParenE (e, true) => simplifysLT e acc
  | ParenE (e', false) => paren false e (simplifyLT e') :: acc
  | InfixE (lhs, (_, _, ">>"),   rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
  | InfixE (lhs, (_, _, "++"),   rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
  | InfixE (lhs, (_, _, "\\\\"), rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
  | InfixE (lhs, (_, _, "THEN"), rhs) => group true (tr e) (simplifyLThen lhs [simplify rhs]) :: acc
  | InfixE (lhs, (_, _, ">|"),    rhs) =>
    simplifysLT lhs (grouped false (LNullOk o LTacsToLT o simplifyTacList) rhs :: acc)
  | InfixE (lhs, (_, _, "THENL"), rhs) =>
    simplifysLT lhs (grouped false (LNullOk o LTacsToLT o simplifyTacList) rhs :: acc)
  | InfixE (lhs, (_, _, ">>>"),     rhs) => simplifysLT lhs (simplifysLT rhs acc)
  | InfixE (lhs, (_, _, "THEN_LT"), rhs) => simplifysLT lhs (simplifysLT rhs acc)
  | InfixE (lhs, (_, _, "ORELSE_LT"), rhs) =>
    group true (tr e) (LFirst (simplifyLFirst lhs (simplifyLFirst rhs []))) :: acc
  | AppE [(_, _, IdentE "TACS_TO_LT"), rhs] =>
    group true (tr e) (LTacsToLT (simplifyTacList rhs)) :: acc
  | AppE [(_, _, IdentE "NULL_OK_LT"), rhs] =>
    group true (tr e) (LNullOk (simplifyLT rhs)) :: acc
  | AppE [(_, _, IdentE "ALLGOALS"), rhs] => group true (tr e) (LAllGoals (simplify rhs)) :: acc
  | AppE [(_, _, IdentE "TRYALL"),   rhs] => group true (tr e) (LAllGoals $ Try (simplify rhs)) :: acc
  | AppE [(_, _, IdentE "NTH_GOAL"), rhs, n] => group true (tr e) (LNthGoal (simplify rhs, tr n)) :: acc
  | AppE [(_, _, IdentE "LASTGOAL"), rhs] => group true (tr e) (LLastGoal (simplify rhs)) :: acc
  | AppE [(_, _, IdentE "HEADGOAL"), rhs] => group true (tr e) (LHeadGoal (simplify rhs)) :: acc
  | AppE [(_, _, IdentE "SPLIT_LT"), n, (_, _, TupleE ([lhs, rhs], _))] =>
    group true (tr e) (LSplit (tr n, grouped true simplifyLT lhs, grouped true simplifyLT rhs)) :: acc
  | AppE [(_, _, IdentE "TRY_LT"), rhs] => group true (tr e) (LTry (simplifyLT rhs)) :: acc
  | AppE [(_, _, IdentE "REPEAT_LT"), rhs] => group true (tr e) (LRepeat (simplifyLT rhs)) :: acc
  | AppE [(_, _, IdentE "EVERY_LT"), (_, _, ListE (args, _))] =>
    foldr (uncurry simplifysLT) acc args
  | AppE [(_, _, IdentE "FIRST_LT"), (_, _, ListE (args, _))] =>
    group true (tr e) (LFirst (foldr (uncurry simplifyLFirst) [] args)) :: acc
  | AppE [(_, _, IdentE "SELECT_LT_THEN"), lhs, rhs] =>
    group true (tr e) (LSelectThen (grouped true simplify lhs, grouped true simplify rhs)) :: acc
  | AppE [(_, _, IdentE "SELECT_LT"), lhs] =>
    group true (tr e) (LSelectThen (grouped true simplify lhs, Then [])) :: acc
  | IdentE "REVERSE_LT" => group true (tr e) LReverse :: acc
  | IdentE "ALL_LT" => group true (tr e) (LThenLT []) :: acc
  | _ => LOpaque (trPrec e) :: acc

  and simplifyLT e = LThenLT (simplifysLT e [])

  in simplify o parseSMLSimple end

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

fun printTacsAsE s [] = ""
  | printTacsAsE s (l::ls) = let
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
    fun mkInfixl s acc [] = Option.valOf acc
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
      | go (LSelectThen (e1, e2)) = TApp ("SELECT_LT_THEN", [go e1, go e2])
      | go (List (p, ls)) = TList (map go ls)
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
  val getPrec = fn "by" => 8 | "suffices_by" => 8 | _ => 0
  fun printTree prec (TAtom s) = print s
    | printTree prec (TOpaque (p, s)) = parenIf (p < prec) (fn () => print s)
    | printTree prec (TInfix (e1, s, e2)) = let
      val p = getPrec s
      val _ = parenIf (getPrec s < prec) (fn () => (
        printTree p e1; newline (); app print [s, " "]; printTree (p+1) e2))
      in () end
    | printTree prec (TApp (s, args)) =
      parenIf (9 < prec) (fn () => (
        print s; app (fn e => (print " "; printTree 10 e)) args))
    | printTree prec (TList []) = print "[]"
    | printTree prec (TList (a::l)) = (
      print "["; printTree 0 a;
      app (fn e => (print ", "; printTree 0 e)) l; print "]")
    | printTree prec (TTuple []) = print "()"
    | printTree prec (TTuple (a::l)) = (
      print "("; printTree 0 a;
      app (fn e => (print ", "; printTree 0 e)) l; print ")")
  fun goL l = case optTree $ mkTree l of
      TAtom "ALL_TAC" => NONE
    | t => SOME t
  fun goLL l [] = (
      case goL l of
        SOME t => (print "e("; printTree 0 t; print ");\n")
      | NONE => ())
    | goLL l (l'::ls) = (
      case goL l of
        SOME t => (print "val _ = e("; printTree 0 t; print ");\n")
      | NONE => ();
      goLL l' ls)
  in goLL l ls; concat $ rev (!r) end

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

datatype tac_frag_mid
  = FNextFirst
  | FNextTacsToLT
  | FNextSplit
  | FNextSelect

datatype tac_frag_close
  = FClose
  | FCloseFirst
  | FCloseRepeat

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
      group p (mbracket FClose FNextTacsToLT FOpenTacsToLT (fn one =>
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
    | go (FFMid e :: l) acc = raise Bind
    | go (FFClose e :: l) acc = raise Bind
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
  and slice1 sp (true, true) a acc = cons a acc
    | slice1 _ _ (FGroup (sp as (l, r), ls)) acc =
      if stop <= l orelse r <= start then acc else slice sp ls acc
    | slice1 sp (true, false) (FBracket (start, ls, _, _)) acc =
      slice sp ls $ cons (FFOpen start) acc
    | slice1 sp (false, false) (FBracket (_, ls, _, _)) acc = slice sp ls acc
    | slice1 sp (false, true) (FBracket (e as (start, ls, stop, a))) acc =
      if sliceClose then cons (FFClose stop) $ slice sp ls acc else
        (case start of
          FOpen => separateE sp ls I acc
        | FOpenThen1 => separateE sp ls (cons (FAtom (First []))) acc
        | FOpenNullOk => join sp ls I acc
        | FOpenNthGoal _ => join sp ls I acc
        | FOpenLastGoal => join sp ls I acc
        | FOpenHeadGoal => join sp ls I acc
        | _ => cons (FAtom a) acc)
    | slice1 sp (inclStart, inclStop) (e as FMBracket (opn, mid, cls, ls, a)) acc =
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
    | slice1 sp _ a acc = cons a acc
  val (ll, l) = slice sp (linearize isAtom e) ([], [])
  in rev (rev l :: ll) end

end
