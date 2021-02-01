(**
  structure LassieParserLib
  Implements a parser from the intermediate language produced by
  SEMPRE into HOL4 tactics by looking them up in a map provided by
  TacticMap.sml
**)
structure LassieParserLib =
struct

  open Abbrev Tactical Manager Conv BoundedRewrites proofManagerLib;
  open LassieUtilsLib TacticMap;

  exception NoParseException of string;

  datatype SempreParse =
    HOLTactic of tactic
    | Command of unit -> proof
    | Subgoal of int
    | Termgoal of term frag list;

  val tacticMap = ref TacticMap.stdTree;

  val thmModifs = ["Once", "GSYM"];

  datatype token =
    Subg of int
    | Id of string
    | TermStart
    | TermEnd
    | LBrac
    | RBrac
    | ListStart
    | ListEnd
    | ListSep;

  fun lex (strs:string list) : (token * string list) option =
    case strs of
    [] =>  NONE
    | s1 :: strs =>
      case s1 of
       "(" => SOME (LBrac, strs)
      | ")" => SOME (RBrac, strs)
      | "[" => SOME (ListStart, strs)
      | "]" => SOME (ListEnd, strs)
      | "," => SOME (ListSep, strs)
      | "TERMSTART" => SOME (TermStart, strs)
      | "TERMEND" => SOME (TermEnd, strs)
      | "ALLGOALS" => SOME (Subg (~ 1), strs)
      | "TERMGOAL" => SOME (Subg (~2), strs)
      | "INTGOAL" =>
        (case strs of
        [] => NONE
        | s2 :: strs2 =>
          (case Int.fromString s2 of
          NONE => NONE
          | SOME i => SOME (Subg i, strs)))
      | _ =>  SOME (Id s1, strs);

  fun findThm (name:string) :thm option =
    let val spl = LassieUtilsLib.string_split name #"."
      val cmp =
        if (List.length spl = 1) then
          fn ((theory, theorem), stmt) => hd spl = theorem
        else
          fn ((theory, theorem), stmt) =>
            (LassieUtilsLib.get_prefix_before_match "Theory" (hd spl)) = theory andalso
            hd (tl spl) = theorem
    in
      case List.find cmp (DB.listDB()) of
      NONE => NONE
      | SOME (_, (th, _)) =>  SOME th
    end;

  fun parseThm (strs:string list) : (string * thm * string list) =
    case lex strs of
    NONE => raise NoParseException "No theorem identifier found where theorem was expected"
    | SOME (Id s, strs1) =>
      if (List.exists (fn a => a = s) thmModifs) then
        let val (thStr, th, strs2) = parseThm strs1
            val txt = s ^ " " ^ thStr in
        case s of
        "Once" => (txt, Once th, strs2)
        | "GSYM" => (txt, GSYM th, strs2)
        | _ => raise NoParseException ("Invalid theorem modifier "^s^" found\n")
        end
      else
      (case findThm s of
      NONE => raise NoParseException ("Could not find theorem " ^ s ^ " in current context")
      | SOME th => (s, th, strs1))
    | _ => raise NoParseException ("Could not parse a theorem where a theorem was expected\n");

  fun peek (s:string list) :token =
    case lex s of
    SOME (tok, strs) => tok
    | _ =>  raise (NoParseException "Could not look into next token when expecting a token\n")

  (** Function tokToString should only be used for list pretty printing, nothing
      else. Thus we exclude other tokens from prettyprinting. **)
  fun tokToString t =
  case t of
    TermStart => "`"
    | TermEnd => "`"
    | LBrac => "("
    | RBrac => ")"
    | ListStart => "["
    | ListEnd => "]"
    | ListSep => ","
    | _ => "";

  local
    (* Generic list parsing function, takes as input the strings to be parsed, a
       function parsing a single element of the list, and tokens describing the
       end and function parsing the separator of the list *)
    fun readList strs singleton endTok sep : (string * 'a list * string list) =
      if (case lex strs of
          NONE => false
          | SOME (tok, strs2) => tok = endTok) then (tokToString endTok,[], snd (valOf (lex strs)))
      else
      let val (strdescr, th, strs2) = singleton strs in
      if (case lex strs2 of
          NONE => false
          | SOME (tok, strs3) => tok = endTok) then
            (strdescr ^ " " ^ tokToString endTok, [th], snd (valOf (lex strs2)))
      else
        let
          val (strSep, strs3) = sep strs2
          val (strs, ths, strs4) = readList strs3 singleton endTok sep
          val descr = strdescr ^ strSep ^ " " ^ strs
        in
          (descr, th :: ths, strs4)
        end
      end
  in
  fun parseList (strs:string list) singleton startTok endTok sep =
    case lex strs of
    SOME (tok,strs) =>
      if (tok = startTok) then
        let val (strdescr, lst, strs2) = readList strs singleton endTok sep
        in (tokToString startTok ^ " " ^ strdescr, lst, strs2) end
      else raise NoParseException "No valid list"
    |  _ => raise NoParseException "No valid theorem list"
  end;

  fun consumeListSep strs =
    case lex strs of
    SOME (ListSep, strs2) => (",", strs2)
    | _ => raise NoParseException "No list separator found";

  fun parseThmList strs = parseList strs parseThm ListStart ListEnd consumeListSep;

  fun consumeTmSep strs = ("", strs);

  fun parseTm (strs:string list) :(string * term frag list * string list) =
    let
        val (strdescr, tm, strs) =
          parseList strs (fn (ss:string list) => (hd ss, hd ss, tl ss)) TermStart TermEnd consumeTmSep
        val fullTm = foldl (fn (s1,s2) => if s2 = "" then s1 else s1 ^ " " ^ s2) "" (List.rev tm)
    in
      (strdescr, [QUOTE fullTm], strs)
    end;

  fun parseTmList strs =
    parseList strs parseTm ListStart ListEnd consumeListSep;

  fun parseThmTactic strs =
    case lex strs of
    SOME (LBrac, strs1) =>
      let val (descr, thmtac, strs2) = parseThmTactic strs1 in
        case lex strs2 of
        SOME (RBrac, strs3) => (descr, thmtac, strs3)
        | _ => raise NoParseException ("Imbalanced parenthesis\n")
      end
    | SOME (Id id, strs) =>
      (case TacticMap.lookupTac id (!tacticMap) of
      SOME (ThmTactic th) => (id, th, strs)
      | SOME (QuotSpecThmTactic t) =>
        let val (tmStr, tm, strs2) = parseTm strs
          val (thmTac, thmtac, strs3) = parseThmTactic strs2 in
        (id ^" "^ tmStr ^" "^ thmTac, t tm thmtac, strs3) end
      | SOME (QuotListSpecThmTactic t) =>
        let val (tmsStr, tm, strs2) = parseTmList strs
          val (thmTac, thmtac, strs3) = parseThmTactic strs2 in
        (id ^" "^ tmsStr ^" "^ thmTac, t tm thmtac, strs3) end
      | _ => raise NoParseException ("Id " ^ id ^ " not found \n"))
    | _ => raise NoParseException ("No theorem tactic found where it was expected\n");

  local
    fun parsePartial (inp:string list) :(string * tactic * string list) =
      case lex inp of
      SOME (Id str, strs) =>
      (case TacticMap.lookupTac str (!tacticMap) of
        SOME (Tactic t) => (str, t,strs)
        | SOME (Tactical tt) =>
          let val (descr, t, strs) = parsePartial strs in
            (str ^" "^ descr, tt t, strs)
          end
        | SOME (ThmTactic th) =>
          let val (thTacDescr,thTac, strs) = parseThmTactic inp
              val (thmDescr, th, strs) = parseThm strs in
              (thTacDescr ^ " " ^ thmDescr, thTac th, strs)
          end
        | SOME (ThmListTactic thsTac) =>
          let val (thmsDescr, thms, strs) = parseThmList strs in
            (str ^ " " ^ thmsDescr, thsTac thms, strs)
          end
        | SOME (QuotTactic qt) =>
          let val (tmDescr, tm, strs) = parseTm strs in
            (str ^" "^tmDescr, qt tm, strs)
          end
        | SOME (AsmTestTactic t) =>
          let val (thmTacDescr, thTac, strs) = parseThmTactic strs in
            (str ^" "^ thmTacDescr, t thTac, strs)
          end
        | SOME (AsmMatchTactic t) =>
          let val (tmDescr, tm, strs2) = parseTm strs
              val (thmTacDescr, thTac, strs3) = parseThmTactic strs2
          in
            (str ^" "^tmDescr^" "^thmTacDescr, t tm thTac, strs3)
          end
        | SOME (QuotSpecThmTactic t) =>
          let
            val (tmDescr, tm, strs2) = parseTm strs
            val (thTacDescr, thTac, strs3) = parseThmTactic strs2
            val (thmDescr, thm, strs4) = parseThm strs3
          in
            (str ^" "^tmDescr^" "^thTacDescr^" "^thmDescr, t tm thTac thm, strs4)
          end
        | SOME (QuotListSpecThmTactic t) =>
          let
            val (tmsDescr, tms, strs2) = parseTmList strs
            val (thTacDescr, thTac, strs3) = parseThmTactic strs2
            val (thmDescr, thm, strs4) = parseThm strs3
          in
            (str ^" "^tmsDescr^" "^thTacDescr^" "^thmDescr, t tms thTac thm, strs4)
          end
        | _ => raise NoParseException ("Id " ^ str ^ " not found\n"))
      | _ => raise NoParseException ("Unparsable string found\n");
    fun parseFull (inp:string list) : (string * tactic * string list) =
      let val (strDescr1, t1, strs1) =
        (case peek inp of
        TermStart =>
          let val (tmDescr, tm, strs2) = parseTm inp in
          case lex strs2 of
          SOME (Id str, strs3) =>
            (case TacticMap.lookupTac str (!tacticMap) of
            SOME (TermComb tc) =>
              let val (tacDescr, tac, strs4) = parseFull strs3 in
                (tmDescr ^" "^str^" "^tacDescr,tc (tm,tac), strs4)
              end
            | _ => raise NoParseException ("Term combinator " ^ str ^ " not found\n"))
          | _ => raise NoParseException ("Unsupported tactic structure in " ^ (foldl (fn (a,b) => b ^ a) "" inp))
          end
        | LBrac =>
          let val (tacDescr, t1, strs1) = parseFull (snd (valOf (lex inp))) in
            case peek strs1 of
            RBrac => ("(" ^ tacDescr^")", t1, snd (valOf (lex strs1)))
            | _ => raise NoParseException "Unmatched parenthesis"
          end
        | _ => parsePartial inp)
      in
        case lex strs1 of
        SOME (Id str, strs2) =>
          (case TacticMap.lookupTac str (!tacticMap) of
          SOME (TacticComb t) =>
              let val (tacDescr, t2, strs3) = parseFull strs2 in
                (strDescr1 ^" "^ str ^" "^ tacDescr, t (t1, t2), strs3)
              end
          | _ => raise NoParseException ("Tactic combinator " ^ str ^ " not found\n"))
        | _ => (strDescr1, t1, strs1)
      end;
  in
    fun parse (sempreResp:string) :(SempreParse * string)=
      let
        val inp = LassieUtilsLib.string_split sempreResp #" "
        val inp = List.rev (foldl (fn (s,ss) => if s = "" then ss else s::ss) [] inp)
     in
      case peek inp of
      Subg n =>
        if n = ~2 then
          let
            val (_, strs) = Option.valOf (lex inp)
            val (descr, tm, strs1) = parseTm (snd (Option.valOf (lex inp))) in
            (Termgoal tm, "Subgoal " ^ descr) end
        else (Subgoal n, "Subgoal " ^ (Int.toString n))
      | Id s =>
        if s = "back" then (Command b,"") else
        let val res = parseFull inp in
        ((HOLTactic (#2 res)),#1res)
        end
      | _ =>
        let val res = parseFull inp in
        ((HOLTactic (#2 res)),#1res)
        end
      end;
  end;

  fun addCustomTactic (tac:tactic) (str:string) =
    tacticMap := insTac (str, tac) (!tacticMap);

  fun addCustomThmTactic (tac:thm_tactic) (str:string) =
    tacticMap := insThmTac (str, tac) (!tacticMap)

end;
