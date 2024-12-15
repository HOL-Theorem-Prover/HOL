(* ========================================================================= *)
(* FILE          : tttToken.sml                                              *)
(* DESCRIPTION   : Combining, parsing and predicting tactic tokens           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure tttToken :> tttToken =
struct

open HolKernel Abbrev boolLib aiLib
  smlTimeout smlLexer smlParser smlExecute
  mlFeature mlThmData mlTacticData mlNearestNeighbor mlTreeNeuralNetwork
  psMinimize tttSetup

val ERR = mk_HOL_ERR "tttToken"
fun debug_err s1 s2 = (debug (s1 ^ " : " ^ s2); raise ERR s1 s2)

(* -------------------------------------------------------------------------
   Union types for different type of tactics
   ------------------------------------------------------------------------- *)

datatype pretac =
    NoargTac of tactic
  | ThmlTac of thm list -> tactic
  | TermTac of term quotation -> tactic

fun dest_noargtac pretac = case pretac of
  NoargTac x => x | _ => raise ERR "dest_noargtac" ""
fun dest_thmltac pretac = case pretac of
  ThmlTac x => x | _ => raise ERR "dest_thmltac" ""
fun dest_termtac pretac = case pretac of
  TermTac x => x | _ => raise ERR "dest_termtac" ""

(* -------------------------------------------------------------------------
   Tokens that forms a tactic
   ------------------------------------------------------------------------- *)

datatype token = Stac of string | Sterm of string | Sthml of string list

fun dest_stac token =
  case token of Stac s => s | _ => raise ERR "dest_stac" ""
fun dest_sterm token =
  case token of Sterm s => s | _ => raise ERR "dest_sterm" ""
fun dest_sthml token =
  case token of Sthml sl => sl | _ => raise ERR "dest_sthml" ""

type parsetoken =
  {parse_stac : string -> pretac ,
   parse_thmidl : string list -> thm list,
   parse_sterm : string -> term quotation}

fun string_of_token token = case token of
    Stac s => "tac: " ^ s
  | Sterm s => "term: " ^ s
  | Sthml sl => "thml: " ^ String.concatWith " " sl

fun compare_token (t1,t2) =
  String.compare (string_of_token t1, string_of_token t2)

(* -------------------------------------------------------------------------
   Possible argument types for a tactic
   ------------------------------------------------------------------------- *)

datatype aty = Aterm | Athml

val termarg_placeholder = "tactictoe_termarg"
val thmlarg_placeholder = "tactictoe_thmlarg"
val tactictoe_thmlarg : thm list = []
val tactictoe_termarg : term quotation = [QUOTE "tactictoe_termag:'a"]

fun is_termstac stac =
  mem termarg_placeholder (partial_sml_lexer stac)
fun is_thmlstac stac =
  mem thmlarg_placeholder (partial_sml_lexer stac)

fun extract_atyl stac =
  (if is_thmlstac stac then [Athml] else []) @
  (if is_termstac stac then [Aterm] else [])

(* -------------------------------------------------------------------------
   Abstraction/instantiation of list of theorems in tactic strings
   ------------------------------------------------------------------------- *)

fun change_thml thml = case thml of
    [] => NONE
  | a :: m => (if is_thm (String.concatWith " " a) then SOME thml else NONE)

fun abstract_thml_loop thmlacc l = case l of
    []       => []
  | "[" :: m =>
    let
      val (el,cont) = split_level "]" m
      val thml = rpt_split_level "," el
    in
      case change_thml thml of
        NONE => "[" :: abstract_thml_loop thmlacc m
      | SOME x =>
        (
        thmlacc := map (String.concatWith " ") thml :: !thmlacc;
        thmlarg_placeholder :: abstract_thml_loop thmlacc cont
        )
    end
  | a :: m => a :: abstract_thml_loop thmlacc m

fun abstract_thml stac =
  if is_thmlstac stac then NONE else
  let
    val sl1 = partial_sml_lexer stac
    val thmllref = ref []
    val sl2 = abstract_thml_loop thmllref sl1
  in
    if null (!thmllref)
    then NONE
    else SOME (String.concatWith " " sl2, !thmllref)
  end

fun sthml_of_thmidl thmidl =
  "[ " ^ String.concatWith " , " (map dbfetch_of_thmid thmidl) ^ " ]"

fun inst_thml thmidl stac =
  let
    val sthml = sthml_of_thmidl thmidl
    val estac1 = partial_sml_lexer stac
    val estac2 = subst_sl (thmlarg_placeholder,sthml) estac1
  in
    String.concatWith " " estac2
  end

(* -------------------------------------------------------------------------
   Abstracting/instantiation of left-most term in tactics
   ------------------------------------------------------------------------- *)

fun is_quoted s =
  let val n = String.size s in
    String.sub (s,0) = #"\"" andalso String.sub (s, n - 1) = #"\""
  end

fun abstract_term_loop termref l = case l of
    [] => []
  | "[" :: a :: b :: "]" :: m =>
    if drop_sig a = "QUOTE" andalso is_quoted b
      then
        (
        termref := SOME b;
        termarg_placeholder :: m
        )
      else hd l :: abstract_term_loop termref (tl l)
  | a :: m => a :: abstract_term_loop termref m

fun abstract_term stac =
  if is_termstac stac then NONE else
  let
    val sl1 = partial_sml_lexer stac
    val termref = ref NONE
    val sl2 = abstract_term_loop termref sl1
  in
    if isSome (!termref)
    then SOME (String.concatWith " " sl2, valOf (!termref))
    else NONE
  end
  handle Interrupt => raise Interrupt | _ =>
    (debug ("error: abstract_term: " ^ stac); NONE)

fun inst_term sterm stac =
  let
    val estac1 = partial_sml_lexer stac
    val qterm = "[ HOLPP.QUOTE " ^ mlquote sterm ^ " ]"
    val estac2 = subst_sl (termarg_placeholder,qterm) estac1
  in
    String.concatWith " " estac2
  end
  handle Interrupt => raise Interrupt | _ => debug_err "inst_term" stac

(*
load "tttToken"; open tttToken;
val stac = "EXISTS_TAC ``1:num``";
val stac' = HolParser.fromString false stac;
val (astac,sterm) = valOf (abstract_term stac');
val istac = inst_term "2:num" astac;
*)

(* -------------------------------------------------------------------------
   Predict subterms of a goal
   ------------------------------------------------------------------------- *)

(*
fun pred_ssubterm (asl,w) stm =
  let
    val tm = Parse.Term [QUOTE
      (valOf (String.fromString (aiLib.unquote_string stm)))]
      handle Interrupt => raise Interrupt | _ =>
        debug_err "error: pred_ssubterm" stm
    val mem = !show_types
    val tmll = map (find_terms (fn _ => true)) (w :: asl)
    val tml1 = mk_term_set (List.concat tmll)
    val tmfea = map_assoc (fn x => ~ (length tml1) :: fea_of_term true x) tml1
    val symweight = learn_tfidf tmfea
    val tml2 = termknn (symweight,tmfea) 1 (fea_of_term true tm)
    val r = (show_types := true; term_to_string (hd tml2))
  in
    show_types := mem; r
  end
  handle Interrupt => raise Interrupt | _ =>
    debug_err "error: pred_ssubterm" "unexpected"
*)

(* -------------------------------------------------------------------------
   Build tactic and tactic string from tokens
   ------------------------------------------------------------------------- *)

fun build_tac {parse_stac,parse_thmidl,parse_sterm} tokenl = case tokenl of
    [Stac stac] => dest_noargtac (parse_stac stac)
  | [Stac stac, Sthml thmidl] =>
     let
       val thmltac = dest_thmltac (parse_stac stac)
       val thml = parse_thmidl thmidl
     in
       thmltac thml
     end
  | [Stac stac, Sterm sterm] =>
    let
      val termtac = dest_termtac (parse_stac stac)
      val term = parse_sterm sterm
    in
      termtac term
    end
  | _ => raise ERR "build_tac" "not supported"

fun build_stac tokenl = case tokenl of
    [Stac stac] => stac
  | [Stac stac, Sthml thmidl] => inst_thml thmidl stac
  | [Stac stac, Sterm sterm] => inst_term sterm stac
  | _ => raise ERR "build_stac" "not supported"

(* -------------------------------------------------------------------------
   Parsing a list of tactics (of different types)
   ------------------------------------------------------------------------- *)

val sml_pretacl_glob = ref []

fun mk_valid s = "Tactical.VALID ( " ^ s ^ " )"

fun mk_pretac stac = case extract_atyl stac of
    [] => "tttToken.NoargTac ( " ^ mk_valid stac ^ ")"
  | [Athml] => "tttToken.ThmlTac ( " ^
    "fn " ^ thmlarg_placeholder ^ " => " ^ mk_valid stac ^ ")"
  | [Aterm] => "tttToken.TermTac ( " ^
    "fn " ^ termarg_placeholder ^ " => " ^ mk_valid stac ^ ")"
  | _ => raise ERR "mk_pretac" "not supported"

fun pretacl_of_sml tim stacl =
  let
    val ttacl = "[ " ^ String.concatWith " , " (map mk_pretac stacl) ^ " ]"
    val program =
      "let fun f () = tttToken.sml_pretacl_glob := " ^ ttacl ^ " in " ^
      "smlTimeout.timeout " ^ rts tim ^ " f () end"
    val b = quse_string program
  in
    if b then SOME (!sml_pretacl_glob) else NONE
  end

end (* struct *)
