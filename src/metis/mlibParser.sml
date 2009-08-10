(* ========================================================================= *)
(* PARSER COMBINATORS                                                        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "mlibStream"];
*)

(*
*)
structure mlibParser :> mlibParser =
struct

open mlibUseful;

structure S = mlibStream; local open mlibStream in end;

infixr 9 >>++;
infixr 8 ++;
infixr 7 >>;
infixr 6 ||;
infix ##;

type 'a stream = 'a S.stream;
val omap       = Option.map;

(* ------------------------------------------------------------------------- *)
(* Generic.                                                                  *)
(* ------------------------------------------------------------------------- *)

exception Noparse;

fun op ++ (parser1, parser2) input =
  let
    val (result1, rest1) = parser1 input
    val (result2, rest2) = parser2 rest1
  in
    ((result1, result2), rest2)
  end;

fun op >> (parser : 'a -> 'b * 'a, treatment) input =
  let
    val (result, rest) = parser input
  in
    (treatment result, rest)
  end;

fun op >>++ (parser, treatment) input =
  let
    val (result, rest) = parser input
  in
    treatment result rest
  end;

fun op || (parser1, parser2) input = parser1 input
handle Noparse => parser2 input;

fun smany parser state input =
  let
    val (state,input) = parser state input
  in
    smany parser state input
  end
  handle Noparse => (state,input);

fun many parser =
    let
      fun sparser l = parser >> (fn x => x :: l)
    in
      smany sparser [] >> rev
    end;

fun atleastone p = (p ++ many p) >> op::;

fun nothing input = ((), input);

fun optional p = (p >> SOME) || (nothing >> K NONE);

(* ------------------------------------------------------------------------- *)
(* mlibStream-based.                                                             *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) parser = 'a stream -> 'b * 'a stream

fun everything parser =
    let
      fun f input =
          let
            val (result,input) = parser input
          in
            S.append (S.from_list result) (fn () => f input)
          end
          handle Noparse => if S.null input then S.NIL else raise Noparse
    in
      f
    end;

fun maybe p S.NIL = raise Noparse
  | maybe p (S.CONS (h,t)) =
  case p h of SOME r => (r, t ()) | NONE => raise Noparse;

fun finished S.NIL = ((), S.NIL)
  | finished (S.CONS _) = raise Noparse;

fun some p = maybe (fn x => if p x then SOME x else NONE);

fun any input = some (K true) input;

fun exact tok = some (fn item => item = tok);

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing for infix operators.                          *)
(* ------------------------------------------------------------------------- *)

type infixities = {tok : string, prec : int, left_assoc : bool} list;
type 'a con      = string * 'a * 'a -> 'a;
type 'a des      = 'a -> (string * 'a * 'a) option;
type 'a iparser  = (string, 'a) parser;
type 'a iprinter = ('a * bool) pp;

local
  fun unflatten ({tok, prec, left_assoc}, ([], _)) =
    ([(left_assoc, [tok])], prec)
    | unflatten ({tok, prec, left_assoc}, ((a, l) :: dealt, p)) =
    if p = prec then
      (assert (left_assoc = a) (Bug "infix parser/printer: mixed assocs");
       ((a, tok :: l) :: dealt, p))
    else
      ((left_assoc, [tok]) :: (a, l) :: dealt, prec);
in
  val layerops = fst o foldl unflatten ([], 0) o sort_map #prec Int.compare;
end;

local
  fun chop (#" " :: chs) = (curry op+ 1 ## I) (chop chs) | chop chs = (0,chs);
  fun nspaces n = funpow n (curry op^ " ") "";
  fun spacify tok =
    let
      val chs = explode tok
      val (r, chs) = chop (rev chs)
      val (l, chs) = chop (rev chs)
    in
      ((l, r), implode chs)
    end;
  fun lrspaces (l, r) =
    (if l = 0 then K () else C PP.add_string (nspaces l),
     if r = 0 then K () else C PP.add_break (r, 0));
in
  val op_spaces = (lrspaces ## I) o spacify;
  val op_clean  = snd             o spacify;
end;

val optoks : infixities -> string list = map (fn {tok, ...} => op_clean tok);

fun parse_gen_infix update sof toks parse inp =
  let
    val (e, rest) = parse inp
    val continue =
      case rest of S.NIL => NONE
      | S.CONS (h, t) => if mem h toks then SOME (h, t) else NONE
  in
    case continue of NONE => (sof e, rest)
    | SOME (h, t) => parse_gen_infix update (update sof h e) toks parse (t ())
  end;

fun parse_left_infix toks con =
  parse_gen_infix (fn f => fn t => fn a => fn b => con (t, f a, b)) I toks;

fun parse_right_infix toks con =
  parse_gen_infix (fn f => fn t => fn a => fn b => f (con (t, a, b))) I toks;

fun parse_infixes ops =
  let
    val layeredops = map (I ## map op_clean) (layerops ops)
    fun iparser (a, t) = (if a then parse_left_infix else parse_right_infix) t
    val iparsers = map iparser layeredops
  in
    fn con => fn subparser => foldl (fn (p,sp) => p con sp) subparser iparsers
  end;

fun pp_gen_infix left toks : 'a des -> 'a iprinter -> 'a iprinter =
  let
    val spc = map op_spaces toks
  in
    fn dest => fn pp_sub =>
    let
      fun dest' tm =
        case dest tm of NONE => NONE
        | SOME (t, a, b) => omap (pair (a,b)) (List.find (equal t o snd) spc)
      open PP
      fun pp_go pp (tmr as (tm,r)) =
        case dest' tm of NONE => pp_sub pp tmr
        | SOME ((a,b),((lspc,rspc),tok))
          => ((if left then pp_go else pp_sub) pp (a,true);
              lspc pp; add_string pp tok; rspc pp;
              (if left then pp_sub else pp_go) pp (b,r))
    in
      fn pp => fn tmr as (tm,_) =>
      case dest' tm of NONE => pp_sub pp tmr
      | SOME _ => (begin_block pp INCONSISTENT 0; pp_go pp tmr; end_block pp)
    end
  end;

fun pp_left_infix toks = pp_gen_infix true toks;

fun pp_right_infix toks = pp_gen_infix false toks;

fun pp_infixes ops =
  let
    val layeredops = layerops ops
    val toks = List.concat (map (map op_clean o snd) layeredops)
    fun iprinter (a,t) = (if a then pp_left_infix else pp_right_infix) t
    val iprinters = map iprinter layeredops
  in
    fn dest => fn pp_sub =>
    let
      fun printer sub = foldl (fn (ip,p) => ip dest p) sub iprinters
      fun is_op t = case dest t of SOME (x,_,_) => mem x toks | _ => false
      open PP
      fun subpr pp (tmr as (tm,_)) =
        if is_op tm then
          (begin_block pp INCONSISTENT 1; add_string pp "(";
           printer subpr pp (tm, false); add_string pp ")"; end_block pp)
        else pp_sub pp tmr
    in
      fn pp => fn tmr =>
      (begin_block pp INCONSISTENT 0; printer subpr pp tmr; end_block pp)
    end
  end;

(* ------------------------------------------------------------------------- *)
(* Lexing.                                                                   *)
(* ------------------------------------------------------------------------- *)

val space = Char.isSpace;
val digit = Char.isDigit;
val lower = Char.isLower;
val upper = Char.isUpper;
val alpha = Char.isAlpha;
val alphanum = fn c => alpha c orelse digit c orelse c = #"'" orelse c = #"_";
val symbol = Char.contains "<>=-*+/\\?@|!$%&~#^:";
val punct = Char.contains "()[]{}.,;";

(* ------------------------------------------------------------------------- *)
(* Quotations.                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a quotation = 'a frag list;

fun quotation_parser parser pp_a =
  let val f = PP.pp_to_string (!LINE_LENGTH) pp_a
  in parser o foldl (fn (QUOTE q, s) => s ^ q | (ANTIQUOTE a, s) => s ^ f a) ""
  end;

end
