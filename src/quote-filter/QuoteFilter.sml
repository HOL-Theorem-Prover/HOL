(****************************************************************************)
(* FILE          : hol-quote-filter.sml                                     *)
(* DESCRIPTION   : Function to provide quotation and antiquotation for the  *)
(*                 HOL system by filtering ML strings containing ML text.   *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 20th July 1996                                           *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 9th July 1997                                          *)
(* Modified      : September 22, 1997, Ken Larsen                           *)
(****************************************************************************)

(*==========================================================================*)
(* Expects the following Standard ML datatype to have been declared:        *)
(*                                                                          *)
(*    datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;                 *)
(*                                                                          *)
(* and also the functions term_parser, type_parser, and ty_antiq.           *)
(*                                                                          *)
(* This filter adds the following special features to Standard ML:          *)
(*                                                                          *)
(*    `...`        a generic quotation                                      *)
(*    ``...``      a HOL term quotation                                     *)
(*    ``:...``     a HOL type quotation                                     *)
(*    --`...`--    a HOL term quotation (for backward compatibility)        *)
(*    ==`:...`==   a HOL type quotation (for backward compatibility)        *)
(*                                                                          *)
(*    `... ^(...) ...`      antiquotation in a generic quotation            *)
(*    ``... ^(...) ...``    term antiquotation in a HOL term                *)
(*    ``... :^(...) ...``   type antiquotation in a HOL term                *)
(*    ``:... ^(...) ...``   type antiquotation in a HOL type                *)
(*                                                                          *)
(* where (...) may be an alphanumeric or symbolic ML identifier or a        *)
(* parenthesized expression. The number of lines in the processed           *)
(* text remains unchanged.                                                  *)
(*                                                                          *)
(* Limitations:                                                             *)
(*                                                                          *)
(*    o No carriage return or line feed may appear between the `--'         *)
(*      or `==' and the quotation marks in the old-style quotations.        *)
(*==========================================================================*)

structure QuoteFilter =
struct

local

open Portable_List;

fun mem x []        = false
  | mem x (y :: ys) = (x = y) orelse mem x ys;

fun ord c = Portable_String.ordof (c,0);
val op ^ = Portable_String.^;
val implode = Portable_String.concat;
val explode = map Portable_String.str o Portable_String.explode;

datatype state = Initial | String | Comment | Quote | TmQuote | OldTmQuote
               | TyQuote | OldTyQuote | AntiQuote;

fun is_letter c =
   let val n = ord c
   in  (ord "A" <= n andalso n <= ord "Z") orelse
       (ord "a" <= n andalso n <= ord "z")
   end;
fun is_digit c =
   let val n = ord c
   in  ord "0" <= n andalso n <= ord "9"
   end;
val is_symbol =
   let val symbols = explode "!%&$+/:<=>?@~|#*\\-^"
   in  fn c => mem c symbols
   end;

fun scan_alphanum [] f = f []
  | scan_alphanum (cs as (c :: cs')) f =
   if (is_letter c) orelse (is_digit c) orelse (c = "_") orelse (c = "'")
   then c :: scan_alphanum cs' f
   else f cs;

fun scan_symbol [] f = f []
  | scan_symbol (cs as (c :: cs')) f =
   if (is_symbol c)
   then c :: scan_symbol cs' f
   else f cs;

fun scan_id [] f = f []
  | scan_id (cs as (c :: _)) f =
   if (is_letter c)
   then scan_alphanum cs f
   else scan_symbol cs f;

fun consume_ws [] = []
  | consume_ws (" " :: cs) = cs
  | consume_ws ("\t" :: cs) = cs
  | consume_ws (cs as (_ :: _)) = cs;

fun new_frame e = (0,0,Initial) :: e;
val pop = tl;

fun antiquote e = length e > 1;

fun pardepth ((pd,_,_) :: _) = pd
and comdepth ((_,cd,_) :: _) = cd
and prevstate ((_,_,ps) :: _) = ps;

fun inc_pardepth ((pd,cd,ps) :: e) = (pd + 1,cd,ps) :: e
and dec_pardepth ((pd,cd,ps) :: e) = (pd - 1,cd,ps) :: e
and inc_comdepth ((pd,cd,ps) :: e) = (pd,cd + 1,ps) :: e
and dec_comdepth ((pd,cd,ps) :: e) = (pd,cd - 1,ps) :: e
and set_prevstate s ((pd,cd,ps) :: e) = (pd,cd,s) :: e;

fun filter e (s as Initial) cs =
   (case cs
    of []                => []
     | "\"" :: cs'       => "\"" :: filter e String cs'
     | "(" :: "*" :: cs' => "(*" :: filter (inc_comdepth e) Comment cs'
     | "(" :: cs'        => "("  :: filter (inc_pardepth e) s cs'
     | ")" :: cs'        => ")"  :: let val e' = dec_pardepth e
                                    in  if (antiquote e') andalso
                                           (pardepth e' < 1)
                                        then let val e'' = pop e'
                                             in  "),QUOTE \"" ::
                                                 filter e'' (prevstate e'') cs'
                                             end
                                        else filter e' s cs'
                                    end
     | "=" :: "=" :: cs' => (case (consume_ws cs')
                             of "`" :: cs'' => "(Parse.type_parser [QUOTE \"" ::
                                               filter e OldTyQuote cs''
                              | _ => "==" :: filter e s cs')
     | "-" :: "-" :: cs' => (case (consume_ws cs')
                             of "`" :: cs'' => "(Parse.term_parser [QUOTE \"" ::
                                               filter e OldTmQuote cs''
                              | _ => "--" :: filter e s cs')
     | "`" :: "`" :: cs' => (case (consume_ws cs')
                             of ":" :: cs'' => "(Parse.type_parser [QUOTE \":" ::
                                               filter e TyQuote cs''
                              | _ => "(Parse.term_parser [QUOTE \"" ::
                                     filter e TmQuote cs')
     | "`" :: cs'        => "[QUOTE \"" :: filter e Quote cs'
(*   | "\n" :: cs'       => "\n" :: filter e s cs' *)
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as String) cs =
   (case cs
    of []                  => []
     | "\\" :: "\\" :: cs' => "\\\\" :: filter e s cs'
     | "\\" :: "\"" :: cs' => "\\\"" :: filter e s cs'
     | "\"" :: cs'         => "\"" :: filter e Initial cs'
     | c :: cs'            => c :: filter e s cs')
  | filter e (s as Comment) cs =
   (case cs
    of []                => []
     | "(" :: "*" :: cs' => "(*" :: filter (inc_comdepth e) s cs'
     | "*" :: ")" :: cs' => "*)" :: let val e' = dec_comdepth e
                                    in  filter e' (if (comdepth e' < 1)
                                                   then Initial
                                                   else s) cs'
                                    end
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as Quote) cs =
   (case cs
    of []                => []
     | "`" :: cs'        => "\"]" :: filter e Initial cs'
     | "^" :: cs'        => "\",ANTIQUOTE (" ::
                            filter (set_prevstate s e) AntiQuote cs'
     | "\\" :: cs'       => "\\\\" :: filter e s cs'
     | "\"" :: cs'       => "\\\"" :: filter e s cs'
     | "\t" :: cs'       => "\\t" :: filter e s cs'
     | "\n" :: cs'       => " \",\nQUOTE \"" :: filter e s cs'
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as TmQuote) cs =
   (case cs
    of []                => []
     | "`" :: "`" :: cs' => "\"])" :: filter e Initial cs'
     | ":" :: cs'        => (case (consume_ws cs')
                             of "^" :: cs'' => ":\",ANTIQUOTE (ty_antiq " ::
                                               filter (set_prevstate s e)
                                                  AntiQuote cs''
                              | _ => ":" :: filter e s cs')
     | "^" :: cs'        => "\",ANTIQUOTE (" ::
                            filter (set_prevstate s e) AntiQuote cs'
     | "\\" :: cs'       => "\\\\" :: filter e s cs'
     | "\"" :: cs'       => "\\\"" :: filter e s cs'
     | "\t" :: cs'       => "\\t" :: filter e s cs'
     | "\n" :: cs'       => " \",\nQUOTE \"" :: filter e s cs'
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as OldTmQuote) cs =
   (case cs
    of []                => []
     | "`" :: cs'        => (case (consume_ws cs')
                             of "-" :: "-" :: cs'' =>
                                "\"])" :: filter e Initial cs''
                              | _ => "`" :: filter e s cs')
     | "^" :: cs'        => "\",ANTIQUOTE (" ::
                            filter (set_prevstate s e) AntiQuote cs'
     | "\\" :: cs'       => "\\\\" :: filter e s cs'
     | "\"" :: cs'       => "\\\"" :: filter e s cs'
     | "\t" :: cs'       => "\\t" :: filter e s cs'
     | "\n" :: cs'       => " \",\nQUOTE \"" :: filter e s cs'
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as TyQuote) cs =
   (case cs
    of []                => []
     | "`" :: "`" :: cs' => "\"])" :: filter e Initial cs'
     | "^" :: cs'        => "\",ANTIQUOTE (ty_antiq " ::
                            filter (set_prevstate s e) AntiQuote cs'
     | "\\" :: cs'       => "\\\\" :: filter e s cs'
     | "\"" :: cs'       => "\\\"" :: filter e s cs'
     | "\t" :: cs'       => "\\t" :: filter e s cs'
     | "\n" :: cs'       => " \",\nQUOTE \"" :: filter e s cs'
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as OldTyQuote) cs =
   (case cs
    of []                => []
     | "`" :: cs'        => (case (consume_ws cs')
                             of "=" :: "=" :: cs'' =>
                                "\"])" :: filter e Initial cs''
                              | _ => "`" :: filter e s cs')
     | "^" :: cs'        => "\",ANTIQUOTE (" ::
                            filter (set_prevstate s e) AntiQuote cs'
     | "\\" :: cs'       => "\\\\" :: filter e s cs'
     | "\"" :: cs'       => "\\\"" :: filter e s cs'
     | "\t" :: cs'       => "\\t" :: filter e s cs'
     | "\n" :: cs'       => " \",\nQUOTE \"" :: filter e s cs'
     | c :: cs'          => c :: filter e s cs')
  | filter e (s as AntiQuote) cs =
   (case cs
    of []                => []
     | "(" :: _          => filter (new_frame e) Initial cs
     | " " :: cs'        => filter e s (consume_ws cs')
     | "\n" :: cs'       => "\n" :: filter e s cs'
     | c :: _            => if (is_letter c) orelse (is_symbol c)
                            then scan_id cs
                                    (fn cs' => "),QUOTE \"" ::
                                               filter e (prevstate e) cs')
                            else "),QUOTE \"" :: filter e (prevstate e) cs);

in

val quote_filter = implode o filter (new_frame []) Initial o explode;

end;

end; (* QuoteFilter *)
