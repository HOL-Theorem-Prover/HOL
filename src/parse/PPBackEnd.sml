structure PPBackEnd :> PPBackEnd =
struct

type hol_type = Type.hol_type
open Portable

open term_pp_types


(* ========================================================================== *)
(* Datatypes used by the backends                                             *)
(* ========================================================================== *)

type t = term_grammar.grammar term_pp_types.ppbackend
type output_colors = {
    bv    : pp_color,
    fv    : pp_color,
    tyv   : pp_color,
    tyop  : pp_color,
    tysyn : pp_color
  }

(* ========================================================================== *)
(* some auxiliary functions for styles                                        *)
(* ========================================================================== *)

(* -------------------------------- *)
(* Full styles                      *)
(* -------------------------------- *)

val UserStyle_dict = ref
   (Redblackmap.mkDict String.compare:
     (string, pp_style list * (string * pp_style list) list) Redblackmap.dict)

fun register_UserStyle backendOpt sty stL =
let
   val (default_stL, bstL) =
       Redblackmap.find (!UserStyle_dict, sty) handle NotFound => (stL,[])

   val default_stL = if isSome(backendOpt) then default_stL else stL
   val bstL = if isSome(backendOpt) then
      (valOf backendOpt, stL)::
      (Lib.filter (fn (s,_) => not (s = valOf backendOpt)) bstL) else bstL

   val _ =
       UserStyle_dict :=
       Redblackmap.insert (!UserStyle_dict, sty, (default_stL, bstL))
in
   ()
end;

fun lookup_UserStyle backend sty =
let
   val (default_stL, bstL) = Redblackmap.find (!UserStyle_dict, sty)
       handle NotFound =>
       (register_UserStyle NONE sty []; ([],[]))
   val styL = Lib.assoc backend bstL handle Feedback.HOL_ERR _ => default_stL
in
   styL
end

fun known_UserStyles () =
   map Lib.fst (Redblackmap.listItems (!UserStyle_dict))


(* fullstyle:
     foreground option * background option * bold? * underlined? * user styles
*)
type pp_full_style =
     pp_color option * pp_color option * bool * bool * string list

val base_style = (NONE, NONE, false, false,[]):pp_full_style

fun update_style (_, bg,b,u,uL)  (FG c) = (SOME c, bg, b, u, uL)
  | update_style (fg,_ ,b,u,uL)  (BG c) = (fg, SOME c, b, u, uL)
  | update_style (fg,bg,_,u,uL)  Bold = (fg, bg, true, u, uL)
  | update_style (fg,bg,b,_,uL)  Underline = (fg, bg, b, true, uL)
  | update_style (fg,bg,b,u,uL)  (UserStyle st) = (fg, bg, b, true, st::uL)

val list_update_style = foldl (fn (s, fs) => update_style fs s)


(* -------------------------------- *)
(* A stack for styles               *)
(* -------------------------------- *)

fun top_style style_stack = let val st = !style_stack in
   if null st then base_style else hd st end;

fun pop_style style_stack = let val st = !style_stack in
   if null st then base_style else (style_stack := tl st;hd st) end;

fun push_style style_stack sty =
   (style_stack := sty::(!style_stack))

fun push_styleL style_stack styL =
let
   val top_fsty = top_style style_stack;
   val new_fsty = list_update_style top_fsty styL;
   val _ = push_style style_stack new_fsty
in
   new_fsty
end;


fun expand_UserStyle b [] = []
  | expand_UserStyle b ((UserStyle st)::styL) =
      expand_UserStyle b (lookup_UserStyle b st @ styL)
  | expand_UserStyle b (st::styL) = st::expand_UserStyle b styL

fun user_push_styleL b style_stack styL =
    push_styleL style_stack (expand_UserStyle b styL);




(* ========================================================================== *)
(* terminals                                                                  *)
(* ========================================================================== *)


(* -------------------------------- *)
(* Traces                           *)
(* -------------------------------- *)

val add_type_information = ref true
val _ = Feedback.register_btrace ("PPBackEnd show types", add_type_information)

val backend_use_annotations = ref true
val _ = Feedback.register_btrace ("PPBackEnd use annotations",
                                  backend_use_annotations)

val backend_use_styles = ref true
val _ = Feedback.register_btrace ("PPBackEnd use styles", backend_use_styles)

val backend_use_css = ref true
val _ = Feedback.register_btrace ("PPBackEnd use css", backend_use_styles)

fun add_ssz (s,sz) =
  case sz of NONE => smpp.add_string s | SOME sz => smpp.add_stringsz (s,sz)

(* -------------------------------- *)
(* raw terminal                     *)
(* -------------------------------- *)

val raw_terminal : t = {
   extras = {name = "raw_terminal",
             tm_grammar_upd = (fn g => g),
             ty_grammar_upd = (fn g => g)},
   add_break      = smpp.add_break,
   add_string     = smpp.add_string,
   add_xstring    = fn {s,sz,...} => add_ssz (s,sz),
   add_newline    = smpp.add_newline,
   ublock         = smpp.block,
   ustyle         = fn sty => fn p => p}


(* -------------------------------- *)
(* vt100 terminal                   *)
(* -------------------------------- *)

fun color_to_vt100 Black       = (false, 0)
  | color_to_vt100 RedBrown    = (false, 1)
  | color_to_vt100 Green       = (false, 2)
  | color_to_vt100 BrownGreen  = (false, 3)
  | color_to_vt100 DarkBlue    = (false, 4)
  | color_to_vt100 Purple      = (false, 5)
  | color_to_vt100 BlueGreen   = (false, 6)
  | color_to_vt100 LightGrey   = (false, 7)
  | color_to_vt100 DarkGrey    = (true,  0)
  | color_to_vt100 OrangeRed   = (true,  1)
  | color_to_vt100 VividGreen  = (true,  2)
  | color_to_vt100 Yellow      = (true,  3)
  | color_to_vt100 Blue        = (true,  4)
  | color_to_vt100 PinkPurple  = (true,  5)
  | color_to_vt100 LightBlue   = (true,  6)
  | color_to_vt100 White       = (true,  7);

fun fg_to_vt100 c =
let
   val (light, col_ind) = color_to_vt100 c
in
   (if light then ";1;3" else ";3") ^
   Int.toString col_ind
end;

fun bg_to_vt100 c =
let
   val (light, col_ind) = color_to_vt100 c
in
   ";4"^(Int.toString col_ind)
end;


fun full_style_to_vt100 (fg,bg,b,u,_) =
   (* reset *)      "\027[0"^
   (* foreground *) (if isSome fg then (fg_to_vt100 (valOf fg)) else "") ^
   (* background *) (if isSome bg then (bg_to_vt100 (valOf bg)) else "") ^
   (* bold *)       (if b then ";1" else "") ^
   (* underline *)  (if u then ";4" else "") ^
   (* done *)       "m";


fun ansi_terminal (name : string) (colors : output_colors) : t =
let
  open smpp
  val style_stack = ref ([]:pp_full_style list);
  fun set_style fsty =
    smpp.add_stringsz (full_style_to_vt100 fsty, 0)

  fun reset_style() = set_style (top_style style_stack)

  fun ustyle styL p =
    if not (!backend_use_styles) then nothing
    else
      (user_push_styleL name style_stack styL; reset_style()) >> p >>
      (pop_style style_stack ; reset_style())

  fun add_color_string c ssz =
    set_style (SOME c, NONE, false, false, []) >>
    add_ssz ssz >>
    reset_style()

  fun add_xstring {s,sz,ann} =
    if not (!backend_use_annotations) orelse not (isSome ann) then
      add_ssz (s,sz)
    else
      case valOf ann of
        FV _    => add_color_string (#fv colors) (s,sz)
      | BV _    => add_color_string (#bv colors) (s,sz)
      | TyV     => add_color_string (#tyv colors) (s,sz)
      | TyOp _  => add_color_string (#tyop colors) (s,sz)
      | TySyn _ => add_color_string (#tysyn colors) (s,sz)
      | _ => add_ssz (s,sz)
in
  {extras = {name           = name,
             tm_grammar_upd = (fn g => g),
             ty_grammar_upd = (fn g => g)},
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   ublock         = #ublock raw_terminal,
   add_string     = #add_string  raw_terminal,
   add_xstring    = add_xstring,
   ustyle         = ustyle}
end

val vt100_terminal = ansi_terminal "vt100_terminal" {
  fv = Blue,
  bv = Green,
  tyv = Purple,
  tyop = BlueGreen,
  tysyn = BlueGreen
}

(* -------------------------------- *)
(* emacs terminal                   *)
(* -------------------------------- *)

fun color_to_char Black       = #"0"
  | color_to_char RedBrown    = #"1"
  | color_to_char Green       = #"2"
  | color_to_char BrownGreen  = #"3"
  | color_to_char DarkBlue    = #"4"
  | color_to_char Purple      = #"5"
  | color_to_char BlueGreen   = #"6"
  | color_to_char DarkGrey    = #"7"
  | color_to_char LightGrey   = #"8"
  | color_to_char OrangeRed   = #"9"
  | color_to_char VividGreen  = #"A"
  | color_to_char Yellow      = #"B"
  | color_to_char Blue        = #"C"
  | color_to_char PinkPurple  = #"D"
  | color_to_char LightBlue   = #"E"
  | color_to_char White       = #"F";

fun color_option_to_string NONE = "-"
  | color_option_to_string (SOME c) =
      Char.toString (color_to_char c);

fun bool_to_string true = "X"
  | bool_to_string false = "-";

fun full_style_to_emacs_string (fg,bg,b,u,_) =
   (color_option_to_string fg) ^
   (color_option_to_string bg) ^
   (bool_to_string b) ^
   (bool_to_string u);


val emacs_terminal = let
  open smpp
  val name = "emacs_terminal";
  fun lazy_string ls = if !add_type_information then (ls ()) else "";
  fun fv s tystr = "(*(*(*FV\000"^(lazy_string tystr)^"\000"^s^"*)*)*)"
  fun bv s tystr = "(*(*(*BV\000"^(lazy_string tystr)^"\000"^s^"*)*)*)"
  fun tyv s = "(*(*(*TV"^s^"*)*)*)"
  fun tyop info s = "(*(*(*TY\000"^(lazy_string info)^"\000"^s^"*)*)*)"
  fun tysyn info s = "(*(*(*TY\000"^(lazy_string info)^"\000"^s^"*)*)*)"
  fun const {Thy,Name,Ty=(_, tyf)} s = let
    val thy' = if Thy = "" then "overloaded" else Thy
  in
    "(*(*(*CO\000" ^ thy' ^ "$" ^ Name ^ " : " ^ lazy_string tyf ^
    "\000" ^ s ^ "*)*)*)"
  end
  fun add_xstring {s, sz, ann} =
      if not (!backend_use_annotations) orelse not (isSome ann) then
        add_ssz (s,sz)
      else
        let
          open smpp
          val sz = case sz of NONE => UTF8.size s | SOME sz => sz
        in
          case valOf ann of
              FV (_,tystr) => add_stringsz (fv s tystr, sz)
            | BV (_,tystr) => add_stringsz (bv s tystr, sz)
            | Const crec => add_stringsz (const crec s, sz)
            | SymConst crec => add_stringsz (const crec s, sz)
            | TyV => add_stringsz (tyv s, sz)
            | TyOp thy => add_stringsz (tyop thy s, sz)
            | TySyn r => add_stringsz (tysyn r s, sz)
            | _ => add_stringsz (s,sz)
        end

  val style_stack = ref ([]:pp_full_style list);
  fun ustyle sty p =
     if not (!backend_use_styles) then nothing else
     let
        val fsty      = user_push_styleL name style_stack sty
        val sty_str   = full_style_to_emacs_string fsty
        val print_str = "(*(*(*ST\000"^sty_str^"\000";
     in
        add_stringsz (print_str, 0) >> p >> add_stringsz ("*)*)*)", 0)
     end;

in
  {extras = {name           = name,
             tm_grammar_upd = (fn g => g),
             ty_grammar_upd = (fn g => g)},
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   ublock         = #ublock raw_terminal,
   add_string     = #add_string  raw_terminal,
   add_xstring    = add_xstring,
   ustyle         = ustyle}
end;



(* -------------------------------- *)
(* html terminal                    *)
(* -------------------------------- *)

fun color_to_html Black       = "black"
  | color_to_html RedBrown    = "maroon"
  | color_to_html Green       = "green"
  | color_to_html BrownGreen  = "olive"
  | color_to_html DarkBlue    = "navy"
  | color_to_html Purple      = "purple"
  | color_to_html BlueGreen   = "teal"
  | color_to_html DarkGrey    = "gray"
  | color_to_html LightGrey   = "silver"
  | color_to_html OrangeRed   = "red"
  | color_to_html VividGreen  = "lime"
  | color_to_html Yellow      = "yellow"
  | color_to_html Blue        = "blue"
  | color_to_html PinkPurple  = "magenta"
  | color_to_html LightBlue   = "cyan"
  | color_to_html White       = "white";


fun full_style_to_html (fg,bg,b,u,[]) =
   "style=\"" ^
   (* foreground *)
   (if isSome fg then ("color:"^(color_to_html (valOf fg))^"; ") else "") ^
   (* background *)
   (if isSome bg then ("background-color:"^(color_to_html (valOf bg))^"; ")
    else "") ^
   (* bold *)       (if b then "font-weight:bold; " else "") ^
   (* underline *)  (if u then "text-decoration:underline; " else "") ^
   "\""
 | full_style_to_html (_,_,_,_,st::stL) =
   "class=\"hol_pp_"^st^"\"";



fun char_html_escape c =
case c of
  #"<"  => "&lt;"
| #">"  => "&gt;"
| #"&" => "&amp;"
| #"\"" => "&quot;"
| c => Char.toString c

fun html_escape s =
    valOf (String.fromString (String.translate char_html_escape s))

val html_terminal =
let
  val name = "html_terminal";
  open smpp
  fun add_ssz (s,sz) = let
    val sz = case sz of NONE => UTF8.size s | SOME sz => sz
  in add_stringsz (html_escape s, sz) end

  val style_stack = ref ([]:pp_full_style list);
  fun set_style fsty =
      add_stringsz ("<span "^(full_style_to_html fsty)^">", 0)

  fun ustyle styL p =
      if not (!backend_use_styles) then p
      else
        ((if (!backend_use_css) then push_styleL
          else user_push_styleL name) style_stack styL;
         set_style (top_style style_stack)) >>
        p >>
        (pop_style style_stack;
         add_stringsz ("</span>", 0))

  fun add_color_string c ssz =
     (set_style (SOME c, NONE, false, false, []) >>
      add_ssz ssz >>
      add_stringsz ("</span>", 0))


  fun add_ann_string_general ty ls_opt ssz =
     add_stringsz ("<span class=\""^ty^"\"", 0) >>
     (if ((!add_type_information) andalso (isSome ls_opt)) then
        add_stringsz (" title=\""^((valOf ls_opt) ())^"\"", 0)
      else nothing) >>
     add_stringsz (">", 0) >>
     add_ssz ssz >>
     add_stringsz ("</span>", 0)

(* When using CSS you need a style-sheet like
   <style type="text/css">
      span.freevar  {color: blue}
      span.boundvar {color: green}
      span.typevar  {color: purple}
      span.type     {color: teal}
   </style>
*)
  fun add_ann_string___css (ssz, ann) =
      case ann of
        FV (_,tystr) => add_ann_string_general "freevar" (SOME tystr) ssz
      | BV (_,tystr) => add_ann_string_general "boundvar" (SOME tystr) ssz
      | TyV => add_ann_string_general "typevar" NONE ssz
      | TyOp thy => add_ann_string_general "type" (SOME thy) ssz
      | TySyn r => add_ann_string_general "type" (SOME r) ssz
      | _ => add_ssz ssz

  fun add_ann_string___simple (ssz, ann) =
      case ann of
        FV _    => add_color_string Blue ssz
      | BV _    => add_color_string Green ssz
      | TyV     => add_color_string Purple ssz
      | TyOp _  => add_color_string BlueGreen ssz
      | TySyn _ => add_color_string BlueGreen ssz
      | _ => add_ssz ssz

  fun add_xstring {s,sz,ann} =
    if not (!backend_use_annotations) orelse not (isSome ann) then
      add_ssz (s,sz)
    else (if (!backend_use_css) then add_ann_string___css
          else add_ann_string___simple) ((s,sz), valOf ann)
in
  {extras = {name           = name,
             tm_grammar_upd = (fn g => g),
             ty_grammar_upd = (fn g => g)},
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   ublock         = #ublock raw_terminal,
   add_string     = add_string,
   add_xstring    = add_xstring,
   ustyle         = ustyle}
end

end (* struct *)
