structure PPBackEnd :> PPBackEnd =
struct

type hol_type = Type.hol_type
open Portable




(* ========================================================================== *)
(* Datatypes used by the backends                                             *)
(* ========================================================================== *)

datatype annotation = BV of hol_type * (unit -> string)
                    | FV of hol_type * (unit -> string)
                    | TyV
                    | TyOp of (unit -> string)
                    | TySyn of (unit -> string)
                    | Const of {Thy:string,Name:string,Ty:hol_type} * string
                    | Note of string;

(* The default 16 color palette *)
datatype pp_color =
    Black     | RedBrown   | Green      | BrownGreen
  | DarkBlue  | Purple     | BlueGreen  | DarkGrey
  | LightGrey | OrangeRed  | VividGreen | Yellow
  | Blue      | PinkPurple | LightBlue  | White;

datatype pp_style =
    FG of pp_color
  | BG of pp_color
  | Bold
  | Underline
  | UserStyle of string;

type xstring = {s:string,sz:int option,ann:annotation option}

type t = {add_string : ppstream -> string -> unit,
          add_xstring : ppstream -> xstring -> unit,
          begin_block : ppstream -> PP.break_style -> int -> unit,
          end_block : ppstream -> unit,
          add_break : ppstream -> int * int -> unit,
          add_newline : ppstream -> unit,
          begin_style : ppstream -> pp_style list -> unit,
          end_style : ppstream -> unit,
          name : string}


(* ========================================================================== *)
(* with_pp_stream                                                             *)
(* ========================================================================== *)

fun with_ppstream (t:t) pps =
    {add_break = #add_break t pps,
     add_newline = (fn () => #add_newline t pps),
     add_string = #add_string t pps,
     add_xstring = #add_xstring t pps,
     begin_block = #begin_block t pps,
     end_block = (fn () => #end_block t pps),
     begin_style = #begin_style t pps,
     end_style = (fn () => #end_style t pps),
     clear_ppstream = (fn () => PP.clear_ppstream pps),
     flush_ppstream = (fn () => PP.flush_ppstream pps)
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
    expand_UserStyle b ((lookup_UserStyle b st)@styL)
  | expand_UserStyle b (st::styL) =
    (st::(expand_UserStyle b styL))

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

fun add_ssz pps (s,sz) =
  case sz of NONE => PP.add_string pps s
           | SOME sz => PP.add_stringsz pps (s,sz)

(* -------------------------------- *)
(* raw terminal                     *)
(* -------------------------------- *)

val raw_terminal : t = {
   name = "raw_terminal",
   add_break      = PP.add_break,
   add_string     = PP.add_string,
   add_xstring    = (fn pps => fn {s,sz,...} => add_ssz pps (s,sz)),
   add_newline    = PP.add_newline,
   begin_block    = PP.begin_block,
   end_block      = PP.end_block,
   begin_style    = fn pps => fn sty => (),
   end_style      = fn pps => ()}


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


val vt100_terminal =
let
  val name = "vt100_terminal";
  val style_stack = ref ([]:pp_full_style list);
  fun set_style pps fsty =
      PP.add_stringsz pps (full_style_to_vt100 fsty, 0)

  fun reset_style pps = set_style pps (top_style style_stack)

  fun begin_style pps styL = if not (!backend_use_styles) then () else
        (user_push_styleL name style_stack styL;
         reset_style pps);

  fun end_style pps = if not (!backend_use_styles) then () else
        (pop_style style_stack;
         reset_style pps);

  fun add_color_string pps c ssz =
     (set_style pps (SOME c, NONE, false, false, []);
      add_ssz pps ssz;
      reset_style pps);

  fun add_xstring pps {s,sz,ann} =
      if not (!backend_use_annotations) orelse not (isSome ann)
      then add_ssz pps (s,sz) else

      case valOf ann of
        FV _    => add_color_string pps Blue (s,sz)
      | BV _    => add_color_string pps Green (s,sz)
      | TyV     => add_color_string pps Purple (s,sz)
      | TyOp _  => add_color_string pps BlueGreen (s,sz)
      | TySyn _ => add_color_string pps BlueGreen (s,sz)
      | _ => add_ssz pps (s,sz)
in
  {name           = name,
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   begin_block    = #begin_block raw_terminal,
   end_block      = #end_block   raw_terminal,
   add_string     = #add_string  raw_terminal,
   add_xstring    = add_xstring,
   begin_style    = begin_style,
   end_style      = end_style}
end


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
  val name = "emacs_terminal";
  fun lazy_string ls = if !add_type_information then (ls ()) else "";
  fun fv s tystr = "(*(*(*FV\000"^(lazy_string tystr)^"\000"^s^"*)*)*)"
  fun bv s tystr = "(*(*(*BV\000"^(lazy_string tystr)^"\000"^s^"*)*)*)"
  fun tyv s = "(*(*(*TV"^s^"*)*)*)"
  fun tyop info s = "(*(*(*TY\000"^(lazy_string info)^"\000"^s^"*)*)*)"
  fun tysyn info s = "(*(*(*TY\000"^(lazy_string info)^"\000"^s^"*)*)*)"
  fun add_xstring pps {s, sz, ann} =
      if not (!backend_use_annotations) orelse not (isSome ann) then
        add_ssz pps (s,sz) else
      let val sz = case sz of NONE => UTF8.size s | SOME sz => sz in
      case valOf ann of
        FV (_,tystr) => PP.add_stringsz pps (fv s tystr, sz)
      | BV (_,tystr) => PP.add_stringsz pps (bv s tystr, sz)
      | TyV => PP.add_stringsz pps (tyv s, sz)
      | TyOp thy => PP.add_stringsz pps (tyop thy s, sz)
      | TySyn r => PP.add_stringsz pps (tysyn r s, sz)
      | _ => PP.add_stringsz pps (s,sz)
      end

  val style_stack = ref ([]:pp_full_style list);
  fun begin_style pps sty =
     if not (!backend_use_styles) then () else
     let
        val fsty      = user_push_styleL name style_stack sty
        val sty_str   = full_style_to_emacs_string fsty
        val print_str = "(*(*(*ST\000"^sty_str^"\000";
     in
        PP.add_stringsz pps (print_str, 0)
     end;

  fun end_style pps =
     if not (!backend_use_styles) then () else
     let
        val _ = pop_style style_stack
        val print_str = "*)*)*)";
     in
        PP.add_stringsz pps (print_str, 0)
     end;

in
  {name           = name,
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   begin_block    = #begin_block raw_terminal,
   end_block      = #end_block   raw_terminal,
   add_string     = #add_string  raw_terminal,
   add_xstring    = add_xstring,
   begin_style    = begin_style,
   end_style      = end_style}
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
  fun add_ssz pps (s,sz) = let
    val sz = case sz of NONE => UTF8.size s | SOME sz => sz
  in PP.add_stringsz pps (html_escape s, sz) end

  val style_stack = ref ([]:pp_full_style list);
  fun set_style pps fsty =
      PP.add_stringsz pps ("<span "^(full_style_to_html fsty)^">", 0)


  fun reset_style pps = PP.add_stringsz pps ("</span>", 0)

  fun begin_style pps styL =
      if not (!backend_use_styles) then ()
      else ((if (!backend_use_css) then push_styleL
             else user_push_styleL name) style_stack styL;
            set_style pps (top_style style_stack))

  fun end_style pps =
      if not (!backend_use_styles) then ()
      else
        (pop_style style_stack;
         PP.add_stringsz pps ("</span>", 0))

  fun add_color_string pps c ssz =
     (set_style pps (SOME c, NONE, false, false, []);
      add_ssz pps ssz;
      reset_style pps);


  fun add_ann_string_general pps ty ls_opt ssz =
  let
     val _ = PP.add_stringsz pps ("<span class=\""^ty^"\"", 0)
     val _ = if ((!add_type_information) andalso (isSome ls_opt)) then
               PP.add_stringsz pps (" title=\""^((valOf ls_opt) ())^"\"", 0)
             else ()
     val _ = PP.add_stringsz pps (">", 0)
     val _ = add_ssz pps ssz
     val _ = PP.add_stringsz pps ("</span>", 0)
  in
     ()
  end;

(* When using CSS you need a style-sheet like
   <style type="text/css">
      span.freevar  {color: blue}
      span.boundvar {color: green}
      span.typevar  {color: purple}
      span.type     {color: teal}
   </style>
*)
  fun add_ann_string___css pps (ssz, ann) =
      case ann of
        FV (_,tystr) => add_ann_string_general pps "freevar" (SOME tystr) ssz
      | BV (_,tystr) => add_ann_string_general pps "boundvar" (SOME tystr) ssz
      | TyV => add_ann_string_general pps "typevar" NONE ssz
      | TyOp thy => add_ann_string_general pps "type" (SOME thy) ssz
      | TySyn r => add_ann_string_general pps "type" (SOME r) ssz
      | _ => add_ssz pps ssz

  fun add_ann_string___simple pps (ssz, ann) =
      case ann of
        FV _    => add_color_string pps Blue ssz
      | BV _    => add_color_string pps Green ssz
      | TyV     => add_color_string pps Purple ssz
      | TyOp _  => add_color_string pps BlueGreen ssz
      | TySyn _ => add_color_string pps BlueGreen ssz
      | _ => add_ssz pps ssz

  fun add_xstring pps {s,sz,ann} =
    if not (!backend_use_annotations) orelse not (isSome ann) then
      add_ssz pps (s,sz)
    else (if (!backend_use_css) then add_ann_string___css
          else add_ann_string___simple) pps ((s,sz), valOf ann)
in
  {name           = name,
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   begin_block    = #begin_block raw_terminal,
   end_block      = #end_block   raw_terminal,
   add_string     = add_string,
   add_xstring    = add_xstring,
   begin_style    = begin_style,
   end_style      = end_style}
end


end (* struct *)
