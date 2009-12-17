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

type t = {add_string : ppstream -> string -> unit,
          add_ann_string : ppstream -> string * annotation -> unit,
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
     add_ann_string = #add_ann_string t pps,
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

(*fullstyle: foreground option * background option * bold? * underlined?*)
type pp_full_style = (pp_color option) * (pp_color option) * bool * bool

val base_style = (NONE, NONE, false, false):pp_full_style

fun update_style (_, bg,b,u)  (FG c) = (SOME c, bg, b, u)
  | update_style (fg,_ ,b,u)  (BG c) = (fg, SOME c, b, u)
  | update_style (fg,bg,_,u)  Bold = (fg, bg, true, u)
  | update_style (fg,bg,b,_)  Underline = (fg, bg, b, true)

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


(* ========================================================================== *)
(* terminals                                                                  *)
(* ========================================================================== *)


(* -------------------------------- *)
(* Traces                           *)
(* -------------------------------- *)

val emacs_add_type_information = ref true
val _ = Feedback.register_btrace ("emacs_terminal show types", emacs_add_type_information);

val backend_use_annotations = ref true
val _ = Feedback.register_btrace ("PPBackEnd use annotations", backend_use_annotations);

val backend_use_styles = ref true
val _ = Feedback.register_btrace ("PPBackEnd use styles", backend_use_styles);


(* -------------------------------- *)
(* raw terminal                     *)
(* -------------------------------- *)

val raw_terminal = {
   name = "raw_terminal",
   add_break      = PP.add_break,
   add_string     = PP.add_string,
   add_ann_string = (fn pps => fn (s,_) => PP.add_string pps s),
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


fun full_style_to_vt100 (fg,bg,b,u) =
   (* reset *)      "\027[0"^ 
   (* foreground *) (if isSome fg then (fg_to_vt100 (valOf fg)) else "") ^ 
   (* background *) (if isSome bg then (bg_to_vt100 (valOf bg)) else "") ^
   (* bold *)       (if b then ";1" else "") ^
   (* underline *)  (if u then ";4" else "") ^ 
   (* done *)       "m";


val vt100_terminal = 
let
  val style_stack = ref ([]:pp_full_style list);
  fun set_style pps fsty =
      PP.add_stringsz pps (full_style_to_vt100 fsty, 0)

  fun reset_style pps = set_style pps (top_style style_stack)

  fun begin_style pps styL = if not (!backend_use_styles) then () else
        (push_styleL style_stack styL;
         reset_style pps);

  fun end_style pps = if not (!backend_use_styles) then () else
        (pop_style style_stack;
         reset_style pps);

  fun add_color_string pps c s =
     (set_style pps (SOME c, NONE, false, false);
      PP.add_string pps s;
      reset_style pps);

  fun add_ann_string pps (s, ann) =
      if not (!backend_use_annotations) then PP.add_string pps s else

      case ann of
        FV _    => add_color_string pps Blue s
      | BV _    => add_color_string pps Green s
      | TyV     => add_color_string pps Purple s
      | TyOp _  => add_color_string pps BlueGreen s
      | TySyn _ => add_color_string pps BlueGreen s
      | _ => PP.add_string pps s
in
  {name           = "vt100_terminal",
   add_ann_string = add_ann_string,
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   begin_block    = #begin_block raw_terminal,
   end_block      = #end_block   raw_terminal,
   add_string     = #add_string  raw_terminal,
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

fun full_style_to_emacs_string (fg,bg,b,u) =
   (color_option_to_string fg) ^ 
   (color_option_to_string bg) ^ 
   (bool_to_string b) ^
   (bool_to_string u);


val emacs_terminal = let
  val sz = UTF8.size
  fun lazy_string ls = if !emacs_add_type_information then (ls ()) else "";
  fun fv s tystr = "(*(*(*FV\000"^(lazy_string tystr)^"\000"^s^"*)*)*)"
  fun bv s tystr = "(*(*(*BV\000"^(lazy_string tystr)^"\000"^s^"*)*)*)"
  fun tyv s = "(*(*(*TV"^s^"*)*)*)"
  fun tyop info s = "(*(*(*TY\000"^(lazy_string info)^"\000"^s^"*)*)*)"
  fun tysyn info s = "(*(*(*TY\000"^(lazy_string info)^"\000"^s^"*)*)*)"
  fun add_ann_string pps (s, ann) =
      if not (!backend_use_annotations) then PP.add_string pps s else
      case ann of
        FV (_,tystr) => PP.add_stringsz pps (fv s tystr, sz s)
      | BV (_,tystr) => PP.add_stringsz pps (bv s tystr, sz s)
      | TyV => PP.add_stringsz pps (tyv s, sz s)
      | TyOp thy => PP.add_stringsz pps (tyop thy s, sz s)
      | TySyn r => PP.add_stringsz pps (tysyn r s, sz s)
      | _ => PP.add_string pps s


  val style_stack = ref ([]:pp_full_style list);     
  fun begin_style pps sty =
     if not (!backend_use_styles) then () else
     let
        val fsty      = push_styleL style_stack sty
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
  {name           = "emacs_terminal",
   add_ann_string = add_ann_string,
   add_break      = #add_break   raw_terminal,
   add_newline    = #add_newline raw_terminal,
   begin_block    = #begin_block raw_terminal,
   end_block      = #end_block   raw_terminal,
   add_string     = #add_string  raw_terminal,
   begin_style    = begin_style,
   end_style      = end_style}
end;


end (* struct *)
