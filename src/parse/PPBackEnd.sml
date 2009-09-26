structure PPBackEnd :> PPBackEnd =
struct

type kind = Kind.kind
type hol_type = Type.hol_type
open Portable

datatype annotation = BV of hol_type * string
                    | FV of hol_type * string
                    | TyBV of kind * int (*rank*) * string
                    | TyFV of kind * int (*rank*) * string
                    | TyOp of string
                    | TySyn of string
                    | Const of {Thy:string,Name:string,Ty:hol_type} * string
                    | Note of string

type t = {add_string : ppstream -> string -> unit,
          add_ann_string : ppstream -> string * annotation -> unit,
          begin_block : ppstream -> PP.break_style -> int -> unit,
          end_block : ppstream -> unit,
          add_break : ppstream -> int * int -> unit,
          add_newline : ppstream -> unit,
          name : string}

fun with_ppstream (t:t) pps =
    {add_break = #add_break t pps,
     add_newline = (fn () => #add_newline t pps),
     add_string = #add_string t pps,
     add_ann_string = #add_ann_string t pps,
     begin_block = #begin_block t pps,
     end_block = (fn () => #end_block t pps),
     clear_ppstream = (fn () => PP.clear_ppstream pps),
     flush_ppstream = (fn () => PP.flush_ppstream pps)
    }

val raw_terminal =
    {add_break = PP.add_break,
     add_string = PP.add_string,
     add_ann_string = (fn pps => fn (s,_) => PP.add_string pps s),
     add_newline = PP.add_newline,
     begin_block = PP.begin_block,
     end_block = PP.end_block,
     name = "raw_terminal"}

val vt100_terminal = let
  fun boldblue s = "\027[1;34m" ^ s ^ "\027[0m"
  fun green s = "\027[32m" ^ s ^ "\027[0m"
  fun cyan s = "\027[36m" ^ s ^ "\027[0m"
  fun purple s = "\027[35m" ^ s ^ "\027[0m"
  fun brown s = "\027[0;33m" ^ s ^ "\027[0m"
  fun add_ann_string pps (s, ann) =
      case ann of
        FV _ => PP.add_stringsz pps (boldblue s, UTF8.size s)
      | BV _ => PP.add_stringsz pps (green s, UTF8.size s)
      | TyFV _ => PP.add_stringsz pps (purple s, UTF8.size s)
      | TyBV _ => PP.add_stringsz pps (brown s, UTF8.size s)
      | TyOp _ => PP.add_stringsz pps (cyan s, UTF8.size s)
      | TySyn _ => PP.add_stringsz pps (cyan s, UTF8.size s)
      | _ => PP.add_string pps s
in
  {add_break = PP.add_break,
   add_string = PP.add_string,
   add_ann_string = add_ann_string,
   add_newline = PP.add_newline,
   begin_block = PP.begin_block,
   end_block = PP.end_block,
   name = "vt100_terminal"}
end

val emacs_terminal = let
  val sz = UTF8.size
  fun fv s tystr = "(*(*(*FV\000"^tystr^"\000"^s^"*)*)*)"
  fun bv s tystr = "(*(*(*BV\000"^tystr^"\000"^s^"*)*)*)"
  fun tyfv s kdstr = "(*(*(*TF\000"^kdstr^"\000"^s^"*)*)*)"
  fun tybv s kdstr = "(*(*(*TB\000"^kdstr^"\000"^s^"*)*)*)"
  fun tyop info s = "(*(*(*TY\000"^info^"\000"^s^"*)*)*)"
  fun tysyn info s = "(*(*(*TY\000"^info^"\000"^s^"*)*)*)"
  fun add_ann_string pps (s, ann) =
      case ann of
        FV (_,tystr) => PP.add_stringsz pps (fv s tystr, sz s)
      | BV (_,tystr) => PP.add_stringsz pps (bv s tystr, sz s)
      | TyFV (_,_,kdstr) => PP.add_stringsz pps (tyfv s kdstr, sz s)
      | TyBV (_,_,kdstr) => PP.add_stringsz pps (tybv s kdstr, sz s)
      | TyOp thy => PP.add_stringsz pps (tyop thy s, sz s)
      | TySyn r => PP.add_stringsz pps (tysyn r s, sz s)
      | _ => PP.add_string pps s
in
  {name = "emacs_terminal",
   add_break = #add_break raw_terminal,
   add_newline = #add_newline raw_terminal,
   add_ann_string = add_ann_string,
   begin_block = #begin_block raw_terminal,
   end_block = #end_block raw_terminal,
   add_string = #add_string raw_terminal}
end

end (* struct *)
