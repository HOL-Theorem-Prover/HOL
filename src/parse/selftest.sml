open PPBackEnd PP Lib Type;

(* -------------------------------------------------------------------------- *)
(* Test code for terminal styles                                              *)
(* -------------------------------------------------------------------------- *)

val color_name_fw_spaces      = "          ";
fun color_name_fw Black       = "Black     "
  | color_name_fw RedBrown    = "RedBrown  "
  | color_name_fw Green       = "Green     "
  | color_name_fw BrownGreen  = "BrownGreen"
  | color_name_fw DarkBlue    = "DarkBlue  "
  | color_name_fw Purple      = "Purple    "
  | color_name_fw BlueGreen   = "BlueGreen "
  | color_name_fw DarkGrey    = "DarkGrey  "
  | color_name_fw LightGrey   = "LightGrey "
  | color_name_fw OrangeRed   = "OrangeRed "
  | color_name_fw VividGreen  = "VividGreen"
  | color_name_fw Yellow      = "Yellow    "
  | color_name_fw Blue        = "Blue      "
  | color_name_fw PinkPurple  = "PinkPurple"
  | color_name_fw LightBlue   = "LightBlue "
  | color_name_fw White       = "White     ";


val color_list =
  [ Black     , RedBrown   , Green      , BrownGreen,
    DarkBlue  , Purple     , BlueGreen  , DarkGrey,
    LightGrey , OrangeRed  , VividGreen , Yellow,
    Blue      , PinkPurple , LightBlue  , White]


fun test_terminal test_bg (terminal:t) =
let
   val pp_out = Portable.stdOut_ppstream ();
   val {add_string, add_ann_string, add_newline, add_break,
        begin_style, end_style, begin_block, end_block, ...} =
       with_ppstream terminal pp_out

   val fg_styles =
          ((" -            "^color_name_fw_spaces), [])::
     map (fn c =>
          ((" - Foreground "^(color_name_fw c)), [FG c])) color_list
   val bold_fg_styles =
     (map (fn (s, styL) => (" -     "^s, styL)) fg_styles)@
     (map (fn (s, styL) => (" - Bold"^s, Bold::styL)) fg_styles)
   val und_fg_styles =
     (map (fn (s, styL) => ("         "^s, styL)) bold_fg_styles)@
     (map (fn (s, styL) => ("Underline"^s, Underline::styL)) bold_fg_styles)

   val full_styles = if not test_bg then und_fg_styles else
     (flatten (
        (map (fn (s, styL) =>
            ((s^" -            "^color_name_fw_spaces), styL)) und_fg_styles)::
         (map (fn c =>
          map (fn (s, styL) =>
            ((s^" - Background "^(color_name_fw c)), (BG c)::styL)) und_fg_styles)
          color_list)))
in
   PP.clear_ppstream pp_out;
   (#begin_block terminal) pp_out INCONSISTENT 0;

   add_string "Terminal testing"; add_newline();
   add_string "================"; add_newline();
   add_newline();

   add_string "Annotations:"; add_newline();
   add_string "------------"; add_newline();
   add_ann_string ("Bound variable", BV (bool, fn () => ": bool"));
   add_newline();
   add_ann_string ("Free variable", FV (bool, fn () => ": bool"));
   add_newline();
   add_ann_string ("Type variable", TyV);
   add_newline();
   add_ann_string ("TySyn", TySyn (fn () => "TySyn"));
   add_newline();
   add_ann_string ("TyOp", TyOp (fn () => "TyOp"));
   add_newline();
   add_ann_string ("Const", Const ({Name = "test-name", Thy = "test-thy",
        Ty = Type.bool},"==>"));
   add_newline();
   add_ann_string ("Note", Note "Some note") ;
   add_newline();

   add_newline(); add_newline();

   add_string "Basic styles:"; add_newline();
   add_string "-------------"; add_newline();
   add_string "default style"; add_newline();
   begin_style [Bold]; add_string "Bold"; end_style(); add_newline();
   begin_style [Underline]; add_string "Underline"; end_style(); add_newline();
   map (fn c => (
      add_string "Foreground ";
      begin_style [FG c]; 
          add_string (color_name_fw c); 
      end_style(); add_newline())) color_list;
   map (fn c => (
      add_string "Background ";
      begin_style [BG c]; 
          add_string (color_name_fw c); 
      end_style(); add_newline())) color_list;

   add_newline(); add_newline();

   if test_bg then (
      add_string "All style combinations:"; add_newline();
      add_string "------------------------"; add_newline()
   ) else (
      add_string "All style combinations (without background color):"; add_newline();
      add_string "--------------------------------------------------"; add_newline()
   );
   map (fn (s, styL) => (
      begin_style styL; 
          add_string s; 
      end_style(); add_newline())) full_styles;
   add_newline();add_newline();

   (#end_block terminal) pp_out;
   PP.flush_ppstream pp_out
end;


val _ = print "raw terminal\n";
val _ = print "============\n\n";
val _ = test_terminal false (PPBackEnd.raw_terminal);

val _ = print "emacs terminal\n";
val _ = print "==============\n\n";
val _ = test_terminal false (PPBackEnd.emacs_terminal);
			 
val _ = print "vt100 terminal\n";
val _ = print "==============\n\n";
val _ = test_terminal false (PPBackEnd.vt100_terminal);



(* -------------------------------------------------------------------------- *)
(* Test code for style errors (non terminated style)                          *)
(* -------------------------------------------------------------------------- *)

fun test_style_error (terminal:t) =
let
   val pp_out = Portable.stdOut_ppstream ();
   val {add_string, add_ann_string, add_newline, add_break,
        begin_style, end_style, begin_block, end_block, ...} =
       with_ppstream terminal pp_out
in
   PP.clear_ppstream pp_out;
   (#begin_block terminal) pp_out INCONSISTENT 0;

   add_string "Style error";
   begin_style [Bold]; add_string "...."; add_newline();

   (#end_block terminal) pp_out;
   PP.flush_ppstream pp_out
end;

(*

full test including backgrounds
val _ = test_terminal true (!Parse.current_backend)


error testing for backends (be careful)
val _ = test_style_error (!Parse.current_backend)

*)
