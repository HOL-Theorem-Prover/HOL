structure writerLib =
struct

open HolKernel boolLib bossLib Parse;

val writer_prints = ref true;

local
  val filename_base = ref "output_";
  val filename_current = ref "";
  val current_graph_file = ref (NONE:TextIO.outstream option)
  val last_line_is_blank = ref false;
  fun remove_trailing_underscores s = let
    fun aux (#"_"::cs) = aux cs | aux xs = String.implode (rev xs)
    in aux (rev (String.explode s)) end
  fun graph_filename () = remove_trailing_underscores (!filename_base) ^ "_mc_graph.txt"
  fun print_fail str = (print (str ^ "\n"); failwith str);
in
  fun reset_graph_file () =
    TextIO.closeOut (TextIO.openOut (graph_filename ()))
    handle Io _ => ()
  fun close_current () =
    ((case !current_graph_file of NONE => () | SOME f => TextIO.closeOut f);
     (current_graph_file := NONE))
  fun write_graph str =
    case !current_graph_file of
      NONE => print_fail "Attempt to write to graph file, but no graph file open."
    | SOME f => TextIO.output (f,str)
  fun open_current sec_name =
    (close_current ();
     filename_current := sec_name; last_line_is_blank := false;
     current_graph_file := SOME (TextIO.openAppend (graph_filename ()));
     write_graph "\n")
  fun set_base filename =
    (close_current ();
     filename_base := filename;
     reset_graph_file ())
  fun write_txt_and_print str =
    (if !writer_prints then print str else ())
  fun write_blank_line () =
    if !last_line_is_blank then () else
      (write_txt_and_print "\n"; last_line_is_blank := true)
  fun write_line str =
    (write_txt_and_print (str ^ "\n");
     last_line_is_blank := (size str = 0))
  fun write_section str =
    (write_blank_line ();
     write_line str;
     write_line (String.translate (fn c => "=") str);
     write_blank_line ())
  fun write_subsection str =
    (write_blank_line ();
     write_line str;
     write_line (String.translate (fn c => "-") str);
     write_blank_line ())
  fun write_indented_block str = let
    val lines = String.tokens (fn c => c = #"\n") str
    in (write_blank_line ();
        map (fn l => if l = "" then () else write_line ("    " ^ l)) lines;
        write_blank_line ()) end
  fun write_term th = let
    val _ = set_trace "PPBackEnd use annotations" 0
    val _ = write_indented_block (term_to_string th)
    val _ = set_trace "PPBackEnd use annotations" 1
    in () end
  fun write_thm th = let
    val _ = set_trace "PPBackEnd use annotations" 0
    val a = !Globals.show_assums
    val _ = Globals.show_assums := false
    val _ = write_indented_block (thm_to_string th)
    val _ = set_trace "PPBackEnd use annotations" 1
    in Globals.show_assums := a end
end

end
