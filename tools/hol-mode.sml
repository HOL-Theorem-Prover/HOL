(*=====================================================================  *)
(* FILE          : holmode.sml                                           *)
(* DESCRIPTION   : some ml-callbacks used by hol-mode                    *)
(* ===================================================================== *)



(*
   val use_goal_stack = true;
   val context_string_opt = SOME ("f (SOME x) (SOME 0) = T");
   val term_string = "f";

   (set_goal ([], ``f y = F``))
*)

val _ = load "Sanity";

local
   fun repeat_print s n = if (n <= 0) then () else (print s; repeat_print s (n-1));
   val print_space = repeat_print " ";
   fun print_width n s = (print s; (print_space (n - (size s))));
   fun print_header c s =
      (print s;print "\n";repeat_print c (if (size s) < 70 then size s else 70);print "\n");

in

fun type_of_in_context use_goal_stack context_string_opt term_string =
let
   fun term_does_type_match t1 t2 =
   let
      val (vsubst, _) = match_term t1 t2
   in
      null vsubst
   end handle HOL_ERR _ => false


   (*no context*)
   val term_no_context_term =
      Parse.parse_in_context [] [QUOTE term_string]

   (*user context*)
   val context_term_opt =
      if isSome context_string_opt then
         total (Parse.parse_in_context []) [QUOTE (valOf context_string_opt)]
      else NONE;

   val (term_user_context_term,context_matchesL) =
      if not (isSome context_term_opt) then
         (term_no_context_term, [])
      else (
         Parse.parse_in_context (free_vars (valOf context_term_opt)) [QUOTE term_string],

         HOLset.listItems (HOLset.addList (empty_tmset,
         (find_terms (term_does_type_match (term_no_context_term))
           (valOf context_term_opt)))));


   (*goalstack context*)
   val goalstack_context = (if use_goal_stack then
                    (flatten (map (fn (ts,t) => t::ts) (proofManagerLib.top_goals())))
                 else []) handle Interrupt => raise Interrupt | _ => [];

   val term_goalstack_context_term =
      Parse.parse_in_context (free_varsl goalstack_context) [QUOTE term_string]

   val goalstack_matchesL = HOLset.listItems (
      HOLset.addList (empty_tmset,
         flatten (map (find_terms (term_does_type_match (term_no_context_term)))
         goalstack_context)))
in
   (term_no_context_term, term_user_context_term, term_goalstack_context_term,
    context_matchesL, goalstack_matchesL)
end;



fun print_type_of_in_context use_goal_stack context_string_opt term_string =
let
   val (t1, t2, t3, tL1, tL2) =
      type_of_in_context use_goal_stack context_string_opt term_string;

   val t1s = term_to_string t1
   val t2s = term_to_string t2
   val t3s = term_to_string t3
   val tL1s = map term_to_string tL1
   val tL2s = map term_to_string tL2

   val list_max = foldl (fn (a,b) => if a > b then a else b) 0

   fun print_term_width w (t,s) =
      (print_width w s;
       print " ";
       print (type_to_string (type_of t));print "\n")
   val print_term = print_term_width 0;


   fun print_term_list l =
       let
          val max_width = list_max (map (size o snd) l)
       in
          map (print_term_width max_width) l;()
       end;

in
   print "\n\n\n\n";
   print_header "=" ("\nType information for \"" ^ term_string ^ "\"");
   print "\n\n";
   print_header "-" "No context:";
   print_term (t1, t1s);
   (if ((aconv t1 t2) orelse not (isSome context_string_opt)) then () else (
      print "\n\n";
      print_header "-" ("In context \"" ^ (valOf context_string_opt) ^ "\":");
      print_term (t2,t2s)));
   (if (aconv t1 t3) then () else (
      print "\n\n";
      print_header "-" ("In goalstack context:");
      print_term (t3, t3s)));
   (if (null tL1) then () else (
      print "\n\n";
      print_header "-" ("Matching subterms in context \"" ^ (valOf context_string_opt) ^ "\":");
      print_term_list (zip tL1 tL1s)));
   (if (null tL2) then () else (
      print "\n\n";
      print_header "-" ("Matching subterms in goalstack-context:");
      print_term_list (zip tL2 tL2s)));
   print "\n\n\n\n"
end;


fun print_current_load_paths () =
let
   val paths = !loadPath
   val _ = print "\n\n";
   val _ = print_header "-" "Current loadPath";
   val _ = map (fn t => (print "  ";print t; print "\n")) paths
   val _ = print "\n";
in
   ()
end;


fun emacs_hol_mode_loaded () =
   ["HOL_Interactive", "Meta",
  "Array", "ArraySlice", "BinIO", "BinPrimIO", "Bool", "Byte",
  "CharArray", "CharArraySlice", "Char", "CharVector",
  "CharVectorSlice", "CommandLine.name", "Date", "General", "IEEEReal",
  "Int", "IO", "LargeInt", "LargeReal", "LargeWord", "List", "ListPair",
  "Math", "Option", "OS", "Position", "Real", "StringCvt", "String",
  "Substring", "TextIO", "TextPrimIO", "Text", "Timer", "Time",
  "VectorSlice", "Vector", "Word8Array", "Word8ArraySlice",
  "Word8Vector", "Word8VectorSlice", "Word8", "Word"] @ (Meta.loaded());

fun print_hol_mode_loaded () =
let
   val loaded = emacs_hol_mode_loaded();
   val sorted_loaded = sort (fn s1 => fn s2 => String.< (s1, s2)) loaded
   val _ = print "\n\n";
   val _ = print_header "-" "Loaded Modules";
   val _ = List.map (fn t => (print "  ";print t; print "\n")) sorted_loaded
   val _ = print "\n";
in
   ()
end;

fun print_current_hol_status hol_ex holmake_ex () = let
  val _ = HOL_Interactive.print_banner()
  val _ = print "\n";
  val _ = (print "Hol executable    : "; print hol_ex; print "\n");
  val _ = (print "Holmake executable: "; print holmake_ex; print "\n");
  val _ = (print "Holdir            : "; print HOLDIR; print "\n");
  val _ = print_current_load_paths();
  val _ = print_hol_mode_loaded();
in
  ()
end;

end;
