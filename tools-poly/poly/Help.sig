signature Help = sig
(* Help -- on-line help functions *)

val help           : string -> unit

val displayLines   : int ref
val helpdirs       : string list ref
val indexfiles     : string list ref
val specialfiles   : {term : string, file : string, title : string} list ref
val welcome        : string vector ref
val browser        : (string -> unit) ref
val defaultBrowser : string -> unit
end;
(*
   [help s] provides on-line help on the topic indicated by string s.

      help "lib";   gives an overview of the Moscow ML library.
      help "id";    provides help on identifier id (case-insensitive).

   If exactly one identifier in the library matches id (case-insensitive),
   then the browser opens the signature defining that identifier,
   positioning the first occurrence of id at the center of the screen.

   If more than one identifier matches id (case-insensitive), then a
   small menu lists the signatures containing the identifier.  To
   invoke the browser, just type in the number of the desired
   signature.

   The browser accepts the following commands, which must be followed
   by a newline:

      d      move down by half a screen
      u      move up by half a screen
      t      move to top of file
      b      move to bottom of file
      /str   cyclically search for string str in help file (case-insensitive)
      n      search for next occurrence of str
      q      quit the browser

   A newline by itself moves down one screen (24 lines).

   [helpdirs] is a reference to a list of additional directories to be
   searched for help files.  The directories are searched in order,
   after the -stdlib directory.

   [indexfiles] is a reference to a list of full paths of help term
   index files.  Setting `indexfiles' affects subsequent invocations
   of `help'.  (Every invocation of `help' reads the index files anew).

   [specialfiles] is a reference to a list of {term, file, title}
   records, each of which maps a search term to the specified file
   with the specified title (in the browser).  The string in the
   `term' field should be all lowercase, since the argument passed to
   `help' will be converted to lowercase.

   [welcome] is a reference to the text shown in response to the query
   help "".  This is a vector of lines of text.

   [browser] is a reference to the function that gets invoked on the
   text of the help file.  Initially set to defaultBrowser.

   [defaultBrowser] is the default (built-in) help browser.

   [displayLines] is a reference to the size of the display (window)
   assumed by the defaultBrowser; initially 24 lines.  Set it to the
   actual size of your window for best results.
*)
