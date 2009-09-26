(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions *)

structure Library =
struct

  fun write_strings_to_file path strings =
  let
    val outstream = TextIO.openOut path
  in
    List.app (TextIO.output o Lib.pair outstream) strings;
    TextIO.closeOut outstream
  end

end
