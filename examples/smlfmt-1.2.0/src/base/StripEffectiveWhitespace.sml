(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure StripEffectiveWhitespace:
sig
  val strip: {tabWidth: int, removeAtMost: int}
             -> string
             -> {removed: int, result: string}
end =
struct

  fun strip {tabWidth, removeAtMost = n} s =
    let
      (* val _ =
        ( print ( "TCS.stripEffectiveWhitespace\n"
                ^ "  tabWidth " ^ Int.toString tabWidth ^ "\n"
                ^ "  removeAtMost " ^ Int.toString n ^ "\n"
                ^ "  string " ^ String.toString s ^ "\n")) *)

      (** Walk forwards in the string, keep track of current index i
        * and count of effective whitespace that has been stripped.
        * Normal characters count 1 effective, and tabs are handled
        * specially.
        *
        * Returns the final count and index, as well as possibly a new
        * front for the string (where a tab has been split into multiple
        * spaces).
        *
        * TODO: Generalize this for arbitrary characters with arbitrary
        * widths?
        *)
      fun loop count i =
        if count >= n orelse i >= String.size s then
          ("", count, i)
        else if String.sub (s, i) = #"\t" then
          let
            val tabstop = count + tabWidth - count mod tabWidth
          in
            if tabstop <= n then
              loop tabstop (i + 1)
            else
              let val newfront = CharVector.tabulate (tabstop - n, fn _ => #" ")
              in (newfront, count, i)
              end
          end
        else if Char.isSpace (String.sub (s, i)) then
          loop (count + 1) (i + 1)
        else
          ("", count, i)

      val (newfront, count, i) = loop 0 0
    (* val _ =
      print ( "  count " ^ Int.toString count ^ "\n"
            ^ "  idx " ^ Int.toString i ^ "\n") *)
    in
      {removed = count, result = newfront ^ String.extract (s, i, NONE)}
    end

end
