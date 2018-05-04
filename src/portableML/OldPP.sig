signature OldPP =
sig
(* PP -- pretty-printing -- from the SML/NJ library *)

type ppstream
type ppconsumer = { consumer  : string -> unit,
                    linewidth : int,
                    flush     : unit -> unit }

datatype break_style = datatype HOLPP.break_style

type ppstream_interface =
     { add_stringsz : (string * int) -> unit,
       add_break : int * int -> unit,
       begin_block : break_style -> int -> unit,
       clear_ppstream : unit -> unit,
       end_block : unit -> unit,
       flush : unit -> unit,
       linewidth : int}

datatype frag = datatype HOLPP.frag
type 'a quotation = 'a frag list

val mk_ppstream    : ppconsumer -> ppstream
val pps_from_iface : ppstream_interface -> ppstream
val add_break      : ppstream -> int * int -> unit
val add_newline    : ppstream -> unit
val add_string     : ppstream -> string -> unit
val add_stringsz   : ppstream -> (string * int) -> unit
val begin_block    : ppstream -> break_style -> int -> unit
val end_block      : ppstream -> unit
val clear_ppstream : ppstream -> unit
val flush_ppstream : ppstream -> unit
val with_pp        : ppconsumer -> (ppstream -> unit) -> unit
val pp_to_string   : int -> (ppstream -> 'a -> unit) -> 'a -> string
val lineWidth      : ppstream -> int
val catch_withpp_err : bool ref

val pr_list : ('a -> unit) -> (unit -> 'b) -> (unit -> 'c) -> 'a list ->
              unit

val with_ppstream : ppstream ->
                    {add_break      : int * int -> unit,
                     add_newline    : unit -> unit,
                     add_string     : string -> unit,
                     begin_block    : HOLPP.break_style -> int -> unit,
                     clear_ppstream : unit -> unit,
                     end_block      : unit -> unit,
                     flush_ppstream : unit -> unit}

(*
   This structure provides tools for creating customized Oppen-style
   pretty-printers, based on the type ppstream.  A ppstream is an
   output stream that contains prettyprinting commands.  The commands
   are placed in the stream by various function calls listed below.

   There following primitives add commands to the stream:
   begin_block, end_block, add_string, add_break, and add_newline.
   All calls to add_string, add_break, and add_newline must happen
   between a pair of calls to begin_block and end_block must be
   properly nested dynamically.  All calls to begin_block and
   end_block must be properly nested (dynamically).

   [ppconsumer] is the type of sinks for pretty-printing.  A value of
   type ppconsumer is a record
                 { consumer  : string -> unit,
                   linewidth : int,
                   flush     : unit -> unit }
   of a string consumer, a specified linewidth, and a flush function
   which is called whenever flush_ppstream is called.

   A prettyprinter can be called outright to print a value.  In
   addition, a prettyprinter for a base type or nullary datatype ty
   can be installed in the top-level system.  Then the installed
   prettyprinter will be invoked automatically whenever a value of
   type ty is to be printed.

   [break_style] is the type of line break styles for blocks:

   [CONSISTENT] specifies that if any line break occurs inside the
   block, then all indicated line breaks occur.

   [INCONSISTENT] specifies that breaks will be inserted to only to
   avoid overfull lines.

   [mk_ppstream {consumer, linewidth, flush}] creates a new ppstream
   which invokes the consumer to output text, putting at most
   linewidth characters on each line.

   [dest_ppstream ppstrm] extracts the linewidth, flush function, and
   consumer from a ppstream.

   [add_break ppstrm (size, offset)] notifies the pretty-printer that
   a line break is possible at this point.
   * When the current block style is CONSISTENT:
      ** if the entire block fits on the remainder of the line, then
         output size spaces; else
      ** increase the current indentation by the block offset;
         further indent every item of the block by offset, and add
         one newline at every add_break in the block.
   * When the current block style is INCONSISTENT:
      ** if the next component of the block fits on the remainder of
         the line, then output size spaces; else
      ** issue a newline and indent to the current indentation level
         plus the block offset plus the offset.

   [add_newline ppstrm] issues a newline.

   [add_stringsz ppstrm str] outputs the string str to the ppstream
   (calculating its width using the UTF8.size function).

   [add_string ppstrm (str,sz)] outputs the string str to the ppstream
   but the ppstream treats it as if it were sz many characters wide
   rather than its true width.

   [begin_block ppstrm style blockoffset] begins a new block and
   level of indentation, with the given style and block offset.

   [end_block ppstrm] closes the current block.

   [clear_ppstream ppstrm] restarts the stream, without affecting the
   underlying consumer.

   [flush_ppstream ppstrm] executes any remaining commands in the
   ppstream (that is, flushes currently accumulated output to the
   consumer associated with ppstrm); executes the flush function
   associated with the consumer; and calls clear_ppstream.

   [with_pp consumer f] makes a new ppstream from the consumer and
   applies f (which can be thought of as a producer) to that
   ppstream, then flushed the ppstream and returns the value of f.

   [pp_to_string linewidth printit x] constructs a new ppstream
   ppstrm whose consumer accumulates the output in a string s.  Then
   evaluates (printit ppstrm x) and finally returns the string s.
*)
end
