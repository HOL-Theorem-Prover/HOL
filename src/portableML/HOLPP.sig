signature HOLPP =
sig
(* PP -- pretty-printing -- from the SML/NJ library *)

type ppstream
type ppconsumer = { consumer  : string -> unit,
                    linewidth : int,
                    flush     : unit -> unit }

datatype break_style =
    CONSISTENT
  | INCONSISTENT

type ppstream_interface =
     { add_stringsz : (string * int) -> unit,
       add_break : int * int -> unit,
       begin_block : break_style -> int -> unit,
       clear_ppstream : unit -> unit,
       end_block : unit -> unit,
       flush : unit -> unit,
       linewidth : int}

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
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


   Example 1: A simple prettyprinter for Booleans:

       load "PP";
       fun ppbool pps d =
           let open PP
           in
               begin_block pps INCONSISTENT 6;
               add_string pps (if d then "right" else "wrong");
               end_block pps
           end;

   Now one may define a ppstream to print to, and exercise it:

       val ppstrm = PP.mk_ppstream {consumer  =
                                    fn s => TextIO.output(TextIO.stdOut, s),
                                    linewidth = 72,
                                    flush     =
                                     fn () => TextIO.flushOut TextIO.stdOut};

       fun ppb b = (ppbool ppstrm b; PP.flush_ppstream ppstrm);

       - ppb false;
       wrong> val it = () : unit

   The prettyprinter may also be installed in the toplevel system;
   then it will be used to print all expressions of type bool
   subsequently computed:

       - installPP ppbool;
       > val it = () : unit
       - 1=0;
       > val it = wrong : bool
       - 1=1;
       > val it = right : bool

   See library Meta for a description of installPP.


   Example 2: Prettyprinting simple expressions (examples/pretty/ppexpr.sml):

       datatype expr =
           Cst of int
         | Neg of expr
         | Plus of expr * expr

       fun ppexpr pps e0 =
           let open PP
               fun ppe (Cst i)        = add_string pps (Int.toString i)
                 | ppe (Neg e)        = (add_string pps "~"; ppe e)
                 | ppe (Plus(e1, e2)) = (begin_block pps CONSISTENT 0;
                                         add_string pps "(";
                                         ppe e1;
                                         add_string pps " + ";
                                         add_break pps (0, 1);
                                         ppe e2;
                                         add_string pps ")";
                                         end_block pps)
           in
               begin_block pps INCONSISTENT 0;
               ppe e0;
               end_block pps
           end

       val _ = installPP ppexpr;

       (* Some example values: *)

       val e1 = Cst 1;
       val e2 = Cst 2;
       val e3 = Plus(e1, Neg e2);
       val e4 = Plus(Neg e3, e3);
       val e5 = Plus(Neg e4, e4);
       val e6 = Plus(e5, e5);
       val e7 = Plus(e6, e6);
       val e8 =
           Plus(e3, Plus(e3, Plus(e3, Plus(e3, Plus(e3, Plus(e3, e7))))));
*)

end;
