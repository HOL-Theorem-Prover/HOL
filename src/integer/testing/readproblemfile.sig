signature readproblemfile = sig

  val readterm : TextIO.instream -> Term.term option option
  val foldl : (Term.term option * 'a -> 'a) -> 'a -> TextIO.instream -> 'a
  val app  : (Term.term option -> 'a) -> TextIO.instream -> unit
end

(*
   [readterm is] attempts to read a term from the stream is.  If the stream
   is at EOF, then the value returned is NONE.  Otherwise, it is
   SOME (SOME t) if there is a term there to be read, or SOME NONE if
   something was read, but if failed to parse as a term.  The stream must
   delimit its terms with blank lines.

   [foldl f v0 is] reads terms from stream is (using readterm above),
   and applies the function f to each term and the value of the "previous"
   v.  The very first term read is combined with the initial value v0.
   Thus, if there are three terms in the stream, the value
       f (t3, f (t2, f(t1, v0)))
   will be computed.  In fact, f is given a term option to allow for the
   fact that readterm may fail to successfully parse a term.

   [app f is] applies function f to the terms in stream is and ignores the
   results.
*)
