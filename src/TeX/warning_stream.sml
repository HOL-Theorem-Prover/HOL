val () = Feedback.WARNING_outstream :=
           (fn s => (TextIO.output(TextIO.stdErr, s);
                     TextIO.flushOut TextIO.stdErr))
