(* Poly/ML pretty printers for HOL's abstract types, installed into the
   LSP session.

   `tools-poly/prelude.ML' installs these for the REPL, but the LSP
   branch of `hol.ML' does not load the prelude: the prelude `open's
   HolKernel, Parse and boolLib, and what is open at the top level is
   what the user's file compiles against, so the LSP session
   deliberately opens nothing.  A pretty printer is not a name, though,
   so the printers can be had without that cost.

   What this buys hover: with no printer installed,
   `PolyML.NameSpace.Values.print' renders a value of type `thm' as
   `?', which is why the hover handler special-cased theorems by
   looking their *names* up in DB.  With the printer installed the
   theorem prints from the value itself, which also covers a `[local]'
   theorem -- never in DB -- and a value that merely contains theorems
   (`thm list', `term * thm', a record of them).  Name lookup can do
   none of that.

   `HOLPP.pretty' is `PolyML.pretty' under Poly/ML (see
   `src/portableML/poly/PrettyImpl.sml'), so a printer hands back a
   tree whose breaks are still abstract and the caller lays it out at
   whatever width it likes.  That is what lets a hover render at the
   client's box width rather than at a width compiled in here.

   `HOLmessage.message' is here for a second reason.  `exnMessage'
   renders an exception's argument with Poly/ML's generic printer, and
   a `HOL_ERR' carries its text in that field, so with no printer the
   whole message a HOL error was raised with reads back as
   `HOL_ERROR {message = ?, origins = ...}'.  The registration used to
   sit in `src/prekernel/HOLmessage.sml', where it was saved with the
   heap and so reached every session; it had to move out because
   `PolyML.addPrettyPrinter' does not exist under Moscow ML, and the
   two preludes it moved to are exactly what an LSP session does not
   load.

   Each printer forces `PPBackEnd.raw_terminal' for the duration.  The
   LSP session's backend is a colour one -- the goals pane wants ANSI
   escapes -- and those escapes would be garbage in the markdown of a
   hover.  Unicode is unaffected: the raw backend still emits the
   turnstile and the quantifiers. *)

local
  (* As in prelude.ML: a Poly/ML pretty printer ignores the depth and
     the argument-printer, since HOL's own printers take neither. *)
  fun pp2polypp (ppfn: 'b -> HOLPP.pretty) =
      fn _ => fn _ => fn e: 'b => ppfn e
  fun raw ppfn x =
      Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal) ppfn x
in
val () = PolyML.addPrettyPrinter (pp2polypp (raw Hol_pp.pp_thm));
val () = PolyML.addPrettyPrinter
           (pp2polypp (raw (Parse.term_pp_with_delimiters Hol_pp.pp_term)));
val () = PolyML.addPrettyPrinter
           (pp2polypp (raw (Parse.type_pp_with_delimiters Hol_pp.pp_type)));
val () = PolyML.addPrettyPrinter (pp2polypp (raw HOLmessage.toPretty));
end;
