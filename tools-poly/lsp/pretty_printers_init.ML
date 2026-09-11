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
end;
