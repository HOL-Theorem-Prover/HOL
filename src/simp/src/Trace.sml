structure Trace :> Trace =
struct
open Feedback boolSyntax Rsyntax Abbrev;

val print_term = Lib.say o Parse.term_to_string
val print_thm = Parse.print_thm
val concl = Thm.concl
val say = Lib.say

   (* ---------------------------------------------------------------------
    * Tracing utilities
    * ---------------------------------------------------------------------*)

    datatype action =
             LZ_TEXT of unit -> string
           | TEXT of string
           | REDUCE of (string * Term.term)
           | REWRITING of (Term.term * Thm.thm)
           | SIDECOND_ATTEMPT of Term.term
           | SIDECOND_SOLVED of Thm.thm
           | SIDECOND_NOT_SOLVED of Term.term
           | OPENING of (Term.term * Thm.thm)
           | PRODUCE of (Term.term * string * Thm.thm)
           | IGNORE of (string * Thm.thm)
           | MORE_CONTEXT of Thm.thm;

   val trace_hook : ((int * action) -> unit) ref = ref (fn (n,s) => ());
   fun trace x = (!trace_hook) x

val trace_level = ref 0;
val _ = Feedback.register_trace("simplifier", trace_level, 7);

fun tty_trace (LZ_TEXT fs) = (say "  "; say (fs ()); say "\n")
  | tty_trace (TEXT s) = (say "  "; say s; say "\n")
  | tty_trace (REDUCE (s,tm)) = (say "  "; say s; say " "; print_term tm; say "\n")
  | tty_trace (REWRITING (tm,thm)) =
    (say "  rewriting "; print_term tm; say " with "; print_thm thm; say "\n")
  | tty_trace (SIDECOND_ATTEMPT tm) =
    (say "  trying to solve: "; print_term tm; say "\n")
  | tty_trace (SIDECOND_SOLVED thm) =
    (say "  solved! "; print_thm thm; say "\n")
  | tty_trace (SIDECOND_NOT_SOLVED tm) =
    (say "  couldn't solve: "; print_term tm; say "\n")
  | tty_trace (OPENING (tm,thm)) =
    (say "  "; print_term tm; say " matches congruence rule "; print_thm thm; say "\n")
  | tty_trace (PRODUCE (tm,s,thm)) =
    (say "  "; print_term tm; say " via "; say s; say " simplifies to: ";
     print_term (rhs (concl thm)) handle HOL_ERR _ => print_thm thm; say "\n")
  | tty_trace (IGNORE (s,thm)) =
    (say "  Ignoring "; say s; say " rewrite\n     "; print_thm thm; say "\n")
  | tty_trace (MORE_CONTEXT thm) =
    (say "  more context: "; print_thm thm; say "\n");

val _ = trace_hook :=
        (fn (n,a) => if (n <= !trace_level) then
                       (say "[";
                        say ((Arbnum.toString o #usec o Portable.dest_time)
                             (#usr (Timer.checkCPUTimer Globals.hol_clock)));
                        say "]: ";
                        tty_trace a)
                     else ())

end (* struct *)
