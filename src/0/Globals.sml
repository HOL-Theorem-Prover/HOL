(* ===================================================================== *)
(* FILE          : Globals.sml                                           *)
(* DESCRIPTION   : Contains global flags for hol98.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(*               : July 17, 1998                                         *)
(*                                                                       *)
(* ===================================================================== *)


structure Globals :> Globals =
struct

open Portable;

(*---------------------------------------------------------------------------*
 * Installation-specific information.                                        *
 *---------------------------------------------------------------------------*)

val HOLDIR = "/local/scratch/kxs/working";


(*---------------------------------------------------------------------------*
 * Version information                                                       *
 *---------------------------------------------------------------------------*)

val release = "Taupo";
val version = 0;

(*-------------------------------------------------------------------------*
 * Bogus hack for defining strings                                         *
 *-------------------------------------------------------------------------*)

local val defined = ref false
in
fun strings_defined() = !defined
fun assert_strings_defined() = defined := true
end;

(*---------------------------------------------------------------------------*
 * Controlling the display of exceptions                                     *
 *---------------------------------------------------------------------------*)

val print_exceptions = ref true;

(*---------------------------------------------------------------------------*
 * For showing assumptions in theorems                                       *
 *---------------------------------------------------------------------------*)

val show_assums = ref false

(*---------------------------------------------------------------------------*
 * For showing oracles used to prove theorems.                               *
 *---------------------------------------------------------------------------*)
val show_tags = ref false

(*---------------------------------------------------------------------------*
 * For showing the axioms used in the proof of a theorem.                    *
 *---------------------------------------------------------------------------*)
val show_axioms = ref true

(*---------------------------------------------------------------------------*
 * For showing the time taken to "scrub" the current theory of out-of-date   *
 * items. For developers.                                                    *
 *---------------------------------------------------------------------------*)
val show_scrub = ref true


(*---------------------------------------------------------------------------*
 * Assignable function for printing errors.                                  *
 *---------------------------------------------------------------------------*)

val output_HOL_ERR =
   ref (fn {message,origin_function,origin_structure} =>
         ( output(std_out, ("\nException raised at "^origin_structure^"."^
			    origin_function^":\n"^message^"\n"));
	  Portable.flush_out std_out));

(*---------------------------------------------------------------------------*
 * Gives some ability to tweak the lexis. It is initially being used         *
 * to make "~" more widely accessible in symbolic identifiers.               *
 *---------------------------------------------------------------------------*)

(* val tilde_symbols = ref []:string list ref; *)

(*---------------------------------------------------------------------------*
 * Prettyprinting flags                                                      *
 *---------------------------------------------------------------------------*)

val type_pp_prefix = ref ""  and type_pp_suffix = ref ""
val term_pp_prefix = ref ""  and term_pp_suffix = ref ""


(*---------------------------------------------------------------------------*
 * Tells the prettyprinters how wide the page is.                            *
 *---------------------------------------------------------------------------*)
val linewidth = Portable.linewidth;

(*---------------------------------------------------------------------------*
 * Controls depth of printing for terms. Since the pp recursively decrements *
 * this value when traversing a term, and since printing stops when the      *
 * value is 0, the negative value means "print everything". Warning:         *
 * this will work to negmaxint, but no guarantees after that.                *
 *---------------------------------------------------------------------------*)

val max_print_depth = ref ~1;

val pp_flags = {(*show_dB        = ref false,*)
                show_restrict  = ref true,
                show_types     = ref false,
                infix_at_front = ref false,
                stack_infixes  = ref true,
                in_at_end      = ref false};

(*---------------------------------------------------------------------------*
 * For showing the deBruijn structure of a term                              *
 *---------------------------------------------------------------------------*)

(* val show_dB = #show_dB pp_flags; *)

(*---------------------------------------------------------------------------*
 * For showing the representation of a term having restricted quantifiers    *
 *---------------------------------------------------------------------------*)

val show_restrict = #show_restrict pp_flags;

(*---------------------------------------------------------------------------*
 * For prettyprinting type information in a term.                            *
 *---------------------------------------------------------------------------*)

val show_types = #show_types pp_flags;

(*---------------------------------------------------------------------------*
 * For printing HOL infixes at beginning or end of lines.                    *
 *---------------------------------------------------------------------------*)

val infix_at_front = #infix_at_front pp_flags;

(*---------------------------------------------------------------------------*
 * Controls whether each argument of an infix goes on a new line.            *
 *---------------------------------------------------------------------------*)

val stack_infixes = #stack_infixes pp_flags;

(*---------------------------------------------------------------------------*
 * Controls whether the "in" of a let expression is printed at the           *
 * end of the line.                                                          *
 *---------------------------------------------------------------------------*)

val in_at_end = #in_at_end pp_flags;

(*---------------------------------------------------------------------------*
 * This is mainly for documentation purposes.                                *
 *---------------------------------------------------------------------------*)

(* val reserved_identifiers = {symbolic = ["\\", ";", "=>", "|", ":" ],
                            alphanumeric = ["let", "in", "and", "of"]}
*)


val goal_line = ref "------------------------------------";


(*---------------------------------------------------------------------------*
 * At the end of type inference, HOL now guesses names for unconstrained     *
 * type variables, if this flag is set.                                      *
 *---------------------------------------------------------------------------*)
val guessing_tyvars = ref true;

(*---------------------------------------------------------------------------*
 * If this flag is set, then the system will print a message when such       *
 * guesses are made.                                                         *
 *---------------------------------------------------------------------------*)

val notify_on_tyvar_guess = ref true;

(*---------------------------------------------------------------------------*
 * The syntax used to highlight out-of-date constants in the prettyprinters  *
 * for types and terms.                                                      *
 *---------------------------------------------------------------------------*)

val old = ref (fn s => String.concat["old->",s,"<-old"]);

(*---------------------------------------------------------------------------*
 * Flag used to tell how to do renaming: if it's NONE, do priming; if it's   *
 * SOME s, increment a numerical suffix and append it to s.                  *
 *---------------------------------------------------------------------------*)

val priming = ref (NONE:string option);

end; (* Globals *)
