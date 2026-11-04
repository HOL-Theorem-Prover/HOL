signature statementDossierLib =
sig

type name = {Thy : string, Name : string}

(* title, preamble: the heading and the opening text of the document.
   theorems: the stored theorems to describe, in this order.
   expand_theories: theories whose constants are expanded, that is, have
     their definitions shown and their own constants followed; normally
     the consumer's theories (see script_theories).
   expand_consts: single constants from other theories to expand too.
     The constants their definitions mention are expanded only if they
     are themselves in an expanded theory or listed here.
   stop_theories, stop_consts: never expanded, even if listed above.
   equation_lemmas: stored theorems to show beside the definition of a
     constant, in addition to automatically discovered equation lemmas.
   source_dirs: (label, directory) pairs to look for theory scripts in,
     to find the line of each theorem; the label prefixes the path shown.
   outputs: the files to write, each with its format.
   snippets: optionally (input, output) files for pages that link into
     the HTML dossier: text read from the input is printed by HOL with
     the dossier's highlighting and links (see README.md).
   assumptions: optionally a theorem and a markdown file explaining each
     of its hypotheses (see README.md); the dossier shows each
     hypothesis, its definition and its explanation after the theorem.
   supporting: stored theorems shown after the theorems, stated but not
     expanded. *)
datatype output_format = Markdown | Html

type config = {
  title : string,
  preamble : string,
  theorems : name list,
  expand_theories : string list,
  expand_consts : name list,
  stop_theories : string list,
  stop_consts : name list,
  equation_lemmas : (name * name list) list,
  source_dirs : (string * string) list,
  outputs : (output_format * string) list,
  snippets : (string * string) option,
  assumptions : {theorem : name, prose : string} option,
  supporting : name list
}


(* List theories whose scripts occur below these source directories. *)
val script_theories : string list -> string list

(* Write stored statements and their definition closure to the outputs.
   Raises Fail on invalid configuration or assumption prose. *)
val run : config -> unit

(* Original stored statements selected for the theorem and definition sections.
   Definition sections identify their constant and retain whole sequents. *)
val statement_sections : config ->
  (string * (name * Thm.thm) list) list

(* Additional prose belongs in About, away from the opening explanation.
   Omitted types are not described or linked; their uses remain in formulas.
   Reader view hides traversal metadata, raw duplicate statements and pinning
   formulas, and displays definitions as implicitly quantified clauses.
   Pinning names are still validated. Theory sources link boundary constants
   to caller-supplied source URLs. About prose is Markdown. *)
type presentation = {about : string, omit_types : name list,
                     reader_view : bool,
                     theory_sources : (string * string) list}
val run_with_presentation : presentation -> config -> unit

end
