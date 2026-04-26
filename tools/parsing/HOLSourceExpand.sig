signature HOLSourceExpand = sig

val mkSemi: HOLSourceAST.dec list -> HOLSourceAST.dec list

val expandDec:
  { fileline: int -> HOLSourceAST.fileline,
    parseError: int * int -> string -> unit,
    quietOpen: bool } ->
  HOLSourceAST.dec -> HOLSourceAST.dec

(* Holmake tactic text storage: set source text accessor before parsing,
   read tactic text after expansion. Used by fragment-stepped prover.
   Each entry is (thm_name, source_text, has_proof_attrs).
   source_text: raw tactic text from source (for fragment stepping).
   has_proof_attrs: true when Proof[exclude_simps ...] etc. are present. *)
val holmake_source_text_fn : (int * int -> string) option ref
val holmake_tactic_text : (string * string * bool) list ref
val holmake_active : bool ref  (* true when -g or --dumpheap is active *)

end
