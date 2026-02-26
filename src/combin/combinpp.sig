signature combinpp =
sig

val upd_processor : term_grammar.absyn_postprocessor
val upd_printer : term_grammar.userprinter

val new_form :
    { left : string, right : string,
      upd_term_name : Term.term * string,
      lookup_term_name : (Term.term * string) option } ->
    unit

val remove_paren_syntax : string -> unit

val enable_dictsyntax : unit -> unit
  (* only needs calling once *)
end

(*

Written out in s-expression pseudo syntax (and abbreviating the names
above in what I hope is the obvious way, the processor expects to
consume

  (toplevel f (consupd (leftarrow k1 d1)
                       (consupd (leftarrow k2 d2) .. idupd)))

and produce

  (constname k1 d1 (constname k2 d2 ... f))

The toplevel-consupd-idupd stuff can be generated with a suffix listform.

The arrows can be a standard infix.

It is then also up to the client to overload constname to the desired
semantics.

*)
