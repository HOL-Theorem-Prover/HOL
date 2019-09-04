signature DFA_Codegen =
sig

 type dfa =
   {name       : string,
    src_regexp : string,
    finals     : bool list,
    table      : int list list}

 val Ada  : dfa -> TextIO.outstream -> unit
 val C    : dfa -> TextIO.outstream -> unit
 val SML  : dfa -> TextIO.outstream -> unit
 val Java : dfa -> TextIO.outstream -> unit

end
