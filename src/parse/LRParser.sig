(* LRParser: signature for a polymorphic LR parser *)

signature LRParser =
sig
  exception ParseError

  val parse 
    : {table : LRTable.table,
       lexer : ('b,'c) Token.token Stream.stream,
       arg: 'arg,
       saction : int * 'c * (LRTable.state * ('b*'c*'c)) list * 'arg 
                 -> LRTable.nonterm * ('b * 'c * 'c) 
                    * ((LRTable.state * ('b * 'c * 'c)) list),
       void : 'b,
       ec : { is_keyword : LRTable.term -> bool,
              noShift : LRTable.term -> bool,
              preferred_change : (LRTable.term list * LRTable.term list) list,
              errtermvalue : LRTable.term -> 'b,
              showTerminal : LRTable.term -> string,
              terms: LRTable.term list,
              error : string * 'c * 'c -> unit },
       lookahead : int  (* max amount of lookahead used in error correction *)
      } 
       -> 'b * ('b,'c) Token.token Stream.stream
end
