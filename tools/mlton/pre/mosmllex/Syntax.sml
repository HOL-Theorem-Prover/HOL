(* The shallow abstract syntax *)

structure Syntax =
struct

datatype location = Location of string

datatype regular_expression
  = Epsilon
  | Characters  of char list
  | Sequence    of regular_expression * regular_expression
  | Alternative of regular_expression * regular_expression
  | Repetition  of regular_expression
  | Name        of string

type rules = (string * (regular_expression * location) list) list

(* return type of Grammar.lexer_definition *)
datatype lexer_definition
  = Lexdef of
     {header: location,  (* header declarations, typically opens *)
      footer: location,  (* footer declarations *)
      lexarg: location,  (* argument to "makeLex" function *)
      lets: (string * regular_expression) list,
      rules: rules}

(* Representation of automata *)

datatype automata
  = Perform of int
  | Shift of automata_trans * automata_move Array.array
and automata_trans
  = No_remember
  | Remember of int
and automata_move
  = Backtrack
  | Goto of int

end (* structure Syntax *)
