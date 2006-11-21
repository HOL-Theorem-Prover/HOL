signature TREE = 
sig 
  type size

datatype stm = SEQ of stm * stm
             | LABEL of Temp.label
             | JUMP of Temp.label
             | CJUMP of exp * Temp.label
	     | MOVE of exp * exp
             | EXP of exp

     and exp = BINOP of binop * exp * exp
	     | RELOP of relop * exp * exp
             | MEM of exp
             | TEMP of Temp.temp
             | ESEQ of stm * exp
             | NAME of Temp.label
             | NCONST of Arbint.int
	     | WCONST of Arbint.int
	     | CALL of exp * exp
	     | PAIR of exp * exp

      and binop = PLUS | MINUS | MUL | DIV 
                | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR | ROR

      and relop = EQ | NE | LT | GT | LE | GE | CC | LS | HI | CS

      val pair2list : exp -> exp list	
 (*
  val notRel : relop -> relop
  val commute: relop -> relop
 *)

end

structure Tree : TREE = 
struct
  type size = int

datatype stm = SEQ of stm * stm
             | LABEL of Temp.label
             | JUMP of Temp.label
             | CJUMP of exp * Temp.label
	     | MOVE of exp * exp
             | EXP of exp

     and exp = BINOP of binop * exp * exp
	     | RELOP of relop * exp * exp
             | MEM of exp
             | TEMP of Temp.temp
             | ESEQ of stm * exp
             | NAME of Temp.label
             | NCONST of Arbint.int
	     | WCONST of Arbint.int
	     | CALL of exp * exp
	     | PAIR of exp * exp

      and binop = PLUS | MINUS | MUL | DIV 
                | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR | ROR

      and relop = EQ | NE | LT | GT | LE | GE 
	        | CC | LS | HI | CS

  fun pair2list (PAIR(v1, v2)) =
        (pair2list v1) @ (pair2list v2)
   |  pair2list v = [v]

end
