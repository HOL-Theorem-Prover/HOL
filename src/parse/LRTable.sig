(* LRTable: signature for an LR Table.

   The list of actions and gotos passed to mkLrTable must be ordered by state
   number. The values for state 0 are the first in the list, the values for
    state 1 are next, etc.
*)

signature LRTable =
    sig
        datatype ('a,'b) pairlist = EMPTY | PAIR of 'a * 'b * ('a,'b) pairlist
	datatype state = STATE of int
	datatype term = T of int
	datatype nonterm = NT of int
	datatype action = SHIFT of state
			| REDUCE of int
			| ACCEPT
			| ERROR
	type table
	
	val numStates : table -> int
	val numRules : table -> int
	val describeActions : table -> state ->
				(term,action) pairlist * action
	val describeGoto : table -> state -> (nonterm,state) pairlist
	val action : table -> state * term -> action
	val goto : table -> state * nonterm -> state
	val initialState : table -> state
	exception Goto of state * nonterm

	val mkLrTable : {actions : ((term,action) pairlist * action) array,
			 gotos : (nonterm,state) pairlist array,
			 numStates : int, numRules : int,
			 initialState : state} -> table
    end
