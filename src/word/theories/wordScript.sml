(* ===================================================================== *)
(* FILE		: mk_word.ml						 *)
(* DESCRIPTION   : Create the theory word as the descendent theory of	 *)
(*   	    	  all the word_xxx theories.				 *)
(* WRITES FILE   : word.th  	    					 *)
(*									 *)
(* AUTHOR	: (c) Wai Wong						 *)
(* DATE		: 24 September 1992					 *)
(* TRANSLATOR: Paul Curzon  3 June 1993, September 1994			 *)
(* ===================================================================== *)

val _ = Parse.new_theory"word";

local open bword_arithTheory bword_bitopTheory in end;

val _ = Parse.export_theory();
