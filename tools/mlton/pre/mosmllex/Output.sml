(* Generating a DFA as a set of mutually recursive functions *)

signature OUTPUT =
sig
  val output_lexdef
      : TextIO.outstream *  (* output destination *)
        Syntax.location *   (* header *)
        Syntax.location *   (* footer *)
        Syntax.location *   (* lexarg *)
        ((string * int) list *                (* initial_st *)
         Syntax.automata Array.array *        (* states *)
	 (int * Syntax.location) list list)   (* actions *)
        -> unit
end

structure Output : OUTPUT =
struct

local open Syntax Fnlib
in

val output = TextIO.output

fun output_char_const os (i : int) =
    if i <= 127 then
      (output(os, "#\"");
       output(os,Char.toString(Char.chr i));
       output(os,"\""))
    else
      (output(os, "#\"\\");
       output(os, Int.toString i);
       output(os, "\""))

(* 2- Generating the states *)

fun enumerate_vect v =
    let fun enum(env,pos) =
	    if pos >= Array.length v then env
	    else let val pl = lookup (Array.sub(v,pos)) env
	          in pl := pos :: !pl; enum(env,pos+1)
		 end
	         handle Subscript =>
	           enum (((Array.sub(v,pos), ref [pos]) :: env), pos+1)
     in Sort.sort
	  ((fn ((e1, ref pl1),(e2, ref pl2)) => 
	      List.length pl1 >= List.length pl2),
	   (enum([],0)))
    end

fun addToInterv(c,acc) =
    case acc
      of nil => [(c, c)]
       | (c1, c2) :: rest =>
	   if c+1 = c1 then
	     (c, c2) :: rest
	   else
	     (c, c) :: acc

fun mkIntervals cs =
    foldl addToInterv [] cs

fun addInterv dest ((c1, c2),(intervs, singls)) =
    if c1 > c2 then (intervs, singls)
    else if c2 - c1 >= 5 then ((dest, (c1, c2)) :: intervs, singls)
    else addInterv dest ((c1+1, c2),(intervs, (dest, c1) :: singls))

fun unzipInterv trans =
    foldr
      (fn ((dest, chars), acc) =>
	 foldr (addInterv dest) acc (mkIntervals (!chars)))
      ([], [])
      trans


(* main output function *)
fun output_lexdef (os,header,footer,lexarg,(initial_st, states, actions)) =
let

fun outputStdFuns () = (
     output(os,"fun setLastAction f = LexBuffer.setLastAction lexbuf f\n");
     output(os,"fun resetLastPos () = LexBuffer.resetLastPos lexbuf\n");
     output(os,"fun resetStartPos () = LexBuffer.resetStartPos lexbuf\n");
     output(os,"fun getLexeme () = LexBuffer.getLexeme lexbuf\n");
     output(os,"fun getLexemeChar n = LexBuffer.getLexemeChar lexbuf n\n");
     output(os,"fun getLexemeStart () = LexBuffer.getLexemeStart lexbuf\n");
     output(os,"fun getLexemeEnd () = LexBuffer.getLexemeEnd lexbuf\n");
     output(os,"fun getNextChar () = LexBuffer.getNextChar lexbuf\n");
     output(os,"fun backtrack () = LexBuffer.backtrack lexbuf\n")
    )

(* 1- Generating the actions *)

fun copy_chunk (Location s) =
    output(os,s)

fun output_actname (i : int) =
    output(os, "action_" ^ Int.toString i)

fun output_action (i : int, act) =
    (output_actname i; 
     output(os, " () = (\n");
     copy_chunk act;
     output(os, ")\nand "))

fun output_actcheck []  = ()
  | output_actcheck [_] = ()
  | output_actcheck ((a1, _) :: ar) =
    (output(os, "val _ = fn _ => [");
     output_actname a1;
     app (fn (a, _) => (output(os, ", "); output_actname a)) ar;
     output(os, "];\n"))

fun output_move Backtrack =
      output(os, "backtrack ()")
  | output_move (Goto dest) =
     (case Array.sub(states, dest)
        of Perform act_num =>
             output(os, "action_" ^ Int.toString act_num ^ " ()")
	 | _ =>
             output(os, "state_" ^ Int.toString dest ^ " ()"))

fun output_one_trans_i (dest, (c1, c2)) =
(
  output(os, " if currChar >= ");
  output_char_const (os) c1;
  output(os, " andalso currChar <= ");
  output_char_const (os) c2;
  output(os, " then  ");
  output_move dest;
  output(os, "\n else")
)

fun output_one_trans_s (dest, c) =
(
  output_char_const (os) c;
  output(os, " => ");
  output_move dest;
  output(os, "\n |  ")
)

fun output_all_trans_i trans =
  app output_one_trans_i trans

fun output_all_trans_s trans =
(
  output(os, " case currChar of\n    ");
  app output_one_trans_s trans;
  output(os, "_ => ")
)

fun output_all_trans trans =
(
  case enumerate_vect trans
    of [] =>
        raise Fail "output_all_trans"
     | (default, _) :: rest =>
        (output(os, " let val currChar = getNextChar () in\n");
         case unzipInterv rest of
             ([], trans_s) =>
               (output_all_trans_s trans_s;
                output_move default)
           | (trans_i, []) =>
               (output_all_trans_i trans_i;
                output(os, " ");
                output_move default)
           | (trans_i, trans_s) =>
               (output_all_trans_i trans_i;
                output_all_trans_s trans_s;
                output_move default));
  output(os, "\n end)\nand ")
)

fun output_state (state_num : int) =
    fn Perform i =>
        ()
     | Shift(what_to_do, moves) =>
	(output(os,
	   "state_"  ^ Int.toString state_num ^ " () = (\n");
	 (case what_to_do
	    of No_remember => ()
	     | Remember i =>
		(output(os,
		   " resetLastPos ();\n");
		 output(os,
		   (" setLastAction action_" ^
				    Int.toString i ^ ";\n"))));
	 output_all_trans moves)


(* 3- Generating the entry points *)

fun output_entries [] = 
      raise Fail "output_entries"
  | output_entries ((name, state_num : int) :: rest) =
      (output(os, name ^ " () =\n");
       output(os,
         "  (resetStartPos ();\n");
       output(os,
         "   state_" ^ Int.toString state_num ^ " ())\n");
       case rest
         of [] => output(os, "\n")
          | _  => (output(os, "\nand "); output_entries rest))

in (* All together *)

  output(TextIO.stdOut, Int.toString (Array.length states)); 
  output(TextIO.stdOut, " states, ");
  output(TextIO.stdOut, Int.toString
	 (List.foldl (op+) 0 (List.map List.length actions)));
  output(TextIO.stdOut, " actions.\n"); TextIO.flushOut TextIO.stdOut;  
  copy_chunk header;				(* structure heading *)
  output(os,"fun makeLex ");
  copy_chunk lexarg;
  output(os," lexbuf = \n let\n");
  outputStdFuns ();
  output(os,"fun ");
  app (app output_action) actions;
  for (fn i => output_state i (Array.sub(states, i)))
      0 (Array.length states - 1);
  output_entries initial_st;
  output(os, "(* The following checks type consistency of actions *)\n");
  app output_actcheck actions;
  output(os,"in main\n end\n");
  copy_chunk footer				(* end of the file *)

end (* output_lexdef *)

end (* local *)
end (* structure Output *)
