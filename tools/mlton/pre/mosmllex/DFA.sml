(* DFA.sml *)
(* Compiling a lexer definition to a DFA *)

structure DFA : DFA =
struct

local
  open Fnlib Syntax
in

(* Deep abstract syntax for regular expressions *)

datatype regexp
  = Empty
  | Chars of int
  | Action of int
  | Seq of regexp * regexp
  | Alt of regexp * regexp
  | Star of regexp


(* From shallow to deep syntax *)

val chars = ref ([] : char list list)
val chars_count = ref 0
val actions_count = ref 0

fun encode_regexp Epsilon = Empty
  | encode_regexp (Characters cl) =
      let val n = !chars_count
       in chars := cl :: !chars;
          incr chars_count;
          Chars(n)
      end
  | encode_regexp (Sequence(r1,r2)) =
      Seq(encode_regexp r1, encode_regexp r2)
  | encode_regexp (Alternative(r1,r2)) =
      Alt(encode_regexp r1, encode_regexp r2)
  | encode_regexp (Repetition r) =
      Star (encode_regexp r)
  | encode_regexp (Name _) = raise Fail "Lexgen.encode_regexp"


fun encode_casedef casedef =
    let val actions = ref ([] : (int * location) list)
	fun addact ((expr, act),reg) =
	    let val act_num = !actions_count
	     in	incr actions_count;
		actions := (act_num, act) :: !actions;
		Alt(reg, Seq(encode_regexp expr, Action act_num))
	    end
	val regexp = foldl addact Empty casedef
    in (regexp, !actions)
    end

(*
  This function simulates map as defined in Caml Light,
  to ensure the evaluation order from right to left!
  This is essential, if f may produce side-effects.

  The goal is to get mosmllex to produce exactly the same
  result, as its version written in Caml Light.
*)

fun caml_map f [] = []
  | caml_map f (x::xs) =
      let val ys = caml_map f xs
          val y  = f x
       in y :: ys
      end

fun encode_lexdef ld =
    (chars := [];
     chars_count := 0;
     actions_count := 0;
     let val name_regexp_actdef_list =
	     caml_map (fn (name, casedef) => (name, encode_casedef casedef)) ld
	 val chr = Array.fromList (rev (!chars))
	 val name_regexp_list = 
	     map (fn (n, (r, _)) => (n, r)) name_regexp_actdef_list
	 val act = 
	     map (fn (_, (_, a)) => a) name_regexp_actdef_list
     in
         chars := [];
         (chr, name_regexp_list, act)
     end)

(* To generate a NFA directly from a regular expression.
   Refer to Aho-Sethi-Ullman, dragon book, chap. 3 *)

datatype transition
  = OnChars of int
  | ToAction of int


fun merge_trans [] s2 = s2
  | merge_trans s1 [] = s1
  | merge_trans (s1 as (t1 as OnChars n1) :: r1)
                (s2 as (t2 as OnChars n2) :: r2) =
      if n1 = n2 then t1 :: merge_trans r1 r2 else
      if n1 < n2 then t1 :: merge_trans r1 s2 else
                      t2 :: merge_trans s1 r2
  | merge_trans (s1 as (t1 as ToAction n1) :: r1)
                (s2 as (t2 as ToAction n2) :: r2) =
      if n1 = n2 then t1 :: merge_trans r1 r2 else
      if n1 < n2 then t1 :: merge_trans r1 s2 else
                      t2 :: merge_trans s1 r2
  | merge_trans (s1 as (t1 as OnChars n1) :: r1)
                (s2 as (t2 as ToAction n2) :: r2) =
      t1 :: merge_trans r1 s2
  | merge_trans (s1 as (t1 as ToAction n1) :: r1)
                (s2 as (t2 as OnChars n2) :: r2) =
      t2 :: merge_trans s1 r2


fun nullable Empty        = true
  | nullable (Chars _)    = false
  | nullable (Action _)   = false
  | nullable (Seq(r1,r2)) = nullable r1 andalso nullable r2
  | nullable (Alt(r1,r2)) = nullable r1 orelse nullable r2
  | nullable (Star r)     = true


fun firstpos Empty        = []
  | firstpos (Chars pos)  = [OnChars pos]
  | firstpos (Action act) = [ToAction act]
  | firstpos (Seq(r1,r2)) =
                  if nullable r1
                  then merge_trans (firstpos r1) (firstpos r2)
                  else firstpos r1
  | firstpos (Alt(r1,r2)) = merge_trans (firstpos r1) (firstpos r2)
  | firstpos (Star r)     = firstpos r


fun lastpos Empty        = []
  | lastpos (Chars pos)  = [OnChars pos]
  | lastpos (Action act) = [ToAction act]
  | lastpos (Seq(r1,r2)) =
      if nullable r2
      then merge_trans (lastpos r1) (lastpos r2)
      else lastpos r2
  | lastpos (Alt(r1,r2)) = merge_trans (lastpos r1) (lastpos r2)
  | lastpos (Star r)     = lastpos r


fun followpos size name_regexp_list =
    let open Array infix 9 sub
	val v = array(size, [])
	fun fill_pos first = fn
		OnChars pos => update(v, pos, merge_trans first (v sub pos))
	      | ToAction _  => ()
	fun fill (Seq(r1,r2)) =
	      (fill r1; fill r2;
	       List.app (fill_pos (firstpos r2)) (lastpos r1))
	  | fill (Alt(r1,r2)) =
	      (fill r1; fill r2)
	  | fill (Star r) =
	      (fill r;
	       List.app (fill_pos (firstpos r)) (lastpos r))
	  | fill _ = ()
    in  List.app (fn (name, regexp) => fill regexp) name_regexp_list;
	v
    end


val no_action = 32767

val split_trans_set =
    foldl
      (fn (trans, (act_pos_set as (act, pos_set))) =>
	 case trans
	   of OnChars pos   => (act, pos :: pos_set)
	    | ToAction act1 => if act1 < act then (act1, pos_set)
					     else act_pos_set)
      (no_action, [])

(*******************************Begin JGR changes*******************************)
(* using smlnj-lib Hashtable *)

fun hashTransition (OnChars n) = n*2
  | hashTransition (ToAction n) = n*2 + 1

fun eqTransition(OnChars n1, OnChars n2) = n1 = n2
  | eqTransition(ToAction n1, ToAction n2) = n1 = n2
  | eqTransition _ = false

fun eqTransitionLst (nil,nil) = true
  | eqTransitionLst (x::xs,y::ys) =
      eqTransition(x,y) andalso eqTransitionLst(xs,ys)
  | eqTransitionLst _ = false

fun hashTransitionLst l = 
    Word.fromInt (List.foldl (fn (x,y) => (hashTransition x) + y) 0 l)

fun clearTable tbl = HashTable.filteri (fn p => false) tbl

exception FindErr

val memory  = (HashTable.mkTable (hashTransitionLst, fn (x,y) => x=y) 
                                 (131,FindErr) 
               : (transition list, int) HashTable.hash_table)
val todo    = ref ([] : (transition list * int) list)
val next    = ref 0

fun reset_state_mem () =
  (clearTable memory; todo := []; next := 0)

fun get_state st =
    HashTable.lookup memory st
    handle FindErr =>
      let val nbr = !next
       in incr next;
	  HashTable.insert memory (st,nbr);
	  todo := (st, nbr) :: !todo;
	  nbr
      end

(*******************************End JGR changes********************************)

fun map_on_states f =
    case !todo
      of []  => []
       | (st,i)::r =>
	   (todo := r; let val res = f st in (res,i) :: map_on_states f end)


fun number_of_states () = !next


fun goto_state [] = Backtrack
  | goto_state ps = Goto (get_state ps)


fun transition_from chars follow pos_set =
    let open Array infix 9 sub
	val tr = array(256, [])
	val shift = array(256, Backtrack)
    in
	List.app (fn pos =>
	      List.app (fn c =>
		     update(tr, Char.ord c,
		       merge_trans (tr sub (Char.ord c)) (follow sub pos)))
		  (chars sub pos))
	    pos_set;
	for (fn i => update(shift, i, goto_state (tr sub i)))
	    0 255;
	shift
    end


fun translate_state chars follow state =
    case split_trans_set state
      of (n, []) => Perform n
       | (n, ps) => Shift((if n = no_action then No_remember else Remember n),
			  transition_from chars follow ps)


fun make_dfa (lexdef: Syntax.rules) =
    let val (chars, name_regexp_list, actions) =
	  encode_lexdef lexdef
	val follow =
	  followpos (Array.length chars) name_regexp_list
	val () = reset_state_mem()
	val initial_states =
	  caml_map
	      (fn (name, regexp) => (name, get_state(firstpos regexp)))
	      name_regexp_list
	val states =
	  map_on_states (translate_state chars follow)
	val v =
	  Array.array(number_of_states(), Perform 0)
    in
	List.app (fn (auto, i) => Array.update(v, i, auto)) states;
	reset_state_mem();
	(initial_states, v, actions)
    end


end (* local *)
end (* structure DFA *)
