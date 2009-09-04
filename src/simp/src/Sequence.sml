(* copyright Univ. Cambridge/ Larry Paulson *)

structure Sequence :> Sequence =
struct

open liteLib;

fun prs s = Portable.output (Portable.std_out, s);

datatype 'a seq = Seq of unit -> ('a * 'a seq)option;

(*Return next sequence element as NONE or SOME(x,str) *)
fun seq_pull(Seq f) = f();

(*Head and tail.  Beware of calling the sequence function twice!!*)
fun seq_hd s = #1 (the (seq_pull s))
and seq_tl s = #2 (the (seq_pull s));

(*the abstraction for making a sequence*)
val mk_seq = Seq;

(*prefix an element to the sequence
    use cons(x,s) only if evaluation of s need not be delayed,
      otherwise use mk_seq(fn()=> SOME(x,s)) *)
fun seq_cons all = Seq(fn()=>SOME all);

(*the empty sequence*)
val seq_nil = Seq(fn()=>NONE);

fun seq_single(x) = seq_cons (x, seq_nil);

(*The list of the first n elements, paired with rest of sequence.
  If length of list is less than n, then sequence had less than n elements.*)
fun seq_chop (n:int, s: 'a seq): 'a list * 'a seq =
  if n<=0 then ([],s)
  else case seq_pull(s) of
           NONE => ([],s)
         | SOME(x,s') => let val (xs,s'') = seq_chop (n-1,s')
		         in  (x::xs, s'')  end;

(*conversion from sequence to list*)
fun list_of_seq (s: 'a seq) : 'a list = case seq_pull(s) of
        NONE => []
      | SOME(x,s') => x :: list_of_seq s';


(*conversion from list to sequence*)
fun seq_of_list []     = seq_nil
  | seq_of_list (x::l) = seq_cons (x, seq_of_list l);


(*functional to print a sequence, up to "count" elements
  the function prelem should print the element number and also the element*)
fun seq_print (prelem: int -> 'a -> unit) count (s: 'a seq) : unit =
  let fun pr (k,s) =
	   if k>count then ()
	   else case seq_pull(s) of
	       NONE => ()
	     | SOME(x,s') => (prelem k x;  prs"\n";  pr (k+1, s'))
  in  pr(1,s)  end;

(*Map the function f over the sequence, making a new sequence*)
fun seq_map f xq = mk_seq (fn()=> case seq_pull(xq) of
        NONE       => NONE
      | SOME(x,yq) => SOME(f x,  seq_map f yq));

(*Sequence seq_append:  put the elements of xq in front of those of yq*)
fun seq_append (xq,yq)  =
  let fun copy xq = mk_seq (fn()=>
	    case seq_pull xq of
		 NONE       => seq_pull yq
	       | SOME(x,xq') => SOME (x, copy xq'))
  in  copy xq end;

(*Interleave elements of xq with those of yq -- fairer than seq_append*)
fun seq_interleave (xq,yq) = mk_seq (fn()=>
      case seq_pull(xq) of
          NONE       => seq_pull yq
	| SOME(x,xq') => SOME (x, seq_interleave(yq, xq')));

(*map over a sequence xq, append the sequence yq*)
fun seq_mapp f xq yq =
  let fun copy s = mk_seq (fn()=>
            case seq_pull(s) of
	        NONE       => seq_pull(yq)
              | SOME(x,xq') => SOME(f x, copy xq'))
  in  copy xq end;

(*Flatten a sequence of sequences to a single sequence. *)
fun seq_flat ss = mk_seq (fn()=> case seq_pull(ss) of
        NONE => NONE
      | SOME(s,ss') =>  seq_pull(seq_append(s, seq_flat ss')));


(*accumulating a function over a sequence;  this is lazy*)
fun seq_iterate (f: 'a * 'b seq -> 'b seq) (s: 'a seq, bstr: 'b seq) : 'b seq =
  let fun its s = mk_seq (fn()=>
            case seq_pull(s) of
	        NONE       => seq_pull bstr
	      | SOME(a,s') => seq_pull(f(a, its s')))
  in  its s end;

fun seq_filter pred xq =
  let fun copy s = mk_seq (fn()=>
            case seq_pull(s) of
	        NONE       => NONE
              | SOME(x,xq') => if pred x then SOME(x, copy xq')
			       else seq_pull (copy xq') )
  in  copy xq end


fun seq_mapfilter f xq =
  let fun copy s = mk_seq (fn()=>
            case seq_pull(s) of
	        NONE       => NONE
              | SOME(x,xq') => SOME(f x, copy xq')
			       handle Interrupt => raise Interrupt
                                    | _ => seq_pull (copy xq'))
  in  copy xq end;



(*----------------------------------------------------------------------
 * seq_diagonalize
 *    compute the cross product of two sequences, yet only computing
 * each sequence once.
 * --------------------------------------------------------------------*)

local fun diag (s1,l1) (s2,l2) () =
	case (seq_pull s1,seq_pull s2) of
	    (NONE,NONE) => NONE
	  | (NONE,SOME (h2,s2')) =>
		seq_pull(seq_append(seq_of_list (map (fn x => (x,h2)) l1),
			    mk_seq (diag (seq_nil,l1) (s2',h2::l2))))
	  | (SOME (h1,s1'),NONE) =>
		seq_pull(seq_append(seq_of_list (map (fn x => (h1,x)) l2),
			    mk_seq (diag (s1',h1::l1) (seq_nil,l2))))
	  | (SOME (h1,s1'),SOME (h2,s2')) =>
		SOME ((h1,h2),
		      seq_append(seq_of_list (map (fn x => (h1,x)) l2),
			     seq_append(seq_of_list (map (fn x => (x,h2)) l1),
				    mk_seq (diag (s1',h1::l1) (s2',h2::l2)))))
in
fun seq_diagonalize s1 s2 = mk_seq (diag (s1,[]) (s2,[]))
end;

(*---------------------------------------------------------------------------
 * seq_permutations : 'a list -> 'a list seq
 *---------------------------------------------------------------------------*)

fun seq_permutations l =
   let fun remove_el n l =
       if (n = 1) then (hd l,tl l)
       else let val (x,l') = remove_el (n - 1) (tl l)
	    in  (x,(hd l)::l')
	    end
       fun one_smaller_subsets l =
          let fun one_smaller_subsets' l n () =
	      if (null l) then NONE
	      else SOME(remove_el n l,mk_seq (one_smaller_subsets' l (n + 1)))
		  handle Interrupt => raise Interrupt
                       | _ => NONE
          in  mk_seq (one_smaller_subsets' l 1)
          end
   in
   if (null l) then seq_nil
   else if (null (tl l)) then seq_single [hd l]
   else let val oss = one_smaller_subsets l
            val subperms = seq_map (fn (x,y) => (x,seq_permutations y)) oss
        in seq_flat (seq_map (fn (x,sofl) => seq_map (fn l => x::l) sofl) subperms)
        end
   end;


end (* struct *)

