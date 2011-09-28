(* PP -- Oppen-style prettyprinters.
 *
 * Modified for Moscow ML from SML/NJ Library version 0.2
 *
 * COPYRIGHT (c) 1992 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *)

(* the functions and data for actually doing printing. *)
structure HOLPP :> HOLPP =
struct

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
type 'a quotation = 'a frag list


open Array
infix 9 sub

fun magic x = x

(* the queue library, formerly in unit Ppqueue *)

datatype Qend = Qback | Qfront

exception QUEUE_FULL
exception QUEUE_EMPTY
exception REQUESTED_QUEUE_SIZE_TOO_SMALL

local
    fun ++ i n = (i + 1) mod n
    fun -- i n = (i - 1) mod n
in

abstype 'a queue = QUEUE of {elems: 'a array, (* the contents *)
                             front: int ref,
                             back: int ref,
                             size: int}  (* fixed size of element array *)
with

  fun is_empty (QUEUE{front=ref ~1, back=ref ~1,...}) = true
    | is_empty _ = false

  fun mk_queue n init_val =
      if (n < 2)
      then raise REQUESTED_QUEUE_SIZE_TOO_SMALL
      else QUEUE{elems=array(n, init_val), front=ref ~1, back=ref ~1, size=n}

  fun clear_queue (QUEUE{front,back,...}) = (front := ~1; back := ~1)

  fun queue_at Qfront (QUEUE{elems,front,...}) = elems sub !front
    | queue_at Qback (QUEUE{elems,back,...}) = elems sub !back

  fun en_queue Qfront item (Q as QUEUE{elems,front,back,size}) =
        if (is_empty Q)
        then (front := 0; back := 0;
              update(elems,0,item))
        else let val i = --(!front) size
             in  if (i = !back)
                 then raise QUEUE_FULL
                 else (update(elems,i,item); front := i)
             end
    | en_queue Qback item (Q as QUEUE{elems,front,back,size}) =
        if (is_empty Q)
        then (front := 0; back := 0;
              update(elems,0,item))
        else let val i = ++(!back) size
             in  if (i = !front)
                 then raise QUEUE_FULL
                 else (update(elems,i,item); back := i)
             end

  fun de_queue Qfront (Q as QUEUE{front,back,size,...}) =
        if (!front = !back) (* unitary queue *)
        then clear_queue Q
        else front := ++(!front) size
    | de_queue Qback (Q as QUEUE{front,back,size,...}) =
        if (!front = !back)
        then clear_queue Q
        else back := --(!back) size

end (* abstype queue *)
end (* local   *)


(* exception PP_FAIL of string *)

datatype break_style = CONSISTENT | INCONSISTENT

datatype break_info
  = FITS
  | PACK_ONTO_LINE of int
  | ONE_PER_LINE of int

(* Some global values *)
val INFINITY = 999999

abstype indent_stack = Istack of break_info list ref
with
  fun mk_indent_stack() = Istack (ref([]:break_info list))
  fun clear_indent_stack (Istack stk) = (stk := ([]:break_info list))
  fun top (Istack stk) =
      case !stk
        of nil => raise Fail "PP-error: top: badly formed block"
	 | x::_ => x
  fun push (x,(Istack stk)) = stk := x::(!stk)
  fun pop (Istack stk) =
      case !stk
        of nil => raise Fail "PP-error: pop: badly formed block"
	 | _::rest => stk := rest
end

(* The delim_stack is used to compute the size of blocks. It is
   a stack of indices into the token buffer. The indices only point to
   BBs, Es, and BRs. We push BBs and Es onto the stack until a BR
   is encountered. Then we compute sizes and pop. When we encounter
   a BR in the middle of a block, we compute the Distance_to_next_break
   of the previous BR in the block, if there was one.

   We need to be able to delete from the bottom of the delim_stack, so
   we use a queue, treated with a stack discipline, i.e., we only add
   items at the head of the queue, but can delete from the front or
   back of the queue.
*)
abstype delim_stack = Dstack of int queue
with
  fun new_delim_stack i = Dstack(mk_queue i ~1)
  fun reset_delim_stack (Dstack q) = clear_queue q

  fun pop_delim_stack (Dstack d) = de_queue Qfront d
  fun pop_bottom_delim_stack (Dstack d) = de_queue Qback d

  fun push_delim_stack(i,Dstack d) = en_queue Qfront i d
  fun top_delim_stack (Dstack d) = queue_at Qfront d
  fun bottom_delim_stack (Dstack d) = queue_at Qback d
  fun delim_stack_is_empty (Dstack d) = is_empty d
end


type block_info = { Block_size : int ref,
                    Block_offset : int,
                    How_to_indent : break_style }


(* Distance_to_next_break includes Number_of_blanks. Break_offset is
   a local offset for the break. BB represents a sequence of contiguous
   Begins. E represents a sequence of contiguous Ends.
*)
datatype pp_token
  = S of  {String : string, Length : int}
  | BB of {Pblocks : block_info list ref,   (* Processed   *)
           Ublocks : block_info list ref}  (* Unprocessed *)
  | E of  {Pend : int ref, Uend : int ref}
  | BR of {Distance_to_next_break : int ref,
           Number_of_blanks : int,
           Break_offset : int}


(* The initial values in the token buffer *)
val initial_token_value = S{String = "", Length = 0}

datatype ppstream =
  PPS of
     {consumer : string -> unit,
      linewidth : int,
      flush : unit -> unit,
      the_token_buffer : pp_token array,
      the_delim_stack : delim_stack,
      the_indent_stack : indent_stack,
      ++ : int ref -> unit,    (* increment circular buffer index *)
      space_left : int ref,    (* remaining columns on page *)
      left_index : int ref,    (* insertion index *)
      right_index : int ref,   (* output index *)
      left_sum : int ref,      (* size of strings and spaces inserted *)
      right_sum : int ref}     (* size of strings and spaces printed *)

fun lineWidth (PPS {linewidth, ...}) = linewidth

type ppconsumer = {consumer : string -> unit,
		   linewidth : int,
		   flush : unit -> unit}

fun safe_consumer ofn = let
  val output_stack = ref ([]:string list)
  fun doit s = let
  in
    if String.size s = 0 then ()
    else if String.sub(s,0) = #"\n" then
      (output_stack := []; ofn ("\n"); doit(String.extract(s,1,NONE)))
    else if CharVector.all Char.isSpace s then
      output_stack := s :: !output_stack
    else (List.app ofn (List.rev (!output_stack));
          output_stack := [];
          ofn(s))
  end
in
  doit
end

fun mk_ppstream {consumer,linewidth,flush} =
    if (linewidth<5)
    then raise Fail "PP-error: linewidth too_small"
    else let val buf_size = 3*linewidth
          in
             PPS{consumer = safe_consumer consumer,
		 linewidth = linewidth,
		 flush = flush,
		 the_token_buffer = array(buf_size, initial_token_value),
		 the_delim_stack = new_delim_stack buf_size,
		 the_indent_stack = mk_indent_stack (),
		 ++ = fn i => i := ((!i + 1) mod buf_size),
		 space_left = ref linewidth,
		 left_index = ref 0, right_index = ref 0,
		 left_sum = ref 0, right_sum = ref 0}
	 end



fun dest_ppstream(pps : ppstream) =
  let val PPS{consumer,linewidth,flush, ...} = pps
  in {consumer=consumer,linewidth=linewidth,flush=flush} end

local
  val space = " "
  fun mk_space (0,s) = String.concat s
    | mk_space (n,s) = mk_space((n-1), (space::s))
  val space_table = Vector.tabulate(100, fn i => mk_space(i,[]))
  fun nspaces n = Vector.sub(space_table, n)
      handle General.Subscript =>
	if n < 0
	then ""
	else let val n2 = n div 2
		 val n2_spaces = nspaces n2
		 val extra = if (n = (2*n2)) then "" else space
              in String.concat [n2_spaces, n2_spaces, extra]
	     end
in
  fun cr_indent (ofn, i) = ofn ("\n"^(nspaces i))
  fun indent (ofn,i) = ofn (nspaces i)
end


(* Print a the first member of a contiguous sequence of Begins. If there
   are "processed" Begins, then take the first off the list. If there are
   no processed Begins, take the last member off the "unprocessed" list.
   This works because the unprocessed list is treated as a stack, the
   processed list as a FIFO queue. How can an item on the unprocessed list
   be printable? Because of what goes on in add_string. See there for details.
*)

fun print_BB (_,{Pblocks = ref [], Ublocks = ref []}) =
             raise Fail "PP-error: print_BB"
  | print_BB (PPS{the_indent_stack,linewidth,space_left=ref sp_left,...},
             {Pblocks as ref({How_to_indent=CONSISTENT,Block_size,
                              Block_offset}::rst),
              Ublocks=ref[]}) =
       (push ((if (!Block_size > sp_left)
               then ONE_PER_LINE (linewidth - (sp_left - Block_offset))
               else FITS),
	      the_indent_stack);
        Pblocks := rst)
  | print_BB(PPS{the_indent_stack,linewidth,space_left=ref sp_left,...},
             {Pblocks as ref({Block_size,Block_offset,...}::rst),Ublocks=ref[]}) =
       (push ((if (!Block_size > sp_left)
               then PACK_ONTO_LINE (linewidth - (sp_left - Block_offset))
               else FITS),
	      the_indent_stack);
        Pblocks := rst)
  | print_BB (PPS{the_indent_stack, linewidth, space_left=ref sp_left,...},
              {Ublocks,...}) =
      let fun pr_end_Ublock [{How_to_indent=CONSISTENT,Block_size,Block_offset}] l =
		(push ((if (!Block_size > sp_left)
			then ONE_PER_LINE (linewidth - (sp_left - Block_offset))
			else FITS),
		       the_indent_stack);
                 List.rev l)
	    | pr_end_Ublock [{Block_size,Block_offset,...}] l =
		(push ((if (!Block_size > sp_left)
			then PACK_ONTO_LINE (linewidth - (sp_left - Block_offset))
			else FITS),
		       the_indent_stack);
                 List.rev l)
	    | pr_end_Ublock (a::rst) l = pr_end_Ublock rst (a::l)
            | pr_end_Ublock _ _ =
                raise Fail "PP-error: print_BB: internal error"
       in Ublocks := pr_end_Ublock(!Ublocks) []
      end


(* Uend should always be 0 when print_E is called. *)
fun print_E (_,{Pend = ref 0, Uend = ref 0}) =
      raise Fail "PP-error: print_E"
  | print_E (istack,{Pend, ...}) =
      let fun pop_n_times 0 = ()
	    | pop_n_times n = (pop istack; pop_n_times(n-1))
       in pop_n_times(!Pend); Pend := 0
      end


(* "cursor" is how many spaces across the page we are. *)

fun print_token(PPS{consumer,space_left,...}, S{String,Length}) =
      (consumer String;
       space_left := (!space_left) - Length)
  | print_token(ppstrm,BB b) = print_BB(ppstrm,b)
  | print_token(PPS{the_indent_stack,...},E e) =
      print_E (the_indent_stack,e)
  | print_token (PPS{the_indent_stack,space_left,consumer,linewidth,...},
                 BR{Distance_to_next_break,Number_of_blanks,Break_offset}) =
     (case (top the_indent_stack)
        of FITS =>
	     (space_left := (!space_left) - Number_of_blanks;
              indent (consumer,Number_of_blanks))
         | (ONE_PER_LINE cursor) =>
             let val new_cursor = cursor + Break_offset
              in space_left := linewidth - new_cursor;
                 cr_indent (consumer,new_cursor)
	     end
         | (PACK_ONTO_LINE cursor) =>
	     if (!Distance_to_next_break > (!space_left))
	     then let val new_cursor = cursor + Break_offset
		   in space_left := linewidth - new_cursor;
		      cr_indent(consumer,new_cursor)
		  end
	     else (space_left := !space_left - Number_of_blanks;
		   indent (consumer,Number_of_blanks)))


fun clear_ppstream(pps : ppstream) =
    let val PPS{the_token_buffer, the_delim_stack,
                the_indent_stack,left_sum, right_sum,
                left_index, right_index,space_left,linewidth,...}
              = pps
        val buf_size = 3*linewidth
	fun set i =
	    if (i = buf_size)
	    then ()
	    else (update(the_token_buffer,i,initial_token_value);
		  set (i+1))
     in set 0;
	clear_indent_stack the_indent_stack;
	reset_delim_stack the_delim_stack;
	left_sum := 0; right_sum := 0;
	left_index := 0; right_index := 0;
	space_left := linewidth
    end


(* Move insertion head to right unless adding a BB and already at a BB,
   or unless adding an E and already at an E.
*)
fun BB_inc_right_index(PPS{the_token_buffer, right_index, ++,...})=
    case (the_token_buffer sub (!right_index))
      of (BB _) => ()
       | _ => ++right_index

fun E_inc_right_index(PPS{the_token_buffer,right_index, ++,...})=
    case (the_token_buffer sub (!right_index))
      of (E _) => ()
       | _ => ++right_index


fun pointers_coincide(PPS{left_index,right_index,the_token_buffer,...}) =
    (!left_index = !right_index) andalso
    (case (the_token_buffer sub (!left_index))
       of (BB {Pblocks = ref [], Ublocks = ref []}) => true
	| (BB _) => false
	| (E {Pend = ref 0, Uend = ref 0}) => true
	| (E _) => false
	| _ => true)

fun advance_left (ppstrm as PPS{consumer,left_index,left_sum,
                                the_token_buffer,++,...},
                  instr) =
    let val NEG = ~1
	val POS = 0
	fun inc_left_sum (BR{Number_of_blanks, ...}) =
		 left_sum := (!left_sum) + Number_of_blanks
	  | inc_left_sum (S{Length, ...}) = left_sum := (!left_sum) + Length
	  | inc_left_sum _ = ()

	fun last_size [{Block_size, ...}:block_info] = !Block_size
	  | last_size (_::rst) = last_size rst
          | last_size _ = raise Fail "PP-error: last_size: internal error"
	fun token_size (S{Length, ...}) = Length
	  | token_size (BB b) =
	     (case b
                of {Pblocks = ref [], Ublocks = ref []} =>
                     raise Fail "PP-error: BB_size"
	         | {Pblocks as ref(_::_),Ublocks=ref[]} => POS
		 | {Ublocks, ...} => last_size (!Ublocks))
	  | token_size (E{Pend = ref 0, Uend = ref 0}) =
              raise Fail "PP-error: token_size.E"
	  | token_size (E{Pend = ref 0, ...}) = NEG
	  | token_size (E _) = POS
	  | token_size (BR {Distance_to_next_break, ...}) = !Distance_to_next_break
	fun loop (instr) =
	    if (token_size instr < 0)  (* synchronization point; cannot advance *)
	    then ()
	    else (print_token(ppstrm,instr);
		  inc_left_sum instr;
		  if (pointers_coincide ppstrm)
		  then ()
		  else (* increment left index *)

    (* When this is evaluated, we know that the left_index has not yet
       caught up to the right_index. If we are at a BB or an E, we can
       increment left_index if there is no work to be done, i.e., all Begins
       or Ends have been dealt with. Also, we should do some housekeeping and
       clear the buffer at left_index, otherwise we can get errors when
       left_index catches up to right_index and we reset the indices to 0.
       (We might find ourselves adding a BB to an "old" BB, with the result
       that the index is not pushed onto the delim_stack. This can lead to
       mangled output.)
    *)
		       (case (the_token_buffer sub (!left_index))
			  of (BB {Pblocks = ref [], Ublocks = ref []}) =>
			       (update(the_token_buffer,!left_index,
				       initial_token_value);
				++left_index)
			   | (BB _) => ()
			   | (E {Pend = ref 0, Uend = ref 0}) =>
			       (update(the_token_buffer,!left_index,
				       initial_token_value);
				++left_index)
			   | (E _) => ()
			   | _ => ++left_index;
			loop (the_token_buffer sub (!left_index))))
     in loop instr
    end


fun begin_block (pps : ppstream) style offset =
  let val ppstrm = pps : ppstream
      val PPS{the_token_buffer, the_delim_stack,left_index,
              left_sum, right_index, right_sum,...}
            = ppstrm
  in
   (if (delim_stack_is_empty the_delim_stack)
    then (left_index := 0;
	  left_sum := 1;
	  right_index := 0;
	  right_sum := 1)
    else BB_inc_right_index ppstrm;
    case (the_token_buffer sub (!right_index))
      of (BB {Ublocks, ...}) =>
	   Ublocks := {Block_size = ref (~(!right_sum)),
		       Block_offset = offset,
		       How_to_indent = style}::(!Ublocks)
       | _ => (update(the_token_buffer, !right_index,
		      BB{Pblocks = ref [],
			 Ublocks = ref [{Block_size = ref (~(!right_sum)),
					 Block_offset = offset,
					 How_to_indent = style}]});
	       push_delim_stack (!right_index, the_delim_stack)))
  end

fun end_block(pps : ppstream) =
  let val ppstrm = pps
      val PPS{the_token_buffer,the_delim_stack,right_index,...}
            = ppstrm
  in
    if (delim_stack_is_empty the_delim_stack)
    then print_token(ppstrm,(E{Pend = ref 1, Uend = ref 0}))
    else (E_inc_right_index ppstrm;
	  case (the_token_buffer sub (!right_index))
            of (E{Uend, ...}) => Uend := !Uend + 1
	     | _ => (update(the_token_buffer,!right_index,
			    E{Uend = ref 1, Pend = ref 0});
		     push_delim_stack (!right_index, the_delim_stack)))
  end

local
  fun check_delim_stack(PPS{the_token_buffer,the_delim_stack,right_sum,...}) =
      let fun check k =
	      if (delim_stack_is_empty the_delim_stack)
	      then ()
	      else case(the_token_buffer sub (top_delim_stack the_delim_stack))
		     of (BB{Ublocks as ref ((b as {Block_size, ...})::rst),
			    Pblocks}) =>
			   if (k>0)
			   then (Block_size := !right_sum + !Block_size;
				 Pblocks := b :: (!Pblocks);
				 Ublocks := rst;
				 if (List.length rst = 0)
				 then pop_delim_stack the_delim_stack
				 else ();
				 check(k-1))
			   else ()
		      | (E{Pend,Uend}) =>
			   (Pend := (!Pend) + (!Uend);
			    Uend := 0;
			    pop_delim_stack the_delim_stack;
			    check(k + !Pend))
		      | (BR{Distance_to_next_break, ...}) =>
			   (Distance_to_next_break :=
			      !right_sum + !Distance_to_next_break;
			    pop_delim_stack the_delim_stack;
			    if (k>0)
			    then check k
			    else ())
                      | _ => raise Fail "PP-error: check_delim_stack.catchall"
       in check 0
      end
in

  fun add_break (pps : ppstream) (n, break_offset) =
    let val ppstrm = magic pps : ppstream
        val PPS{the_token_buffer,the_delim_stack,left_index,
                right_index,left_sum,right_sum, ++, ...}
              = ppstrm
    in
      (if (delim_stack_is_empty the_delim_stack)
       then (left_index := 0; right_index := 0;
	     left_sum := 1;   right_sum := 1)
       else ++right_index;
       update(the_token_buffer, !right_index,
	      BR{Distance_to_next_break = ref (~(!right_sum)),
		 Number_of_blanks = n,
		 Break_offset = break_offset});
       check_delim_stack ppstrm;
       right_sum := (!right_sum) + n;
       push_delim_stack (!right_index,the_delim_stack))
    end

  fun flush_ppstream0(pps : ppstream) =
    let val ppstrm = magic pps : ppstream
        val PPS{the_delim_stack,the_token_buffer, flush, left_index,...}
              = ppstrm
    in
      (if (delim_stack_is_empty the_delim_stack)
       then ()
       else (check_delim_stack ppstrm;
	     advance_left(ppstrm, the_token_buffer sub (!left_index)));
       flush())
    end

end (* local *)


fun flush_ppstream ppstrm =
    (flush_ppstream0 ppstrm;
     clear_ppstream ppstrm)

fun add_stringsz (pps : ppstream) (s,slen) =
    let val PPS{the_token_buffer,the_delim_stack,consumer,
                right_index,right_sum,left_sum,
                left_index,space_left,++,...}
              = pps
        fun fnl [{Block_size, ...}:block_info] = Block_size := INFINITY
	  | fnl (_::rst) = fnl rst
          | fnl _ = raise Fail "PP-error: fnl: internal error"

	fun set(dstack,BB{Ublocks as ref[{Block_size,...}:block_info],...}) =
	      (pop_bottom_delim_stack dstack;
	       Block_size := INFINITY)
	  | set (_,BB {Ublocks = ref(_::rst), ...}) = fnl rst
	  | set (dstack, E{Pend,Uend}) =
	      (Pend := (!Pend) + (!Uend);
	       Uend := 0;
	       pop_bottom_delim_stack dstack)
	  | set (dstack,BR{Distance_to_next_break,...}) =
	      (pop_bottom_delim_stack dstack;
	       Distance_to_next_break := INFINITY)
          | set _ = raise (Fail "PP-error: add_string.set")

	fun check_stream () =
	    if ((!right_sum - !left_sum) > !space_left)
	    then if (delim_stack_is_empty the_delim_stack)
		 then ()
		 else let val i = bottom_delim_stack the_delim_stack
		       in if (!left_index = i)
			  then set (the_delim_stack, the_token_buffer sub i)
			  else ();
			  advance_left(pps, the_token_buffer sub (!left_index));
		          if (pointers_coincide pps) then ()
                          else check_stream ()
		      end
	    else ()

	val S_token = S{String = s, Length = slen}

    in if (delim_stack_is_empty the_delim_stack)
       then print_token(pps,S_token)
       else (++right_index;
             update(the_token_buffer, !right_index, S_token);
             right_sum := (!right_sum)+slen;
             check_stream ())
   end


fun add_string pps s = let
  val slen = UTF8.size s
in
  add_stringsz pps (s,slen)
end

(* Derived form. The +2 is for peace of mind *)
fun add_newline (pps : ppstream) =
  let val PPS{linewidth, ...} = pps
  in add_break pps (linewidth+2,0) end

(* Derived form. Builds a ppstream, sends pretty printing commands called in
   f to the ppstream, then flushes ppstream.
*)
val catch_withpp_err = ref true

fun with_pp ppconsumer ppfn = let
  val ppstrm = mk_ppstream ppconsumer
in
  ppfn ppstrm;
  flush_ppstream0 ppstrm
end handle e as Fail msg =>
           if !catch_withpp_err then
             TextIO.print (">>>> Pretty-printer failure: " ^ msg ^ "\n")
           else raise e

fun pp_to_string linewidth ppfn ob =
    let val l = ref ([]:string list)
	fun attach s = l := (s::(!l))
     in with_pp {consumer = attach, linewidth=linewidth, flush = fn()=>()}
		(fn ppstrm =>  ppfn ppstrm ob);
	String.concat(List.rev(!l))
    end
end; (* struct *)
