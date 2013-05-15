(*****************************************************************************)
(* FILE          : streams.sml                                               *)
(* DESCRIPTION   : Datatype and functions for streams (lazy lists).          *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 20th April 1991                                           *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Streams :> Streams =
struct
  open Arbint
  val op << = String.<


open Lib;
infix ##;

(*---------------------------------------------------------------------------*)
(* Datatype for lazy lists                                                   *)
(*---------------------------------------------------------------------------*)

datatype 'a stream = Stream of 'a * (unit -> 'a stream);

exception end_of_stream;

(*---------------------------------------------------------------------------*)
(* stream_map : ('a -> 'b) -> (unit -> 'a stream) -> (unit -> 'b stream)     *)
(*---------------------------------------------------------------------------*)

fun stream_map f s () =
   case s ()
   of (Stream (x,s')) => (Stream (f x,stream_map f s'));

(*---------------------------------------------------------------------------*)
(* stream_append : (unit -> 'a stream) ->                                    *)
(*                 (unit -> 'a stream) ->                                    *)
(*                 (unit -> 'a stream)                                       *)
(*---------------------------------------------------------------------------*)

fun stream_append s1 s2 () =
   (case s1 ()
    of (Stream (x,s1')) => (Stream (x,stream_append s1' s2)))
   handle end_of_stream => s2 ();

(*---------------------------------------------------------------------------*)
(* stream_flat : (unit -> (unit -> 'a stream) stream) -> unit -> 'a stream   *)
(*---------------------------------------------------------------------------*)

fun stream_flat ss () =
   case ss ()
   of (Stream (s,ss')) => (stream_append s (stream_flat ss') ());

(*---------------------------------------------------------------------------*)
(* permutations : 'a list -> unit -> 'a list stream                          *)
(*---------------------------------------------------------------------------*)

fun permutations l () =
   let fun remove_el n l =
          if ((null l) orelse (n < one))
          then raise end_of_stream
          else if (n = one)
               then (hd l,tl l)
               else let val (x,l') = remove_el (n - one) (tl l)
                    in  (x,(hd l)::l')
                    end
       fun one_smaller_subsets l =
          let fun one_smaller_subsets' l n () =
                 if (null l)
                 then raise end_of_stream
                 else Stream (remove_el n l,one_smaller_subsets' l (n + one))
          in  one_smaller_subsets' l one
          end
   in
   if (null l) then raise end_of_stream
   else if (null (tl l)) then Stream ([hd l],fn () => raise end_of_stream)
   else let val oss = one_smaller_subsets l
            val subperms = stream_map (I ## permutations) oss
        in  stream_flat
               (stream_map (fn (x,sofl) => stream_map (fn l => x::l) sofl)
                   subperms) ()
        end
   end;

end
