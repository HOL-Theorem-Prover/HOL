(*---------------------------------------------------------------------------
    An abstract type of streams, where a stream element can be either 
    a character or an item of type 'a.
 ---------------------------------------------------------------------------*)
structure Strm :> Strm =
struct

(*---------------------------------------------------------------------------
   Need a type for grabbing things from a quotation.
 ---------------------------------------------------------------------------*)

datatype 'a item = CH of Char.char
                 | AQ of 'a;

datatype 'a strm = STRM of Substring.substring * 'a frag list;

(*---------------------------------------------------------------------------
   Create a strm from a quotation. Slightly optimized for the common case.
 ---------------------------------------------------------------------------*)
fun strm_of (QUOTE s::rst) = STRM(Substring.all s, rst)
  | strm_of L = STRM(Substring.all "", L);


(*---------------------------------------------------------------------------
    Grab something from the head of a stream. If the head is a character,
    then return it and the rest of the stream. If the head is an empty
    string, then shift to the next frag in the quotation. If the head is
    an antiquote, return it, and configure the rest of the stream.
 ---------------------------------------------------------------------------*)

fun get (STRM(prefix,flist)) =
  case Substring.getc prefix
   of SOME(c,ss) => SOME(CH c, STRM(ss,flist))
    | NONE => 
        (case flist 
          of [] => NONE
           | QUOTE s::rst => get (STRM(Substring.all s, rst))
           | ANTIQUOTE x::rst => SOME(AQ x, STRM(Substring.all "", rst)));


(*---------------------------------------------------------------------------
   Note: the following makes the assumption that "QUOTE" blocks in a 
   quotation are maximal. Thus we expect not to find a quotation that 
   looks like:

       [ ..., QUOTE <string1>, QUOTE <string2>, ... ]

   The quotations returned by the MoscowML compiler (and SML/NJ) already 
   meet this requirement.
 ---------------------------------------------------------------------------*)
   
fun dropl P (STRM(prefix,flist)) = STRM(Substring.dropl P prefix,flist);

fun splitl P (STRM(prefix,flist)) = 
   let val (l,r) = Substring.splitl P prefix
   in 
       (l, STRM(r, flist))
   end;

fun base (STRM(prefix,flist)) = Substring.base prefix;

local fun str_of [] = []
        | str_of (QUOTE s::rst) = s::str_of rst
        | str_of (ANTIQUOTE x::rst) = " <antiquote> "::str_of rst
in
fun string_of (STRM(ss,q)) = String.concat (Substring.string ss::str_of q)
end;


(*---------------------------------------------------------------------------*
 * Consume a potentially nested comment. The leading two characters of the   *
 * comment have already been seen.                                           *
 *---------------------------------------------------------------------------*)

local open Option
in
fun MLcomment s0 =
  case get s0
   of SOME (CH #"(", s1)      (* recursive comment, possibly *)
        => (case get s1
             of SOME (CH #"*", s2)  => mapPartial MLcomment (MLcomment s2)
              | SOME _ => MLcomment s1
              | NONE   => NONE)
    | SOME (CH #"*", s1) 
        => (case get s1
             of SOME (CH #")", s2) => SOME s2  (* found end of comment *)
              | SOME _ => MLcomment s1
              | NONE   => NONE)
    | SOME (_, s1) => MLcomment s1
    | NONE => NONE
end;

end;
