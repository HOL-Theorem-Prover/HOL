(* ===================================================================== *)
(* FILE          : lib.sml                                               *)
(* DESCRIPTION   : library of useful SML functions.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)


structure Lib :> Lib =
struct

fun LIB_ERR func mesg =
  Exception.HOL_ERR{origin_structure="Lib",
                    origin_function=func,
                    message=mesg};

(*---------------------------------------------------------------------------*
 * Combinators                                                               *
 *---------------------------------------------------------------------------*)

fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y
infix 3 ##
fun (f ## g) (x,y) = (f x, g y)
fun A f x = f x
fun B f g x = f (g x)
fun C f x y = f y x
fun I x = x
fun K x y = x
fun S f g x = f x (g x)
fun W f x = f x x

(*---------------------------------------------------------------------------*
 * Curried versions of infixes.                                              *
 *---------------------------------------------------------------------------*)

fun append l1 l2 = l1@l2
fun equal x y = (x=y);
val concat = curry (op ^)
fun cons a L = a::L

fun fst (x,_) = x   and   snd (_,y) = y;


(*---------------------------------------------------------------------------*
 * Success and failure.                                                      *
 *---------------------------------------------------------------------------*)

fun can f x =
  (f x; true) handle Interrupt => raise Interrupt | _  => false;

fun total f x = SOME (f x) handle Interrupt => raise Interrupt | _ => NONE;

fun partial e f x =
   case f x
    of SOME y => y
     | NONE => raise e;


(*---------------------------------------------------------------------------*
 * A version of try that coerces non-HOL_ERR exceptions to be HOL_ERRs.      *
 * To be used with tacticals and the like that get driven by HOL_ERR         *
 * exceptions.                                                               *
 *---------------------------------------------------------------------------*)

local open Exception
      val default_exn = HOL_ERR
             {origin_structure="Lib",
              origin_function="trye", message="original exn. not a HOL_ERR"}
in
fun trye f x = f x handle e as HOL_ERR _ => raise e
                        | Interrupt      => raise Interrupt
                        |         _      => raise default_exn
end;

(*---------------------------------------------------------------------------*
 * For interactive use: "Raise" prints out the exception.                    *
 *---------------------------------------------------------------------------*)

fun try f x =
  f x handle Interrupt => raise Interrupt | e => Exception.Raise e;


fun assert P x = if P x then x else raise LIB_ERR"assert" "predicate not true"


(*---------------------------------------------------------------------------*
 *        Common list operations                                             *
 *---------------------------------------------------------------------------*)

fun tryfind f =
 let fun F [] = raise LIB_ERR "tryfind" "all applications failed"
       | F (h::t) = f h handle Interrupt => raise Interrupt | _ => F t
 in F
 end;

(* Counting starts from 1 *)
local fun elem (_, [])     = raise LIB_ERR "el" "index too large"
        | elem (1, h::_)   = h
        | elem (n, _::rst) = elem (n-1, rst)
in
fun el n l =
  if n<1 then raise LIB_ERR "el" "index too small"
  else elem(n,l)
end;


fun map2 f L1 L2 =
 let fun mp2 [] [] L = rev L
       | mp2 (a1::rst1) (a2::rst2) L = mp2 rst1 rst2 (f a1 a2::L)
       | mp2 _ _ _ = raise LIB_ERR "map2" "different length lists"
   in mp2 L1 L2 []
   end;

fun all P =
   let fun every [] = true
         | every (a::rst) = P a andalso every rst
   in every
   end;

fun all2 P =
   let fun every2 [] [] = true
         | every2 (a1::rst1) (a2::rst2) = P a1 a2 andalso every2 rst1 rst2
         | every2  _ _ = raise LIB_ERR "all2" "different length lists"
   in every2
   end;

val exists = List.exists;

fun first P =
   let fun oneth (a::rst) = if P a then a else oneth rst
         | oneth [] = raise LIB_ERR "first" "unsatisfied predicate"
   in oneth
   end;

fun split_after n alist =
   if (n >= 0)
   then let fun spa 0 (L,R) = (rev L,R)
              | spa n (L,a::rst) = spa (n-1) (a::L, rst)
              | spa _ _ = raise LIB_ERR "split_after" "index too big"
        in spa n ([],alist)
        end
   else raise LIB_ERR "split_after" "negative index";


fun itlist f L base_value =
   let fun it [] = base_value
         | it (a::rst) = f a (it rst)
   in it L
   end;

fun itlist2 f L1 L2 base_value =
  let fun it ([],[]) = base_value
        | it (a::rst1, b::rst2) = f a b (it (rst1,rst2))
        | it _ = raise LIB_ERR "itlist2" "lists of different length"
   in  it (L1,L2)
   end;

fun rev_itlist f =
   let fun rev_it [] base = base
         | rev_it (a::rst) base = rev_it rst (f a base)
   in rev_it
   end;

fun rev_itlist2 f L1 L2 =
  let fun rev_it2 ([],[]) base = base
        | rev_it2 (a::rst1, b::rst2) base = rev_it2 (rst1,rst2) (f a b base)
        | rev_it2 _ _ = raise LIB_ERR"rev_itlist2" "lists of different length"
  in rev_it2 (L1,L2)
  end;

fun end_itlist f =
   let fun endit [] = raise LIB_ERR "end_itlist" "list too short"
         | endit [x] = x
         | endit (x::rst) = f x (endit rst)
   in endit
   end;

fun gather p L = itlist (fn x => fn y => if (p x) then x::y else y) L []

val filter = gather;

fun partition p alist =
   itlist (fn x => fn (L,R) => if (p x) then (x::L, R) else (L, x::R))
          alist ([],[]);

fun zip [] [] = []
  | zip (a::b) (c::d) = (a,c)::zip b d
  | zip _ _ = raise LIB_ERR "zip" "different length lists"

fun unzip L =
  itlist (fn (x,y) => fn (l1,l2) =>(x::l1, y::l2)) L ([],[]);

fun combine(l1,l2) = zip l1 l2
val split = unzip

fun mapfilter f list =
   itlist(fn i => fn L => (f i::L)
                          handle Interrupt => raise Interrupt
                               |         _ => L) list [];

fun flatten [] = []
  | flatten ([]::t) = flatten t
  | flatten ((h::t)::rst) = h::flatten(t::rst);

fun front_last [] = raise LIB_ERR "front_last" "empty list"
  | front_last [x] = ([],x)
  | front_last (h::t) = let val (L,b) = front_last t in (h::L,b) end;

fun last [] = raise LIB_ERR "last" "empty list"
  | last [x] = x
  | last (_::t) = last t

fun pluck P =
  let fun pl _ [] = raise LIB_ERR "pluck" "predicate not satisfied"
        | pl A (h::t) =
           if P h then (h, rev_itlist cons A t)
                  else pl (h::A) t
  in
     pl []
  end;

fun funpow n f x =
   let fun iter (0,res) = res
         | iter (n,res) = iter (n-1, f res)
   in
     if (n<0) then x else iter(n,x)
   end;

(*---------------------------------------------------------------------------*
 * For loops                                                                 *
 *---------------------------------------------------------------------------*)

fun for base top f =
   let fun For i = if (i>top) then [] else f i::For(i+1)
   in For base
   end;

fun for_se base top f =
   let fun For i = if (i>top) then () else (f i; For(i+1))
   in For base
   end;

fun list_of_array A = for 0 (Array.length A - 1) (fn i => Array.sub(A,i));

(*---------------------------------------------------------------------------*
 * Assoc lists.                                                              *
 *---------------------------------------------------------------------------*)

fun assoc item =
   let fun assc ((key,ob)::rst) = if (item = key) then ob else assc rst
         | assc [] = raise LIB_ERR "assoc" "not found"
   in assc
   end

fun assoc1 item =
   let fun assc ((entry as (key,_))::rst) =
             if (item = key) then SOME entry else assc rst
         | assc [] = NONE
    in assc
    end;

fun assoc2 item =
   let fun assc((entry as (_,key))::rst) =
            if (item = key) then SOME entry else assc rst
         | assc [] = NONE
   in assc
   end;

fun words2 sep string =
    snd (itlist (fn ch => fn (chs,tokl) =>
          if ch=sep
          then if (null chs) then ([],tokl)
		else ([], (Portable.implode chs :: tokl))
          else (ch::chs, tokl))
        (sep::Portable.explode string)
        ([],[]));

(*---------------------------------------------------------------------------*
 * A naive merge sort.                                                       *
 *---------------------------------------------------------------------------*)

fun sort P =
  let fun merge [] a = a
        | merge a [] = a
        | merge (A as (a::t1)) (B as (b::t2)) =
             if P a b then a::merge t1 B
                      else b::merge A t2
      fun srt [] = []
        | srt [a] = a
        | srt (h1::h2::t) = srt (merge h1 h2::t)
   in
     srt o (map (fn x => [x]))
   end;

val int_sort = sort (curry (op <= :int*int->bool))


(*---------------------------------------------------------------------------*
 * Substitutions.                                                            *
 *---------------------------------------------------------------------------*)
type ('a,'b) subst = {redex:'a, residue:'b} list

fun subst_assoc test =
 let fun assc [] = NONE
       | assc ({redex,residue}::rst) =
          if (test redex) then SOME(residue) else assc rst
   in assc
   end;

infix 5 |->
fun (r1 |-> r2) = {redex=r1, residue=r2};


(*---------------------------------------------------------------------------*
 * Sets as lists                                                             *
 *---------------------------------------------------------------------------*)

fun mem i =
   let fun itr (a::rst) = (i=a) orelse itr rst
         | itr [] = false
   in itr
   end;

fun insert i L = if (mem i L) then L else i::L

fun mk_set [] = []
  | mk_set (a::rst) = insert a (mk_set rst)

fun union [] S = S
  | union S [] = S
  | union (a::rst) S2 = union rst (insert a S2)

(* Union of a family of sets *)
fun U set_o_sets = itlist union set_o_sets []

(* All the elements in the first set that are not also in the second set. *)
fun set_diff a b = gather (fn x => not (mem x b)) a
val subtract = set_diff

fun intersect [] _ = []
  | intersect _ [] = []
  | intersect S1 S2 = mk_set(gather (C mem S2) S1)

fun null_intersection _  [] = true
  | null_intersection [] _ = true
  | null_intersection (a::rst) S =
        if (mem a S) then false
        else null_intersection rst S

fun set_eq S1 S2 = (set_diff S1 S2 = []) andalso (set_diff S2 S1 = []);

(*---------------------------------------------------------------------------*
 * Opaque type set operations                                                *
 *---------------------------------------------------------------------------*)

fun op_mem eq_func i =
   let val eqi = eq_func i
       fun mem [] = false
         | mem (a::b) = eqi a orelse mem b
   in mem
   end;

fun op_insert eq_func =
  let val mem = op_mem eq_func
  in fn i => fn L => if (mem i L) then L else i::L
  end;

fun op_mk_set eqf =
  let val insert = op_insert eqf
      fun mkset [] = []
        | mkset (a::rst) = insert a (mkset rst)
  in mkset
  end;

fun op_union eq_func =
   let val mem = op_mem eq_func
       val insert = op_insert eq_func
       fun un [] [] = []
         | un a []  = a
         | un [] a  = a
         | un (a::b) c = un b (insert a c)
   in un
   end;


(* Union of a family of sets *)
fun op_U eq_func set_o_sets = itlist (op_union eq_func) set_o_sets [];

fun op_intersect eq_func a b =
  let val mem = op_mem eq_func
      val in_b = C mem b
      val mk_set = op_mk_set eq_func
   in mk_set(gather in_b a)
   end;

(* All the elements in the first set that are not also in the second set. *)
fun op_set_diff eq_func S1 S2 =
  let val memb = op_mem eq_func
  in filter (fn x => not (memb x S2)) S1
  end;

(*---------------------------------------------------------------------------*
 * Strings.                                                                  *
 *---------------------------------------------------------------------------*)

val int_to_string = Int.toString;
val string_to_int =
  partial (LIB_ERR "string_to_int" "not convertable")
          Int.fromString

val say = TextIO.print;
fun quote s = let
  fun munge c =
    case c of
      #"\\" => "\\\\"
    | #"\n" => "\\n"
    | #"\"" => "\\\""
    | x => str x
in
  String.concat ["\"",String.translate munge s,"\""]
end

fun prime s = s^"'";

fun commafy [] = []
  | commafy [x] = [x]
  | commafy (x::rst) = (x::", "::commafy rst);


(*---------------------------------------------------------------------------*
 * Timing                                                                    *
 *---------------------------------------------------------------------------*)

fun start_time () = Timer.startCPUTimer()

fun end_time timer =
  let val {gc,sys,usr} = Timer.checkCPUTimer timer
  in
     Portable.output(Portable.std_out,
          "runtime: "^Time.toString usr ^ "s,\
      \    gctime: "^Time.toString gc ^ "s, \
      \    systime: "^Time.toString sys ^"s.\n");
     Portable.flush_out(Portable.std_out)
  end

fun time f x =
  let val timer = start_time()
      val y = f x
  in
     end_time timer;  y
  end


(*---------------------------------------------------------------------------*
 * Invoking a function with a flag temporarily assigned to the given value.  *
 *---------------------------------------------------------------------------*)

fun with_flag (flag,b) f x =
  let val fval = !flag
      val () = flag := b
      val res = f x handle e => (flag := fval;
                                 case e of Interrupt => raise e
                                         | _ => Exception.Raise e)
   in
     flag := fval;
     res
   end;


(*---------------------------------------------------------------------------*
 * An abstract type of imperative streams.                                   *
 *---------------------------------------------------------------------------*)

abstype ('a,'b) istream = STRM of {mutator : 'a -> 'a,
                                   project : 'a -> 'b,
                                   state   : 'a ref,
                                   init    : 'a}
with
  fun mk_istream f i g = STRM{mutator=f, project=g, state=ref i, init=i}
  fun next(strm as STRM{mutator, state, ...}) =
    let val _ = state := mutator (!state)
    in strm end;
  fun state(STRM{project,state, ...}) = project(!state)
  fun reset(strm as STRM{state, init, ...}) =
      let val _ = state := init
      in strm end;
end;

(* Should be generalized to an arbitrary outstream. *)
fun mesg false _ = ()
  | mesg true s = say(String.concat["<<HOL message: ", s, ".>>\n"]);

(*---------------------------------------------------------------------------*
 * A hash function used for various tasks in the system. It works fairly     *
 * well for our applications, but is not industrial strength. The size       *
 * argument should be a prime. The function then takes a string and          *
 * a pair (i,A) and returns a number < size. In the pair (i,A), "i" is       *
 * the index in the string to start hashing from, and A is an accumulator.   *
 * In simple cases i=0 and A=0.                                              *
 *---------------------------------------------------------------------------*)

local open Char String
in
fun hash size = fn s =>
  let fun hsh(i,A) =
       hsh(i+1, (A*4 + ord(sub(s,i))) mod size)
        handle Subscript => A
  in hsh end
end;


datatype ('a,'b)sum = LEFT of 'a | RIGHT of 'b;


end (* Lib *)
