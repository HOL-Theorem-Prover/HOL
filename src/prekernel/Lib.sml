(* ===================================================================== *)
(* FILE          : Lib.sml                                               *)
(* DESCRIPTION   : library of useful SML functions.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)


structure Lib :> Lib =
struct

open Feedback;

val ERR = mk_HOL_ERR "Lib";

datatype frag = datatype Portable.frag

(*---------------------------------------------------------------------------*
 * Combinators                                                               *
 *---------------------------------------------------------------------------*)

fun curry f x y = f (x,y)
fun uncurry f (x,y) = f x y
infix 3 ##
fun (f ## g) (x,y) = (f x, g y)
fun apfst f (x, y) = (f x, y)
fun apsnd f (x, y) = (x, f y)
infix |>
fun x |> f = f x
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
val strcat = curry (op ^)
fun cons a L = a::L
fun pair x y = (x,y)

fun rpair x y = (y,x)
fun swap (x,y) = (y,x)
fun fst (x,_) = x
fun snd (_,y) = y

fun triple x y z = (x, y, z)
fun quadruple x1 x2 x3 x4 = (x1, x2, x3, x4)

(*---------------------------------------------------------------------------*
 * Success and failure. Interrupt has a special status in Standard ML.       *
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

local val default_exn = ERR "trye" "original exn. not a HOL_ERR"
in
fun trye f x =
  f x handle e as HOL_ERR _ => raise e
           | Interrupt      => raise Interrupt
           | _              => raise default_exn
end;

(*---------------------------------------------------------------------------*
 * For interactive use: "Raise" prints out the exception.                    *
 *---------------------------------------------------------------------------*)

fun try f x = f x handle e => Feedback.Raise e;

fun assert_exn P x e = if P x then x else raise e
fun assert P x       = assert_exn P x (ERR"assert" "predicate not true")
fun with_exn f x e   = f x handle Interrupt => raise Interrupt | _ => raise e


(*---------------------------------------------------------------------------*
 *        Common list operations                                             *
 *---------------------------------------------------------------------------*)

fun single x = [x]

(* turning lists into tuples *)

fun singleton_of_list [x] = x
  | singleton_of_list _ = raise ERR "singleton_of_list" "not a list of length 1"

fun pair_of_list [x, y] = (x, y)
  | pair_of_list _ = raise ERR "pair_of_list" "not a list of length 2"

fun triple_of_list [x, y, z] = (x, y, z)
  | triple_of_list _ = raise ERR "triple_of_list" "not a list of length 3"

fun quadruple_of_list [x1, x2, x3, x4] = (x1, x2, x3, x4)
  | quadruple_of_list _ = raise ERR "quadruple_of_list" "not a list of length 4"


fun tryfind f =
 let fun F [] = raise ERR "tryfind" "all applications failed"
       | F (h::t) = f h handle Interrupt => raise Interrupt | _ => F t
 in F
 end;

(* Counting starts from 1 *)
fun el n l =
 if n<1 then raise ERR "el" "index too small" else
 let fun elem (_, [])     = raise ERR "el" "index too large"
       | elem (1, h::_)   = h
       | elem (n, _::rst) = elem (n-1, rst)
 in
    elem(n,l)
 end;

fun index P l =
  let fun idx (i, [])   = raise ERR "index" "no such element"
        | idx (i, y::l) = if P y then i else idx (i+1, l)
  in idx(0,l)
  end;

fun map2 f L1 L2 =
 let fun mp2 [] [] L = rev L
       | mp2 (a1::rst1) (a2::rst2) L = mp2 rst1 rst2 (f a1 a2::L)
       | mp2 _ _ _ = raise ERR "map2" "different length lists"
   in mp2 L1 L2 []
   end;

val all = List.all

fun all2 P =
   let fun every2 [] [] = true
         | every2 (a1::rst1) (a2::rst2) = P a1 a2 andalso every2 rst1 rst2
         | every2  _ _ = raise ERR "all2" "different length lists"
   in every2
   end;

val exists = List.exists;

fun first P =
   let fun oneth (a::rst) = if P a then a else oneth rst
         | oneth [] = raise ERR "first" "unsatisfied predicate"
   in oneth
   end;

fun first_opt f =
   let fun fo n [] = NONE
         | fo n (a::rst) =
              let val vo = f n a handle Interrupt => raise Interrupt | _  => NONE in
              if (isSome vo) then vo else fo (n+1) rst end;
   in fo 0 end;

fun split_after n alist =
   if n >= 0
   then let fun spa 0 (L,R) = (rev L,R)
              | spa n (L,a::rst) = spa (n-1) (a::L, rst)
              | spa _ _ = raise ERR "split_after" "index too big"
        in spa n ([],alist)
        end
   else raise ERR "split_after" "negative index";

fun itlist f L base_value = List.foldr (uncurry f) base_value L

fun itlist2 f L1 L2 base_value =
  let fun itl ([],[]) = base_value
        | itl (a::rst1, b::rst2) = f a b (itl (rst1,rst2))
        | itl _ = raise ERR "itlist2" "lists of different length"
   in  itl (L1,L2)
   end;

fun rev_itlist f L base_value = List.foldl (uncurry f) base_value L

fun rev_itlist2 f L1 L2 =
  let fun rev_it2 ([],[]) base = base
        | rev_it2 (a::rst1, b::rst2) base = rev_it2 (rst1,rst2) (f a b base)
        | rev_it2 _ _ = raise ERR"rev_itlist2" "lists of different length"
  in rev_it2 (L1,L2)
  end;

fun end_itlist f =
   let fun endit [] = raise ERR "end_itlist" "list too short"
         | endit [x] = x
         | endit (h::t) = f h (endit t)
   in endit
   end;

fun foldl_map _ (acc, []) = (acc, [])
  | foldl_map f (acc, x :: xs) =
    let val (acc', y) = f (acc, x)
        val (acc'', ys) = foldl_map f (acc', xs)
    in (acc'', y :: ys) end

(* separate s [x1, x2, ..., xn] ===> [x1, s, x2, s, ..., s, xn] *)
fun separate s (x :: (xs as _ :: _)) = x :: s :: separate s xs
  | separate _ xs = xs

val filter = List.filter

fun get_first f l =
    case l of
      [] => NONE
    | h::t => (case f h of NONE => get_first f t | some => some)

fun partition P alist =
   itlist (fn x => fn (L,R) => if P x then (x::L, R) else (L, x::R))
          alist ([],[]);

fun zip [] [] = []
  | zip (a::b) (c::d) = (a,c)::zip b d
  | zip _ _ = raise ERR "zip" "different length lists"

val unzip = ListPair.unzip

fun combine(l1,l2) = zip l1 l2
val split = unzip

fun mapfilter f list =
  itlist(fn i => fn L => (f i::L)
                handle Interrupt => raise Interrupt
                     | otherwise => L)
     list [];

val flatten = List.concat

fun front_last l =
  let fun fl _ [] = raise ERR "front_last" "empty list"
        | fl acc [x]    = (List.rev acc,x)
        | fl acc (h::t) = fl (h::acc) t
  in fl [] l
  end;

fun butlast l =
  fst (front_last l) handle HOL_ERR _ => raise ERR "butlast" "empty list";

fun last []     = raise ERR "last" "empty list"
  | last [x]    = x
  | last (_::t) = last t

fun pluck P =
 let fun pl _ [] = raise ERR "pluck" "predicate not satisfied"
       | pl A (h::t) = if P h then (h, List.revAppend(A,t)) else pl (h::A) t
 in pl []
 end;

fun trypluck f =
 let fun try acc [] = raise ERR "trypluck" "no successful fn. application"
       | try acc (h::t) =
          case total f h
           of NONE => try (h::acc) t
            | SOME v => (v,List.revAppend(acc,t))
 in try []
 end

fun trypluck' f list = let
  fun recurse acc l =
      case l of
        [] => (NONE, list)
      | h::t => (case f h of
                   NONE => recurse (h::acc) t
                 | SOME v => (SOME v, List.revAppend(acc,t)))
in
  recurse [] list
end

fun funpow n f x =
 let fun iter (0,res) = res
       | iter (n,res) = iter (n-1, f res)
 in if n<0 then x else iter(n,x)
 end;

fun repeat f =
 let exception LAST of 'a
     fun loop x =
       let val y = (f x handle
                        Interrupt => raise Interrupt
                      | otherwise => raise (LAST x))
       in loop y
       end
  in fn x => loop x handle (LAST y) => y
  end;

fun enumerate i [] = []
  | enumerate i (h::t) = (i,h)::enumerate (i+1) t

fun upto b t =
  let fun up i A = if i>t then A else up (i+1) (i::A)
  in List.rev (up b [])
  end;

fun appi f lst = let
  fun recurse n lst =
      case lst of
        [] => ()
      | h :: t => (f n h; recurse (n + 1) t)
in
  recurse 0 lst
end

fun mapi f lst = let
  fun recurse n acc lst =
      case lst of
        [] => acc
      | h :: t => recurse (n + 1) (f n h :: acc) t
in
  List.rev (recurse 0 [] lst)
end

fun mapshape [] _ _ =  []
  | mapshape (n::nums) (f::funcs) all_args =
     let val (fargs,rst) = split_after n all_args
     in f fargs :: mapshape nums funcs rst
     end
  | mapshape _ _ _ = raise ERR "mapshape" "irregular lists";

type 'a cmp = 'a * 'a -> order

fun flip_order LESS = GREATER
  | flip_order EQUAL = EQUAL
  | flip_order GREATER = LESS
fun flip_cmp cmp = flip_order o cmp

fun bool_compare (true, true) = EQUAL
  | bool_compare (true, false) = GREATER
  | bool_compare (false, true) = LESS
  | bool_compare (false, false) = EQUAL

fun list_compare cfn =
 let fun comp ([],[]) = EQUAL
       | comp ([], _) = LESS
       | comp (_, []) = GREATER
       | comp (h1::t1, h2::t2) =
          case cfn (h1,h2) of EQUAL => comp (t1,t2) | x => x
  in comp end;

fun pair_compare (acmp, bcmp) ((a1, b1), (a2, b2)) =
    case acmp(a1, a2) of
      EQUAL => bcmp(b1, b2)
    | x => x

fun measure_cmp f (x,y) = Int.compare(f x, f y)
fun inv_img_cmp f c (x,y) = c (f x, f y)

(* streamlined combination of inv_img_cmp and pair_compare *)
fun lex_cmp (c1,c2) (f1,f2) (x1,x2) =
  case c1(f1 x1, f1 x2) of
    EQUAL => c2(f2 x1, f2 x2)
  | x => x

(*---------------------------------------------------------------------------*
 * For loops                                                                 *
 *---------------------------------------------------------------------------*)

fun for base top f =
 let fun For i = if i>top then [] else f i::For(i+1) in For base end;

fun for_se base top f =
 let fun For i = if i>top then () else (f i; For(i+1)) in For base end;

(*---------------------------------------------------------------------------*
 * Assoc lists.                                                              *
 *---------------------------------------------------------------------------*)

fun assoc item =
  let fun assc ((key,ob)::rst) = if item=key then ob else assc rst
        | assc [] = raise ERR "assoc" "not found"
  in assc
  end

fun rev_assoc item =
  let fun assc ((ob,key)::rst) = if item=key then ob else assc rst
        | assc [] = raise ERR "assoc" "not found"
  in assc
  end

fun assoc1 item =
  let fun assc ((e as (key,_))::rst) = if item=key then SOME e else assc rst
        | assc [] = NONE
  in assc
  end;

fun assoc2 item =
  let fun assc((e as (_,key))::rst) = if item=key then SOME e else assc rst
        | assc [] = NONE
  in assc
  end;

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


(*---------------------------------------------------------------------------*)
(* Topologically sort a list wrt partial order R.                            *)
(*---------------------------------------------------------------------------*)

fun topsort R = let
  fun pred_of y x = R x y
  fun a1 l1 l2 = l1 @ l2
  fun a2 l1 l2 = foldl (op::) l2 l1
  fun deps [] _ acc = acc
    | deps (h::t) front (nodeps,rst) = let
        val pred_of_h = pred_of h
        val hdep = exists pred_of_h t orelse
                   exists pred_of_h front
        val acc = if hdep then (nodeps,h::rst)
                          else (h::nodeps,rst)
      in deps t (h::front) acc end
  fun loop _ [] = []
    | loop (a1,a2) l =
        case (deps l [] ([],[])) of
          ([],_) => raise ERR "topsort" "cyclic dependency"
        | (nodeps,rst) => a1 nodeps (loop (a2,a1) rst)
in loop (a2,a1) end

(* for the following two implementations,
   each node appears before all its dependencies
   in the returned list *)

(* O(n*log(n)) time version
   deps = map from nodes to adjacency lists *)
fun dict_topsort deps = let
  open Redblackmap
  val deps = transform (fn ls => ref (SOME ls)) deps
  fun visit (n,ls) =
  let val r = find (deps,n) in
    case !r of
      NONE => ls
    | SOME dl => let
        val _ = r := NONE
        val ls = List.foldl visit ls dl
      in n::ls end
  end
  fun v (n,_,ls) = visit (n,ls)
in
  foldl v [] deps
end

(* linear time version
   only works when nodes are integers 0 up to some n
   deps = vector of adjacency lists *)
fun vector_topsort deps = let
  open Array
  val n = Vector.length deps
  val a = tabulate (n, SOME o (curry Vector.sub deps))
  fun visit (n,ls) =
    case sub (a,n) of
      NONE => ls
    | SOME dl => let
        val _ = update (a,n,NONE)
        val ls = List.foldl visit ls dl
      in n::ls end
  fun v (0,ls) = ls
    | v (n,ls) = v(n-1,visit(n-1,ls))
in v(n,[]) end

(*---------------------------------------------------------------------------*
 * Substitutions.                                                            *
 *---------------------------------------------------------------------------*)

type ('a,'b) subst = {redex:'a, residue:'b} list

fun subst_assoc test =
 let fun assc [] = NONE
       | assc ({redex,residue}::rst) =
          if test redex then SOME(residue) else assc rst
   in assc
   end;

infix 5 |->
fun (r1 |-> r2) = {redex=r1, residue=r2};


(*---------------------------------------------------------------------------*
 * Sets as lists                                                             *
 *---------------------------------------------------------------------------*)

fun mem i = List.exists (equal i)

fun insert i L = if mem i L then L else i::L

fun mk_set [] = []
  | mk_set (a::rst) = insert a (mk_set rst)

fun union [] S = S
  | union S [] = S
  | union (a::rst) S2 = union rst (insert a S2)

(* Union of a family of sets *)
fun U set_o_sets = itlist union set_o_sets []

(* All the elements in the first set that are not also in the second set. *)
fun set_diff a b = filter (not o C mem b) a
val subtract = set_diff

fun intersect [] _ = []
  | intersect _ [] = []
  | intersect S1 S2 = mk_set(filter (C mem S2) S1)

fun null_intersection _  [] = true
  | null_intersection [] _ = true
  | null_intersection (a::rst) S =
      if mem a S then false else null_intersection rst S

fun set_eq S1 S2 = (set_diff S1 S2 = []) andalso (set_diff S2 S1 = []);

(*---------------------------------------------------------------------------*
 * Opaque type set operations                                                *
 *---------------------------------------------------------------------------*)

fun op_mem eq_func i = List.exists (eq_func i)

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
   in mk_set(filter in_b a)
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
  partial (ERR "string_to_int" "not convertable")
          Int.fromString

val saying = ref true;
fun say s = if !saying then TextIO.print s else ();


(*---------------------------------------------------------------------------
   quote puts double quotes around a string. mlquote does this as well,
   but also quotes all of the characters in the string so that the
   resulting string could be printed out in a way that would make it a
   valid ML lexeme  (e.g., newlines turn into \n)
 ---------------------------------------------------------------------------*)

fun mlquote s = String.concat ["\"",String.toString s,"\""]
fun quote s = String.concat ["\"",s,"\""]

val is_substring = String.isSubstring

fun prime s = s^"'";

fun unprime s =
  let
    val n = size s - 1
  in
    if 0 <= n andalso String.sub (s,n) = #"'" then String.substring (s,0,n)
    else raise ERR "unprime" "string doesn't end with a prime"
  end;

val commafy = separate ", "

fun words2 sep string =
    snd (itlist (fn ch => fn (chs,tokl) =>
          if ch=sep
          then if (null chs) then ([],tokl)
		else ([], (Portable.implode chs :: tokl))
          else (ch::chs, tokl))
        (sep::Portable.explode string)
        ([],[]));

fun unprefix pfx s =
    if String.isPrefix pfx s then String.extract(s, size pfx, NONE)
    else raise ERR "unprefix" "1st argument is not a prefix of 2nd argument"


fun str_all P s = let
  fun recurse n = n < 0 orelse P (String.sub(s,n)) andalso recurse (n - 1)
in
  recurse (size s - 1)
end

(*---------------------------------------------------------------------------*
 * A hash function used for various tasks in the system. It works fairly     *
 * well for our applications, but is not industrial strength. The size       *
 * argument should be a prime. The function then takes a string and          *
 * a pair (i,A) and returns a number < size. "i" is the index in the         *
 * string to start hashing from, and A is an accumulator.  In simple         *
 * cases i=0 and A=0.                                                        *
 *---------------------------------------------------------------------------*)

local open Char String
in
fun hash size =
 fn s =>
  let fun hsh(i,A) = hsh(i+1, (A*4 + ord(sub(s,i))) mod size)
                     handle Subscript => A
  in hsh end
end;

(*---------------------------------------------------------------------------*
 * Timing                                                                    *
 *---------------------------------------------------------------------------*)

fun start_time () = Timer.startCPUTimer()

fun end_time timer =
  let val {sys,usr} = Timer.checkCPUTimer timer
      val gc = Timer.checkGCTime timer
  in
     TextIO.output(TextIO.stdOut,
          "runtime: "^Time.toString usr ^ "s,\
      \    gctime: "^Time.toString gc ^ "s, \
      \    systime: "^Time.toString sys ^"s.\n");
     TextIO.flushOut TextIO.stdOut
  end

fun time f x =
  let val timer = start_time()
      val y = f x handle e => (end_time timer; raise e)
  in
     end_time timer;  y
  end

fun start_real_time () = Timer.startRealTimer()

fun end_real_time timer =
  (TextIO.output(TextIO.stdOut,
     "realtime: " ^ Time.toString (Timer.checkRealTimer timer) ^ "s\n");
   TextIO.flushOut TextIO.stdOut)

fun real_time f x =
  let val timer = start_real_time()
      val y = f x handle e => (end_real_time timer; raise e)
  in
     end_real_time timer; y
  end

(*---------------------------------------------------------------------------*
 * Invoking a function with a flag temporarily assigned to the given value.  *
 *---------------------------------------------------------------------------*)

fun with_flag (flag,b) f x =
  let val fval = !flag
      val () = flag := b
      val res = f x handle e => (flag := fval; raise e)
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


(*---------------------------------------------------------------------------
    A type that can be used for sharing, and some functions for lifting
    to various type operators (just lists and pairs currently).
 ---------------------------------------------------------------------------*)

datatype 'a delta = SAME | DIFF of 'a;

fun delta_apply f x = case f x of SAME => x | DIFF y => y;

fun delta_map f =
 let fun map [] = SAME
       | map (h::t) =
          case (f h, map t)
           of (SAME, SAME)       => SAME
            | (SAME, DIFF t')    => DIFF(h  :: t')
            | (DIFF h', SAME)    => DIFF(h' :: t)
            | (DIFF h', DIFF t') => DIFF(h' :: t')
 in map end;

fun delta_pair f g (x,y) =
  case (f x, g y)
   of (SAME, SAME)       => SAME
    | (SAME, DIFF y')    => DIFF (x, y')
    | (DIFF x', SAME)    => DIFF (x', y)
    | (DIFF x', DIFF y') => DIFF (x', y');


(*---------------------------------------------------------------------------
    A function that strips leading (nested) comments and whitespace
    from a string.
 ---------------------------------------------------------------------------*)

fun deinitcomment0 ss n =
    case Substring.getc ss of
        NONE => ss
      | SOME (c,ss') =>
        if Char.isSpace c then
            deinitcomment0 ss' n
        else if c = #"(" then
            case Substring.getc ss' of
                NONE => ss
              | SOME (c,ss'') =>
                if c = #"*" then
                    deinitcomment0 ss'' (n+1)
                else if n = 0 then
                    ss
                else
                    deinitcomment0 ss'' n
        else if n > 0 andalso c = #"*" then
            case Substring.getc ss' of
                NONE => ss
              | SOME (c,ss'') =>
                if c = #")" then
                    deinitcomment0 ss'' (n-1)
                else
                    deinitcomment0 ss'' n
        else if n = 0 then
            ss
        else
            deinitcomment0 ss' n

fun deinitcommentss ss =                   deinitcomment0               ss  0
fun deinitcomment   s  = Substring.string (deinitcomment0 (Substring.full s) 0)

(*---------------------------------------------------------------------------*)
(* Yet another variant of the sum type, used for the failure monad           *)
(*---------------------------------------------------------------------------*)

datatype ('a,'b) verdict = PASS of 'a | FAIL of 'b;

fun verdict f c x = PASS (f x) handle e => FAIL (c x,e);

fun ?>(PASS x,f) = f x
  | ?>(FAIL y,f) = FAIL y;

end (* Lib *)
