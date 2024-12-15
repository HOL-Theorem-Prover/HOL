(* ===================================================================== *)
(* FILE          : Portable.sml                                          *)
(* DESCRIPTION   : Structure for SML System dependent functions.         *)
(* AUTHOR        : Ken Larsen, University of Cambridge (or DTU)          *)
(*                 based on code by                                      *)
(*                 Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 19 September, 1997                                    *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)
(* Copyright 1997 by University of Cambridge *)

(* Share and Enjoy *)

structure Portable :> Portable =
struct

structure Process = OS.Process
structure FileSys = OS.FileSys

exception Div = General.Div
exception Mod = General.Div

fun assert_exn P x e = if P x then x else raise e
fun with_exn f x e = f x handle Interrupt => raise Interrupt | _ => raise e
fun finally finish f x =
    let
      val result = Exn.capture f x
    in
      finish();
      Exn.release result
    end

val int_to_string = Int.toString

(*---------------------------------------------------------------------------*
 * Combinators                                                               *
 *---------------------------------------------------------------------------*)

fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y
infix 3 ##
fun (f ## g) (x, y) = (f x, g y)
fun apfst f (x, y) = (f x, y)
fun apsnd f (x, y) = (x, f y)
fun pair_map f (x, y) = (f x, f y)
infix |> ||> |>> ||->
fun x |> f = f x
fun (x,y) |>> f = (f x, y)
fun (x,y) ||> f = (x, f y)
fun (x,y) ||-> f = f x y
infixr $ ?
fun f $ x = f x
fun (b ? f) x = if b then f x else x
fun B2 f g x y = f (g x y)
fun C f x y = f y x
fun flip f (x,y) = f (y,x)
fun I x = x
fun K x y = x
fun S f g x = f x (g x)
fun W f x = f x x

(*---------------------------------------------------------------------------*
 * Curried versions of infixes.                                              *
 *---------------------------------------------------------------------------*)

fun append l1 l2 = l1 @ l2
fun equal x y = x = y
val strcat = curry (op ^)
fun cons a L = a :: L
fun pair x y = (x, y)

fun rpair x y = (y, x)
fun swap (x, y) = (y, x)
fun fst (x, _) = x
fun snd (_, y) = y

fun triple x y z = (x, y, z)
fun quadruple x1 x2 x3 x4 = (x1, x2, x3, x4)

(*---------------------------------------------------------------------------*
 * Success and failure. Interrupt has a special status in Standard ML.       *
 *---------------------------------------------------------------------------*)

fun can f x = (f x; true) handle Interrupt => raise Interrupt | _ => false

fun total f x = SOME (f x) handle Interrupt => raise Interrupt | _ => NONE

fun partial e f x = case f x of SOME y => y | NONE => raise e

fun these (SOME x) = x
  | these NONE = []

(* ----------------------------------------------------------------------
    Lists
   ---------------------------------------------------------------------- *)

fun list_of_singleton a = [a]
fun single a = [a]
fun the_single [x] = x
  | the_single _ = raise List.Empty;
fun singleton f x = the_single (f [x])

fun list_of_pair (a, b) = [a, b]
fun list_of_triple (a, b, c) = [a, b, c]
fun list_of_quadruple (a, b, c, d) = [a, b, c, d]

fun the_list NONE = []
  | the_list (SOME x) = [x]
fun the_default d NONE = d
  | the_default _ (SOME x) = x

val all = List.all
val exists = List.exists

fun first_opt f =
   let
      fun fo n [] = NONE
        | fo n (a :: rst) =
            let
               val vo = f n a handle Interrupt => raise Interrupt | _ => NONE
            in
               if isSome vo then vo else fo (n + 1) rst
            end
   in
      fo 0
   end

fun itlist f L base_value = List.foldr (uncurry f) base_value L
val foldr' = itlist

fun rev_itlist f L base_value = List.foldl (uncurry f) base_value L
val foldl' = rev_itlist

fun foldl_map _ (acc, []) = (acc, [])
  | foldl_map f (acc, x :: xs) =
      let
         val (acc', y) = f (acc, x)
         val (acc'', ys) = foldl_map f (acc', xs)
      in
         (acc'', y :: ys)
      end

fun foldl2' _ [] [] z = z
  | foldl2' f (x::xs) (y::ys) z = foldl2' f xs ys (f x y z)
  | foldl2' _ _ _ _ = raise ListPair.UnequalLengths
fun foldr2' _ [] [] z = z
  | foldr2' f (x::xs) (y::ys) z = f x y (foldr2' f xs ys z)
  | foldr2' _ _ _ _ = raise ListPair.UnequalLengths

fun zip3 ([], [], []) = []
  | zip3 (h1::t1, h2::t2, h3::t3) = (h1,h2,h3) :: zip3 (t1,t2,t3)
  | zip3 _ = raise ListPair.UnequalLengths

(* separate s [x1, x2, ..., xn] ===> [x1, s, x2, s, ..., s, xn] *)

fun separate s (x :: (xs as _ :: _)) = x :: s :: separate s xs
  | separate _ xs = xs

val filter = List.filter
fun filter_out P = filter (not o P)

val partition = List.partition

fun pull_prefix ps l =
  case ps of
      [] => l
    | p :: rest =>
      let
        val (s, l0) = List.partition p l
      in
        s @ pull_prefix rest l0
      end

val unzip = ListPair.unzip
val split = unzip

fun mapfilter f = List.mapPartial (total f)

val flatten = List.concat
fun front_last l =
  let
     fun fl _ [] = raise List.Empty
       | fl acc [x] = (List.rev acc, x)
       | fl acc (h :: t) = fl (h :: acc) t
  in
     fl [] l
  end



fun trypluck' f list =
   let
     fun recurse acc l =
        case l of
           [] => (NONE, list)
         | h :: t => (case f h of
                         NONE => recurse (h :: acc) t
                       | SOME v => (SOME v, List.revAppend (acc, t)))
   in
      recurse [] list
   end

fun plucki P xs =
    let fun recur A i l =
            case l of
                [] => NONE
              | h::t => if P h then SOME(h, i, List.revAppend(A,t))
                        else recur (h::A) (i + 1) t
    in
      recur [] 0 xs
    end

fun funpow n f x =
   let
      fun iter (0, res) = res
        | iter (n, res) = iter (n - 1, f res)
   in
      if n < 0 then x else iter (n, x)
   end

fun repeat f =
   let
      exception LAST of 'a
      fun loop x =
         let
            val y = (f x handle Interrupt => raise Interrupt
                              | otherwise => raise (LAST x))
         in
            loop y
         end
   in
      fn x => loop x handle (LAST y) => y
   end

fun enumerate i [] = []
  | enumerate i (h :: t) = (i, h) :: enumerate (i + 1) t

fun upto b t =
   let
      fun up i A = if i > t then A else up (i + 1) (i :: A)
   in
      List.rev (up b [])
   end

fun appi f =
   let
      fun recurse n lst =
         case lst of
            [] => ()
          | h :: t => (f n h; recurse (n + 1) t)
   in
      recurse 0
   end

fun mapi f lst =
   let
      fun recurse n acc lst =
         case lst of
            [] => acc
          | h :: t => recurse (n + 1) (f n h :: acc) t
   in
      List.rev (recurse 0 [] lst)
   end

fun assoc1 item =
   let
      fun assc ((e as (key, _)) :: rst) =
            if item = key then SOME e else assc rst
        | assc [] = NONE
   in
      assc
   end

fun assoc2 item =
   let
      fun assc ((e as (_, key)) :: rst) =
            if item = key then SOME e else assc rst
        | assc [] = NONE
   in
      assc
   end

type 'a cmp = 'a * 'a -> order

fun flip_order LESS = GREATER
  | flip_order EQUAL = EQUAL
  | flip_order GREATER = LESS

fun flip_cmp cmp = flip_order o cmp

fun bool_compare (true, true) = EQUAL
  | bool_compare (true, false) = GREATER
  | bool_compare (false, true) = LESS
  | bool_compare (false, false) = EQUAL

fun option_compare cmp optp =
  case optp of
      (NONE, NONE) => EQUAL
    | (NONE, SOME _) => LESS
    | (SOME _, NONE) => GREATER
    | (SOME x, SOME y) => cmp(x,y)

fun list_compare cfn =
   let
      fun comp ([], []) = EQUAL
        | comp ([], _) = LESS
        | comp (_, []) = GREATER
        | comp (h1 :: t1, h2 :: t2) =
            case cfn (h1, h2) of EQUAL => comp (t1, t2) | x => x
   in
      comp
   end

fun pair_compare (acmp, bcmp) ((a1, b1), (a2, b2)) =
   case acmp (a1, a2) of
      EQUAL => bcmp (b1, b2)
    | x => x

fun measure_cmp f (x, y) = Int.compare (f x, f y)
fun inv_img_cmp f c (x, y) = c (f x, f y)

(* streamlined combination of inv_img_cmp and pair_compare *)
fun lex_cmp (c1, c2) (f1, f2) (x1, x2) =
   case c1 (f1 x1, f1 x2) of
      EQUAL => c2 (f2 x1, f2 x2)
    | x => x

(*---------------------------------------------------------------------------*
 * For loops                                                                 *
 *---------------------------------------------------------------------------*)

fun for base top f =
   let fun For i = if i > top then [] else f i :: For (i + 1) in For base end

fun for_se base top f =
   let fun For i = if i > top then () else (f i; For (i + 1)) in For base end

(*---------------------------------------------------------------------------*
 * A naive merge sort.                                                       *
 *---------------------------------------------------------------------------*)

fun sort P =
   let
      fun merge [] a = a
        | merge a [] = a
        | merge (A as (a :: t1)) (B as (b :: t2)) =
             if P a b then a :: merge t1 B
                      else b :: merge A t2
      fun srt [] = []
        | srt [a] = a
        | srt (h1 :: h2 :: t) = srt (merge h1 h2 :: t)
   in
      srt o (map (fn x => [x]))
   end

val int_sort = sort (curry (op <= : int * int -> bool))

(* linear time version of topsort (in Lib)
   only works when nodes are integers 0 up to some n
   deps = vector of adjacency lists *)

fun vector_topsort deps =
   let
      open Array
      val n = Vector.length deps
      val a = tabulate (n, SOME o (curry Vector.sub deps))
      fun visit (n, ls) =
         case sub (a, n) of
            NONE => ls
          | SOME dl => let
                          val _ = update (a, n, NONE)
                          val ls = List.foldl visit ls dl
                       in
                          n :: ls
                       end
      fun v (0, ls) = ls
        | v (n, ls) = v (n - 1, visit (n - 1, ls))
   in
      v (n, [])
   end

(*---------------------------------------------------------------------------*
 * Substitutions.                                                            *
 *---------------------------------------------------------------------------*)

type ('a, 'b) subst = {redex: 'a, residue: 'b} list

fun subst_assoc test =
   let
      fun assc [] = NONE
        | assc ({redex, residue} :: rst) =
            if test redex then SOME residue else assc rst
   in
      assc
   end

infix 5 |->
fun (r1 |-> r2) = {redex = r1, residue = r2}

(*---------------------------------------------------------------------------*
 * Sets as lists                                                             *
 *---------------------------------------------------------------------------*)

fun mem i = List.exists (equal i)

fun insert i L = if mem i L then L else i :: L

fun mk_set [] = []
  | mk_set (a :: rst) = insert a (mk_set rst)

fun union [] S = S
  | union S [] = S
  | union (a :: rst) S2 = union rst (insert a S2)

(* Union of a family of sets *)

fun U set_o_sets = itlist union set_o_sets []

(* All the elements in the first set that are not also in the second set. *)

fun set_diff a b = filter (not o C mem b) a
val subtract = set_diff

fun intersect [] _ = []
  | intersect _ [] = []
  | intersect S1 S2 = mk_set (filter (C mem S2) S1)

fun null_intersection _ [] = true
  | null_intersection [] _ = true
  | null_intersection (a :: rst) S =
      not (mem a S) andalso null_intersection rst S

fun set_eq S1 S2 = set_diff S1 S2 = [] andalso set_diff S2 S1 = []

(*---------------------------------------------------------------------------*
 * Opaque type set operations                                                *
 *---------------------------------------------------------------------------*)

(* functions for lifting equality functions over standard type operators *)
type 'a eqf = 'a -> 'a -> bool
fun pair_eq eq1 eq2 (x1,y1) (x2,y2) = eq1 x1 x2 andalso eq2 y1 y2
fun fst_eq eq (x1,y1) (x2,y2) = eq x1 x2
fun option_eq eq NONE NONE = true
  | option_eq eq (SOME x) (SOME y) = eq x y
  | option_eq _ _ _ = false
fun inv_img_eq f (eq:'b eqf) a1 a2 = eq (f a1) (f a2)
fun list_eq eq l1 l2 = ListPair.allEq (fn (x,y) => eq x y) (l1, l2)
fun redres_eq eq1 eq2 {residue=res1,redex=red1} {residue=res2,redex=red2} =
  eq1 red1 red2 andalso eq2 res1 res2

fun op_assoc1 eq_func k alist =
  case alist of
      [] => NONE
    | (k',v) :: rest => if eq_func k k' then SOME v
                        else op_assoc1 eq_func k rest

fun op_mem eq_func i = List.exists (eq_func i)

fun op_insert eq_func =
   let
      val mem = op_mem eq_func
   in
      fn i => fn L => if (mem i L) then L else i :: L
   end

fun op_mk_set eqf =
   let
      val insert = op_insert eqf
      fun mkset [] = []
        | mkset (a :: rst) = insert a (mkset rst)
   in
      mkset
   end

fun op_union eq_func =
   let
      val mem = op_mem eq_func
      val insert = op_insert eq_func
      fun un [] [] = []
        | un a [] = a
        | un [] a = a
        | un (a :: b) c = un b (insert a c)
   in
      un
   end

(* Union of a family of sets *)

fun op_U eq_func set_o_sets = itlist (op_union eq_func) set_o_sets []

fun op_intersect eq_func a b =
   let
      val mem = op_mem eq_func
      val in_b = C mem b
      val mk_set = op_mk_set eq_func
   in
      mk_set (filter in_b a)
   end

(* All the elements in the first set that are not also in the second set. *)

fun op_set_diff eq_func S1 S2 =
   let
      val memb = op_mem eq_func
   in
      filter (fn x => not (memb x S2)) S1
   end

fun op_remove eq x list =
  if op_mem eq x list then
    filter (fn y => not (eq x y)) list
  else list

fun op_update eq x xs = cons x (op_remove eq x xs)

(*---------------------------------------------------------------------------
   quote puts double quotes around a string. mlquote does this as well,
   but also quotes all of the characters in the string so that the
   resulting string could be printed out in a way that would make it a
   valid ML lexeme  (e.g., newlines turn into \n)
 ---------------------------------------------------------------------------*)

fun mlquote s = String.concat ["\"", String.toString s, "\""]

fun quote s = String.concat ["\"", s, "\""]

val is_substring = String.isSubstring

fun prime s = s ^ "'"

val commafy = separate ", "

fun enclose ld rd s = ld ^ s ^ rd

val str_all = CharVector.all

(*---------------------------------------------------------------------------*
 * A hash function used for various tasks in the system. It works fairly     *
 * well for our applications, but is not industrial strength. The size       *
 * argument should be a prime. The function then takes a string and          *
 * a pair (i,A) and returns a number < size. "i" is the index in the         *
 * string to start hashing from, and A is an accumulator.  In simple         *
 * cases i=0 and A=0.                                                        *
 *---------------------------------------------------------------------------*)

local
   open Char String
in
   fun hash size =
      fn s =>
         let
            fun hsh (i, A) =
               hsh (i + 1, (A * 4 + ord (sub (s, i))) mod size)
               handle Subscript => A
         in
            hsh
         end
end

(*---------------------------------------------------------------------------
      Refs
 ---------------------------------------------------------------------------*)

fun inc r = (r := !r + 1)
fun dec r = (r := !r - 1)

(*---------------------------------------------------------------------------
   SML/NJ v.93 style string operations
 ---------------------------------------------------------------------------*)

fun ordof (string, place) = Char.ord (String.sub (string, place))
val implode = String.concat
val explode = map Char.toString o String.explode

fun words2 sep string =
   snd (itlist (fn ch => fn (chs, tokl) =>
                   if ch = sep
                      then if null chs
                              then ([], tokl)
                           else ([], implode chs :: tokl)
                   else (ch :: chs, tokl))
               (sep :: explode string) ([], []))

fun replace_string {from, to} =
  let
    val next = Substring.position from
    val drop = Substring.triml (String.size from)
    val to = Substring.full to
    fun f acc s =
      let
        val (prefix,s) = next s
        val acc = prefix::acc
      in
        if Substring.isEmpty s then
          Substring.concat(List.rev acc)
        else
          f (to::acc) (drop s)
      end
  in
    f [] o Substring.full
  end

val remove_wspace =
    String.translate (fn c => if Char.isSpace c then "" else str c)

(*---------------------------------------------------------------------------
    System
 ---------------------------------------------------------------------------*)

val getEnv   = Process.getEnv
val cd       = FileSys.chDir
val pwd      = FileSys.getDir
fun system s = if Process.isSuccess (Process.system s) then 0 else 1
val getArgs  = CommandLine.arguments
val argv     = getArgs
fun exit()   = Process.exit Process.success

(*---------------------------------------------------------------------------
    IO
 ---------------------------------------------------------------------------*)

exception Io of string;
type instream      = TextIO.instream
type outstream     = TextIO.outstream
val std_out        = TextIO.stdOut
val stdin          = TextIO.stdIn
fun open_in file   = HOLFileSys.openIn file
                     handle IO.Io{cause=SysErr(s,_),...} => raise (Io s)
                                   (* handle OS.SysErr (s,_) => raise Io s; *)
fun open_out file  = HOLFileSys.openOut file
                     handle IO.Io{cause=SysErr(s,_),...} => raise (Io s)
                                   (* handle OS.SysErr (s,_) => raise Io s; *)
val output         = TextIO.output
fun outputc strm s = output(strm,s)
val close_in       = TextIO.closeIn
val close_out      = TextIO.closeOut
val flush_out      = TextIO.flushOut
fun input_line is  = case TextIO.inputLine is of NONE => "" | SOME s => s
val end_of_stream  = TextIO.endOfStream

(*---------------------------------------------------------------------------*)
(* Yet another variant of the sum type, used for the failure monad           *)
(*---------------------------------------------------------------------------*)

datatype ('a, 'b) verdict = PASS of 'a | FAIL of 'b

fun verdict f c x = PASS (f x) handle e => FAIL (c x, e)

fun ?>(PASS x, f) = f x
  | ?>(FAIL y, f) = FAIL y

(*---------------------------------------------------------------------------
    Time
 ---------------------------------------------------------------------------*)

type time = Time.time

local
   open Time
in
   val timestamp: unit -> time = now
   val time_to_string: time -> string = toString
   fun dest_time t =
      let
         val r = toReal t
         val sec = Arbnum.floor (toReal t)
         val sec_million = Arbnum.* (sec, Arbnum.fromInt 1000000)
         val r_million = r * 1000000.0
         val usec = Arbnum.- (Arbnum.floor r_million, sec_million)
      in
         {sec = sec, usec = usec}
      end
   fun mk_time {sec, usec} =
      fromReal (Real.+ (Arbnum.toReal sec, Arbnum.toReal usec / 1000000.0))
   fun time_eq (t1:time) t2 = (t1 = t2)
   fun time_lt (t1:time) t2 = Time.<(t1,t2)
   fun time_max (t1,t2) = if time_lt t1 t2 then t2 else t1
   fun time_maxl l =
     case l of
         [] => Time.zeroTime
       | h::t => List.foldl time_max h t
   fun realtime f x =
     let
       val timer = Timer.startRealTimer()
       val result = verdict f (fn x => x) x
       val t = Timer.checkRealTimer timer
     in
       print ("clock time: " ^ Time.toString t ^ "s\n");
       case result of
           PASS y => y
         | FAIL (_, e) => raise e
     end
end

(*---------------------------------------------------------------------------*
 * Invoking a function with a flag temporarily assigned to the given value.  *
 *---------------------------------------------------------------------------*)

fun with_flag (flag, b) f x =
   let
      val fval = !flag
      fun doit () = (flag := b; f x)
      val res = Exn.capture doit ()
   in
      flag := fval; Exn.release res
   end

fun genwith_flag({get,set}, v) f x =
    let
      val old = get()
      val res = Exn.capture (fn () => (set v; f x)) ()
    in
      set old; Exn.release res
    end

(*---------------------------------------------------------------------------*
 * An abstract type of imperative streams.                                   *
 *---------------------------------------------------------------------------*)

abstype ('a, 'b) istream = STRM of {mutator: 'a -> 'a,
                                    project: 'a -> 'b,
                                    state: 'a ref,
                                    init: 'a}
with
   fun mk_istream f i g =
      STRM {mutator = f, project = g, state = ref i, init = i}
   fun next (strm as STRM{mutator, state, ...}) =
      (state := mutator (!state); strm)
   fun state (STRM {project, state, ...}) = project (!state)
   fun reset (strm as STRM {state, init, ...}) = (state := init; strm)
end

(*---------------------------------------------------------------------------
    A type that can be used for sharing, and some functions for lifting
    to various type operators (just lists and pairs currently).
 ---------------------------------------------------------------------------*)

datatype 'a delta = SAME | DIFF of 'a

fun delta_apply f x = case f x of SAME => x | DIFF y => y

fun delta_map f =
   let
      fun map [] = SAME
        | map (h :: t) =
            case (f h, map t) of
               (SAME, SAME) => SAME
             | (SAME, DIFF t') => DIFF (h  :: t')
             | (DIFF h', SAME) => DIFF (h' :: t)
             | (DIFF h', DIFF t') => DIFF (h' :: t')
   in
      map
   end

fun delta_pair f g (x, y) =
  case (f x, g y) of
     (SAME, SAME) => SAME
   | (SAME, DIFF y') => DIFF (x, y')
   | (DIFF x', SAME) => DIFF (x', y)
   | (DIFF x', DIFF y') => DIFF (x', y')

(*---------------------------------------------------------------------------
    A function that strips leading (nested) comments and whitespace
    from a string.
 ---------------------------------------------------------------------------*)

fun deinitcomment0 ss n =
   case Substring.getc ss of
      NONE => ss
    | SOME (c, ss') =>
        if Char.isSpace c
           then deinitcomment0 ss' n
        else if c = #"("
           then case Substring.getc ss' of
                   NONE => ss
                 | SOME (c, ss'') =>
                      if c = #"*"
                         then deinitcomment0 ss'' (n + 1)
                      else if n = 0
                         then ss
                      else deinitcomment0 ss'' n
        else if n > 0 andalso c = #"*"
           then case Substring.getc ss' of
                   NONE => ss
                 | SOME (c, ss'') =>
                      if c = #")"
                         then deinitcomment0 ss'' (n - 1)
                      else deinitcomment0 ss'' n
        else if n = 0
           then ss
        else deinitcomment0 ss' n

fun deinitcommentss ss = deinitcomment0 ss 0
fun deinitcomment s = Substring.string (deinitcomment0 (Substring.full s) 0)

(*---------------------------------------------------------------------------
    Pretty Printing
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Simple and heavily used.
 * pfun = item printing function
 * dfun = delimiter printing function
 * bfun = break printer function
 *---------------------------------------------------------------------------*)

fun with_ppstream ppstrm =
  let
    open OldPP
  in
    {add_string     = add_string ppstrm,
     add_break      = add_break ppstrm,
     begin_block    = begin_block ppstrm,
     end_block      = fn () => end_block ppstrm,
     add_newline    = fn () => add_newline ppstrm,
     clear_ppstream = fn () => clear_ppstream ppstrm,
     flush_ppstream = fn () => flush_ppstream ppstrm}
  end

(*---------------------------------------------------------------------------
      MoscowML returns lists of QUOTE'd strings when a quote is spread
      over more than one line. "norm_quote" concatenates all adjacent
      QUOTE elements in this list.
 ---------------------------------------------------------------------------*)

type 'a quotation = 'a HOLPP.quotation
open HOLPP HOLquotation

fun pprint f x = prettyPrint(TextIO.print, 72) (f x)

local
  fun strip_comments (d, a) s =
    if Substring.size s = 0
      then a
    else let
           val (l, r) = Substring.splitl (fn c => c <> #"(" andalso c <> #"*") s
           val a' = if 0 < d then a else a @ [l]
         in
           if Substring.isPrefix "(*#loc " r
             then strip_comments (d + 1, a @ [Substring.trimr 1 l])
                    (Substring.triml 7 r)
           else if Substring.isPrefix "(*" r
             then strip_comments (d + 1, a') (Substring.triml 2 r)
           else if Substring.isPrefix "*)" r
             then strip_comments (d - 1, a') (Substring.triml 2 r)
           else if Substring.size r = 0
             then a'
           else let
                  val (r1, r2) = Substring.splitAt (r, 1)
                in
                  strip_comments (d, if 0 < d then a' else a' @ [r1]) r2
                end
         end
  val finish = Substring.concat o strip_comments (0, []) o Substring.full o
               String.concat o List.rev
in
  fun quote_to_string (f : 'a -> string) =
    let
      fun quote_to_strings a =
        fn [] => finish a
         | QUOTE s :: r => quote_to_strings (s :: a) r
         | ANTIQUOTE s :: r => quote_to_strings (f s :: a) r
    in
      quote_to_strings []
    end
  val quote_to_string_list =
    String.tokens (fn c => c = #"\n") o quote_to_string (fn x => x)
end

(* suck in implementation specific stuff *)

open MLSYSPortable
structure HOLSusp = MLSYSPortable.HOLSusp

(* rebinding the exception seems to be necessary in Moscow ML 2.01 *)

exception Interrupt = MLSYSPortable.Interrupt

end (* Portable *)
