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

val ERR = mk_HOL_ERR "Lib"

open Portable;
datatype frag = datatype HOLPP.frag

(*---------------------------------------------------------------------------*
 * A version of try that coerces non-HOL_ERR exceptions to be HOL_ERRs.      *
 * To be used with tacticals and the like that get driven by HOL_ERR         *
 * exceptions.                                                               *
 *---------------------------------------------------------------------------*)

local
   val default_exn = ERR "trye" "original exn. not a HOL_ERR"
in
   fun trye f x =
      f x handle e as HOL_ERR _ => raise e
               | Interrupt => raise Interrupt
               | _ => raise default_exn
end

(*---------------------------------------------------------------------------*
 * For interactive use: "Raise" prints out the exception.                    *
 *---------------------------------------------------------------------------*)

fun try f x = f x handle e => Feedback.Raise e

fun assert P x = assert_exn P x (ERR "assert" "predicate not true")

(*---------------------------------------------------------------------------*
 *        Common list operations                                             *
 *---------------------------------------------------------------------------*)

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
   let
      fun F [] = raise ERR "tryfind" "all applications failed"
        | F (h :: t) = f h handle Interrupt => raise Interrupt | _ => F t
   in
      F
   end

(* Counting starts from 1 *)

fun el n l =
   if n < 1
      then raise ERR "el" "index too small"
   else let
           fun elem (_, []) = raise ERR "el" "index too large"
             | elem (1, h :: _) = h
             | elem (n, _ :: rst) = elem (n - 1, rst)
        in
           elem (n, l)
        end

(* this generates [0, ..., n - 1] just like `pred_set$count` *)
fun count n = List.tabulate(n, I);

fun index P l =
   let
      fun idx (i, []) = raise ERR "index" "no such element"
        | idx (i, y :: l) = if P y then i else idx (i + 1, l)
   in
      idx (0, l)
   end

fun map2 f L1 L2 =
   let
      fun mp2 [] [] L = rev L
        | mp2 (a1 :: rst1) (a2 :: rst2) L = mp2 rst1 rst2 (f a1 a2 :: L)
        | mp2 _ _ _ = raise ERR "map2" "different length lists"
   in
      mp2 L1 L2 []
   end

fun all2 P =
   let
      fun every2 [] [] = true
        | every2 (a1 :: rst1) (a2 :: rst2) = P a1 a2 andalso every2 rst1 rst2
        | every2  _ _ = raise ERR "all2" "different length lists"
   in
      every2
   end

fun first P =
   let
      fun oneth (a :: rst) = if P a then a else oneth rst
        | oneth [] = raise ERR "first" "unsatisfied predicate"
   in
      oneth
   end

fun split_after n alist =
   if n >= 0
      then let
              fun spa 0 (L, R) = (rev L, R)
                | spa n (L, a :: rst) = spa (n - 1) (a :: L, rst)
                | spa _ _ = raise ERR "split_after" "index too big"
           in
              spa n ([], alist)
           end
   else raise ERR "split_after" "negative index"

fun itlist2 f L1 L2 base_value =
   let
      fun itl ([], []) = base_value
        | itl (a :: rst1, b :: rst2) = f a b (itl (rst1, rst2))
        | itl _ = raise ERR "itlist2" "lists of different length"
   in
      itl (L1, L2)
   end

fun rev_itlist2 f L1 L2 =
  let
     fun rev_it2 ([], []) base = base
       | rev_it2 (a :: rst1, b :: rst2) base = rev_it2 (rst1, rst2) (f a b base)
       | rev_it2 _ _ = raise ERR"rev_itlist2" "lists of different length"
  in
     rev_it2 (L1, L2)
  end

fun end_itlist f =
   let
      fun endit [] = raise ERR "end_itlist" "list too short"
        | endit [x] = x
        | endit (h :: t) = f h (endit t)
   in
      endit
   end

fun get_first f l =
   case l of
      [] => NONE
    | h :: t => (case f h of NONE => get_first f t | some => some)

fun zip [] [] = []
  | zip (a :: b) (c :: d) = (a, c) :: zip b d
  | zip _ _ = raise ERR "zip" "different length lists"

fun combine (l1, l2) = zip l1 l2

fun butlast l =
   fst (front_last l) handle HOL_ERR _ => raise ERR "butlast" "empty list"

fun last [] = raise ERR "last" "empty list"
  | last [x] = x
  | last (_ :: t) = last t

fun pluck P =
   let
      fun pl _ [] = raise ERR "pluck" "predicate not satisfied"
        | pl A (h :: t) =
            if P h then (h, List.revAppend (A, t)) else pl (h :: A) t
   in
      pl []
   end

fun trypluck f =
   let
      fun try acc [] = raise ERR "trypluck" "no successful fn. application"
        | try acc (h :: t) =
             case total f h of
                NONE => try (h :: acc) t
              | SOME v => (v, List.revAppend (acc, t))
   in
      try []
   end

(* apnth : ('a -> 'a) -> int -> 'a list -> 'a list
  apply a function to the nth member of a list *)
fun apnth f 0 (y :: ys) = f y :: ys
  | apnth f n (y :: ys) = y :: apnth f (n-1) ys
  | apnth f n [] = raise ERR "apnth" "list too short (or -ve index)"

fun mapshape [] _ _ =  []
  | mapshape (n :: nums) (f :: funcs) all_args =
     let
        val (fargs, rst) = split_after n all_args
     in
        f fargs :: mapshape nums funcs rst
     end
  | mapshape _ _ _ = raise ERR "mapshape" "irregular lists"

(*---------------------------------------------------------------------------*
 * More list operations (from HOL-Light's lib.sml)                           *
 *---------------------------------------------------------------------------*)

fun forall p [] = true
  | forall p (h::t) = p(h) andalso forall p t

fun forall2 p [] [] = true
  | forall2 p (h1::t1) (h2::t2) = p h1 h2 andalso forall2 p t1 t2
  | forall2 _ _ _ = false

(* removing adjacent equal elements from list *)
fun uniq (x::y::xs) = if x = y then uniq (y::xs) else x::uniq (y::xs)
  | uniq xs = xs

(* convert list into set by eliminating duplicates *)
fun setify lte s = uniq (sort lte s)

(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

(* NOTE: the returned list of "pairs" has no duplications but must be eqtype *)
fun allpairs (f :'a -> 'b -> ''c) (l1 :'a list) (l2 :'b list) :''c list =
    itlist (union o C map l2 o f) l1 [];

(* NOTE: eqtype is not required, while the returned list of "pairs" may have
   duplications. *)
fun allpairs' (f :'a -> 'b -> 'c) (h1::t1) l2 =
    itlist (fn x => fn a => f h1 x :: a) l2 (allpairs' f t1 l2)
  | allpairs' f [] l2 = []

(* NOTE: eqtype is not required, no duplications, but an explicit equal test
   function is required *)
fun op_allpairs eq f l1 l2 =
    itlist ((op_union eq) o C map l2 o f) l1 [];

(*---------------------------------------------------------------------------*
 * Assoc lists.                                                              *
 *---------------------------------------------------------------------------*)

fun assoc item =
   let
      fun assc ((key, ob) :: rst) = if item = key then ob else assc rst
        | assc [] = raise ERR "assoc" "not found"
   in
      assc
   end

fun rev_assoc item =
   let
      fun assc ((ob, key) :: rst) = if item = key then ob else assc rst
        | assc [] = raise ERR "assoc" "not found"
   in
      assc
   end

fun op_assoc eq_func k l =
  case l of
      [] => raise ERR "op_assoc" "not found"
    | (key,ob) :: rst => if eq_func k key then ob else op_assoc eq_func k rst

fun op_rev_assoc eq_func k l =
  case l of
      [] => raise ERR "op_rev_assoc" "not found"
    | (ob,key) :: rest => if eq_func k key then ob
                          else op_rev_assoc eq_func k rest

(*---------------------------------------------------------------------------*)
(* Topologically sort a list wrt partial order R.                            *)
(*---------------------------------------------------------------------------*)

fun topsort R =
   let
      fun pred_of y x = R x y
      fun a1 l1 l2 = l1 @ l2
      fun a2 l1 l2 = foldl (op ::) l2 l1
      fun deps [] _ acc = acc
        | deps (h :: t) front (nodeps, rst) =
            let
               val pred_of_h = pred_of h
               val hdep = exists pred_of_h t orelse exists pred_of_h front
               val acc = if hdep then (nodeps, h :: rst) else (h :: nodeps, rst)
            in
               deps t (h :: front) acc
            end
      fun loop _ [] = []
        | loop (a1, a2) l =
            case (deps l [] ([], [])) of
              ([], _) => raise ERR "topsort" "cyclic dependency"
            | (nodeps, rst) => a1 nodeps (loop (a2, a1) rst)
   in
      loop (a2, a1)
   end

(* for the following two implementations,
   each node appears before all its dependencies
   in the returned list *)

(* O(n*log(n)) time version
   deps = map from nodes to adjacency lists *)

local open HOLdict in
type ('a, 'b) dict = ('a, 'b) dict

fun dict_topsort deps =
   let
      val deps = transform (fn ls => ref (SOME ls)) deps
      fun visit (n, ls) =
         let
            val r = find (deps, n)
         in
            case !r of
               NONE => ls
             | SOME dl => let
                             val _ = r := NONE
                             val ls = List.foldl visit ls dl
                          in
                             n :: ls
                          end
         end
      fun v (n, _, ls) = visit (n, ls)
   in
      foldl v [] deps
   end
end (* local *)

(*---------------------------------------------------------------------------*
 * Strings.                                                                  *
 *---------------------------------------------------------------------------*)

val string_to_int =
   partial (ERR "string_to_int" "not convertable") Int.fromString

val saying = ref true

fun say s = if !saying then !Feedback.MESG_outstream s else ()

fun unprime s =
   let
     val n = size s - 1
   in
      if 0 <= n andalso String.sub (s, n) = #"'"
         then String.substring (s, 0, n)
      else raise ERR "unprime" "string doesn't end with a prime"
   end

fun extract_pc s =
    let
      (* c = # of primes seen;
         i = current index into string, terminate on -1
         -- does right thing on UTF8 encoded codepoints
       *)
      fun recurse c i =
          if i < 0 then ("", c)
          else if String.sub(s,i) = #"'" then recurse (c + 1) (i - 1)
          else (String.substring(s,0,i+1), c)
    in
      recurse 0 (String.size s - 1)
    end


fun unprefix pfx s =
   if String.isPrefix pfx s
      then String.extract (s, size pfx, NONE)
   else raise ERR "unprefix" "1st argument is not a prefix of 2nd argument"

fun ppstring pf x = HOLPP.pp_to_string (!Globals.linewidth) pf x

fun delete_trailing_wspace s =
  let
    val toks = String.fields (equal #"\n") s
    fun do1 i s =
      if i < 0 then ""
      else if Char.isSpace (String.sub(s,i)) then do1 (i - 1) s
      else String.extract(s,0,SOME(i + 1))
    fun remove_rptd_nls i cnt s =
      if i < 0 then if cnt > 0 then "\n" else ""
      else if String.sub(s,i) = #"\n" then
        remove_rptd_nls (i - 1) (cnt + 1) s
      else String.extract(s,0,SOME(i + 1 + (if cnt > 0 then 1 else 0)))
    val s1 = String.concatWith "\n" (map (fn s => do1 (size s - 1) s) toks)
  in
    remove_rptd_nls (size s1 - 1) 0 s1
  end

(*---------------------------------------------------------------------------*
 * Timing                                                                    *
 *---------------------------------------------------------------------------*)

local
   val second = Time.fromReal 1.0
   val minute = Time.fromReal 60.0
   val year0 = Date.year (Date.fromTimeUniv Time.zeroTime)
   fun to_str i u = if i = 0 then "" else Int.toString i ^ u
in
   fun time_to_string t =
      if Time.< (t, second)
         then Time.fmt 5 t ^ "s"
      else if Time.< (t, minute)
         then Time.fmt 1 t ^ "s"
      else let
              val d = Date.fromTimeUniv t
              val years = Date.year d - year0
              val days = Date.yearDay d
              val hours = Date.hour d
              val minutes = Date.minute d
           in
              if years + days + hours = 0 andalso minutes < 10 then
                 to_str minutes "m" ^ Date.fmt "%Ss" d
              else to_str years "y" ^ to_str days "d" ^ to_str hours "h" ^
                   Date.fmt "%Mm%Ss" d
           end
end

fun start_time () = Timer.startCPUTimer ()

fun end_time timer =
   let
      val {sys, usr} = Timer.checkCPUTimer timer
      val gc = Timer.checkGCTime timer
   in
      say ("runtime: " ^ time_to_string usr ^ ",\
       \    gctime: " ^ time_to_string gc ^ ", \
       \    systime: " ^ time_to_string sys ^ ".\n")
   end

fun time f x =
   let
      val timer = start_time ()
      val y = f x handle e => (end_time timer; raise e)
   in
      end_time timer; y
   end

fun start_real_time () = Timer.startRealTimer ()

fun end_real_time timer =
  say ("realtime: " ^ Time.toString (Timer.checkRealTimer timer) ^ "s\n")

fun real_time f x =
   let
      val timer = start_real_time ()
      val y = f x handle e => (end_real_time timer; raise e)
   in
      end_real_time timer; y
   end

(* set helpers/abbreviations *)
type 'a set = 'a HOLset.set
fun op Un p = HOLset.union p
fun op Isct p = HOLset.intersection p
fun op -- p = HOLset.difference p
fun op IN (e,s) = HOLset.member(s,e)

(* more equality function functions *)
fun subst_eq aeq beq = list_eq (redres_eq aeq beq)

end (* Lib *)
