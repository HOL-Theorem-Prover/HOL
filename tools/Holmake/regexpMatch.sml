(*---------------------------------------------------------------------------*)
(* Brzozowski-style regexp compilation with extension to character classes   *)
(* and other improvements from a paper by Owens,Reppy, and Turon.            *)
(*---------------------------------------------------------------------------*)

structure regexpMatch :> regexpMatch =
struct

exception regexpErr of string * string

fun ERR s1 s2 = regexpErr(s1,s2)
fun pair x y = (x,y)
fun K x y = x

val debug = ref false

val print = fn s => if !debug then print s else ()

(*---------------------------------------------------------------------------*)
(* Regular expressions have character sets at the leaves                     *)
(*---------------------------------------------------------------------------*)

type charset = Char.char Binaryset.set;

val Empty_Charset = Binaryset.empty Char.compare;
val empty_cset = Empty_Charset
fun isEmpty_Charset cset = Binaryset.isEmpty cset;

(* ----------------------------------------------------------------------
    We use full range of 8-bit characters, but this can be changed.
   ---------------------------------------------------------------------- *)

val MAX_ORD = 255;  (* Char.maxOrd is 255 *)
val alphabet = List.tabulate(MAX_ORD + 1, Char.chr)
val ALPHABET_SIZE = MAX_ORD + 1;
val allchars = Binaryset.addList(Empty_Charset, alphabet);
val univ_cset = allchars

fun charset_compare(cset1,cset2) =
 let open Binaryset
     fun compare [] [] = EQUAL
       | compare [] _  = LESS
       | compare _ []  = GREATER
       | compare ((h1:char)::t1) (h2::t2) =
           if h1 < h2 then LESS else
           if h1 > h2 then GREATER
           else compare t1 t2
 in
    if Systeml.pointer_eq(cset1,cset2) then EQUAL
    else compare (listItems cset1) (listItems cset2)
 end;

(*---------------------------------------------------------------------------*)
(* The type of regular expressions                                           *)
(*---------------------------------------------------------------------------*)

datatype regexp
   = Epsilon
   | Symbs of charset
   | Not of regexp
   | Sum of regexp * regexp
   | And of regexp * regexp
   | Dot of regexp * regexp
   | Star of regexp;

val Empty_Regexp = Symbs Empty_Charset;

(*---------------------------------------------------------------------------*)
(* Total order on regexp.                                                     *)
(*---------------------------------------------------------------------------*)

fun regexp_compare (r1,r2) =
 if Systeml.pointer_eq(r1,r2) then EQUAL
 else
 case (r1,r2)
  of (Epsilon, Epsilon) => EQUAL
   | (Epsilon, _)       => LESS

   | (Symbs _, Epsilon) => GREATER
   | (Symbs a, Symbs b) => charset_compare(a,b)
   | (Symbs _, _)       => LESS

   | (Not _, Epsilon)   => GREATER
   | (Not _, Symbs _)   => GREATER
   | (Not r1, Not r2)   => regexp_compare(r1,r2)
   | (Not r1, _)        => LESS

   | (Sum _, Epsilon)    => GREATER
   | (Sum _, Symbs _)    => GREATER
   | (Sum _, Not _)      => GREATER
   | (Sum p1, Sum p2)     => pair_regexp_compare (p1,p2)
   | (Sum _, _)          => LESS

   | (And _, Epsilon)   => GREATER
   | (And _, Symbs _)   => GREATER
   | (And _, Not _)     => GREATER
   | (And _, Sum _)      => GREATER
   | (And p1, And p2)   => pair_regexp_compare (p1,p2)
   | (And _, _)         => LESS

   | (Dot _, Epsilon)   => GREATER
   | (Dot _, Symbs _)   => GREATER
   | (Dot _, Not _)     => GREATER
   | (Dot _, Sum _)      => GREATER
   | (Dot _, And _)     => GREATER
   | (Dot p1, Dot p2)   => pair_regexp_compare (p1,p2)
   | (Dot _, _)         => LESS

   | (Star _, Epsilon)  => GREATER
   | (Star _, Symbs _)  => GREATER
   | (Star _, Not _)    => GREATER
   | (Star _, Sum _)    => GREATER
   | (Star _, And _)    => GREATER
   | (Star _, Dot _)    => GREATER
   | (Star r1, Star r2) => regexp_compare (r1,r2)
and
 pair_regexp_compare ((r1,r2), (r3,r4)) =
    case regexp_compare (r1,r3)
     of EQUAL => regexp_compare (r2,r4)
      | other => other;

fun regexpEqual r1 r2 = (regexp_compare(r1,r2) = EQUAL);

(*---------------------------------------------------------------------------*)
(* Is Epsilon in the language of a regular expression?                       *)
(*---------------------------------------------------------------------------*)

fun hasEpsilon Epsilon      = true
  | hasEpsilon (Symbs _)    = false
  | hasEpsilon (Not r)      = not(hasEpsilon r)
  | hasEpsilon (Sum(r1,r2))  = hasEpsilon r1 orelse hasEpsilon r2
  | hasEpsilon (And(r1,r2)) = hasEpsilon r1 andalso hasEpsilon r2
  | hasEpsilon (Dot(r1,r2)) = hasEpsilon r1 andalso hasEpsilon r2
  | hasEpsilon (Star _)     = true;

(*---------------------------------------------------------------------------*)
(* Translation to DFA.                                                       *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Two regexps are equivalent if they have the same language. This is         *)
(* expensive to decide, however Brzozowski found that a weaker notion of     *)
(* equivalence sufficed in order to build DFAs from regexps.                  *)
(*---------------------------------------------------------------------------*)

fun normNot (Not(Not r)) = r
  | normNot other = other;

fun normStar (Star Epsilon) = Epsilon
  | normStar (r as Star(Symbs cset)) = if isEmpty_Charset cset then Epsilon else r
  | normStar (Star (r as Star _)) = r
  | normStar otherwise = otherwise;

fun normDot (Dot(Epsilon,r)) = r
  | normDot (Dot(r,Epsilon)) = r
  | normDot (r as Dot(r1 as Star a,Star b)) = if regexpEqual a b then r1 else r
  | normDot (r as Dot(Dot(r1,r2),r3)) =
    let fun linear (Dot(Dot(r1,r2),r3)) = Dot(r1,linear(Dot(r2,r3)))
          | linear x = x
    in linear r
    end
  | normDot (r as Dot(Symbs cset1,Symbs cset2)) =
     if isEmpty_Charset cset1 orelse isEmpty_Charset cset2
     then Empty_Regexp else r
  | normDot (r as Dot(Symbs cset,_)) = if isEmpty_Charset cset then Empty_Regexp else r
  | normDot (r as Dot(_,Symbs cset)) = if isEmpty_Charset cset then Empty_Regexp else r
  | normDot otherwise = otherwise;

fun normAnd (r as And(Symbs a,Symbs b)) = Symbs (Binaryset.intersection(a,b))
  | normAnd (r as And(Symbs cset,_)) = if isEmpty_Charset cset then Empty_Regexp else r
  | normAnd (r as And(_,Symbs cset)) = if isEmpty_Charset cset then Empty_Regexp else r
  | normAnd (And(And(r1,r2),r3)) = normAnd(And(r1,normAnd(And(r2,r3))))
  | normAnd (r as And(r1,s as And(r2,r3))) =
     (case regexp_compare(r1,r2)
       of EQUAL => s
        | LESS => r
        | GREATER => And(r2,normAnd(And(r1,r3))))
  | normAnd (r as And(r1,r2)) =
     (case regexp_compare(r1,r2)
       of EQUAL => r1
        | LESS => r
        | GREATER => And(r2,r1))
  | normAnd r = r;

fun normSum (Sum(Symbs a, Symbs b)) = Symbs(Binaryset.union(a,b))
  | normSum (t as Sum(Symbs a,r))   = if isEmpty_Charset a then r else t
  | normSum (t as Sum(r, Symbs a))  = if isEmpty_Charset a then r else t
  | normSum (Sum(Sum(r1,r2),r3)) = normSum(Sum(r1,normSum(Sum(r2,r3))))
  | normSum (r as Sum(r1,s as Sum(r2,r3))) =
     (case regexp_compare(r1,r2)
       of EQUAL => s
        | LESS => r
        | GREATER => Sum(r2,normSum(Sum(r1,r3))))
  | normSum (r as Sum(r1,r2)) =
     (case regexp_compare(r1,r2)
       of EQUAL => r1
        | LESS => r
        | GREATER => Sum(r2,r1))
  | normSum r = r;

fun norm (Not P)    = normNot(Not (norm P))
  | norm (Sum(P,Q))  = normSum (Sum  (norm P, norm Q))
  | norm (And(P,Q)) = normAnd(And (norm P, norm Q))
  | norm (Dot(P,Q)) = normDot(Dot (norm P, norm Q))
  | norm (Star P)   = normStar (Star (norm P))
  | norm r = r;

fun simpDeriv x Epsilon    = Empty_Regexp
  | simpDeriv x (Symbs cs) = if Binaryset.member(cs,x) then Epsilon else Empty_Regexp
  | simpDeriv x (Not P)    = normNot(Not (simpDeriv x P))
  | simpDeriv x (Sum(P,Q))  = normSum (Sum  (simpDeriv x P,simpDeriv x Q))
  | simpDeriv x (And(P,Q)) = normAnd(And (simpDeriv x P, simpDeriv x Q))
  | simpDeriv x (Dot(P,Q)) =
      let val pq = normDot(Dot (simpDeriv x P, Q))
      in if hasEpsilon P
           then normSum(Sum(pq,simpDeriv x Q))
           else pq
      end
  | simpDeriv x (Star P) = normDot (Dot(simpDeriv x P, normStar(Star P)));


(*---------------------------------------------------------------------------*)
(* Approximate character classes. A character class is a set of charsets.    *)
(*---------------------------------------------------------------------------*)

val empty_class = Binaryset.empty charset_compare;
fun classList chlist = Binaryset.addList(empty_class, chlist)
val allchar_class = classList [allchars];

fun cross [] l2 = []
  | cross (h::t) l2 = map (pair h) l2 @ cross t l2;

fun moodge class1 class2 =
 let open Binaryset
     val pairs = cross (listItems class1) (listItems class2)
 in
   List.foldl (fn ((p:char set * char set), acc) =>
                  add (acc,Binaryset.intersection p))
              empty_class
              pairs
 end;

fun approxClasses Epsilon = allchar_class
  | approxClasses (Symbs a) = classList [a, Binaryset.difference(allchars,a)]
  | approxClasses (Not r) = approxClasses r
  | approxClasses (Star r) = approxClasses r
  | approxClasses (Sum(r1,r2)) = moodge (approxClasses r1) (approxClasses r2)
  | approxClasses (And(r1,r2)) = moodge (approxClasses r1) (approxClasses r2)
  | approxClasses (Dot(r1,r2)) =
       if hasEpsilon r1
         then moodge (approxClasses r1) (approxClasses r2)
         else approxClasses r1;

val Qempty = Binaryset.empty regexp_compare
fun pair_compare (f1, f2) ((x1,y1), (x2,y2)) =
    case f1 (x1, x2) of
        EQUAL => f2 (y1, y2)
      | x => x

val deltaMap_key_compare = pair_compare (regexp_compare, charset_compare)
val deltaMap_initial =
      Binarymap.mkDict deltaMap_key_compare :(regexp*charset,regexp)Binarymap.dict
fun insert_deltaMap ((d,r), deltaMap) = Binarymap.insert(deltaMap,d,r);

fun pick class = Option.valOf(Binaryset.find (K true) class);

(*---------------------------------------------------------------------------*)
(* Map a regular expression to a DFA representation.                         *)
(*---------------------------------------------------------------------------*)

fun regexp_to_dfa r =
 let val counter = ref 0
     fun work [] (Q,deltaMap) = (Q,deltaMap)
       | work (r::t) (Q,deltaMap) =
          if Binaryset.member(Q,r)  (* state r already seen? *)
            then (print "re-encountering state.\n";
                  work t (Q,deltaMap))
          else let
            val _ = print ("computing outarcs for state :"^
                           Int.toString(!counter)^".\n")
            val _ = counter := !counter + 1
            val charclasses = List.filter (not o Binaryset.isEmpty)
                                          (Binaryset.listItems(approxClasses r))
            val _ = print ("Number of arcs: "^
                           Int.toString(List.length charclasses)^"\n")
            val outarcs =
                List.map (fn c => ((r,c),simpDeriv (pick c) r)) charclasses
            val targets = List.map #2 outarcs
            val deltaMap' = List.foldl insert_deltaMap deltaMap outarcs
            val Q' = Binaryset.add(Q,r)
          in
             work (targets@t) (Q',deltaMap')
          end
     val initialState = norm r
     val (Q,deltaMap) = work [initialState] (Qempty,deltaMap_initial)
     val finalStates = Binaryset.foldl (fn (q,acc) =>
               if hasEpsilon q then Binaryset.add(acc,q) else acc)
               Qempty Q
 in
   (Q,initialState,deltaMap,finalStates)
 end

fun dfa_to_arrays (Q,q0,deltaMap,F) =
 let val _ = print "Mapping to array representation.\n"
     val states = Binaryset.listItems Q
     val nstates = List.length states
     val Qmap = Vector.fromList states
     fun Qindex i = Vector.sub(Qmap,i)  (* int -> regexp *)
     val QindexInv = Vector.foldli(fn(i,r,m) => Binarymap.insert(m,r,i))
                       (Binarymap.mkDict regexp_compare) Qmap
     fun QindexInvFn r = Binarymap.find(QindexInv,r) (* regexp -> int *)
     fun row i =
      let val q = Qindex i
          val outarcs = Binarymap.foldl(fn((regexp,charset),regexp',arcs)
                         => if regexpEqual regexp q
                             then (charset,regexp')::arcs
                             else arcs) [] deltaMap
          fun flatarc (charset,regexp) =
                 List.map (fn c => (Char.ord(c),regexp))
                          (Binaryset.listItems charset)
          val flatarcs = List.concat (List.map flatarc outarcs)
          val sortarcs =
              Listsort.sort (fn ((a,b), (c,d)) => Int.compare(a,c)) flatarcs
          val sortarcs' = List.map (fn (i,q) => QindexInvFn q) sortarcs
          val _ = if List.length sortarcs' <> ALPHABET_SIZE
                   then raise ERR
                              "dfa_to_arrays"
                              "total partition elements differs from \
                              \size of alphabet"
                   else ()
      in
          Vector.fromList sortarcs'
      end
 in
   {delta = Vector.tabulate(nstates, row),
    start = QindexInvFn q0,
    final = Vector.tabulate(nstates, fn i => Binaryset.member(F,Qindex i))
   }
 end;

val regexp_to_dfa_arrays = dfa_to_arrays o regexp_to_dfa;

fun match r =
 let val {delta,start,final} = regexp_to_dfa_arrays r
     val _ = print (String.concat["DFA states: ",
                    Int.toString(Vector.length delta),".\n"])
     fun step (a,q) = Vector.sub(Vector.sub(delta,q), Char.ord a)
     fun exec ss = Substring.foldl step start ss
 in
   fn s => Vector.sub(final,exec (Substring.full s))
 end;

fun pred_to_set P =
    Binaryset.foldl (fn (c, acc) => if P c then Binaryset.add(acc, c) else acc)
                    empty_cset
                    allchars

fun fromList cs = Binaryset.addList (empty_cset, cs)

structure POSIX = struct
  val alnum_set = pred_to_set Char.isAlphaNum
  val alpha_set = pred_to_set Char.isAlpha
  val ascii_set = pred_to_set Char.isAscii
  val blank_set = fromList [#" ", #"\t"]
  val cntrl_set = pred_to_set Char.isCntrl
  val digit_set = pred_to_set Char.isDigit
  val graph_set = pred_to_set Char.isGraph
  val lower_set = pred_to_set Char.isLower
  val print_set = pred_to_set Char.isPrint
  val punct_set = pred_to_set Char.isPunct
  val space_set = pred_to_set Char.isSpace
  val upper_set = pred_to_set Char.isUpper
  val xdigit_set = pred_to_set Char.isHexDigit
  val word_set = Binaryset.add(alnum_set, #"_")

end

end
