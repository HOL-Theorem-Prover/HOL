(* Redblackset -- sets implemented by Okasaki-style Red-Black trees *)
(* Ken Friis Larsen <kfl@it.edu>                                    *)
structure Redblackset :>  Redblackset =
struct

  datatype 'item tree = LEAF
                      | RED   of 'item * 'item tree * 'item tree
                      | BLACK of 'item * 'item tree * 'item tree

  type 'item set  = ('item * 'item -> order) * 'item tree * int

  exception NotFound

  fun empty compare = (compare, LEAF, 0)

  fun numItems (_, _, n) = n

  fun singleton compare x = (compare, BLACK(x, LEAF, LEAF), 1)

  fun isEmpty (_, LEAF, _) = true
    | isEmpty _            = false

  fun member ((compare, tree, n), elm) =
      let fun memShared x left right =
              case compare(elm,x) of
                  EQUAL   => true
                | LESS    => mem left
                | GREATER => mem right
          and mem LEAF                    = false
            | mem (RED(x, left, right))   = memShared x left right
            | mem (BLACK(x, left, right)) = memShared x left right
      in  mem tree end

  fun retrieve (set, x) = if member(set, x) then x else raise NotFound

  fun peek (set, x) = if member(set, x) then SOME x else NONE

  fun lbalance z (RED(y,RED(x,a,b),c)) d =
      RED(y,BLACK(x,a,b),BLACK(z,c,d))
    | lbalance z (RED(x,a,RED(y,b,c))) d =
      RED(y,BLACK(x,a,b),BLACK(z,c,d))
    | lbalance x left right = BLACK(x, left, right)

  fun rbalance x a (RED(y,b,RED(z,c,d))) =
      RED(y,BLACK(x,a,b),BLACK(z,c,d))
    | rbalance x a (RED(z,RED(y,b,c),d)) =
      RED(y,BLACK(x,a,b),BLACK(z,c,d))
    | rbalance x left right = BLACK(x, left, right)


  local
    fun lbal x (l,inc) r = (lbalance x l r, inc)
    fun rbal x l (r,inc) = (rbalance x l r, inc)
    fun REDl(x,(l,inc),r) = (RED(x,l,r), inc)
    fun REDr(x,l,(r,inc)) = (RED(x,l,r), inc)
    fun insert compare elm = let
      fun ins LEAF = (RED(elm,LEAF,LEAF), 1)
        | ins (BLACK(x,left,right)) = let
          in
            case compare(elm, x) of
              LESS    => lbal x (ins left) right
            | GREATER => rbal x left (ins right)
            | EQUAL   => (BLACK(elm,left,right), 0)
          end
        | ins (RED(x,left,right)) = let
          in
            case compare(elm, x) of
              LESS    => REDl(x, (ins left), right)
            | GREATER => REDr(x, left, (ins right))
            | EQUAL   => (RED(elm,left,right), 0)
          end
    in
      ins
    end
  in

  fun add (set as (compare, tree, n), elm) = let
    val (nt, inc) = insert compare elm tree
  in
    ( compare
    , case nt of
        RED(e, l, r) => BLACK(e, l, r)
      | tree         => tree
    , n+inc)
  end

  fun addList (set, xs) = List.foldl (fn(x,set) => add(set, x)) set xs
  end

  fun fromList compare xs =
    addList (empty compare, xs)

  fun push LEAF stack = stack
    | push tree stack = tree :: stack

  fun pushNode left x right stack =
      left :: (BLACK(x, LEAF, LEAF) :: (push right stack))

  fun getMin []             some none = none
    | getMin (tree :: rest) some none =
      case tree of
          LEAF                  => getMin rest some none
        | RED  (x, LEAF, right) => some x (push right rest)
        | BLACK(x, LEAF, right) => some x (push right rest)
        | RED  (x, left, right) => getMin(pushNode left x right rest) some none
        | BLACK(x, left, right) => getMin(pushNode left x right rest) some none

  fun getMax []             some none = none
    | getMax (tree :: rest) some none =
      case tree of
          LEAF                  => getMax rest some none
        | RED  (x, left, LEAF)  => some x (push left rest)
        | BLACK(x, left, LEAF)  => some x (push left rest)
        | RED  (x, left, right) => getMax(pushNode right x left rest) some none
        | BLACK(x, left, right) => getMax(pushNode right x left rest) some none

  fun fold get f e (compare, tree, n) =
      let fun loop stack acc =
              get stack (fn x => fn stack => loop stack (f(x, acc))) acc
      in  loop [tree] e end

  fun foldl f = fold getMin f

  fun foldr f = fold getMax f

  fun listItems set = foldr op:: [] set

  fun appAll get f (compare, tree, n) =
      let fun loop stack = get stack (fn x => (f x; loop)) ()
      in  loop [tree] end

  fun app f = appAll getMin f

  fun revapp f = appAll getMax f

  fun find p set =
      let exception EXIT of 'a
          fun newp x = if p x then raise EXIT x else ()
      in  (app newp set; NONE)
          handle EXIT x => SOME x end


  (*  Ralf Hinze's convert a sorted list to RB tree *)
  local
      datatype 'item digits =
               ZERO
             | ONE of 'item * 'item tree * 'item digits
             | TWO of 'item * 'item tree * 'item * 'item tree * 'item digits

      fun incr x a ZERO                  = ONE(x, a, ZERO)
        | incr x a (ONE(y, b, ds))       = TWO(x, a, y, b, ds)
        | incr z c (TWO(y, b, x, a, ds)) =
          ONE(z, c, incr y (BLACK(x, a, b)) ds)

      fun insertMax(a, digits) = incr a LEAF digits

      fun build ZERO                  a = a
        | build (ONE(x, a, ds))       b = build ds (BLACK(x, a, b))
        | build (TWO(y, b, x, a, ds)) c = build ds (BLACK(x, a, RED(y, b, c)))

      fun buildAll digits = build digits LEAF

      fun toInt digits =
          let fun loop ZERO power acc            = acc
                | loop (ONE(_,_,rest)) power acc =
                  loop rest (2*power) (power + acc)
                | loop (TWO(_,_,_,_,rest)) power acc =
                  loop rest (2*power) (2*power + acc)
          in  loop digits 1 0 end

      fun get stack = getMin stack (fn x => fn stack => SOME(x,stack)) NONE

      fun insRest stack acc =
          getMin stack (fn x => fn stack => insRest stack (insertMax(x,acc)))
                 acc

  in
  fun fromSortedList (compare, ls) =
      let val digits = List.foldl insertMax ZERO ls
      in  (compare, buildAll digits, toInt digits) end


  (* FIXME: it *must* be possible to write union, equal, isSubset,
            intersection, and difference more elegant.
  *)
  fun actual_union (s1 as (compare, t1, n1), s2 as (_, t2, n2)) =
      let fun loop x y stack1 stack2 res =
              case compare(x, y) of
                  EQUAL =>
                  let val res = insertMax(x, res)
                  in  case (get stack1, get stack2) of
                          (SOME(x, s1), SOME(y, s2)) => loop x y s1 s2 res
                        | (NONE, NONE)               => res
                        | (SOME _, _)                => insRest stack1 res
                        | (_, SOME _)                => insRest stack2 res
                  end
                | LESS =>
                  let val res = insertMax(x, res)
                  in  case get stack1 of
                          NONE => insRest stack2 (insertMax(y, res))
                        | SOME(x, stack1) => loop x y stack1 stack2 res
                  end
                | GREATER =>
                  let val res = insertMax(y, res)
                  in  case get stack2 of
                          NONE => insRest stack1 (insertMax(x, res))
                        | SOME(y, stack2) => loop x y stack1 stack2 res
                  end
      in  (* FIXME: here is lots of room for optimizations *)
          case (get [t1], get [t2]) of
              (SOME(x, stack1), SOME(y, stack2)) =>
              let val digits = loop x y stack1 stack2 ZERO
              in  (compare, buildAll digits, toInt digits) end
            | (_, SOME _) => s2
            | _           => s1 end

  local
      val ln2 = Math.ln 2.0
  in
  fun union ((_, _, 0), s2) = s2
    | union (s1,(_, _, 0)) = s1
    | union (s1 as (_, _, n1), s2 as (_, _, n2)) =
      let val ((smin,nmin),(smax,nmax)) =
              if (n1<n2) then ((s1,Real.fromInt n1),(s2,Real.fromInt n2))
              else ((s2,Real.fromInt n2),(s1,Real.fromInt n1))
      in
          if Math.ln nmax / ln2 * nmin < nmin + nmax
          then foldl (fn(x, res) => add(res, x)) smax smin
          else actual_union(s1,s2)
      end
  end

  fun equal ((compare, t1, _), (_, t2, _)) =
      let fun loop x y stack1 stack2 =
              case compare(x, y) of
                  EQUAL =>
                  (case (get stack1, get stack2) of
                       (SOME(x, s1), SOME(y, s2)) => loop x y s1 s2
                     | (NONE, NONE)               => true
                     | _                          => false)
                | _ => false
      in  (* FIXME: here is lots of room for optimizations *)
          case (get [t1], get [t2]) of
              (SOME(x, stack1), SOME(y, stack2)) => loop x y stack1 stack2
            | (NONE, NONE)                       => true
            | _                                  => false end

  fun isSubset ((compare, t1, _), (_, t2, _)) =
      let fun loop x y stack1 stack2 =
              case compare(x, y) of
                  EQUAL =>
                  (case (get stack1, get stack2) of
                       (SOME(x, s1), SOME(y, s2)) => loop x y s1 s2
                     | (NONE, _)                  => true
                     | _                          => false)
                | LESS => false
                | GREATER =>
                  (case get stack2 of
                       SOME(y, stack2) => loop x y stack1 stack2
                     | NONE            => false)
      in  (* FIXME: here is lots of room for optimizations *)
          case (get [t1], get [t2]) of
              (SOME(x, stack1), SOME(y, stack2)) => loop x y stack1 stack2
            | (NONE, _)                          => true
            | _                                  => false
      end


  fun intersection (s1 as (compare, t1, n1), s2 as (_, t2, n2)) =
      let fun loop x y stack1 stack2 res =
              case compare(x, y) of
                  EQUAL =>
                  let val res = insertMax(x, res)
                  in  case (get stack1, get stack2) of
                          (SOME(x, s1), SOME(y, s2)) => loop x y s1 s2 res
                        | _                          => res
                  end
                | LESS =>
                  (case get stack1 of
                       NONE            => res
                     | SOME(x, stack1) => loop x y stack1 stack2 res)
                | GREATER =>
                  (case get stack2 of
                       NONE            => res
                     | SOME(y, stack2) => loop x y stack1 stack2 res)
      in  (* FIXME: here is lots of room for optimizations *)
          case (get [t1], get [t2]) of
              (SOME(x, stack1), SOME(y, stack2)) =>
              let val digits = loop x y stack1 stack2 ZERO
              in  (compare, buildAll digits, toInt digits) end
            | _           => empty compare end


  fun difference (s1 as (compare, t1, n1), s2 as (_, t2, n2)) =
      let fun loop x y stack1 stack2 res =
              case compare(x, y) of
                  EQUAL =>
                  (case (get stack1, get stack2) of
                       (SOME(x, s1), SOME(y, s2)) => loop x y s1 s2 res
                     | (SOME _, _)                => insRest stack1 res
                     | _                          => res)
                | LESS =>
                  let val res = insertMax(x, res)
                  in  case get stack1 of
                          NONE            => res
                        | SOME(x, stack1) => loop x y stack1 stack2 res
                  end
                | GREATER =>
                  (case get stack2 of
                       NONE => insRest stack1 (insertMax(x, res))
                     | SOME(y, stack2) => loop x y stack1 stack2 res)
      in  (* FIXME: here is lots of room for optimizations *)
          case (get [t1], get [t2]) of
              (SOME(x, stack1), SOME(y, stack2)) =>
              let val digits = loop x y stack1 stack2 ZERO
              in  (compare, buildAll digits, toInt digits) end
            | (_, SOME _) => empty compare
            | _           => s1 end
  end


  (* Peter Sestoft's convert a sorted list to RB tree *)
  fun fromSortedList' ls =
      let val len = length ls
          fun log2 n =
              let fun loop k p = if p >= n then k else loop (k+1) (2*p)
              in loop 0 1 end
          fun h 0 _ xs = (LEAF, xs)
            | h n d xs =
              let val m = n div 2
                  val (t1, ys) = h m       (d-1) xs
                  val y = hd ys
                  and yr = tl ys
                  val (t2, zs) = h (n-m-1) (d-1) yr
              in (if d=0 then RED(y, t1, t2) else BLACK(y, t1, t2), zs) end
      in  ( case #1 (h len (log2 (len + 1) - 1) ls) of
                RED(x, left, right) => BLACK(x, left, right)
              | tree                => tree
          , len) end


  exception RedBlackSetError

  (* delete a la Stefan M. Kahrs *)

  fun sub1 (BLACK arg) = RED arg
    | sub1 _ = raise RedBlackSetError

  fun balleft y (RED(x,a,b)) c             = RED(y, BLACK(x, a, b), c)
    | balleft x bl (BLACK(y, a, b))        = rbalance x bl (RED(y, a, b))
    | balleft x bl (RED(z,BLACK(y,a,b),c)) =
      RED(y, BLACK(x, bl, a), rbalance z b (sub1 c))
    | balleft _ _ _ = raise RedBlackSetError

  fun balright x a             (RED(y,b,c)) = RED(x, a, BLACK(y, b, c))
    | balright y (BLACK(x,a,b))          br = lbalance y (RED(x,a,b)) br
    | balright z (RED(x,a,BLACK(y,b,c))) br =
      RED(y, lbalance x (sub1 a) b, BLACK(z, c, br))
    | balright _ _ _ = raise RedBlackSetError


  (* [append left right] constructs a new tree t.
  PRECONDITIONS: RB left /\ RB right
              /\ !e in left => !x in right e < x
  POSTCONDITION: not (RB t)
  *)
  fun append LEAF right                    = right
    | append left LEAF                     = left
    | append (RED(x,a,b)) (RED(y,c,d))     =
      (case append b c of
           RED(z, b, c) => RED(z, RED(x, a, b), RED(y, c, d))
         | bc           => RED(x, a, RED(y, bc, d)))
    | append a (RED(x,b,c))                = RED(x, append a b, c)
    | append (RED(x,a,b)) c                = RED(x, a, append b c)
    | append (BLACK(x,a,b)) (BLACK(y,c,d)) =
      (case append b c of
           RED(z, b, c) => RED(z, BLACK(x, a, b), BLACK(y, c, d))
         | bc           => balleft x a (BLACK(y, bc, d)))

  fun delete (set as (compare, tree, n), x) =
      let fun delShared y a b =
              case compare(x,y) of
                  EQUAL   => append a b
                | LESS    => (case a of
                                  BLACK _ => balleft y (del a) b
                                | _       => RED(y, del a, b))
                | GREATER => (case b of
                                  BLACK _ => balright y a (del b)
                                | _       => RED(y, a, del b))
          and del LEAF             = raise NotFound
            | del (RED(y, a, b))   = delShared y a b
            | del (BLACK(y, a, b)) = delShared y a b
      in  ( compare
          , case del tree of
                RED arg => BLACK arg
              | tree    => tree
          , n-1) end

  fun filter p (set as (compare, _, _)) =
      foldl (fn (e, acc) => if p e then add(acc,e)
                            else acc)
         (empty compare)
         set

end
