(* Redblackmap --                                                   *)
(*    applicative maps implemented by Okasaki-style Red-Black trees *)
(* Ken Friis Larsen <ken@friislarsen.net>                           *)
structure Redblackmap :>  Redblackmap =
struct

  datatype ('key, 'a) tree =
           LEAF
         | RED   of 'key * 'a * ('key, 'a) tree * ('key, 'a) tree
         | BLACK of 'key * 'a * ('key, 'a) tree * ('key, 'a) tree

  type ('key, 'a) dict  = ('key * 'key -> order) * ('key, 'a) tree * int

  exception NotFound

  fun mkDict compare = (compare, LEAF, 0)

  fun numItems (_, _, n) = n

  fun isEmpty (_, _, n) = (n = 0)

  fun findKey ((compare, tree, n), key) =
      let fun loopShared k x left right =
              case compare(key, k) of
                  EQUAL   => (k, x)
                | LESS    => loop left
                | GREATER => loop right
          and loop LEAF                       = raise NotFound
            | loop (RED(k, x, left, right))   = loopShared k x left right
            | loop (BLACK(k, x, left, right)) = loopShared k x left right
      in  loop tree end

  fun find x = #2(findKey x)

  fun peek (set, key) = SOME(find(set, key))
                        handle NotFound => NONE

  fun lbalance z zd (RED(y,yd,RED(x,xd,a,b),c)) d =
      RED(y,yd,BLACK(x,xd,a,b),BLACK(z,zd,c,d))
    | lbalance z zd (RED(x,xd,a,RED(y,yd,b,c))) d =
      RED(y,yd,BLACK(x,xd,a,b),BLACK(z,zd,c,d))
    | lbalance k x left right = BLACK(k, x, left, right)

  fun rbalance x xd a (RED(y,yd,b,RED(z,zd,c,d))) =
      RED(y,yd,BLACK(x,xd,a,b),BLACK(z,zd,c,d))
    | rbalance x xd a (RED(z,zd,RED(y,yd,b,c),d)) =
      RED(y,yd,BLACK(x,xd,a,b),BLACK(z,zd,c,d))
    | rbalance k x left right = BLACK(k, x, left, right)

  exception GETOUT

  fun update (set as (compare, tree, n), key, data) =
      let val addone = ref true
          fun ins LEAF = RED(key,data NONE,LEAF,LEAF)
	    | ins (BLACK(k,x,left,right)) =
              (case compare(key, k) of
                   LESS    => lbalance k x (ins left) right
                 | GREATER => rbalance k x left (ins right)
                 | EQUAL   => (addone := false; BLACK(key, data (SOME x), left, right)))
	    | ins (RED(k, x,left,right)) =
              (case compare(key, k) of
                   LESS    => RED(k, x, (ins left), right)
                 | GREATER => RED(k, x, left, (ins right))
                 | EQUAL   => (addone := false; RED(key, data (SOME x), left, right)))
      in  ( compare
          , case ins tree of
                RED x => BLACK x
              | tree  => tree
          , if !addone then n+1 else n) end

  local fun K x _ = x in
    fun insert (set, key, data) = update (set, key, K data)
  end

  fun insertList (m, xs) =
    List.foldl (fn ((i, v), m) => insert (m, i, v)) m xs

  fun fromList compare xs =
    insertList (mkDict compare, xs)

  fun push LEAF stack = stack
    | push tree stack = tree :: stack

  fun pushNode left k x right stack =
      left :: (BLACK(k, x, LEAF, LEAF) :: (push right stack))

  fun getMin []             some none = none
    | getMin (tree :: rest) some none =
      case tree of
          LEAF                 => getMin rest some none
        | RED  (k, x, LEAF, b) => some k x (push b rest)
        | BLACK(k, x, LEAF, b) => some k x (push b rest)
        | RED  (k, x, a, b)    => getMin(pushNode a k x b rest) some none
        | BLACK(k, x, a, b)    => getMin(pushNode a k x b rest) some none

  fun getMax []             some none = none
    | getMax (tree :: rest) some none =
      case tree of
          LEAF                 => getMax rest some none
        | RED  (k, x, a, LEAF) => some k x (push a rest)
        | BLACK(k, x, a, LEAF) => some k x (push a rest)
        | RED  (k, x, a, b)    => getMax(pushNode b k x a rest) some none
        | BLACK(k, x, a, b)    => getMax(pushNode b k x a rest) some none

  fun fold get f e (compare, tree, n) =
      let fun loop stack acc =
              get stack (fn k =>fn x =>fn stack => loop stack (f(k,x,acc))) acc
      in  loop [tree] e end

  fun foldl f = fold getMin f

  fun foldr f = fold getMax f

  fun listItems set = foldr (fn(k,x,res) => (k,x)::res) [] set

  fun appAll get f (compare, tree, n) =
      let fun loop stack = get stack (fn k => fn x => (f(k,x); loop)) ()
      in  loop [tree] end

  fun app f = appAll getMin f

  fun revapp f = appAll getMax f


  exception RedBlackMapError

  (* remove a la Stefan M. Kahrs *)
  fun redden (BLACK arg) = RED arg
    | redden _ = raise RedBlackMapError

  fun balleft y yd (RED(x,xd,a,b)) c                =
      RED(y, yd, BLACK(x, xd, a, b), c)
    | balleft x xd bl (BLACK(y, yd, a, b))          =
      rbalance x xd bl (RED(y, yd, a, b))
    | balleft x xd bl (RED(z,zd,BLACK(y,yd,a,b),c)) =
      RED(y, yd, BLACK(x, xd, bl, a), rbalance z zd b (redden c))
    | balleft _ _ _ _ = raise RedBlackMapError

  fun balright x xd a             (RED(y, yd ,b,c)) =
      RED(x, xd, a, BLACK(y, yd, b, c))
    | balright y yd (BLACK(x,xd,a,b))          br =
      lbalance y yd (RED(x,xd,a,b)) br
    | balright z zd (RED(x,xd,a,BLACK(y,yd,b,c))) br =
      RED(y, yd, lbalance x xd (redden a) b, BLACK(z, zd, c, br))
    | balright _ _ _ _ = raise RedBlackMapError


  (* [append left right] constructs a new tree t.
  PRECONDITIONS: RB left /\ RB right
              /\ !e in left => !x in right e < x
  POSTCONDITION: not (RB t)
  *)
  fun append LEAF right                    = right
    | append left LEAF                     = left
    | append (RED(x,xd,a,b)) (RED(y,yd,c,d))     =
      (case append b c of
	   RED(z, zd, b, c) => RED(z, zd, RED(x, xd, a, b), RED(y, yd, c, d))
         | bc           => RED(x, xd, a, RED(y, yd, bc, d)))
    | append a (RED(x,xd,b,c))                = RED(x, xd, append a b, c)
    | append (RED(x,xd,a,b)) c                = RED(x, xd, a, append b c)
    | append (BLACK(x,xd,a,b)) (BLACK(y,yd,c,d)) =
      (case append b c of
	   RED(z, zd, b, c) => RED(z, zd, BLACK(x,xd,a,b), BLACK(y,yd,c,d))
         | bc           => balleft x xd a (BLACK(y, yd, bc, d)))

  fun remove ((compare, tree, n), key) =
      let fun delShared k x a b =
              case compare(key, k) of
                  EQUAL   => (x, append a b)
                | LESS    =>
                  let val (res, a') = del a
                  in  (res, case a of
                                BLACK _ => balleft k x a' b
                              | _       => RED(k, x, a', b)) end
                | GREATER =>
                  let val (res, b') = del b
                  in  (res, case b of
                                BLACK _ => balright k x a b'
                              | _       => RED(k, x, a, b')) end
          and del LEAF                = raise NotFound
            | del (RED(k, x, a, b))   = delShared k x a b
            | del (BLACK(k, x, a, b)) = delShared k x a b

          val (res, tree) = case del tree of
                                (res, RED arg) => (res, BLACK arg)
                              | x              => x
      in  ((compare, tree, n-1), res) end

  fun map f (compare, tree, n) =
      let fun loop LEAF = LEAF
            | loop (RED(k,x,a,b)) =
              let val a = loop a
                  val x = f(k,x)
              in  RED(k,x,a, loop b) end
            | loop (BLACK(k,x,a,b)) =
              let val a = loop a
                  val x = f(k,x)
              in  BLACK(k,x,a, loop b) end
      in  (compare, loop tree, n) end

  fun transform f (compare, tree, n) =
      let fun loop LEAF = LEAF
            | loop (RED(k,x,a,b)) =
              let val a = loop a
              in  RED(k, f x, a, loop b) end
            | loop (BLACK(k,x,a,b)) =
              let val a = loop a
              in  BLACK(k, f x, a, loop b) end
      in  (compare, loop tree, n) end
end
(*
val t1 = Redblackset.addList(Redblackset.empty Int.compare, [43,25,13,14]);
val t2 = Redblackset.addList(Redblackset.empty Int.compare, [43,1,2,3]);
val t3 = Redblackset.addList(Redblackset.empty Int.compare, [1,3]);
*)
