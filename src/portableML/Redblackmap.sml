structure Redblackmap :> Redblackmap =
struct

  (* essentially a port of Ken Friis Larsen's implementation of Redblacksets *)

  datatype ('key, 'item) tree = LEAF
                              | RED of 'key * 'item *
                                       ('key,'item) tree * ('key,'item) tree
                              | BLACK of 'key * 'item *
                                         ('key,'item) tree * ('key,'item) tree

  type ('key, 'item) dict = ('key * 'key -> order) * ('key, 'item) tree * int

  exception NotFound

  fun mkDict compare = (compare, LEAF, 0)
  fun numItems (_, _, n) = n


  fun find ((compare, tree, n), k) = let
    fun findShared k' i left right =
        case compare(k, k') of
          EQUAL => i
        | LESS => find0 left
        | GREATER => find0 right
    and find0 LEAF             = raise NotFound
      | find0 (RED(x,y,l,r))   = findShared x y l r
      | find0 (BLACK(x,y,l,r)) = findShared x y l r
  in
    find0 tree
  end

  fun peek(d, k) = SOME (find(d, k)) handle NotFound => NONE

  fun lbalance z k (RED(y,j,RED(x,i,a,b),c)) d =
      RED(y,j,BLACK(x,i,a,b),BLACK(z,k,c,d))
    | lbalance z k (RED(x,i,a,RED(y,j,b,c))) d =
      RED(y,j,BLACK(x,i,a,b),BLACK(z,k,c,d))
    | lbalance x i left right = BLACK(x, i, left, right)

  fun rbalance x i a (RED(y,j,b,RED(z,k,c,d))) =
      RED(y,j,BLACK(x,i,a,b),BLACK(z,k,c,d))
    | rbalance x i a (RED(z,k,RED(y,j,b,c),d)) =
      RED(y,j,BLACK(x,i,a,b),BLACK(z,k,c,d))
    | rbalance x i left right = BLACK(x, i, left, right)

  exception GETOUT

  local
      fun insert0 compare k v =
          let fun ins LEAF = (RED(k,v,LEAF,LEAF), true)
	        | ins (BLACK(x,i,left,right)) =
                  (case compare(k, x) of
                     LESS    => let
                       val (newleft, ext) = ins left
                     in
                       (lbalance x i newleft right, ext)
                     end
                   | GREATER => let
                       val (newright, ext) = ins right
                     in
                       (rbalance x i left newright, ext)
                     end
                   | EQUAL   => (BLACK(x,v,left,right), false))
	        | ins (RED(x,i,left,right)) =
                  (case compare(k, x) of
                     LESS    => let
                       val (newleft, ext) = ins left
                     in
                       (RED(x, i, newleft, right), ext)
                     end
                   | GREATER => let
                       val (newright, ext) = ins right
                     in
                       (RED(x, i, left, newright), ext)
                     end
                   | EQUAL   => (RED(x,v,left,right), false))
          in  ins end
  in

  fun insert (map as (compare, tree, n), k, v) = let
    val (new_tree, extended) = insert0 compare k v tree
  in
    (compare,
     (case new_tree of
        RED tuple => BLACK tuple
      | x => x),
     if extended then n + 1 else n)
  end
  end (* local *)

  (* delete a la Stefan M. Kahrs *)

  fun sub1 (BLACK arg) = RED arg
    | sub1 x = raise Fail "RBmap.sub1: Invariant failure?"

  fun balleft y j (RED(x,i,a,b)) c = RED(y, j, BLACK(x, i, a, b), c)
    | balleft x i bl (BLACK(y, j, a, b)) = rbalance x i bl (RED(y, j, a, b))
    | balleft x i bl (RED(z,k,BLACK(y,j,a,b),c)) =
      RED(y, j, BLACK(x, i, bl, a), rbalance z k b (sub1 c))
    | balleft _ _ _ _ = raise Fail "RBmap.balleft: Invariant failure?"

  fun balright x i a (RED(y,j,b,c)) = RED(x, i, a, BLACK(y, j, b, c))
    | balright y j (BLACK(x,i,a,b)) br = lbalance y j (RED(x,i,a,b)) br
    | balright z k (RED(x,i,a,BLACK(y,j,b,c))) br =
      RED(y, j, lbalance x i (sub1 a) b, BLACK(z, k, c, br))
    | balright _ _ _ _ = raise Fail "RBmap.balright: Invariant failure?"


  (* [append left right] constructs a new tree t.
  PRECONDITIONS: RB left /\ RB right
              /\ !e in left => !x in right e < x
  POSTCONDITION: not (RB t)
  *)
  fun append LEAF right                    = right
    | append left LEAF                     = left
    | append (RED(x,i,a,b)) (RED(y,j,c,d))     =
      (case append b c of
	   RED(z, k, b, c) => RED(z, k, RED(x, i, a, b), RED(y, k, c, d))
         | bc           => RED(x, i, a, RED(y, j, bc, d)))
    | append a (RED(x,i,b,c))                = RED(x, i, append a b, c)
    | append (RED(x,i,a,b)) c                = RED(x, i, a, append b c)
    | append (BLACK(x,i,a,b)) (BLACK(y,j,c,d)) =
      (case append b c of
	   RED(z, k, b, c) => RED(z, k, BLACK(x, i, a, b), BLACK(y, j, c, d))
         | bc           => balleft x i a (BLACK(y, j, bc, d)))

  fun remove (dict as (compare, tree, n), x) = let
    fun delShared y j a b =
        case compare(x,y) of
          EQUAL   => (append a b, j)
        | LESS    => let
            val (newtree, kvalue) = del a
          in
            case a of
              BLACK _ => (balleft y j newtree b, kvalue)
            | _       => (RED(y, j, newtree, b), kvalue)
          end
        | GREATER => let
            val (newtree, kvalue) = del b
          in
            case b of
              BLACK _ => (balright y j a newtree, kvalue)
            | _       => (RED(y, j, a, newtree), kvalue)
          end
    and del LEAF             = raise NotFound
      | del (RED(y, j, a, b))   = delShared y j a b
      | del (BLACK(y, j, a, b)) = delShared y j a b
    val (newtree, kvalue) = del tree
  in  ((compare,
        (case newtree of
            RED arg => BLACK arg
          | tree    => tree), n-1),
       kvalue)
  end


  fun push LEAF stack = stack
    | push tree stack = tree :: stack

  fun pushNode left x i right stack =
      left :: (BLACK(x, i, LEAF, LEAF) :: (push right stack))

  fun getMin []             some none = none
    | getMin (tree :: rest) some none =
      case tree of
          LEAF                     => getMin rest some none
        | RED  (x, i, LEAF, right) => some x i (push right rest)
        | BLACK(x, i, LEAF, right) => some x i (push right rest)
        | RED  (x, i, left, right) =>
            getMin(pushNode left x i right rest) some none
        | BLACK(x, i, left, right) =>
          getMin(pushNode left x i right rest) some none

  fun getMax []             some none = none
    | getMax (tree :: rest) some none =
      case tree of
          LEAF                    => getMax rest some none
        | RED  (x, i, left, LEAF)  => some x i (push left rest)
        | BLACK(x, i, left, LEAF)  => some x i (push left rest)
        | RED  (x, i, left, right) =>
            getMax(pushNode right x i left rest) some none
        | BLACK(x, i, left, right) =>
            getMax(pushNode right x i left rest) some none

  fun fold get f e (compare, tree, n) =
      let fun loop stack acc =
              get stack (fn x => fn i => fn stack =>
                                            loop stack (f(x, i, acc))) acc
      in  loop [tree] e end

  fun foldl f = fold getMin f

  fun foldr f = fold getMax f

  fun listItems set = foldr (fn(k,v,acc) => (k,v)::acc) [] set

  fun appAll get f (compare, tree, n) =
      let fun loop stack = get stack (fn x => fn i => (f(x,i); loop)) ()
      in  loop [tree] end

  fun app f = appAll getMin f

  fun revapp f = appAll getMax f

  fun map f (cmp, t, n) = let
    fun map0 t kt =
        case t of
          LEAF => kt LEAF
        | RED(k,v,l,r) =>
            map0 l (fn l' => map0 r (fn r' => kt (RED(k, f(k,v), l', r'))))
        | BLACK(k,v,l,r) =>
            map0 l (fn l' => map0 r (fn r' => kt (BLACK(k, f(k,v), l', r'))))
  in
    (cmp, map0 t (fn x => x), n)
  end

  fun transform f = map (fn (k,v) => f v)

end; (* struct *)