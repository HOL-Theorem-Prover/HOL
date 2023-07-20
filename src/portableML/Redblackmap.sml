(*
 * COPYRIGHT (c) 2014 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * This code is based on Chris Okasaki's implementation [1] of
 * red-black trees.  The linear-time tree construction code is
 * based on the paper "Constructing red-black trees" by Hinze [2],
 * and the delete function is based on the description in Cormen,
 * Leiserson, and Rivest [3].
 *
 * A red-black tree should satisfy the following two invariants:
 *
 *   Red Invariant: each red node has black children (empty nodes are
 *   considered black).
 *
 *   Black Invariant: each path from the root to an empty node has the
 *     same number of black nodes (the tree's black height).
 *
 * The Black invariant implies that any node with only one child
 * will be black and its child will be a red leaf.
 *)

structure Redblackmap :> Redblackmap =
  struct
    type 'key compare = 'key * 'key -> order

    datatype color = R | B

    datatype ('key, 'a) tree
      = E (* empty *)
      | T of (color * ('key, 'a) tree * 'key * 'a * ('key, 'a) tree)

    (* was: 'a map *)
    datatype ('key, 'a) dict = MAP of (int * ('key, 'a) tree * 'key compare)

    exception NotFound

    fun isEmpty (MAP(_, E, _)) = true
      | isEmpty _ = false

    (* was: val empty = MAP(0, E) *)
    fun mkDict compare = MAP(0, E, compare)

    fun singleton compare (xk, x) = MAP(1, T(B, E, xk, x, E), compare)

    fun insert (MAP(nItems, m, compare), xk, x) = let
          val nItems' = ref nItems
          fun ins E = (nItems' := nItems+1; T(R, E, xk, x, E))
            | ins (s as T(color, a, yk, y, b)) = (case compare(xk, yk)
                 of LESS => (case a
                       of T(R, c, zk, z, d) => (case compare(xk, zk)
                             of LESS => (case ins c
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,e,wk, w,f), zk, z, T(B,d,yk,y,b))
                                    | c => T(B, T(R,c,zk,z,d), yk, y, b)
                                  (* end case *))
                              | EQUAL => T(color, T(R, c, xk, x, d), yk, y, b)
                              | GREATER => (case ins d
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,c,zk,z,e), wk, w, T(B,f,yk,y,b))
                                    | d => T(B, T(R,c,zk,z,d), yk, y, b)
                                  (* end case *))
                            (* end case *))
                        | _ => T(B, ins a, yk, y, b)
                      (* end case *))
                  | EQUAL => T(color, a, xk, x, b)
                  | GREATER => (case b
                       of T(R, c, zk, z, d) => (case compare(xk, zk)
                             of LESS => (case ins c
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,a,yk,y,e), wk, w, T(B,f,zk,z,d))
                                    | c => T(B, a, yk, y, T(R,c,zk,z,d))
                                  (* end case *))
                              | EQUAL => T(color, a, yk, y, T(R, c, xk, x, d))
                              | GREATER => (case ins d
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,a,yk,y,c), zk, z, T(B,e,wk,w,f))
                                    | d => T(B, a, yk, y, T(R,c,zk,z,d))
                                  (* end case *))
                            (* end case *))
                        | _ => T(B, a, yk, y, ins b)
                      (* end case *))
                (* end case *))
    in
        case ins m of
            E => raise Fail "cannot be empty here"
         | T(_, a, yk, y, b) => MAP(!nItems', T(B, a, yk, y, b), compare)
    end
    fun insert' ((xk, x), m) = insert (m, xk, x)

    fun insertWithi comb (MAP(nItems, m, compare), xk, x) = let
          val nItems' = ref nItems
          fun ins E = (nItems' := nItems+1; T(R, E, xk, x, E))
            | ins (s as T(color, a, yk, y, b)) = (case compare(xk, yk)
                 of LESS => (case a
                       of T(R, c, zk, z, d) => (case compare(xk, zk)
                             of LESS => (case ins c
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,e,wk, w,f), zk, z, T(B,d,yk,y,b))
                                    | c => T(B, T(R,c,zk,z,d), yk, y, b)
                                  (* end case *))
                              | EQUAL => let
                                  val x' = comb(xk, z, x)
                                  in
                                    T(color, T(R, c, xk, x', d), yk, y, b)
                                  end
                              | GREATER => (case ins d
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,c,zk,z,e), wk, w, T(B,f,yk,y,b))
                                    | d => T(B, T(R,c,zk,z,d), yk, y, b)
                                  (* end case *))
                            (* end case *))
                        | _ => T(B, ins a, yk, y, b)
                      (* end case *))
                  | EQUAL => T(color, a, xk, comb(xk, y, x), b)
                  | GREATER => (case b
                       of T(R, c, zk, z, d) => (case compare(xk, zk)
                             of LESS => (case ins c
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,a,yk,y,e), wk, w, T(B,f,zk,z,d))
                                    | c => T(B, a, yk, y, T(R,c,zk,z,d))
                                  (* end case *))
                              | EQUAL => let
                                  val x' = comb(xk, z, x)
                                  in
                                    T(color, a, yk, y, T(R, c, xk, x', d))
                                  end
                              | GREATER => (case ins d
                                   of T(R, e, wk, w, f) =>
                                        T(R, T(B,a,yk,y,c), zk, z, T(B,e,wk,w,f))
                                    | d => T(B, a, yk, y, T(R,c,zk,z,d))
                                  (* end case *))
                            (* end case *))
                        | _ => T(B, a, yk, y, ins b)
                      (* end case *))
                (* end case *))
    in
        case ins m of
            E => raise Fail "cannot be empty here"
         | T(_, a, yk, y, b) => MAP(!nItems', T(B, a, yk, y, b), compare)
    end
    fun insertWith comb = insertWithi (fn (_, x1, x2) => comb(x1, x2))

  (* Is a key in the domain of the map? *)
    fun inDomain (MAP(_, t, compare), k) = let
          fun find' E = false
            | find' (T(_, a, yk, y, b)) = (case compare(k, yk)
                 of LESS => find' a
                  | EQUAL => true
                  | GREATER => find' b
                (* end case *))
          in
            find' t
          end

  (* Look for an item, return NONE if the item doesn't exist
     NOTE: the name of this function was "find".
   *)
    fun peek (MAP(_, t, compare), k) = let
          fun find' E = NONE
            | find' (T(_, a, yk, y, b)) = (case compare(k, yk)
                 of LESS => find' a
                  | EQUAL => SOME y
                  | GREATER => find' b
                (* end case *))
          in
            find' t
          end

  (* Look for an item, raise NotFound if the item doesn't exist
     NOTE: the name of this function was "lookup".
   *)
    fun find (MAP(_, t, compare), k) = let
          fun look E = raise NotFound
            | look (T(_, a, yk, y, b)) = (case compare(k, yk)
                 of LESS => look a
                  | EQUAL => y
                  | GREATER => look b
                (* end case *))
          in
            look t
          end

  (* Remove an item, returning new map and value removed.
   * Raises NotFound if not found.
   *)
    local
      datatype ('key, 'a) zipper
        = TOP
        | LEFT of (color * 'key * 'a * ('key, 'a) tree * ('key, 'a) zipper)
        | RIGHT of (color * ('key, 'a) tree * 'key * 'a * ('key, 'a) zipper)
    in
    fun remove (MAP(nItems, t, compare), k) = let
        (* zip the zipper *)
          fun zip (TOP, t) = t
            | zip (LEFT(color, xk, x, b, z), a) = zip(z, T(color, a, xk, x, b))
            | zip (RIGHT(color, a, xk, x, z), b) = zip(z, T(color, a, xk, x, b))
        (* zip the zipper while resolving a black deficit *)
          fun fixupZip (TOP, t) = (true, t)
          (* case 1 from CLR *)
            | fixupZip (LEFT(B, xk, x, T(R, a, yk, y, b), p), t) = (case a
                 of T(_, T(R, a11, wk, w, a12), zk, z, a2) =>
                      (* case 1L ==> case 3L ==> case 4L *)
                      (false, zip (p, T(B, T(R, T(B, t, xk, x, a11), wk, w,
                                                T(B, a12, zk, z, a2)), yk, y, b)))
                  | T(_, a1, zk, z, T(R, a21, wk, w, t22)) =>
                      (* case 1L ==> case 4L *)
                      (false, zip (p, T(B, T(R, T(B, t, xk, x, a1), zk, z,
                                           T(B, a21, wk, w, t22)), yk, y, b)))
                  | T(_, a1, zk, z, a2) =>
                      (* case 1L ==> case 2L; rotate + recolor fixes deficit *)
                      (false, zip (p, T(B, T(B, t, xk, x, T(R, a1, zk, z, a2)), yk, y, b)))
                  | _ => fixupZip (LEFT(R, xk, x, a, LEFT(B, yk, y, b, p)), t)
                (* end case *))
            | fixupZip (RIGHT(B, T(R, a, xk, x, b), yk, y, p), t) = (case b
                 of T(_, b1, zk, z, T(R, b21, wk, w, b22)) =>
                      (* case 1R ==> case 3R ==> case 4R *)
                      (false, zip (p, T(B, a, xk, x, T(R, T(B, b1, zk, z, b21), wk, w,
                                                          T(B, b22, yk, y, t)))))
                  | T(_, T(R, b11, wk, w, b12), zk, z, b2) =>
                      (* case 1R ==> case 4R *)
                      (false, zip (p, T(B, a, xk, x, T(R, T(B, b11, wk, w, b12), zk, z,
                                                          T(B, b2, yk, y, t)))))
                  | T(_, b1, zk, z, b2) =>
                      (* case 1L ==> case 2L; rotate + recolor fixes deficit *)
                      (false, zip (p, T(B, a, xk, x, T(B, T(R, b1, zk, z, b2), yk, y, t))))
                  | _ => fixupZip (RIGHT(R, b, yk, y, RIGHT(B, a, xk, x, p)), t)
                (* end case *))
          (* case 3 from CLR *)
            | fixupZip (LEFT(color, xk, x, T(B, T(R, a1, yk, y, a2), zk, z, b), p), t) =
              (* case 3L ==> case 4L *)
                (false, zip (p, T(color, T(B, t, xk, x, a1), yk, y, T(B, a2, zk, z, b))))
            | fixupZip (RIGHT(color, T(B, a, xk, x, T(R, b1, yk, y, b2)), zk, z, p), t) =
              (* case 3R ==> case 4R; rotate, recolor, plus rotate fixes deficit *)
                (false, zip (p, T(color, T(B, a, xk, x, b1), yk, y, T(B, b2, zk, z, t))))
          (* case 4 from CLR *)
            | fixupZip (LEFT(color, xk, x, T(B, a, yk, y, T(R, b1, zk, z, b2)), p), t) =
                (false, zip (p, T(color, T(B, t, xk, x, a), yk, y, T(B, b1, zk, z, b2))))
            | fixupZip (RIGHT(color, T(B, T(R, a1, zk, z, a2), xk, x, b), yk, y, p), t) =
                (false, zip (p, T(color, T(B, a1, zk, z, a2), xk, x, T(B, b, yk, y, t))))
          (* case 2 from CLR; note that "a" and "b" are guaranteed to be black, since we did
           * not match cases 3 or 4.
           *)
            | fixupZip (LEFT(R, xk, x, T(B, a, yk, y, b), p), t) =
                (false, zip (p, T(B, t, xk, x, T(R, a, yk, y, b))))
            | fixupZip (LEFT(B, xk, x, T(B, a, yk, y, b), p), t) =
                fixupZip (p, T(B, t, xk, x, T(R, a, yk, y, b)))
            | fixupZip (RIGHT(R, T(B, a, xk, x, b), yk, y, p), t) =
                (false, zip (p, T(B, T(R, a, xk, x, b), yk, y, t)))
            | fixupZip (RIGHT(B, T(B, a, xk, x, b), yk, y, p), t) =
                fixupZip (p, T(B, T(R, a, xk, x, b), yk, y, t))
          (* push deficit up the tree by recoloring a black node as red *)
            | fixupZip (LEFT(_, yk, y, E, p), t) = fixupZip (p, T(R, t, yk, y, E))
            | fixupZip (RIGHT(_, E, yk, y, p), t) = fixupZip (p, T(R, E, yk, y, t))
          (* impossible cases that violate the red invariant *)
            | fixupZip _ = raise Fail "Red invariant violation"
        (* delete the minimum value from a non-empty tree, returning a 4-tuple
         * (key, elem, bd, tr), where key is the minimum key, elem is the element
         * named by key, tr is the residual tree with elem removed, and bd is true
         * if tr has a black-depth that is less than the original tree.
         *)
          fun delMin (T(R, E, yk, y, b), p) =
              (* replace the node by its right subtree (which must be E) *)
                (yk, y, false, zip(p, b))
            | delMin (T(B, E, yk, y, T(R, a', yk', y', b')), p) =
              (* replace the node with its right child, while recoloring the child black to
               * preserve the black invariant.
               *)
                (yk, y, false, zip (p, T(B, a', yk', y', b')))
            | delMin (T(B, E, yk, y, E), p) = let
              (* delete the node, which reduces the black-depth by one, so we attempt to fix
               * the deficit on the path back.
               *)
                val (blkDeficit, t) = fixupZip (p, E)
                in
                  (yk, y, blkDeficit, t)
                end
            | delMin (T(color, a, yk, y, b), z) = delMin(a, LEFT(color, yk, y, b, z))
            | delMin (E, _) = raise Match
          fun del (E, p) = raise NotFound
            | del (T(color, a, yk, y, b), p) = (case compare(k, yk)
                 of LESS => del (a, LEFT(color, yk, y, b, p))
                  | EQUAL => (case (color, a, b)
                       of (R, E, E) => (y, zip(p, E))
                        | (B, E, E) => (y, #2 (fixupZip (p, E)))
                        | (_, T(_, a', yk', y', b'), E) =>
                          (* node is black and left child is red; we replace the node with its
                           * left child recolored to black.
                           *)
                            (y, zip(p, T(B, a', yk', y', b')))
                        | (_, E, T(_, a', yk', y', b')) =>
                          (* node is black and right child is red; we replace the node with its
                           * right child recolored to black.
                           *)
                            (y, zip(p, T(B, a', yk', y', b')))
                        | _ => let
                            val (minKey, minElem, blkDeficit, b) = delMin (b, TOP)
                            in
                              if blkDeficit
                                then (y, #2 (fixupZip (RIGHT(color, a, minKey, minElem, p), b)))
                                else (y, zip (p, T(color, a, minKey, minElem, b)))
                            end
                      (* end case *))
                  | GREATER => del (b, RIGHT(color, a, yk, y, p))
                (* end case *))
          val (item, t) = del(t, TOP)
          in
            case t
             of T(R, a, xk, x, b) => (MAP(nItems-1, T(B, a, xk, x, b), compare), item)
              | t => (MAP(nItems-1, t, compare), item)
            (* end case *)
          end
    end (* local *)

  (* return the first item in the map (or NONE if it is empty) *)
    fun first (MAP(_, t, _)) = let
          fun f E = NONE
            | f (T(_, E, _, x, _)) = SOME x
            | f (T(_, a, _, _, _)) = f a
          in
            f t
          end
    fun firsti (MAP(_, t, _)) = let
          fun f E = NONE
            | f (T(_, E, xk, x, _)) = SOME(xk, x)
            | f (T(_, a, _, _, _)) = f a
          in
            f t
          end

  (* Return the number of items in the map *)
    fun numItems (MAP(n, _, _)) = n

  (* NOTE: renamed foldl => foldl', foldli => foldl *)
    fun foldl' f = let
          fun foldf (E, accum) = accum
            | foldf (T(_, a, _, x, b), accum) =
                foldf(b, f(x, foldf(a, accum)))
          in
            fn init => fn (MAP(_, m, _)) => foldf(m, init)
          end
    fun foldl f = let
          fun foldf (E, accum) = accum
            | foldf (T(_, a, xk, x, b), accum) =
                foldf(b, f(xk, x, foldf(a, accum)))
          in
            fn init => fn (MAP(_, m, _)) => foldf(m, init)
          end

  (* NOTE: renamed foldr => foldr', foldri => foldr *)
    fun foldr' f = let
          fun foldf (E, accum) = accum
            | foldf (T(_, a, _, x, b), accum) =
                foldf(a, f(x, foldf(b, accum)))
          in
            fn init => fn (MAP(_, m, _)) => foldf(m, init)
          end
    fun foldr f = let
          fun foldf (E, accum) = accum
            | foldf (T(_, a, xk, x, b), accum) =
                foldf(a, f(xk, x, foldf(b, accum)))
          in
            fn init => fn (MAP(_, m, _)) => foldf(m, init)
          end

    (* NOTE: renamed listItems => listItems', listItemsi => listItems *)
    fun listItems' m = foldr' (op ::) [] m
    fun listItems m = foldr (fn (xk, x, l) => (xk, x)::l) [] m

  (* return an ordered list of the keys in the map. *)
    fun listKeys m = foldr (fn (k, _, l) => k::l) [] m

  (* functions for walking the tree while keeping a stack of parents
   * to be visited.
   *)
    fun next ((t as T(_, _, _, _, b))::rest) = (t, left(b, rest))
      | next _ = (E, [])
    and left (E, rest) = rest
      | left (t as T(_, a, _, _, _), rest) = left(a, t::rest)
    fun start m = left(m, [])

  (* given an ordering on the map's range, return an ordering
   * on the map.
   *)
    fun collate cmpRng = let
          fun cmp compare (t1, t2) =
              (case (next t1, next t2)
                 of ((E, _), (E, _)) => EQUAL
                  | ((E, _), _) => LESS
                  | (_, (E, _)) => GREATER
                  | ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of EQUAL => (case cmpRng(x, y)
                             of EQUAL => cmp compare (r1, r2)
                              | order => order
                            (* end case *))
                        | order => order
                      (* end case *))
                (* end case *))
          in
            fn (MAP(_, m1, compare), MAP(_, m2, _)) => cmp compare (start m1, start m2)
          end

  (* support for constructing red-black trees in linear time from increasing
   * ordered sequences (based on a description by R. Hinze).  Note that the
   * elements in the digits are ordered with the largest on the left, whereas
   * the elements of the trees are ordered with the largest on the right.
   *)
    datatype ('key, 'a) digit
      = ZERO
      | ONE of ('key * 'a * ('key, 'a) tree * ('key, 'a) digit)
      | TWO of ('key * 'a * ('key, 'a) tree * 'key * 'a * ('key, 'a) tree *
                ('key, 'a) digit)

  (* add an item that is guaranteed to be larger than any in l *)
    fun addItem (ak, a, l) = let
          fun incr (ak, a, t, ZERO) = ONE(ak, a, t, ZERO)
            | incr (ak1, a1, t1, ONE(ak2, a2, t2, r)) =
                TWO(ak1, a1, t1, ak2, a2, t2, r)
            | incr (ak1, a1, t1, TWO(ak2, a2, t2, ak3, a3, t3, r)) =
                ONE(ak1, a1, t1, incr(ak2, a2, T(B, t3, ak3, a3, t2), r))
          in
            incr(ak, a, E, l)
          end
  (* link the digits into a tree *)
    fun linkAll t = let
          fun link (t, ZERO) = t
            | link (t1, ONE(ak, a, t2, r)) = link(T(B, t2, ak, a, t1), r)
            | link (t, TWO(ak1, a1, t1, ak2, a2, t2, r)) =
                link(T(B, T(R, t2, ak2, a2, t1), ak1, a1, t), r)
          in
            link (E, t)
          end

    local
      fun ins ((E, _), n, result) = (n, result)
        | ins ((T(_, _, xk, x, _), r), n, result) =
            ins(next r, n+1, addItem(xk, x, result))
    in

  (* NOTE: the input pairs must be pre-sorted by the keys w.r.t. compare *)
    fun fromOrderedList compare pairs = let
        fun add (l, n, result) =
           (case l
              of []        => (n, result)
              |  (k,x)::xs => add(xs, n+1, addItem(k,x,result))
           (* end case *));
        val (n, result) = add (pairs, 0, ZERO)
    in
        MAP(n, linkAll result, compare)
    end

  (* return a map whose domain is the union of the domains of the two input
   * maps, using the supplied function to define the map on elements that
   * are in both domains.
   *)
    fun unionWith mergeFn (MAP(_, m1, compare), MAP(_, m2, _)) = let
          fun union (t1, t2, n, result) =
              (case (next t1, next t2)
                 of ((E, _), (E, _)) => (n, result)
                  | ((E, _), t2) => ins(t2, n, result)
                  | (t1, (E, _)) => ins(t1, n, result)
                  | ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of LESS => union (r1, t2, n+1, addItem(xk, x, result))
                        | EQUAL =>
                            union (r1, r2, n+1, addItem(xk, mergeFn(x, y), result))
                        | GREATER => union (t1, r2, n+1, addItem(yk, y, result))
                      (* end case *))
                (* end case *));
          val (n, result) = union (start m1, start m2, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end
    fun unionWithi mergeFn (MAP(_, m1, compare), MAP(_, m2, _)) = let
          fun union (t1, t2, n, result) =
              (case (next t1, next t2)
                 of ((E, _), (E, _)) => (n, result)
                  | ((E, _), t2) => ins(t2, n, result)
                  | (t1, (E, _)) => ins(t1, n, result)
                  | ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of LESS => union (r1, t2, n+1, addItem(xk, x, result))
                        | EQUAL => union (
                            r1, r2, n+1, addItem(xk, mergeFn(xk, x, y), result))
                        | GREATER => union (t1, r2, n+1, addItem(yk, y, result))
                      (* end case *))
                (* end case *));
          val (n, result) = union (start m1, start m2, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end

  (* return a map whose domain is the intersection of the domains of the
   * two input maps, using the supplied function to define the range.
   *)
    fun intersectWith mergeFn (MAP(_, m1, compare), MAP(_, m2, _)) = let
          fun intersect (t1, t2, n, result) =
              (case (next t1, next t2)
                 of ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of LESS => intersect (r1, t2, n, result)
                        | EQUAL =>
                            intersect (r1, r2, n+1,
                              addItem(xk, mergeFn(x, y), result))
                        | GREATER => intersect (t1, r2, n, result)
                      (* end case *))
                  | _ => (n, result)
                (* end case *));
          val (n, result) = intersect (start m1, start m2, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end
    fun intersectWithi mergeFn (MAP(_, m1, compare), MAP(_, m2, _)) = let
          fun intersect (t1, t2, n, result) =
              (case (next t1, next t2)
                 of ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of LESS => intersect (r1, t2, n, result)
                        | EQUAL =>
                            intersect (r1, r2, n+1,
                              addItem(xk, mergeFn(xk, x, y), result))
                        | GREATER => intersect (t1, r2, n, result)
                      (* end case *))
                  | _ => (n, result)
                (* end case *));
          val (n, result) = intersect (start m1, start m2, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end

    fun mergeWith mergeFn (MAP(_, m1, compare), MAP(_, m2, _)) = let
          fun merge (t1, t2, n, result) =
              (case (next t1, next t2)
                 of ((E, _), (E, _)) => (n, result)
                  | ((E, _), (T(_, _, yk, y, _), r2)) =>
                      mergef (yk, NONE, SOME y, t1, r2, n, result)
                  | ((T(_, _, xk, x, _), r1), (E, _)) =>
                      mergef (xk, SOME x, NONE, r1, t2, n, result)
                  | ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of LESS => mergef (xk, SOME x, NONE, r1, t2, n, result)
                        | EQUAL => mergef (xk, SOME x, SOME y, r1, r2, n, result)
                        | GREATER => mergef (yk, NONE, SOME y, t1, r2, n, result)
                      (* end case *))
                (* end case *))
          and mergef (k, x1, x2, r1, r2, n, result) =
              (case mergeFn(x1, x2)
                 of NONE => merge (r1, r2, n, result)
                  | SOME y => merge (r1, r2, n+1, addItem(k, y, result))
                (* end case *));
          val (n, result) = merge (start m1, start m2, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end
    fun mergeWithi mergeFn (MAP(_, m1, compare), MAP(_, m2, _)) = let
          fun merge (t1, t2, n, result) =
              (case (next t1, next t2)
                 of ((E, _), (E, _)) => (n, result)
                  | ((E, _), (T(_, _, yk, y, _), r2)) =>
                      mergef (yk, NONE, SOME y, t1, r2, n, result)
                  | ((T(_, _, xk, x, _), r1), (E, _)) =>
                      mergef (xk, SOME x, NONE, r1, t2, n, result)
                  | ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
                      case compare(xk, yk)
                       of LESS => mergef (xk, SOME x, NONE, r1, t2, n, result)
                        | EQUAL => mergef (xk, SOME x, SOME y, r1, r2, n, result)
                        | GREATER => mergef (yk, NONE, SOME y, t1, r2, n, result)
                      (* end case *))
                (* end case *))
          and mergef (k, x1, x2, r1, r2, n, result) =
              (case mergeFn(k, x1, x2)
                 of NONE => merge (r1, r2, n, result)
                  | SOME y => merge (r1, r2, n+1, addItem(k, y, result))
                (* end case *));
          val (n, result) = merge (start m1, start m2, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end
    end (* local *)

    (* NOTE: renamed app => app', appi => app *)
    fun app' f = let
          fun appf E = ()
            | appf (T(_, a, _, x, b)) = (appf a; f x; appf b)
          in
            fn (MAP(_, m, _)) => appf m
          end
    fun app f = let
          fun appf E = ()
            | appf (T(_, a, xk, x, b)) = (appf a; f(xk, x); appf b)
          in
            fn (MAP(_, m, _)) => appf m
          end

    (* NOTE: renamed map => transform, mapi => map *)
    fun transform f = let
          fun mapf E = E
            | mapf (T(color, a, xk, x, b)) =
                T(color, mapf a, xk, f x, mapf b)
          in
            fn (MAP(n, m, compare)) => MAP(n, mapf m, compare)
          end
    fun map f = let
          fun mapf E = E
            | mapf (T(color, a, xk, x, b)) =
                T(color, mapf a, xk, f(xk, x), mapf b)
          in
            fn (MAP(n, m, compare)) => MAP(n, mapf m, compare)
          end

  (* Filter out those elements of the map that do not satisfy the
   * predicate.  The filtering is done in increasing map order.
   *)
    fun filter pred (MAP(_, t, compare)) = let
          fun walk (E, n, result) = (n, result)
            | walk (T(_, a, xk, x, b), n, result) = let
                val (n, result) = walk(a, n, result)
                in
                  if (pred x)
                    then walk(b, n+1, addItem(xk, x, result))
                    else walk(b, n, result)
                end
          val (n, result) = walk (t, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end
    fun filteri pred (MAP(_, t, compare)) = let
          fun walk (E, n, result) = (n, result)
            | walk (T(_, a, xk, x, b), n, result) = let
                val (n, result) = walk(a, n, result)
                in
                  if (pred(xk, x))
                    then walk(b, n+1, addItem(xk, x, result))
                    else walk(b, n, result)
                end
          val (n, result) = walk (t, 0, ZERO)
          in
            MAP(n, linkAll result, compare)
          end

  (* map a partial function over the elements of a map in increasing
   * map order.
   *)
    fun mapPartial f (m as MAP(_,_,compare)) = let
          fun f' (xk, x, m') = (case f x
                 of NONE => m'
                  | (SOME y) => insert(m', xk, y)
                (* end case *))
          in
            foldl f' (mkDict compare) m
          end
    fun mapPartiali f (m as MAP(_,_,compare)) = let
          fun f' (xk, x, m') = (case f(xk, x)
                 of NONE => m'
                  | (SOME y) => insert(m', xk, y)
                (* end case *))
          in
            foldl f' (mkDict compare) m
          end

  (* check the elements of a map with a predicate and return true if
   * any element satisfies the predicate. Return false otherwise.
   * Elements are checked in key order.
   *)
    fun exists pred = let
          fun exists' E = false
            | exists' (T(_, a, _, x, b)) = exists' a orelse pred x orelse exists' b
          in
            fn (MAP(_, m, _)) => exists' m
          end
    fun existsi pred = let
          fun exists' E = false
            | exists' (T(_, a, k, x, b)) = exists' a orelse pred(k, x) orelse exists' b
          in
            fn (MAP(_, m, _)) => exists' m
          end

  (* check the elements of a map with a predicate and return true if
   * they all satisfy the predicate. Return false otherwise.  Elements
   * are checked in key order.
   *)
    fun all pred = let
          fun all' E = true
            | all' (T(_, a, _, x, b)) = all' a andalso pred x andalso all' b
          in
            fn (MAP(_, m, _)) => all' m
          end
    fun alli pred = let
          fun all' E = true
            | all' (T(_, a, k, x, b)) = all' a andalso pred(k, x) andalso all' b
          in
            fn (MAP(_, m, _)) => all' m
          end

  (* Additional functions for compatibilities with the old Redblackmap *)
    fun revapp (f :'key * 'a -> unit) m =
        foldr (fn (k,x,_) => f (k,x)) () m

    fun insertList (m, pairs) =
        Portable.itlist (fn (k,x) => fn m' =>
                            insertWith (fn (x,y) => y) (m', k, x)) pairs m

    fun findKey (m,k) = (k,find (m,k))

    fun fromList compare pairs =
        insertList (mkDict compare, pairs)

    fun update (m, (k :'key), (f :'a option -> 'a)) =
        case peek(m, k) of
           NONE   => insert (m, k, f NONE)
         | SOME v => insertWith (fn (x,y) => y) (m, k, f (SOME v))

  end;

(* References:

  [1] Okasaki, C., 1999. Red-black trees in a functional setting. Journal of
      functional programming, 9(4), pp.471-477.

  [2] Hinze, R., 1999, May. Constructing red-black trees. In Proceedings of
      the Workshop on Algorithmic Aspects of Advanced Programming Languages,
      WAAAPL (Vol. 99, pp. 89-99).

  [3] Cormen, T.H., Leiserson, C.E., Rivest, R.L. and Stein, C., 2022.
      Introduction to algorithms. MIT press.
 *)
