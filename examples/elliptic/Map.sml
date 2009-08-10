(* ========================================================================= *)
(* FINITE MAPS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Map :> Map =
struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Bug = mlibUseful.Bug;

exception Error = mlibUseful.Error;

val pointerEqual = Portable.pointer_eq;

val K = mlibUseful.K;

val snd = mlibUseful.snd;

(* ------------------------------------------------------------------------- *)
(* Random search trees.                                                      *)
(* ------------------------------------------------------------------------- *)

type ('a,'b,'c) binaryNode =
     {size : int,
      priority : real,
      left : 'c,
      key : 'a,
      value : 'b,
      right : 'c};

datatype ('a,'b) tree = E | T of ('a, 'b, ('a,'b) tree) binaryNode;

type ('a,'b) node = ('a, 'b, ('a,'b) tree) binaryNode;

datatype ('a,'b) map = Map of ('a * 'a -> order) * ('a,'b) tree;

(* ------------------------------------------------------------------------- *)
(* Random priorities.                                                        *)
(* ------------------------------------------------------------------------- *)

local
  val randomPriority =
      let
        val gen = Random.newgenseed 2.0
      in
        fn () => Random.random gen
      end;

  val priorityOrder = Real.compare;
in
  fun treeSingleton (key,value) =
      T {size = 1, priority = randomPriority (),
         left = E, key = key, value = value, right = E};

  fun nodePriorityOrder cmp (x1 : ('a,'b) node, x2 : ('a,'b) node) =
      let
        val {priority = p1, key = k1, ...} = x1
        and {priority = p2, key = k2, ...} = x2
      in
        case priorityOrder (p1,p2) of
          LESS => LESS
        | EQUAL => cmp (k1,k2)
        | GREATER => GREATER
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun checkSizes E = 0
    | checkSizes (T {size,left,right,...}) =
      let
        val l = checkSizes left
        and r = checkSizes right
        val () = if l + 1 + r = size then () else raise Error "wrong size"
      in
        size
      end

  fun checkSorted _ x E = x
    | checkSorted cmp x (T {left,key,right,...}) =
      let
        val x = checkSorted cmp x left
        val () =
            case x of
              NONE => ()
            | SOME k =>
              case cmp (k,key) of
                LESS => ()
              | EQUAL => raise Error "duplicate keys"
              | GREATER => raise Error "unsorted"
      in
        checkSorted cmp (SOME key) right
      end;

  fun checkPriorities _ E = NONE
    | checkPriorities cmp (T (x as {left,right,...})) =
      let
        val () =
            case checkPriorities cmp left of
              NONE => ()
            | SOME l =>
              case nodePriorityOrder cmp (l,x) of
                LESS => ()
              | EQUAL => raise Error "left child has equal key"
              | GREATER => raise Error "left child has greater priority"
        val () =
            case checkPriorities cmp right of
              NONE => ()
            | SOME r =>
              case nodePriorityOrder cmp (r,x) of
                LESS => ()
              | EQUAL => raise Error "right child has equal key"
              | GREATER => raise Error "right child has greater priority"
      in
        SOME x
      end;
in
  fun checkWellformed s (m as Map (cmp,tree)) =
      (let
         val _ = checkSizes tree
         val _ = checkSorted cmp NONE tree
         val _ = checkPriorities cmp tree
         val () = print "."
       in
         m
       end
       handle Error err => raise Bug err)
      handle Bug bug =>
        raise Bug ("RandomMap.checkWellformed: " ^ bug ^ " (" ^ s ^ ")");
end;

fun comparison (Map (cmp,_)) = cmp;

fun new cmp = Map (cmp,E);

fun treeSize E = 0
  | treeSize (T {size = s, ...}) = s;

fun size (Map (_,tree)) = treeSize tree;

fun mkT p l k v r =
    T {size = treeSize l + 1 + treeSize r, priority = p,
       left = l, key = k, value = v, right = r};

fun singleton cmp key_value = Map (cmp, treeSingleton key_value);

local
  fun treePeek cmp E pkey = NONE
    | treePeek cmp (T {left,key,value,right,...}) pkey =
      case cmp (pkey,key) of
        LESS => treePeek cmp left pkey
      | EQUAL => SOME value
      | GREATER => treePeek cmp right pkey
in
  fun peek (Map (cmp,tree)) key = treePeek cmp tree key;
end;

(* treeAppend assumes that every element of the first tree is less than *)
(* every element of the second tree. *)

fun treeAppend _ t1 E = t1
  | treeAppend _ E t2 = t2
  | treeAppend cmp (t1 as T x1) (t2 as T x2) =
    case nodePriorityOrder cmp (x1,x2) of
      LESS =>
      let
        val {priority = p2,
             left = l2, key = k2, value = v2, right = r2, ...} = x2
      in
        mkT p2 (treeAppend cmp t1 l2) k2 v2 r2
      end
    | EQUAL => raise Bug "RandomSet.treeAppend: equal keys"
    | GREATER =>
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
      in
        mkT p1 l1 k1 v1 (treeAppend cmp r1 t2)
      end;

(* nodePartition splits the node into three parts: the keys comparing less *)
(* than the supplied key, an optional equal key, and the keys comparing *)
(* greater. *)

local
  fun mkLeft [] t = t
    | mkLeft (({priority,left,key,value,...} : ('a,'b) node) :: xs) t =
      mkLeft xs (mkT priority left key value t);

  fun mkRight [] t = t
    | mkRight (({priority,key,value,right,...} : ('a,'b) node) :: xs) t =
      mkRight xs (mkT priority t key value right);

  fun treePart _ _ lefts rights E = (mkLeft lefts E, NONE, mkRight rights E)
    | treePart cmp pkey lefts rights (T x) = nodePart cmp pkey lefts rights x
  and nodePart cmp pkey lefts rights (x as {left,key,value,right,...}) =
      case cmp (pkey,key) of
        LESS => treePart cmp pkey lefts (x :: rights) left
      | EQUAL => (mkLeft lefts left, SOME (key,value), mkRight rights right)
      | GREATER => treePart cmp pkey (x :: lefts) rights right;
in
  fun nodePartition cmp x pkey = nodePart cmp pkey [] [] x;
end;

(* union first calls treeCombineRemove, to combine the values *)
(* for equal keys into the first map and remove them from the second map. *)
(* Note that the combined key is always the one from the second map. *)

local
  fun treeCombineRemove _ _ t1 E = (t1,E)
    | treeCombineRemove _ _ E t2 = (E,t2)
    | treeCombineRemove cmp f (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
        val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        val (l1,l2) = treeCombineRemove cmp f l1 l2
        and (r1,r2) = treeCombineRemove cmp f r1 r2
      in
        case k2_v2 of
          NONE =>
          if treeSize l2 + treeSize r2 = #size x2 then (t1,t2)
          else (mkT p1 l1 k1 v1 r1, treeAppend cmp l2 r2)
        | SOME (k2,v2) =>
          case f (v1,v2) of
            NONE => (treeAppend cmp l1 r1, treeAppend cmp l2 r2)
          | SOME v => (mkT p1 l1 k2 v r1, treeAppend cmp l2 r2)
      end;

  fun treeUnionDisjoint _ t1 E = t1
    | treeUnionDisjoint _ E t2 = t2
    | treeUnionDisjoint cmp (T x1) (T x2) =
      case nodePriorityOrder cmp (x1,x2) of
        LESS => nodeUnionDisjoint cmp x2 x1
      | EQUAL => raise Bug "RandomSet.unionDisjoint: equal keys"
      | GREATER => nodeUnionDisjoint cmp x1 x2
  and nodeUnionDisjoint cmp x1 x2 =
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
        val (l2,_,r2) = nodePartition cmp x2 k1
        val l = treeUnionDisjoint cmp l1 l2
        and r = treeUnionDisjoint cmp r1 r2
      in
        mkT p1 l k1 v1 r
      end;
in
  fun union f (m1 as Map (cmp,t1)) (Map (_,t2)) =
      if pointerEqual (t1,t2) then m1
      else
        let
          val (t1,t2) = treeCombineRemove cmp f t1 t2
        in
          Map (cmp, treeUnionDisjoint cmp t1 t2)
        end;
end;

(*
val union =
    fn f => fn t1 => fn t2 =>
    checkWellformed
      "after union"
      (union f (checkWellformed "before union 1" t1)
               (checkWellformed "before union 2" t2));
*)

(* intersect is a simple case of the union algorithm. *)

local
  fun treeIntersect _ _ _ E = E
    | treeIntersect _ _ E _ = E
    | treeIntersect cmp f (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
        val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        val l = treeIntersect cmp f l1 l2
        and r = treeIntersect cmp f r1 r2
      in
        case k2_v2 of
          NONE => treeAppend cmp l r
        | SOME (k2,v2) =>
          case f (v1,v2) of
            NONE => treeAppend cmp l r
          | SOME v => mkT p1 l k2 v r
      end;
in
  fun intersect f (m1 as Map (cmp,t1)) (Map (_,t2)) =
      if pointerEqual (t1,t2) then m1
      else Map (cmp, treeIntersect cmp f t1 t2);
end;

(*
val intersect =
    fn f => fn t1 => fn t2 =>
    checkWellformed
      "after intersect"
      (intersect f (checkWellformed "before intersect 1" t1)
                   (checkWellformed "before intersect 2" t2));
*)

(* delete raises an exception if the supplied key is not found, which *)
(* makes it simpler to maximize sharing. *)

local
  fun treeDelete _ E _ = raise Error "RandomMap.delete: element not found"
    | treeDelete cmp (T {priority,left,key,value,right,...}) dkey =
      case cmp (dkey,key) of
        LESS => mkT priority (treeDelete cmp left dkey) key value right
      | EQUAL => treeAppend cmp left right
      | GREATER => mkT priority left key value (treeDelete cmp right dkey);
in
  fun delete (Map (cmp,tree)) key = Map (cmp, treeDelete cmp tree key);
end;

(*
val delete =
    fn t => fn x =>
    checkWellformed
      "after delete" (delete (checkWellformed "before delete" t) x);
*)

(* Set difference is mainly used when using maps as sets *)

local
  fun treeDifference _ t1 E = t1
    | treeDifference _ E _ = E
    | treeDifference cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, priority = p1,
             left = l1, key = k1, value = v1, right = r1} = x1
        val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        val l = treeDifference cmp l1 l2
        and r = treeDifference cmp r1 r2
      in
        if Option.isSome k2_v2 then treeAppend cmp l r
        else if treeSize l + treeSize r + 1 = s1 then t1
        else mkT p1 l k1 v1 r
      end;
in
  fun difference (Map (cmp,tree1)) (Map (_,tree2)) =
      if pointerEqual (tree1,tree2) then Map (cmp,E)
      else Map (cmp, treeDifference cmp tree1 tree2);
end;

(*
val difference =
    fn t1 => fn t2 =>
    checkWellformed
      "after difference"
      (difference (checkWellformed "before difference 1" t1)
                  (checkWellformed "before difference 2" t2));
*)

(* subsetDomain is mainly used when using maps as sets. *)

local
  fun treeSubsetDomain _ E _ = true
    | treeSubsetDomain _ _ E = false
    | treeSubsetDomain cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 <= s2 andalso
        let
          val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2_v2 andalso
          treeSubsetDomain cmp l1 l2 andalso
          treeSubsetDomain cmp r1 r2
        end
      end;
in
  fun subsetDomain (Map (cmp,tree1)) (Map (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeSubsetDomain cmp tree1 tree2
end;

(* equalDomain is mainly used when using maps as sets. *)

local
  fun treeEqualDomain _ E _ = true
    | treeEqualDomain _ _ E = false
    | treeEqualDomain cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 = s2 andalso
        let
          val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2_v2 andalso
          treeEqualDomain cmp l1 l2 andalso
          treeEqualDomain cmp r1 r2
        end
      end;
in
  fun equalDomain (Map (cmp,tree1)) (Map (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeEqualDomain cmp tree1 tree2
end;

(* mapPartial is the basic function for preserving the tree structure. *)
(* It applies the argument function to the elements *in order*. *)

local
  fun treeMapPartial cmp _ E = E
    | treeMapPartial cmp f (T {priority,left,key,value,right,...}) =
      let
        val left = treeMapPartial cmp f left
        and value' = f (key,value)
        and right = treeMapPartial cmp f right
      in
        case value' of
          NONE => treeAppend cmp left right
        | SOME value => mkT priority left key value right
      end;
in
  fun mapPartial f (Map (cmp,tree)) = Map (cmp, treeMapPartial cmp f tree);
end;

(* map is a primitive function for efficiency reasons. *)
(* It also applies the argument function to the elements *in order*. *)

local
  fun treeMap _ E = E
    | treeMap f (T {size,priority,left,key,value,right}) =
      let
        val left = treeMap f left
        and value = f (key,value)
        and right = treeMap f right
      in
        T {size = size, priority = priority, left = left,
           key = key, value = value, right = right}
      end;
in
  fun map f (Map (cmp,tree)) = Map (cmp, treeMap f tree);
end;

(* nth picks the nth smallest key/value (counting from 0). *)


local
  fun treeNth E _ = raise Error "RandomMap.nth"
    | treeNth (T {left,key,value,right,...}) n =
      let
        val k = treeSize left
      in
        if n = k then (key,value)
        else if n < k then treeNth left n
        else treeNth right (n - (k + 1))
      end;
in
  fun nth (Map (_,tree)) n = treeNth tree n;
end;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

fun leftSpine E acc = acc
  | leftSpine (t as T {left,...}) acc = leftSpine left (t :: acc);

fun rightSpine E acc = acc
  | rightSpine (t as T {right,...}) acc = rightSpine right (t :: acc);

datatype ('key,'a) iterator =
    LR of ('key * 'a) * ('key,'a) tree * ('key,'a) tree list
  | RL of ('key * 'a) * ('key,'a) tree * ('key,'a) tree list;

fun mkLR [] = NONE
  | mkLR (T {key,value,right,...} :: l) = SOME (LR ((key,value),right,l))
  | mkLR (E :: _) = raise Bug "RandomMap.mkLR";

fun mkRL [] = NONE
  | mkRL (T {key,value,left,...} :: l) = SOME (RL ((key,value),left,l))
  | mkRL (E :: _) = raise Bug "RandomMap.mkRL";

fun mkIterator (Map (_,tree)) = mkLR (leftSpine tree []);

fun mkRevIterator (Map (_,tree)) = mkRL (rightSpine tree []);

fun readIterator (LR (key_value,_,_)) = key_value
  | readIterator (RL (key_value,_,_)) = key_value;

fun advanceIterator (LR (_,next,l)) = mkLR (leftSpine next l)
  | advanceIterator (RL (_,next,l)) = mkRL (rightSpine next l);

(* ------------------------------------------------------------------------- *)
(* Derived operations.                                                       *)
(* ------------------------------------------------------------------------- *)

fun null m = size m = 0;

fun get m key =
    case peek m key of
      NONE => raise Error "RandomMap.get: element not found"
    | SOME value => value;

fun inDomain key m = Option.isSome (peek m key);

fun insert m key_value =
    union (SOME o snd) m (singleton (comparison m) key_value);

(*
val insert =
    fn m => fn x =>
    checkWellformed
      "after insert" (insert (checkWellformed "before insert" m) x);
*)

local
  fun fold _ NONE acc = acc
    | fold f (SOME iter) acc =
      let
        val (key,value) = readIterator iter
      in
        fold f (advanceIterator iter) (f (key,value,acc))
      end;
in
  fun foldl f b m = fold f (mkIterator m) b;

  fun foldr f b m = fold f (mkRevIterator m) b;
end;

local
  fun find _ NONE = NONE
    | find pred (SOME iter) =
      let
        val key_value = readIterator iter
      in
        if pred key_value then SOME key_value
        else find pred (advanceIterator iter)
      end;
in
  fun findl p m = find p (mkIterator m);

  fun findr p m = find p (mkRevIterator m);
end;

fun fromList cmp l = List.foldl (fn (k_v,m) => insert m k_v) (new cmp) l;

fun insertList m l = union (SOME o snd) m (fromList (comparison m) l);

fun filter p =
    let
      fun f (key_value as (_,value)) =
          if p key_value then SOME value else NONE
    in
      mapPartial f
    end;

fun app f m = foldl (fn (key,value,()) => f (key,value)) () m;

fun transform f = map (fn (_,value) => f value);

fun toList m = foldr (fn (key,value,l) => (key,value) :: l) [] m;

fun domain m = foldr (fn (key,_,l) => key :: l) [] m;

fun exists p m = Option.isSome (findl p m);

fun all p m = not (exists (not o p) m);

local
  fun iterCompare _ _ NONE NONE = EQUAL
    | iterCompare _ _ NONE (SOME _) = LESS
    | iterCompare _ _ (SOME _) NONE = GREATER
    | iterCompare kcmp vcmp (SOME i1) (SOME i2) =
      keyIterCompare kcmp vcmp (readIterator i1) (readIterator i2) i1 i2
  and keyIterCompare kcmp vcmp (k1,v1) (k2,v2) i1 i2 =
      case kcmp (k1,k2) of
        LESS => LESS
      | EQUAL =>
        (case vcmp (v1,v2) of
           LESS => LESS
         | EQUAL =>
           iterCompare kcmp vcmp (advanceIterator i1) (advanceIterator i2)
         | GREATER => GREATER)
      | GREATER => GREATER;
in
  fun compare cmp (m1,m2) =
      iterCompare (comparison m1) cmp (mkIterator m1) (mkIterator m2);
end;

end
