(* ========================================================================= *)
(* FINITE MAPS WITH RANDOMLY BALANCED TREES                                  *)
(* Implemented by Joe Hurd, 2006                                             *)
(* ========================================================================= *)

structure Randomset :> Randomset =
struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Bug of string;

exception NotFound;

fun snd (_,x) = x;

(* ------------------------------------------------------------------------- *)
(* Random priorities.                                                        *)
(* ------------------------------------------------------------------------- *)

local
  val MAXIMUM_PRIORITY = 1000000;
  val gen = Random.newgenseed 2.0;
in
  fun randomPriority () = Random.range (0,MAXIMUM_PRIORITY) gen;
end;

fun priorityOrder cmp ((p1,k1),(p2,k2)) =
    case Int.compare (p1,p2) of
      LESS => LESS
    | EQUAL => cmp (k1,k2)
    | GREATER => GREATER;

(* ------------------------------------------------------------------------- *)
(* Random search trees.                                                      *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) binaryNode =
     {size : int,
      priority : int,
      left : 'b,
      key : 'a,
      right : 'b};

datatype 'a tree = E | T of ('a, 'a tree) binaryNode;

type 'a node = ('a, 'a tree) binaryNode;

datatype 'a set = Set of ('a * 'a -> order) * 'a tree;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun nodePriorityOrder cmp (x1 : 'a node, x2 : 'a node) =
    let
      val {priority = p1, key = k1, ...} = x1
      and {priority = p2, key = k2, ...} = x2
    in
      priorityOrder cmp ((p1,k1),(p2,k2))
    end;

local
  fun checkSizes E = 0
    | checkSizes (T {size,left,right,...}) =
      let
        val l = checkSizes left
        and r = checkSizes right
        val () = if l + 1 + r = size then () else raise Bug "wrong size"
      in
        size
      end

  fun checkSorted _ E x = x
    | checkSorted cmp (T {left,key,right,...}) x =
      let
        val x = checkSorted cmp left x
        val ok = case x of NONE => true | SOME k => cmp (k,key) = LESS
      in
        if not ok then raise Bug "unsorted"
        else checkSorted cmp right (SOME key)
      end;

  fun checkPriorities _ E = NONE
    | checkPriorities cmp (T (x as {left,right,...})) =
      let
        val () =
            case checkPriorities cmp left of
              NONE => ()
            | SOME l => if nodePriorityOrder cmp (l,x) = LESS then ()
                        else raise Bug "left out of order"
        val () =
            case checkPriorities cmp right of
              NONE => ()
            | SOME r => if nodePriorityOrder cmp (r,x) = LESS then ()
                        else raise Bug "right out of order"
      in
        SOME x
      end;
in
  fun checkWellformed s (Set (cmp,t)) =
      let
        val _ = checkSizes t
        val _ = checkSorted cmp t NONE
        val _ = checkPriorities cmp t
        val () = print "."
      in
        t
      end
      handle Bug bug =>
        raise Bug ("Randomset.checkWellformed: " ^ bug ^ " (" ^ s ^ ")");
end;

fun empty cmp = Set (cmp,E);

fun size E = 0
  | size (T {size = s, ...}) = s;

fun numItems (Set (_,t)) = size t;

fun mkT p l k r =
    T {size = size l + 1 + size r, priority = p, left = l, key = k, right = r};

fun singleton cmp key =
    Set (cmp, T {size = 1, priority = randomPriority (), left = E,
                 key = key, right = E});

local
  fun treePeek _ E _ = NONE
    | treePeek cmp (T {left,key,right,...}) pkey =
      case cmp (pkey,key) of
        LESS => treePeek cmp left pkey
      | EQUAL => SOME key
      | GREATER => treePeek cmp right pkey;
in
  fun peek (Set (cmp,t), k) = treePeek cmp t k;
end;

(* append assumes that every element of the first tree is less than every *)
(* element of the second tree. If this is not the case, use union instead. *)

fun treeAppend _ t1 E = t1
  | treeAppend _ E t2 = t2
  | treeAppend cmp (t1 as T x1) (t2 as T x2) =
    let
      val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
      and {priority = p2, left = l2, key = k2, right = r2, ...} = x2
    in
      case nodePriorityOrder cmp (x1,x2) of
        LESS => mkT p2 (treeAppend cmp t1 l2) k2 r2
      | EQUAL => raise Bug "Randomset.treeAppend: equal keys"
      | GREATER => mkT p1 l1 k1 (treeAppend cmp r1 t2)
    end;

(* partition splits the map into three sets: the keys comparing less *)
(* than the supplied key, an optional equal key, and the keys comparing *)
(* greater. *)

local
  fun mkLeft [] t = t
    | mkLeft (({priority,left,key,...} : 'a node) :: xs) t =
      mkLeft xs (mkT priority left key t);

  fun mkRight [] t = t
    | mkRight (({priority,key,right,...} : 'a node) :: xs) t =
      mkRight xs (mkT priority t key right);

  fun treePart _ _ lefts rights E = (mkLeft lefts E, NONE, mkRight rights E)
    | treePart cmp pkey lefts rights (T x) = nodePart cmp pkey lefts rights x
  and nodePart cmp pkey lefts rights (x as {priority,left,key,right,...}) =
      case cmp (pkey,key) of
        LESS => treePart cmp pkey lefts (x :: rights) left
      | EQUAL => (mkLeft lefts left, SOME key, mkRight rights right)
      | GREATER => treePart cmp pkey (x :: lefts) rights right;
in
  fun treePartition cmp t pkey = treePart cmp pkey [] [] t;

  fun nodePartition cmp x pkey = nodePart cmp pkey [] [] x;
end;

(* union first calls combineRemove, to combine the values *)
(* for equal keys into the first map and remove them from the second map. *)
(* Note that the combined key is always the one from the second map. *)

local
  fun combineRemove _ t1 E = (t1,E)
    | combineRemove _ E t2 = (E,t2)
    | combineRemove cmp (t1 as T x1) (t2 as T x2) =
      if Portable.pointer_eq (x1,x2) then (t2,E)
      else
        let
          val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
          val (l2,k2,r2) = nodePartition cmp x2 k1
          val (l1,l2) = combineRemove cmp l1 l2
          and (r1,r2) = combineRemove cmp r1 r2
        in
          case k2 of
            NONE => if size l2 + size r2 = #size x2 then (t1,t2)
                    else (mkT p1 l1 k1 r1, treeAppend cmp l2 r2)
          | SOME k2 => (mkT p1 l1 k2 r1, treeAppend cmp l2 r2)
        end;

  fun unionDisjoint _ t1 E = t1
    | unionDisjoint _ E t2 = t2
    | unionDisjoint cmp (T x1) (T x2) =
      case nodePriorityOrder cmp (x1,x2) of
        LESS => nodeUnionDisjoint cmp x2 x1
      | EQUAL => raise Bug "Randomset.unionDisjoint: equal keys"
      | GREATER => nodeUnionDisjoint cmp x1 x2
  and nodeUnionDisjoint cmp x1 x2 =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,_,r2) = nodePartition cmp x2 k1
      in
        mkT p1 (unionDisjoint cmp l1 l2) k1 (unionDisjoint cmp r1 r2)
      end;
in
  fun union (Set (cmp,t1), Set (_,t2)) =
      let
        val (t1,t2) = combineRemove cmp t1 t2
      in
        Set (cmp, unionDisjoint cmp t1 t2)
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
  fun treeIntersect _ _ E = E
    | treeIntersect _ E _ = E
    | treeIntersect cmp (t1 as T x1) (t2 as T x2) =
      if Portable.pointer_eq (x1,x2) then t2
      else
        let
          val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
          val (l2,k2,r2) = nodePartition cmp x2 k1
          val l1 = treeIntersect cmp l1 l2
          and r1 = treeIntersect cmp r1 r2
        in
          case k2 of
            NONE => treeAppend cmp l1 r1
          | SOME k2 => mkT p1 l1 k2 r1
        end;
in
 fun intersection (Set (cmp,t1), Set (_,t2)) =
     Set (cmp, treeIntersect cmp t1 t2);
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
  fun treeDelete _ E _ = raise NotFound
    | treeDelete cmp (T {priority,left,key,right,...}) dkey =
      case cmp (dkey,key) of
        LESS => mkT priority (treeDelete cmp left dkey) key right
      | EQUAL => treeAppend cmp left right
      | GREATER => mkT priority left key (treeDelete cmp right dkey);
in
  fun delete (Set (cmp,t), k) = Set (cmp, treeDelete cmp t k);
end;
 
(*
val delete =
    fn t => fn x =>
    checkWellformed
      "after delete" (delete (checkWellformed "before delete" t) x);
*)

(* difference is mainly used when using maps as sets. *)

local
  fun treeDifference _ t1 E = t1
    | treeDifference _ E _ = E
    | treeDifference cmp (t1 as T x1) (T x2) =
      if Portable.pointer_eq (x1,x2) then E
      else
        let
          val {size = s1, priority = p1, left = l1, key = k1, right = r1} = x1
          val (l2,k2,r2) = nodePartition cmp x2 k1
          val l1 = treeDifference cmp l1 l2
          and r1 = treeDifference cmp r1 r2
        in
          if Option.isSome k2 then treeAppend cmp l1 r1
          else if size l1 + size r1 + 1 = s1 then t1
          else mkT p1 l1 k1 r1
        end;
in
  fun difference (Set (cmp,t1), Set (_,t2)) =
      Set (cmp, treeDifference cmp t1 t2);
end;

(*
val difference =
    fn t1 => fn t2 =>
    checkWellformed
      "after difference"
      (difference (checkWellformed "before difference 1" t1)
                  (checkWellformed "before difference 2" t2));
*)

(* isSubset uses tricks to short-circuit the check. *)

local
  fun subset _ E _ = true
    | subset _ _ E = false
    | subset cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        Portable.pointer_eq (x1,x2) orelse
        (s1 <= s2 andalso
         let
           val (l2,k2_v2,r2) = nodePartition cmp x2 k1
         in
           Option.isSome k2_v2 andalso
           subset cmp l1 l2 andalso subset cmp r1 r2
         end)
      end;
in
  fun isSubset (Set (cmp,s1), Set (_,s2)) = subset cmp s1 s2;
end;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

fun leftSpine E acc = acc
  | leftSpine (t as T {left,...}) acc = leftSpine left (t :: acc);

fun rightSpine E acc = acc
  | rightSpine (t as T {right,...}) acc = rightSpine right (t :: acc);

datatype 'a iterator =
    LR of 'a * 'a tree * 'a tree list
  | RL of 'a * 'a tree * 'a tree list;

fun mkLR [] = NONE
  | mkLR (T {key,right,...} :: l) = SOME (LR (key,right,l))
  | mkLR (E :: _) = raise Bug "Randomset.mkLR";

fun mkRL [] = NONE
  | mkRL (T {key,left,...} :: l) = SOME (RL (key,left,l))
  | mkRL (E :: _) = raise Bug "Randomset.mkRL";

fun mkIterator (Set (_,t)) = mkLR (leftSpine t []);

fun mkRevIterator (Set (_,t)) = mkRL (rightSpine t []);

fun readIterator (LR (key_value,_,_)) = key_value
  | readIterator (RL (key_value,_,_)) = key_value;

fun advanceIterator (LR (_,next,l)) = mkLR (leftSpine next l)
  | advanceIterator (RL (_,next,l)) = mkRL (rightSpine next l);

(* ------------------------------------------------------------------------- *)
(* Derived operations.                                                       *)
(* ------------------------------------------------------------------------- *)

fun isEmpty s = numItems s = 0;

fun retrieve (s,k) = case peek (s,k) of NONE => raise NotFound | SOME k => k;

fun member (s,k) = Option.isSome (peek (s,k));

fun add (s as Set (cmp,_), k) = union (s, singleton cmp k);

local
  fun fold _ NONE acc = acc
    | fold f (SOME iter) acc =
      fold f (advanceIterator iter) (f (readIterator iter, acc));
in
  fun foldl f b m = fold f (mkIterator m) b;

  fun foldr f b m = fold f (mkRevIterator m) b;
end;

local
  fun findi _ NONE = NONE
    | findi pred (SOME iter) =
      let
        val key = readIterator iter
      in
        if pred key then SOME key
        else findi pred (advanceIterator iter)
      end;
in
  fun find p m = findi p (mkIterator m);
end;

fun addList (s,l) = List.foldl (fn (k,z) => add (z,k)) s l;

fun listItems s = foldr op:: [] s;

fun equal (s1,s2) =
    Portable.pointer_eq (s1,s2) orelse
    (numItems s1 = numItems s2 andalso
     isSubset (s1,s2) andalso isSubset (s2,s1));

fun app f s = foldl (fn (k,()) => f k) () s;

fun revapp f s = foldr (fn (k,()) => f k) () s;

end
