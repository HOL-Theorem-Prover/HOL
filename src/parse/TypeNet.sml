structure TypeNet :> TypeNet =
struct

open HolKernel

datatype label = TV
               | TOP of {Thy : string, Tyop : string} * int
  (* The integer records arity of operator - this is necessary when
     types are redefined.  If the old and new versions have the
     same arity, all is well, but if they are different then the data
     structure expects the wrong thing.

     For example, if scratch$foo is of arity 1, then there will be a
     ND node beneath it (where the argument gets treated).  But if
     the user dumps that foo, and replaces it with one of arity 0, an
     attempt to follow the tree will find the node that was right before
     when it should be a leaf.

     If the user does a lot of this, the data structure will slowly fill
     up with garbage.  If a type gets replaced with a new one of the same
     arity, the data for the old type will be returned as part of a
     Binarymap.listItems when "match" is called, but the user will eliminate
     the junk with the usual sort of call to match_type.  With "peek", the
     old data won't be called because the lookup at the leaf's Binarymap
     will just find whatever's supposed to be associated with the new type.
  *)

fun reccmp ({Thy=th1,Tyop=op1}, {Thy=th2,Tyop=op2}) =
    pair_compare(String.compare, String.compare) ((op1,th1),(op2,th2))

fun labcmp p =
    case p of
      (TV, TV) => EQUAL
    | (TV, TOP _) => LESS
    | (TOP opdata1, TOP opdata2) =>
         pair_compare(reccmp, Int.compare) (opdata1, opdata2)
    | (TOP _, TV) => GREATER

datatype 'a N = LF of (hol_type,'a) Binarymap.dict
              | ND of (label,'a N) Binarymap.dict
              | EMPTY
(* redundant EMPTY constructor is used to get around value polymorphism problem
   when creating a single value for empty below *)

type 'a typenet = 'a N * int

val empty = (EMPTY, 0)

fun mkempty () = ND (Binarymap.mkDict labcmp)

fun ndest_type ty =
    if is_vartype ty then (TV, [])
    else let
        val  {Thy,Tyop,Args} = dest_thy_type ty
      in
        (TOP({Thy=Thy,Tyop=Tyop},length Args), Args)
      end

fun insert ((net,sz), ty, item) = let
  fun newnode labs =
      case labs of
        [] => LF (Binarymap.mkDict Type.compare)
      | _ => mkempty()
  fun trav (net, tys) =
      case (net, tys) of
        (LF d, []) => LF (Binarymap.insert(d,ty,item))
      | (ND d, ty::tys0) => let
          val (lab, rest) = ndest_type ty
          val tys = rest @ tys0
          val n' =
              case Binarymap.peek(d,lab) of
                NONE => trav(newnode tys, tys)
              | SOME n => trav(n, tys)
          val d' = Binarymap.insert(d, lab, n')
        in
          ND d'
        end
      | (EMPTY, tys) => trav(mkempty(), tys)
      | _ => raise Fail "TypeNet.insert: catastrophic invariant failure"
in
  (trav(net,[ty]), sz + 1)
end

fun listItems (net, sz) = let
  fun cons'(k,v,acc) = (k,v)::acc
  fun trav (net, acc) =
      case net of
        LF d => Binarymap.foldl cons' acc d
      | ND d => let
          fun foldthis (k,v,acc) = trav(v,acc)
        in
          Binarymap.foldl foldthis acc d
        end
      | EMPTY => []
in
  trav(net, [])
end

fun numItems (net, sz) = sz

fun peek ((net,sz), ty) = let
  fun trav (net, tys) =
      case (net, tys) of
        (LF d, []) => Binarymap.peek(d, ty)
      | (ND d, ty::tys) => let
          val (lab, rest) = ndest_type ty
        in
          case Binarymap.peek(d, lab) of
            NONE => NONE
          | SOME n => trav(n, rest @ tys)
        end
      | (EMPTY, _) => NONE
      | _ => raise Fail "TypeNet.peek: catastrophic invariant failure"
in
  trav(net, [ty])
end

fun find (n, ty) =
    valOf (peek (n, ty)) handle Option => raise Binarymap.NotFound

fun match ((net,sz), ty) = let
  fun trav acc (net, tyl) =
      case (net, tyl) of
        (EMPTY, _) => []
      | (LF d, []) => Binarymap.listItems d @ acc
      | (ND d, ty::tys) => let
          val varresult = case Binarymap.peek(d, TV) of
                            NONE => acc
                          | SOME n => trav acc (n, tys)
          val (lab, rest) = ndest_type ty
        in
          case lab of
            TV => varresult
          | TOP _ => let
            in
              case Binarymap.peek (d, lab) of
                NONE => varresult
              | SOME n => trav varresult (n, rest @ tys)
            end
        end
      | _ => raise Fail "TypeNet.match: catastrophic invariant failure"
in
  trav [] (net, [ty])
end

fun delete ((net,sz), ty) = let
  fun trav (p as (net, tyl)) =
      case p of
        (EMPTY, _) => raise Binarymap.NotFound
      | (LF d, []) => let
          val (d',removed) = Binarymap.remove(d, ty)
        in
          if Binarymap.numItems d' = 0 then (NONE, removed)
          else (SOME (LF d'), removed)
        end
      | (ND d, ty::tys) => let
          val (lab, rest) = ndest_type ty
        in
          case Binarymap.peek(d, lab) of
            NONE => raise Binarymap.NotFound
          | SOME n => let
            in
              case trav (n, rest @ tys) of
                (NONE, removed) => let
                  val (d',_) = Binarymap.remove(d, lab)
                in
                  if Binarymap.numItems d' = 0 then (NONE, removed)
                  else (SOME (ND d'), removed)
                end
              | (SOME n', removed) => (SOME (ND (Binarymap.insert(d,lab,n'))),
                                       removed)
            end
        end
      | _ => raise Fail "TypeNet.delete: catastrophic invariant failure"
in
  case trav (net, [ty]) of
    (NONE, removed) => (empty, removed)
  | (SOME n, removed) =>  ((n,sz-1), removed)
end

fun app f (net, sz) = let
  fun trav n =
      case n of
        LF d => Binarymap.app f d
      | ND d => Binarymap.app (fn (lab, n) => trav n) d
      | EMPTY => ()
in
  trav net
end

fun fold f acc (net, sz) = let
  fun trav acc n =
      case n of
        LF d => Binarymap.foldl f acc d
      | ND d => Binarymap.foldl (fn (lab,n',acc) => trav acc n') acc d
      | EMPTY => acc
in
  trav acc net
end

fun map f (net, sz) = let
  fun trav n =
      case n of
        LF d => LF (Binarymap.map f d)
      | ND d => ND (Binarymap.transform trav d)
      | EMPTY => EMPTY
in
  (trav net, sz)
end

fun transform f = map (fn (k,v) => f v)


end (* struct *)
