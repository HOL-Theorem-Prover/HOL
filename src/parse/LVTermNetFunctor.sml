signature SET =
sig

  type value
  type set
  val empty : set
  val insert : set * value -> set
  val fold : (value * 'a -> 'a) -> 'a -> set -> 'a
  val listItems : set -> value list

end

signature LV_TERM_NET =
sig

  (* signature names modelled on Binarymap's *)
  type lvtermnet
  type term = Term.term
  type key = Term.term list * Term.term
  type value
  type set

  val empty : lvtermnet
  val insert : (lvtermnet * key * value) -> lvtermnet
  val find : lvtermnet * key -> set
  val peek : lvtermnet * key -> set
  val match : lvtermnet * term -> (key * value) list

  val delete : lvtermnet * key -> lvtermnet * set
  val numItems : lvtermnet -> int
  val listItems : lvtermnet -> (key * value) list
  val app : (key * set -> unit) -> lvtermnet -> unit
  val fold : (key * value * 'b -> 'b) -> 'b -> lvtermnet -> 'b

end

functor LVTermNetFunctor(S : SET) : LV_TERM_NET =
struct

open HolKernel

datatype label = V of int
               | C of {Name : string, Thy : string} * int
               | Lam of int
               | LV of string * int
type key = term list * term
type value = S.value
type set = S.set

val tlt_compare = pair_compare (list_compare Term.compare, Term.compare)

fun labcmp (p as (l1, l2)) =
    case p of
      (V n1, V n2) => Int.compare(n1, n2)
    | (V _, _) => LESS
    | (_, V _) => GREATER
    | (C ({Name=nm1,Thy=th1}, n1), C ({Name=nm2,Thy=th2}, n2)) =>
         pair_compare (Int.compare,
                       pair_compare (String.compare, String.compare))
                      ((n1, (th1, nm1)), (n2, (th2, nm2)))
    | (C _, _) => LESS
    | (_, C _) => GREATER
    | (Lam n1, Lam n2) => Int.compare (n1, n2)
    | (Lam _, _) => LESS
    | (_, Lam _) => GREATER
    | (LV p1, LV p2) => pair_compare (String.compare, Int.compare) (p1, p2)

datatype N = LF of (key,S.set) Binarymap.dict
           | ND of (label,N) Binarymap.dict

type lvtermnet = N * int

val empty_node = ND (Binarymap.mkDict labcmp)
val empty = (empty_node, 0)

fun ndest_term (fvs, tm) = let
  val (f, args) = strip_comb tm
  val args' = map (fn t => (fvs, t)) args
in
  case dest_term f of
    VAR(s, ty) => if mem tm fvs then (LV (s, length args), args')
                  else (V (length args), args')
  | LAMB(bv, bod) => (Lam (length args), (subtract fvs [bv], bod) :: args')
  | CONST{Name,Thy,Ty} => (C ({Name=Name,Thy=Thy}, length args), args')
  | COMB _ => raise Fail "impossible"
end

fun cons_insert (bmap, k, i) =
    case Binarymap.peek(bmap,k) of
      NONE => Binarymap.insert(bmap,k,S.insert(S.empty,i))
    | SOME items => Binarymap.insert(bmap,k,S.insert(items, i))

fun insert ((net,sz), k, item) = let
  fun newnode labs =
      case labs of
        [] => LF (Binarymap.mkDict tlt_compare)
      | _ => empty_node
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => LF (cons_insert(d,k,item))
      | (ND d, k::ks0) => let
          val (lab, rest) = ndest_term k
          val ks = rest @ ks0
          val n' =
              case Binarymap.peek(d,lab) of
                NONE => trav(newnode ks, ks)
              | SOME n => trav(n, ks)
        in
          ND (Binarymap.insert(d, lab, n'))
        end
      | _ => raise Fail "LVTermNet.insert: catastrophic invariant failure"
in
  (trav(net,[k]), sz + 1)
end

fun listItems (net, sz) = let
  fun cons'(k,vs,acc) = S.fold (fn (v,acc) => (k,v)::acc) acc vs
  fun trav (net, acc) =
      case net of
        LF d => Binarymap.foldl cons' acc d
      | ND d => let
          fun foldthis (k,v,acc) = trav(v,acc)
        in
          Binarymap.foldl foldthis acc d
        end
in
  trav(net, [])
end

fun numItems (net, sz) = sz

fun peek ((net,sz), k) = let
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => (valOf (Binarymap.peek(d, k)) handle Option => S.empty)
      | (ND d, k::ks) => let
          val (lab, rest) = ndest_term k
        in
          case Binarymap.peek(d, lab) of
            NONE => S.empty
          | SOME n => trav(n, rest @ ks)
        end
      | _ => raise Fail "LVTermNet.peek: catastrophic invariant failure"
in
  trav(net, [k])
end

val find = peek

fun lookup_label tm = let
  val (f, args) = strip_comb tm
in
  case dest_term f of
    CONST{Name, Thy, ...} => (C ({Name=Name,Thy=Thy}, length args), args)
  | LAMB(Bvar, Body) => (Lam (length args), Body::args)
  | VAR (s, _) => (LV (s, length args), args)
  | _ => raise Fail "LVTermNet.lookup_label: catastrophic invariant failure"
end

fun conslistItems (d, acc) = let
  fun listfold k (v,acc) = (k,v)::acc
  fun mapfold (k,vs,acc) = S.fold (listfold k) acc vs
in
  Binarymap.foldl mapfold acc d
end

fun match ((net,sz), tm) = let
  fun trav acc (net, ks) =
      case (net, ks) of
        (LF d, []) => conslistItems (d, acc)
      | (ND d, k::ks0) => let
          val varresult = case Binarymap.peek(d, V 0) of
                            NONE => acc
                          | SOME n => trav acc (n, ks0)
          val (lab, rest) = lookup_label k
          val varhead_result = let
            val n = length (#2 (strip_comb k))
          in
            if n = 0 then varresult
            else
              case Binarymap.peek (d, V n) of
                NONE => varresult
              | SOME n => trav varresult (n, rest @ ks0)
          end
        in
          case Binarymap.peek (d, lab) of
            NONE => varhead_result
          | SOME n => trav varhead_result (n, rest @ ks0)
        end
      | _ => raise Fail "LVTermNet.match: catastrophic invariant failure"
in
  trav [] (net, [tm])
end

fun delete ((net,sz), k) = let
  fun trav (p as (net, ks)) =
      case p of
        (LF d, []) => let
          val (d',removed) = Binarymap.remove(d, k)
        in
          if Binarymap.numItems d' = 0 then (NONE, removed)
          else (SOME (LF d'), removed)
        end
      | (ND d, k::ks) => let
          val (lab, rest) = ndest_term k
        in
          case Binarymap.peek(d, lab) of
            NONE => raise Binarymap.NotFound
          | SOME n => let
            in
              case trav (n, rest @ ks) of
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
      | _ => raise Fail "LVTermNet.delete: catastrophic invariant failure"
in
  case trav (net, [k]) of
    (NONE, removed) => (empty, removed)
  | (SOME n, removed) =>  ((n,sz-1), removed)
end

fun app f (net, sz) = let
  fun trav n =
      case n of
        LF d => Binarymap.app f d
      | ND d => Binarymap.app (fn (lab, n) => trav n) d
in
  trav net
end

fun consfoldl f acc d = let
  fun setfold k (d, acc) = f (k, d, acc)
  fun mapfold (k,vs,acc) = S.fold (setfold k) acc vs
in
  Binarymap.foldl mapfold acc d
end

fun fold f acc (net, sz) = let
  fun trav acc n =
      case n of
        LF d => consfoldl f acc d
      | ND d => Binarymap.foldl (fn (lab,n',acc) => trav acc n') acc d
in
  trav acc net
end

end (* struct *)
