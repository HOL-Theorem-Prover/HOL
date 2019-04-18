structure LVTermNet :> LVTermNet =
struct

open HolKernel

datatype label = V of int
               | C of {Name : string, Thy : string} * int
               | Lam of int
               | LV of string * int
type key = term list * term

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

datatype 'a N = LF of (key,'a list) Binarymap.dict
              | ND of (label,'a N) Binarymap.dict
              | EMPTY
(* redundant EMPTY constructor is used to get around value polymorphism problem
   when creating a single value for empty below *)

type 'a lvtermnet = 'a N * int

val empty = (EMPTY, 0)

fun mkempty () = ND (Binarymap.mkDict labcmp)

fun ndest_term (fvs, tm) = let
  val (f, args) = strip_comb tm
  val args' = map (fn t => (fvs, t)) args
in
  case dest_term f of
    VAR(s, ty) => if op_mem aconv f fvs then (LV (s, length args), args')
                  else (V (length args), args')
  | LAMB(bv, bod) =>
      (Lam (length args), (op_set_diff aconv fvs [bv], bod) :: args')
  | CONST{Name,Thy,Ty} => (C ({Name=Name,Thy=Thy}, length args), args')
  | COMB _ => raise Fail "impossible"
end

fun cons_insert (bmap, k, i) =
    case Binarymap.peek(bmap,k) of
      NONE => Binarymap.insert(bmap,k,[i])
    | SOME items => Binarymap.insert(bmap,k,i::items)

fun insert ((net,sz), k, item) = let
  fun newnode labs =
      case labs of
        [] => LF (Binarymap.mkDict tlt_compare)
      | _ => mkempty()
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
      | (EMPTY, ks) => trav(mkempty(), ks)
      | _ => raise Fail "LVTermNet.insert: catastrophic invariant failure"
in
  (trav(net,[k]), sz + 1)
end

fun listItems (net, sz) = let
  fun cons'(k,vs,acc) = List.foldl (fn (v,acc) => (k,v)::acc) acc vs
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

fun peek ((net,sz), k) = let
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => (valOf (Binarymap.peek(d, k)) handle Option => [])
      | (ND d, k::ks) => let
          val (lab, rest) = ndest_term k
        in
          case Binarymap.peek(d, lab) of
            NONE => []
          | SOME n => trav(n, rest @ ks)
        end
      | (EMPTY, _) => []
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
  fun mapfold (k,vs,acc) = List.foldl (listfold k) acc vs
in
  Binarymap.foldl mapfold acc d
end

fun match ((net,sz), tm) = let
  fun trav acc (net, ks) =
      case (net, ks) of
        (EMPTY, _) => []
      | (LF d, []) => conslistItems (d, acc)
      | (ND d, k::ks0) => let
          val varresult = case Binarymap.peek(d, V 0) of
                            NONE => acc
                          | SOME n => trav acc (n, ks0)
          val (lab, rest) = lookup_label k
          val restn = length rest
          val varhead_results = let
            fun recurse acc n =
              if n = 0 then acc
              else
                case Binarymap.peek (d, V n) of
                    NONE => recurse acc (n - 1)
                  | SOME m => recurse
                                (trav acc (m, List.drop(rest, restn - n) @ ks0))
                                (n - 1)
          in
            recurse varresult (length (#2 (strip_comb k)))
          end
        in
          case Binarymap.peek (d, lab) of
            NONE => varhead_results
          | SOME n => trav varhead_results (n, rest @ ks0)
        end
      | _ => raise Fail "LVTermNet.match: catastrophic invariant failure"
in
  trav [] (net, [tm])
end

fun delete ((net,sz), k) = let
  fun trav (p as (net, ks)) =
      case p of
        (EMPTY, _) => raise Binarymap.NotFound
      | (LF d, []) => let
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
      | EMPTY => ()
in
  trav net
end

fun consfoldl f acc d = let
  fun listfold k (d, acc) = f (k, d, acc)
  fun mapfold (k,vs,acc) = List.foldl (listfold k) acc vs
in
  Binarymap.foldl mapfold acc d
end

fun fold f acc (net, sz) = let
  fun trav acc n =
      case n of
        LF d => consfoldl f acc d
      | ND d => Binarymap.foldl (fn (lab,n',acc) => trav acc n') acc d
      | EMPTY => acc
in
  trav acc net
end

fun consmap f d = let
  fun foldthis (k,vs,acc) = let
    val bs = map (fn v => f(k,v)) vs
  in
    Binarymap.insert(acc,k,bs)
  end
in
  Binarymap.foldl foldthis (Binarymap.mkDict tlt_compare) d
end

fun map f (net, sz) = let
  fun trav n =
      case n of
        LF d => LF (consmap f d)
      | ND d => ND (Binarymap.transform trav d)
      | EMPTY => EMPTY
in
  (trav net, sz)
end

fun transform f = map (fn (k,v) => f v)


end (* struct *)
