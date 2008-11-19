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

datatype 'a N = LF of (key,'a) Binarymap.dict
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
    VAR(s, ty) => if mem tm fvs then (LV (s, length args), args')
                  else (V (length args), args')
  | LAMB(bv, bod) => (Lam (length args), (subtract fvs [bv], bod) :: args')
  | CONST{Name,Thy,Ty} => (C ({Name=Name,Thy=Thy}, length args), args')
  | COMB _ => raise Fail "impossible"
end

fun insert ((net,sz), k, item) = let
  fun newnode labs =
      case labs of
        [] => LF (Binarymap.mkDict tlt_compare)
      | _ => mkempty()
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => let 
          val inc = 
              case Binarymap.peek(d, k) of NONE => 1 | SOME _ => 0
        in 
          (LF (Binarymap.insert(d,k,item)), inc)
        end
      | (ND d, k::ks0) => let
          val (lab, rest) = ndest_term k
          val ks = rest @ ks0
          val (n',inc) =
              case Binarymap.peek(d,lab) of
                NONE => trav(newnode ks, ks)
              | SOME n => trav(n, ks)
          val d' = Binarymap.insert(d, lab, n')
        in
          (ND d', inc)
        end
      | (EMPTY, ks) => trav(mkempty(), ks)
      | _ => raise Fail "TypeNet.insert: catastrophic invariant failure"
  val (net', inc) = trav(net,[k])
in
  (net', sz + inc)
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

fun peek ((net,sz), k) = let
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => Binarymap.peek(d, k)
      | (ND d, k::ks) => let
          val (lab, rest) = ndest_term k
        in
          case Binarymap.peek(d, lab) of
            NONE => NONE
          | SOME n => trav(n, rest @ ks)
        end
      | (EMPTY, _) => NONE
      | _ => raise Fail "TypeNet.peek: catastrophic invariant failure"
in
  trav(net, [k])
end

fun find (n, k) =
    valOf (peek (n, k)) handle Option => raise Binarymap.NotFound


fun lookup_label tm = let 
  val (f, args) = strip_comb tm
in
  case dest_term f of 
    CONST{Name, Thy, ...} => (C ({Name=Name,Thy=Thy}, length args), args)
  | LAMB(Bvar, Body) => (Lam (length args), args)
  | VAR (s, _) => (LV (s, length args), args)
  | _ => raise Fail "LVTermNet.lookup_label: catastrophic invariant failure"
end

fun match ((net,sz), tm) = let
  fun trav acc (net, ks) =
      case (net, ks) of
        (EMPTY, _) => []
      | (LF d, []) => Binarymap.listItems d @ acc
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
