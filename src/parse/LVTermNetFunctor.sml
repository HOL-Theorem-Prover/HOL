signature LVSET =
sig
  type value
  type t
  val empty : t
  val insert : t * value -> t
  val fold : (value * 'a -> 'a) -> 'a -> t -> 'a
  val listItems : t -> value list
end

signature LV_TERM_NET =
sig

  (* signature names modelled on Redblackmap's *)
  type lvtermnet
  type term = Term.term
  type key = Term.term list * Term.term
  type value
  structure Set : LVSET where type value = value
  exception NotFound

  val empty : lvtermnet
  val insert : (lvtermnet * key * value) -> lvtermnet
  val find : lvtermnet * key -> Set.t
  val peek : lvtermnet * key -> Set.t
  val match : lvtermnet * term -> (key * value) list

  val delete : lvtermnet * key -> lvtermnet * Set.t  (* raises NotFound *)
  val numItems : lvtermnet -> int
  val listItems : lvtermnet -> (key * value) list
  val app : (key * Set.t -> unit) -> lvtermnet -> unit
  val fold : (key * value * 'b -> 'b) -> 'b -> lvtermnet -> 'b

end

functor LVTermNetFunctor(S : LVSET) : LV_TERM_NET =
struct

open HolKernel

exception NotFound

datatype label = V of int
               | C of {Name : string, Thy : string} * int
               | Lam of int
               | LV of string * int
type key = term list * term
type value = S.value
structure Set = S

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

structure KeyTab = Table(struct
  type key = term list * term
  val ord = tlt_compare
  fun pp _ = HOLPP.add_string "<lvtm-key>"
end)

structure LabelTab = Table(struct
  type key = label
  val ord = labcmp
  fun pp _ = HOLPP.add_string "<lvtm-label>"
end)

datatype N = LF of S.t KeyTab.table
           | ND of N LabelTab.table

type lvtermnet = N * int

val empty_node = ND LabelTab.empty
val empty = (empty_node, 0)

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
    case KeyTab.lookup bmap k of
      NONE => KeyTab.update (k, S.insert(S.empty,i)) bmap
    | SOME items => KeyTab.update (k, S.insert(items, i)) bmap

fun insert ((net,sz), k, item) = let
  fun newnode labs =
      case labs of
        [] => LF KeyTab.empty
      | _ => empty_node
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => LF (cons_insert(d,k,item))
      | (ND d, k::ks0) => let
          val (lab, rest) = ndest_term k
          val ks = rest @ ks0
          val n' =
              case LabelTab.lookup d lab of
                NONE => trav(newnode ks, ks)
              | SOME n => trav(n, ks)
        in
          ND (LabelTab.update (lab, n') d)
        end
      | _ => raise Fail "LVTermNet.insert: catastrophic invariant failure"
in
  (trav(net,[k]), sz + 1)
end

fun listItems (net, sz) = let
  fun cons' (k,vs) acc = S.fold (fn (v,acc) => (k,v)::acc) acc vs
  fun trav (net, acc) =
      case net of
        LF d => KeyTab.fold cons' d acc
      | ND d => LabelTab.fold (fn (_,v) => fn acc => trav(v,acc)) d acc
in
  trav(net, [])
end

fun numItems (net, sz) = sz

fun peek ((net,sz), k) = let
  fun trav (net, tms) =
      case (net, tms) of
        (LF d, []) => (case KeyTab.lookup d k of
                           NONE => S.empty
                         | SOME items => items)
      | (ND d, k::ks) => let
          val (lab, rest) = ndest_term k
        in
          case LabelTab.lookup d lab of
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
  fun mapfold (k,vs) acc = S.fold (listfold k) acc vs
in
  KeyTab.fold mapfold d acc
end

fun match ((net,sz), tm) = let
  fun trav acc (net, ks) =
      case (net, ks) of
        (LF d, []) => conslistItems (d, acc)
      | (ND d, k::ks0) => let
          val varresult = case LabelTab.lookup d (V 0) of
                            NONE => acc
                          | SOME n => trav acc (n, ks0)
          val (lab, rest) = lookup_label k
          val restn = length rest
          val varhead_results = let
            fun recurse acc n =
              if n = 0 then acc
              else
                case LabelTab.lookup d (V n) of
                    NONE => recurse acc (n - 1)
                  | SOME m => recurse
                                (trav acc (m, List.drop(rest, restn - n) @ ks0))
                                (n - 1)
          in
            recurse varresult (length (#2 (strip_comb k)))
          end
        in
          case LabelTab.lookup d lab of
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
        (LF d, []) =>
        (case KeyTab.lookup d k of
             NONE => raise NotFound
           | SOME removed =>
             let val d' = KeyTab.delete k d
             in if KeyTab.size d' = 0 then (NONE, removed)
                else (SOME (LF d'), removed)
             end)
      | (ND d, k::ks) => let
          val (lab, rest) = ndest_term k
        in
          case LabelTab.lookup d lab of
            NONE => raise NotFound
          | SOME n => let
            in
              case trav (n, rest @ ks) of
                (NONE, removed) => let
                  val d' = LabelTab.delete lab d
                in
                  if LabelTab.size d' = 0 then (NONE, removed)
                  else (SOME (ND d'), removed)
                end
              | (SOME n', removed) => (SOME (ND (LabelTab.update (lab, n') d)),
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
        LF d => List.app f (KeyTab.dest d)
      | ND d => List.app (fn (_, n) => trav n) (LabelTab.dest d)
in
  trav net
end

fun consfoldl f acc d = let
  fun setfold k (d, acc) = f (k, d, acc)
  fun mapfold (k,vs) acc = S.fold (setfold k) acc vs
in
  KeyTab.fold mapfold d acc
end

fun fold f acc (net, sz) = let
  fun trav acc n =
      case n of
        LF d => consfoldl f acc d
      | ND d => LabelTab.fold (fn (_,n') => fn acc => trav acc n') d acc
in
  trav acc net
end

end (* struct *)
