structure patriciaLib :> patriciaLib =
struct

open Word;

type 'a pnode = { key : word, data : 'a };

datatype 'a ptree = Empty | Leaf of 'a pnode | Branch of word * word * 'a ptree * 'a ptree;

fun is_empty x = case x of Empty => true | _ => false;
fun zero_bit k m = andb(k,m) = 0w0;
fun lowest_bit x = andb(x,0w0 - x);
fun branching_bit p0 p1 = lowest_bit (xorb(p0,p1));
fun mask p m = andb(p,m - 0w1);
fun match_prefix k p m = (mask k m) = p;

val empty = Empty;

fun member k t =
  case t of
    Empty => NONE
  | Leaf j => if k = #key j then SOME j else NONE
  | Branch (_,m,l,r) => member k (if zero_bit k m then l else r);

fun join (p0,t0,p1,t1) =
  let val m = branching_bit p0 p1 in
    if zero_bit p0 m then
      Branch (mask p0 m, m, t0, t1)
    else 
      Branch (mask p0 m, m, t1, t0)
  end;

fun add k t =
  let val kkey = #key k
      fun ins t =
        case t of
          Empty => Leaf k
        | Leaf j => 
            if #key j = kkey then t else join (kkey, Leaf k, #key j, t)
        | Branch (p,m,t0,t1) =>
            if match_prefix kkey p m then
              if zero_bit kkey m then 
                Branch (p, m, ins t0, t1)
              else
                Branch (p, m, t0, ins t1)
            else
              join (kkey, Leaf k, p, t)
  in
    ins t
  end;

fun update k t =
  case t of
     Empty => t
   | Leaf j => if #key j = #key k then Leaf k else t
   | Branch (_,m,l,r) => update k (if zero_bit (#key k) m then l else r);

fun branch x =
  case x of
    (_,_,Empty,t) => t
  | (_,_,t,Empty) => t
  | (p,m,t0,t1) => Branch (p,m,t0,t1);

fun remove k t =
  let fun rmv t =
        case t of
          Empty => Empty
        | Leaf j => 
            if #key j = k then Empty else t
        | Branch (p,m,t0,t1) =>
            if match_prefix k p m then
              if zero_bit k m then 
                branch (p, m, rmv t0, t1)
              else
                branch (p, m, t0, rmv t1)
            else
              t
  in
    rmv t
  end;

fun keys t = 
  let fun traverse t =
    case t of
      Empty => []
    | Leaf j => [#key j]
    | Branch (_,_,l,r) => traverse l @ traverse r
  in
    Listsort.sort Word.compare (traverse t)
  end;

(*
val t =
  (add {key = 0w1, data = "hello"} o
   add {key = 0w2, data = "world"} o
   add {key = 0w3, data = "mars"} o
   add {key = 0w4, data = "hello"} o
   add {key = 0w5, data = "world"} o
   add {key = 0w6, data = "mars"} o
   add {key = 0w7, data = "earth"}) empty;
*)

end;
