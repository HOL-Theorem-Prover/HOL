
(* Merge sort example in Moscow ML *)

datatype num = O | S of num;

fun inf_egal O n = true
  | inf_egal (S k) O = false
  | inf_egal (S k) (S l) = (inf_egal k l)
;

fun fusion (h1::t1) (h2::t2) =
      if (inf_egal h1 h2) then h1::(fusion t1 (h2::t2))
      else h2::(fusion (h1::t1) t2)
  | fusion [] l2 = l2
  | fusion l1 [] = l1
;


datatype arbin = Fe | Br of num * arbin * arbin;

fun Tas2Ln Fe = []
  | Tas2Ln (Br (n,a1,a2)) = n::(fusion (Tas2Ln a1) (Tas2Ln a2))
;

fun insTas Fe n = Br(n,Fe,Fe)
  | insTas (Br(m,a1,a2)) n =
      if (inf_egal n m) then Br(n,a2,insTas a1 m) else Br(m,a2,insTas a1 n)
;

fun Ln2Tas [] = Fe
  | Ln2Tas (n::ns) = insTas (Ln2Tas ns) n
;

fun tri_heap l = Tas2Ln (Ln2Tas l);

val n1 = S O;
val n2 = S n1;
val n3 = S n2;
val n4 = S n3;

fun app_l20 l =
  [ n2,O,n1,O,n1,n3,n4,
    n1,O,n1,n3,O,n1,n3,
    n4,n2,O,n1,O,n1 ] @ l
;

fun double l () = let val ll = l() in ll@ll end;
fun triple l () = let val ll = l() in ll@(ll@ll) end;


val L20 = app_l20 [];
val L100 = funpow 5 app_l20 [];
val L200 = double (fn _ => L100);
val L400 = double L200;
val L1200 = triple L400;
val L2400 = double L1200;
val L4800 = double L2400;
val L9600 = double L4800;
val L19200 = double L9600;
val L38400 = double L19200;


time (funpow 100 (fn() => (tri_heap (L200()); ()))) (); (* ~ 0.36s *)
time (funpow 100 (fn() => (tri_heap (L1200()); ()))) (); (* ~ 4.17s *)
time (funpow 10 (fn() => (tri_heap (L19200()); ()))) (); (* ~ 15.7s *)
time (funpow 10 (fn() => (tri_heap (L38400()); ()))) (); (* ~ 43.3s *)
