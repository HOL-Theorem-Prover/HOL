(* ========================================================================= *)
(* A TYPE TO STORE CLAUSES WAITING TO BE USED (THEAP = THEOREM HEAP)         *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

(*
app load ["mlibHeap", "mlibQueue", "mlibThm", "Subsumers1"];
*)

(*
*)
structure mlibTheap :> mlibTheap =
struct

infix |->;

open mlibUseful mlibTerm mlibThm;

structure Q = mlibQueue; local open mlibQueue in end;
structure H = mlibHeap; local open mlibHeap in end;
structure S = mlibSubsum; local open mlibSubsum in end;

type 'a queue  = 'a Q.queue;
type 'a heap   = 'a H.heap;
type 'a subsum = 'a S.subsum;

(* ------------------------------------------------------------------------- *)
(* Tuning parameters.                                                        *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo_skew : int, cleaning_freq : int}

val defaults = {fifo_skew = 3, cleaning_freq = 1000};

(* ------------------------------------------------------------------------- *)
(* Theorem HEAPs.                                                            *)
(* ------------------------------------------------------------------------- *)

type theap =
  ((int * int) * (int * int)) * thm queue * (int * (int * thm) heap) *
  thm subsum;

local fun order ((m, _ : thm), (n, _ : thm)) = Int.compare (m, n);
in val empty_theap_heap = H.empty order;
end;

fun new_theap {fifo_skew, cleaning_freq} =
  ((D cleaning_freq, D fifo_skew), Q.empty, (0, empty_theap_heap), S.empty);

val empty_theap = new_theap defaults;

fun theap_size (_, _, (_, h), _) = H.size h;
fun theap_weight (_, _, (w, _), _) = w;

fun clean_theap (((_, C), F), Q, (_, H), _) =
  let
    val hash = Polyhash.mkPolyTable (10000, ERR "cleap_theap" "not found")
    fun mark (v, th) = Polyhash.insert hash (clause th, v)
    val () = H.app mark H
    fun add (v, th) (q, w, h, l) =
      (Q.add th q, w + v, H.add (v, th) h, S.add (clause th |-> th) l)
    fun check q n =
      if Q.is_empty q then n
      else
        let
          val th = Q.hd q
        in
          check (Q.tl q)
          (case total (Polyhash.remove hash) (clause th) of NONE => n
           | SOME v => add (v, th) n)
        end
  in
    (fn (q, w, h, l) => (((C, C), F), q, (w, h), l))
    (check Q (Q.empty, 0, empty_theap_heap, S.empty))
  end;

fun theap_add th (h as (((0, _), _), _, _, _)) = theap_add th (clean_theap h)
  | theap_add th (((c, cm), f), q, (w, h), l) =
  let
    val cl = clause th
    val v = formula_size (list_mk_disj cl)
    val h' = H.add (v, th) h
  in
    (((c - 1, cm), f), Q.add th q, (w + v, h'), S.add (clause th |-> th) l)
  end;

fun theap_addl ths h = foldl (uncurry theap_add) h ths;

fun theap_remove ((c, (0, f)), q, h, l) =
  if Q.is_empty q then NONE
  else SOME (Q.hd q, ((c, (f, f)), Q.tl q, h, l))
  | theap_remove ((c, (n, f)), q, (w, h), l) =
  if H.is_empty h then NONE
  else
    let val ((v, x), h) = H.remove h
    in SOME (x, ((c, (n - 1, f)), q, (w - v, h), l))
    end;

fun theap_subsumers (_, _, _, l) = l;

fun theap_info thp =
  "(" ^ int_to_string (theap_size thp) ^ "," ^
  int_to_string (theap_weight thp) ^ ")";

end