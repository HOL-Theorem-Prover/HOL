(* ARITH_CONV under Timeout.apply.  The timer interrupts the thread once;
   the decision procedure's own failure handlers must let that interrupt
   through, rather than turn it into an ordinary failure or carry on to a
   result after the deadline.  Poly/ML only: Timeout is. *)

open HolKernel boolLib numSyntax testutils

(* x0 < xm \/ xm < x0 \/ x0 = xm, from m disjunctive hypotheses: slow
   enough for a deadline to land in the middle of the search *)
fun v i = mk_var ("x" ^ Int.toString i, num)
fun disj m =
  let
    val hyps = List.tabulate (m, fn i =>
      mk_disj (mk_leq (mk_plus (v i, term_of_int 1), v (i + 1)),
               mk_leq (mk_plus (v (i + 1), term_of_int 2), v i)))
    val concl = mk_disj (mk_less (v 0, v m), mk_less (v m, v 0))
  in
    mk_imp (list_mk_conj hyps, mk_disj (concl, mk_eq (v 0, v m)))
  end
val goal = disj 12

fun seconds_since t = Time.toReal (Time.- (Time.now (), t))
fun secs x = Real.fmt (StringCvt.FIX (SOME 3)) x ^ "s"
(* die does not come back, but is typed as though it might *)
fun died msg = (die msg; false)

(* An uninterrupted search, timed more than once: a single run is a poor
   yardstick.  The first is the slowest of all (the heap image pages in
   and the ML heap grows under it), and even once warm, runs on an idle
   machine spread over some 20%.  The quickest is the safe baseline,
   because the deadlines below have to stay inside a search that may turn
   out quicker than the one that was measured. *)
val full =
  let
    fun once () =
      let val t = Time.now () in Arith.ARITH_CONV goal; seconds_since t end
  in
    List.foldl Real.min (once ()) [once (), once ()]
  end

(* Deadlines spread over the first five eighths of the search.  They stop
   well short of the whole because a deadline the search can reach on its
   own makes the trial a race: when the search gets there first, the timer
   has nothing left to interrupt, and whether Timeout.apply reports a
   result or a TIMEOUT comes down to which of the two wins, not to what
   the decision procedure did with its interrupt. *)
val budgets = List.tabulate (10, fn k => full * real (k + 1) / 16.0)

(* How late a result may be and still be the timer's fault rather than the
   search's: the timer thread has to wake, and the interrupt has to reach
   a safe point, either of which a stop-the-world GC can hold up.  Half a
   second of that has been seen on an idle machine.  A swallowed interrupt
   is nothing like this close to its deadline: it runs the search out to
   the end, three eighths of it or more past the budget. *)
val slack = Real.max (1.0, full / 2.0)

val _ = tprint "ARITH_CONV: an interrupted search ends in TIMEOUT"

(* returns whether the deadline did interrupt the search *)
fun trial d =
  let
    val finished = ref NONE
    fun conv tm =
      let val th = Arith.ARITH_CONV tm
      in finished := SOME (Time.now ()); th end
    val t = Time.now ()
    val r = Exn.capture (Timeout.apply (Time.fromReal d) conv) goal
  in
    case r of
        Exn.Exn (Timeout.TIMEOUT _) => true
      | Exn.Res _ =>
          (* the search's own finishing time, not the time Timeout.apply
             took to return: a GC between the two is not an overrun *)
          let
            val elapsed =
              case !finished of
                  SOME ft => Time.toReal (Time.- (ft, t))
                | NONE => raise Fail "ARITH_CONV returned without a stamp"
          in
            if elapsed <= d + slack then false
            else died ("result " ^ secs (elapsed - d) ^ " after a " ^ secs d ^
                       " deadline (an uninterrupted search takes " ^
                       secs full ^ ")")
          end
      | Exn.Exn e =>
          died ("deadline of " ^ secs d ^ " became " ^ General.exnMessage e)
  end

val timed_out = List.exists (fn b => b) (List.map trial budgets)

(* no budget was more than five eighths of a search, so some of them must
   have cut one short; if none did, the trials above tested nothing *)
val _ =
  if timed_out then OK ()
  else die ("no deadline interrupted the search (budgets up to " ^
            secs (full * 0.625) ^ ")")
