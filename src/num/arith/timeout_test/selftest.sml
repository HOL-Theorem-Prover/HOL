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

val full =
  let val t = Time.now () in Arith.ARITH_CONV goal; seconds_since t end

val _ = tprint "ARITH_CONV: an interrupted search ends in TIMEOUT"

fun trial k =
  let
    val d = full * real k / 12.0
    val t = Time.now ()
    val r = Exn.capture (Timeout.apply (Time.fromReal d) Arith.ARITH_CONV) goal
    val elapsed = seconds_since t
  in
    case r of
        Exn.Exn (Timeout.TIMEOUT _) => ()
      | Exn.Res _ =>
          (* the timer thread can wake a little late, letting a search
             that finishes just after the deadline return normally *)
          if elapsed <= d + 0.05 then ()
          else die ("result after the deadline: " ^ Real.toString elapsed ^
                    "s for a " ^ Real.toString d ^ "s budget")
      | Exn.Exn e =>
          die ("deadline of " ^ Real.toString d ^ "s became " ^
               General.exnMessage e)
  end

val _ = List.app trial (List.tabulate (10, fn k => k + 1))
val _ = OK ()
