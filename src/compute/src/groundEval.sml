structure groundEval =
struct
(* used to track where the values in a term are.

   A value is essentially a weak-head normal form, where constants get
   to be to values too.
*)

val _ = overload_on ("B1", ``BIT1``);
val _ = overload_on ("B2", ``BIT2``);
val _ = overload_on ("iZ", ``numeral$iZ``);
val _ = overload_on ("NUM", ``NUMERAL``)

datatype vTree = KnownValue | vComb of vTree * vTree | Constructor

fun mk_vcomb(Constructor, KnownValue) = KnownValue
  | mk_vcomb(Constructor, Constructor) = KnownValue
  | mk_vcomb(vt1, vt2) = vComb(vt1,vt2)

fun kvify (vComb _) = KnownValue
  | kvify vt = vt

datatype GEset = GE of { constrs : term HOLset.set,
                         rwts : ((term -> thm) * vTree) Net.net }

fun constrs (GE {constrs,...}) = constrs
fun rwts (GE {rwts,...}) = rwts

fun vTreeOf geset t =
    case dest_term t of
        COMB(t1, t2) => mk_vcomb(vTreeOf geset t1, vTreeOf geset t2)
      | CONST _ => if HOLset.member(constrs geset, t) then Constructor
                   else KnownValue
      | _ => KnownValue

fun add_rwt thm (geset as GE{constrs, rwts}) = let
  val c = thm |> concl |> strip_forall |> #2
in
  GE {constrs = constrs,
      rwts = Net.insert (lhs c, (REWR_CONV thm, vTreeOf geset (rhs c)))
                        rwts
     }
end

datatype convresult = TM of term * vTree | THM of thm * vTree

datatype cont = Conv of (convresult -> convresult)
              | Trans of thm * (convresult -> convresult)

fun getKF (Conv cf) = cf
  | getKF (Trans (_, cf)) = cf

fun Kthm (Conv cf) = TRUTH
  | Kthm (Trans(th, _)) = th

fun kcombine (Conv cf) th = Trans(th,cf)
  | kcombine (Trans(th0, cf)) th = Trans(TRANS th0 th, cf)

fun apply_cont k vt th =
    case k of
      Conv f => f (THM(th, vt))
    | Trans(th0,f) => f (THM(TRANS th0 th
                             handle HOL_ERR _ =>
                                raise mk_HOL_ERR "apply_cont"
                                      "TRANS"
                                      ("Failed to trans " ^
                                       term_to_string (concl th0) ^
                                       " and " ^
                                       term_to_string (concl th)),
                             vt))

fun apply_unchanged k vt t =
    case k of
      Conv f => f (TM(t, vt))
    | Trans(th,k0) => apply_cont (Conv k0) vt th

fun result_thm (TM (t,_)) = REFL t
  | result_thm (THM (th, _)) = th

fun result_tree (TM(_, vt)) = vt
  | result_tree (THM(_, vt)) = vt

fun changedp (TM _) = false
  | changedp (THM _) = true

fun result_term (TM (t, _)) = t
  | result_term (THM (th, _)) = rand (concl th)

datatype msg = LZT of string * term
             | MSG of string

fun nspaces x = CharVector.tabulate(x, K #" ")
fun trace(x, LZT(s,t)) = print (nspaces x ^ s ^ term_to_string t ^ "\n")
  | trace(x, MSG s) = print (nspaces x ^ s ^ "\n")

val ncset = HOLset.addList(empty_tmset,
                           [``NUMERAL``, ``BIT1``, ``BIT2``,
                            ``0:num``, ``ZERO``]);

val ge0 = GE {constrs = ncset, rwts = Net.empty }
val ge = List.foldl (fn (th,ge) => add_rwt th ge) ge0
                    (Rewrite.mk_rewrites numeralTheory.numeral_distrib @
                     Rewrite.mk_rewrites numeralTheory.numeral_add @
                     Rewrite.mk_rewrites numeralTheory.numeral_suc @
                     Rewrite.mk_rewrites numeralTheory.numeral_iisuc)

fun try_conv t (c,vt) =
    let
      val th = c t
    in
      SOME (th, vt)
    end handle HOL_ERR _ => NONE

fun tracek n s (Conv _) = trace(n, MSG (s ^ " Conv(...)"))
  | tracek n s (Trans(th, _)) = trace(n, LZT(s ^ " Trans: ", concl th))

fun sanity (Trans(th,_)) t = aconv (rhs (concl th)) t
  | sanity _ t = true

fun reduction geset vt t k = let
  fun std i vt t k =
      (sanity k t orelse raise Fail ("std on "^term_to_string t ^ " and " ^
                                     term_to_string (concl (Kthm k)));
       trace(i, LZT("std: SANITY OK, entering ", t));
       tracek i "Kont = " k;
       case vt of
         vComb(vt1, vt2) =>
          let
            val (l,r) = dest_comb t
          in
            trace (i, LZT("L-Descending into ", l));
            std (i + 2) vt1 l (Conv(do_right (i + 2) vt t vt2 r k))
          end
        | _ => apply_unchanged k vt t)

  and do_right i pvt ptm rvt rtm k leftresult =
      (trace(i, LZT("Left finished with ", result_term leftresult));
       trace(i - 2, LZT("R-Descending into ", rtm));
       std i rvt rtm (Conv(finish (i - 2) pvt ptm k leftresult)))
  and finish i pvt ptm k leftresult rightresult =
      let
        val _ = trace (i + 2, LZT ("Right finished with ",
                                   result_term rightresult))
        val _ = case k of
                    Trans(th, _) => trace(i,
                                          LZT("finish conv is Trans(|- ",
                                              concl th))
                  | _ => trace(i, MSG ("finish conv is Conv(...)"))
        val result0 =
            case (leftresult, rightresult) of
                (TM _, TM _) => TM (ptm, KnownValue)
              | (l, r) => THM(MK_COMB(result_thm l, result_thm r),
                              KnownValue)
        val result_tm = result_term result0
        val _ = sanity k ptm orelse
                raise Fail ("finish on " ^ term_to_string result_tm ^
                            " and " ^
                            term_to_string (concl (Kthm k)))
        val _ = trace(i, MSG ("Combining " ^
                              term_to_string (result_term leftresult) ^
                              " and " ^
                              term_to_string (result_term rightresult)))
        val _ = if changedp result0 then
                  trace(i, LZT ("Changed sub-terms gives |- ",
                                concl (result_thm result0)))
                else trace(i, LZT ("No change in subterms of ", result_tm))
      in
        if is_abs (result_term leftresult) then
          let
            val newth = Beta (result_thm result0)
            val vt = vTreeOf geset (#2 (dest_abs (result_term leftresult)))
            val _ = trace(i, LZT("Called BETA_CONV, getting: |- ",
                                 concl newth))
          in
            std i vt (rhs (concl newth)) (kcombine k newth)
          end
        else
          case get_first (try_conv result_tm) (Net.match result_tm (rwts geset))
           of
              NONE =>
              if changedp result0 then
                (trace(i, LZT("Applying kont to ", result_term result0));
                 apply_cont k
                            (result_tree result0)
                            (result_thm result0))
              else apply_unchanged k
                                   (result_tree result0)
                                   (result_term result0)
            | SOME(newth, vt) =>
              let
              in
                trace(i, LZT ("Conv resulted in: |- ", concl newth));
                if changedp result0 then
                  std i vt
                      (rhs (concl newth))
                      (kcombine k (TRANS (result_thm result0) newth))
                else
                  std i vt (rhs (concl newth)) (kcombine k newth)
              end
      end
in
  std 0 vt t k
end
;

(*
fun dot t = reduction ge (vTreeOf ge t) t (Conv (fn x => x));
fun testdot t expected = let
  val result = dot t
in
    aconv (result_term (dot t)) expected andalso
    result_tree result = KnownValue
  orelse
    raise Fail ("Reduction of " ^ term_to_string t ^ " didn't give back " ^
                term_to_string expected)
end

testdot ``1 + 1`` ``2``;
testdot ``2 + 1`` ``3``;
testdot ``3 + 4`` ``7``;
testdot ``4 + 5 + 9`` ``18``;

testdot ``(\x. x + y) 5`` ``5 + y``;
testdot ``(\x. x + x + 1) ((\y. y + 10) 4)`` ``29``;

*)
end
