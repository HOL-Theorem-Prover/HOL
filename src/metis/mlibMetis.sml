(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "Mosml", "mlibTerm", "mlibThm", "mlibCanon",
  "mlibSolver", "mlibMeson", "mlibResolution"];
*)

(*
*)
structure mlibMetis :> mlibMetis =
struct

open mlibUseful mlibTerm mlibThm mlibMeter mlibCanon mlibSolver mlibMeson mlibResolution;

infix |-> ::> @> oo ## ::* ::@;

(* ------------------------------------------------------------------------- *)
(* Tuning parameters.                                                        *)
(* ------------------------------------------------------------------------- *)

type Mparm = mlibMeson.parameters;
type Rparm = mlibResolution.parameters;

type parameters =
  {meson           : bool,
   delta           : bool,
   resolution      : bool,
   meson_parm      : Mparm,
   resolution_parm : Rparm};

val defaults =
  {meson           = true,
   delta           = true,
   resolution      = true,
   meson_parm      = mlibMeson.defaults,
   resolution_parm = mlibResolution.defaults};

fun update_parm_meson f parm =
  let
    val {meson, delta, resolution, meson_parm, resolution_parm} = parm
  in
    {meson = f meson, delta = delta, resolution = resolution,
     meson_parm = meson_parm, resolution_parm = resolution_parm}
  end;

fun update_parm_delta f parm =
  let
    val {meson, delta, resolution, meson_parm, resolution_parm} = parm
  in
    {meson = meson, delta = f delta, resolution = resolution,
     meson_parm = meson_parm, resolution_parm = resolution_parm}
  end;

fun update_parm_resolution f parm =
  let
    val {meson, delta, resolution, meson_parm, resolution_parm} = parm
  in
    {meson = meson, delta = delta, resolution = f resolution,
     meson_parm = meson_parm, resolution_parm = resolution_parm}
  end;

fun update_parm_meson_parm f parm =
  let
    val {meson, delta, resolution, meson_parm, resolution_parm} = parm
  in
    {meson = meson, delta = delta, resolution = resolution,
     meson_parm = f meson_parm, resolution_parm = resolution_parm}
  end;

fun update_parm_resolution_parm f parm =
  let
    val {meson, delta, resolution, meson_parm, resolution_parm} = parm
  in
    {meson = meson, delta = delta, resolution = resolution,
     meson_parm = meson_parm, resolution_parm = f resolution_parm}
  end;

(* ------------------------------------------------------------------------- *)
(* The metis combination of solvers.                                         *)
(* ------------------------------------------------------------------------- *)

fun metis' {meson = m, delta = d, resolution = r, meson_parm, resolution_parm} =
  combine
  ((if m then cons (time1, meson' meson_parm) else I)
   ((if r then cons (time1, resolution' resolution_parm) else I)
    ((if d then cons (time2, delta' meson_parm) else I)
     [])));

val metis = metis' defaults;

(* ------------------------------------------------------------------------- *)
(* A user-friendly interface.                                                *)
(* ------------------------------------------------------------------------- *)

val settings = ref defaults;

val limit : limit ref = ref {time = SOME 10.0, infs = NONE};

fun raw_prove (Imp (a, Imp (b, False))) =
  let
    val (thms, hyps) = (axiomatize a, axiomatize b)
    val solv = metis' (!settings)
  in
    refute (initialize solv {limit = !limit, thms = thms, hyps = hyps})
  end
  | raw_prove _ = raise ERR "raw_prove" "formula not of type a ==> b ==> F";

fun prove g =
  let
    val hyps = eq_axiomatize' (Not (generalize g))
    val solv = set_of_support all_negative (metis' (!settings))
  in
    refute (initialize solv {limit = !limit, thms = [], hyps = hyps})
  end;

fun query database =
  initialize prolog {thms = axiomatize database, hyps = [], limit = unlimited};

(* quick testing
val time = Mosml.time;
quotation := true;
installPP pp_term;
installPP pp_formula;
installPP mlibSubst.pp_subst;
installPP pp_thm;

(* Testing the metis prover *)

prove True;

val p59 = parse_formula `(!x. P(x) <=> ~P(f(x))) ==> (?x. P(x) /\ ~P(f(x)))`;
val ths = axiomatize (Not (generalize p59));
prove p59;

val p39 = parse_formula `~(?x. !y. P(y,x) <=> ~P(y,y))`;
clausal (Not (generalize p39));
axiomatize (Not (generalize p39));
prove p39;

val num14 = parse_formula
  `(!X. product(X, X, square(X))) /\
   (!Z X Y. ~product(X, Y, Z) \/ product(Y, X, Z)) /\
   (!Z X Y. ~product(X, Y, Z) \/ divides(X, Z)) /\
   (!Y X V Z.
      ~prime(X) \/ ~product(Y, Z, V) \/ ~divides(X, V) \/ divides(X, Y) \/
      divides(X, Z)) /\ prime(a) /\
   product(a, square(c), square(b)) /\ ~divides(a, b) ==> F`;
prove num14;

val p26 = parse_formula
 `((?x. P(x)) <=> (?x. Q(x))) /\
   (!x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((!x. P(x) ==> R(x)) <=> (!x. Q(x) ==> U(x)))`;
clausal (Not (generalize p26));
prove p26;

val los = parse_formula
 `(!x y z. P x y ==> P y z ==> P x z) /\
  (!x y z. Q x y ==> Q y z ==> Q x z) /\ (!x y. Q x y ==> Q y x) /\
  (!x y. P x y \/ Q x y) ==> (!x y. P x y) \/ !x y. Q x y`;
try prove los;

val puz2 = parse_formula
  `(!X. equal(X, X)) /\ (!Y X. ~equal(X, Y) \/ equal(Y, X)) /\
   (!Z X Y. ~equal(X, Y) \/ ~equal(Y, Z) \/ equal(X, Z)) /\
   (!B A. ~equal(A, B) \/ equal(every_one_but(A), every_one_but(B))) /\
   (!E C D. ~equal(C, D) \/ ~hates(C, E) \/ hates(D, E)) /\
   (!H F_avoid G.
      ~equal(F_avoid, G) \/ ~hates(H, F_avoid) \/ hates(H, G)) /\
   (!K I J. ~equal(I, J) \/ ~killed(I, K) \/ killed(J, K)) /\
   (!N L M. ~equal(L, M) \/ ~killed(N, L) \/ killed(N, M)) /\
   (!P O.
      ~equal(O, P) \/ ~lives_at_dreadsbury(O) \/ lives_at_dreadsbury(P)) /\
   (!S Q R. ~equal(Q, R) \/ ~richer(Q, S) \/ richer(R, S)) /\
   (!V T_avoid U.
      ~equal(T_avoid, U) \/ ~richer(V, T_avoid) \/ richer(V, U)) /\
   lives_at_dreadsbury(someone()) /\ killed(someone(), aunt_agatha()) /\
   lives_at_dreadsbury(aunt_agatha()) /\ lives_at_dreadsbury(butler()) /\
   lives_at_dreadsbury(charles()) /\
   (!Person.
      ~lives_at_dreadsbury(Person) \/ equal(Person, aunt_agatha()) \/
      equal(Person, butler()) \/ equal(Person, charles())) /\
   (!Victim Killer. ~killed(Killer, Victim) \/ hates(Killer, Victim)) /\
   (!Victim Killer. ~killed(Killer, Victim) \/ ~richer(Killer, Victim)) /\
   (!Person. ~hates(aunt_agatha(), Person) \/ ~hates(charles(), Person)) /\
   (!Person. equal(Person, butler()) \/ hates(aunt_agatha(), Person)) /\
   (!Person. richer(Person, aunt_agatha()) \/ hates(butler(), Person)) /\
   (!Person. ~hates(aunt_agatha(), Person) \/ hates(butler(), Person)) /\
   (!Person. ~hates(Person, every_one_but(Person))) /\
   ~equal(aunt_agatha(), butler()) /\
   ~killed(aunt_agatha(), aunt_agatha()) ==> F`;
prove puz2;

val num284 = parse_formula
  `fibonacci(0, successor(0)) /\ fibonacci(successor(0), successor(0)) /\
   (!N2 N1 N F1 FN F2.
      ~sum(N1, successor(0), N) \/ ~sum(N2, successor(successor(0)), N) \/
      ~fibonacci(N1, F1) \/ ~fibonacci(N2, F2) \/ ~sum(F1, F2, FN) \/
      fibonacci(N, FN)) /\ (!X. sum(X, 0, X)) /\
   (!Z X Y. ~sum(X, Y, Z) \/ sum(X, successor(Y), successor(Z))) /\
   (!Result.
      ~fibonacci(successor(successor(successor(successor(successor(successor(successor(successor(0)))))))),
                 Result)) ==> F`;
prove num284;

val p29 = parse_formula
  `(?x. P(x)) /\ (?x. G(x)) ==>
   ((!x. P(x) ==> H(x)) /\ (!x. G(x) ==> J(x)) <=>
    (!x y. P(x) /\ G(y) ==> H(x) /\ J(y)))`;
clausal (Not (generalize p29));
prove p29;

val num27 = parse_formula
  `(!A. equalish(add(A, 0), A)) /\
   (!A B. equalish(add(A, successor(B)), successor(add(A, B)))) /\
   (!A. equalish(multiply(A, 0), 0)) /\
   (!A B. equalish(multiply(A, successor(B)), add(multiply(A, B), A))) /\
   (!B A. ~equalish(successor(A), successor(B)) \/ equalish(A, B)) /\
   (!B A. ~equalish(A, B) \/ equalish(successor(A), successor(B))) /\
   (!C A B. ~less(A, B) \/ ~less(C, A) \/ less(C, B)) /\
   (!C B A. ~equalish(add(successor(A), B), C) \/ less(B, C)) /\
   (!B A.
      ~less(A, B) \/
      equalish(add(successor(predecessor_of_1st_minus_2nd(B, A)), A),
        B)) /\ (!X. equalish(X, X)) /\
   (!Y X. ~equalish(X, Y) \/ equalish(Y, X)) /\
   (!Z X Y. ~equalish(X, Y) \/ ~equalish(Y, Z) \/ equalish(X, Z)) /\
   (!C A B. ~equalish(A, B) \/ equalish(multiply(A, C), multiply(B, C))) /\
   (!B A. ~less(A, B) \/ ~equalish(A, B)) /\
   (!B A. less(A, B) \/ equalish(B, A) \/ less(B, A)) /\
   (!A. ~less(A, A)) /\ (!A. ~equalish(successor(A), 0)) /\
   (!C A B.
      ~less(A, B) \/ equalish(C, 0) \/
      less(multiply(A, C), multiply(B, C))) /\ ~less(b(), a()) /\
   less(multiply(b(), c()), multiply(a(), c())) /\ ~equalish(c(), 0) ==>
   F`;
prove num27;

val model_completeness = parse_formula
  `(!M p. sentence(p) ==> holds(M,p) \/ holds(M,not(p))) /\
   (!M p. ~(holds(M,p) /\ holds(M,not(p)))) ==>
   ((!p.
       sentence(p) ==>
       (!M. models(M,S) ==> holds(M,p)) \/
       (!M. models(M,S) ==> holds(M,not(p)))) <=>
    (!M M'.
       models(M,S) /\ models(M',S) ==>
       (!p. sentence(p) ==> (holds(M,p) <=> holds(M',p)))))`;
prove model_completeness;

val agatha = parse_formula
  `lives(agatha()) /\ lives(butler()) /\ lives(charles()) /\
   (killed(agatha(),agatha()) \/ killed(butler(),agatha()) \/
    killed(charles(),agatha())) /\
   (!x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (!x. hates(agatha(),x) ==> ~hates(charles(),x)) /\
   (hates(agatha(),agatha()) /\ hates(agatha(),charles())) /\
   (!x. lives(x) /\ ~richer(x,agatha()) ==> hates(butler(),x)) /\
   (!x. hates(agatha(),x) ==> hates(butler(),x)) /\
   (!x. ~hates(x,agatha()) \/ ~hates(x,butler()) \/ ~hates(x,charles()))
   ==>
   killed(agatha(),agatha()) /\ ~killed(butler(),agatha()) /\
   ~killed(charles(),agatha())`;
prove agatha;

val boo3 = parse_formula
 `(!X. equal(X, X)) /\ (!Y X. ~equal(X, Y) \/ equal(Y, X)) /\
  (!Z X Y. ~equal(X, Y) \/ ~equal(Y, Z) \/ equal(X, Z)) /\
  (!Y X. sum(X, Y, add(X, Y))) /\ (!Y X. product(X, Y, multiply(X, Y))) /\
  (!Z X Y. ~sum(X, Y, Z) \/ sum(Y, X, Z)) /\
  (!Z X Y. ~product(X, Y, Z) \/ product(Y, X, Z)) /\
  (!X. sum(additive_identity(), X, X)) /\
  (!X. sum(X, additive_identity(), X)) /\
  (!X. product(multiplicative_identity(), X, X)) /\
  (!X. product(X, multiplicative_identity(), X)) /\
  (!Z X Y V1 V3 V4 V2.
     ~product(X, Y, V1) \/ ~product(X, Z, V2) \/ ~sum(Y, Z, V3) \/
     ~product(X, V3, V4) \/ sum(V1, V2, V4)) /\
  (!Z X Y V1 V3 V4 V2.
     ~product(X, Y, V1) \/ ~product(X, Z, V2) \/ ~sum(Y, Z, V3) \/
     ~sum(V1, V2, V4) \/ product(X, V3, V4)) /\
  (!Z Y X V1 V3 V4 V2.
     ~product(Y, X, V1) \/ ~product(Z, X, V2) \/ ~sum(Y, Z, V3) \/
     ~product(V3, X, V4) \/ sum(V1, V2, V4)) /\
  (!Z Y X V1 V3 V4 V2.
     ~product(Y, X, V1) \/ ~product(Z, X, V2) \/ ~sum(Y, Z, V3) \/
     ~sum(V1, V2, V4) \/ product(V3, X, V4)) /\
  (!Z X Y V1 V3 V4 V2.
     ~sum(X, Y, V1) \/ ~sum(X, Z, V2) \/ ~product(Y, Z, V3) \/
     ~sum(X, V3, V4) \/ product(V1, V2, V4)) /\
  (!Z X Y V1 V3 V4 V2.
     ~sum(X, Y, V1) \/ ~sum(X, Z, V2) \/ ~product(Y, Z, V3) \/
     ~product(V1, V2, V4) \/ sum(X, V3, V4)) /\
  (!Z Y X V1 V3 V4 V2.
     ~sum(Y, X, V1) \/ ~sum(Z, X, V2) \/ ~product(Y, Z, V3) \/
     ~sum(V3, X, V4) \/ product(V1, V2, V4)) /\
  (!Z Y X V1 V3 V4 V2.
     ~sum(Y, X, V1) \/ ~sum(Z, X, V2) \/ ~product(Y, Z, V3) \/
     ~product(V1, V2, V4) \/ sum(V3, X, V4)) /\
  (!X. sum(inverse(X), X, multiplicative_identity())) /\
  (!X. sum(X, inverse(X), multiplicative_identity())) /\
  (!X. product(inverse(X), X, additive_identity())) /\
  (!X. product(X, inverse(X), additive_identity())) /\
  (!V X Y U. ~sum(X, Y, U) \/ ~sum(X, Y, V) \/ equal(U, V)) /\
  (!V X Y U. ~product(X, Y, U) \/ ~product(X, Y, V) \/ equal(U, V)) /\
  (!W X Y Z. ~equal(X, Y) \/ ~sum(X, W, Z) \/ sum(Y, W, Z)) /\
  (!W X Y Z. ~equal(X, Y) \/ ~sum(W, X, Z) \/ sum(W, Y, Z)) /\
  (!W X Y Z. ~equal(X, Y) \/ ~sum(W, Z, X) \/ sum(W, Z, Y)) /\
  (!W X Y Z. ~equal(X, Y) \/ ~product(X, W, Z) \/ product(Y, W, Z)) /\
  (!W X Y Z. ~equal(X, Y) \/ ~product(W, X, Z) \/ product(W, Y, Z)) /\
  (!W X Y Z. ~equal(X, Y) \/ ~product(W, Z, X) \/ product(W, Z, Y)) /\
  (!W X Y. ~equal(X, Y) \/ equal(add(X, W), add(Y, W))) /\
  (!W X Y. ~equal(X, Y) \/ equal(add(W, X), add(W, Y))) /\
  (!W X Y. ~equal(X, Y) \/ equal(multiply(X, W), multiply(Y, W))) /\
  (!W X Y. ~equal(X, Y) \/ equal(multiply(W, X), multiply(W, Y))) /\
  (!Y X. ~equal(X, Y) \/ equal(inverse(X), inverse(Y))) /\
  ~product(x(), x(), x()) ==> F`;
prove boo3;

val fld5 = parse_formula
 `(!Y X V W Z U.
     sum(X, V, W) \/ ~sum(X, Y, U) \/ ~sum(Y, Z, V) \/ ~sum(U, Z, W)) /\
  (!X U Z W V Y.
     sum(U, Z, W) \/ ~sum(X, Y, U) \/ ~sum(Y, Z, V) \/ ~sum(X, V, W)) /\
  (!X. sum(additive_identity(), X, X) \/ ~defined(X)) /\
  (!X. sum(additive_inverse(X), X, additive_identity()) \/ ~defined(X)) /\
  (!Z Y X. sum(Y, X, Z) \/ ~sum(X, Y, Z)) /\
  (!Y X V W Z U.
     product(X, V, W) \/ ~product(X, Y, U) \/ ~product(Y, Z, V) \/
     ~product(U, Z, W)) /\
  (!X U Z W V Y.
     product(U, Z, W) \/ ~product(X, Y, U) \/ ~product(Y, Z, V) \/
     ~product(X, V, W)) /\
  (!X. product(multiplicative_identity(), X, X) \/ ~defined(X)) /\
  (!X.
     product(multiplicative_inverse(X), X, multiplicative_identity()) \/
     sum(additive_identity(), X, additive_identity()) \/ ~defined(X)) /\
  (!Z Y X. product(Y, X, Z) \/ ~product(X, Y, Z)) /\
  (!X C D B Z A Y.
     sum(C, D, B) \/ ~sum(X, Y, A) \/ ~product(A, Z, B) \/
     ~product(X, Z, C) \/ ~product(Y, Z, D)) /\
  (!X A Z B C D Y.
     product(A, Z, B) \/ ~sum(X, Y, A) \/ ~product(X, Z, C) \/
     ~product(Y, Z, D) \/ ~sum(C, D, B)) /\
  (!X Y. defined(add(X, Y)) \/ ~defined(X) \/ ~defined(Y)) /\
  defined(additive_identity()) /\
  (!X. defined(additive_inverse(X)) \/ ~defined(X)) /\
  (!X Y. defined(multiply(X, Y)) \/ ~defined(X) \/ ~defined(Y)) /\
  defined(multiplicative_identity()) /\
  (!X.
     defined(multiplicative_inverse(X)) \/ ~defined(X) \/
     sum(additive_identity(), X, additive_identity())) /\
  (!Y X. sum(X, Y, add(X, Y)) \/ ~defined(X) \/ ~defined(Y)) /\
  (!Y X. product(X, Y, multiply(X, Y)) \/ ~defined(X) \/ ~defined(Y)) /\
  (!Y X.
     sum(additive_identity(), X, Y) \/ ~less_or_equal(X, Y) \/
     ~less_or_equal(Y, X)) /\
  (!Y X Z.
     less_or_equal(X, Z) \/ ~less_or_equal(X, Y) \/
     ~less_or_equal(Y, Z)) /\
  (!Y X.
     less_or_equal(X, Y) \/ less_or_equal(Y, X) \/ ~defined(X) \/
     ~defined(Y)) /\
  (!X U V Z Y.
     less_or_equal(U, V) \/ ~less_or_equal(X, Y) \/ ~sum(X, Z, U) \/
     ~sum(Y, Z, V)) /\
  (!X Z Y.
     less_or_equal(additive_identity(), Z) \/
     ~less_or_equal(additive_identity(), X) \/
     ~less_or_equal(additive_identity(), Y) \/ ~product(X, Y, Z)) /\
  ~sum(additive_identity(), additive_identity(),
     multiplicative_identity()) /\ defined(a()) /\ defined(b()) /\
  (!X. ~sum(a(), X, b())) ==> F`;
prove fld5;
*)

end
