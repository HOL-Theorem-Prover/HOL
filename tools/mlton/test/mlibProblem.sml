(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

structure mlibProblem :> mlibProblem =
struct

type 'a quotation = 'a frag list;
type 'a problem   = {name : string, comment : string, goal : 'a quotation};
type 'a set       = {name : string, blurb : string, probs : 'a problem list};

fun mk_set n b p =
  {name = n, blurb = Int.toString (length p) ^ " " ^ b, probs = p};

(* ========================================================================= *)
(* Accessing individual problems.                                            *)
(* ========================================================================= *)

fun extract (p : 'a set) n =
  case List.find (fn {name, ...} => name = n) (#probs p) of SOME x => x
  | NONE => raise Fail ("Couldn't find a problem called \"" ^ n ^ "\"");

fun get p = #goal o extract (p ());

(* ========================================================================= *)
(* mlibProblems without equality.                                                *)
(* ========================================================================= *)

fun nonequality () =

mk_set "nonequality" "problems without equality from various sources" [

(* ------------------------------------------------------------------------- *)
(* Trivia (some of which demonstrate ex-bugs in provers).                    *)
(* ------------------------------------------------------------------------- *)

{name    = "TRUE",
 comment = "",
 goal    = `
T`},

{name    = "JH_test",
 comment = "",
 goal    = `
!x y. ?z. p x \/ p y ==> p z`},

{name    = "CYCLIC",
 comment = "",
 goal    = `
(!x. p (g (c x))) ==> ?z. p (g z)`},

{name    = "MN_bug",
 comment = "",
 goal    = `
(!x. ?y. f y x x) ==> ?z. f z 0 0`},

{name    = "RELATION_COMPOSITION",
 comment = "",
 goal    = `
(!x. ?y. p x y) /\ (!x. ?y. q x y) /\
(!x y z. p x y /\ q y z ==> r x z) ==> !x. ?y. r x y`},

(* ------------------------------------------------------------------------- *)
(* Propositional Logic.                                                      *)
(* ------------------------------------------------------------------------- *)

{name    = "PROP_1",
 comment = "",
 goal    = `
p ==> q <=> ~q ==> ~p`},

{name    = "PROP_2",
 comment = "",
 goal    = `
~~p <=> p`},

{name    = "PROP_3",
 comment = "",
 goal    = `
~(p ==> q) ==> q ==> p`},

{name    = "PROP_4",
 comment = "",
 goal    = `
~p ==> q <=> ~q ==> p`},

{name    = "PROP_5",
 comment = "",
 goal    = `
(p \/ q ==> p \/ r) ==> p \/ (q ==> r)`},

{name    = "PROP_6",
 comment = "",
 goal    = `
p \/ ~p`},

{name    = "PROP_7",
 comment = "",
 goal    = `
p \/ ~~~p`},

{name    = "PROP_8",
 comment = "",
 goal    = `
((p ==> q) ==> p) ==> p`},

{name    = "PROP_9",
 comment = "",
 goal    = `
(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)`},

{name    = "PROP_10",
 comment = "",
 goal    = `
(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)`},

{name    = "PROP_11",
 comment = "",
 goal    = `
p <=> p`},

{name    = "PROP_12",
 comment = "",
 goal    = `
((p <=> q) <=> r) <=> p <=> q <=> r`},

{name    = "PROP_13",
 comment = "",
 goal    = `
p \/ q /\ r <=> (p \/ q) /\ (p \/ r)`},

{name    = "PROP_14",
 comment = "",
 goal    = `
(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)`},

{name    = "PROP_15",
 comment = "",
 goal    = `
p ==> q <=> ~p \/ q`},

{name    = "PROP_16",
 comment = "",
 goal    = `
(p ==> q) \/ (q ==> p)`},

{name    = "PROP_17",
 comment = "",
 goal    = `
p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)`},

{name    = "MATHS4_EXAMPLE",
 comment = "",
 goal    = `
(a \/ ~k ==> g) /\ (g ==> q) /\ ~q ==> k`},

{name    = "LOGICPROOF_1996",
 comment = "",
 goal    = `
(p ==> r) /\ (~p ==> ~q) /\ (p \/ q) ==> p /\ r`},

{name    = "XOR_ASSOC",
 comment = "",
 goal    = `
~(~(p <=> q) <=> r) <=> ~(p <=> ~(q <=> r))`},

{name    = "ALL_3_CLAUSES",
 comment = "",
 goal    = `
(p \/ q \/ r) /\ (p \/ q \/ ~r) /\ (p \/ ~q \/ r) /\ (p \/ ~q \/ ~r) /\
(~p \/ q \/ r) /\ (~p \/ q \/ ~r) /\ (~p \/ ~q \/ r) /\
(~p \/ ~q \/ ~r) ==> F`},

{name    = "CLAUSE_SIMP",
 comment = "",
 goal    = `
(lit ==> clause) ==> (lit \/ clause <=> clause)`},

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

{name    = "P18",
 comment = "The drinker's principle.",
 goal    = `
?very_popular_guy. !whole_pub. drinks very_popular_guy ==> drinks whole_pub`},

{name    = "P19",
 comment = "",
 goal    = `
?x. !y z. (p y ==> q z) ==> p x ==> q x`},

{name    = "P20",
 comment = "",
 goal    = `
(!x y. ?z. !w. p x /\ q y ==> r z /\ u w) /\ (!x y. p x /\ q y) ==> ?z. r z`},

{name    = "P21",
 comment = "",
 goal    = `
(?x. p ==> q x) /\ (?x. q x ==> p) ==> ?x. p <=> q x`},

{name    = "P22",
 comment = "",
 goal    = `
(!x. p <=> q x) ==> (p <=> !x. q x)`},

{name    = "P23",
 comment = "",
 goal    = `
(!x. p \/ q x) <=> p \/ !x. q x`},

{name    = "P24",
 comment = "",
 goal    = `
~(?x. u x /\ q x) /\ (!x. p x ==> q x \/ r x) /\ ~(?x. p x ==> ?x. q x) /\
(!x. q x /\ r x ==> u x) ==> ?x. p x /\ r x`},

{name    = "P25",
 comment = "",
 goal    = `
(?x. p x) /\ (!x. u x ==> ~g x /\ r x) /\ (!x. p x ==> g x /\ u x) /\
((!x. p x ==> q x) \/ ?x. q x /\ p x) ==> ?x. q x /\ p x`},

{name    = "P26",
 comment = "",
 goal    = `
((?x. p x) <=> ?x. q x) /\ (!x y. p x /\ q y ==> (r x <=> u y)) ==>
((!x. p x ==> r x) <=> !x. q x ==> u x)`},

{name    = "P27",
 comment = "",
 goal    = `
(?x. p x /\ ~q x) /\ (!x. p x ==> r x) /\ (!x. u x /\ s x ==> p x) /\
(?x. r x /\ ~q x) ==> (!x. u x ==> ~r x) ==> !x. u x ==> ~s x`},

{name    = "P28",
 comment = "",
 goal    = `
(!x. p x ==> !x. q x) /\ ((!x. q x \/ r x) ==> ?x. q x /\ r x) /\
((?x. r x) ==> !x. l x ==> m x) ==> !x. p x /\ l x ==> m x`},

{name    = "P29",
 comment = "",
 goal    = `
(?x. p x) /\ (?x. g x) ==>
((!x. p x ==> h x) /\ (!x. g x ==> j x) <=>
 !x y. p x /\ g y ==> h x /\ j y)`},

{name    = "P30",
 comment = "",
 goal    = `
(!x. p x \/ g x ==> ~h x) /\ (!x. (g x ==> ~u x) ==> p x /\ h x) ==>
!x. u x`},

{name    = "P31",
 comment = "",
 goal    = `
~(?x. p x /\ (g x \/ h x)) /\ (?x. q x /\ p x) /\ (!x. ~h x ==> j x) ==>
?x. q x /\ j x`},

{name    = "P32",
 comment = "",
 goal    = `
(!x. p x /\ (g x \/ h x) ==> q x) /\ (!x. q x /\ h x ==> j x) /\
(!x. r x ==> h x) ==> !x. p x /\ r x ==> j x`},

{name    = "P33",
 comment = "",
 goal    = `
(!x. p a /\ (p x ==> p b) ==> p c) <=>
(!x. p a ==> p x \/ p c) /\ (p a ==> p b ==> p c)`},

{name    = "P34",
 comment = "This gives rise to 5184 clauses when naively converted to CNF!",
 goal    = `
((?x. !y. p x <=> p y) <=> (?x. q x) <=> !y. q y) <=>
(?x. !y. q x <=> q y) <=> (?x. p x) <=> !y. p y`},

{name    = "P35",
 comment = "",
 goal    = `
?x y. p x y ==> !x y. p x y`},

(* ------------------------------------------------------------------------- *)
(* Predicate logic without functions.                                        *)
(* ------------------------------------------------------------------------- *)

{name    = "P36",
 comment = "",
 goal    = `
(!x. ?y. p x y) /\ (!x. ?y. g x y) /\
(!x y. p x y \/ g x y ==> !z. p y z \/ g y z ==> h x z) ==> !x. ?y. h x y`},

{name    = "P37",
 comment = "",
 goal    = `
(!z. ?w. !x. ?y. (p x z ==> p y w) /\ p y z /\ (p y w ==> ?v. q v w)) /\
(!x z. ~p x z ==> ?y. q y z) /\ ((?x y. q x y) ==> !x. r x x) ==>
!x. ?y. r x y`},

{name    = "P38",
 comment = "",
 goal    = `
(!x. p a /\ (p x ==> ?y. p y /\ r x y) ==> ?z w. p z /\ r x w /\ r w z) <=>
!x.
  (~p a \/ p x \/ ?z w. p z /\ r x w /\ r w z) /\
  (~p a \/ ~(?y. p y /\ r x y) \/ ?z w. p z /\ r x w /\ r w z)`},

{name    = "P39",
 comment = "",
 goal    = `
~?x. !y. p y x <=> ~p y y`},

{name    = "P40",
 comment = "",
 goal    = `
(?y. !x. p x y <=> p x x) ==> ~!x. ?y. !z. p z y <=> ~p z x`},

{name    = "P41",
 comment = "",
 goal    = `
(!z. ?y. !x. p x y <=> p x z /\ ~p x x) ==> ~?z. !x. p x z`},

{name    = "P42",
 comment = "",
 goal    = `
~?y. !x. p x y <=> ~?z. p x z /\ p z x`},

{name    = "P43",
 comment = "",
 goal    = `
(!x y. q x y <=> !z. p z x <=> p z y) ==> !x y. q x y <=> q y x`},

{name    = "P44",
 comment = "",
 goal    = `
(!x. p x ==> (?y. g y /\ h x y) /\ ?y. g y /\ ~h x y) /\
(?x. j x /\ !y. g y ==> h x y) ==> ?x. j x /\ ~p x`},

{name    = "P45",
 comment = "",
 goal    = `
(!x. p x /\ (!y. g y /\ h x y ==> j x y) ==> !y. g y /\ h x y ==> r y) /\
~(?y. l y /\ r y) /\
(?x. p x /\ (!y. h x y ==> l y) /\ !y. g y /\ h x y ==> j x y) ==>
?x. p x /\ ~?y. g y /\ h x y`},

{name    = "P46",
 comment = "",
 goal    = `
(!x. p x /\ (!y. p y /\ h y x ==> g y) ==> g x) /\
((?x. p x /\ ~g x) ==> ?x. p x /\ ~g x /\ !y. p y /\ ~g y ==> j x y) /\
(!x y. p x /\ p y /\ h x y ==> ~j y x) ==> !x. p x ==> g x`},

{name    = "P50",
 comment = "",
 goal    = `
(!x. f0 a x \/ !y. f0 x y) ==> ?x. !y. f0 x y`},

(* ------------------------------------------------------------------------- *)
(* Full predicate logic.                                                     *)
(* ------------------------------------------------------------------------- *)

{name    = "LOGICPROOF_L10",
 comment = "",
 goal    = `
!x. ?y. ~(P y x <=> ~P y y)`},

{name    = "LOGICPROOF_1999",
 comment = "A non-theorem.",
 goal    = `
(?x. p x /\ q x) ==> ?x. p (f x x) \/ !y. q y`},

{name    = "P55",
 comment = "Example from Manthey and Bry, CADE-9. [JRH]",
 goal    = `
lives agatha /\ lives butler /\ lives charles /\
(killed agatha agatha \/ killed butler agatha \/ killed charles agatha) /\
(!x y. killed x y ==> hates x y /\ ~richer x y) /\
(!x. hates agatha x ==> ~hates charles x) /\
(hates agatha agatha /\ hates agatha charles) /\
(!x. lives x /\ ~richer x agatha ==> hates butler x) /\
(!x. hates agatha x ==> hates butler x) /\
(!x. ~hates x agatha \/ ~hates x butler \/ ~hates x charles) ==>
killed agatha agatha /\ ~killed butler agatha /\ ~killed charles agatha`},

{name    = "P57",
 comment = "",
 goal    = `
p (f a b) (f b c) /\ p (f b c) (f a c) /\
(!x y z. p x y /\ p y z ==> p x z) ==> p (f a b) (f a c)`},

{name    = "P58",
 comment = "See info-hol 1498 [JRH]",
 goal    = `
!x. ?v w. !y z. p x /\ q y ==> (p v \/ r w) /\ (r z ==> q v)`},

{name    = "P59",
 comment = "",
 goal    = `
(!x. p x <=> ~p (f x)) ==> ?x. p x /\ ~p (f x)`},

{name    = "P60",
 comment = "",
 goal    = `
!x. p x (f x) <=> ?y. (!z. p z y ==> p z (f x)) /\ p x y`},

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

{name    = "GILMORE_1",
 comment =
"Amazingly, this still seems non-trivial... in HOL [MESON_TAC] it\n" ^
"works at depth 45! [JRH]\n" ^
"Confirmed (depth=45, inferences=263702, time=148s), though if\n" ^
"lemmaizing is used then a lemma is discovered at depth 29 that allows\n" ^
"a much quicker proof (depth=30, inferences=10039, time=5.5s).",
 goal    = `
?x. !y z.
  (f y ==> g y <=> f x) /\ (f y ==> h y <=> g x) /\
  ((f y ==> g y) ==> h y <=> h x) ==> f z /\ g z /\ h z`},

{name    = "GILMORE_2",
 comment =
"This is not valid, according to Gilmore. [JRH]\n" ^
"Confirmed: ordered resolution quickly saturates.",
 goal    = `
?x y. !z.
  (f x z <=> f z y) /\ (f z y <=> f z z) /\ (f x y <=> f y x) ==>
  (f x y <=> f x z)`},

{name    = "GILMORE_3",
 comment = "",
 goal    = `
?x. !y z.
  ((f y z ==> g y ==> h x) ==> f x x) /\ ((f z x ==> g x) ==> h z) /\
  f x y ==> f z z`},

{name    = "GILMORE_4",
 comment = "",
 goal    = `
?x y. !z. (f x y ==> f y z /\ f z z) /\ (f x y /\ g x y ==> g x z /\ g z z)`},

{name    = "GILMORE_5",
 comment = "",
 goal    = `
(!x. ?y. f x y \/ f y x) /\ (!x y. f y x ==> f y y) ==> ?z. f z z`},

{name    = "GILMORE_6",
 comment = "",
 goal    = `
!x. ?y.
  (?w. !v. f w x ==> g v w /\ g w x) ==>
  (?w. !v. f w y ==> g v w /\ g w y) \/
  !z v. ?w. g v z \/ h w y z ==> g z w`},

{name    = "GILMORE_7",
 comment = "",
 goal    = `
(!x. k x ==> ?y. l y /\ (f x y ==> g x y)) /\
(?z. k z /\ !w. l w ==> f z w) ==> ?v w. k v /\ l w /\ g v w`},

{name    = "GILMORE_8",
 comment = "",
 goal    = `
?x. !y z.
  ((f y z ==> g y ==> !w. ?v. h w v x) ==> f x x) /\
  ((f z x ==> g x) ==> !w. ?v. h w v z) /\ f x y ==> f z z`},

{name    = "GILMORE_9",
 comment =
"mlibModel elimination (in HOL):\n" ^
"- With lemmaizing: (depth=18, inferences=15632, time=21s)\n" ^
"- Without: gave up waiting after (depth=25, inferences=2125072, ...)",
 goal    = `
!x. ?y. !z.
  ((!w. ?v. f y w v /\ g y w /\ ~h y x) ==>
   (!w. ?v. f x w v /\ g z u /\ ~h x z) ==>
   !w. ?v. f x w v /\ g y w /\ ~h x y) /\
  ((!w. ?v. f x w v /\ g y w /\ ~h x y) ==>
   ~(!w. ?v. f x w v /\ g z w /\ ~h x z) ==>
   (!w. ?v. f y w v /\ g y w /\ ~h y x) /\
   !w. ?v. f z w v /\ g y w /\ ~h z y)`},

{name    = "GILMORE_9a",
 comment =
"Translation of Gilmore procedure using separate definitions. [JRH]",
 goal    = `
(!x y. p x y <=> !w. ?v. f x w v /\ g y w /\ ~h x y) ==>
!x. ?y. !z.
  (p y x ==> p x z ==> p x y) /\ (p x y ==> ~p x z ==> p y x /\ p z y)`},

{name    = "BAD_CONNECTIONS",
 comment =
"The interesting example where connections make the proof longer. [JRH]",
 goal    = `
~a /\ (a \/ b) /\ (c \/ d) /\ (~b \/ e \/ f) /\ (~c \/ ~e) /\ (~c \/ ~f) /\
(~b \/ g \/ h) /\ (~d \/ ~g) /\ (~d \/ ~h) ==> F`},

{name    = "LOS",
 comment =
"The classic Los puzzle. (Clausal version MSC006-1 in the TPTP library.)\n" ^
"Note: this is actually in the decidable AE subset, though that doesn't\n" ^
"yield a very efficient proof. [JRH]",
 goal    = `
(!x y z. p x y ==> p y z ==> p x z) /\
(!x y z. q x y ==> q y z ==> q x z) /\ (!x y. q x y ==> q y x) /\
(!x y. p x y \/ q x y) ==> (!x y. p x y) \/ !x y. q x y`},

{name    = "STEAM_ROLLER",
 comment = "",
 goal    = `
((!x. p1 x ==> p0 x) /\ ?x. p1 x) /\ ((!x. p2 x ==> p0 x) /\ ?x. p2 x) /\
((!x. p3 x ==> p0 x) /\ ?x. p3 x) /\ ((!x. p4 x ==> p0 x) /\ ?x. p4 x) /\
((!x. p5 x ==> p0 x) /\ ?x. p5 x) /\ ((?x. q1 x) /\ !x. q1 x ==> q0 x) /\
(!x.
   p0 x ==>
   (!y. q0 y ==> r x y) \/
   !y. p0 y /\ s0 y x /\ (?z. q0 z /\ r y z) ==> r x y) /\
(!x y. p3 y /\ (p5 x \/ p4 x) ==> s0 x y) /\
(!x y. p3 x /\ p2 y ==> s0 x y) /\ (!x y. p2 x /\ p1 y ==> s0 x y) /\
(!x y. p1 x /\ (p2 y \/ q1 y) ==> ~r x y) /\
(!x y. p3 x /\ p4 y ==> r x y) /\ (!x y. p3 x /\ p5 y ==> ~r x y) /\
(!x. p4 x \/ p5 x ==> ?y. q0 y /\ r x y) ==>
?x y. p0 x /\ p0 y /\ ?z. q1 z /\ r y z /\ r x y`},

{name    = "MODEL_COMPLETENESS",
 comment =
"An incestuous example used to establish completeness characterization. [JRH]",
 goal    = `
(!w x. sentence x ==> holds w x \/ holds w (not x)) /\
(!w x. ~(holds w x /\ holds w (not x))) ==>
((!x.
    sentence x ==>
    (!w. models w s ==> holds w x) \/
    !w. models w s ==> holds w (not x)) <=>
 !w v.
   models w s /\ models v s ==>
   !x. sentence x ==> (holds w x <=> holds v x))`}

];

(* ========================================================================= *)
(* mlibProblems with equality.                                                   *)
(* ========================================================================= *)

fun equality () =

mk_set "equality" "equality problems from various sources" [

(* ------------------------------------------------------------------------- *)
(* Trivia (some of which demonstrate ex-bugs in the prover).                 *)
(* ------------------------------------------------------------------------- *)

{name    = "REFLEXIVITY",
 comment = "",
 goal    = `
c = c`},

{name    = "SYMMETRY",
 comment = "",
 goal    = `
!x y. x = y ==> y = x`},

{name    = "TRANSITIVITY",
 comment = "",
 goal    = `
!x y z. x = y /\ y = z ==> x = z`},

{name    = "TRANS_SYMM",
 comment = "",
 goal    = `
!x y z. x = y /\ y = z ==> z = x`},

{name    = "SUBSTITUTIVITY",
 comment = "",
 goal    = `
!x y. f x /\ x = y ==> f y`},

{name    = "CYCLIC_SUBSTITUTION_BUG",
 comment = "",
 goal    = `
!y. (!x. y = g (c x)) ==> ?z. y = g z`},

{name    = "JUDITA_1",
 comment = "",
 goal    = `
~(a = b) /\ (!x. x = c) ==> F`},

{name    = "JUDITA_1'",
 comment = "",
 goal    = `
~(a = b) /\ (!x y. x = y) ==> F`},

{name    = "JUDITA_2",
 comment = "",
 goal    = `
p a /\ ~p b /\ (!x. x = c) ==> F`},

{name    = "JUDITA_2'",
 comment = "",
 goal    = `
p a /\ ~p b /\ (!x y. x = y) ==> F`},

{name    = "JUDITA_3",
 comment = "",
 goal    = `
p a /\ p b /\ ~(a = b) /\ ~p c /\ (!x. x = a \/ x = d) ==> F`},

{name    = "INJECTIVITY",
 comment = "",
 goal    = `
(!x y. f x = f y ==> x = y) /\ f a = f b ==> a = b`},

{name    = "INJECTIVITY2",
 comment = "",
 goal    = `
(!x y. g (f x) = g (f y) ==> x = y) /\ f a = f b ==> a = b`},

{name    = "SELF_REWRITE",
 comment = "",
 goal    = `
f (g (h c)) = h c /\ g (h c) = b /\ f b = a /\ (!x. ~(a = h x)) ==> F`},

(* ------------------------------------------------------------------------- *)
(* Simple equality problems.                                                 *)
(* ------------------------------------------------------------------------- *)

{name    = "P48",
 comment = "",
 goal    = `
(a = b \/ c = d) /\ (a = c \/ b = d) ==> a = d \/ b = c`},

{name    = "P49",
 comment = "",
 goal    = `
(?x y. !z. z = x \/ z = y) /\ p a /\ p b /\ ~(a = b) ==> !x. p x`},

{name    = "P51",
 comment = "",
 goal    = `
(?z w. !x y. f0 x y <=> x = z /\ y = w) ==>
?z. !x. (?w. !y. f0 x y <=> y = w) <=> x = z`},

{name    = "P52",
 comment = "",
 goal    = `
(?z w. !x y. f0 x y <=> x = z /\ y = w) ==>
?w. !y. (?z. !x. f0 x y <=> x = z) <=> y = w`},

{name    = "UNSKOLEMIZED_MELHAM",
 comment = "The Melham problem after an inverse skolemization step.",
 goal    = `
(!x y. g x = g y ==> f x = f y) ==> !y. ?w. !x. y = g x ==> w = f x`},
 
{name    = "CONGRUENCE_CLOSURE_EXAMPLE",
 comment = "The example always given for congruence closure.",
 goal    = `
!x. f (f (f (f (f x)))) = x /\ f (f (f x)) = x ==> f x = x`},

{name    = "EWD",
 comment =
"A simple example (see EWD1266a and the application to Morley's\n" ^
"theorem). [JRH]",
 goal    = `
(!x. f x ==> g x) /\ (?x. f x) /\ (!x y. g x /\ g y ==> x = y) ==>
!y. g y ==> f y`},

{name    = "EWD'",
 comment = "",
 goal    = `
(!x. f (f x) = f x) /\ (!x. ?y. f y = x) ==> !x. f x = x`},

{name    = "JIA",
 comment = "Needs only the K combinator",
 goal    = `
(!x y. k % x % y = x) /\ (!v. P (v % a) a) /\ (!w. Q (w % b) b) ==>
!z. ?x y. P (z % x % y) x /\ Q (z % x % y) y`},

{name    = "WISHNU",
 comment = "Wishnu Prasetya's example. [JRH]",
 goal    = `
(?x. x = f (g x) /\ !x'. x' = f (g x') ==> x = x') <=>
?y. y = g (f y) /\ !y'. y' = g (f y') ==> y = y'`},

{name    = "AGATHA",
 comment = "An equality version of the Agatha puzzle. [JRH]",
 goal    = `
(?x. lives x /\ killed x agatha) /\
(lives agatha /\ lives butler /\ lives charles) /\
(!x. lives x ==> x = agatha \/ x = butler \/ x = charles) /\
(!x y. killed x y ==> hates x y) /\ (!x y. killed x y ==> ~richer x y) /\
(!x. hates agatha x ==> ~hates charles x) /\
(!x. ~(x = butler) ==> hates agatha x) /\
(!x. ~richer x agatha ==> hates butler x) /\
(!x. hates agatha x ==> hates butler x) /\ (!x. ?y. ~hates x y) /\
~(agatha = butler) ==>
killed agatha agatha /\ ~killed butler agatha /\ ~killed charles agatha`},

{name    = "DIVIDES_9",
 comment = "",
 goal    = `
(!x y. x * y = y * x) /\ (!x y z. x * y * z = x * (y * z)) /\
(!x y. divides x y <=> ?z. y = z * x) ==>
!x y z. divides x y ==> divides x (z * y)`},

{name    = "DIVIDES_9'",
 comment = "",
 goal    = `
(!x y. x * y = y * x) /\ (!x y z. x * y * z = x * (y * z)) /\
(!x y. divides x y <=> ?z. z * x = y) ==>
!x y z. divides x y ==> divides x (z * y)`},

(* ------------------------------------------------------------------------- *)
(* Group theory examples.                                                    *)
(* ------------------------------------------------------------------------- *)

{name    = "GROUP_INVERSE_INVERSE",
 comment = "",
 goal    = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. i (i x) = x`},

{name    = "GROUP_RIGHT_INVERSE",
 comment = "Size 18, 61814 seconds. [JRH]",
 goal    = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. x * i x = e`},

{name    = "GROUP_RIGHT_IDENTITY",
 comment = "",
 goal    = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. x * e = x`},

{name    = "GROUP_IDENTITY_EQUIV",
 comment = "",
 goal    = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\
(!x. i x * x = e) ==> !x. x * x = x <=> x = e`},

{name    = "KLEIN_GROUP_COMMUTATIVE",
 comment = "",
 goal    = `
(!x y z. x * (y * z) = x * y * z) /\ (!x. e * x = x) /\ (!x. x * e = x) /\
(!x. x * x = e) ==> !x y. x * y = y * x`},

(* ------------------------------------------------------------------------- *)
(* Ring theory examples.                                                     *)
(* ------------------------------------------------------------------------- *)

{name    = "JACOBSON_2",
 comment = "",
 goal    = `
(!x. 0 + x = x) /\ (!x. x + 0 = x) /\ (!x. n x + x = 0) /\
(!x. x + n x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y. x + y = y + x) /\ (!x y z. x * (y * z) = x * y * z) /\
(!x y z. x * (y + z) = x * y + x * z) /\
(!x y z. (x + y) * z = x * z + y * z) /\ (!x. x * x = x) ==>
!x y. x * y = y * x`},

{name    = "JACOBSON_3",
 comment = "",
 goal    = `
(!x. 0 + x = x) /\ (!x. x + 0 = x) /\ (!x. n x + x = 0) /\
(!x. x + n x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y. x + y = y + x) /\ (!x y z. x * (y * z) = x * y * z) /\
(!x y z. x * (y + z) = x * y + x * z) /\
(!x y z. (x + y) * z = x * z + y * z) /\ (!x. x * (x * x) = x) ==>
!x y. x * y = y * x`}

];

(* ========================================================================= *)
(* Some sample problems from the TPTP archive.                               *)
(* Note: for brevity some relation/function names have been shortened.       *)
(* ========================================================================= *)

fun tptp () =

mk_set "tptp" "sample problems from the TPTP collection"

[

{name    = "ALG005-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. ~(x = y) \/ x + z = y + z) /\
(!x y z. ~(x = y) \/ z + x = z + y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) /\ (!x y. x + (y + x) = x) /\
(!x y. x + (x + y) = y + (y + x)) /\
(!x y z. x + y + z = x + z + (y + z)) /\ (!x y. x * y = x + (x + y)) ==>
~(a * b * c = a * (b * c)) ==> F`},

{name    = "ALG006-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. ~(x = y) \/ x + z = y + z) /\
(!x y z. ~(x = y) \/ z + x = z + y) /\ (!x y. x + (y + x) = x) /\
(!x y. x + (x + y) = y + (y + x)) /\
(!x y z. x + y + z = x + z + (y + z)) ==> ~(a + c + b = a + b + c) ==> F`},

{name    = "BOO021-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. ~(x = y) \/ x + z = y + z) /\
(!x y z. ~(x = y) \/ z + x = z + y) /\ (!x y. ~(x = y) \/ i x = i y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) /\ (!x y. (x + y) * y = y) /\
(!x y z. x * (y + z) = y * x + z * x) /\ (!x. x + i x = 1) /\
(!x y. x * y + y = y) /\ (!x y z. x + y * z = (y + x) * (z + x)) /\
(!x. x * i x = 0) ==> ~(b * a = a * b) ==> F`},

{name    = "COL058-2",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. r (r 0 x) y = r x (r y y)) /\ (!x y z. ~(x = y) \/ r x z = r y z) /\
(!x y z. ~(x = y) \/ r z x = r z y) ==>
~(r (r (r 0 (r (r 0 (r 0 0)) (r 0 (r 0 0)))) (r 0 (r 0 0)))
  (r (r 0 (r (r 0 (r 0 0)) (r 0 (r 0 0)))) (r 0 (r 0 0))) =
  r (r 0 (r (r 0 (r 0 0)) (r 0 (r 0 0)))) (r 0 (r 0 0))) ==> F`},

{name    = "COL060-3",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. b % x % y % z = x % (y % z)) /\ (!x y. t % x % y = y % x) /\
(!x y z. ~(x = y) \/ x % z = y % z) /\
(!x y z. ~(x = y) \/ z % x = z % y) ==>
~(b % (b % (t % b) % b) % t % (x) % (y) % (z) = (y) % ((x) % (z))) ==> F`},

{name    = "GEO002-4",
 comment = "",
 goal    = `
(!x y z v. ~between x y z \/ ~between y v z \/ between x y v) /\
(!x y z. ~equidistant x y z z \/ x == y) /\
(!x y z v w.
   ~between x y z \/ ~between v z w \/
   between x (outer_pasch y x v w z) v) /\
(!x y z v w.
   ~between x y z \/ ~between v z w \/
   between w y (outer_pasch y x v w z)) /\
(!x y z v. between x y (extension x y z v)) /\
(!x y z v. equidistant x (extension y x z v) z v) /\
(!x y z v. ~(x == y) \/ ~between z v x \/ between z v y) ==>
~between a a b ==> F`},

{name    = "GEO036-2",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x y. equidistant x y y x) /\
(!x y z x' y' z'.
   ~equidistant x y z x' \/ ~equidistant x y y' z' \/
   equidistant z x' y' z') /\ (!x y z. ~equidistant x y z z \/ x = y) /\
(!x y z v. between x y (extension x y z v)) /\
(!x y z v. equidistant x (extension y x z v) z v) /\
(!x y z v w x' y' z'.
   ~equidistant x y z v \/ ~equidistant y w v x' \/
   ~equidistant x y' z z' \/ ~equidistant y y' v z' \/ ~between x y w \/
   ~between z v x' \/ x = y \/ equidistant w y' x' z') /\
(!x y. ~between x y x \/ x = y) /\
(!x y z v w.
   ~between x y z \/ ~between v w z \/
   between y (inner_pasch x y z w v) v) /\
(!x y z v w.
   ~between x y z \/ ~between v w z \/
   between w (inner_pasch x y z w v) x) /\
~between lower_dimension_point_1 lower_dimension_point_2
 lower_dimension_point_3 /\
~between lower_dimension_point_2 lower_dimension_point_3
 lower_dimension_point_1 /\
~between lower_dimension_point_3 lower_dimension_point_1
 lower_dimension_point_2 /\
(!x y z v w.
   ~equidistant x y x z \/ ~equidistant v y v z \/ ~equidistant w y w z \/
   between x v w \/ between v w x \/ between w x v \/ y = z) /\
(!x y z v w.
   ~between x y z \/ ~between v y w \/ x = y \/
   between x v (euclid1 x v y w z)) /\
(!x y z v w.
   ~between x y z \/ ~between v y w \/ x = y \/
   between x w (euclid2 x v y w z)) /\
(!x y z v w.
   ~between x y z \/ ~between v y w \/ x = y \/
   between (euclid1 x v y w z) z (euclid2 x v y w z)) /\
(!x y z x' y' z'.
   ~equidistant x y x z \/ ~equidistant x x' x y' \/ ~between x y x' \/
   ~between y z' x' \/ between z (continuous x y z z' x' y') y') /\
(!x y z x' y' z'.
   ~equidistant x y x z \/ ~equidistant x x' x y' \/ ~between x y x' \/
   ~between y z' x' \/ equidistant x z' x (continuous x y z z' x' y')) /\
(!x y z v. ~(x = y) \/ ~between x z v \/ between y z v) /\
(!x y z v. ~(x = y) \/ ~between z x v \/ between z y v) /\
(!x y z v. ~(x = y) \/ ~between z v x \/ between z v y) /\
(!x y z v w. ~(x = y) \/ ~equidistant x z v w \/ equidistant y z v w) /\
(!x y z v w. ~(x = y) \/ ~equidistant z x v w \/ equidistant z y v w) /\
(!x y z v w. ~(x = y) \/ ~equidistant z v x w \/ equidistant z v y w) /\
(!x y z v w. ~(x = y) \/ ~equidistant z v w x \/ equidistant z v w y) /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch x z x' y' z' = inner_pasch y z x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x x' y' z' = inner_pasch z y x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x' x y' z' = inner_pasch z x' y y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x' y' x z' = inner_pasch z x' y' y z') /\
(!x y z x' y' z'.
   ~(x = y) \/ inner_pasch z x' y' z' x = inner_pasch z x' y' z' y) /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 x z x' y' z' = euclid1 y z x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x x' y' z' = euclid1 z y x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x' x y' z' = euclid1 z x' y y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x' y' x z' = euclid1 z x' y' y z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid1 z x' y' z' x = euclid1 z x' y' z' y) /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 x z x' y' z' = euclid2 y z x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x x' y' z' = euclid2 z y x' y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x' x y' z' = euclid2 z x' y y' z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x' y' x z' = euclid2 z x' y' y z') /\
(!x y z x' y' z'.
   ~(x = y) \/ euclid2 z x' y' z' x = euclid2 z x' y' z' y) /\
(!x y z v w. ~(x = y) \/ extension x z v w = extension y z v w) /\
(!x y z v w. ~(x = y) \/ extension z x v w = extension z y v w) /\
(!x y z v w. ~(x = y) \/ extension z v x w = extension z v y w) /\
(!x y z v w. ~(x = y) \/ extension z v w x = extension z v w y) /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous x z v w x' y' = continuous y z v w x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z x v w x' y' = continuous z y v w x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v x w x' y' = continuous z v y w x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v w x x' y' = continuous z v w y x' y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v w x' x y' = continuous z v w x' y y') /\
(!x y z v w x' y'.
   ~(x = y) \/ continuous z v w x' y' x = continuous z v w x' y' y) ==>
lower_dimension_point_1 = lower_dimension_point_2 \/
lower_dimension_point_2 = lower_dimension_point_3 \/
lower_dimension_point_1 = lower_dimension_point_3 ==> F`},

{name    = "GRP010-4",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x y. ~(x = y) \/ i x = i y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) /\ (!x y z. x * y * z = x * (y * z)) /\
(!x. 1 * x = x) /\ (!x. i x * x = 1) /\ c * b = 1 ==> ~(b * c = 1) ==> F`},

{name    = "GRP057-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z v. x * i (i (i y * (i x * z)) * v * i (y * v)) = z) /\
(!x y. ~(x = y) \/ i x = i y) /\ (!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) ==>
~(i a1 * a1 = i b1 * b1) \/ ~(i b2 * b2 * a2 = a2) \/
~(a3 * b3 * c3 = a3 * (b3 * c3)) ==> F`},

{name    = "GRP086-1",
 comment = "Bug check: used to be unsolvable without sticky constraints",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. x * (y * z * i (x * z)) = y) /\ (!x y. ~(x = y) \/ i x = i y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) ==>
(!x y.
   ~(i a1 * a1 = i b1 * b1) \/ ~(i b2 * b2 * a2 = a2) \/
   ~(a3 * b3 * c3 = a3 * (b3 * c3)) \/ ~(x * y = y * x)) ==> F`},

{name    = "GRP104-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z.
   double_divide x
   (inverse
    (double_divide
     (inverse (double_divide (double_divide x y) (inverse z))) y)) = z) /\
(!x y. x * y = inverse (double_divide y x)) /\
(!x y. ~(x = y) \/ inverse x = inverse y) /\
(!x y z. ~(x = y) \/ x * z = y * z) /\
(!x y z. ~(x = y) \/ z * x = z * y) /\
(!x y z. ~(x = y) \/ double_divide x z = double_divide y z) /\
(!x y z. ~(x = y) \/ double_divide z x = double_divide z y) ==>
(!x y.
   ~(inverse a1 * a1 = inverse b1 * b1) \/ ~(inverse b2 * b2 * a2 = a2) \/
   ~(a3 * b3 * c3 = a3 * (b3 * c3)) \/ ~(x * y = y * x)) ==> F`},

{name    = "GRP128-4.003",
 comment = "",
 goal    = `
(!x y.
   ~elt x \/ ~elt y \/ product e_1 x y \/ product e_2 x y \/
   product e_3 x y) /\
(!x y.
   ~elt x \/ ~elt y \/ product x e_1 y \/ product x e_2 y \/
   product x e_3 y) /\ elt e_1 /\ elt e_2 /\ elt e_3 /\ ~(e_1 == e_2) /\
~(e_1 == e_3) /\ ~(e_2 == e_1) /\ ~(e_2 == e_3) /\ ~(e_3 == e_1) /\
~(e_3 == e_2) /\
(!x y.
   ~elt x \/ ~elt y \/ product x y e_1 \/ product x y e_2 \/
   product x y e_3) /\
(!x y z v. ~product x y z \/ ~product x y v \/ z == v) /\
(!x y z v. ~product x y z \/ ~product x v z \/ y == v) /\
(!x y z v. ~product x y z \/ ~product v y z \/ x == v) ==>
(!x y z v. product x y z \/ ~product x z v \/ ~product z y v) /\
(!x y z v. product x y z \/ ~product v x z \/ ~product v y x) /\
(!x y z v. ~product x y z \/ ~product z y v \/ product x z v) ==> F`},

{name    = "HEN006-3",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x <= y) \/ x / y = 0) /\ (!x y. ~(x / y = 0) \/ x <= y) /\
(!x y. x / y <= x) /\ (!x y z. x / y / (z / y) <= x / z / y) /\
(!x. 0 <= x) /\ (!x y. ~(x <= y) \/ ~(y <= x) \/ x = y) /\ (!x. x <= 1) /\
(!x y z. ~(x = y) \/ x / z = y / z) /\
(!x y z. ~(x = y) \/ z / x = z / y) /\
(!x y z. ~(x = y) \/ ~(x <= z) \/ y <= z) /\
(!x y z. ~(x = y) \/ ~(z <= x) \/ z <= y) /\ a / b <= d ==>
~(a / d <= b) ==> F`},

{name    = "LAT005-3",
 comment = "SAM's lemma",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x. meet x x = x) /\
(!x. join x x = x) /\ (!x y. meet x (join x y) = x) /\
(!x y. join x (meet x y) = x) /\ (!x y. meet x y = meet y x) /\
(!x y. join x y = join y x) /\
(!x y z. meet (meet x y) z = meet x (meet y z)) /\
(!x y z. join (join x y) z = join x (join y z)) /\
(!x y z. ~(x = y) \/ join x z = join y z) /\
(!x y z. ~(x = y) \/ join z x = join z y) /\
(!x y z. ~(x = y) \/ meet x z = meet y z) /\
(!x y z. ~(x = y) \/ meet z x = meet z y) /\ (!x. meet x 0 = 0) /\
(!x. join x 0 = x) /\ (!x. meet x 1 = x) /\ (!x. join x 1 = 1) /\
(!x y z. ~(meet x y = x) \/ meet y (join x z) = join x (meet z y)) /\
(!x y. ~complement x y \/ meet x y = 0) /\
(!x y. ~complement x y \/ join x y = 1) /\
(!x y. ~(meet x y = 0) \/ ~(join x y = 1) \/ complement x y) /\
(!x y z. ~(x = y) \/ ~complement x z \/ complement y z) /\
(!x y z. ~(x = y) \/ ~complement z x \/ complement z y) /\
complement r1 (join a b) /\ complement r2 (meet a b) ==>
~(r1 = meet (join r1 (meet r2 b)) (join r1 (meet r2 a))) ==> F`},

{name    = "LCL009-1",
 comment = "",
 goal    = `
(!x y. ~p (x - y) \/ ~p x \/ p y) /\
(!x y z. p (x - y - (z - y - (x - z)))) ==>
~p (a - b - c - (a - (b - c))) ==> F`},

{name    = "LCL087-1",
 comment =
"Solved quickly by resolution when NOT tracking term-ordering constraints.",
 goal    = `
(!x y. ~p (implies x y) \/ ~p x \/ p y) /\
(!x y z v w.
   p
   (implies (implies (implies x y) (implies z v))
    (implies w (implies (implies v x) (implies z x))))) ==>
~p (implies a (implies b a)) ==> F`},

{name    = "LCL107-1",
 comment = "A very small problem that's tricky to prove.",
 goal    = `
(!x y. ~p (x - y) \/ ~p x \/ p y) /\
(!x y z v w x' y'.
   p
   (x - y - z - (v - w - (x' - w - (x' - v) - y')) -
    (z - (y - x - y')))) ==> ~p (a - b - c - (e - b - (a - e - c))) ==> F`},

{name    = "LCL187-1",
 comment = "",
 goal    = `
(!x. axiom (or (not (or x x)) x)) /\ (!x y. axiom (or (not x) (or y x))) /\
(!x y. axiom (or (not (or x y)) (or y x))) /\
(!x y z. axiom (or (not (or x (or y z))) (or y (or x z)))) /\
(!x y z. axiom (or (not (or (not x) y)) (or (not (or z x)) (or z y)))) /\
(!x. theorem x \/ ~axiom x) /\
(!x y. theorem x \/ ~axiom (or (not y) x) \/ ~theorem y) /\
(!x y z.
   theorem (or (not x) y) \/ ~axiom (or (not x) z) \/
   ~theorem (or (not z) y)) ==>
~theorem (or (not p) (or (not (not p)) q)) ==> F`},

{name    = "LDA007-3",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y z. f x (f y z) = f (f x y) (f x z)) /\
(!x y z. ~(x = y) \/ f x z = f y z) /\
(!x y z. ~(x = y) \/ f z x = f z y) /\ tt = f t t /\ ts = f t s /\
tt_ts = f tt ts /\ tk = f t k /\ tsk = f ts k ==>
~(f t tsk = f tt_ts tk) ==> F`},

{name    = "NUM001-1",
 comment = "",
 goal    = `
(!x. x == x) /\ (!x y z. ~(x == y) \/ ~(y == z) \/ x == z) /\
(!x y. x + y == y + x) /\ (!x y z. x + (y + z) == x + y + z) /\
(!x y. x + y - y == x) /\ (!x y. x == x + y - y) /\
(!x y z. x - y + z == x + z - y) /\ (!x y z. x + y - z == x - z + y) /\
(!x y z v. ~(x == y) \/ ~(z == x + v) \/ z == y + v) /\
(!x y z v. ~(x == y) \/ ~(z == v + x) \/ z == v + y) /\
(!x y z v. ~(x == y) \/ ~(z == x - v) \/ z == y - v) /\
(!x y z v. ~(x == y) \/ ~(z == v - x) \/ z == v - y) ==>
~(a + b + c == a + (b + c)) ==> F`},

{name    = "NUM014-1",
 comment = "",
 goal    = `
(!x. product x x (square x)) /\
(!x y z. ~product x y z \/ product y x z) /\
(!x y z. ~product x y z \/ divides x z) /\
(!x y z v.
   ~prime x \/ ~product y z v \/ ~divides x v \/ divides x y \/
   divides x z) /\ prime a /\ product a (square c) (square b) ==>
~divides a b ==> F`},

{name    = "PUZ001-1",
 comment = "",
 goal    = `
lives agatha /\ lives butler /\ lives charles /\
(!x y. ~killed x y \/ ~richer x y) /\
(!x. ~hates agatha x \/ ~hates charles x) /\
(!x. ~hates x agatha \/ ~hates x butler \/ ~hates x charles) /\
hates agatha agatha /\ hates agatha charles /\
(!x y. ~killed x y \/ hates x y) /\
(!x. ~hates agatha x \/ hates butler x) /\
(!x. ~lives x \/ richer x agatha \/ hates butler x) ==>
killed butler agatha \/ killed charles agatha ==> F`},

{name    = "PUZ011-1",
 comment =
"Curiosity: solved trivially by meson without cache cutting, but not with.",
 goal    = `
ocean atlantic /\ ocean indian /\ borders atlantic brazil /\
borders atlantic uruguay /\ borders atlantic (venesuela) /\
borders atlantic (zaire) /\ borders atlantic nigeria /\
borders atlantic angola /\ borders indian india /\
borders indian pakistan /\ borders indian iran /\ borders indian somalia /\
borders indian kenya /\ borders indian tanzania /\ south_american brazil /\
south_american uruguay /\ south_american (venesuela) /\ african (zaire) /\
african nigeria /\ african angola /\ african somalia /\ african kenya /\
african tanzania /\ asian india /\ asian pakistan /\ asian iran ==>
(!x y z.
   ~ocean x \/ ~borders x y \/ ~african y \/ ~borders x z \/ ~asian z) ==>
F`},

{name    = "PUZ020-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x = y) \/ statement_by x = statement_by y) /\
(!x. ~person x \/ knight x \/ knave x) /\
(!x. ~person x \/ ~knight x \/ ~knave x) /\
(!x y. ~says x y \/ a_truth y \/ ~a_truth y) /\
(!x y. ~says x y \/ ~(x = y)) /\ (!x y. ~says x y \/ y = statement_by x) /\
(!x y. ~person x \/ ~(x = statement_by y)) /\
(!x. ~person x \/ ~a_truth (statement_by x) \/ knight x) /\
(!x. ~person x \/ a_truth (statement_by x) \/ knave x) /\
(!x y. ~(x = y) \/ ~knight x \/ knight y) /\
(!x y. ~(x = y) \/ ~knave x \/ knave y) /\
(!x y. ~(x = y) \/ ~person x \/ person y) /\
(!x y z. ~(x = y) \/ ~says x z \/ says y z) /\
(!x y z. ~(x = y) \/ ~says z x \/ says z y) /\
(!x y. ~(x = y) \/ ~a_truth x \/ a_truth y) /\
(!x y. ~knight x \/ ~says x y \/ a_truth y) /\
(!x y. ~knave x \/ ~says x y \/ ~a_truth y) /\ person husband /\
person (wife) /\ ~(husband = (wife)) /\
says husband (statement_by husband) /\
(~a_truth (statement_by husband) \/ ~knight husband \/ knight (wife)) /\
(a_truth (statement_by husband) \/ ~knight husband) /\
(a_truth (statement_by husband) \/ knight (wife)) /\
(~knight (wife) \/ a_truth (statement_by husband)) ==> ~knight husband ==>
F`},

{name    = "ROB002-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\ (!x y. x + y = y + x) /\
(!x y z. x + y + z = x + (y + z)) /\
(!x y. negate (negate (x + y) + negate (x + negate y)) = x) /\
(!x y z. ~(x = y) \/ x + z = y + z) /\
(!x y z. ~(x = y) \/ z + x = z + y) /\
(!x y. ~(x = y) \/ negate x = negate y) /\ (!x. negate (negate x) = x) ==>
~(negate (a + negate b) + negate (negate a + negate b) = b) ==> F`}

];

(* ========================================================================= *)
(* Some problems from HOL.                                                   *)
(* ========================================================================= *)

fun hol () =

mk_set "hol" "HOL subgoals sent to MESON_TAC" [

{name = "Coder_4_0",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth /\
(!x y z. ~(APPEND % x % y = APPEND % z % y) \/ x = z) /\
(!x y z. APPEND % x % y = APPEND % z % y \/ ~(x = z)) /\
(!x y z. APPEND % x % y = APPEND % x % z \/ ~(y = z)) /\
(!x y z. ~(APPEND % x % y = APPEND % x % z) \/ y = z) ==>
$ ((wf_encoder) % p % e) /\ (!x. e % x = f % x \/ ~$ (p % x)) /\
$ ((wf_encoder) % p % f) /\ $ (p % q) /\ $ (p % q') /\
APPEND % (f % q) % r = APPEND % (f % q') % r' /\ q = q' /\ ~(r' = r) ==> F`},

{name = "DeepSyntax_47",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_add x z = int_add y v) /\
(!x y. ~(x = y) \/ int_neg x = int_neg y) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ eval_form y v \/ ~eval_form x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z v.
   int_lt (int_add x y) (int_add z v) \/ ~int_lt x z \/ ~int_lt y v) /\
(!x. int_add x (int_of_num 0) = x) /\
(!x. int_add x (int_neg x) = int_of_num 0) /\
(!x y z. int_add x (int_add y z) = int_add (int_add x y) z) ==>
int_lt (int_neg d) (int_of_num 0) /\ eval_form g (x) /\
int_lt (int_add (x) d) i /\ ~int_lt (x) i ==> F`},

{name = "divides_9",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y * z) = x * y * z) /\ (!x y. x * y = y * x) /\
(!x y. ~divides x y \/ y = gv1556 x y * x) /\
(!x y z. divides x y \/ ~(y = z * x)) ==>
divides gv1546 gv1547 /\ ~divides gv1546 (gv1547 * gv1548) ==> F`},

{name = "Encode_28",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ MOD x z = MOD y v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT2 x = BIT2 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ EXP x z = EXP y v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ DIV x z = DIV y v) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. x * y = y * x) /\
(!x y z. MOD (MOD x (y * z)) y = MOD x y \/ ~(0 < y) \/ ~(0 < z)) ==>
(!x.
   MOD x (NUMERAL (BIT2 (ZERO))) = 0 \/
   MOD x (NUMERAL (BIT2 (ZERO))) = NUMERAL (BIT1 (ZERO))) /\
MOD
(DIV (x) (NUMERAL (BIT2 (ZERO))) * NUMERAL (BIT2 (ZERO)) +
 MOD (x) (NUMERAL (BIT2 (ZERO))))
(NUMERAL (BIT2 (ZERO)) * EXP (NUMERAL (BIT2 (ZERO))) m) =
MOD
(DIV (y) (NUMERAL (BIT2 (ZERO))) * NUMERAL (BIT2 (ZERO)) +
 MOD (y) (NUMERAL (BIT2 (ZERO))))
(NUMERAL (BIT2 (ZERO)) * EXP (NUMERAL (BIT2 (ZERO))) m) /\
0 < EXP (NUMERAL (BIT2 (ZERO))) m /\ 0 < NUMERAL (BIT2 (ZERO)) /\
(!x y.
   ~(MOD (x * NUMERAL (BIT2 (ZERO)) + MOD (x) (NUMERAL (BIT2 (ZERO))))
     (NUMERAL (BIT2 (ZERO))) =
     MOD (y * NUMERAL (BIT2 (ZERO)) + MOD (y) (NUMERAL (BIT2 (ZERO))))
     (NUMERAL (BIT2 (ZERO))))) ==> F`},

{name = "euclid_4",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y * z) = x * y * z) /\
(!x y. ~divides x y \/ y = x * gv5371 x y) /\
(!x y z. divides x y \/ ~(y = x * z)) ==>
divides gv5316 gv5317 /\ divides gv5315 gv5316 /\
~divides gv5315 gv5317 ==> F`},

{name = "euclid_8",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. x * y = y * x) /\ (!x y z. x * (y * z) = x * y * z) /\
(!x y. ~divides x y \/ y = x * gv7050 x y) /\
(!x y z. divides x y \/ ~(y = x * z)) ==>
divides gv7000 gv7001 /\ ~divides gv7000 (gv7002 * gv7001) ==> F`},

{name = "extra_arith_6",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. ~(SUC x * y = SUC x * z) \/ y = z) /\
(!x y z. SUC x * y = SUC x * z \/ ~(y = z)) /\
(!x y z. x * (y * z) = x * y * z) /\ (!x y. x * y = y * x) ==>
SUC n * b = q * (SUC n * a) /\ 0 < SUC n /\ ~(b = q * a) ==> F`},

{name = "extra_real_5",
 comment = "",
 goal = `
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth ==>
(!x y z v.
   $ (real_lt % x % (sup % P)) \/ ~$ (P % y) \/ ~$ (real_lt % x % y) \/
   ~$ (P % z) \/ ~$ (real_lte % (gv6327 % v) % v)) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (P % (gv6327 % x)) \/ ~$ (P % y) \/
   ~$ (real_lte % (gv6327 % z) % z)) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (real_lt % x % (gv6327 % x)) \/
   ~$ (P % y) \/ ~$ (real_lte % (gv6327 % z) % z)) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (real_lt % x % (gv6327 % x)) \/
   ~$ (P % y) \/ $ (P % (gv6327 % z))) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (P % (gv6327 % x)) \/ ~$ (P % y) \/
   $ (P % (gv6327 % z))) /\
(!x y z v.
   $ (real_lt % x % (sup % P)) \/ ~$ (P % y) \/ ~$ (real_lt % x % y) \/
   ~$ (P % z) \/ $ (P % (gv6327 % v))) /\ $ (P % (x)) /\
(!x. $ (real_lte % x % (z)) \/ ~$ (P % x)) /\
(!x.
   $ (real_lt % (gv6328 % x) % (gv6329 % x)) \/
   $ (real_lt % (gv6328 % x) % x)) /\
(!x. $ (P % (gv6329 % x)) \/ $ (real_lt % (gv6328 % x) % x)) /\
(!x y.
   ~$ (real_lt % (gv6328 % x) % y) \/ ~$ (P % y) \/
   ~$ (real_lt % (gv6328 % x) % x)) ==> F`},

{name = "gcd_19",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\ (!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y <= v \/ ~(x <= z)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y + z) = x * y + x * z) /\ (!x y. x + SUC y = SUC (x + y)) /\
(!x y. SUC x + y = SUC (x + y)) /\ (!x. x + 0 = x) /\ (!x. 0 + x = x) /\
(!x y. x * SUC y = x + x * y) /\ (!x y. SUC x * y = x * y + y) /\
(!x. x * NUMERAL (BIT1 (ZERO)) = x) /\
(!x. NUMERAL (BIT1 (ZERO)) * x = x) /\ (!x. x * 0 = 0) /\
(!x. 0 * x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y z. divides x y \/ ~divides x z \/ ~divides x (z + y)) ==>
~((x) + (z) <= (x)) /\ divides c (d * SUC (x)) /\
divides c (d * SUC ((x) + (z))) /\ ~divides c (d * (z)) ==> F`},
 
{name = "gcd_20",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\ (!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y <= v \/ ~(x <= z)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y + z) = x * y + x * z) /\ (!x y. x + SUC y = SUC (x + y)) /\
(!x y. SUC x + y = SUC (x + y)) /\ (!x. x + 0 = x) /\ (!x. 0 + x = x) /\
(!x y. x * SUC y = x + x * y) /\ (!x y. SUC x * y = x * y + y) /\
(!x. x * NUMERAL (BIT1 (ZERO)) = x) /\
(!x. NUMERAL (BIT1 (ZERO)) * x = x) /\ (!x. x * 0 = 0) /\
(!x. 0 * x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y z. divides x y \/ ~divides x z \/ ~divides x (z + y)) ==>
(y) <= (y) + (z) /\ divides c (d * SUC ((y) + (z))) /\
divides c (d * SUC (y)) /\ ~divides c (d * (z)) ==> F`},

{name = "gcd_21",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x + z = y + v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\ (!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ divides y v \/ ~divides x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y <= v \/ ~(x <= z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. x * (y + z) = x * y + x * z) /\ (!x y. x + SUC y = SUC (x + y)) /\
(!x y. SUC x + y = SUC (x + y)) /\ (!x. x + 0 = x) /\ (!x. 0 + x = x) /\
(!x y. x * SUC y = x + x * y) /\ (!x y. SUC x * y = x * y + y) /\
(!x. x * NUMERAL (BIT1 (ZERO)) = x) /\
(!x. NUMERAL (BIT1 (ZERO)) * x = x) /\ (!x. x * 0 = 0) /\
(!x. 0 * x = 0) /\ (!x y z. x + (y + z) = x + y + z) /\
(!x y z. divides x y \/ ~divides x z \/ ~divides x (z + y)) ==>
divides c (d * SUC (y)) /\ (y) <= (y) + (z) /\
divides c (d * SUC ((y) + (z))) /\ ~divides c (d * (z)) ==> F`},

{name = "int_arith_6",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_mul x z = int_mul y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. int_mul x y = int_mul y x) /\ (!x. ~int_lt x x) /\
(!x y z. ~(int_mul x y = int_mul z y) \/ y = int_of_num 0 \/ x = z) /\
(!x y z. int_mul x y = int_mul z y \/ ~(y = int_of_num 0)) /\
(!x y z. int_mul x y = int_mul z y \/ ~(x = z)) ==>
int_lt (int_of_num 0) gv1085 /\
int_mul gv1085 gv1086 = int_mul gv1085 gv1087 /\ ~(gv1086 = gv1087) ==> F`},

{name = "int_arith_139",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_add x z = int_add y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_le y v \/ ~int_le x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x. int_add (int_of_num 0) x = x) /\
(!x y z v.
   int_le (int_add x y) (int_add z v) \/ ~int_le x z \/ ~int_le y v) /\
(!x y z. int_add x (int_add y z) = int_add (int_add x y) z) /\
(!x y. int_add x y = int_add y x) /\
(!x y z. ~int_le (int_add x y) (int_add x z) \/ int_le y z) /\
(!x y z. int_le (int_add x y) (int_add x z) \/ ~int_le y z) ==>
int_le (x) (y) /\ int_le (int_of_num 0) (int_add c (x)) /\
~int_le (int_of_num 0) (int_add c (y)) ==> F`},

{name = "llist_69",
 comment = "",
 goal = `
(!x y. ~(x = y) \/ LTL x = LTL y) /\ (!x y. ~(x = y) \/ SOME x = SOME y) /\
(!x y. ~(x = y) \/ LHD x = LHD y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ LCONS x z = LCONS y v) /\
(!x y. ~(x = y) \/ g x = g y) /\ (!x y. ~(x = y) \/ THE x = THE y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ LNTH z x = LNTH v y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ LDROP z x = LDROP v y) /\
(!x y. ~(x = y) \/ SUC x = SUC y) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y z. ~(x = LCONS y z) \/ LTL x = SOME z) /\
(!x y z. ~(x = LCONS y z) \/ LHD x = SOME y) /\
(!x y z. x = LCONS y z \/ ~(LHD x = SOME y) \/ ~(LTL x = SOME z)) ==>
LTL (g (LCONS LNIL t)) =
SOME (g (LCONS (THE (LTL (THE (LNTH n t)))) (THE (LDROP (SUC n) t)))) /\
LHD (g (LCONS LNIL t)) = SOME (THE (LHD (THE (LNTH n t)))) /\
LHD (g t) = SOME (THE (LHD (THE (LNTH n t)))) /\
LTL (g t) =
SOME (g (LCONS (THE (LTL (THE (LNTH n t)))) (THE (LDROP (SUC n) t)))) /\
~(g (LCONS LNIL t) = g t) ==> F`},

{name = "MachineTransition_0",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth /\ Eq = equality /\
(!x y z.
   ~$ (Next % x % y % z) \/ $ (x % ((,) % (gv940 % x % y % z) % z))) /\
(!x y z. ~$ (Next % x % y % z) \/ $ (y % (gv940 % x % y % z))) /\
(!x y z v. $ (Next % x % y % z) \/ ~$ (y % v) \/ ~$ (x % ((,) % v % z))) /\
(!x y z. ~$ (Prev % x % y % z) \/ $ (y % (gv935 % x % y % z))) /\
(!x y z.
   ~$ (Prev % x % y % z) \/ $ (x % ((,) % z % (gv935 % x % y % z)))) /\
(!x y z v.
   $ (Prev % x % y % z) \/ ~$ (x % ((,) % z % v)) \/ ~$ (y % v)) ==>
$ (Next % gv914 % (Eq % gv915) % gv916) /\
~$ (Prev % gv914 % (Eq % gv916) % gv915) ==> F`},

{name = "MachineTransition_2_1",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth /\
(!x y z. ReachIn % x % (Next % x % y) % z = ReachIn % x % y % (SUC % z)) /\
(!x y z.
   ~$ (Next % x % y % z) \/ $ (x % ((,) % (gv5488 % x % y % z) % z))) /\
(!x y z. ~$ (Next % x % y % z) \/ $ (y % (gv5488 % x % y % z))) /\
(!x y z v. $ (Next % x % y % z) \/ ~$ (y % v) \/ ~$ (x % ((,) % v % z))) /\
(!x y z. ReachIn % x % y % (SUC % z) = Next % x % (ReachIn % x % y % z)) /\
(!x y. ReachIn % x % y % 0 = y) ==>
$ (ReachIn % R % (Next % R % B) % gv5278 % state) /\
(!x. ~$ (ReachIn % R % B % gv5278 % x) \/ ~$ (R % ((,) % x % state))) ==> F`},

{name = "MachineTransition_52",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth /\
(!x y z.
   $
   ((<=) % (gv7028 % x % y % z) %
    ((+) % x % (NUMERAL % (BIT1 % (ZERO))))) \/
   z % ((+) % x % (NUMERAL % (BIT1 % (ZERO)))) =
   y % ((+) % x % (NUMERAL % (BIT1 % (ZERO))))) /\
(!x y z.
   ~(x % (gv7028 % y % z % x) = z % (gv7028 % y % z % x)) \/
   x % ((+) % y % (NUMERAL % (BIT1 % (ZERO)))) =
   z % ((+) % y % (NUMERAL % (BIT1 % (ZERO))))) /\
(!x y z v.
   ~(x % (gv7028 % y % z % x) = z % (gv7028 % y % z % x)) \/
   x % v = z % v \/ ~$ ((<=) % v % y)) /\
(!x y z v.
   $
   ((<=) % (gv7028 % x % y % z) %
    ((+) % x % (NUMERAL % (BIT1 % (ZERO))))) \/ z % v = y % v \/
   ~$ ((<=) % v % x)) /\
(!x y z v.
   ~$ ((<=) % x % ((+) % y % (NUMERAL % (BIT1 % (ZERO))))) \/
   z % x = v % x \/
   ~(z % (gv7027 % y % v % z) = v % (gv7027 % y % v % z)) \/
   ~(z % ((+) % y % (NUMERAL % (BIT1 % (ZERO)))) =
     v % ((+) % y % (NUMERAL % (BIT1 % (ZERO)))))) /\
(!x y z v.
   ~$ ((<=) % x % ((+) % y % (NUMERAL % (BIT1 % (ZERO))))) \/
   z % x = v % x \/ $ ((<=) % (gv7027 % y % v % z) % y) \/
   ~(z % ((+) % y % (NUMERAL % (BIT1 % (ZERO)))) =
     v % ((+) % y % (NUMERAL % (BIT1 % (ZERO)))))) ==>
($ (FinPath % ((,) % R % s) % f2 % n) \/
 ~$ (FinPath % ((,) % R % s) % f1 % n) \/ ~(f1 % gv7034 = f2 % gv7034)) /\
(~$ (FinPath % ((,) % R % s) % f2 % n) \/
 $ (FinPath % ((,) % R % s) % f1 % n) \/ ~(f1 % gv7034 = f2 % gv7034)) /\
(~$ (FinPath % ((,) % R % s) % f2 % n) \/
 $ (FinPath % ((,) % R % s) % f1 % n) \/ $ ((<=) % gv7034 % n)) /\
($ (FinPath % ((,) % R % s) % f2 % n) \/
 ~$ (FinPath % ((,) % R % s) % f1 % n) \/ $ ((<=) % gv7034 % n)) /\
(!x.
   f1 % x = f2 % x \/
   ~$ ((<=) % x % ((+) % n % (NUMERAL % (BIT1 % (ZERO)))))) /\
$ (FinPath % ((,) % R % s) % f2 % n) /\
$
(R % ((,) % (f2 % n) % (f2 % ((+) % n % (NUMERAL % (BIT1 % (ZERO))))))) /\
~$ (FinPath % ((,) % R % s) % f1 % n) ==> F`},

{name = "measure_138",
 comment = "",
 goal = `
(!x y z. ~SUBSET x y \/ IN z y \/ ~IN z x) /\
(!x y. SUBSET x y \/ IN (gv122874 x y) x) /\
(!x y. SUBSET x y \/ ~IN (gv122874 x y) y) /\
(!x. sigma_algebra (sigma x)) /\ (!x y z. ~IN x (INTER y z) \/ IN x z) /\
(!x y z. ~IN x (INTER y z) \/ IN x y) /\
(!x y z. IN x (INTER y z) \/ ~IN x y \/ ~IN x z) /\
(!x y.
   ~sigma_algebra x \/ IN (BIGUNION y) x \/ ~countable y \/ ~SUBSET y x) /\
(!x y. ~sigma_algebra x \/ IN (COMPL y) x \/ ~IN y x) /\
(!x. ~sigma_algebra x \/ IN EMPTY x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ ~IN (COMPL (gv122851 x)) x \/
   SUBSET (gv122852 x) x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ IN (gv122851 x) x \/
   SUBSET (gv122852 x) x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ IN (gv122851 x) x \/
   countable (gv122852 x)) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ ~IN (COMPL (gv122851 x)) x \/
   countable (gv122852 x)) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ IN (gv122851 x) x \/
   ~IN (BIGUNION (gv122852 x)) x) /\
(!x.
   sigma_algebra x \/ ~IN EMPTY x \/ ~IN (COMPL (gv122851 x)) x \/
   ~IN (BIGUNION (gv122852 x)) x) ==>
SUBSET c (INTER p (sigma a)) /\
(!x. IN (BIGUNION x) p \/ ~countable x \/ ~SUBSET x (INTER p (sigma a))) /\
SUBSET a p /\ IN EMPTY p /\
(!x. IN (COMPL x) p \/ ~IN x (INTER p (sigma a))) /\ countable c /\
~IN (BIGUNION c) (sigma a) ==> F`},

{name = "mlibOmega_13",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_mul x z = int_mul y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ evalupper y v \/ ~evalupper x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_le y v \/ ~int_le x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. ~int_le x y \/ int_lt x y \/ x = y) /\
(!x y. int_le x y \/ ~int_lt x y) /\ (!x y. int_le x y \/ ~(x = y)) /\
(!x y z.
   int_lt x y \/
   ~int_lt (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) /\
(!x y z.
   ~int_lt x y \/
   int_lt (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) /\ (!x y z. int_lt x y \/ ~int_le x z \/ ~int_lt z y) ==>
(!x y. evalupper x uppers \/ ~evalupper y uppers \/ ~int_lt x y) /\
int_le (int_mul (int_of_num p_1) (x)) p_2 /\ evalupper (x) uppers /\
int_lt (y) (x) /\ 0 < p_1 /\ ~int_le (int_mul (int_of_num p_1) (y)) p_2 ==>
F`},

{name = "mlibOmega_71",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_mul x z = int_mul y v) /\
(!x y. ~(x = y) \/ int_of_num x = int_of_num y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_add x z = int_add y v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT1 x = BIT1 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ (x, z) = (y, v)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ evallower y v \/ ~evallower x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ rshadow_row v y \/ ~rshadow_row z x) /\
(!x y z v.
   ~(x = y) \/ ~(z = v) \/ dark_shadow_cond_row v y \/
   ~dark_shadow_cond_row z x) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_le y v \/ ~int_le x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ EVERY y v \/ ~EVERY x z) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ int_lt y v \/ ~int_lt x z) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y. int_mul x y = int_mul y x) /\
(!x y z. int_mul x (int_mul y z) = int_mul (int_mul x y) z) /\
(!x y z.
   int_le x y \/
   ~int_le (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) /\
(!x y z.
   ~int_le x y \/
   int_le (int_mul (int_of_num z) x) (int_mul (int_of_num z) y) \/
   ~(0 < z)) ==>
(!x y z.
   evallower (gv6249 x y z) lowers \/ ~(0 < y) \/ ~evallower x lowers \/
   ~rshadow_row (y, z) lowers \/ ~dark_shadow_cond_row (y, z) lowers) /\
(!x y z.
   int_le (int_mul (int_of_num x) (gv6249 y x z)) z \/ ~(0 < x) \/
   ~evallower y lowers \/ ~rshadow_row (x, z) lowers \/
   ~dark_shadow_cond_row (x, z) lowers) /\ 0 < c /\
int_le R (int_mul (int_of_num d) (x)) /\ evallower (x) lowers /\ 0 < d /\
EVERY fst_nzero lowers /\
int_le (int_mul (int_of_num c) R) (int_mul (int_of_num d) L) /\
rshadow_row (c, L) lowers /\ dark_shadow_cond_row (c, L) lowers /\
(!x.
   ~int_lt (int_mul (int_of_num d) L)
    (int_mul (int_of_num (c * d))
     (int_add x (int_of_num (NUMERAL (BIT1 (ZERO)))))) \/
   ~int_lt (int_mul (int_of_num (c * d)) x) (int_mul (int_of_num c) R)) /\
int_le (int_mul (int_of_num c) (y)) L /\ evallower (y) lowers /\
int_le (int_mul (int_of_num (c * d)) (y)) (int_mul (int_of_num d) L) /\
int_le (int_mul (int_of_num c) R) (int_mul (int_of_num (c * d)) (x)) /\
int_lt (int_mul (int_of_num (c * d)) (y)) (int_mul (int_of_num c) R) /\
0 < c * d /\
int_le (int_mul (int_of_num c) R) (int_mul (int_of_num (c * d)) j) /\
int_le (int_mul (int_of_num (c * d)) j) (int_mul (int_of_num d) L) /\
int_le (int_mul (int_mul (int_of_num c) (int_of_num d)) j)
(int_mul (int_of_num d) L) /\ ~int_le (int_mul (int_of_num c) j) L ==> F`},

{name = "pred_set_1",
 comment = "Small problem that's hard for ordered resolution",
 goal = `
(!x y z. ~(x <= y) \/ z :: y \/ ~(z :: x)) /\
(!x y. x <= y \/ ~(a x y :: y)) /\ (!x y. x <= y \/ a x y :: x) /\
(!x y z. ~(x :: y * z) \/ x :: z) /\ (!x y z. ~(x :: y * z) \/ x :: y) /\
(!x y z. x :: y * z \/ ~(x :: y) \/ ~(x :: z)) ==>
b <= c /\ b <= d /\ ~(b <= c * d) ==> F`},

{name = "pred_set_54_1",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth /\
(!x y z. ~$ (IN % x % (INSERT % y % z)) \/ x = y \/ $ (IN % x % z)) /\
(!x y z. $ (IN % x % (INSERT % y % z)) \/ ~(x = y)) /\
(!x y z. $ (IN % x % (INSERT % y % z)) \/ ~$ (IN % x % z)) ==>
(!x y z. f % x % (f % y % z) = f % y % (f % x % z)) /\
(!x y z.
   ITSET % f % (INSERT % x % y) % z =
   ITSET % f % (DELETE % y % x) % (f % x % z) \/
   ~$ ((<) % (CARD % y) % (v)) \/ ~$ (FINITE % y)) /\ (v) = CARD % s /\
$ (FINITE % s) /\ REST % (INSERT % (x) % s) = t /\
CHOICE % (INSERT % (x) % s) = (y) /\ ~$ (IN % (y) % t) /\
~$ (IN % (x) % s) /\ INSERT % (x) % s = INSERT % (y) % t /\ ~((x) = (y)) /\
~$ (IN % (x) % t) ==> F`},

{name = "prob_44",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth ==>
(!x y z.
   ~$ (IN % x % (prefix_set % (x'))) \/ ~$ (IN % x % (prefix_set % (x))) \/
   ~$ (IN % y % c) \/ ~$ (IN % (gv24939 % y) % (prefix_set % (x))) \/
   ~$ (IN % (gv24939 % y) % (prefix_set % y)) \/
   ~$ (IN % (gv24940 % z) % (prefix_set % z)) \/
   ~$ (IN % (gv24940 % z) % (prefix_set % (x'))) \/ ~$ (IN % z % c)) /\
(!x y z.
   ~$ (IN % x % (prefix_set % (x'))) \/ ~$ (IN % x % (prefix_set % (x))) \/
   ~$ (IN % y % c) \/ $ (IN % (gv24939 % y) % (prefix_set % (x))) \/
   $ (IN % (gv24939 % y) % (prefix_set % y)) \/
   ~$ (IN % (gv24940 % z) % (prefix_set % z)) \/
   ~$ (IN % (gv24940 % z) % (prefix_set % (x'))) \/ ~$ (IN % z % c)) /\
(!x y z.
   ~$ (IN % x % (prefix_set % (x'))) \/ ~$ (IN % x % (prefix_set % (x))) \/
   ~$ (IN % y % c) \/ $ (IN % (gv24939 % y) % (prefix_set % (x))) \/
   $ (IN % (gv24939 % y) % (prefix_set % y)) \/
   $ (IN % (gv24940 % z) % (prefix_set % z)) \/
   $ (IN % (gv24940 % z) % (prefix_set % (x'))) \/ ~$ (IN % z % c)) /\
(!x y z.
   ~$ (IN % x % (prefix_set % (x'))) \/ ~$ (IN % x % (prefix_set % (x))) \/
   ~$ (IN % y % c) \/ ~$ (IN % (gv24939 % y) % (prefix_set % (x))) \/
   ~$ (IN % (gv24939 % y) % (prefix_set % y)) \/
   $ (IN % (gv24940 % z) % (prefix_set % z)) \/
   $ (IN % (gv24940 % z) % (prefix_set % (x'))) \/ ~$ (IN % z % c)) /\
$ (IN % (x') % c) /\
$ (IN % (PREIMAGE % ((o) % SND % f) % s) % (events % bern)) /\
(!x y.
   f % x =
   (,) % (FST % (f % (prefix_seq % y))) % (sdrop % (LENGTH % y) % x) \/
   ~$ (IN % y % c) \/ ~$ (IN % x % (prefix_set % y))) /\
$
(IN % ((o) % SND % f) %
 (measurable % (events % bern) % (events % bern))) /\
$ (countable % (range % ((o) % FST % f))) /\
$ (IN % ((o) % FST % f) % (measurable % (events % bern) % UNIV)) /\
$ (prefix_cover % c) /\ $ (IN % s % (events % bern)) /\ $ (IN % (x) % c) /\
($ (IN % (x'') % (prefix_set % (x))) \/
 $ (IN % (x'') % (prefix_set % (x')))) /\
(~$ (IN % (x'') % (prefix_set % (x))) \/
 ~$ (IN % (x'') % (prefix_set % (x')))) /\
$ (IN % (x''') % (prefix_set % (x))) /\
$ (IN % (x''') % (prefix_set % (x'))) ==> F`},

{name = "prob_53",
 comment = "",
 goal = `
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   x = y \/ ~$ (x % (EXT_POINT % x % y)) \/
   ~$ (y % (EXT_POINT % x % y))) /\
(!x y.
   x = y \/ $ (x % (EXT_POINT % x % y)) \/ $ (y % (EXT_POINT % x % y))) /\
(!x y. x = y \/ ~(x % (EXT_POINT % x % y) = y % (EXT_POINT % x % y))) /\
(!x y. ~$ x \/ ~(x = y) \/ $ y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ x % z = y % v) /\
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth ==>
(!x y z.
   ~$ (IN % x % (prefix_set % (x'''))) \/
   ~$ (IN % x % (prefix_set % (x''))) \/ ~$ (IN % y % c) \/
   ~$ (IN % (gv39280 % y) % (prefix_set % (x''))) \/
   ~$ (IN % (gv39280 % y) % (prefix_set % y)) \/
   ~$ (IN % (gv39280 % z) % (prefix_set % z)) \/
   ~$ (IN % (gv39280 % z) % (prefix_set % (x'''))) \/ ~$ (IN % z % c)) /\
(!x y z.
   ~$ (IN % x % (prefix_set % (x'''))) \/
   ~$ (IN % x % (prefix_set % (x''))) \/ ~$ (IN % y % c) \/
   $ (IN % (gv39280 % y) % (prefix_set % (x''))) \/
   $ (IN % (gv39280 % y) % (prefix_set % y)) \/
   ~$ (IN % (gv39280 % z) % (prefix_set % z)) \/
   ~$ (IN % (gv39280 % z) % (prefix_set % (x'''))) \/ ~$ (IN % z % c)) /\
(!x y z.
   ~$ (IN % x % (prefix_set % (x'''))) \/
   ~$ (IN % x % (prefix_set % (x''))) \/ ~$ (IN % y % c) \/
   $ (IN % (gv39280 % y) % (prefix_set % (x''))) \/
   $ (IN % (gv39280 % y) % (prefix_set % y)) \/
   $ (IN % (gv39280 % z) % (prefix_set % z)) \/
   $ (IN % (gv39280 % z) % (prefix_set % (x'''))) \/ ~$ (IN % z % c)) /\
(!x y z.
   ~$ (IN % x % (prefix_set % (x'''))) \/
   ~$ (IN % x % (prefix_set % (x''))) \/ ~$ (IN % y % c) \/
   ~$ (IN % (gv39280 % y) % (prefix_set % (x''))) \/
   ~$ (IN % (gv39280 % y) % (prefix_set % y)) \/
   $ (IN % (gv39280 % z) % (prefix_set % z)) \/
   $ (IN % (gv39280 % z) % (prefix_set % (x'''))) \/ ~$ (IN % z % c)) /\
$ (IN % (x''') % c) /\
$ (IN % (PREIMAGE % ((o) % SND % f) % (x')) % (events % bern)) /\
$ (IN % (x') % (events % bern)) /\ $ (prefix_cover % c) /\
$ (IN % ((o) % FST % f) % (measurable % (events % bern) % UNIV)) /\
$ (countable % (range % ((o) % FST % f))) /\
$
(IN % ((o) % SND % f) %
 (measurable % (events % bern) % (events % bern))) /\
(!x y.
   f % x =
   (,) % (FST % (f % (prefix_seq % y))) % (sdrop % (LENGTH % y) % x) \/
   ~$ (IN % y % c) \/ ~$ (IN % x % (prefix_set % y))) /\
$ (IN % (PREIMAGE % ((o) % FST % f) % (x)) % (events % bern)) /\
$ (IN % (x'') % c) /\
($ (IN % (x'''') % (prefix_set % (x''))) \/
 $ (IN % (x'''') % (prefix_set % (x''')))) /\
(~$ (IN % (x'''') % (prefix_set % (x''))) \/
 ~$ (IN % (x'''') % (prefix_set % (x''')))) /\
$ (IN % (x''''') % (prefix_set % (x''))) /\
$ (IN % (x''''') % (prefix_set % (x'''))) ==> F`},

{name = "prob_extra_22",
 comment = "",
 goal = `
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth ==>
$ (P % (x)) /\ (!x. $ (real_lte % x % (z)) \/ ~$ (P % x)) /\
(!x y z v.
   $ (real_lt % x % (sup % P)) \/ ~$ (P % y) \/ ~$ (real_lt % x % y) \/
   ~$ (P % z) \/ ~$ (real_lte % (gv13960 % v) % v)) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (P % (gv13960 % x)) \/ ~$ (P % y) \/
   ~$ (real_lte % (gv13960 % z) % z)) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (real_lt % x % (gv13960 % x)) \/
   ~$ (P % y) \/ ~$ (real_lte % (gv13960 % z) % z)) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (real_lt % x % (gv13960 % x)) \/
   ~$ (P % y) \/ $ (P % (gv13960 % z))) /\
(!x y z.
   ~$ (real_lt % x % (sup % P)) \/ $ (P % (gv13960 % x)) \/ ~$ (P % y) \/
   $ (P % (gv13960 % z))) /\
(!x y z v.
   $ (real_lt % x % (sup % P)) \/ ~$ (P % y) \/ ~$ (real_lt % x % y) \/
   ~$ (P % z) \/ $ (P % (gv13960 % v))) /\
(!x.
   $ (real_lt % (gv13925 % x) % (gv13926 % x)) \/
   $ (real_lt % (gv13925 % x) % x)) /\
(!x. $ (P % (gv13926 % x)) \/ $ (real_lt % (gv13925 % x) % x)) /\
(!x y.
   ~$ (real_lt % (gv13925 % x) % y) \/ ~$ (P % y) \/
   ~$ (real_lt % (gv13925 % x) % x)) ==> F`},

{name = "root2_2",
 comment = "",
 goal = `
(!x y z v. ~(x = y) \/ ~(z = v) \/ x * z = y * v) /\
(!x y. ~(x = y) \/ NUMERAL x = NUMERAL y) /\
(!x y. ~(x = y) \/ BIT2 x = BIT2 y) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ EXP x z = EXP y v) /\
(!x y z v. ~(x = y) \/ ~(z = v) \/ y < v \/ ~(x < z)) /\
(!x y. ~(x = y) \/ EVEN y \/ ~EVEN x) /\
(!x y z. ~(x = y) \/ ~(x = z) \/ y = z) /\ (!x. x = x) /\
(!x y.
   ~(EXP (NUMERAL (BIT2 (ZERO)) * x) (NUMERAL (BIT2 (ZERO))) =
     NUMERAL (BIT2 (ZERO)) * EXP y (NUMERAL (BIT2 (ZERO)))) \/
   NUMERAL (BIT2 (ZERO)) * EXP x (NUMERAL (BIT2 (ZERO))) =
   EXP y (NUMERAL (BIT2 (ZERO)))) /\
(!x y.
   EXP (NUMERAL (BIT2 (ZERO)) * x) (NUMERAL (BIT2 (ZERO))) =
   NUMERAL (BIT2 (ZERO)) * EXP y (NUMERAL (BIT2 (ZERO))) \/
   ~(NUMERAL (BIT2 (ZERO)) * EXP x (NUMERAL (BIT2 (ZERO))) =
     EXP y (NUMERAL (BIT2 (ZERO))))) /\
(!x. ~EVEN x \/ x = NUMERAL (BIT2 (ZERO)) * gv4671 x) /\
(!x y. EVEN x \/ ~(x = NUMERAL (BIT2 (ZERO)) * y)) /\
(!x y. ~EVEN (x * y) \/ EVEN x \/ EVEN y) /\
(!x y. EVEN (x * y) \/ ~EVEN x) /\ (!x y. EVEN (x * y) \/ ~EVEN y) /\
(!x. EXP x (NUMERAL (BIT2 (ZERO))) = x * x) /\
(!x. EVEN (NUMERAL (BIT2 (ZERO)) * x)) ==>
EXP (NUMERAL (BIT2 (ZERO)) * k) (NUMERAL (BIT2 (ZERO))) =
NUMERAL (BIT2 (ZERO)) * EXP n (NUMERAL (BIT2 (ZERO))) /\
(!x y.
   ~(EXP x (NUMERAL (BIT2 (ZERO))) =
     NUMERAL (BIT2 (ZERO)) * EXP y (NUMERAL (BIT2 (ZERO)))) \/ x = 0 \/
   ~(x < NUMERAL (BIT2 (ZERO)) * k)) /\
(!x y.
   ~(EXP x (NUMERAL (BIT2 (ZERO))) =
     NUMERAL (BIT2 (ZERO)) * EXP y (NUMERAL (BIT2 (ZERO)))) \/ y = 0 \/
   ~(x < NUMERAL (BIT2 (ZERO)) * k)) /\
(!x. ~(n = NUMERAL (BIT2 (ZERO)) * x)) ==> F`},

{name = "mlibTermRewriting_13",
 comment = "",
 goal = `
~$ (existential % (K % falsity)) /\ $ (existential % (K % truth)) /\
~$ (universal % (K % falsity)) /\ $ (universal % (K % truth)) /\
~$ falsity /\ $ truth /\
(!x y z v.
   ~$ (RTC % x % y % z) \/ $ (RTC % x % v % z) \/ ~$ (RTC % x % v % y)) ==>
$ ((WCR) % R) /\ $ (SN % R) /\
(!x y z.
   ~$ (RTC % R % x % y) \/ ~$ (RTC % R % x % z) \/
   $ (RTC % R % y % (gv1300 % x % z % y)) \/ ~$ (TC % R % (x) % x)) /\
(!x y z.
   ~$ (RTC % R % x % y) \/ ~$ (RTC % R % x % z) \/
   $ (RTC % R % z % (gv1300 % x % z % y)) \/ ~$ (TC % R % (x) % x)) /\
$ (RTC % R % (x) % (y)) /\ $ (RTC % R % (x) % (z)) /\ $ (R % (x) % (y1)) /\
$ (RTC % R % (y1) % (y)) /\ $ (R % (x) % (z1)) /\
$ (RTC % R % (z1) % (z)) /\ $ (RTC % R % (y1) % (x0)) /\
$ (RTC % R % (z1) % (x0)) /\ $ (TC % R % (x) % (y1)) /\
$ (TC % R % (x) % (z1)) /\ $ (RTC % R % (y) % (y2)) /\
$ (RTC % R % (x0) % (y2)) /\ $ (RTC % R % (z) % (z2)) /\
$ (RTC % R % (x0) % (z2)) /\ $ (TC % R % (x) % (x0)) /\
(!x. ~$ (RTC % R % (y) % x) \/ ~$ (RTC % R % (z) % x)) ==> F`}

];

(* ========================================================================= *)
(* TPTP problems classified as "unsatisfiable" in TPTP-v2.5.0/tptp/PUZ/      *)
(* Created by Joe Hurd using tptp-parse.pl, November 2002.                   *)
(* ========================================================================= *)

fun puzzle () =

mk_set "puzzle" "unsatisfiable PUZxxx-x problems in TPTP-v2.5.0" [

{name    = "PUZ001-1",
 comment = "",
 goal    = `
lives agatha /\ lives butler /\ lives charles /\
(!x y. ~killed x y \/ ~richer x y) /\
(!x. ~hates agatha x \/ ~hates charles x) /\
(!x. ~hates x agatha \/ ~hates x butler \/ ~hates x charles) /\
hates agatha agatha /\ hates agatha charles /\
(!x y. ~killed x y \/ hates x y) /\
(!x. ~hates agatha x \/ hates butler x) /\
(!x. ~lives x \/ richer x agatha \/ hates butler x) ==>
killed butler agatha \/ killed charles agatha ==> F`},

{name    = "PUZ001-2",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x = y) \/ every_one_but x = every_one_but y) /\
(!x y z. ~(x = y) \/ ~hates x z \/ hates y z) /\
(!x y z. ~(x = y) \/ ~hates z x \/ hates z y) /\
(!x y z. ~(x = y) \/ ~killed x z \/ killed y z) /\
(!x y z. ~(x = y) \/ ~killed z x \/ killed z y) /\
(!x y. ~(x = y) \/ ~lives_at_dreadsbury x \/ lives_at_dreadsbury y) /\
(!x y z. ~(x = y) \/ ~richer x z \/ richer y z) /\
(!x y z. ~(x = y) \/ ~richer z x \/ richer z y) /\
lives_at_dreadsbury someone /\ killed someone aunt_agatha /\
lives_at_dreadsbury aunt_agatha /\ lives_at_dreadsbury butler /\
lives_at_dreadsbury charles /\
(!x.
   ~lives_at_dreadsbury x \/ x = aunt_agatha \/ x = butler \/
   x = charles) /\ (!x y. ~killed x y \/ hates x y) /\
(!x y. ~killed x y \/ ~richer x y) /\
(!x. ~hates aunt_agatha x \/ ~hates charles x) /\
(!x. x = butler \/ hates aunt_agatha x) /\
(!x. richer x aunt_agatha \/ hates butler x) /\
(!x. ~hates aunt_agatha x \/ hates butler x) /\
(!x. ~hates x (every_one_but x)) /\ ~(aunt_agatha = butler) ==>
~killed aunt_agatha aunt_agatha ==> F`},

{name    = "PUZ002-1",
 comment = "",
 goal    = `
(!x. ~in_house x \/ cat x) /\ (!x. ~gazer x \/ suitable_pet x) /\
(!x. ~detested x \/ avoided x) /\ (!x. ~carnivore x \/ prowler x) /\
(!x. ~cat x \/ mouse_killer x) /\ (!x. ~takes_to_me x \/ in_house x) /\
(!x. ~kangaroo x \/ ~suitable_pet x) /\
(!x. ~mouse_killer x \/ carnivore x) /\
(!x. takes_to_me x \/ detested x) /\ (!x. ~prowler x \/ gazer x) /\
kangaroo the_kangaroo ==> ~avoided the_kangaroo ==> F`},

{name    = "PUZ003-1",
 comment = "",
 goal    = `
(!x y. ~member x \/ ~member y \/ ~shaved x y \/ shaved members x) /\
(!x y. ~shaved members x \/ ~member y \/ shaved y x) /\ member guido /\
member lorenzo /\ member petruchio /\ member cesare /\
shaved guido cesare ==> ~shaved petruchio lorenzo ==> F`},

{name    = "PUZ004-1",
 comment = "",
 goal    = `
(~dated \/ on_blue_paper) /\ (~in_third_person \/ in_black_ink) /\
(in_third_person \/ ~in_black_ink) /\ (~can_be_read \/ ~filed) /\
(~on_one_sheet \/ dated) /\ (crossed \/ in_black_ink) /\
(~by_brown \/ begins_with_dear_sir) /\ (~on_blue_paper \/ filed) /\
(on_one_sheet \/ ~crossed) /\
(~begins_with_dear_sir \/ ~in_third_person) /\ by_brown ==> can_be_read ==>
F`},

{name    = "PUZ005-1",
 comment = "",
 goal    = `
(!x.
   monday x \/ tuesday x \/ (wednesday) x \/ thursday x \/ friday x \/
   saturday x \/ sunday x) /\ (!x. ~monday x \/ ~tuesday x) /\
(!x. ~monday x \/ ~(wednesday) x) /\ (!x. ~monday x \/ ~thursday x) /\
(!x. ~monday x \/ ~friday x) /\ (!x. ~monday x \/ ~saturday x) /\
(!x. ~monday x \/ ~sunday x) /\ (!x. ~tuesday x \/ ~(wednesday) x) /\
(!x. ~tuesday x \/ ~thursday x) /\ (!x. ~tuesday x \/ ~friday x) /\
(!x. ~tuesday x \/ ~saturday x) /\ (!x. ~tuesday x \/ ~sunday x) /\
(!x. ~(wednesday) x \/ ~thursday x) /\ (!x. ~(wednesday) x \/ ~friday x) /\
(!x. ~(wednesday) x \/ ~saturday x) /\ (!x. ~(wednesday) x \/ ~sunday x) /\
(!x. ~thursday x \/ ~friday x) /\ (!x. ~thursday x \/ ~saturday x) /\
(!x. ~thursday x \/ ~sunday x) /\ (!x. ~friday x \/ ~saturday x) /\
(!x. ~friday x \/ ~sunday x) /\ (!x. ~saturday x \/ ~sunday x) /\
(!x. ~monday ((yesterday) x) \/ tuesday x) /\
(!x. ~tuesday ((yesterday) x) \/ (wednesday) x) /\
(!x. ~(wednesday) ((yesterday) x) \/ thursday x) /\
(!x. ~thursday ((yesterday) x) \/ friday x) /\
(!x. ~friday ((yesterday) x) \/ saturday x) /\
(!x. ~saturday ((yesterday) x) \/ sunday x) /\
(!x. ~sunday ((yesterday) x) \/ monday x) /\
(!x. monday ((yesterday) x) \/ ~tuesday x) /\
(!x. tuesday ((yesterday) x) \/ ~(wednesday) x) /\
(!x. (wednesday) ((yesterday) x) \/ ~thursday x) /\
(!x. thursday ((yesterday) x) \/ ~friday x) /\
(!x. friday ((yesterday) x) \/ ~saturday x) /\
(!x. saturday ((yesterday) x) \/ ~sunday x) /\
(!x. sunday ((yesterday) x) \/ ~monday x) /\
(!x.
   ~member x (lying_days lion) \/ monday x \/ tuesday x \/
   (wednesday) x) /\
(!x.
   ~member x (lying_days unicorn) \/ thursday x \/ friday x \/
   saturday x) /\ (!x. ~monday x \/ member x (lying_days lion)) /\
(!x. ~tuesday x \/ member x (lying_days lion)) /\
(!x. ~(wednesday) x \/ member x (lying_days lion)) /\
(!x. ~thursday x \/ member x (lying_days unicorn)) /\
(!x. ~friday x \/ member x (lying_days unicorn)) /\
(!x. ~saturday x \/ member x (lying_days unicorn)) /\
(!x y z.
   member x (lying_days y) \/ ~admits y x z \/ member z (lying_days y)) /\
(!x y z.
   member x (lying_days y) \/ admits y x z \/ ~member z (lying_days y)) /\
(!x y z.
   ~member x (lying_days y) \/ ~admits y x z \/
   ~member z (lying_days y)) /\
(!x y z.
   ~member x (lying_days y) \/ admits y x z \/ member z (lying_days y)) /\
admits lion today ((yesterday) today) /\
admits unicorn today ((yesterday) today) ==> ~thursday today ==> F`},

{name    = "PUZ006-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x. from_mars x \/ from_venus x) /\ (!x. ~from_mars x \/ ~from_venus x) /\
(!x. male x \/ female x) /\ (!x. ~male x \/ ~female x) /\
(!x. truthteller x \/ liar x) /\ (!x. ~truthteller x \/ ~liar x) /\
(!x y. ~says x y \/ a_truth y \/ ~a_truth y) /\
(!x y. ~says x y \/ y = statement_by x) /\
(!x. ~a_truth (statement_by x) \/ truthteller x) /\
(!x. a_truth (statement_by x) \/ liar x) /\
(!x. ~from_venus x \/ ~female x \/ truthteller x) /\
(!x. ~from_venus x \/ ~male x \/ liar x) /\
(!x. ~from_mars x \/ ~male x \/ truthteller x) /\
(!x. ~from_mars x \/ ~female x \/ liar x) /\
(!x y. ~truthteller x \/ ~says x y \/ a_truth y) /\
(!x y. ~liar x \/ ~says x y \/ ~a_truth y) /\
(!x y. ~(x = y) \/ ~a_truth x \/ a_truth y) /\
(!x y. ~(x = y) \/ ~female x \/ female y) /\
(!x y. ~(x = y) \/ ~from_mars x \/ from_mars y) /\
(!x y. ~(x = y) \/ ~from_venus x \/ from_venus y) /\
(!x y. ~(x = y) \/ ~liar x \/ liar y) /\
(!x y. ~(x = y) \/ ~male x \/ male y) /\
(!x y z. ~(x = y) \/ ~says x z \/ says y z) /\
(!x y z. ~(x = y) \/ ~says z x \/ says z y) /\
(!x y. ~(x = y) \/ statement_by x = statement_by y) /\
(!x y. ~(x = y) \/ ~truthteller x \/ truthteller y) /\
says ork bog_is_from_venus /\ says bog ork_is_from_mars /\
says ork bog_is_male /\ says bog ork_is_female /\
(~a_truth bog_is_from_venus \/ from_venus bog) /\
(~a_truth ork_is_from_mars \/ from_mars ork) /\
(~a_truth bog_is_male \/ male bog) /\
(~a_truth ork_is_female \/ female ork) /\
(~from_venus bog \/ a_truth bog_is_from_venus) /\
(~from_mars ork \/ a_truth ork_is_from_mars) /\
(~male bog \/ a_truth bog_is_male) /\
(~female ork \/ a_truth ork_is_female) ==> ~female bog ==> F`},

{name    = "PUZ007-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x. from_mars x \/ from_venus x) /\ (!x. ~from_mars x \/ ~from_venus x) /\
(!x. male x \/ female x) /\ (!x. ~male x \/ ~female x) /\
(!x. truthteller x \/ liar x) /\ (!x. ~truthteller x \/ ~liar x) /\
(!x y. ~says x y \/ a_truth y \/ ~a_truth y) /\
(!x y. ~says x y \/ y = statement_by x) /\
(!x. ~a_truth (statement_by x) \/ truthteller x) /\
(!x. a_truth (statement_by x) \/ liar x) /\
(!x. ~from_venus x \/ ~female x \/ truthteller x) /\
(!x. ~from_venus x \/ ~male x \/ liar x) /\
(!x. ~from_mars x \/ ~male x \/ truthteller x) /\
(!x. ~from_mars x \/ ~female x \/ liar x) /\
(!x y. ~truthteller x \/ ~says x y \/ a_truth y) /\
(!x y. ~liar x \/ ~says x y \/ ~a_truth y) /\
(!x y. ~(x = y) \/ ~a_truth x \/ a_truth y) /\
(!x y. ~(x = y) \/ ~female x \/ female y) /\
(!x y. ~(x = y) \/ ~from_mars x \/ from_mars y) /\
(!x y. ~(x = y) \/ ~from_venus x \/ from_venus y) /\
(!x y. ~(x = y) \/ ~liar x \/ liar y) /\
(!x y. ~(x = y) \/ ~male x \/ male y) /\
(!x y z. ~(x = y) \/ ~says x z \/ says y z) /\
(!x y z. ~(x = y) \/ ~says z x \/ says z y) /\
(!x y. ~(x = y) \/ statement_by x = statement_by y) /\
(!x y. ~(x = y) \/ ~truthteller x \/ truthteller y) /\
says a a_from_mars /\ says b a_has_lied /\
(~from_mars a \/ a_truth a_from_mars) /\
(from_mars a \/ ~a_truth a_from_mars) /\
(~a_truth a_from_mars \/ ~a_truth (statement_by b)) /\
statement_by a = a_from_mars /\ statement_by b = a_has_lied /\
(a_truth a_from_mars \/ a_truth (statement_by b)) /\
(~female a \/ male b) /\ (~male a \/ female b) ==>
(from_mars b \/ from_mars a) /\ (from_venus a \/ from_venus b) ==> F`},

{name    = "PUZ008-1",
 comment = "",
 goal    = `
(!x y z v.
   ~achievable ((west) (m x) (c (s y))) boatonwest (east (m z) (c v)) \/
   achievable ((west) (m x) (c y)) boatoneast (east (m z) (c (s v)))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast (east (m z) (c (s v))) \/
   achievable ((west) (m x) (c (s y))) boatonwest (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m x) (c (s (s y)))) boatonwest
    (east (m z) (c v)) \/
   achievable ((west) (m x) (c y)) boatoneast
   (east (m z) (c (s (s v))))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast
    (east (m z) (c (s (s v)))) \/
   achievable ((west) (m x) (c (s (s y)))) boatonwest
   (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m (s x)) (c y)) boatonwest (east (m z) (c v)) \/
   achievable ((west) (m x) (c y)) boatoneast (east (m (s z)) (c v))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast (east (m (s z)) (c v)) \/
   achievable ((west) (m (s x)) (c y)) boatonwest (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m (s (s x))) (c y)) boatonwest
    (east (m z) (c v)) \/
   achievable ((west) (m x) (c y)) boatoneast
   (east (m (s (s z))) (c v))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast
    (east (m (s (s z))) (c v)) \/
   achievable ((west) (m (s (s x))) (c y)) boatonwest
   (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m (s x)) (c (s y))) boatonwest
    (east (m z) (c v)) \/
   achievable ((west) (m x) (c y)) boatoneast
   (east (m (s z)) (c (s v)))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast
    (east (m (s z)) (c (s v))) \/
   achievable ((west) (m (s x)) (c (s y))) boatonwest
   (east (m z) (c v))) /\
(!x y z v. achievable ((west) (m (s x)) (c (s (s x)))) y (east z v)) /\
(!x y z v. achievable ((west) (m (s x)) (c (s (s (s x))))) y (east z v)) /\
(!x y z v. achievable ((west) x y) z (east (m (s v)) (c (s (s v))))) /\
(!x y z v. achievable ((west) x y) z (east (m (s v)) (c (s (s (s v)))))) /\
achievable ((west) (m (s (s (s 0)))) (c (s (s (s 0))))) boatonwest
(east (m 0) (c 0)) ==>
(!x.
   ~achievable ((west) (m 0) (c 0)) x
    (east (m (s (s (s 0)))) (c (s (s (s 0)))))) ==> F`},

{name    = "PUZ008-2",
 comment = "",
 goal    = `
(~banks ((west) (m 0) (c 3)) (east (m 3) (c 0)) boatonwest \/
 banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatoneast) /\
(~banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatonwest \/
 banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatoneast) /\
(~banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatonwest \/
 banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatoneast) /\
(~banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatonwest \/
 banks ((west) (m 3) (c 0)) (east (m 0) (c 3)) boatoneast) /\
(~banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatonwest \/
 banks ((west) (m 0) (c 0)) (east (m 3) (c 3)) boatoneast) /\
(~banks ((west) (m 3) (c 3)) (east (m 0) (c 0)) boatonwest \/
 banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatoneast) /\
(~banks ((west) (m 0) (c 3)) (east (m 3) (c 0)) boatonwest \/
 banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatoneast) /\
(~banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatonwest \/
 banks ((west) (m 3) (c 0)) (east (m 0) (c 3)) boatoneast) /\
(~banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatonwest \/
 banks ((west) (m 0) (c 0)) (east (m 3) (c 3)) boatoneast) /\
(~banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatoneast \/
 banks ((west) (m 0) (c 3)) (east (m 3) (c 0)) boatonwest) /\
(~banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatoneast \/
 banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatonwest) /\
(~banks ((west) (m 3) (c 0)) (east (m 0) (c 3)) boatoneast \/
 banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatonwest) /\
(~banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatoneast \/
 banks ((west) (m 3) (c 3)) (east (m 0) (c 0)) boatonwest) /\
(~banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatoneast \/
 banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatonwest) /\
(~banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatoneast \/
 banks ((west) (m 0) (c 3)) (east (m 3) (c 0)) boatonwest) /\
(~banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatoneast \/
 banks ((west) (m 3) (c 3)) (east (m 0) (c 0)) boatonwest) /\
(~banks ((west) (m 3) (c 0)) (east (m 0) (c 3)) boatoneast \/
 banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatonwest) /\
(~banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatonwest \/
 banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatoneast) /\
(~banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatonwest \/
 banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatoneast) /\
(~banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatonwest \/
 banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatoneast) /\
(~banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatonwest \/
 banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatoneast) /\
(~banks ((west) (m 0) (c 1)) (east (m 3) (c 2)) boatoneast \/
 banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatonwest) /\
(~banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatoneast \/
 banks ((west) (m 3) (c 2)) (east (m 0) (c 1)) boatonwest) /\
(~banks ((west) (m 0) (c 2)) (east (m 3) (c 1)) boatoneast \/
 banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatonwest) /\
(~banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatoneast \/
 banks ((west) (m 3) (c 1)) (east (m 0) (c 2)) boatonwest) /\
(~banks ((west) (m 3) (c 3)) (east (m 0) (c 0)) boatonwest \/
 banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatoneast) /\
(~banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatonwest \/
 banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatoneast) /\
(~banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatonwest \/
 banks ((west) (m 0) (c 0)) (east (m 3) (c 3)) boatoneast) /\
(~banks ((west) (m 1) (c 1)) (east (m 2) (c 2)) boatoneast \/
 banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatonwest) /\
(~banks ((west) (m 2) (c 2)) (east (m 1) (c 1)) boatoneast \/
 banks ((west) (m 3) (c 3)) (east (m 0) (c 0)) boatonwest) /\
banks ((west) (m 3) (c 3)) (east (m 0) (c 0)) boatonwest ==>
~banks ((west) (m 0) (c 0)) (east (m 3) (c 3)) boatoneast ==> F`},

{name    = "PUZ008-3",
 comment = "",
 goal    = `
(!x. safe 0 x) /\ (!x y. ~greater_or_equal x y \/ safe x y) /\
(!x. greater_or_equal x 0) /\
(!x y. greater_or_equal (s x) (s y) \/ ~greater_or_equal x y) /\
(!x y z v.
   ~achievable ((west) (m x) (c (s y))) boatonwest (east (m z) (c v)) \/
   ~safe x y \/ ~safe z (s v) \/
   achievable ((west) (m x) (c y)) boatoneast (east (m z) (c (s v)))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast (east (m z) (c (s v))) \/
   ~safe x (s y) \/ ~safe z v \/
   achievable ((west) (m x) (c (s y))) boatonwest (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m x) (c (s (s y)))) boatonwest
    (east (m z) (c v)) \/ ~safe x y \/ ~safe z (s (s v)) \/
   achievable ((west) (m x) (c y)) boatoneast
   (east (m z) (c (s (s v))))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast
    (east (m z) (c (s (s v)))) \/ ~safe x (s (s y)) \/ ~safe z v \/
   achievable ((west) (m x) (c (s (s y)))) boatonwest
   (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m (s x)) (c y)) boatonwest (east (m z) (c v)) \/
   ~safe x y \/ ~safe (s z) v \/
   achievable ((west) (m x) (c y)) boatoneast (east (m (s z)) (c v))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast (east (m (s z)) (c v)) \/
   ~safe (s x) y \/ ~safe z v \/
   achievable ((west) (m (s x)) (c y)) boatonwest (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m (s (s x))) (c y)) boatonwest
    (east (m z) (c v)) \/ ~safe x y \/ ~safe (s (s z)) v \/
   achievable ((west) (m x) (c y)) boatoneast
   (east (m (s (s z))) (c v))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast
    (east (m (s (s z))) (c v)) \/ ~safe (s (s x)) y \/ ~safe z v \/
   achievable ((west) (m (s (s x))) (c y)) boatonwest
   (east (m z) (c v))) /\
(!x y z v.
   ~achievable ((west) (m (s x)) (c (s y))) boatonwest
    (east (m z) (c v)) \/ ~safe x y \/ ~safe (s z) (s v) \/
   achievable ((west) (m x) (c y)) boatoneast
   (east (m (s z)) (c (s v)))) /\
(!x y z v.
   ~achievable ((west) (m x) (c y)) boatoneast
    (east (m (s z)) (c (s v))) \/ ~safe (s x) (s y) \/ ~safe z v \/
   achievable ((west) (m (s x)) (c (s y))) boatonwest
   (east (m z) (c v))) /\
achievable ((west) (m (s (s (s 0)))) (c (s (s (s 0))))) boatonwest
(east (m 0) (c 0)) ==>
(!x.
   ~achievable ((west) (m 0) (c 0)) x
    (east (m (s (s (s 0)))) (c (s (s (s 0)))))) ==> F`},

{name    = "PUZ009-1",
 comment = "",
 goal    = `
(~a_is_a_knight \/ ~b_is_a_knight) /\ (~a_is_a_knight \/ ~d_is_a_knight) /\
(~b_is_a_knight \/ ~a_is_a_knight) /\ (b_is_a_knight \/ a_is_a_knight) /\
(~b_is_a_knight \/ c_is_a_knight \/ d_is_a_knight) /\
(~c_is_a_knight \/ ~d_is_a_knight) /\ (~d_is_a_knight \/ ~a_is_a_knight) /\
(~d_is_a_knight \/ b_is_a_knight) /\ (~d_is_a_knight \/ ~c_is_a_knight) /\
(~e_is_a_knight \/ ~d_is_a_knight \/ c_is_a_knight) /\
(e_is_a_knight \/ d_is_a_knight) /\ (e_is_a_knight \/ ~c_is_a_knight) /\
(d_is_a_knight \/ a_is_a_knight \/ c_is_a_knight) /\
(d_is_a_knight \/ ~b_is_a_knight \/ c_is_a_knight) /\
(~a_is_a_knight \/ ~e_is_a_knight \/ c_is_a_knight) /\
(a_is_a_knight \/ e_is_a_knight) /\ (a_is_a_knight \/ ~c_is_a_knight) ==>
b_is_a_knight ==> F`},

{name    = "PUZ010-1",
 comment = "",
 goal    = `
(!x.
   ~person x \/ lives x house_1 \/ lives x house_2 \/ lives x house_3 \/
   lives x house_4 \/ lives x house_5) /\
(!x. ~house x \/ ~lives english x \/ ~lives spaniard x) /\
(!x. ~house x \/ ~lives english x \/ ~lives norwegian x) /\
(!x. ~house x \/ ~lives english x \/ ~lives ukranian x) /\
(!x. ~house x \/ ~lives english x \/ ~lives japanese x) /\
(!x. ~house x \/ ~lives spaniard x \/ ~lives norwegian x) /\
(!x. ~house x \/ ~lives spaniard x \/ ~lives ukranian x) /\
(!x. ~house x \/ ~lives spaniard x \/ ~lives japanese x) /\
(!x. ~house x \/ ~lives norwegian x \/ ~lives ukranian x) /\
(!x. ~house x \/ ~lives norwegian x \/ ~lives japanese x) /\
(!x. ~house x \/ ~lives ukranian x \/ ~lives japanese x) /\
(!x.
   ~person x \/ drinks x orange \/ drinks x coffee \/ drinks x tea \/
   drinks x milk \/ drinks x (water)) /\
(!x. ~drink x \/ ~drinks english x \/ ~drinks spaniard x) /\
(!x. ~drink x \/ ~drinks english x \/ ~drinks norwegian x) /\
(!x. ~drink x \/ ~drinks english x \/ ~drinks ukranian x) /\
(!x. ~drink x \/ ~drinks english x \/ ~drinks japanese x) /\
(!x. ~drink x \/ ~drinks spaniard x \/ ~drinks norwegian x) /\
(!x. ~drink x \/ ~drinks spaniard x \/ ~drinks ukranian x) /\
(!x. ~drink x \/ ~drinks spaniard x \/ ~drinks japanese x) /\
(!x. ~drink x \/ ~drinks norwegian x \/ ~drinks ukranian x) /\
(!x. ~drink x \/ ~drinks norwegian x \/ ~drinks japanese x) /\
(!x. ~drink x \/ ~drinks ukranian x \/ ~drinks japanese x) /\
(!x.
   ~person x \/ drives x masserati \/ drives x saab \/ drives x porsche \/
   drives x honda \/ drives x jaguar) /\
(!x. ~car x \/ ~drives english x \/ ~drives spaniard x) /\
(!x. ~car x \/ ~drives english x \/ ~drives norwegian x) /\
(!x. ~car x \/ ~drives english x \/ ~drives ukranian x) /\
(!x. ~car x \/ ~drives english x \/ ~drives japanese x) /\
(!x. ~car x \/ ~drives spaniard x \/ ~drives norwegian x) /\
(!x. ~car x \/ ~drives spaniard x \/ ~drives ukranian x) /\
(!x. ~car x \/ ~drives spaniard x \/ ~drives japanese x) /\
(!x. ~car x \/ ~drives norwegian x \/ ~drives ukranian x) /\
(!x. ~car x \/ ~drives norwegian x \/ ~drives japanese x) /\
(!x. ~car x \/ ~drives ukranian x \/ ~drives japanese x) /\
(!x.
   ~person x \/ owns x dog \/ owns x snails \/ owns x horse \/
   owns x fox \/ owns x (zebra)) /\
(!x. ~animal x \/ ~owns english x \/ ~owns spaniard x) /\
(!x. ~animal x \/ ~owns english x \/ ~owns norwegian x) /\
(!x. ~animal x \/ ~owns english x \/ ~owns ukranian x) /\
(!x. ~animal x \/ ~owns english x \/ ~owns japanese x) /\
(!x. ~animal x \/ ~owns spaniard x \/ ~owns norwegian x) /\
(!x. ~animal x \/ ~owns spaniard x \/ ~owns ukranian x) /\
(!x. ~animal x \/ ~owns spaniard x \/ ~owns japanese x) /\
(!x. ~animal x \/ ~owns norwegian x \/ ~owns ukranian x) /\
(!x. ~animal x \/ ~owns norwegian x \/ ~owns japanese x) /\
(!x. ~animal x \/ ~owns ukranian x \/ ~owns japanese x) /\
(!x.
   ~house x \/ is_color x red \/ is_color x (yellow) \/ is_color x blue \/
   is_color x green \/ is_color x ivory) /\
(!x. ~color x \/ ~is_color house_1 x \/ ~is_color house_2 x) /\
(!x. ~color x \/ ~is_color house_1 x \/ ~is_color house_3 x) /\
(!x. ~color x \/ ~is_color house_1 x \/ ~is_color house_4 x) /\
(!x. ~color x \/ ~is_color house_1 x \/ ~is_color house_5 x) /\
(!x. ~color x \/ ~is_color house_2 x \/ ~is_color house_3 x) /\
(!x. ~color x \/ ~is_color house_2 x \/ ~is_color house_4 x) /\
(!x. ~color x \/ ~is_color house_2 x \/ ~is_color house_5 x) /\
(!x. ~color x \/ ~is_color house_3 x \/ ~is_color house_4 x) /\
(!x. ~color x \/ ~is_color house_3 x \/ ~is_color house_5 x) /\
(!x. ~color x \/ ~is_color house_4 x \/ ~is_color house_5 x) /\
person english /\ person spaniard /\ person norwegian /\ person ukranian /\
person japanese /\ house house_1 /\ house house_2 /\ house house_3 /\
house house_4 /\ house house_5 /\ color red /\ color green /\
color (yellow) /\ color ivory /\ color blue /\ car jaguar /\ car honda /\
car masserati /\ car porsche /\ car saab /\ drink tea /\ drink orange /\
drink (water) /\ drink milk /\ drink coffee /\ animal dog /\
animal (zebra) /\ animal snails /\ animal horse /\ animal fox /\
(!x. is_color x red \/ ~house x \/ ~lives english x) /\
owns spaniard dog /\ lives norwegian house_1 /\
(!x y.
   is_color x (yellow) \/ ~person y \/ ~drives y masserati \/ ~house x \/
   ~lives y x) /\
(!x y z v.
   next_to x y \/ ~person z \/ ~owns z fox \/ ~house x \/ ~lives z x \/
   ~person v \/ ~drives v saab \/ ~house y \/ ~lives v y) /\
(!x y.
   is_color x blue \/ ~house y \/ ~lives norwegian y \/ ~house x \/
   ~next_to y x) /\
(!x. owns x snails \/ ~person x \/ ~drives x porsche) /\
(!x. drinks x orange \/ ~person x \/ ~drives x honda) /\
drinks ukranian tea /\ drives japanese jaguar /\
(!x y z v.
   next_to x y \/ ~person z \/ ~drives z masserati \/ ~house x \/
   ~lives z x \/ ~person v \/ ~owns v horse \/ ~house y \/ ~lives v y) /\
(!x y.
   is_color x green \/ ~person y \/ ~drinks y coffee \/ ~house x \/
   ~lives y x) /\
(!x y.
   left_of x y \/ ~house y \/ ~is_color y green \/ ~house x \/
   ~is_color x ivory) /\
(!x. lives x house_3 \/ ~person x \/ ~drinks x milk) /\
(!x y. next_to x y \/ ~left_of x y) /\
(!x y. next_to x y \/ ~left_of y x) /\
(!x y. left_of x y \/ ~next_to x y \/ left_of y x) /\
left_of house_1 house_2 /\ left_of house_2 house_3 /\
left_of house_3 house_4 /\ left_of house_4 house_5 /\
~left_of house_1 house_1 /\ ~left_of house_2 house_1 /\
~left_of house_3 house_1 /\ ~left_of house_4 house_1 /\
~left_of house_5 house_1 /\ ~left_of house_2 house_2 /\
~left_of house_3 house_2 /\ ~left_of house_4 house_2 /\
~left_of house_5 house_2 /\ ~left_of house_1 house_3 /\
~left_of house_3 house_3 /\ ~left_of house_4 house_3 /\
~left_of house_5 house_3 /\ ~left_of house_1 house_4 /\
~left_of house_2 house_4 /\ ~left_of house_4 house_4 /\
~left_of house_5 house_4 /\ ~left_of house_1 house_5 /\
~left_of house_2 house_5 /\ ~left_of house_3 house_5 /\
~left_of house_5 house_5 ==>
~drinks norwegian (water) \/ ~drinks ukranian tea \/
~drinks japanese coffee \/ ~drinks english milk \/
~drinks spaniard orange \/ ~owns norwegian fox \/ ~owns ukranian horse \/
~owns japanese (zebra) \/ ~owns english snails \/ ~owns spaniard dog \/
~drives norwegian masserati \/ ~drives ukranian saab \/
~drives japanese jaguar \/ ~drives english porsche \/
~drives spaniard honda \/ ~lives norwegian house_1 \/
~lives ukranian house_2 \/ ~lives japanese house_5 \/
~lives english house_3 \/ ~lives spaniard house_4 \/
~is_color house_1 (yellow) \/ ~is_color house_2 blue \/
~is_color house_3 red \/ ~is_color house_4 ivory \/
~is_color house_5 green ==> F`},

{name    = "PUZ011-1",
 comment = "",
 goal    = `
ocean atlantic /\ ocean indian /\ borders atlantic brazil /\
borders atlantic uruguay /\ borders atlantic (venesuela) /\
borders atlantic (zaire) /\ borders atlantic nigeria /\
borders atlantic angola /\ borders indian india /\
borders indian pakistan /\ borders indian iran /\ borders indian somalia /\
borders indian kenya /\ borders indian tanzania /\ south_american brazil /\
south_american uruguay /\ south_american (venesuela) /\ african (zaire) /\
african nigeria /\ african angola /\ african somalia /\ african kenya /\
african tanzania /\ asian india /\ asian pakistan /\ asian iran ==>
(!x y z.
   ~ocean x \/ ~borders x y \/ ~african y \/ ~borders x z \/ ~asian z) ==>
F`},

{name    = "PUZ012-1",
 comment = "",
 goal    = `
(!x. equal_fruits x x) /\ (!x. equal_boxes x x) /\
(!x y. ~label x y \/ ~contains x y) /\
(!x. contains boxa x \/ contains boxb x \/ contains boxc x) /\
(!x. contains x apples \/ contains x bananas \/ contains x oranges) /\
(!x y z. ~contains x y \/ ~contains x z \/ equal_fruits y z) /\
(!x y z. ~contains x y \/ ~contains z y \/ equal_boxes x z) /\
~equal_boxes boxa boxb /\ ~equal_boxes boxb boxc /\
~equal_boxes boxa boxc /\ ~equal_fruits apples bananas /\
~equal_fruits bananas oranges /\ ~equal_fruits apples oranges /\
label boxa apples /\ label boxb oranges /\ label boxc bananas /\
contains boxb apples ==>
~contains boxa bananas \/ ~contains boxc oranges ==> F`},

{name    = "PUZ013-1",
 comment = "",
 goal    = `
(~some_english_sing \/ ~some_english_sing_not \/
 some_monitors_are_awake) /\
(~some_scotch_dance \/ ~some_irish_fight \/ some_welsh_eat) /\
(~some_germans_play \/ some_germans_play_not \/
 some_of_the_eleven_are_not_oiling) /\
(~some_monitors_are_awake \/ ~some_monitors_are_not_awake \/
 some_irish_fight) /\
(~some_germans_play \/ some_scotch_dance \/ some_welsh_eat_not) /\
(~some_scotch_dance_not \/ ~some_irish_fight_not \/ some_germans_play) /\
(~some_monitors_are_awake \/ ~some_welsh_eat \/ ~some_scotch_dance) /\
(~some_germans_play_not \/ ~some_welsh_eat_not \/ ~some_irish_fight) /\
(~some_english_sing \/ some_english_sing_not \/ ~some_scotch_dance_not \/
 ~some_germans_play) /\
(~some_english_sing \/ ~some_monitors_are_not_awake \/
 some_irish_fight_not) /\
(~some_monitors_are_awake \/ ~some_of_the_eleven_are_not_oiling \/
 some_scotch_dance) /\ (some_english_sing_not \/ some_english_sing) /\
(some_monitors_are_not_awake \/ some_monitors_are_awake) /\
(some_scotch_dance \/ some_scotch_dance_not) /\
(some_irish_fight \/ some_irish_fight_not) /\
(some_welsh_eat \/ some_welsh_eat_not) /\
(some_germans_play \/ some_germans_play_not) /\ some_english_sing /\
some_scotch_dance_not ==> ~some_monitors_are_awake ==> F`},

{name    = "PUZ014-1",
 comment = "",
 goal    = `
(~some_english_sing \/ ~some_english_sing_not \/
 some_monitors_are_awake) /\
(~some_scotch_dance \/ ~some_irish_fight \/ some_welsh_eat) /\
(~some_germans_play \/ some_germans_play_not \/
 some_of_the_eleven_are_not_oiling) /\
(~some_monitors_are_awake \/ ~some_monitors_are_not_awake \/
 some_irish_fight) /\
(~some_germans_play \/ some_scotch_dance \/ some_welsh_eat_not) /\
(~some_scotch_dance_not \/ ~some_irish_fight_not \/ some_germans_play) /\
(~some_monitors_are_awake \/ ~some_welsh_eat \/ ~some_scotch_dance) /\
(~some_germans_play_not \/ ~some_welsh_eat_not \/ ~some_irish_fight) /\
(~some_english_sing \/ some_english_sing_not \/ ~some_scotch_dance_not \/
 ~some_germans_play) /\
(~some_english_sing \/ ~some_monitors_are_not_awake \/
 some_irish_fight_not) /\
(~some_monitors_are_awake \/ ~some_of_the_eleven_are_not_oiling \/
 some_scotch_dance) /\ (some_english_sing_not \/ some_english_sing) /\
(some_monitors_are_not_awake \/ some_monitors_are_awake) /\
(some_scotch_dance \/ some_scotch_dance_not) /\
(some_irish_fight \/ some_irish_fight_not) /\
(some_welsh_eat \/ some_welsh_eat_not) /\
(some_germans_play \/ some_germans_play_not) /\ some_english_sing /\
some_scotch_dance_not ==> some_monitors_are_not_awake ==> F`},

{name    = "PUZ015-2.006",
 comment = "",
 goal    = `
T ==>
~horizontal_1_1 /\ ~(vertical_1_1) /\ ~horizontal_6_5 /\ ~(vertical_5_6) /\
(horizontal_1_2 \/ (vertical_1_2) \/ horizontal_1_1) /\
(horizontal_1_3 \/ (vertical_1_3) \/ horizontal_1_2) /\
(horizontal_1_4 \/ (vertical_1_4) \/ horizontal_1_3) /\
(horizontal_1_5 \/ (vertical_1_5) \/ horizontal_1_4) /\
((vertical_1_6) \/ horizontal_1_5) /\
(horizontal_2_1 \/ (vertical_2_1) \/ (vertical_1_1)) /\
(horizontal_2_2 \/ (vertical_2_2) \/ horizontal_2_1 \/ (vertical_1_2)) /\
(horizontal_2_3 \/ (vertical_2_3) \/ horizontal_2_2 \/ (vertical_1_3)) /\
(horizontal_2_4 \/ (vertical_2_4) \/ horizontal_2_3 \/ (vertical_1_4)) /\
(horizontal_2_5 \/ (vertical_2_5) \/ horizontal_2_4 \/ (vertical_1_5)) /\
((vertical_2_6) \/ horizontal_2_5 \/ (vertical_1_6)) /\
(horizontal_3_1 \/ (vertical_3_1) \/ (vertical_2_1)) /\
(horizontal_3_2 \/ (vertical_3_2) \/ horizontal_3_1 \/ (vertical_2_2)) /\
(horizontal_3_3 \/ (vertical_3_3) \/ horizontal_3_2 \/ (vertical_2_3)) /\
(horizontal_3_4 \/ (vertical_3_4) \/ horizontal_3_3 \/ (vertical_2_4)) /\
(horizontal_3_5 \/ (vertical_3_5) \/ horizontal_3_4 \/ (vertical_2_5)) /\
((vertical_3_6) \/ horizontal_3_5 \/ (vertical_2_6)) /\
(horizontal_4_1 \/ (vertical_4_1) \/ (vertical_3_1)) /\
(horizontal_4_2 \/ (vertical_4_2) \/ horizontal_4_1 \/ (vertical_3_2)) /\
(horizontal_4_3 \/ (vertical_4_3) \/ horizontal_4_2 \/ (vertical_3_3)) /\
(horizontal_4_4 \/ (vertical_4_4) \/ horizontal_4_3 \/ (vertical_3_4)) /\
(horizontal_4_5 \/ (vertical_4_5) \/ horizontal_4_4 \/ (vertical_3_5)) /\
((vertical_4_6) \/ horizontal_4_5 \/ (vertical_3_6)) /\
(horizontal_5_1 \/ (vertical_5_1) \/ (vertical_4_1)) /\
(horizontal_5_2 \/ (vertical_5_2) \/ horizontal_5_1 \/ (vertical_4_2)) /\
(horizontal_5_3 \/ (vertical_5_3) \/ horizontal_5_2 \/ (vertical_4_3)) /\
(horizontal_5_4 \/ (vertical_5_4) \/ horizontal_5_3 \/ (vertical_4_4)) /\
(horizontal_5_5 \/ (vertical_5_5) \/ horizontal_5_4 \/ (vertical_4_5)) /\
((vertical_5_6) \/ horizontal_5_5 \/ (vertical_4_6)) /\
(horizontal_6_1 \/ (vertical_5_1)) /\
(horizontal_6_2 \/ horizontal_6_1 \/ (vertical_5_2)) /\
(horizontal_6_3 \/ horizontal_6_2 \/ (vertical_5_3)) /\
(horizontal_6_4 \/ horizontal_6_3 \/ (vertical_5_4)) /\
(horizontal_6_5 \/ horizontal_6_4 \/ (vertical_5_5)) /\
(~horizontal_1_2 \/ ~(vertical_1_2)) /\
(~horizontal_1_2 \/ ~horizontal_1_1) /\
(~(vertical_1_2) \/ ~horizontal_1_1) /\
(~horizontal_1_3 \/ ~(vertical_1_3)) /\
(~horizontal_1_3 \/ ~horizontal_1_2) /\
(~(vertical_1_3) \/ ~horizontal_1_2) /\
(~horizontal_1_4 \/ ~(vertical_1_4)) /\
(~horizontal_1_4 \/ ~horizontal_1_3) /\
(~(vertical_1_4) \/ ~horizontal_1_3) /\
(~horizontal_1_5 \/ ~(vertical_1_5)) /\
(~horizontal_1_5 \/ ~horizontal_1_4) /\
(~(vertical_1_5) \/ ~horizontal_1_4) /\
(~(vertical_1_6) \/ ~horizontal_1_5) /\
(~horizontal_2_1 \/ ~(vertical_2_1)) /\
(~horizontal_2_1 \/ ~(vertical_1_1)) /\
(~(vertical_2_1) \/ ~(vertical_1_1)) /\
(~horizontal_2_2 \/ ~(vertical_2_2)) /\
(~horizontal_2_2 \/ ~horizontal_2_1) /\
(~horizontal_2_2 \/ ~(vertical_1_2)) /\
(~(vertical_2_2) \/ ~horizontal_2_1) /\
(~(vertical_2_2) \/ ~(vertical_1_2)) /\
(~horizontal_2_1 \/ ~(vertical_1_2)) /\
(~horizontal_2_3 \/ ~(vertical_2_3)) /\
(~horizontal_2_3 \/ ~horizontal_2_2) /\
(~horizontal_2_3 \/ ~(vertical_1_3)) /\
(~(vertical_2_3) \/ ~horizontal_2_2) /\
(~(vertical_2_3) \/ ~(vertical_1_3)) /\
(~horizontal_2_2 \/ ~(vertical_1_3)) /\
(~horizontal_2_4 \/ ~(vertical_2_4)) /\
(~horizontal_2_4 \/ ~horizontal_2_3) /\
(~horizontal_2_4 \/ ~(vertical_1_4)) /\
(~(vertical_2_4) \/ ~horizontal_2_3) /\
(~(vertical_2_4) \/ ~(vertical_1_4)) /\
(~horizontal_2_3 \/ ~(vertical_1_4)) /\
(~horizontal_2_5 \/ ~(vertical_2_5)) /\
(~horizontal_2_5 \/ ~horizontal_2_4) /\
(~horizontal_2_5 \/ ~(vertical_1_5)) /\
(~(vertical_2_5) \/ ~horizontal_2_4) /\
(~(vertical_2_5) \/ ~(vertical_1_5)) /\
(~horizontal_2_4 \/ ~(vertical_1_5)) /\
(~(vertical_2_6) \/ ~horizontal_2_5) /\
(~(vertical_2_6) \/ ~(vertical_1_6)) /\
(~horizontal_2_5 \/ ~(vertical_1_6)) /\
(~horizontal_3_1 \/ ~(vertical_3_1)) /\
(~horizontal_3_1 \/ ~(vertical_2_1)) /\
(~(vertical_3_1) \/ ~(vertical_2_1)) /\
(~horizontal_3_2 \/ ~(vertical_3_2)) /\
(~horizontal_3_2 \/ ~horizontal_3_1) /\
(~horizontal_3_2 \/ ~(vertical_2_2)) /\
(~(vertical_3_2) \/ ~horizontal_3_1) /\
(~(vertical_3_2) \/ ~(vertical_2_2)) /\
(~horizontal_3_1 \/ ~(vertical_2_2)) /\
(~horizontal_3_3 \/ ~(vertical_3_3)) /\
(~horizontal_3_3 \/ ~horizontal_3_2) /\
(~horizontal_3_3 \/ ~(vertical_2_3)) /\
(~(vertical_3_3) \/ ~horizontal_3_2) /\
(~(vertical_3_3) \/ ~(vertical_2_3)) /\
(~horizontal_3_2 \/ ~(vertical_2_3)) /\
(~horizontal_3_4 \/ ~(vertical_3_4)) /\
(~horizontal_3_4 \/ ~horizontal_3_3) /\
(~horizontal_3_4 \/ ~(vertical_2_4)) /\
(~(vertical_3_4) \/ ~horizontal_3_3) /\
(~(vertical_3_4) \/ ~(vertical_2_4)) /\
(~horizontal_3_3 \/ ~(vertical_2_4)) /\
(~horizontal_3_5 \/ ~(vertical_3_5)) /\
(~horizontal_3_5 \/ ~horizontal_3_4) /\
(~horizontal_3_5 \/ ~(vertical_2_5)) /\
(~(vertical_3_5) \/ ~horizontal_3_4) /\
(~(vertical_3_5) \/ ~(vertical_2_5)) /\
(~horizontal_3_4 \/ ~(vertical_2_5)) /\
(~(vertical_3_6) \/ ~horizontal_3_5) /\
(~(vertical_3_6) \/ ~(vertical_2_6)) /\
(~horizontal_3_5 \/ ~(vertical_2_6)) /\
(~horizontal_4_1 \/ ~(vertical_4_1)) /\
(~horizontal_4_1 \/ ~(vertical_3_1)) /\
(~(vertical_4_1) \/ ~(vertical_3_1)) /\
(~horizontal_4_2 \/ ~(vertical_4_2)) /\
(~horizontal_4_2 \/ ~horizontal_4_1) /\
(~horizontal_4_2 \/ ~(vertical_3_2)) /\
(~(vertical_4_2) \/ ~horizontal_4_1) /\
(~(vertical_4_2) \/ ~(vertical_3_2)) /\
(~horizontal_4_1 \/ ~(vertical_3_2)) /\
(~horizontal_4_3 \/ ~(vertical_4_3)) /\
(~horizontal_4_3 \/ ~horizontal_4_2) /\
(~horizontal_4_3 \/ ~(vertical_3_3)) /\
(~(vertical_4_3) \/ ~horizontal_4_2) /\
(~(vertical_4_3) \/ ~(vertical_3_3)) /\
(~horizontal_4_2 \/ ~(vertical_3_3)) /\
(~horizontal_4_4 \/ ~(vertical_4_4)) /\
(~horizontal_4_4 \/ ~horizontal_4_3) /\
(~horizontal_4_4 \/ ~(vertical_3_4)) /\
(~(vertical_4_4) \/ ~horizontal_4_3) /\
(~(vertical_4_4) \/ ~(vertical_3_4)) /\
(~horizontal_4_3 \/ ~(vertical_3_4)) /\
(~horizontal_4_5 \/ ~(vertical_4_5)) /\
(~horizontal_4_5 \/ ~horizontal_4_4) /\
(~horizontal_4_5 \/ ~(vertical_3_5)) /\
(~(vertical_4_5) \/ ~horizontal_4_4) /\
(~(vertical_4_5) \/ ~(vertical_3_5)) /\
(~horizontal_4_4 \/ ~(vertical_3_5)) /\
(~(vertical_4_6) \/ ~horizontal_4_5) /\
(~(vertical_4_6) \/ ~(vertical_3_6)) /\
(~horizontal_4_5 \/ ~(vertical_3_6)) /\
(~horizontal_5_1 \/ ~(vertical_5_1)) /\
(~horizontal_5_1 \/ ~(vertical_4_1)) /\
(~(vertical_5_1) \/ ~(vertical_4_1)) /\
(~horizontal_5_2 \/ ~(vertical_5_2)) /\
(~horizontal_5_2 \/ ~horizontal_5_1) /\
(~horizontal_5_2 \/ ~(vertical_4_2)) /\
(~(vertical_5_2) \/ ~horizontal_5_1) /\
(~(vertical_5_2) \/ ~(vertical_4_2)) /\
(~horizontal_5_1 \/ ~(vertical_4_2)) /\
(~horizontal_5_3 \/ ~(vertical_5_3)) /\
(~horizontal_5_3 \/ ~horizontal_5_2) /\
(~horizontal_5_3 \/ ~(vertical_4_3)) /\
(~(vertical_5_3) \/ ~horizontal_5_2) /\
(~(vertical_5_3) \/ ~(vertical_4_3)) /\
(~horizontal_5_2 \/ ~(vertical_4_3)) /\
(~horizontal_5_4 \/ ~(vertical_5_4)) /\
(~horizontal_5_4 \/ ~horizontal_5_3) /\
(~horizontal_5_4 \/ ~(vertical_4_4)) /\
(~(vertical_5_4) \/ ~horizontal_5_3) /\
(~(vertical_5_4) \/ ~(vertical_4_4)) /\
(~horizontal_5_3 \/ ~(vertical_4_4)) /\
(~horizontal_5_5 \/ ~(vertical_5_5)) /\
(~horizontal_5_5 \/ ~horizontal_5_4) /\
(~horizontal_5_5 \/ ~(vertical_4_5)) /\
(~(vertical_5_5) \/ ~horizontal_5_4) /\
(~(vertical_5_5) \/ ~(vertical_4_5)) /\
(~horizontal_5_4 \/ ~(vertical_4_5)) /\
(~(vertical_5_6) \/ ~horizontal_5_5) /\
(~(vertical_5_6) \/ ~(vertical_4_6)) /\
(~horizontal_5_5 \/ ~(vertical_4_6)) /\
(~horizontal_6_1 \/ ~(vertical_5_1)) /\
(~horizontal_6_2 \/ ~horizontal_6_1) /\
(~horizontal_6_2 \/ ~(vertical_5_2)) /\
(~horizontal_6_1 \/ ~(vertical_5_2)) /\
(~horizontal_6_3 \/ ~horizontal_6_2) /\
(~horizontal_6_3 \/ ~(vertical_5_3)) /\
(~horizontal_6_2 \/ ~(vertical_5_3)) /\
(~horizontal_6_4 \/ ~horizontal_6_3) /\
(~horizontal_6_4 \/ ~(vertical_5_4)) /\
(~horizontal_6_3 \/ ~(vertical_5_4)) /\
(~horizontal_6_5 \/ ~horizontal_6_4) /\
(~horizontal_6_5 \/ ~(vertical_5_5)) /\
(~horizontal_6_4 \/ ~(vertical_5_5)) ==> F`},

{name    = "PUZ016-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x = y) \/ complement x = complement y) /\
(!x y. ~(x = y) \/ row x = row y) /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares x z v w x' y' z' v' = squares y z v w x' y' z' v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z x v w x' y' z' v' = squares z y v w x' y' z' v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z v x w x' y' z' v' = squares z v y w x' y' z' v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z v w x x' y' z' v' = squares z v w y x' y' z' v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z v w x' x y' z' v' = squares z v w x' y y' z' v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z v w x' y' x z' v' = squares z v w x' y' y z' v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z v w x' y' z' x v' = squares z v w x' y' z' y v') /\
(!x y z v w x' y' z' v'.
   ~(x = y) \/
   squares z v w x' y' z' v' x = squares z v w x' y' z' v' y) /\
(!x y. ~(x = y) \/ successor x = successor y) /\
(!x y z. ~(x = y) \/ ~achievable x z \/ achievable y z) /\
(!x y z. ~(x = y) \/ ~achievable z x \/ achievable z y) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares not_covered not_covered y z v w x' y') \/
   achievable (row x) (squares covered covered y z v w x' y')) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares y not_covered not_covered z v w x' y') \/
   achievable (row x) (squares y covered covered z v w x' y')) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares y z not_covered not_covered v w x' y') \/
   achievable (row x) (squares y z covered covered v w x' y')) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares y z v not_covered not_covered w x' y') \/
   achievable (row x) (squares y z v covered covered w x' y')) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares y z v w not_covered not_covered x' y') \/
   achievable (row x) (squares y z v w covered covered x' y')) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares y z v w x' not_covered not_covered y') \/
   achievable (row x) (squares y z v w x' covered covered y')) /\
(!x y z v w x' y'.
   ~achievable (row x) (squares y z v w x' y' not_covered not_covered) \/
   achievable (row x) (squares y z v w x' y' covered covered)) /\
(!x y z v w x' y' z' v'.
   ~achievable (row x) (squares y z v w x' y' z' v') \/
   achievable (row (successor x))
   (squares (complement y) (complement z) (complement v) (complement w)
    (complement x') (complement y') (complement z') (complement v'))) /\
successor 1 = 2 /\ successor 2 = 3 /\ successor 3 = 4 /\ successor 4 = 5 /\
successor 5 = 6 /\ successor 6 = 7 /\ successor 7 = 8 /\ successor 8 = 9 /\
complement covered = not_covered /\ complement not_covered = covered /\
complement removed = not_covered /\
achievable (row 1)
(squares not_covered removed removed not_covered not_covered not_covered
 not_covered not_covered) ==>
~achievable (row 8)
 (squares covered covered covered covered covered covered covered
  covered) ==> F`},

{name    = "PUZ016-2.005",
 comment = "",
 goal    = `
T ==>
~horizontal_1_2 /\ ~horizontal_1_3 /\ ~(vertical_1_2) /\ ~(vertical_1_3) /\
~horizontal_1_1 /\ ~horizontal_1_2 /\ (horizontal_1_1 \/ (vertical_1_1)) /\
(horizontal_1_4 \/ (vertical_1_4) \/ horizontal_1_3) /\
((vertical_1_5) \/ horizontal_1_4) /\
(horizontal_2_1 \/ (vertical_2_1) \/ (vertical_1_1)) /\
(horizontal_2_2 \/ (vertical_2_2) \/ horizontal_2_1 \/ (vertical_1_2)) /\
(horizontal_2_3 \/ (vertical_2_3) \/ horizontal_2_2 \/ (vertical_1_3)) /\
(horizontal_2_4 \/ (vertical_2_4) \/ horizontal_2_3 \/ (vertical_1_4)) /\
((vertical_2_5) \/ horizontal_2_4 \/ (vertical_1_5)) /\
(horizontal_3_1 \/ (vertical_3_1) \/ (vertical_2_1)) /\
(horizontal_3_2 \/ (vertical_3_2) \/ horizontal_3_1 \/ (vertical_2_2)) /\
(horizontal_3_3 \/ (vertical_3_3) \/ horizontal_3_2 \/ (vertical_2_3)) /\
(horizontal_3_4 \/ (vertical_3_4) \/ horizontal_3_3 \/ (vertical_2_4)) /\
((vertical_3_5) \/ horizontal_3_4 \/ (vertical_2_5)) /\
(horizontal_4_1 \/ (vertical_4_1) \/ (vertical_3_1)) /\
(horizontal_4_2 \/ (vertical_4_2) \/ horizontal_4_1 \/ (vertical_3_2)) /\
(horizontal_4_3 \/ (vertical_4_3) \/ horizontal_4_2 \/ (vertical_3_3)) /\
(horizontal_4_4 \/ (vertical_4_4) \/ horizontal_4_3 \/ (vertical_3_4)) /\
((vertical_4_5) \/ horizontal_4_4 \/ (vertical_3_5)) /\
(horizontal_5_1 \/ (vertical_4_1)) /\
(horizontal_5_2 \/ horizontal_5_1 \/ (vertical_4_2)) /\
(horizontal_5_3 \/ horizontal_5_2 \/ (vertical_4_3)) /\
(horizontal_5_4 \/ horizontal_5_3 \/ (vertical_4_4)) /\
(horizontal_5_4 \/ (vertical_4_5)) /\
(~horizontal_1_1 \/ ~(vertical_1_1)) /\
(~horizontal_1_4 \/ ~(vertical_1_4)) /\
(~horizontal_1_4 \/ ~horizontal_1_3) /\
(~(vertical_1_4) \/ ~horizontal_1_3) /\
(~(vertical_1_5) \/ ~horizontal_1_4) /\
(~horizontal_2_1 \/ ~(vertical_2_1)) /\
(~horizontal_2_1 \/ ~(vertical_1_1)) /\
(~(vertical_2_1) \/ ~(vertical_1_1)) /\
(~horizontal_2_2 \/ ~(vertical_2_2)) /\
(~horizontal_2_2 \/ ~horizontal_2_1) /\
(~horizontal_2_2 \/ ~(vertical_1_2)) /\
(~(vertical_2_2) \/ ~horizontal_2_1) /\
(~(vertical_2_2) \/ ~(vertical_1_2)) /\
(~horizontal_2_1 \/ ~(vertical_1_2)) /\
(~horizontal_2_3 \/ ~(vertical_2_3)) /\
(~horizontal_2_3 \/ ~horizontal_2_2) /\
(~horizontal_2_3 \/ ~(vertical_1_3)) /\
(~(vertical_2_3) \/ ~horizontal_2_2) /\
(~(vertical_2_3) \/ ~(vertical_1_3)) /\
(~horizontal_2_2 \/ ~(vertical_1_3)) /\
(~horizontal_2_4 \/ ~(vertical_2_4)) /\
(~horizontal_2_4 \/ ~horizontal_2_3) /\
(~horizontal_2_4 \/ ~(vertical_1_4)) /\
(~(vertical_2_4) \/ ~horizontal_2_3) /\
(~(vertical_2_4) \/ ~(vertical_1_4)) /\
(~horizontal_2_3 \/ ~(vertical_1_4)) /\
(~(vertical_2_5) \/ ~horizontal_2_4) /\
(~(vertical_2_5) \/ ~(vertical_1_5)) /\
(~horizontal_2_4 \/ ~(vertical_1_5)) /\
(~horizontal_3_1 \/ ~(vertical_3_1)) /\
(~horizontal_3_1 \/ ~(vertical_2_1)) /\
(~(vertical_3_1) \/ ~(vertical_2_1)) /\
(~horizontal_3_2 \/ ~(vertical_3_2)) /\
(~horizontal_3_2 \/ ~horizontal_3_1) /\
(~horizontal_3_2 \/ ~(vertical_2_2)) /\
(~(vertical_3_2) \/ ~horizontal_3_1) /\
(~(vertical_3_2) \/ ~(vertical_2_2)) /\
(~horizontal_3_1 \/ ~(vertical_2_2)) /\
(~horizontal_3_3 \/ ~(vertical_3_3)) /\
(~horizontal_3_3 \/ ~horizontal_3_2) /\
(~horizontal_3_3 \/ ~(vertical_2_3)) /\
(~(vertical_3_3) \/ ~horizontal_3_2) /\
(~(vertical_3_3) \/ ~(vertical_2_3)) /\
(~horizontal_3_2 \/ ~(vertical_2_3)) /\
(~horizontal_3_4 \/ ~(vertical_3_4)) /\
(~horizontal_3_4 \/ ~horizontal_3_3) /\
(~horizontal_3_4 \/ ~(vertical_2_4)) /\
(~(vertical_3_4) \/ ~horizontal_3_3) /\
(~(vertical_3_4) \/ ~(vertical_2_4)) /\
(~horizontal_3_3 \/ ~(vertical_2_4)) /\
(~(vertical_3_5) \/ ~horizontal_3_4) /\
(~(vertical_3_5) \/ ~(vertical_2_5)) /\
(~horizontal_3_4 \/ ~(vertical_2_5)) /\
(~horizontal_4_1 \/ ~(vertical_4_1)) /\
(~horizontal_4_1 \/ ~(vertical_3_1)) /\
(~(vertical_4_1) \/ ~(vertical_3_1)) /\
(~horizontal_4_2 \/ ~(vertical_4_2)) /\
(~horizontal_4_2 \/ ~horizontal_4_1) /\
(~horizontal_4_2 \/ ~(vertical_3_2)) /\
(~(vertical_4_2) \/ ~horizontal_4_1) /\
(~(vertical_4_2) \/ ~(vertical_3_2)) /\
(~horizontal_4_1 \/ ~(vertical_3_2)) /\
(~horizontal_4_3 \/ ~(vertical_4_3)) /\
(~horizontal_4_3 \/ ~horizontal_4_2) /\
(~horizontal_4_3 \/ ~(vertical_3_3)) /\
(~(vertical_4_3) \/ ~horizontal_4_2) /\
(~(vertical_4_3) \/ ~(vertical_3_3)) /\
(~horizontal_4_2 \/ ~(vertical_3_3)) /\
(~horizontal_4_4 \/ ~(vertical_4_4)) /\
(~horizontal_4_4 \/ ~horizontal_4_3) /\
(~horizontal_4_4 \/ ~(vertical_3_4)) /\
(~(vertical_4_4) \/ ~horizontal_4_3) /\
(~(vertical_4_4) \/ ~(vertical_3_4)) /\
(~horizontal_4_3 \/ ~(vertical_3_4)) /\
(~(vertical_4_5) \/ ~horizontal_4_4) /\
(~(vertical_4_5) \/ ~(vertical_3_5)) /\
(~horizontal_4_4 \/ ~(vertical_3_5)) /\
(~horizontal_5_1 \/ ~(vertical_4_1)) /\
(~horizontal_5_2 \/ ~horizontal_5_1) /\
(~horizontal_5_2 \/ ~(vertical_4_2)) /\
(~horizontal_5_1 \/ ~(vertical_4_2)) /\
(~horizontal_5_3 \/ ~horizontal_5_2) /\
(~horizontal_5_3 \/ ~(vertical_4_3)) /\
(~horizontal_5_2 \/ ~(vertical_4_3)) /\
(~horizontal_5_4 \/ ~horizontal_5_3) /\
(~horizontal_5_4 \/ ~(vertical_4_4)) /\
(~horizontal_5_3 \/ ~(vertical_4_4)) /\
(~horizontal_5_4 \/ ~(vertical_4_5)) ==> F`},

{name    = "PUZ017-1",
 comment = "",
 goal    = `
(!x. samehouse x x) /\ ~samehouse 1 2 /\ ~samehouse 1 3 /\
~samehouse 1 4 /\ ~samehouse 1 5 /\ ~samehouse 2 3 /\ ~samehouse 2 4 /\
~samehouse 2 5 /\ ~samehouse 3 4 /\ ~samehouse 3 5 /\ ~samehouse 4 5 /\
(!x. sameperson x x) /\ ~sameperson englishman italian /\
~sameperson englishman swede /\ ~sameperson englishman russian /\
~sameperson englishman american /\ ~sameperson italian swede /\
~sameperson italian russian /\ ~sameperson italian american /\
~sameperson swede russian /\ ~sameperson swede american /\
~sameperson russian american /\ (!x. samecolor x x) /\
~samecolor red (white) /\ ~samecolor red green /\
~samecolor red (yellow) /\ ~samecolor red blue /\
~samecolor (white) green /\ ~samecolor (white) (yellow) /\
~samecolor (white) blue /\ ~samecolor green (yellow) /\
~samecolor green blue /\ ~samecolor (yellow) blue /\ (!x. samedrink x x) /\
~samedrink lemonade coffee /\ ~samedrink lemonade milk /\
~samedrink lemonade (vodka) /\ ~samedrink lemonade unknown_drink /\
~samedrink coffee milk /\ ~samedrink coffee (vodka) /\
~samedrink coffee unknown_drink /\ ~samedrink milk (vodka) /\
~samedrink milk unknown_drink /\ ~samedrink (vodka) unknown_drink /\
(!x. samegame x x) /\ ~samegame backgammon racquetball /\
~samegame backgammon quoits /\ ~samegame backgammon solitaire /\
~samegame backgammon charades /\ ~samegame racquetball quoits /\
~samegame racquetball solitaire /\ ~samegame racquetball charades /\
~samegame quoits solitaire /\ ~samegame quoits charades /\
~samegame solitaire charades /\ (!x. samepet x x) /\ ~samepet guppy toad /\
~samepet guppy camel /\ ~samepet guppy rat /\ ~samepet guppy no_pet /\
~samepet toad camel /\ ~samepet toad rat /\ ~samepet toad no_pet /\
~samepet camel rat /\ ~samepet camel no_pet /\ ~samepet rat no_pet /\
(!x y. ~nextto x y \/ nextto y x) /\ (!x y. ~left x y \/ ~left y x) /\
(!x y. ~nextto x y \/ left x y \/ left y x) /\
(!x y. ~left x y \/ nextto x y) /\ (!x y. ~samehouse x y \/ ~nextto x y) /\
(!x. ~left x x) /\ (!x. ~nextto x x) /\
(!x.
   hasperson x englishman \/ hasperson x italian \/ hasperson x swede \/
   hasperson x russian \/ hasperson x american) /\
(!x.
   hasperson 1 x \/ hasperson 2 x \/ hasperson 3 x \/ hasperson 4 x \/
   hasperson 5 x) /\
(!x.
   hascolor x red \/ hascolor x (white) \/ hascolor x green \/
   hascolor x (yellow) \/ hascolor x blue) /\
(!x.
   hascolor 1 x \/ hascolor 2 x \/ hascolor 3 x \/ hascolor 4 x \/
   hascolor 5 x) /\
(!x.
   hasdrink x lemonade \/ hasdrink x coffee \/ hasdrink x milk \/
   hasdrink x (vodka) \/ hasdrink x unknown_drink) /\
(!x.
   hasdrink 1 x \/ hasdrink 2 x \/ hasdrink 3 x \/ hasdrink 4 x \/
   hasdrink 5 x) /\
(!x.
   hasgame x backgammon \/ hasgame x racquetball \/ hasgame x quoits \/
   hasgame x solitaire \/ hasgame x charades) /\
(!x.
   hasgame 1 x \/ hasgame 2 x \/ hasgame 3 x \/ hasgame 4 x \/
   hasgame 5 x) /\
(!x.
   haspet x guppy \/ haspet x toad \/ haspet x camel \/ haspet x rat \/
   haspet x no_pet) /\
(!x. haspet 1 x \/ haspet 2 x \/ haspet 3 x \/ haspet 4 x \/ haspet 5 x) /\
(!x y z. samehouse x y \/ ~hascolor x z \/ ~hascolor y z) /\
(!x y z. samehouse x y \/ ~hasperson x z \/ ~hasperson y z) /\
(!x y z. samehouse x y \/ ~hasdrink x z \/ ~hasdrink y z) /\
(!x y z. samehouse x y \/ ~hasgame x z \/ ~hasgame y z) /\
(!x y z. samehouse x y \/ ~haspet x z \/ ~haspet y z) /\
(!x y z. sameperson x y \/ ~hasperson z x \/ ~hasperson z y) /\
(!x y z. samecolor x y \/ ~hascolor z x \/ ~hascolor z y) /\
(!x y z. samedrink x y \/ ~hasdrink z x \/ ~hasdrink z y) /\
(!x y z. samegame x y \/ ~hasgame z x \/ ~hasgame z y) /\
(!x y z. samepet x y \/ ~haspet z x \/ ~haspet z y) /\
(!x. ~hasperson x englishman \/ hascolor x red) /\
(!x. hasperson x englishman \/ ~hascolor x red) /\
(!x y. ~hascolor x (white) \/ ~hascolor y green \/ left x y) /\
(!x y. ~hascolor x (white) \/ hascolor y green \/ ~left x y) /\
(!x y. hascolor x (white) \/ ~hascolor y green \/ ~left x y) /\
(!x. ~hasperson x italian \/ haspet x guppy) /\
(!x. hasperson x italian \/ ~haspet x guppy) /\
(!x. ~hasdrink x lemonade \/ hascolor x green) /\
(!x. hasdrink x lemonade \/ ~hascolor x green) /\
(!x. ~hasperson x swede \/ hasdrink x coffee) /\
(!x. hasperson x swede \/ ~hasdrink x coffee) /\
(!x. ~haspet x toad \/ hasgame x backgammon) /\
(!x. haspet x toad \/ ~hasgame x backgammon) /\
(!x. ~hasgame x racquetball \/ hascolor x (yellow)) /\
(!x. hasgame x racquetball \/ ~hascolor x (yellow)) /\
(!x y z.
   ~haspet x camel \/ samehouse y z \/ ~nextto x y \/ ~nextto x z \/
   hasgame y quoits \/ hasgame z quoits) /\
(!x y.
   ~haspet x camel \/ ~samehouse 1 x \/ ~nextto x y \/ hasgame y quoits) /\
(!x y.
   ~haspet x camel \/ ~samehouse x 5 \/ ~nextto x y \/ hasgame y quoits) /\
(!x y. ~haspet x camel \/ nextto x y \/ ~hasgame y quoits) /\
(!x y z.
   samehouse x y \/ ~nextto z x \/ ~nextto z y \/ ~hasgame z quoits \/
   haspet x camel \/ haspet y camel) /\
(!x y.
   ~samehouse 1 x \/ ~nextto x y \/ ~hasgame x quoits \/ haspet y camel) /\
(!x y.
   ~samehouse x 5 \/ ~nextto x y \/ ~hasgame x quoits \/ haspet y camel) /\
(!x y z.
   ~haspet x rat \/ samehouse y z \/ ~nextto x y \/ ~nextto x z \/
   hasgame y racquetball \/ hasgame z racquetball) /\
(!x y.
   ~haspet x rat \/ ~nextto x y \/ ~samehouse 1 x \/
   hasgame y racquetball) /\
(!x y.
   ~haspet x rat \/ ~nextto x y \/ ~samehouse x 5 \/
   hasgame y racquetball) /\
(!x y. ~haspet x rat \/ nextto x y \/ ~hasgame y racquetball) /\
(!x y z.
   samehouse x y \/ ~nextto z x \/ ~nextto z y \/ ~hasgame z racquetball \/
   haspet x rat \/ haspet y rat) /\
(!x y.
   ~nextto x y \/ ~samehouse 1 x \/ ~hasgame x racquetball \/
   haspet y rat) /\
(!x y.
   ~nextto x y \/ ~samehouse x 5 \/ ~hasgame x racquetball \/
   haspet y rat) /\ (!x. ~hasgame x solitaire \/ hasdrink x (vodka)) /\
(!x. hasgame x solitaire \/ ~hasdrink x (vodka)) /\
(!x. ~hasperson x american \/ hasgame x charades) /\
(!x. hasperson x american \/ ~hasgame x charades) /\
(!x y z.
   ~hasperson x russian \/ samehouse y z \/ ~nextto x y \/ ~nextto x z \/
   hascolor y blue \/ hascolor z blue) /\
(!x y.
   ~hasperson x russian \/ ~samehouse 1 x \/ ~nextto x y \/
   hascolor y blue) /\
(!x y.
   ~hasperson x russian \/ ~samehouse x 5 \/ ~nextto x y \/
   hascolor y blue) /\
(!x y. ~hasperson x russian \/ nextto x y \/ ~hascolor y blue) /\
(!x y z.
   samehouse x y \/ ~nextto z x \/ ~nextto z y \/ ~hascolor z blue \/
   hasperson x russian \/ hasperson y russian) /\
(!x y.
   ~nextto x y \/ ~hascolor x blue \/ ~samehouse 1 x \/
   hasperson y russian) /\
(!x y.
   ~nextto x y \/ ~hascolor x blue \/ ~samehouse x 5 \/
   hasperson y russian) /\ (!x. ~left x 1) /\ (!x. ~left 5 x) /\
left 1 2 /\ left 2 3 /\ left 3 4 /\ left 4 5 /\ ~nextto 1 3 /\
~nextto 1 4 /\ ~nextto 1 5 /\ ~nextto 2 4 /\ ~nextto 2 5 /\ ~nextto 3 5 /\
hasdrink 3 milk /\ hasperson 1 russian ==>
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4.
   ~hasperson 1 x \/ ~hasperson 2 y \/ ~hasperson 3 z \/ ~hasperson 4 v \/
   ~hasperson 5 w \/ ~hascolor 1 x1 \/ ~hascolor 2 y1 \/ ~hascolor 3 z1 \/
   ~hascolor 4 v1 \/ ~hascolor 5 w1 \/ ~hasdrink 1 x2 \/ ~hasdrink 2 y2 \/
   ~hasdrink 3 z2 \/ ~hasdrink 4 v2 \/ ~hasdrink 5 w2 \/ ~hasgame 1 x3 \/
   ~hasgame 2 y3 \/ ~hasgame 3 z3 \/ ~hasgame 4 v3 \/ ~hasgame 5 w3 \/
   ~haspet 1 x4 \/ ~haspet 2 y4 \/ ~haspet 3 z4 \/ ~haspet 4 v4 \/
   ~haspet 5 w4) ==> F`},

{name    = "PUZ018-1",
 comment = "",
 goal    = `
(!x. ~all_on x \/ on a x) /\ (!x. ~all_on x \/ on b x) /\
(!x. ~all_on x \/ on c x) /\
(!x. all_on x \/ ~on a x \/ ~on b x \/ ~on c x) /\
(!x y. ~all_on x \/ ~all_on y \/ same_day x y) /\
consecutive sunday monday /\ consecutive monday tuesday /\
consecutive tuesday (wednesday) /\ consecutive (wednesday) thursday /\
consecutive thursday friday /\ consecutive friday saturday /\
consecutive saturday sunday /\ (!x. same_person x x) /\ ~same_person a b /\
~same_person a c /\ ~same_person b c /\ (!x. same_day x x) /\
~same_day sunday monday /\ ~same_day sunday tuesday /\
~same_day sunday (wednesday) /\ ~same_day sunday thursday /\
~same_day sunday friday /\ ~same_day sunday saturday /\
~same_day monday tuesday /\ ~same_day monday (wednesday) /\
~same_day monday thursday /\ ~same_day monday friday /\
~same_day monday saturday /\ ~same_day tuesday (wednesday) /\
~same_day tuesday thursday /\ ~same_day tuesday friday /\
~same_day tuesday saturday /\ ~same_day (wednesday) thursday /\
~same_day (wednesday) friday /\ ~same_day (wednesday) saturday /\
~same_day thursday friday /\ ~same_day thursday saturday /\
~same_day friday saturday /\
(all_on sunday \/ all_on monday \/ all_on tuesday \/ all_on (wednesday) \/
 all_on thursday \/ all_on friday \/ all_on saturday) /\
(!x y z v w.
   ~consecutive x y \/ ~consecutive y z \/ ~consecutive z v \/ ~on w x \/
   ~on w y \/ ~on w z) /\
(!x y z v.
   on x y \/ on x z \/ on v y \/ on v z \/ same_person x v \/
   same_day y z) /\ ~on a sunday /\ ~on a tuesday /\ ~on a thursday /\
~on b thursday /\ ~on b saturday /\ ~on c sunday ==> ~all_on friday ==> F`},

{name    = "PUZ019-1",
 comment = "",
 goal    = `
(!x. equal_people x x) /\ (!x. equal_jobs x x) /\
(!x y. ~equal_people x y \/ equal_people y x) /\
(!x y. ~equal_jobs x y \/ equal_jobs y x) /\
~equal_people roberta thelma /\ ~equal_people roberta pete /\
~equal_people roberta steve /\ ~equal_people pete thelma /\
~equal_people pete steve /\ ~equal_jobs chef guard /\
~equal_jobs chef nurse /\ ~equal_jobs chef operator /\
~equal_jobs chef police /\ ~equal_jobs chef actor /\
~equal_jobs chef boxer /\ ~equal_jobs chef teacher /\
~equal_jobs guard nurse /\ ~equal_jobs guard operator /\
~equal_jobs guard police /\ ~equal_jobs guard actor /\
~equal_jobs guard boxer /\ ~equal_jobs guard teacher /\
~equal_jobs nurse operator /\ ~equal_jobs nurse police /\
~equal_jobs nurse actor /\ ~equal_jobs nurse boxer /\
~equal_jobs nurse teacher /\ ~equal_jobs operator police /\
~equal_jobs operator actor /\ ~equal_jobs operator boxer /\
~equal_jobs operator teacher /\ ~equal_jobs police actor /\
~equal_jobs police boxer /\ ~equal_jobs police teacher /\
~equal_jobs actor boxer /\ ~equal_jobs actor teacher /\
~equal_jobs boxer teacher /\ (!x. ~has_job x nurse \/ male x) /\
(!x. ~has_job x actor \/ male x) /\ (!x. ~has_job x chef \/ female x) /\
(!x. ~has_job x nurse \/ educated x) /\
(!x. ~has_job x teacher \/ educated x) /\
(!x. ~has_job x police \/ educated x) /\
(!x. ~has_job x chef \/ ~has_job x police) /\ (!x. ~male x \/ ~female x) /\
(!x. male x \/ female x) /\ (!x y. ~husband x y \/ male y) /\
(!x y. ~husband x y \/ female x) /\
(!x y. ~has_job x chef \/ ~has_job y operator \/ husband x y) /\
(!x y. ~has_job x chef \/ has_job y operator \/ ~husband x y) /\
(!x y z. ~has_job x y \/ ~has_job z y \/ equal_people x z) /\
(!x y z v.
   ~has_job x y \/ ~has_job x z \/ ~has_job x v \/ equal_jobs y z \/
   equal_jobs y v \/ equal_jobs z v) /\
(!x.
   has_job roberta x \/ has_job thelma x \/ has_job pete x \/
   has_job steve x) /\
(!x.
   has_job x chef \/ has_job x guard \/ has_job x nurse \/
   has_job x operator \/ has_job x police \/ has_job x teacher \/
   has_job x actor \/ has_job x boxer) /\ ~educated pete /\
~has_job roberta chef /\ ~has_job roberta boxer /\
~has_job roberta police /\ male steve /\ male pete /\ female roberta /\
female thelma ==>
(!x y z v w x' y' z'.
   ~has_job x chef \/ ~has_job y guard \/ ~has_job z nurse \/
   ~has_job v operator \/ ~has_job w police \/ ~has_job x' teacher \/
   ~has_job y' actor \/ ~has_job z' boxer) ==> F`},

{name    = "PUZ020-1",
 comment = "",
 goal    = `
(!x. x = x) /\ (!x y. ~(x = y) \/ y = x) /\
(!x y z. ~(x = y) \/ ~(y = z) \/ x = z) /\
(!x y. ~(x = y) \/ statement_by x = statement_by y) /\
(!x. ~person x \/ knight x \/ knave x) /\
(!x. ~person x \/ ~knight x \/ ~knave x) /\
(!x y. ~says x y \/ a_truth y \/ ~a_truth y) /\
(!x y. ~says x y \/ ~(x = y)) /\ (!x y. ~says x y \/ y = statement_by x) /\
(!x y. ~person x \/ ~(x = statement_by y)) /\
(!x. ~person x \/ ~a_truth (statement_by x) \/ knight x) /\
(!x. ~person x \/ a_truth (statement_by x) \/ knave x) /\
(!x y. ~(x = y) \/ ~knight x \/ knight y) /\
(!x y. ~(x = y) \/ ~knave x \/ knave y) /\
(!x y. ~(x = y) \/ ~person x \/ person y) /\
(!x y z. ~(x = y) \/ ~says x z \/ says y z) /\
(!x y z. ~(x = y) \/ ~says z x \/ says z y) /\
(!x y. ~(x = y) \/ ~a_truth x \/ a_truth y) /\
(!x y. ~knight x \/ ~says x y \/ a_truth y) /\
(!x y. ~knave x \/ ~says x y \/ ~a_truth y) /\ person husband /\
person (wife) /\ ~(husband = (wife)) /\
says husband (statement_by husband) /\
(~a_truth (statement_by husband) \/ ~knight husband \/ knight (wife)) /\
(a_truth (statement_by husband) \/ ~knight husband) /\
(a_truth (statement_by husband) \/ knight (wife)) /\
(~knight (wife) \/ a_truth (statement_by husband)) ==> ~knight husband ==>
F`},

{name    = "PUZ021-1",
 comment = "",
 goal    = `
(!x y. ~a_truth (knight x) y \/ ~a_truth (knave x) y) /\
(!x y. a_truth (knight x) y \/ a_truth (knave x) y) /\
(!x y. ~a_truth (rich x) y \/ ~a_truth (poor x) y) /\
(!x y. a_truth (rich x) y \/ a_truth (poor x) y) /\
(!x y z. ~a_truth (knight x) y \/ ~says x z \/ a_truth z y) /\
(!x y z. ~a_truth (knight x) y \/ says x z \/ ~a_truth z y) /\
(!x y z. ~a_truth (knave x) y \/ ~says x z \/ ~a_truth z y) /\
(!x y z. ~a_truth (knave x) y \/ says x z \/ a_truth z y) /\
(!x y z. ~a_truth (and x y) z \/ a_truth x z) /\
(!x y z. ~a_truth (and x y) z \/ a_truth y z) /\
(!x y z. a_truth (and x y) z \/ ~a_truth x z \/ ~a_truth y z) ==>
(!x. ~says me x \/ ~a_truth (and (knave me) (rich me)) x) /\
(!x. says me x \/ a_truth (and (knave me) (rich me)) x) ==> F`},

{name    = "PUZ022-1",
 comment = "",
 goal    = `
(!x y. ~borders x y \/ borders y x) ==>
ocean atlantic /\ ocean indian /\ ocean pacific /\ ocean southern /\
state (western_australia) /\ state northern_territory /\
state queensland /\ state south_australia /\ state new_south_wales /\
state (victoria) /\ state tasmania /\
borders (western_australia) northern_territory /\
borders (western_australia) south_australia /\
borders south_australia northern_territory /\
borders south_australia queensland /\
borders south_australia new_south_wales /\
borders south_australia (victoria) /\
borders northern_territory queensland /\
borders queensland new_south_wales /\ borders new_south_wales (victoria) /\
borders indian (western_australia) /\ borders indian northern_territory /\
borders indian queensland /\ borders southern (western_australia) /\
borders southern south_australia /\ borders southern (victoria) /\
borders southern tasmania /\ borders pacific queensland /\
borders pacific new_south_wales /\ borders pacific (victoria) /\
borders pacific tasmania /\
(!x y z.
   ~state x \/ ~state y \/ ~borders x y \/ ~borders x z \/ ~borders y z \/
   ~ocean z) ==> F`},

{name    = "PUZ023-1",
 comment = "",
 goal    = `
(!x. a_truth (truthteller x) \/ a_truth (liar x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (liar x)) /\
(!x y. ~a_truth (truthteller x) \/ ~a_truth (says x y) \/ a_truth y) /\
(!x y. ~a_truth (liar x) \/ ~a_truth (says x y) \/ ~a_truth y) /\
(!x y. ~a_truth x \/ ~a_truth (says y x) \/ a_truth (truthteller y)) /\
(!x y. a_truth x \/ ~a_truth (says y x) \/ a_truth (liar y)) /\
(!x y z.
   ~people x y z \/ ~a_truth one_truthteller \/ a_truth (truthteller x) \/
   a_truth (truthteller y) \/ a_truth (truthteller z)) /\
(!x y z.
   ~people x y z \/ ~a_truth (truthteller x) \/ ~a_truth (truthteller y) \/
   ~a_truth one_truthteller) /\
(!x y z.
   ~people x y z \/ ~a_truth (truthteller x) \/ ~a_truth (truthteller z) \/
   ~a_truth one_truthteller) /\
(!x y z.
   ~people x y z \/ ~a_truth (truthteller y) \/ ~a_truth (truthteller z) \/
   ~a_truth one_truthteller) /\
(!x y z.
   ~people x y z \/ a_truth one_truthteller \/ ~a_truth (truthteller x) \/
   a_truth (truthteller y) \/ a_truth (truthteller z)) /\
(!x y z.
   ~people x y z \/ a_truth one_truthteller \/ ~a_truth (truthteller y) \/
   a_truth (truthteller x) \/ a_truth (truthteller z)) /\
(!x y z.
   ~people x y z \/ a_truth one_truthteller \/ ~a_truth (truthteller z) \/
   a_truth (truthteller y) \/ a_truth (truthteller x)) /\ people a b c /\
a_truth (says a garbage) /\ a_truth (says b (says a one_truthteller)) /\
a_truth (says c (liar b)) /\
(~a_truth (liar b) \/ ~a_truth (liar c) \/ an_answer b_and_c_liars) /\
(~a_truth (liar b) \/ ~a_truth (truthteller c) \/
 an_answer b_liar_and_c_truthteller) /\
(~a_truth (truthteller b) \/ ~a_truth (liar c) \/
 an_answer b_truthteller_and_c_liar) /\
(~a_truth (truthteller b) \/ ~a_truth (truthteller c) \/
 an_answer b_and_c_truthtellers) ==> (!x. ~an_answer x) ==> F`},

{name    = "PUZ024-1",
 comment = "",
 goal    = `
(!x. a_truth (truthteller x) \/ a_truth (liar x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (liar x)) /\
(!x y. ~a_truth (truthteller x) \/ ~a_truth (says x y) \/ a_truth y) /\
(!x y. ~a_truth (liar x) \/ ~a_truth (says x y) \/ ~a_truth y) /\
(!x y. ~a_truth x \/ ~a_truth (says y x) \/ a_truth (truthteller y)) /\
(!x y. a_truth x \/ ~a_truth (says y x) \/ a_truth (liar y)) /\
(!x y z.
   ~a_truth (says x one_truthteller) \/ ~people x y z \/
   ~a_truth (truthteller x) \/ ~a_truth (truthteller y) \/
   ~a_truth (truthteller z)) /\
(!x y z.
   ~a_truth one_truthteller \/ ~people x y z \/ a_truth (truthteller x) \/
   a_truth (truthteller y) \/ a_truth (truthteller z)) /\
(!x y z.
   ~a_truth one_truthteller \/ ~people x y z \/ ~a_truth (truthteller y) \/
   ~a_truth (truthteller x) \/ ~a_truth (truthteller z)) /\
(!x y z.
   ~a_truth one_truthteller \/ ~people x y z \/ ~a_truth (liar x) \/
   ~a_truth (truthteller y) \/ a_truth (liar z)) /\
(!x y z.
   a_truth one_truthteller \/ ~people x y z \/ ~a_truth (liar x) \/
   ~a_truth (truthteller y) \/ a_truth (truthteller z)) /\
(!x y z.
   a_truth one_truthteller \/ ~people x y z \/ ~a_truth (liar x) \/
   ~a_truth (liar y) \/ a_truth (liar z)) /\
(!x y z.
   ~a_truth (says x all_are_liars) \/ ~people x y z \/
   ~a_truth (truthteller x)) /\
(!x y z.
   a_truth all_are_liars \/ ~people x y z \/ a_truth (truthteller x) \/
   a_truth (truthteller y) \/ a_truth (truthteller z)) /\ people b c a /\
people a c b /\ people c b a /\ a_truth (says a all_are_liars) /\
a_truth (says b one_truthteller) ==> (!x. ~a_truth (truthteller x)) ==> F`},

{name    = "PUZ025-1",
 comment = "",
 goal    = `
(!x. a_truth (truthteller x) \/ a_truth (liar x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (liar x)) /\
(!x y. ~a_truth (truthteller x) \/ ~a_truth (says x y) \/ a_truth y) /\
(!x y. ~a_truth (liar x) \/ ~a_truth (says x y) \/ ~a_truth y) /\
(!x y. ~a_truth x \/ ~a_truth (says y x) \/ a_truth (truthteller y)) /\
(!x y. a_truth x \/ ~a_truth (says y x) \/ a_truth (liar y)) /\
(!x y z.
   ~people x y z \/ ~a_truth (liar x) \/ ~a_truth (liar y) \/
   a_truth (equal_type x y)) /\
(!x y z.
   ~people x y z \/ ~a_truth (truthteller x) \/ ~a_truth (truthteller y) \/
   a_truth (equal_type x y)) /\
(!x y.
   ~a_truth (equal_type x y) \/ ~a_truth (truthteller x) \/
   a_truth (truthteller y)) /\
(!x y.
   ~a_truth (equal_type x y) \/ ~a_truth (liar x) \/ a_truth (liar y)) /\
(!x y.
   ~a_truth (truthteller x) \/ a_truth (equal_type x y) \/
   a_truth (liar y)) /\
(!x y.
   ~a_truth (liar x) \/ a_truth (equal_type x y) \/
   a_truth (truthteller y)) /\
(!x y. ~a_truth (equal_type x y) \/ a_truth (equal_type y x)) /\
(!x y.
   ~ask_1_if_2 x y \/ ~a_truth (truthteller x) \/ ~a_truth y \/
   answer (yes)) /\
(!x y.
   ~ask_1_if_2 x y \/ ~a_truth (truthteller x) \/ a_truth y \/
   answer no) /\
(!x y. ~ask_1_if_2 x y \/ ~a_truth (liar x) \/ ~a_truth y \/ answer no) /\
(!x y.
   ~ask_1_if_2 x y \/ ~a_truth (liar x) \/ a_truth y \/ answer (yes)) /\
people b c a /\ people a b a /\ people a c b /\ people c b a /\
a_truth (says a (equal_type b c)) /\ ask_1_if_2 c (equal_type a b) ==>
(!x. ~answer x) ==> F`},

{name    = "PUZ026-1",
 comment = "",
 goal    = `
(!x. a_truth (truthteller x) \/ a_truth (liar x) \/ a_truth (normal x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (normal x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (liar x)) /\
(!x. ~a_truth (liar x) \/ ~a_truth (normal x)) /\
(!x y. ~a_truth (truthteller x) \/ ~a_truth (says x y) \/ a_truth y) /\
(!x y. ~a_truth (liar x) \/ ~a_truth (says x y) \/ ~a_truth y) /\
(!x y.
   ~a_truth x \/ ~a_truth (says y x) \/ a_truth (truthteller y) \/
   a_truth (normal y)) /\
(!x y.
   a_truth x \/ ~a_truth (says y x) \/ a_truth (liar y) \/
   a_truth (normal y)) /\
(!x. ~a_truth (not_normal x) \/ ~a_truth (normal x)) /\
(!x. a_truth (not_normal x) \/ a_truth (normal x)) /\
(!x y z.
   ~people x y z \/ ~a_truth (truthteller x) \/
   ~a_truth (truthteller y)) /\
(!x y z.
   ~people x y z \/ ~a_truth (truthteller x) \/
   ~a_truth (truthteller z)) /\
(!x y z. ~people x y z \/ ~a_truth (liar x) \/ ~a_truth (liar y)) /\
(!x y z. ~people x y z \/ ~a_truth (liar x) \/ ~a_truth (liar z)) /\
(!x y z. ~people x y z \/ ~a_truth (normal x) \/ ~a_truth (normal y)) /\
(!x y z. ~people x y z \/ ~a_truth (normal x) \/ ~a_truth (normal z)) /\
people a b c /\ people b c a /\ people c b a /\
a_truth (says a (normal a)) /\ a_truth (says b (normal a)) /\
a_truth (says c (not_normal c)) ==>
(!x y z.
   ~a_truth (liar x) \/ ~a_truth (normal y) \/
   ~a_truth (truthteller z)) ==> F`},

{name    = "PUZ027-1",
 comment = "",
 goal    = `
(!x. a_truth (truthteller x) \/ a_truth (liar x) \/ a_truth (normal x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (normal x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (liar x)) /\
(!x. ~a_truth (liar x) \/ ~a_truth (normal x)) /\
(!x y. ~a_truth (truthteller x) \/ ~a_truth (says x y) \/ a_truth y) /\
(!x y. ~a_truth (liar x) \/ ~a_truth (says x y) \/ ~a_truth y) /\
(!x y.
   ~a_truth x \/ ~a_truth (says y x) \/ a_truth (truthteller y) \/
   a_truth (normal y)) /\
(!x y.
   a_truth x \/ ~a_truth (says y x) \/ a_truth (liar y) \/
   a_truth (normal y)) /\ (!x. a_truth (not_lower x x)) /\
(!x y. ~a_truth (not_lower x y) \/ ~a_truth (lower x y)) /\
(!x y. a_truth (not_lower x y) \/ a_truth (lower x y)) /\
(!x y.
   ~a_truth (lower x y) \/ ~a_truth (liar x) \/ a_truth (normal y) \/
   a_truth (truthteller y)) /\
(!x y.
   ~a_truth (lower x y) \/ ~a_truth (normal x) \/
   a_truth (truthteller y)) /\
(!x y. ~a_truth (lower x y) \/ ~a_truth (truthteller x)) /\
(!x y.
   ~a_truth (lower x y) \/ ~a_truth (truthteller y) \/
   a_truth (normal x) \/ a_truth (liar x)) /\
(!x y. ~a_truth (lower x y) \/ ~a_truth (normal y) \/ a_truth (liar x)) /\
(!x y. ~a_truth (lower x y) \/ ~a_truth (liar y)) /\
(!x y.
   ~a_truth (not_lower x y) \/ ~a_truth (truthteller x) \/
   a_truth (truthteller y) \/ a_truth (lower y x)) /\
(!x y.
   ~a_truth (not_lower x y) \/ ~a_truth (liar x) \/ a_truth (liar y) \/
   a_truth (lower y x)) /\
(!x y.
   ~a_truth (not_lower x y) \/ ~a_truth (normal x) \/ a_truth (normal y) \/
   a_truth (lower y x)) /\ a_truth (says a (lower a b)) /\
a_truth (says b (not_lower a b)) /\
(~a_truth (truthteller a) \/ ~a_truth (truthteller b) \/
 answer a_and_b_truthteller) /\
(~a_truth (truthteller a) \/ ~a_truth (normal b) \/
 answer a_truthteller_b_normal) /\
(~a_truth (truthteller a) \/ ~a_truth (liar b) \/
 answer a_truthteller_b_liar) /\
(~a_truth (normal a) \/ ~a_truth (truthteller b) \/
 answer a_normal_b_truthteller) /\
(~a_truth (normal a) \/ ~a_truth (normal b) \/ answer a_and_b_normal) /\
(~a_truth (normal a) \/ ~a_truth (liar b) \/ answer a_normal_b_liar) /\
(~a_truth (liar a) \/ ~a_truth (truthteller b) \/
 answer a_liar_b_truthteller) /\
(~a_truth (liar a) \/ ~a_truth (normal b) \/ answer a_liar_b_normal) /\
(~a_truth (liar a) \/ ~a_truth (liar b) \/ answer a_and_b_liar) ==>
(!x. ~answer x) ==> F`},

{name    = "PUZ028-5",
 comment = "",
 goal    = `
person one /\ person two /\ person three /\ person four /\ person five /\
person six /\ after one two /\ after two three /\ after three four /\
after four five /\ after five six /\
(!x y z. after x y \/ ~after x z \/ ~after z y) /\
(!x y.
   familiar x y \/ not_familiar x y \/ ~person x \/ ~person y \/
   ~after x y) ==>
(!x y z. ~familiar x y \/ ~familiar y z \/ ~familiar x z) /\
(!x y z. ~not_familiar x y \/ ~not_familiar y z \/ ~not_familiar x z) ==> F`},

{name    = "PUZ028-6",
 comment = "",
 goal    = `
person 1 /\ person 2 /\ person 3 /\ person 4 /\ person 5 /\ person 6 /\
not_equal 1 2 /\ not_equal 1 3 /\ not_equal 1 4 /\ not_equal 1 5 /\
not_equal 1 6 /\ not_equal 2 1 /\ not_equal 2 3 /\ not_equal 2 4 /\
not_equal 2 5 /\ not_equal 2 6 /\ not_equal 3 1 /\ not_equal 3 2 /\
not_equal 3 4 /\ not_equal 3 5 /\ not_equal 3 6 /\ not_equal 4 1 /\
not_equal 4 2 /\ not_equal 4 3 /\ not_equal 4 5 /\ not_equal 4 6 /\
not_equal 5 1 /\ not_equal 5 2 /\ not_equal 5 3 /\ not_equal 5 4 /\
not_equal 5 6 /\ not_equal 6 1 /\ not_equal 6 2 /\ not_equal 6 3 /\
not_equal 6 4 /\ not_equal 6 5 /\
(!x y.
   familiar x y \/ not_familiar x y \/ ~person x \/ ~person y \/
   ~not_equal x y) /\ (!x y. ~familiar x y \/ familiar y x) /\
(!x y. ~not_familiar x y \/ not_familiar y x) ==>
(!x y z. ~familiar x y \/ ~familiar y z \/ ~familiar z x) /\
(!x y z. ~not_familiar x y \/ ~not_familiar y z \/ ~not_familiar z x) ==> F`},

{name    = "PUZ029-1",
 comment = "",
 goal    = `
(!x. dances_on_tightropes x \/ eats_pennybuns x \/ old x) /\
(!x. ~pig x \/ ~liable_to_giddiness x \/ treated_with_respect x) /\
(!x. ~(wise) x \/ ~balloonist x \/ has_umbrella x) /\
(!x.
   ~looks_ridiculous x \/ ~eats_pennybuns x \/ ~eats_lunch_in_public x) /\
(!x. ~balloonist x \/ ~(young) x \/ liable_to_giddiness x) /\
(!x.
   ~fat x \/ ~looks_ridiculous x \/ dances_on_tightropes x \/
   eats_lunch_in_public x) /\
(!x. ~liable_to_giddiness x \/ ~(wise) x \/ ~dances_on_tightropes x) /\
(!x. ~pig x \/ ~has_umbrella x \/ looks_ridiculous x) /\
(!x. dances_on_tightropes x \/ ~treated_with_respect x \/ fat x) /\
(!x. (young) x \/ old x) /\ (!x. ~(young) x \/ ~old x) /\ (wise) piggy /\
(young) piggy /\ pig piggy ==> balloonist piggy ==> F`},

{name    = "PUZ030-1",
 comment = "",
 goal    = `
(!x. ~both x \/ salt x) /\ (!x. ~both x \/ mustard x) /\
(!x. ~salt x \/ ~mustard x \/ both x) /\
(!x. ~oneof x \/ salt x \/ mustard x) /\ (!x. ~oneof x \/ ~both x) /\
(!x. ~oneof x \/ ~neither x) /\ (!x. both x \/ neither x \/ oneof x) /\
(!x. ~oneof x \/ ~salt x \/ ~mustard x) /\ (!x. ~both x \/ ~neither x) /\
(!x. ~neither x \/ ~salt x) /\ (!x. ~neither x \/ ~mustard x) /\
(!x. salt x \/ mustard x \/ neither x) /\
(~salt barry \/ oneof cole \/ oneof lang) /\ (~oneof cole \/ salt barry) /\
(~oneof lang \/ salt barry) /\
(~mustard barry \/ neither dix \/ both mill) /\
(~neither dix \/ mustard barry) /\ (~both mill \/ mustard barry) /\
(~salt cole \/ oneof barry \/ neither mill) /\
(~oneof barry \/ salt cole) /\ (~neither mill \/ salt cole) /\
(~mustard cole \/ both dix \/ both lang) /\ (~both dix \/ mustard cole) /\
(~both lang \/ mustard cole) /\
(~salt dix \/ neither barry \/ both cole) /\
(~neither barry \/ salt dix) /\ (~both cole \/ salt dix) /\
(~mustard dix \/ neither lang \/ neither mill) /\
(~neither lang \/ mustard dix) /\ (~neither mill \/ mustard dix) /\
(~salt lang \/ oneof barry \/ oneof dix) /\ (~oneof barry \/ salt lang) /\
(~oneof dix \/ salt lang) /\
(~mustard lang \/ neither cole \/ neither mill) /\
(~neither cole \/ mustard lang) /\ (~neither mill \/ mustard lang) /\
(~salt mill \/ both barry \/ both lang) /\ (~both barry \/ salt mill) /\
(~both lang \/ mustard mill) /\
(~mustard mill \/ oneof cole \/ oneof dix) /\
(~oneof cole \/ mustard mill) /\ (~oneof dix \/ mustard mill) ==>
~neither cole \/ ~neither dix \/ ~both barry \/ ~oneof lang \/
~salt mill \/ ~mustard lang \/ ~oneof mill ==> F`},

{name    = "PUZ030-2",
 comment = "",
 goal    = `
(~salt_mill \/ mustard_barry \/ mustard_lang) /\
(~salt_mill \/ mustard_barry \/ salt_lang) /\
(~salt_mill \/ salt_barry \/ mustard_lang) /\
(~salt_mill \/ salt_barry \/ salt_lang) /\
(~mustard_lang \/ ~mustard_cole \/ ~mustard_mill) /\
(~mustard_lang \/ ~mustard_cole \/ ~salt_mill) /\
(~mustard_lang \/ ~salt_cole \/ ~mustard_mill) /\
(~mustard_lang \/ ~salt_cole \/ ~salt_mill) /\
(~mustard_dix \/ ~mustard_lang \/ ~mustard_mill) /\
(~mustard_dix \/ ~mustard_lang \/ ~salt_mill) /\
(~mustard_dix \/ ~salt_lang \/ ~mustard_mill) /\
(~mustard_dix \/ ~salt_lang \/ ~salt_mill) /\
(~salt_dix \/ ~mustard_barry \/ mustard_cole) /\
(~salt_dix \/ ~mustard_barry \/ salt_cole) /\
(~salt_dix \/ ~salt_barry \/ mustard_cole) /\
(~salt_dix \/ ~salt_barry \/ salt_cole) /\
(~mustard_cole \/ mustard_dix \/ mustard_lang) /\
(~mustard_cole \/ mustard_dix \/ salt_lang) /\
(~mustard_cole \/ salt_dix \/ mustard_lang) /\
(~mustard_cole \/ salt_dix \/ salt_lang) /\
(~mustard_barry \/ ~mustard_dix \/ mustard_mill) /\
(~mustard_barry \/ ~mustard_dix \/ salt_mill) /\
(~mustard_barry \/ ~salt_dix \/ mustard_mill) /\
(~mustard_barry \/ ~salt_dix \/ salt_mill) /\
(salt_dix \/ ~mustard_dix \/ mustard_mill) /\
(~salt_dix \/ mustard_dix \/ mustard_mill) /\
(salt_cole \/ ~mustard_cole \/ mustard_mill) /\
(~salt_cole \/ mustard_cole \/ mustard_mill) /\
(~salt_lang \/ ~mustard_lang \/ salt_mill) /\
(~salt_barry \/ ~mustard_barry \/ salt_mill) /\
(salt_dix \/ ~mustard_dix \/ salt_lang) /\
(~salt_dix \/ mustard_dix \/ salt_lang) /\
(salt_barry \/ ~mustard_barry \/ salt_lang) /\
(~salt_barry \/ mustard_barry \/ salt_lang) /\
(~salt_cole \/ ~mustard_cole \/ salt_dix) /\
(~salt_lang \/ ~mustard_lang \/ mustard_cole) /\
(~salt_dix \/ ~mustard_dix \/ mustard_cole) /\
(salt_barry \/ ~mustard_barry \/ salt_cole) /\
(~salt_barry \/ mustard_barry \/ salt_cole) /\
(~salt_mill \/ ~mustard_mill \/ mustard_barry) /\
(salt_lang \/ ~mustard_lang \/ salt_barry) /\
(~salt_lang \/ mustard_lang \/ salt_barry) /\
(salt_cole \/ ~mustard_cole \/ salt_barry) /\
(~salt_cole \/ mustard_cole \/ salt_barry) /\
(~salt_cole \/ ~mustard_barry \/ ~salt_barry \/ ~mustard_mill) /\
(~salt_cole \/ ~mustard_barry \/ ~salt_barry \/ ~salt_mill) /\
(~salt_cole \/ salt_barry \/ mustard_barry \/ ~mustard_mill) /\
(~salt_cole \/ salt_barry \/ mustard_barry \/ ~salt_mill) /\
(~mustard_mill \/ ~mustard_cole \/ ~salt_cole \/ ~mustard_dix \/
 ~salt_dix) /\
(~mustard_mill \/ salt_cole \/ mustard_cole \/ salt_dix \/ mustard_dix) /\
(~salt_lang \/ ~mustard_barry \/ ~salt_barry \/ ~mustard_dix \/
 ~salt_dix) /\
(~salt_lang \/ ~mustard_barry \/ ~salt_barry \/ salt_dix \/ mustard_dix) /\
(~salt_lang \/ salt_barry \/ mustard_barry \/ ~mustard_dix \/ ~salt_dix) /\
(~salt_barry \/ ~mustard_cole \/ ~salt_cole \/ ~mustard_lang \/
 ~salt_lang) /\
(~salt_barry \/ ~mustard_cole \/ ~salt_cole \/ salt_lang \/
 mustard_lang) /\ (salt_mill \/ mustard_mill \/ mustard_lang) /\
(salt_cole \/ mustard_cole \/ mustard_lang) /\
(salt_mill \/ mustard_mill \/ mustard_dix) /\
(salt_lang \/ mustard_lang \/ mustard_dix) /\
(salt_barry \/ mustard_barry \/ salt_dix) /\
(salt_mill \/ mustard_mill \/ salt_cole) /\
(salt_dix \/ mustard_dix \/ mustard_barry) ==>
salt_lang \/ ~mustard_barry \/ ~salt_barry \/ ~salt_mill \/
~mustard_lang \/ salt_cole \/ mustard_cole \/ salt_dix \/ mustard_dix \/
mustard_mill ==> F`},

{name    = "PUZ031-1",
 comment = "",
 goal    = `
(!x. animal x \/ ~(wolf) x) /\ (!x. animal x \/ ~fox x) /\
(!x. animal x \/ ~bird x) /\ (!x. animal x \/ ~caterpillar x) /\
(!x. animal x \/ ~snail x) /\ (wolf) a_wolf /\ fox a_fox /\ bird a_bird /\
caterpillar a_caterpillar /\ snail a_snail /\ grain a_grain /\
(!x. plant x \/ ~grain x) /\
(!x y z v.
   eats x y \/ eats x z \/ ~animal x \/ ~plant y \/ ~animal z \/
   ~plant v \/ ~much_smaller z x \/ ~eats z v) /\
(!x y. much_smaller x y \/ ~caterpillar x \/ ~bird y) /\
(!x y. much_smaller x y \/ ~snail x \/ ~bird y) /\
(!x y. much_smaller x y \/ ~bird x \/ ~fox y) /\
(!x y. much_smaller x y \/ ~fox x \/ ~(wolf) y) /\
(!x y. ~(wolf) x \/ ~fox y \/ ~eats x y) /\
(!x y. ~(wolf) x \/ ~grain y \/ ~eats x y) /\
(!x y. eats x y \/ ~bird x \/ ~caterpillar y) /\
(!x y. ~bird x \/ ~snail y \/ ~eats x y) /\
(!x. plant (caterpillar_food_of x) \/ ~caterpillar x) /\
(!x. eats x (caterpillar_food_of x) \/ ~caterpillar x) /\
(!x. plant (snail_food_of x) \/ ~snail x) /\
(!x. eats x (snail_food_of x) \/ ~snail x) ==>
(!x y z. ~animal x \/ ~animal y \/ ~grain z \/ ~eats x y \/ ~eats y z) ==>
F`},

{name    = "PUZ032-1",
 comment = "",
 goal    = `
(!x. a_truth (truthteller x) \/ a_truth (liar x)) /\
(!x. ~a_truth (truthteller x) \/ ~a_truth (liar x)) /\
(!x y. ~a_truth (truthteller x) \/ ~a_truth (says x y) \/ a_truth y) /\
(!x y. ~a_truth (liar x) \/ ~a_truth (says x y) \/ ~a_truth y) /\
(!x y. ~a_truth x \/ ~a_truth (says y x) \/ a_truth (truthteller y)) /\
(!x y. a_truth x \/ ~a_truth (says y x) \/ a_truth (liar y)) /\
a_truth (says a mumble) /\ a_truth (says b (says a (liar a))) /\
a_truth (says c (liar b)) ==> ~a_truth (truthteller c) ==> F`},

{name    = "PUZ033-1",
 comment = "",
 goal    = `
(~(wind_in_east) \/ sunshine) /\
(~cold \/ ~foggy \/ neighbor_practices_flute) /\
(~fire_smokes \/ door_is_open) /\
(~cold \/ ~i_feel_rheumatic \/ fire_is_lit) /\
(~(wind_in_east) \/ ~(wind_in_gusts) \/ fire_smokes) /\
(~door_is_open \/ ~headache) /\
(~sunshine \/ cold \/ ~foggy \/ (window_is_shut)) /\
((wind_in_gusts) \/ ~fire_is_lit \/ door_is_open \/ ~i_feel_rheumatic) /\
(~sunshine \/ foggy) /\ (~neighbor_practices_flute \/ ~door_is_open) /\
(~foggy \/ ~(wind_in_east) \/ i_feel_rheumatic) /\ (wind_in_east) ==>
~(window_is_shut) ==> F`},

{name    = "PUZ034-1.004",
 comment = "",
 goal    = `
(!x y z v.
   range x y (cons x z) \/ ~less x y \/ ~sum x (s 0) v \/ ~range v y z) /\
(!x. range x x (cons x empty_list)) /\ (!x. less 0 (s x)) /\
(!x y. less (s x) (s y) \/ ~less x y) /\ (!x. sum x 0 x) /\
(!x y z. ~sum x y z \/ sum x (s y) (s z)) /\
(!x y. select x (cons x y) y) /\
(!x y z v. select x (cons y z) (cons y v) \/ ~select x z v) /\
(!x. ~same (s x) 0) /\ (!x. ~same 0 (s x)) /\
(!x y. ~same (s x) (s y) \/ same x y) /\
(!x y. diagonal_attack x (s 0) y \/ ~attack x y) /\
(!x y z v w x' y'.
   ~diagonal_attack x y (cons z v) \/ ~sum w y z \/ same w x \/
   ~sum z y x' \/ same x' x \/ ~sum y (s 0) y' \/
   diagonal_attack x y' v) /\ (!x y. ~diagonal_attack x y empty_list) /\
(!x y z v w.
   do_queens x y z \/ ~select v x w \/ attack v y \/
   ~do_queens w (cons v y) z) /\ (!x. do_queens empty_list x x) /\
(!x y z v w.
   queens x y \/ ~sum x (s 0) z \/ ~sum x x v \/ ~range z v w \/
   ~do_queens w empty_list y) ==> (!x. ~queens (s (s (s (s 0)))) x) ==> F`},

{name    = "PUZ035-1",
 comment = "",
 goal    = `
(!x. ~person x \/ isa x knight \/ isa x knave) /\
(!x. ~isa x knight \/ ~isa x knave) /\
(!x. ~isa x knight \/ tell_the_truth x) /\ (!x. ~isa x knave \/ lies x) /\
(!x. ~tell_the_truth x \/ ~lies x) /\
(isa asked knight \/ isa other knight \/ ~response (yes) \/
 ~tell_the_truth asked) /\
(isa asked knight \/ isa other knight \/ ~response no \/ ~lies asked) /\
(!x. ~response (yes) \/ ~lies asked \/ ~isa x knight) /\
(!x. ~response no \/ ~tell_the_truth asked \/ ~isa x knight) /\
(!x. response (yes) \/ ~tell_the_truth asked \/ ~isa x knight) /\
(response no \/ isa asked knight \/ isa other knight \/
 ~tell_the_truth asked) /\ (response (yes) \/ response no) /\
person asked /\ person other ==>
(!x y z. ~response x \/ ~isa asked y \/ ~isa other z) ==> F`},

{name    = "PUZ035-2",
 comment = "",
 goal    = `
(!x. ~person x \/ isa x knight \/ isa x knave) /\
(!x. ~isa x knight \/ ~isa x knave) /\
(!x. ~isa x knight \/ tell_the_truth x) /\ (!x. ~isa x knave \/ lies x) /\
(!x. ~tell_the_truth x \/ ~lies x) /\
(!x. ~person x \/ tell_the_truth x \/ lies x) /\
(isa asked knight \/ isa other knight \/ ~response (yes) \/
 ~tell_the_truth asked) /\
(isa asked knight \/ isa other knight \/ ~response no \/ ~lies asked) /\
(!x. ~response (yes) \/ ~lies asked \/ ~isa x knight) /\
(!x. ~response no \/ ~tell_the_truth asked \/ ~isa x knight) /\
(!x. response (yes) \/ ~tell_the_truth asked \/ ~isa x knight) /\
(response no \/ isa asked knight \/ isa other knight \/
 ~tell_the_truth asked) /\ (response (yes) \/ response no) /\
person asked /\ person other ==>
(!x y z. ~response x \/ ~isa asked y \/ ~isa other z) ==> F`},

{name    = "PUZ035-3",
 comment = "",
 goal    = `
(!x. ~person x \/ true (isa x knight) \/ true (isa x knave)) /\
(!x. ~true (isa x knight) \/ ~true (isa x knave)) /\
(!x y. true x \/ ~says y x \/ ~true (isa y knight)) /\
(!x y. true (isa x knight) \/ ~says x y \/ ~true y) /\
(!x y. true (not x) \/ ~says y x \/ ~true (isa y knave)) /\
(!x y. true (isa x knave) \/ ~says x y \/ ~true (not y)) /\
(says asked (or (isa asked knight) (isa other knight)) \/
 says asked (not (or (isa asked knight) (isa other knight)))) /\
(!x y. true x \/ true (not x) \/ ~says y x) /\
(!x y. true x \/ true (not x) \/ ~says y (not x)) /\
(!x. ~true x \/ ~true (not x)) /\
(!x y. true x \/ true y \/ ~true (or x y)) /\
(!x y. ~true x \/ ~true (not (or x y))) /\
(!x y. ~true x \/ ~true (not (or y x))) /\ person asked /\ person other ==>
(!x y z. ~true (isa asked x) \/ ~true (isa other y) \/ ~says asked z) ==> F`},

{name    = "PUZ035-4",
 comment = "",
 goal    = `
(!x. ~person x \/ true (isa x knight) \/ true (isa x knave)) /\
(!x. ~true (isa x knight) \/ ~true (isa x knave)) /\
(!x y. true x \/ ~says y x \/ ~true (isa y knight)) /\
(!x y. true (isa x knight) \/ ~says x y \/ ~true y) /\
(says asked (or (isa asked knight) (isa other knight)) \/
 says asked (not (or (isa asked knight) (isa other knight)))) /\
(!x y. true x \/ true (not x) \/ ~says y x) /\
(!x y. true x \/ true (not x) \/ ~says y (not x)) /\
(!x. ~true x \/ ~true (not x)) /\
(!x y. true x \/ true y \/ ~true (or x y)) /\
(!x y. ~true x \/ ~true (not (or x y))) /\
(!x y. ~true x \/ ~true (not (or y x))) /\ person asked /\ person other ==>
(!x y z. ~true (isa asked x) \/ ~true (isa other y) \/ ~says asked z) ==> F`},

{name    = "PUZ035-5",
 comment = "",
 goal    = `
(!x. true (isa x knight) \/ true (isa x knave)) /\
(!x. ~true (isa x knight) \/ ~true (isa x knave)) /\
(!x y. true x \/ ~true (isa y knight) \/ ~says y x) /\
(!x y. true (isa x knight) \/ ~true y \/ ~says x y) /\
(!x y. true x \/ true y \/ ~true (or x y)) /\
(!x y. true (or x y) \/ ~true x) /\ (!x y. true (or x y) \/ ~true y) /\
says asked (or (isa asked knight) (isa other knight)) ==>
(!x y. ~true (isa asked x) \/ ~true (isa other y)) ==> F`},

{name    = "PUZ035-6",
 comment = "",
 goal    = `
(!x. true (isa x knight) \/ true (isa x knave)) /\
(!x. ~true (isa x knight) \/ ~true (isa x knave)) /\
(!x y. true x \/ ~true (isa y knight) \/ ~says y x) /\
(!x y. true (isa x knight) \/ ~true y \/ ~says x y) /\
(!x y. true x \/ true y \/ ~true (or x y)) /\
(!x y. true (or x y) \/ ~true x) /\ (!x y. true (or x y) \/ ~true y) /\
(!x. true x \/ true (not x)) /\ (!x. ~true x \/ ~true (not x)) /\
says asked (not (or (isa asked knight) (isa other knight))) ==>
(!x y. ~true (isa asked x) \/ ~true (isa other y)) ==> F`},

{name    = "PUZ035-7",
 comment = "",
 goal    = `
(!x. true (isa x knight) \/ true (isa x knave)) /\
(!x. ~true (isa x knight) \/ ~true (isa x knave)) /\
(!x y. true x \/ ~true (isa y knight) \/ ~reply y x (yes)) /\
(!x y. ~true x \/ true (isa y knight) \/ ~reply y x (yes)) /\
(!x y. ~true x \/ ~true (isa y knight) \/ reply y x (yes)) /\
(!x y. true x \/ true (isa y knight) \/ reply y x (yes)) /\
(!x y. reply x y (yes) \/ reply x y no) /\
(!x y. ~reply x y (yes) \/ ~reply x y no) /\
(!x. true x \/ true (not x)) /\ (!x. ~true x \/ ~true (not x)) /\
(!x y. true x \/ true y \/ ~true (or x y)) /\
(!x y. true (or x y) \/ ~true x) /\ (!x y. true (or x y) \/ ~true y) ==>
(!x y z.
   ~reply asked (or (isa asked knight) (isa other knight)) x \/
   ~true (isa asked y) \/ ~true (isa other z)) ==> F`},

{name    = "PUZ036-1.005",
 comment = "",
 goal    = `
state p_5 p_4 p_3 p_2 p_1 p_6 p_7 p_8 p_9 p_10 p_11 p_12 p_13 p_14 p_15
p_16 p_17 p_18 p_19 p_20 /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 \/
   state y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 \/
   state w3 x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 \/
   state v z y x w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3) ==>
~state p_1 p_2 p_3 p_4 p_5 p_6 p_7 p_8 p_9 p_10 p_11 p_12 p_13 p_14 p_15
 p_16 p_17 p_18 p_19 p_20 ==> F`},

{name    = "PUZ037-1",
 comment = "",
 goal    = `
state b b b b b b b b b r r r g g g (o) (o) (o) (y) (y) (y) g g g (o) (o)
(o) (y) (y) (y) r r r r r r g g g (o) (o) (o) (y) (y) (y) (w) (w) (w) (w)
(w) (w) (w) (w) (w) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state y1 v x z1 w y v1 x1 z z2 v2 w2 x3 y3 z3 v3 w3 x4 w1 x2 y2 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 w4 x5 y5
   z5 v5 w5 x6 y6 z6 y4 z4 v4 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 y7 z7 v7 w7 x8 y8 z8 v8 w8 v6 w6 x7 z9 x10
   v10 y9 w9 z10 x9 v9 y10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 x3 z5 w7 w1 x2 v1 w2 y5 v7 z9 y3 z3 v3 w3 x4 y4 z4 z1
   v2 x5 z7 y9 v5 w5 x6 y6 z6 v6 w6 y1 z2 w4 y7 x9 x8 y8 z8 v8 w8 y2 v4 x7
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z y3 v5 x8 y1 z1 v1 w1 x1 y2 z2 v2 w2 x3 x10 z3 v3 w3 x4 y4 w
   v4 w4 x5 y5 z5 w9 w5 x6 y6 z6 v6 v x7 y7 z7 v7 w7 v9 y8 z8 v8 w8 x9 y9
   z9 x2 z4 w6 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z3 w5 y8 v w x1 y1 z1 v1 z x2 y2 z2 v2 w2 x3 y3 v10 z8 x6 v3 y z4
   v4 w4 x5 y5 z5 v5 z10 v8 y6 w3 x w6 x7 y7 z7 v7 w7 x8 y10 w8 z6 x4 x9 y9
   z9 v9 w9 x10 w1 y4 v6) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z2 y z w4 w x1 y7 z1 v1 y2 v4 x7 x9 v2 w2 x3 y3 z3 v3 w3 y1 x2 z4
   w6 v9 x5 y5 z5 v5 w5 x6 y6 v w1 y4 v6 y10 z7 v7 w7 x8 y8 z8 v8 x w8 y9
   z9 z6 w9 x10 x4 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x v2 z v x5 x1 y1 z7 v1 w1 x2 y2 z2 y9 w2 x3 y3 z3 v3 z1 x4 y4 z4
   v4 w4 w9 y5 z5 v5 w5 x6 w z6 v6 w6 x7 y7 z10 v7 w7 x8 y8 z8 y w8 x9 v8
   z9 v9 y6 x10 y10 w3 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y w2 v w y5 y1 z1 v7 w1 x2 y2 z2 v2 z9 w7 z5 x3 v1 w3 x4 y4 z4
   v4 w4 x5 x10 x8 v5 y3 x1 y6 z6 v6 w6 x7 y7 z7 v10 y8 w5 z3 z v8 w8 x9 y9
   z8 v9 w9 x6 y10 z10 v3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z x1 v1 y w z1 x v y1 v3 w3 x4 w1 x2 y2 z2 v2 w2 x3 y3 z3 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 x6 y6 z6
   y4 z4 v4 w4 x5 y5 z5 v5 w5 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 z8 v8 w8 v6 w6 x7 y7 z7 v7 w7 x8 y8 y10 v9 x9
   z10 w9 y9 v10 x10 z9) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 x7 v4 y2 w1 x2 x9 y7 w4 z2 y1 y3 z3 v3 w3 x4 y4 z4 y9
   z7 x5 v2 z1 v5 w5 x6 y6 z6 v6 w6 z9 v7 y5 w2 v1 x8 y8 z8 v8 w8 w7 z5 x3
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z w6 z4 x2 y1 z1 v1 w1 v9 y2 z2 v2 w2 x3 v z3 v3 w3 x4 y4 w9
   v4 w4 x5 y5 z5 w w5 x6 y6 z6 v6 x10 x7 y7 z7 v7 w7 x1 y8 z8 v8 w8 x9 y9
   z9 x8 v5 y3 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state v6 y4 w1 v w x1 y1 z1 v1 y10 x2 y2 z2 v2 w2 x3 y3 x x4 z6 w8 z10
   z4 v4 w4 x5 y5 z5 v5 y w3 y6 v8 v10 w6 x7 y7 z7 v7 w7 x8 z v3 x6 z8 x9
   y9 z9 v9 w9 x10 y8 w5 z3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state w8 y z z6 w x1 x4 z1 v1 v6 y4 w1 x v2 w2 x3 y3 z3 v3 w3 y10 w6 z4
   x2 v x5 y5 z5 v5 w5 x6 y6 v9 x7 v4 y2 y1 z7 v7 w7 x8 y8 z8 v8 x9 z2 y9
   z9 w4 w9 x10 y7 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x v8 z v y6 x1 y1 w3 v1 w1 x2 y2 z2 y w2 x3 y3 z3 v3 z10 x4 y4 z4
   v4 w4 w y5 z5 v5 w5 x6 w9 z6 v6 w6 x7 y7 z1 v7 w7 x8 y8 z8 y9 w8 x9 v2
   z9 v9 x5 x10 y10 z7 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z8 v w x6 y1 z1 v3 w1 x2 y2 z2 v2 z z3 w5 y8 v10 w3 x4 y4 z4
   v4 w4 x5 x1 y3 v5 x8 x10 y6 z6 v6 w6 x7 y7 z7 v1 x3 z5 w7 z9 v8 w8 x9 y9
   w2 v9 w9 y5 y10 z10 v7) ==>
~state b b b b b b b b b r r r g g g (o) (o) (o) (y) (y) (y) r r r g g g
 (o) (o) (o) (y) (y) (y) r r r g g g (o) (o) (o) (y) (y) (y) (w) (w) (w)
 (w) (w) (w) (w) (w) (w) ==> F`},

{name    = "PUZ037-2",
 comment = "",
 goal    = `
state (y) b (y) (y) b (y) (y) b (y) r r r b g b (o) (o) (o) (w) (y) (w) (w)
(y) (w) r r r b g b (o) (o) (o) r r r b g b (o) (o) (o) (w) (y) (w) g (w) g
g (w) g g (w) g /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state y1 v x z1 w y v1 x1 z z2 v2 w2 x3 y3 z3 v3 w3 x4 w1 x2 y2 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 w4 x5 y5
   z5 v5 w5 x6 y6 z6 y4 z4 v4 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 y7 z7 v7 w7 x8 y8 z8 v8 w8 v6 w6 x7 z9 x10
   v10 y9 w9 z10 x9 v9 y10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 x3 z5 w7 w1 x2 v1 w2 y5 v7 z9 y3 z3 v3 w3 x4 y4 z4 z1
   v2 x5 z7 y9 v5 w5 x6 y6 z6 v6 w6 y1 z2 w4 y7 x9 x8 y8 z8 v8 w8 y2 v4 x7
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z y3 v5 x8 y1 z1 v1 w1 x1 y2 z2 v2 w2 x3 x10 z3 v3 w3 x4 y4 w
   v4 w4 x5 y5 z5 w9 w5 x6 y6 z6 v6 v x7 y7 z7 v7 w7 v9 y8 z8 v8 w8 x9 y9
   z9 x2 z4 w6 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z3 w5 y8 v w x1 y1 z1 v1 z x2 y2 z2 v2 w2 x3 y3 v10 z8 x6 v3 y z4
   v4 w4 x5 y5 z5 v5 z10 v8 y6 w3 x w6 x7 y7 z7 v7 w7 x8 y10 w8 z6 x4 x9 y9
   z9 v9 w9 x10 w1 y4 v6) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z2 y z w4 w x1 y7 z1 v1 y2 v4 x7 x9 v2 w2 x3 y3 z3 v3 w3 y1 x2 z4
   w6 v9 x5 y5 z5 v5 w5 x6 y6 v w1 y4 v6 y10 z7 v7 w7 x8 y8 z8 v8 x w8 y9
   z9 z6 w9 x10 x4 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x v2 z v x5 x1 y1 z7 v1 w1 x2 y2 z2 y9 w2 x3 y3 z3 v3 z1 x4 y4 z4
   v4 w4 w9 y5 z5 v5 w5 x6 w z6 v6 w6 x7 y7 z10 v7 w7 x8 y8 z8 y w8 x9 v8
   z9 v9 y6 x10 y10 w3 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y w2 v w y5 y1 z1 v7 w1 x2 y2 z2 v2 z9 w7 z5 x3 v1 w3 x4 y4 z4
   v4 w4 x5 x10 x8 v5 y3 x1 y6 z6 v6 w6 x7 y7 z7 v10 y8 w5 z3 z v8 w8 x9 y9
   z8 v9 w9 x6 y10 z10 v3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z x1 v1 y w z1 x v y1 v3 w3 x4 w1 x2 y2 z2 v2 w2 x3 y3 z3 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 x6 y6 z6
   y4 z4 v4 w4 x5 y5 z5 v5 w5 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 z8 v8 w8 v6 w6 x7 y7 z7 v7 w7 x8 y8 y10 v9 x9
   z10 w9 y9 v10 x10 z9) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 x7 v4 y2 w1 x2 x9 y7 w4 z2 y1 y3 z3 v3 w3 x4 y4 z4 y9
   z7 x5 v2 z1 v5 w5 x6 y6 z6 v6 w6 z9 v7 y5 w2 v1 x8 y8 z8 v8 w8 w7 z5 x3
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z w6 z4 x2 y1 z1 v1 w1 v9 y2 z2 v2 w2 x3 v z3 v3 w3 x4 y4 w9
   v4 w4 x5 y5 z5 w w5 x6 y6 z6 v6 x10 x7 y7 z7 v7 w7 x1 y8 z8 v8 w8 x9 y9
   z9 x8 v5 y3 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state v6 y4 w1 v w x1 y1 z1 v1 y10 x2 y2 z2 v2 w2 x3 y3 x x4 z6 w8 z10
   z4 v4 w4 x5 y5 z5 v5 y w3 y6 v8 v10 w6 x7 y7 z7 v7 w7 x8 z v3 x6 z8 x9
   y9 z9 v9 w9 x10 y8 w5 z3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state w8 y z z6 w x1 x4 z1 v1 v6 y4 w1 x v2 w2 x3 y3 z3 v3 w3 y10 w6 z4
   x2 v x5 y5 z5 v5 w5 x6 y6 v9 x7 v4 y2 y1 z7 v7 w7 x8 y8 z8 v8 x9 z2 y9
   z9 w4 w9 x10 y7 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x v8 z v y6 x1 y1 w3 v1 w1 x2 y2 z2 y w2 x3 y3 z3 v3 z10 x4 y4 z4
   v4 w4 w y5 z5 v5 w5 x6 w9 z6 v6 w6 x7 y7 z1 v7 w7 x8 y8 z8 y9 w8 x9 v2
   z9 v9 x5 x10 y10 z7 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z8 v w x6 y1 z1 v3 w1 x2 y2 z2 v2 z z3 w5 y8 v10 w3 x4 y4 z4
   v4 w4 x5 x1 y3 v5 x8 x10 y6 z6 v6 w6 x7 y7 z7 v1 x3 z5 w7 z9 v8 w8 x9 y9
   w2 v9 w9 y5 y10 z10 v7) ==>
~state b b b b b b b b b r r r g g g (o) (o) (o) (y) (y) (y) r r r g g g
 (o) (o) (o) (y) (y) (y) r r r g g g (o) (o) (o) (y) (y) (y) (w) (w) (w)
 (w) (w) (w) (w) (w) (w) ==> F`},

{name    = "PUZ037-3",
 comment = "",
 goal    = `
state b r r (w) (w) (w) (y) b b g (y) r b g g (o) g (y) (w) (w) r g (o) r b
g g (o) r b (y) (y) r g (o) g (o) (o) (o) (y) r b (y) (y) r (w) (w) (w) b b
(y) (w) (o) (o) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state y1 v x z1 w y v1 x1 z z2 v2 w2 x3 y3 z3 v3 w3 x4 w1 x2 y2 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 w4 x5 y5
   z5 v5 w5 x6 y6 z6 y4 z4 v4 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 y7 z7 v7 w7 x8 y8 z8 v8 w8 v6 w6 x7 z9 x10
   v10 y9 w9 z10 x9 v9 y10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 x3 z5 w7 w1 x2 v1 w2 y5 v7 z9 y3 z3 v3 w3 x4 y4 z4 z1
   v2 x5 z7 y9 v5 w5 x6 y6 z6 v6 w6 y1 z2 w4 y7 x9 x8 y8 z8 v8 w8 y2 v4 x7
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z y3 v5 x8 y1 z1 v1 w1 x1 y2 z2 v2 w2 x3 x10 z3 v3 w3 x4 y4 w
   v4 w4 x5 y5 z5 w9 w5 x6 y6 z6 v6 v x7 y7 z7 v7 w7 v9 y8 z8 v8 w8 x9 y9
   z9 x2 z4 w6 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z3 w5 y8 v w x1 y1 z1 v1 z x2 y2 z2 v2 w2 x3 y3 v10 z8 x6 v3 y z4
   v4 w4 x5 y5 z5 v5 z10 v8 y6 w3 x w6 x7 y7 z7 v7 w7 x8 y10 w8 z6 x4 x9 y9
   z9 v9 w9 x10 w1 y4 v6) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z2 y z w4 w x1 y7 z1 v1 y2 v4 x7 x9 v2 w2 x3 y3 z3 v3 w3 y1 x2 z4
   w6 v9 x5 y5 z5 v5 w5 x6 y6 v w1 y4 v6 y10 z7 v7 w7 x8 y8 z8 v8 x w8 y9
   z9 z6 w9 x10 x4 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x v2 z v x5 x1 y1 z7 v1 w1 x2 y2 z2 y9 w2 x3 y3 z3 v3 z1 x4 y4 z4
   v4 w4 w9 y5 z5 v5 w5 x6 w z6 v6 w6 x7 y7 z10 v7 w7 x8 y8 z8 y w8 x9 v8
   z9 v9 y6 x10 y10 w3 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y w2 v w y5 y1 z1 v7 w1 x2 y2 z2 v2 z9 w7 z5 x3 v1 w3 x4 y4 z4
   v4 w4 x5 x10 x8 v5 y3 x1 y6 z6 v6 w6 x7 y7 z7 v10 y8 w5 z3 z v8 w8 x9 y9
   z8 v9 w9 x6 y10 z10 v3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state z x1 v1 y w z1 x v y1 v3 w3 x4 w1 x2 y2 z2 v2 w2 x3 y3 z3 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 x6 y6 z6
   y4 z4 v4 w4 x5 y5 z5 v5 w5 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4
   w4 x5 y5 z5 v5 w5 x6 y6 z6 z8 v8 w8 v6 w6 x7 y7 z7 v7 w7 x8 y8 y10 v9 x9
   z10 w9 y9 v10 x10 z9) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z v w x1 x7 v4 y2 w1 x2 x9 y7 w4 z2 y1 y3 z3 v3 w3 x4 y4 z4 y9
   z7 x5 v2 z1 v5 w5 x6 y6 z6 v6 w6 z9 v7 y5 w2 v1 x8 y8 z8 v8 w8 w7 z5 x3
   v9 w9 x10 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z w6 z4 x2 y1 z1 v1 w1 v9 y2 z2 v2 w2 x3 v z3 v3 w3 x4 y4 w9
   v4 w4 x5 y5 z5 w w5 x6 y6 z6 v6 x10 x7 y7 z7 v7 w7 x1 y8 z8 v8 w8 x9 y9
   z9 x8 v5 y3 y10 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state v6 y4 w1 v w x1 y1 z1 v1 y10 x2 y2 z2 v2 w2 x3 y3 x x4 z6 w8 z10
   z4 v4 w4 x5 y5 z5 v5 y w3 y6 v8 v10 w6 x7 y7 z7 v7 w7 x8 z v3 x6 z8 x9
   y9 z9 v9 w9 x10 y8 w5 z3) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state w8 y z z6 w x1 x4 z1 v1 v6 y4 w1 x v2 w2 x3 y3 z3 v3 w3 y10 w6 z4
   x2 v x5 y5 z5 v5 w5 x6 y6 v9 x7 v4 y2 y1 z7 v7 w7 x8 y8 z8 v8 x9 z2 y9
   z9 w4 w9 x10 y7 z10 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x v8 z v y6 x1 y1 w3 v1 w1 x2 y2 z2 y w2 x3 y3 z3 v3 z10 x4 y4 z4
   v4 w4 w y5 z5 v5 w5 x6 w9 z6 v6 w6 x7 y7 z1 v7 w7 x8 y8 z8 y9 w8 x9 v2
   z9 v9 x5 x10 y10 z7 v10) /\
(!x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4 v4 w4 x5
   y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9 z9 v9 w9
   x10 y10 z10 v10.
   ~state x y z v w x1 y1 z1 v1 w1 x2 y2 z2 v2 w2 x3 y3 z3 v3 w3 x4 y4 z4
    v4 w4 x5 y5 z5 v5 w5 x6 y6 z6 v6 w6 x7 y7 z7 v7 w7 x8 y8 z8 v8 w8 x9 y9
    z9 v9 w9 x10 y10 z10 v10 \/
   state x y z8 v w x6 y1 z1 v3 w1 x2 y2 z2 v2 z z3 w5 y8 v10 w3 x4 y4 z4
   v4 w4 x5 x1 y3 v5 x8 x10 y6 z6 v6 w6 x7 y7 z7 v1 x3 z5 w7 z9 v8 w8 x9 y9
   w2 v9 w9 y5 y10 z10 v7) ==>
~state b b b b b b b b b r r r g g g (o) (o) (o) (y) (y) (y) r r r g g g
 (o) (o) (o) (y) (y) (y) r r r g g g (o) (o) (o) (y) (y) (y) (w) (w) (w)
 (w) (w) (w) (w) (w) (w) ==> F`},

{name    = "PUZ038-1",
 comment = "",
 goal    = `
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 y' z') v' w' x'' (e1 y' (s z')) y'' \/
   state x y z v w x' (s1 y' (s z')) v' w' x'' (e1 y' z') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 y' (s z')) v' w' x'' (e1 y' z') y'' \/
   state x y z v w x' (s1 y' z') v' w' x'' (e1 y' (s z')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 y' z') v' w' x'' (e1 (s y') z') y'' \/
   state x y z v w x' (s1 (s y') z') v' w' x'' (e1 y' z') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 (s y') z') v' w' x'' (e1 y' z') y'' \/
   state x y z v w x' (s1 y' z') v' w' x'' (e1 (s y') z') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 z' v') w' x'' (e1 z' (s v')) y'' \/
   state x y z v w x' y' (s2 z' (s v')) w' x'' (e1 z' v') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 z' (s v')) w' x'' (e1 z' v') y'' \/
   state x y z v w x' y' (s2 z' v') w' x'' (e1 z' (s v')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 z' v') w' x'' (e1 (s z') v') y'' \/
   state x y z v w x' y' (s2 (s z') v') w' x'' (e1 z' v') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 (s z') v') w' x'' (e1 z' v') y'' \/
   state x y z v w x' y' (s2 z' v') w' x'' (e1 (s z') v') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 v' w') x'' (e1 v' (s w')) y'' \/
   state x y z v w x' y' z' (s3 v' (s w')) x'' (e1 v' w') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 v' (s w')) x'' (e1 v' w') y'' \/
   state x y z v w x' y' z' (s3 v' w') x'' (e1 v' (s w')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 v' w') x'' (e1 (s v') w') y'' \/
   state x y z v w x' y' z' (s3 (s v') w') x'' (e1 v' w') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 (s v') w') x'' (e1 v' w') y'' \/
   state x y z v w x' y' z' (s3 v' w') x'' (e1 (s v') w') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 w' x'') (e1 w' (s x'')) y'' \/
   state x y z v w x' y' z' v' (s4 w' (s x'')) (e1 w' x'') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 w' (s x'')) (e1 w' x'') y'' \/
   state x y z v w x' y' z' v' (s4 w' x'') (e1 w' (s x'')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 w' x'') (e1 (s w') x'') y'' \/
   state x y z v w x' y' z' v' (s4 (s w') x'') (e1 w' x'') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 (s w') x'') (e1 w' x'') y'' \/
   state x y z v w x' y' z' v' (s4 w' x'') (e1 (s w') x'') y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x ((v1) y z) v w x' y' z' v' w' x'' (e1 y (s z))
    (e2 (s y) (s z)) \/
   state x ((v1) y (s z)) v w x' y' z' v' w' x'' (e1 y z) (e2 (s y) z)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x ((v1) y (s z)) v w x' y' z' v' w' x'' (e1 y z) (e2 (s y) z) \/
   state x ((v1) y z) v w x' y' z' v' w' x'' (e1 y (s z))
   (e2 (s y) (s z))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x ((v1) y z) v w x' y' z' v' w' x'' (e1 (s (s y)) z) y'' \/
   state x ((v1) (s y) z) v w x' y' z' v' w' x'' (e1 y z) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x ((v1) (s y) z) v w x' y' z' v' w' x'' (e1 y z) y'' \/
   state x ((v1) y z) v w x' y' z' v' w' x'' (e1 (s (s y)) z) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y ((v2) z v) w x' y' z' v' w' x'' (e1 z (s v))
    (e2 (s z) (s v)) \/
   state x y ((v2) z (s v)) w x' y' z' v' w' x'' (e1 z v) (e2 (s z) v)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y ((v2) z (s v)) w x' y' z' v' w' x'' (e1 z v) (e2 (s z) v) \/
   state x y ((v2) z v) w x' y' z' v' w' x'' (e1 z (s v))
   (e2 (s z) (s v))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y ((v2) z v) w x' y' z' v' w' x'' (e1 (s (s z)) v) y'' \/
   state x y ((v2) (s z) v) w x' y' z' v' w' x'' (e1 z v) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y ((v2) (s z) v) w x' y' z' v' w' x'' (e1 z v) y'' \/
   state x y ((v2) z v) w x' y' z' v' w' x'' (e1 (s (s z)) v) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z ((v3) v w) x' y' z' v' w' x'' (e1 v (s w))
    (e2 (s v) (s w)) \/
   state x y z ((v3) v (s w)) x' y' z' v' w' x'' (e1 v w) (e2 (s v) w)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z ((v3) v (s w)) x' y' z' v' w' x'' (e1 v w) (e2 (s v) w) \/
   state x y z ((v3) v w) x' y' z' v' w' x'' (e1 v (s w))
   (e2 (s v) (s w))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z ((v3) v w) x' y' z' v' w' x'' (e1 (s (s v)) w) y'' \/
   state x y z ((v3) (s v) w) x' y' z' v' w' x'' (e1 v w) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z ((v3) (s v) w) x' y' z' v' w' x'' (e1 v w) y'' \/
   state x y z ((v3) v w) x' y' z' v' w' x'' (e1 (s (s v)) w) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v ((v4) w x') y' z' v' w' x'' (e1 w (s x'))
    (e2 (s w) (s x')) \/
   state x y z v ((v4) w (s x')) y' z' v' w' x'' (e1 w x')
   (e2 (s w) x')) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v ((v4) w (s x')) y' z' v' w' x'' (e1 w x')
    (e2 (s w) x') \/
   state x y z v ((v4) w x') y' z' v' w' x'' (e1 w (s x'))
   (e2 (s w) (s x'))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v ((v4) w x') y' z' v' w' x'' (e1 (s (s w)) x') y'' \/
   state x y z v ((v4) (s w) x') y' z' v' w' x'' (e1 w x') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v ((v4) (s w) x') y' z' v' w' x'' (e1 w x') y'' \/
   state x y z v ((v4) w x') y' z' v' w' x'' (e1 (s (s w)) x') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w (h x' y') z' v' w' x'' (e1 x' (s (s y'))) y'' \/
   state x y z v w (h x' (s y')) z' v' w' x'' (e1 x' y') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w (h x' (s y')) z' v' w' x'' (e1 x' y') y'' \/
   state x y z v w (h x' y') z' v' w' x'' (e1 x' (s (s y'))) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v w (h x' y') z' v' w' x'' (e1 (s x') y')
    (e2 (s x') (s y')) \/
   state x y z v w (h (s x') y') z' v' w' x'' (e1 x' y') (e2 x' (s y'))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v w (h (s x') y') z' v' w' x'' (e1 x' y') (e2 x' (s y')) \/
   state x y z v w (h x' y') z' v' w' x'' (e1 (s x') y')
   (e2 (s x') (s y'))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb x y) z v w x' y' z' v' w' x'' (e1 x (s (s y)))
    (e2 (s x) (s (s y))) \/
   state (bb x (s y)) z v w x' y' z' v' w' x'' (e1 x y) (e2 (s x) y)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb x (s y)) z v w x' y' z' v' w' x'' (e1 x y) (e2 (s x) y) \/
   state (bb x y) z v w x' y' z' v' w' x'' (e1 x (s (s y)))
   (e2 (s x) (s (s y)))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb x y) z v w x' y' z' v' w' x'' (e1 (s (s x)) y)
    (e2 (s (s x)) (s y)) \/
   state (bb (s x) y) z v w x' y' z' v' w' x'' (e1 x y) (e2 x (s y))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb (s x) y) z v w x' y' z' v' w' x'' (e1 x y) (e2 x (s y)) \/
   state (bb x y) z v w x' y' z' v' w' x'' (e1 (s (s x)) y)
   (e2 (s (s x)) (s y))) /\
(!x y z v w x' y' z' v' w' x'' y'' z'' v''.
   ~state x y z v w x' y' z' v' w' (e1 x'' y'') (e2 z'' v'') \/
   state x y z v w x' y' z' v' w' (e1 z'' v'') (e2 x'' y'')) /\
state (bb (o) (s (o))) ((v1) (o) (o)) ((v2) (o) (s (s (s (o)))))
((v3) (s (s (o))) (o)) ((v4) (s (s (o))) (s (s (s (o)))))
(h (s (s (o))) (s (o))) (s1 (s (s (s (o)))) (s (o)))
(s2 (s (s (s (o)))) (s (s (o)))) (s3 (s (s (s (s (o))))) (s (o)))
(s4 (s (s (s (s (o))))) (s (s (o)))) (e1 (s (s (s (s (o))))) (o))
(e2 (s (s (s (s (o))))) (s (s (s (o))))) ==>
(!x y z v w x' y' z' v' w' x''.
   ~state x y z ((v3) (s (s (s (o)))) (o)) v w x' y' z' v' w' x'') ==> F`},

{name    = "PUZ042-1",
 comment = "",
 goal    = `
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 y' z') v' w' x'' (e1 y' (s z')) y'' \/
   state x y z v w x' (s1 y' (s z')) v' w' x'' (e1 y' z') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 y' (s z')) v' w' x'' (e1 y' z') y'' \/
   state x y z v w x' (s1 y' z') v' w' x'' (e1 y' (s z')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 y' z') v' w' x'' (e1 (s y') z') y'' \/
   state x y z v w x' (s1 (s y') z') v' w' x'' (e1 y' z') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' (s1 (s y') z') v' w' x'' (e1 y' z') y'' \/
   state x y z v w x' (s1 y' z') v' w' x'' (e1 (s y') z') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 z' v') w' x'' (e1 z' (s v')) y'' \/
   state x y z v w x' y' (s2 z' (s v')) w' x'' (e1 z' v') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 z' (s v')) w' x'' (e1 z' v') y'' \/
   state x y z v w x' y' (s2 z' v') w' x'' (e1 z' (s v')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 z' v') w' x'' (e1 (s z') v') y'' \/
   state x y z v w x' y' (s2 (s z') v') w' x'' (e1 z' v') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' (s2 (s z') v') w' x'' (e1 z' v') y'' \/
   state x y z v w x' y' (s2 z' v') w' x'' (e1 (s z') v') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 v' w') x'' (e1 v' (s w')) y'' \/
   state x y z v w x' y' z' (s3 v' (s w')) x'' (e1 v' w') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 v' (s w')) x'' (e1 v' w') y'' \/
   state x y z v w x' y' z' (s3 v' w') x'' (e1 v' (s w')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 v' w') x'' (e1 (s v') w') y'' \/
   state x y z v w x' y' z' (s3 (s v') w') x'' (e1 v' w') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' (s3 (s v') w') x'' (e1 v' w') y'' \/
   state x y z v w x' y' z' (s3 v' w') x'' (e1 (s v') w') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 w' x'') (e1 w' (s x'')) y'' \/
   state x y z v w x' y' z' v' (s4 w' (s x'')) (e1 w' x'') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 w' (s x'')) (e1 w' x'') y'' \/
   state x y z v w x' y' z' v' (s4 w' x'') (e1 w' (s x'')) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 w' x'') (e1 (s w') x'') y'' \/
   state x y z v w x' y' z' v' (s4 (s w') x'') (e1 w' x'') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w x' y' z' v' (s4 (s w') x'') (e1 w' x'') y'' \/
   state x y z v w x' y' z' v' (s4 w' x'') (e1 (s w') x'') y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x ((v1) y z) v w x' y' z' v' w' x'' (e1 y (s z))
    (e2 (s y) (s z)) \/
   state x ((v1) y (s z)) v w x' y' z' v' w' x'' (e1 y z) (e2 (s y) z)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x ((v1) y (s z)) v w x' y' z' v' w' x'' (e1 y z) (e2 (s y) z) \/
   state x ((v1) y z) v w x' y' z' v' w' x'' (e1 y (s z))
   (e2 (s y) (s z))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x ((v1) y z) v w x' y' z' v' w' x'' (e1 (s (s y)) z) y'' \/
   state x ((v1) (s y) z) v w x' y' z' v' w' x'' (e1 y z) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x ((v1) (s y) z) v w x' y' z' v' w' x'' (e1 y z) y'' \/
   state x ((v1) y z) v w x' y' z' v' w' x'' (e1 (s (s y)) z) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y ((v2) z v) w x' y' z' v' w' x'' (e1 z (s v))
    (e2 (s z) (s v)) \/
   state x y ((v2) z (s v)) w x' y' z' v' w' x'' (e1 z v) (e2 (s z) v)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y ((v2) z (s v)) w x' y' z' v' w' x'' (e1 z v) (e2 (s z) v) \/
   state x y ((v2) z v) w x' y' z' v' w' x'' (e1 z (s v))
   (e2 (s z) (s v))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y ((v2) z v) w x' y' z' v' w' x'' (e1 (s (s z)) v) y'' \/
   state x y ((v2) (s z) v) w x' y' z' v' w' x'' (e1 z v) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y ((v2) (s z) v) w x' y' z' v' w' x'' (e1 z v) y'' \/
   state x y ((v2) z v) w x' y' z' v' w' x'' (e1 (s (s z)) v) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z ((v3) v w) x' y' z' v' w' x'' (e1 v (s w))
    (e2 (s v) (s w)) \/
   state x y z ((v3) v (s w)) x' y' z' v' w' x'' (e1 v w) (e2 (s v) w)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z ((v3) v (s w)) x' y' z' v' w' x'' (e1 v w) (e2 (s v) w) \/
   state x y z ((v3) v w) x' y' z' v' w' x'' (e1 v (s w))
   (e2 (s v) (s w))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z ((v3) v w) x' y' z' v' w' x'' (e1 (s (s v)) w) y'' \/
   state x y z ((v3) (s v) w) x' y' z' v' w' x'' (e1 v w) y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z ((v3) (s v) w) x' y' z' v' w' x'' (e1 v w) y'' \/
   state x y z ((v3) v w) x' y' z' v' w' x'' (e1 (s (s v)) w) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v ((v4) w x') y' z' v' w' x'' (e1 w (s x'))
    (e2 (s w) (s x')) \/
   state x y z v ((v4) w (s x')) y' z' v' w' x'' (e1 w x')
   (e2 (s w) x')) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v ((v4) w (s x')) y' z' v' w' x'' (e1 w x')
    (e2 (s w) x') \/
   state x y z v ((v4) w x') y' z' v' w' x'' (e1 w (s x'))
   (e2 (s w) (s x'))) /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v ((v4) w x') y' z' v' w' x'' (e1 (s (s w)) x') y'' \/
   state x y z v ((v4) (s w) x') y' z' v' w' x'' (e1 w x') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v ((v4) (s w) x') y' z' v' w' x'' (e1 w x') y'' \/
   state x y z v ((v4) w x') y' z' v' w' x'' (e1 (s (s w)) x') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w (h x' y') z' v' w' x'' (e1 x' (s (s y'))) y'' \/
   state x y z v w (h x' (s y')) z' v' w' x'' (e1 x' y') y'') /\
(!x y z v w x' y' z' v' w' x'' y''.
   ~state x y z v w (h x' (s y')) z' v' w' x'' (e1 x' y') y'' \/
   state x y z v w (h x' y') z' v' w' x'' (e1 x' (s (s y'))) y'') /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v w (h x' y') z' v' w' x'' (e1 (s x') y')
    (e2 (s x') (s y')) \/
   state x y z v w (h (s x') y') z' v' w' x'' (e1 x' y') (e2 x' (s y'))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v w (h (s x') y') z' v' w' x'' (e1 x' y') (e2 x' (s y')) \/
   state x y z v w (h x' y') z' v' w' x'' (e1 (s x') y')
   (e2 (s x') (s y'))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb x y) z v w x' y' z' v' w' x'' (e1 x (s (s y)))
    (e2 (s x) (s (s y))) \/
   state (bb x (s y)) z v w x' y' z' v' w' x'' (e1 x y) (e2 (s x) y)) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb x (s y)) z v w x' y' z' v' w' x'' (e1 x y) (e2 (s x) y) \/
   state (bb x y) z v w x' y' z' v' w' x'' (e1 x (s (s y)))
   (e2 (s x) (s (s y)))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb x y) z v w x' y' z' v' w' x'' (e1 (s (s x)) y)
    (e2 (s (s x)) (s y)) \/
   state (bb (s x) y) z v w x' y' z' v' w' x'' (e1 x y) (e2 x (s y))) /\
(!x y z v w x' y' z' v' w' x''.
   ~state (bb (s x) y) z v w x' y' z' v' w' x'' (e1 x y) (e2 x (s y)) \/
   state (bb x y) z v w x' y' z' v' w' x'' (e1 (s (s x)) y)
   (e2 (s (s x)) (s y))) /\
(!x y z v w x' y' z' v' w' x'' y'' z'' v''.
   ~state x y z v w x' y' z' v' w' (e1 x'' y'') (e2 z'' v'') \/
   state x y z v w x' y' z' v' w' (e1 z'' v'') (e2 x'' y'')) /\
state (bb (o) (s (o))) ((v1) (o) (o)) ((v2) (o) (s (s (s (o)))))
((v3) (s (s (o))) (o)) ((v4) (s (s (o))) (s (s (s (o)))))
(h (s (s (o))) (s (o))) (s1 (s (s (s (o)))) (s (o)))
(s2 (s (s (s (o)))) (s (s (o)))) (s3 (s (s (s (s (o))))) (s (o)))
(s4 (s (s (s (s (o))))) (s (s (o)))) (e1 (s (s (s (s (o))))) (o))
(e2 (s (s (s (s (o))))) (s (s (s (o))))) ==>
(!x y z v w x' y' z' v' w' x''.
   ~state x y z v w (h (s (s (s (o)))) (s (o))) x' y' z' v' w' x'') ==> F`},

{name    = "PUZ047-1",
 comment = "",
 goal    = `
T ==>
p south south south south start /\
(!x.
   p north north south north (go_alone x) \/
   ~p south north south north x) /\
(!x.
   p south north south north (go_alone x) \/
   ~p north north south north x) /\
(!x.
   p north south north south (go_alone x) \/
   ~p south south north south x) /\
(!x.
   p south south north south (go_alone x) \/
   ~p north south north south x) /\
(!x.
   p north north south north (take_wolf x) \/
   ~p south south south north x) /\
(!x.
   p south south south north (take_wolf x) \/
   ~p north north south north x) /\
(!x.
   p north north north south (take_wolf x) \/
   ~p south south north south x) /\
(!x.
   p south south north south (take_wolf x) \/
   ~p north north north south x) /\
(!x y z. p north x north y (take_goat z) \/ ~p south x south y z) /\
(!x y z. p south x south y (take_goat z) \/ ~p north x north y z) /\
(!x.
   p north north south north (take_cabbage x) \/
   ~p south north south south x) /\
(!x.
   p south north south south (take_cabbage x) \/
   ~p north north south north x) /\
(!x.
   p north south north north (take_cabbage x) \/
   ~p south south north south x) /\
(!x.
   p south south north south (take_cabbage x) \/
   ~p north south north north x) /\ (!x. ~p north north north north x) ==>
F`}

];

(* ========================================================================= *)
(* mlibProblem compilations                                                      *)
(* ========================================================================= *)

fun Nonequality p = extract (nonequality ()) p;
fun Equality    p = extract (equality ())    p;
fun mlibTptp        p = extract (tptp ())        p;

fun exclude l =
  List.filter (fn {name, ...} : 'a problem => not (mlibUseful.mem name l));

(* ------------------------------------------------------------------------- *)
(* A test suite with no problems in it (surprisingly useful).                *)
(* ------------------------------------------------------------------------- *)

fun nothing () = mk_set "nothing" "problems" [];

(* ------------------------------------------------------------------------- *)
(* A tiny test suite used for sanity checking large runs.                    *)
(* ------------------------------------------------------------------------- *)

fun instant () =

mk_set "instant" "problems that all provers can solve" [

Nonequality "TRUE",
Nonequality "JH_test",
Nonequality "CYCLIC",
Nonequality "MN_bug",
Nonequality "PROP_6",
Nonequality "MATHS4_EXAMPLE",
Nonequality "P18",
Nonequality "P39",
Nonequality "P59",
Nonequality "BAD_CONNECTIONS",

Equality "TRANS_SYMM",
Equality "CYCLIC_SUBSTITUTION_BUG",
Equality "P48"

];

(* ------------------------------------------------------------------------- *)
(* A test suite for the MLton version of the prover.                         *)
(* ------------------------------------------------------------------------- *)

fun std () =

mk_set "std" "problems comprising the standard test suite"

(exclude ["P34"]
 (#probs (nonequality ()) @ #probs (equality ()) @ #probs (tptp ())));

(* ------------------------------------------------------------------------- *)
(* A reduced test suite for the Moscow ML version of the prover.             *)
(* ------------------------------------------------------------------------- *)

fun quick () =

mk_set "quick" "problems comprising the quick test suite"

(exclude
 [(* nonequality *)
  "P38", "GILMORE_2", "GILMORE_9", "MODEL_COMPLETENESS",
  (* equality *)
  "JACOBSON_2", "JACOBSON_3",
  (* tptp *)
  "ALG005-1", "GRP057-1", "LCL107-1", "ROB001-1", "RNG009-7", "RNG035-7"]
 (#probs (std ())));

(* ------------------------------------------------------------------------- *)
(* Benchmark used to profile mlibMetis implementations.                          *)
(* ------------------------------------------------------------------------- *)

fun benchmark () = 

mk_set "benchmark" "problems comprising the benchmark problem set"

(#probs (std ()) @ #probs (puzzle ()) @ #probs (hol ()));

(* ------------------------------------------------------------------------- *)
(* mlibMeson benchmark submitted to the MLton development team on 24/9/2002.     *)
(* ------------------------------------------------------------------------- *)

fun meson_benchmark () =

mk_set "meson_benchmark" "problems comprising the MLton meson benchmark" [

Nonequality "P26",
Nonequality "P46",
Nonequality "GILMORE_1",
Nonequality "LOS",
Nonequality "STEAM_ROLLER",

Equality "P48",
Equality "P49",
Equality "AGATHA",

mlibTptp "LCL009-1",
mlibTptp "COL060-3",
mlibTptp "COL058-2",
mlibTptp "LCL107-1",
mlibTptp "BOO021-1",
mlibTptp "GRP128-4.003"

];

end
