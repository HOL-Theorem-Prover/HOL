(****************************************************************************)
(* FILE          : examples.sml                                             *)
(* DESCRIPTION   : Examples to test combined decision procedure.            *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 11th March 1995                                          *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 3rd September 1996                                       *)
(****************************************************************************)

load "decisionLib";
val DECIDE = decisionLib.DECIDE o Parse.Term;

(* Uncomment this to see the internal workings
decisionLib.show_proving := true;
*)

(* Pure linear arithmetic *)
DECIDE `((m <= n) /\ ~(m = n)) ==> (SUC m) <= n`;

(* Linear arithmetic with an irrelevant subterm *)
DECIDE `((p + 3) <= n) ==> (!m. ((m EXP 2 = 0) => (n - 1) | (n - 2)) > p)`;

(* Adapted from the example in Nelson and Oppen's paper *)
DECIDE `~((x <= y) /\ (y <= x + HD [0;x]) /\ P(h(x) - h(y)) /\ ~P(0))`;

(* Equational theory of lists and uninterpreted function symbols *)
DECIDE `((HD x = HD y) /\ (TL x = TL y) /\ ~(NULL x) /\ ~(NULL y)) ==>
         (f(x) = (f:('a)list -> 'b)(y))`;

(* Propositional logic nested inside list structure *)
DECIDE `(x = y) ==> ([x /\ y; y] = [y; x \/ y])`;

(* An example contrived to make the procedure work hard! *)
DECIDE
   `(n > k) /\ (SND p1 <= k + HD l) /\ (p1 = ([0;1;2],m)) /\ (l = [1;2]) ==>
     (FST ((m <= n) => p1 | p2) = CONS 0 l)`;

(* Example from the info-hol mailing list, 12 July 1995 *)
DECIDE `!t. ((SUC t = 0) => F | (inp (SUC t - SUC 0))) /\ inp (SUC t) =
             inp t /\ inp (SUC t)`;

(* Using numeric literals in the same problem. *)
DECIDE `!t. ((t+1 = 0) => F | (inp (t+1 - 1)))
             /\ inp (t+1) = inp t /\ inp (t+1)`;

(* Define a recursive type of Lisp s-expressions *)
val sexp_type_info =
   HOLTypeInfo.define_type_info
      {name = "sexp",
       type_spec = `sexp = Nil | Atom of 'a | Cons of sexp => sexp`,
       fixities = [Term.Prefix,Term.Prefix,Term.Prefix],
       selectors = [("Atom",["Tok"]),("Cons",["Car","Cdr"])],
       discriminators = [("Nil","Nilp"),("Atom","Atomp"),("Cons","Consp")]};

(* Extend the decision procedure to work for the new type *)
DecideTypes.add_type sexp_type_info;

(* A pure example from the theory of equality over s-expressions *)
DECIDE `(Car x = Car y) /\ (Cdr x = Cdr y) /\ Consp x /\ Consp y ==> (x = y)`;

(* A mixture of lists and s-expressions *)
DECIDE `(Car (HD x) = Car (HD y)) /\ (Cdr (HD x) = Cdr (HD y)) /\
         Consp (HD x) /\ Consp (HD y) /\ ~(NULL x) /\ ~(NULL y) ==>
         (HD x = HD y)`;

