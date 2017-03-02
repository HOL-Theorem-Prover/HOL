open Hl_parser;;
open Fusion;;
open Bool;;
open Simp;;

let eQ_REFL = Sequent
 ([],parse_term "!x:A. x = x");;

let rEFL_CLAUSE = Sequent
 ([],parse_term "!x:A. (x = x) <=> T");;

let eQ_SYM = Sequent
 ([],parse_term "!(x:A) y. (x = y) ==> (y = x)");;

let eQ_SYM_EQ = Sequent
 ([],parse_term "!(x:A) y. (x = y) <=> (y = x)");;

let eQ_TRANS = Sequent
 ([],parse_term "!(x:A) y z. (x = y) /\\ (y = z) ==> (x = z)");;

let aC acsuite x = eQT_ELIM (pURE_REWRITE_CONV[acsuite; rEFL_CLAUSE] x);;

let bETA_THM = Sequent
 ([],parse_term "!(f:A->B) y. (\\x. (f:A->B) x) y = f y");;

let aBS_SIMP = Sequent
 ([],parse_term "!(t1:A) (t2:B). (\\x. t1) t2 = t1");;

(* ------------------------------------------------------------------------- *)
(* A few "big name" intuitionistic tautologies.                              *)
(* ------------------------------------------------------------------------- *)

let cONJ_ASSOC = Sequent
 ([],parse_term "!t1 t2 t3. t1 /\\ t2 /\\ t3 <=> (t1 /\\ t2) /\\ t3");;

let cONJ_SYM = Sequent
 ([],parse_term "!t1 t2. t1 /\\ t2 <=> t2 /\\ t1");;

let cONJ_ACI = Sequent
 ([],parse_term "(p /\\ q <=> q /\\ p) /\\
   ((p /\\ q) /\\ r <=> p /\\ (q /\\ r)) /\\
   (p /\\ (q /\\ r) <=> q /\\ (p /\\ r)) /\\
   (p /\\ p <=> p) /\\
   (p /\\ (p /\\ q) <=> p /\\ q)");;

let dISJ_ASSOC = Sequent
 ([],parse_term "!t1 t2 t3. t1 \\/ t2 \\/ t3 <=> (t1 \\/ t2) \\/ t3");;

let dISJ_SYM = Sequent
 ([],parse_term "!t1 t2. t1 \\/ t2 <=> t2 \\/ t1");;

let dISJ_ACI = Sequent
 ([],parse_term "(p \\/ q <=> q \\/ p) /\\
   ((p \\/ q) \\/ r <=> p \\/ (q \\/ r)) /\\
   (p \\/ (q \\/ r) <=> q \\/ (p \\/ r)) /\\
   (p \\/ p <=> p) /\\
   (p \\/ (p \\/ q) <=> p \\/ q)");;

let iMP_CONJ = Sequent
 ([],parse_term "p /\\ q ==> r <=> p ==> q ==> r");;

let iMP_IMP = Equal.gSYM iMP_CONJ;;

let iMP_CONJ_ALT = Sequent
 ([],parse_term "p /\\ q ==> r <=> q ==> p ==> r");;

(* ------------------------------------------------------------------------- *)
(* A couple of "distribution" tautologies are useful.                        *)
(* ------------------------------------------------------------------------- *)

let lEFT_OR_DISTRIB = Sequent
 ([],parse_term "!p q r. p /\\ (q \\/ r) <=> p /\\ q \\/ p /\\ r");;

let rIGHT_OR_DISTRIB = Sequent
 ([],parse_term "!p q r. (p \\/ q) /\\ r <=> p /\\ r \\/ q /\\ r");;

(* ------------------------------------------------------------------------- *)
(* Degenerate cases of quantifiers.                                          *)
(* ------------------------------------------------------------------------- *)

let fORALL_SIMP = Sequent
 ([],parse_term "!t. (!x:A. t) = t");;

let eXISTS_SIMP = Sequent
 ([],parse_term "!t. (?x:A. t) = t");;

(* ------------------------------------------------------------------------- *)
(* I also use this a lot (as a prelude to congruence reasoning).             *)
(* ------------------------------------------------------------------------- *)

let eQ_IMP = Sequent
 ([],parse_term "(a <=> b) ==> a ==> b");;

(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)

let eQ_CLAUSES = Sequent
 ([],parse_term "!t. ((T <=> t) <=> t) /\\ ((t <=> T) <=> t) /\\
       ((F <=> t) <=> ~t) /\\ ((t <=> F) <=> ~t)");;

let nOT_CLAUSES_WEAK = Sequent
 ([],parse_term "(~T <=> F) /\\ (~F <=> T)");;

let aND_CLAUSES = Sequent
 ([],parse_term "!t. (T /\\ t <=> t) /\\ (t /\\ T <=> t) /\\ (F /\\ t <=> F) /\\
       (t /\\ F <=> F) /\\ (t /\\ t <=> t)");;

let oR_CLAUSES = Sequent
 ([],parse_term "!t. (T \\/ t <=> T) /\\ (t \\/ T <=> T) /\\ (F \\/ t <=> t) /\\
       (t \\/ F <=> t) /\\ (t \\/ t <=> t)");;

let iMP_CLAUSES = Sequent
 ([],parse_term "!t. (T ==> t <=> t) /\\ (t ==> T <=> T) /\\ (F ==> t <=> T) /\\
       (t ==> t <=> T) /\\ (t ==> F <=> ~t)");;

let eXISTS_UNIQUE_THM = Sequent
 ([],parse_term "!P. (?!x:A. P x) <=> (?x. P x) /\\ (!x x'. P x /\\ P x' ==> (x = x'))");;

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)

let eXISTS_REFL = Sequent
 ([],parse_term "!a:A. ?x. x = a");;

let eXISTS_UNIQUE_REFL = Sequent
 ([],parse_term "!a:A. ?!x. x = a");;

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)

let uNWIND_THM1 = Sequent
 ([],parse_term "!P (a:A). (?x. a = x /\\ P x) <=> P a");;

let uNWIND_THM2 = Sequent
 ([],parse_term "!P (a:A). (?x. x = a /\\ P x) <=> P a");;

let fORALL_UNWIND_THM2 = Sequent
 ([],parse_term "!P (a:A). (!x. x = a ==> P x) <=> P a");;

let fORALL_UNWIND_THM1 = Sequent
 ([],parse_term "!P a. (!x. a = x ==> P x) <=> P a");;

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)

let sWAP_FORALL_THM = Sequent
 ([],parse_term "!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)");;

let sWAP_EXISTS_THM = Sequent
 ([],parse_term "!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)");;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

let fORALL_AND_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)");;

let aND_FORALL_THM = Sequent
 ([],parse_term "!P Q. (!x. P x) /\\ (!x. Q x) <=> (!x:A. P x /\\ Q x)");;

let lEFT_AND_FORALL_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P x) /\\ Q <=> (!x:A. P x /\\ Q)");;

let rIGHT_AND_FORALL_THM = Sequent
 ([],parse_term "!P Q. P /\\ (!x:A. Q x) <=> (!x. P /\\ Q x)");;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let eXISTS_OR_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)");;

let oR_EXISTS_THM = Sequent
 ([],parse_term "!P Q. (?x. P x) \\/ (?x. Q x) <=> (?x:A. P x \\/ Q x)");;

let lEFT_OR_EXISTS_THM = Sequent
 ([],parse_term "!P Q. (?x. P x) \\/ Q <=> (?x:A. P x \\/ Q)");;

let rIGHT_OR_EXISTS_THM = Sequent
 ([],parse_term "!P Q. P \\/ (?x. Q x) <=> (?x:A. P \\/ Q x)");;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let lEFT_EXISTS_AND_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P x /\\ Q) <=> (?x:A. P x) /\\ Q");;

let rIGHT_EXISTS_AND_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P /\\ Q x) <=> P /\\ (?x:A. Q x)");;

let tRIV_EXISTS_AND_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P /\\ Q) <=> (?x:A. P) /\\ (?x:A. Q)");;

let lEFT_AND_EXISTS_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P x) /\\ Q <=> (?x:A. P x /\\ Q)");;

let rIGHT_AND_EXISTS_THM = Sequent
 ([],parse_term "!P Q. P /\\ (?x:A. Q x) <=> (?x:A. P /\\ Q x)");;

let tRIV_AND_EXISTS_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P) /\\ (?x:A. Q) <=> (?x:A. P /\\ Q)");;

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

let tRIV_FORALL_OR_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P \\/ Q) <=> (!x:A. P) \\/ (!x:A. Q)");;

let tRIV_OR_FORALL_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P) \\/ (!x:A. Q) <=> (!x:A. P \\/ Q)");;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let rIGHT_IMP_FORALL_THM = Sequent
 ([],parse_term "!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)");;

let rIGHT_FORALL_IMP_THM = Sequent
 ([],parse_term "!P Q. (!x. P ==> Q x) <=> (P ==> !x:A. Q x)");;

let lEFT_IMP_EXISTS_THM = Sequent
 ([],parse_term "!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)");;

let lEFT_FORALL_IMP_THM = Sequent
 ([],parse_term "!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)");;

let tRIV_FORALL_IMP_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P ==> Q) <=> ((?x:A. P) ==> (!x:A. Q))");;

let tRIV_EXISTS_IMP_THM = Sequent
 ([],parse_term "!P Q. (?x:A. P ==> Q) <=> ((!x:A. P) ==> (?x:A. Q))");;

(* ------------------------------------------------------------------------- *)
(* Alternative versions of unique existence.                                 *)
(* ------------------------------------------------------------------------- *)

let eXISTS_UNIQUE_ALT = Sequent
 ([],parse_term "!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))");;

let eXISTS_UNIQUE = Sequent
 ([],parse_term "!P:A->bool. (?!x. P x) <=> (?x. P x /\\ !y. P y ==> (y = x))");;

let lEFT_FORALL_OR_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P x \\/ Q) <=> (!x. P x) \\/ Q");;

let rIGHT_FORALL_OR_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P \\/ Q x) <=> P \\/ (!x. Q x)");;

let sKOLEM_THM = Sequent
 ([],parse_term "!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))");;

let lEFT_OR_FORALL_THM = Sequent
 ([],parse_term "!P Q. (!x:A. P x) \\/ Q <=> (!x. P x \\/ Q)");;

let rIGHT_OR_FORALL_THM = Sequent
 ([],parse_term "!P Q. P \\/ (!x:A. Q x) <=> (!x. P \\/ Q x)");;
