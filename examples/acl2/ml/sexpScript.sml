(*****************************************************************************)
(* This file defines a type of s-expressions and various constants and       *)
(* functions on this type (t, nil, car, cdr, cons etc).                      *)
(*                                                                           *)
(* One goal is to construct a model of ACL2 by proving the axioms in         *)
(* axioms.lisp.                                                              *)
(*                                                                           *)
(* File written by Mike Gordon and Matt Kaufmann; maintained by Mike Gordon. *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Ignore everything up to "END BOILERPLATE"                                 *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE NEEDED FOR COMPILATION                                  *)
(*****************************************************************************)

(******************************************************************************
* Load theories
******************************************************************************)
(* The commented out stuff below should be loaded in interactive sessions
quietdec := true;
map 
 load  
 ["complex_rationalTheory", "sexp"];
open complex_rationalTheory sexp;
Globals.checking_const_names := false;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules.
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt).
******************************************************************************)
open stringLib complex_rationalTheory sexp;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "sexp"                                                   *)
(*****************************************************************************)
val _ = new_theory "sexp";

(*****************************************************************************)
(* Define s-expressions.                                                     *)
(*****************************************************************************)

(*****************************************************************************)
(* Introduce mnemonic abbreviations to indicate use of type ``:string``      *)
(*****************************************************************************)
val _ = type_abbrev("packagename", ``:string``);
val _ = type_abbrev("name",        ``:string``);

(*****************************************************************************)
(* ACL2 S-expressions defined as a HOL datatype.                             *)
(* Definition below adapted from Mark Staples' code.                         *)
(*****************************************************************************)
val _ = Hol_datatype
 `sexp = ACL2_SYMBOL    of packagename => name     (* only curried for style *)
       | ACL2_STRING    of string
       | ACL2_CHARACTER of char
       | ACL2_NUMBER    of complex_rational
       | ACL2_PAIR      of sexp => sexp`;          (* only curried for style *)

(*****************************************************************************)
(* Each ACL2 function or constant is given a name of the form "pkg::nam".    *)
(* Since "::" is not handled by the HOL parser (and there are also many      *)
(* other character sequences that HOL can't parse occurring in ACL2          *)
(* names) we also provide a HOL friendly name which is overloaded onto the   *)
(* ACL2 name. For example the ACL2 name "ACL2::BAD-ATOM<=" is given the      *)
(* HOL friendly name "bad_atom_less_equal".                                  *)
(*****************************************************************************)

(*****************************************************************************)
(* Overload "cons" onto ``ACL2_PAIR`` rather than make a definition, so      *)
(* that cons behaves like a constructor and so can be used in patterns in    *)
(* definitions (e.g. see definition of car below).                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Overload short mnemonic names onto the sexp datatype constructors.        *)
(*****************************************************************************)
val _ = declare_names ("ACL2_PAIR",      "cons");
val _ = declare_names ("ACL2_SYMBOL",    "sym");
val _ = declare_names ("ACL2_NUMBER",    "num");
val _ = declare_names ("ACL2_STRING",    "str");
val _ = declare_names ("ACL2_CHARACTER", "chr");

(*****************************************************************************)
(* Introduce some constants to abbreviate common package names.              *)
(*****************************************************************************)
val ACL2_def                = Define `ACL2                = "ACL2"`
and COMMON_LISP_def         = Define `COMMON_LISP         = "COMMON-LISP"`
and KEYWORD_def             = Define `KEYWORD             = "KEYWORD"`
and ACL2_OUTPUT_CHANNEL_def = Define `ACL2_OUTPUT_CHANNEL = "ACL2-OUTPUT-CHANNEL"`;

val asym_def = Define `asym = sym ACL2`;
val csym_def = Define `csym = sym COMMON_LISP`;
val ksym_def = Define `ksym = sym KEYWORD`;
val osym_def = Define `osym = sym ACL2_OUTPUT_CHANNEL`;

val _ =
 add_string_abbrevs
  [("ACL2",                lhs(concl ACL2_def )),
   ("COMMON-LISP",         lhs(concl COMMON_LISP_def)),
   ("KEYWORD",             lhs(concl KEYWORD_def)),
   ("ACL2-OUTPUT-CHANNEL", lhs(concl ACL2_OUTPUT_CHANNEL_def))
  ];


(*****************************************************************************)
(* Definition of primitive constants and functions.                          *)
(*****************************************************************************)
val nil_def = 
 acl2Define "COMMON-LISP::NIL" `nil = sym "COMMON-LISP" "NIL"`; 

val t_def = 
 acl2Define "COMMON-LISP::T" `t = sym "COMMON-LISP" "T"`; 

val quote_def = 
 acl2Define "COMMON-LISP::QUOTE" `quote = sym "COMMON-LISP" "QUOTE"`; 

(*****************************************************************************)
(* From axioms.lisp                                                          *)
(*                                                                           *)
(* ; (equal x x) = T                                                         *)
(*                                                                           *)
(* ; x/=y -> (equal x y) = NIL                                               *)
(*                                                                           *)
(*                                                                           *)
(* equal                                                                     *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* equal (x y)                                                    *)
(*   (equal x y))                                                            *)
(*****************************************************************************)
val equal_def =
 acl2Define "COMMON-LISP::EQUAL" 
  `equal (x:sexp) (y:sexp) = if x = y then t else nil`;

(*****************************************************************************)
(* stringp                                                                   *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* stringp (x)                                                    *)
(*   (stringp x))                                                            *)
(*****************************************************************************)
val stringp_def =
 acl2Define "COMMON-LISP::STRINGP"
  `(stringp(str x) = t) /\ (stringp _ = nil)`;

(*****************************************************************************)
(* characterp                                                                *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* characterp (x)                                                 *)
(*   (characterp x))                                                         *)
(*****************************************************************************)
val characterp_def =
 acl2Define "COMMON-LISP::CHARACTERP"
  `(characterp(chr x) = t) /\ (characterp _ = nil)`;

(*****************************************************************************)
(* Construct a fraction then a rational from numerator and denominator       *)
(*****************************************************************************)
val rat_def = Define `rat n d = abs_rat(abs_frac(n,d))`;

(*****************************************************************************)
(* Construct a complex from four integers: an/ad + (bn/bd)i.                 *)
(*****************************************************************************)
val cpx_def = 
 Define `cpx an ad bn bd = num(com (rat an ad) (rat bn bd))`;

(*****************************************************************************)
(*  Construct a complex from an integer: n |--> n/1  + (0/1)i.               *)
(*****************************************************************************)
val int_def = Define `int n = cpx n 1 0 1`;

(*****************************************************************************)
(*  Construct a complex from a natural number: n |--> int n.                 *)
(*****************************************************************************)
val nat_def = Define `nat n = int(& n)`;

(*****************************************************************************)
(* acl2-numberp                                                              *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* acl2-numberp (x)                                               *)
(*   (numberp x))                                                            *)
(*****************************************************************************)
val acl2_numberp_def =
 acl2Define "ACL2::ACL2-NUMBERP"
  `(acl2_numberp(num x) = t) /\ (acl2_numberp _ = nil)`;

(*****************************************************************************)
(* binary-+                                                                  *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* binary-+ (x y)                                                 *)
(*   (the number                                                             *)
(*        (if (numberp x)                                                    *)
(*            (if (numberp y)                                                *)
(*                (+ (the number x) (the number y))                          *)
(*              (gv binary-+ (x y) x))                                       *)
(*          (gv binary-+ (x y)                                               *)
(*              (if (numberp y)                                              *)
(*                  y                                                        *)
(*                0)))))                                                     *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* binary-+ (x y)                                                 *)
(*   (+ (if (numberp x) x 0)                                                 *)
(*      (if (numberp y) y 0)))                                               *)
(*****************************************************************************)
val add_def =
 acl2Define "ACL2::BINARY-+"
  `(add (num x) (num y) = num(x+y)) /\
   (add (num x) _       = num x)    /\
   (add _       (num y) = num y)    /\
   (add _       _       = int 0)`;

(*****************************************************************************)
(* [Note: space added between "(" and "*" to avoid confusing ML!]            *)
(*                                                                           *)
(* binary-*                                                                  *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* binary-* (x y)                                                 *)
(*   (the number                                                             *)
(*        (if (numberp x)                                                    *)
(*            (if (numberp y)                                                *)
(*                ( * x y)                                                   *)
(*              (gv binary-* (x y) 0))                                       *)
(*          (gv binary-* (x y) 0))))                                         *)
(*****************************************************************************)
val mult_def =
 acl2Define "ACL2::BINARY-*" 
  `(mult (num x) (num y) = num(x*y)) /\
   (mult _       _       = int 0)`;

(*****************************************************************************)
(* ; *1* definition (not very helpful)::                                     *)
(* (defun-*1* < (x y)                                                        *)
(*  (if (and (rationalp x)                                                   *)
(*           (rationalp y))                                                  *)
(*      (< (the rational x) (the rational y))                                *)
(*    (gv < (x y)                                                            *)
(*        (let ((x1 (if (numberp x) x 0))                                    *)
(*              (y1 (if (numberp y) y 0)))                                   *)
(*          (or (< (realpart x1) (realpart y1))                              *)
(*              (and (= (realpart x1) (realpart y1))                         *)
(*                   (< (imagpart x1) (imagpart y1))))))))                   *)
(*****************************************************************************)
val less_def =
 acl2Define "COMMON-LISP::<"
  `(less (num(com xr xi)) (num(com yr yi)) = 
     if xr < yr 
      then t
      else (if xr = yr then (if xi < yi then t else nil) else nil))
   /\
   (less _ (num(com yr yi)) = 
     if rat_0 < yr 
      then t
      else (if rat_0 = yr then (if rat_0 < yi then t else nil) else nil))
   /\
   (less (num(com xr xi)) _ = 
     if xr < rat_0
      then t
      else (if xr = rat_0 then (if xi < rat_0 then t else nil) else nil))
   /\
   (less _ _ =  nil)`;

(*****************************************************************************)
(* unary--                                                                   *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* unary-- (x)                                                    *)
(*   (the number                                                             *)
(*        (if (numberp x)                                                    *)
(*            (- x)                                                          *)
(*          (gv unary-- (x) 0))))                                            *)
(*****************************************************************************)
val unary_minus_def =
 acl2Define "ACL2::UNARY--"
  `(unary_minus(num x) = num(COMPLEX_SUB com_0 x)) /\
   (unary_minus _      = int 0)`;

(*****************************************************************************)
(* unary-/                                                                   *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* unary-/ (x)                                                    *)
(*   (the number                                                             *)
(*        (if (and (numberp x) (not (= x 0)))                                *)
(*            (/ x)                                                          *)
(*          (gv unary-/ (x) 0))))                                            *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* unary-/ (x)                                                    *)
(*   (if (and (numberp x) (not (equal x 0)))                                 *)
(*       (/ x)                                                               *)
(*     0))                                                                   *)
(*****************************************************************************)
val reciprocal_def =
 acl2Define "ACL2::UNARY-/"
  `(reciprocal (num x) = 
     if x = com_0 then int 0 else num(COMPLEX_RECIPROCAL x))
   /\
   (reciprocal _ = int 0)`;

(*****************************************************************************)
(* consp                                                                     *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* consp (x)                                                      *)
(*   (consp x))                                                              *)
(*                                                                           *)
(*****************************************************************************)
val consp_def =
 acl2Define "COMMON-LISP::CONSP"
  `(consp(cons x y) = t) /\ (consp _ = nil)`;

(*****************************************************************************)
(* car                                                                       *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* car (x)                                                        *)
(*   (cond                                                                   *)
(*    ((consp x)                                                             *)
(*     (car x))                                                              *)
(*    ((null x)                                                              *)
(*     nil)                                                                  *)
(*    (t (gv car (x) nil))))                                                 *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* car (x)                                                        *)
(*   (if (consp x) (car x) nil))                                             *)
(*****************************************************************************)
val car_def =
 acl2Define "COMMON-LISP::CAR"
  `(car(cons x _) = x) /\ (car _ = nil)`;

(*****************************************************************************)
(* cdr                                                                       *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* cdr (x)                                                        *)
(*   (cond                                                                   *)
(*    ((consp x)                                                             *)
(*     (cdr x))                                                              *)
(*    ((null x)                                                              *)
(*     nil)                                                                  *)
(*    (t (gv cdr (x) nil))))                                                 *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* cdr (x)                                                        *)
(*   (if (consp x) (cdr x) nil))                                             *)
(*****************************************************************************)
val cdr_def =
 acl2Define "COMMON-LISP::CDR"
  `(cdr(cons _ y) = y) /\ (cdr _ = nil)`;

(*****************************************************************************)
(* realpart                                                                  *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* realpart (x)                                                   *)
(*   (if (numberp x)                                                         *)
(*       (realpart x)                                                        *)
(*     (gv realpart (x) 0)))                                                 *)
(*****************************************************************************)
val realpart_def =
 acl2Define "COMMON-LISP::REALPART"
  `(realpart(num(com a b)) = num(com a rat_0)) /\ 
   (realpart _             = int 0)`;

(*****************************************************************************)
(* imagpart                                                                  *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* imagpart (x)                                                   *)
(*   (if (numberp x)                                                         *)
(*       (imagpart x)                                                        *)
(*     (gv imagpart (x) 0)))                                                 *)
(*****************************************************************************)
val imagpart_def =
 acl2Define "COMMON-LISP::IMAGPART"
  `(imagpart(num(com a b)) = num(com b rat_0)) /\ 
   (imagpart _             = int 0)`;

(*****************************************************************************)
(* rationalp                                                                 *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* rationalp (x)                                                  *)
(*   (rationalp x))                                                          *)
(*****************************************************************************)
val rationalp_def =
 acl2Define "COMMON-LISP::RATIONALP"
  `(rationalp(num(com a b)) = if b = rat_0 then t else nil) /\
   (rationalp _             = nil)`;

(*****************************************************************************)
(* complex-rationalp                                                         *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* complex-rationalp (x)                                          *)
(*   (complexp x))                                                           *)
(*                                                                           *)
(* Complex-rationalp holds only of numbers that are not rational, i.e.,      *)
(* have a non-zero imaginary part.  Here is the ACL2 documentation for       *)
(* COMPLEX-RATIONALP, followed by the doc for COMPLEX (pointed to by the     *)
(* former, and perhaps also useful for you).                                 *)
(*                                                                           *)
(*                                                                           *)
(* COMPLEX-RATIONALP    recognizes complex rational numbers                  *)
(*                                                                           *)
(*                                                                           *)
(* Examples:                                                                 *)
(*  (complex-rationalp 3)       ; nil, as 3 is rational, not complex rational*)
(*  (complex-rationalp #c(3 0)) ; nil, since #c(3 0) is the same as 3        *)
(*  (complex-rationalp t)       ; nil                                        *)
(*  (complex-rationalp #c(3 1)) ; t, as #c(3 1) is the complex number 3 + i  *)
(*****************************************************************************)
val complex_rationalp_def =
 acl2Define "ACL2::COMPLEX-RATIONALP"
  `(complex_rationalp(num(com a b)) = if b = rat_0 then nil else t) 
   /\ 
   (complex_rationalp _ = nil)`;

(*****************************************************************************)
(* complex                                                                   *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* complex (x y)                                                  *)
(*   (complex (the rational (if (rationalp x) x (gv complex (x y) 0)))       *)
(*            (the rational (if (rationalp y) y (gv complex (x y) 0)))))     *)
(*                                                                           *)
(*                                                                           *)
(* COMPLEX    create an ACL2 number                                          *)
(*                                                                           *)
(*                                                                           *)
(*      Examples:                                                            *)
(*      (complex x 3) ; x + 3i, where i is the principal square root of -1   *)
(*      (complex x y) ; x + yi                                               *)
(*      (complex x 0) ; same as x, for rational numbers x                    *)
(*                                                                           *)
(*                                                                           *)
(* The function complex takes two rational number arguments and returns an   *)
(* ACL2 number.  This number will be of type (complex rational) [as defined  *)
(* in the Common Lisp language], except that if the second argument is       *)
(* zero, then complex returns its first argument.  The function              *)
(* complex-rationalp is a recognizer for complex rational numbers, i.e. for  *)
(* ACL2 numbers that are not rational numbers.                               *)
(*                                                                           *)
(* The reader macro #C (which is the same as #c) provides a convenient way   *)
(* for typing in complex numbers.  For explicit rational numbers x and y,    *)
(* #C(x y) is read to the same value as (complex x y).                       *)
(*                                                                           *)
(* The functions realpart and imagpart return the real and imaginary parts   *)
(* (respectively) of a complex (possibly rational) number.  So for example,  *)
(* (realpart #C(3 4)) = 3, (imagpart #C(3 4)) = 4, (realpart 3/4) = 3/4,     *)
(* and (imagpart 3/4) = 0.                                                   *)
(*                                                                           *)
(* The following built-in axiom may be useful for reasoning about complex    *)
(* numbers.                                                                  *)
(*                                                                           *)
(*      (defaxiom complex-definition                                         *)
(*        (implies (and (real/rationalp x)                                   *)
(*                      (real/rationalp y))                                  *)
(*                 (equal (complex x y)                                      *)
(*                        (+ x ( * #c(0 1) y))))                             *)
(*        :rule-classes nil)                                                 *)
(*                                                                           *)
(*                                                                           *)
(* A completion axiom that shows what complex returns on arguments           *)
(* violating its guard (which says that both arguments are rational          *)
(* numbers) is the following.                                                *)
(*                                                                           *)
(*      (equal (complex x y)                                                 *)
(*             (complex (if (rationalp x) x 0)                               *)
(*                      (if (rationalp y) y 0)))                             *)
(*****************************************************************************)
val complex_def =
 acl2Define "COMMON-LISP::COMPLEX"
  `(complex (num(com xr xi)) (num(com yr yi)) =
     num(com (if (xi = rat_0) then xr else rat_0) 
             (if (yi = rat_0) then yr else rat_0)))
   /\
   (complex (num(com xr xi)) _ = 
     num(com (if (xi = rat_0) then xr else rat_0) rat_0))
   /\
   (complex _ (num(com yr yi)) = 
     num(com rat_0 (if (yi = rat_0) then yr else rat_0)))
   /\
   (complex _ _ = int 0)`;

(*****************************************************************************)
(* integerp                                                                  *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* integerp (x)                                                   *)
(*   (integerp x))                                                           *)
(*****************************************************************************)
val integerp_def =
 acl2Define "COMMON-LISP::INTEGERP"
  `(integerp(num n) = if IS_INT n then t else nil) /\
   (integerp _      = nil)`;

(*****************************************************************************)
(* numerator                                                                 *)
(*                                                                           *)
(* ; *1* definition::                                                        *)
(* (defun-*1* numerator (x)                                                  *)
(*   (if (rationalp x)                                                       *)
(*       (numerator x)                                                       *)
(*     (gv numerator (x) 0)))                                                *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* numerator (x)                                                  *)
(*   (if (rationalp x)                                                       *)
(*       (numerator x)                                                       *)
(*     0))                                                                   *)
(*****************************************************************************)
val numerator_def =
 acl2Define "COMMON-LISP::NUMERATOR"
  `(numerator(num(com a b)) = 
     if b = rat_0 then int(reduced_nmr a) else int 0)
   /\
   (numerator _ = int 0)`;

(*****************************************************************************)
(* denominator                                                               *)
(*                                                                           *)
(* ; *1* definition::                                                        *)
(* (defun-*1* denominator (x)                                                *)
(*   (if (rationalp x)                                                       *)
(*       (denominator x)                                                     *)
(*     (gv denominator (x) 1)))                                              *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* denominator (x)                                                *)
(*   (if (rationalp x)                                                       *)
(*       (denominator x)                                                     *)
(*     1))                                                                   *)
(*****************************************************************************)
val denominator_def =
 acl2Define "COMMON-LISP::DENOMINATOR"
  `(denominator(num(com a b)) = 
     if b = rat_0 then int(reduced_dnm a) else int 1)
   /\
   (denominator _ = int 1)`;

(*****************************************************************************)
(* char-code                                                                 *)
(*                                                                           *)
(* ; *1* definition                                                          *)
(* (defun-*1* char-code (x)                                                  *)
(*   (if (characterp x)                                                      *)
(*       (char-code x)                                                       *)
(*     (gv char-code (x) 0))):                                               *)
(*****************************************************************************)
val char_code_def =
 acl2Define "COMMON-LISP::CHAR-CODE"
  `(char_code(chr c) = int (&(ORD c))) /\
   (char_code _      = int 0)`;

(*****************************************************************************)
(* code-char                                                                 *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* code-char (x)                                                  *)
(*   (if (and (integerp x)                                                   *)
(*            (>= x 0)                                                       *)
(*            (< x 256))                                                     *)
(*       (code-char x)                                                       *)
(*     (gv code-char (x) (code-char 0))))                                    *)
(*****************************************************************************)
val code_char_def =
 acl2Define "COMMON-LISP::CODE-CHAR"
  `(code_char(num(com a b)) = 
     if IS_INT(com a b) /\ (0 <= reduced_nmr a) /\ (reduced_nmr a < 256)
      then chr(CHR (Num(reduced_nmr a)))
      else chr(CHR 0))
   /\
   (code_char _ = chr(CHR 0))`;

(*****************************************************************************)
(* From axioms.lisp                                                          *)
(*                                                                           *)
(* ;         (if NIL y z) = z                                                *)
(*                                                                           *)
(* ; x/=NIL -> (if x y z) = y                                                *)
(*                                                                           *)
(* if                                                                        *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* if (x y z)                                                     *)
(*   (error "We just can't stand having a non-lazy IF around.                *)
(*           But we attempted ~%~ to call the executable counterpart         *)
(*           of IF on argument list ~s."                                     *)
(*          (list x y z)))                                                   *)
(*                                                                           *)
(* Can't overload "if" onto ``ACL2_IF`` because of HOL's                     *)
(* `if ... then ... else` construct. Using "ite" instead.                    *)
(*****************************************************************************)
val ite_def =
 acl2Define "COMMON-LISP::IF"
  `ite x (y:sexp) (z:sexp) = if x = nil then z else y`;

(*****************************************************************************)
(* If f : 'a -> sexp then list_to_sexp f : num list : 'a list -> sexp.       *)
(*                                                                           *)
(* For example:                                                              *)
(*                                                                           *)
(* |- list_to_sexp num [1; 2; 3] =                                           *)
(*     cons (num 1) (cons (num 2) (cons (num 3) (sym "COMMON-LISP" "NIL")))  *)
(*****************************************************************************)
val list_to_sexp_def =
 Define
  `(list_to_sexp f [] = nil) /\ 
   (list_to_sexp f (x::l) = cons (f x) (list_to_sexp f l))`;

(*****************************************************************************)
(* coerce                                                                    *)
(*                                                                           *)
(* ; First, we nee to translate this ACL2 definition:                        *)
(*                                                                           *)
(* (defun make-character-list (x)                                            *)
(*   (cond ((atom x) nil)                                                    *)
(*         ((characterp (car x))                                             *)
(*          (cons (car x) (make-character-list (cdr x))))                    *)
(*         (t                                                                *)
(*          (cons (code-char 0) (make-character-list (cdr x))))))            *)
(*                                                                           *)
(* ; We also require HOL functions coerce_string_to_list and                 *)
(* ; coerce_list_to_string (not written here) that coerce a string (e.g.,    *)
(* ; "abc") to an SEXP list (e.g., cons 'a' (cons 'b' (cons 'c' nil)))       *)
(* ; and vice-versa, respectively.                                           *)
(*                                                                           *)
(* ; *1* definition (not very helpful):                                      *)
(* (defun-*1* coerce (x y)                                                   *)
(*   (cond                                                                   *)
(*    ((equal y 'list)                                                       *)
(*     (if (stringp x)                                                       *)
(*         (coerce x 'list)                                                  *)
(*       (gv coerce (x y) nil)))                                             *)
(*    ((character-listp x)                                                   *)
(*     (if (equal y 'string)                                                 *)
(*         (coerce x 'string)                                                *)
(*       (gv coerce (x y) (coerce x 'string))))                              *)
(*    (t                                                                     *)
(*     (gv coerce (x y)                                                      *)
(*         (coerce (make-character-list x) 'string)))))                      *)
(*****************************************************************************)

(*****************************************************************************)
(* (defun make-character-list (x)                                            *)
(*   (cond ((atom x) nil)                                                    *)
(*         ((characterp (car x))                                             *)
(*          (cons (car x) (make-character-list (cdr x))))                    *)
(*         (t                                                                *)
(*          (cons (code-char 0) (make-character-list (cdr x))))))            *)
(*****************************************************************************)
val make_character_list_def =
 Define
  `(make_character_list(cons (chr c) y) = 
     (cons (chr c) (make_character_list y)))
   /\
   (make_character_list(cons x y) = 
     (cons (code_char(int 0)) (make_character_list y))) 
   /\
   (make_character_list _ = nil)`;

(*****************************************************************************)
(* "abc" |--> (cons (chr #"a") (cons (chr #"b") (cons (chr #"c") nil)))      *)
(*                                                                           *)
(* list_to_sexp maps a function down a HOL list and then conses up an        *)
(* s-expression from the resulting list. For example:                        *)
(*                                                                           *)
(*   list_to_sexp chr [a; b; c] =                                            *)
(*    cons (chr a) (cons (chr b) (cons (chr c) (sym "COMMON-LISP" "NIL")))   *)
(*                                                                           *)
(* EXPLODE explodes a HOL string into a HOL list of characters.              *)
(*****************************************************************************)
val coerce_string_to_list_def =
 Define
  `coerce_string_to_list s = list_to_sexp chr (EXPLODE s)`;

(*****************************************************************************)
(* (cons (chr #"a") (cons (chr #"b") (cons (chr #"c") nil))) |--> "abc"      *)
(*                                                                           *)
(* STRING : char->string->string  is HOL's string-cons function.             *)
(*****************************************************************************)
val coerce_list_to_string_def =
 Define
  `(coerce_list_to_string(cons (chr c) y) =
     STRING c (coerce_list_to_string y))
   /\
   (coerce_list_to_string _ = "")`;

val coerce_def =
 acl2Define "COMMON-LISP::COERCE"
  `(coerce (str s) y =
     if y = sym "COMMON-LISP" "LIST"
      then coerce_string_to_list s
      else str "")
   /\
   (coerce (cons a x) y =
     if y = sym "COMMON-LISP" "LIST"
      then nil
      else str(coerce_list_to_string(make_character_list(cons a x))))
   /\
   (coerce _ y = if y = sym "COMMON-LISP" "LIST" then nil else str "")`;

(*****************************************************************************)
(* The following function represents an ACL2 package system, but is not      *)
(* itself an ACL2 primitive; rather, it is used in the translation (see      *)
(* for example intern-in-package-of-symbol).                                 *)
(*                                                                           *)
(*   BASIC_INTERN : string -> string -> SEXP                                 *)
(*                                                                           *)
(* An ACL2 data structure is available to help with the definition of        *)
(* BASIC_INTERN.  For example, after evaluation of (defpkg "FOO" '(a         *)
(* b)), the form (known-package-alist state) evaluates to the following      *)
(* (which I have abbreviated, omitting irrelevant or not-useful info).       *)
(* Note that each package is associated with a list of imported              *)
(* symbols.  For example, "FOO" imports two symbols, represented in HOL      *)
(* as (sym "ACL2" "A") and (sym "ACL2" "B").                                 *)
(*                                                                           *)
(* (("FOO" (A B) ...)                                                        *)
(*  ("ACL2-USER" (& *ACL2-EXPORTS* ...))                                     *)
(*  ("ACL2-PC" NIL ...)                                                      *)
(*  ("ACL2-INPUT-CHANNEL" NIL NIL NIL)                                       *)
(*  ("ACL2-OUTPUT-CHANNEL" NIL NIL NIL)                                      *)
(*  ("ACL2" (&ALLOW-OTHER-KEYS *PRINT-MISER-WIDTH* ...) NIL NIL)             *)
(*  ("COMMON-LISP" NIL NIL NIL)                                              *)
(*  ("KEYWORD" NIL NIL NIL))                                                 *)
(*                                                                           *)
(* Let us turn now to the definition of BASIC_INTERN.                        *)
(*                                                                           *)
(* If pkg_name is the name of a known package and symbol_name is the         *)
(* name of a symbol imported into that package from some other package,      *)
(* named old_pkg, then:                                                      *)
(*                                                                           *)
(*   BASIC_INTERN symbol_name pkg_name = (sym old_pkg symbol_name)           *)
(*                                                                           *)
(* For example, given the package system shown above,                        *)
(* BASIC_INTERN "A" "FOO" = (sym "ACL2" "A").                                *)
(*                                                                           *)
(* Otherwise, if pkg_name is the name of a known package (from the ACL2      *)
(* data structure as shown above), then:                                     *)
(*                                                                           *)
(*   BASIC_INTERN symbol_name pkg_name = (sym pkg_name symbol_name)          *)
(*                                                                           *)
(* Finally, if pkg_name is not the name of a known package, we return        *)
(* an arbitrary value.                                                       *)
(*****************************************************************************)

(*****************************************************************************)
(* ACL2_PACKAGE_ALIST contains a list of triples                             *)
(*                                                                           *)
(*   (symbol-name , known-pkg-name , actual-pkg-name)                        *)
(*                                                                           *)
(* The idea is that when symbol-name is interned into known-pkg-name, the    *)
(* resulting symbol's package name is actual-pkg-name.  That is, the         *)
(* symbol with name symbol-name and package-name actual-pkg-name is          *)
(* imported into package known-pkg-name.                                     *)
(*****************************************************************************)

(*****************************************************************************)
(* Building a term directly out of a slurped in ACL2 package structure       *)
(* (e.g. kpa-v2-9-3.ml) breaks the HOL compiler. We therefore fold in the    *)
(* abbreviations below (this idea due to Konrad). It is strange that         *)
(* rewriting the big term is no problem, but compiling it breaks.            *)
(*****************************************************************************)
val ACL2_CL_def     = Define `ACL2_CL      = ("ACL2", "COMMON-LISP")`;
val ACL2_USER_def   = Define `ACL2_USER    = ("ACL2-USER" , "ACL2")`;
val ACL_USER_CL_def = Define `ACL2_USER_CL = ("ACL2-USER" , "COMMON-LISP")`;

(*****************************************************************************)
(* Convert imported ACL2 package structure:                                  *)
(*                                                                           *)
(*  [                                                                        *)
(*  ("&", "ACL2-USER", "ACL2"),                                              *)
(*  ("*ACL2-EXPORTS*", "ACL2-USER", "ACL2"),                                 *)
(*  ...                                                                      *)
(*  ("VALUES", "ACL2", "COMMON-LISP"),                                       *)
(*  ("ZEROP", "ACL2", "COMMON-LISP")                                         *)
(*  ]                                                                        *)
(*                                                                           *)
(* to corresponding term, then fold in ACL2_CL_def, ACL2_USER_def and        *)
(* ACL_USER_CL_def using REWRITE_CONV, then extract the simplified term.     *)
(* Used to define ACL2_PACKAGE_ALIST                                         *)
(*****************************************************************************)

fun make_package_structure_term l =
 rhs
  (concl
    (REWRITE_CONV
      (map GSYM [ACL2_CL_def,ACL2_USER_def,ACL_USER_CL_def])
      (mk_list
       (map
         (fn (s1,s2,s3) =>
           mk_pair(fromMLstring s1, mk_pair(fromMLstring s2, fromMLstring s3)))
        l,
        ``:string # string # string``))));

val ACL2_PACKAGE_ALIST =
 time
  Define
  `ACL2_PACKAGE_ALIST =
    ^(make_package_structure_term
(* Following List is cut and pasted from ACL2 generated file kpa-v2-9-3.ml *)
[
("&", "ACL2-USER", "ACL2"),
("*ACL2-EXPORTS*", "ACL2-USER", "ACL2"),
("*COMMON-LISP-SPECIALS-AND-CONSTANTS*", "ACL2-USER", "ACL2"),
("*COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*", "ACL2-USER", "ACL2"),
("*MAIN-LISP-PACKAGE-NAME*", "ACL2-USER", "ACL2"),
("*STANDARD-CHARS*", "ACL2-USER", "ACL2"),
("*STANDARD-CI*", "ACL2-USER", "ACL2"),
("*STANDARD-CO*", "ACL2-USER", "ACL2"),
("*STANDARD-OI*", "ACL2-USER", "ACL2"),
("32-BIT-INTEGER-LISTP", "ACL2-USER", "ACL2"),
("32-BIT-INTEGER-LISTP-FORWARD-TO-INTEGER-LISTP", "ACL2-USER", "ACL2"),
("32-BIT-INTEGER-STACK", "ACL2-USER", "ACL2"),
("32-BIT-INTEGER-STACK-LENGTH", "ACL2-USER", "ACL2"),
("32-BIT-INTEGER-STACK-LENGTH1", "ACL2-USER", "ACL2"),
("32-BIT-INTEGERP", "ACL2-USER", "ACL2"),
("32-BIT-INTEGERP-FORWARD-TO-INTEGERP", "ACL2-USER", "ACL2"),
("<-ON-OTHERS", "ACL2-USER", "ACL2"),
("?-FN", "ACL2-USER", "ACL2"),
("@", "ACL2-USER", "ACL2"),
("ABORT!", "ACL2-USER", "ACL2"),
("ACCUMULATED-PERSISTENCE", "ACL2-USER", "ACL2"),
("ACL2-COUNT", "ACL2-USER", "ACL2"),
("ACL2-INPUT-CHANNEL-PACKAGE", "ACL2-USER", "ACL2"),
("ACL2-NUMBERP", "ACL2-USER", "ACL2"),
("ACL2-OUTPUT-CHANNEL-PACKAGE", "ACL2-USER", "ACL2"),
("ACL2-PACKAGE", "ACL2-USER", "ACL2"),
("ADD-DEFAULT-HINTS", "ACL2-USER", "ACL2"),
("ADD-DEFAULT-HINTS!", "ACL2-USER", "ACL2"),
("ADD-INVISIBLE-FNS", "ACL2-USER", "ACL2"),
("ADD-MACRO-ALIAS", "ACL2-USER", "ACL2"),
("ADD-NTH-ALIAS", "ACL2-USER", "ACL2"),
("ADD-PAIR", "ACL2-USER", "ACL2"),
("ADD-PAIR-PRESERVES-ALL-BOUNDP", "ACL2-USER", "ACL2"),
("ADD-TIMERS", "ACL2-USER", "ACL2"),
("ADD-TO-SET-EQ", "ACL2-USER", "ACL2"),
("ADD-TO-SET-EQL", "ACL2-USER", "ACL2"),
("ADD-TO-SET-EQUAL", "ACL2-USER", "ACL2"),
("ALISTP", "ACL2-USER", "ACL2"),
("ALISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("ALL-BOUNDP", "ACL2-USER", "ACL2"),
("ALL-BOUNDP-PRESERVES-ASSOC", "ACL2-USER", "ACL2"),
("ALL-VARS", "ACL2-USER", "ACL2"),
("ALL-VARS1", "ACL2-USER", "ACL2"),
("ALL-VARS1-LST", "ACL2-USER", "ACL2"),
("ALPHA-CHAR-P-FORWARD-TO-CHARACTERP", "ACL2-USER", "ACL2"),
("AND-MACRO", "ACL2-USER", "ACL2"),
("AREF-32-BIT-INTEGER-STACK", "ACL2-USER", "ACL2"),
("AREF-T-STACK", "ACL2-USER", "ACL2"),
("AREF1", "ACL2-USER", "ACL2"),
("AREF2", "ACL2-USER", "ACL2"),
("ARGS", "ACL2-USER", "ACL2"),
("ARRAY1P", "ACL2-USER", "ACL2"),
("ARRAY1P-CONS", "ACL2-USER", "ACL2"),
("ARRAY1P-FORWARD", "ACL2-USER", "ACL2"),
("ARRAY1P-LINEAR", "ACL2-USER", "ACL2"),
("ARRAY2P", "ACL2-USER", "ACL2"),
("ARRAY2P-CONS", "ACL2-USER", "ACL2"),
("ARRAY2P-FORWARD", "ACL2-USER", "ACL2"),
("ARRAY2P-LINEAR", "ACL2-USER", "ACL2"),
("ASET-32-BIT-INTEGER-STACK", "ACL2-USER", "ACL2"),
("ASET-T-STACK", "ACL2-USER", "ACL2"),
("ASET1", "ACL2-USER", "ACL2"),
("ASET2", "ACL2-USER", "ACL2"),
("ASSIGN", "ACL2-USER", "ACL2"),
("ASSOC-ADD-PAIR", "ACL2-USER", "ACL2"),
("ASSOC-EQ", "ACL2-USER", "ACL2"),
("ASSOC-EQ-EQUAL", "ACL2-USER", "ACL2"),
("ASSOC-EQ-EQUAL-ALISTP", "ACL2-USER", "ACL2"),
("ASSOC-EQUAL", "ACL2-USER", "ACL2"),
("ASSOC-KEYWORD", "ACL2-USER", "ACL2"),
("ASSOC-STRING-EQUAL", "ACL2-USER", "ACL2"),
("ASSOC2", "ACL2-USER", "ACL2"),
("ASSOCIATIVITY-OF-*", "ACL2-USER", "ACL2"),
("ASSOCIATIVITY-OF-+", "ACL2-USER", "ACL2"),
("ASSUME", "ACL2-USER", "ACL2"),
("ATOM-LISTP", "ACL2-USER", "ACL2"),
("ATOM-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("BIG-CLOCK-ENTRY", "ACL2-USER", "ACL2"),
("BIG-CLOCK-NEGATIVE-P", "ACL2-USER", "ACL2"),
("BINARY-*", "ACL2-USER", "ACL2"),
("BINARY-+", "ACL2-USER", "ACL2"),
("BINARY-APPEND", "ACL2-USER", "ACL2"),
("BIND-FREE", "ACL2-USER", "ACL2"),
("BINOP-TABLE", "ACL2-USER", "ACL2"),
("ADD-BINOP", "ACL2-USER", "ACL2"),
("REMOVE-BINOP", "ACL2-USER", "ACL2"),
("REMOVE-INVISIBLE-FNS", "ACL2-USER", "ACL2"),
("BOOLEAN-LISTP", "ACL2-USER", "ACL2"),
("BOOLEAN-LISTP-CONS", "ACL2-USER", "ACL2"),
("BOOLEAN-LISTP-FORWARD", "ACL2-USER", "ACL2"),
("BOOLEAN-LISTP-FORWARD-TO-SYMBOL-LISTP", "ACL2-USER", "ACL2"),
("BOOLEANP", "ACL2-USER", "ACL2"),
("BOOLEANP-CHARACTERP", "ACL2-USER", "ACL2"),
("BOOLEANP-COMPOUND-RECOGNIZER", "ACL2-USER", "ACL2"),
("BOUNDED-INTEGER-ALISTP", "ACL2-USER", "ACL2"),
("BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP", "ACL2-USER", "ACL2"),
("BOUNDED-INTEGER-ALISTP2", "ACL2-USER", "ACL2"),
("BOUNDP-GLOBAL", "ACL2-USER", "ACL2"),
("BOUNDP-GLOBAL1", "ACL2-USER", "ACL2"),
("BRR", "ACL2-USER", "ACL2"),
("BRR@", "ACL2-USER", "ACL2"),
("BUILD-STATE1", "ACL2-USER", "ACL2"),
("CAR-CDR-ELIM", "ACL2-USER", "ACL2"),
("CAR-CONS", "ACL2-USER", "ACL2"),
("CASE-LIST", "ACL2-USER", "ACL2"),
("CASE-LIST-CHECK", "ACL2-USER", "ACL2"),
("CASE-MATCH", "ACL2-USER", "ACL2"),
("CASE-SPLIT", "ACL2-USER", "ACL2"),
("CASE-TEST", "ACL2-USER", "ACL2"),
("CBD", "ACL2-USER", "ACL2"),
("CDR-CONS", "ACL2-USER", "ACL2"),
("CDRN", "ACL2-USER", "ACL2"),
("CERTIFY-BOOK", "ACL2-USER", "ACL2"),
("CERTIFY-BOOK!", "ACL2-USER", "ACL2"),
("CHAR-CODE-CODE-CHAR-IS-IDENTITY", "ACL2-USER", "ACL2"),
("CHAR-CODE-LINEAR", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-APPEND", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-COERCE", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-REMOVE-DUPLICATES-EQL", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-REVAPPEND", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-STRING-DOWNCASE-1", "ACL2-USER", "ACL2"),
("CHARACTER-LISTP-STRING-UPCASE1-1", "ACL2-USER", "ACL2"),
("CHARACTERP-CHAR-DOWNCASE", "ACL2-USER", "ACL2"),
("CHARACTERP-CHAR-UPCASE", "ACL2-USER", "ACL2"),
("CHARACTERP-NTH", "ACL2-USER", "ACL2"),
("CHARACTERP-PAGE", "ACL2-USER", "ACL2"),
("CHARACTERP-RUBOUT", "ACL2-USER", "ACL2"),
("CHARACTERP-TAB", "ACL2-USER", "ACL2"),
("CHECK-VARS-NOT-FREE", "ACL2-USER", "ACL2"),
("CHECKPOINT-FORCED-GOALS", "ACL2-USER", "ACL2"),
("CLAUSE", "ACL2-USER", "ACL2"),
("CLOSE-INPUT-CHANNEL", "ACL2-USER", "ACL2"),
("CLOSE-OUTPUT-CHANNEL", "ACL2-USER", "ACL2"),
("CLOSURE", "ACL2-USER", "ACL2"),
("CODE-CHAR-CHAR-CODE-IS-IDENTITY", "ACL2-USER", "ACL2"),
("CODE-CHAR-TYPE", "ACL2-USER", "ACL2"),
("COERCE-INVERSE-1", "ACL2-USER", "ACL2"),
("COERCE-INVERSE-2", "ACL2-USER", "ACL2"),
("COERCE-OBJECT-TO-STATE", "ACL2-USER", "ACL2"),
("COERCE-STATE-TO-OBJECT", "ACL2-USER", "ACL2"),
("COMMUTATIVITY-OF-*", "ACL2-USER", "ACL2"),
("COMMUTATIVITY-OF-+", "ACL2-USER", "ACL2"),
("COMP", "ACL2-USER", "ACL2"),
("COMPLETION-OF-*", "ACL2-USER", "ACL2"),
("COMPLETION-OF-+", "ACL2-USER", "ACL2"),
("COMPLETION-OF-<", "ACL2-USER", "ACL2"),
("COMPLETION-OF-CAR", "ACL2-USER", "ACL2"),
("COMPLETION-OF-CDR", "ACL2-USER", "ACL2"),
("COMPLETION-OF-CHAR-CODE", "ACL2-USER", "ACL2"),
("COMPLETION-OF-CODE-CHAR", "ACL2-USER", "ACL2"),
("COMPLETION-OF-COERCE", "ACL2-USER", "ACL2"),
("COMPLETION-OF-COMPLEX", "ACL2-USER", "ACL2"),
("COMPLETION-OF-DENOMINATOR", "ACL2-USER", "ACL2"),
("COMPLETION-OF-IMAGPART", "ACL2-USER", "ACL2"),
("COMPLETION-OF-INTERN-IN-PACKAGE-OF-SYMBOL", "ACL2-USER", "ACL2"),
("COMPLETION-OF-NUMERATOR", "ACL2-USER", "ACL2"),
("COMPLETION-OF-REALPART", "ACL2-USER", "ACL2"),
("COMPLETION-OF-SYMBOL-NAME", "ACL2-USER", "ACL2"),
("COMPLETION-OF-SYMBOL-PACKAGE-NAME", "ACL2-USER", "ACL2"),
("COMPLETION-OF-UNARY-/", "ACL2-USER", "ACL2"),
("COMPLETION-OF-UNARY-MINUS", "ACL2-USER", "ACL2"),
("COMPLEX-0", "ACL2-USER", "ACL2"),
("COMPLEX-DEFINITION", "ACL2-USER", "ACL2"),
("COMPLEX-EQUAL", "ACL2-USER", "ACL2"),
("COMPLEX-IMPLIES1", "ACL2-USER", "ACL2"),
("COMPLEX-RATIONALP", "ACL2-USER", "ACL2"),
("COMPRESS1", "ACL2-USER", "ACL2"),
("COMPRESS11", "ACL2-USER", "ACL2"),
("COMPRESS2", "ACL2-USER", "ACL2"),
("COMPRESS21", "ACL2-USER", "ACL2"),
("COMPRESS211", "ACL2-USER", "ACL2"),
("COND-CLAUSESP", "ACL2-USER", "ACL2"),
("COND-MACRO", "ACL2-USER", "ACL2"),
("CONS-EQUAL", "ACL2-USER", "ACL2"),
("CONSP-ASSOC", "ACL2-USER", "ACL2"),
("CONSP-ASSOC-EQ", "ACL2-USER", "ACL2"),
("CURRENT-PACKAGE", "ACL2-USER", "ACL2"),
("CURRENT-THEORY", "ACL2-USER", "ACL2"),
("CW-GSTACK", "ACL2-USER", "ACL2"),
("CW", "ACL2-USER", "ACL2"),
("DECREMENT-BIG-CLOCK", "ACL2-USER", "ACL2"),
("DEFABBREV", "ACL2-USER", "ACL2"),
("DEFAULT", "ACL2-USER", "ACL2"),
("DEFAULT-*-1", "ACL2-USER", "ACL2"),
("DEFAULT-*-2", "ACL2-USER", "ACL2"),
("DEFAULT-+-1", "ACL2-USER", "ACL2"),
("DEFAULT-+-2", "ACL2-USER", "ACL2"),
("DEFAULT-<-1", "ACL2-USER", "ACL2"),
("DEFAULT-<-2", "ACL2-USER", "ACL2"),
("DEFAULT-CAR", "ACL2-USER", "ACL2"),
("DEFAULT-CDR", "ACL2-USER", "ACL2"),
("DEFAULT-CHAR-CODE", "ACL2-USER", "ACL2"),
("DEFAULT-COERCE-1", "ACL2-USER", "ACL2"),
("DEFAULT-COERCE-2", "ACL2-USER", "ACL2"),
("DEFAULT-COERCE-3", "ACL2-USER", "ACL2"),
("DEFAULT-COMPILE-FNS", "ACL2-USER", "ACL2"),
("DEFAULT-COMPLEX-1", "ACL2-USER", "ACL2"),
("DEFAULT-COMPLEX-2", "ACL2-USER", "ACL2"),
("DEFAULT-DEFUN-MODE", "ACL2-USER", "ACL2"),
("DEFAULT-DEFUN-MODE-FROM-STATE", "ACL2-USER", "ACL2"),
("DEFAULT-DENOMINATOR", "ACL2-USER", "ACL2"),
("DEFAULT-IMAGPART", "ACL2-USER", "ACL2"),
("DEFAULT-MEASURE-FUNCTION", "ACL2-USER", "ACL2"),
("DEFAULT-NUMERATOR", "ACL2-USER", "ACL2"),
("DEFAULT-REALPART", "ACL2-USER", "ACL2"),
("DEFAULT-SYMBOL-NAME", "ACL2-USER", "ACL2"),
("DEFAULT-SYMBOL-PACKAGE-NAME", "ACL2-USER", "ACL2"),
("DEFAULT-UNARY-/", "ACL2-USER", "ACL2"),
("DEFAULT-UNARY-MINUS", "ACL2-USER", "ACL2"),
("DEFAULT-VERIFY-GUARDS-EAGERNESS", "ACL2-USER", "ACL2"),
("DEFAULT-WELL-FOUNDED-RELATION", "ACL2-USER", "ACL2"),
("DEFAXIOM", "ACL2-USER", "ACL2"),
("DEFCHOOSE", "ACL2-USER", "ACL2"),
("DEFCONG", "ACL2-USER", "ACL2"),
("DEFCONST", "ACL2-USER", "ACL2"),
("DEFDOC", "ACL2-USER", "ACL2"),
("DEFEQUIV", "ACL2-USER", "ACL2"),
("DEFEVALUATOR", "ACL2-USER", "ACL2"),
("DEFEXEC", "ACL2-USER", "ACL2"),
("DEFINE-PC-ATOMIC-MACRO", "ACL2-USER", "ACL2"),
("DEFINE-PC-HELP", "ACL2-USER", "ACL2"),
("DEFINE-PC-MACRO", "ACL2-USER", "ACL2"),
("DEFLABEL", "ACL2-USER", "ACL2"),
("DEFPKG", "ACL2-USER", "ACL2"),
("DEFREFINEMENT", "ACL2-USER", "ACL2"),
("DEFSTOBJ", "ACL2-USER", "ACL2"),
("DEFSTUB", "ACL2-USER", "ACL2"),
("DEFTHEORY", "ACL2-USER", "ACL2"),
("DEFTHM", "ACL2-USER", "ACL2"),
("DEFTHMD", "ACL2-USER", "ACL2"),
("DEFUND", "ACL2-USER", "ACL2"),
("DEFUN-SK", "ACL2-USER", "ACL2"),
("DEFUNS", "ACL2-USER", "ACL2"),
("DELETE-PAIR", "ACL2-USER", "ACL2"),
("DIGIT-TO-CHAR", "ACL2-USER", "ACL2"),
("DIMENSIONS", "ACL2-USER", "ACL2"),
("DISABLE", "ACL2-USER", "ACL2"),
("DISABLE-FORCING", "ACL2-USER", "ACL2"),
("DISABLEDP", "ACL2-USER", "ACL2"),
("DISTRIBUTIVITY", "ACL2-USER", "ACL2"),
("DOC", "ACL2-USER", "ACL2"),
("DOC!", "ACL2-USER", "ACL2"),
("DOCS", "ACL2-USER", "ACL2"),
("DUPLICATES", "ACL2-USER", "ACL2"),
("E/D", "ACL2-USER", "ACL2"),
("E0-ORD-<", "ACL2-USER", "ACL2"),
("E0-ORDINALP", "ACL2-USER", "ACL2"),
("ELIMINATE-DESTRUCTORS", "ACL2-USER", "ACL2"),
("ELIMINATE-IRRELEVANCE", "ACL2-USER", "ACL2"),
("ENABLE", "ACL2-USER", "ACL2"),
("ENABLE-FORCING", "ACL2-USER", "ACL2"),
("ENCAPSULATE", "ACL2-USER", "ACL2"),
("EQLABLE-ALISTP", "ACL2-USER", "ACL2"),
("EQLABLE-ALISTP-FORWARD-TO-ALISTP", "ACL2-USER", "ACL2"),
("EQLABLE-LISTP", "ACL2-USER", "ACL2"),
("EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP", "ACL2-USER", "ACL2"),
("EQLABLEP", "ACL2-USER", "ACL2"),
("EQLABLEP-RECOG", "ACL2-USER", "ACL2"),
("EQUAL-CHAR-CODE", "ACL2-USER", "ACL2"),
("ER", "ACL2-USER", "ACL2"),
("ER-PROGN", "ACL2-USER", "ACL2"),
("ER-PROGN-FN", "ACL2-USER", "ACL2"),
("EVENS", "ACL2-USER", "ACL2"),
("EVENT", "ACL2-USER", "ACL2"),
("EXECUTABLE-COUNTERPART-THEORY", "ACL2-USER", "ACL2"),
("EXPLODE-ATOM", "ACL2-USER", "ACL2"),
("EXPLODE-NONNEGATIVE-INTEGER", "ACL2-USER", "ACL2"),
("EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE", "ACL2-USER", "ACL2"),
("EXTEND-32-BIT-INTEGER-STACK", "ACL2-USER", "ACL2"),
("EXTEND-T-STACK", "ACL2-USER", "ACL2"),
("EXTEND-WORLD", "ACL2-USER", "ACL2"),
("FERTILIZE", "ACL2-USER", "ACL2"),
("FGETPROP", "ACL2-USER", "ACL2"),
("FILE-CLOCK", "ACL2-USER", "ACL2"),
("FILE-CLOCK-P", "ACL2-USER", "ACL2"),
("FILE-CLOCK-P-FORWARD-TO-INTEGERP", "ACL2-USER", "ACL2"),
("FIRST-N-AC", "ACL2-USER", "ACL2"),
("FIX", "ACL2-USER", "ACL2"),
("FIX-TRUE-LIST", "ACL2-USER", "ACL2"),
("FMS", "ACL2-USER", "ACL2"),
("FMT", "ACL2-USER", "ACL2"),
("FMT-TO-COMMENT-WINDOW", "ACL2-USER", "ACL2"),
("FMT1", "ACL2-USER", "ACL2"),
("FORCE", "ACL2-USER", "ACL2"),
("FUNCTION-SYMBOLP", "ACL2-USER", "ACL2"),
("FUNCTION-THEORY", "ACL2-USER", "ACL2"),
("GENERALIZE", "ACL2-USER", "ACL2"),
("GET-GLOBAL", "ACL2-USER", "ACL2"),
("GET-TIMER", "ACL2-USER", "ACL2"),
("GETPROP-DEFAULT", "ACL2-USER", "ACL2"),
("GETPROPS", "ACL2-USER", "ACL2"),
("GETPROPS1", "ACL2-USER", "ACL2"),
("GLOBAL-TABLE", "ACL2-USER", "ACL2"),
("GLOBAL-TABLE-CARS", "ACL2-USER", "ACL2"),
("GLOBAL-TABLE-CARS1", "ACL2-USER", "ACL2"),
("GLOBAL-VAL", "ACL2-USER", "ACL2"),
("GOOD-BYE", "ACL2-USER", "ACL2"),
("GOOD-DEFUN-MODE-P", "ACL2-USER", "ACL2"),
("GROUND-ZERO", "ACL2-USER", "ACL2"),
("HARD-ERROR", "ACL2-USER", "ACL2"),
("HAS-PROPSP", "ACL2-USER", "ACL2"),
("HAS-PROPSP1", "ACL2-USER", "ACL2"),
("HEADER", "ACL2-USER", "ACL2"),
("HELP", "ACL2-USER", "ACL2"),
("HIDE", "ACL2-USER", "ACL2"),
("I-AM-HERE", "ACL2-USER", "ACL2"),
("ID", "ACL2-USER", "ACL2"),
("IDATES", "ACL2-USER", "ACL2"),
("IF*", "ACL2-USER", "ACL2"),
("IFF", "ACL2-USER", "ACL2"),
("IFF-IMPLIES-EQUAL-IMPLIES-1", "ACL2-USER", "ACL2"),
("IFF-IMPLIES-EQUAL-IMPLIES-2", "ACL2-USER", "ACL2"),
("IFF-IMPLIES-EQUAL-NOT", "ACL2-USER", "ACL2"),
("IFF-IS-AN-EQUIVALENCE", "ACL2-USER", "ACL2"),
("IFIX", "ACL2-USER", "ACL2"),
("ILLEGAL", "ACL2-USER", "ACL2"),
("IMAGPART-COMPLEX", "ACL2-USER", "ACL2"),
("IMMEDIATE-FORCE-MODEP", "ACL2-USER", "ACL2"),
("IMPLIES", "ACL2-USER", "ACL2"),
("IMPROPER-CONSP", "ACL2-USER", "ACL2"),
("IN-THEORY", "ACL2-USER", "ACL2"),
("IN-ARITHMETIC-THEORY", "ACL2-USER", "ACL2"),
("INCLUDE-BOOK", "ACL2-USER", "ACL2"),
("INCOMPATIBLE", "ACL2-USER", "ACL2"),
("INCREMENT-TIMER", "ACL2-USER", "ACL2"),
("INDUCT", "ACL2-USER", "ACL2"),
("INT=", "ACL2-USER", "ACL2"),
("INTEGER-0", "ACL2-USER", "ACL2"),
("INTEGER-1", "ACL2-USER", "ACL2"),
("INTEGER-ABS", "ACL2-USER", "ACL2"),
("INTEGER-IMPLIES-RATIONAL", "ACL2-USER", "ACL2"),
("INTEGER-LISTP", "ACL2-USER", "ACL2"),
("INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP", "ACL2-USER", "ACL2"),
("INTEGER-STEP", "ACL2-USER", "ACL2"),
("INTERN$", "ACL2-USER", "ACL2"),
("INTERN-IN-PACKAGE-OF-SYMBOL", "ACL2-USER", "ACL2"),
("INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME", "ACL2-USER", "ACL2"),
("INTERSECTION-EQ", "ACL2-USER", "ACL2"),
("INTERSECTION-THEORIES", "ACL2-USER", "ACL2"),
("INTERSECTP-EQ", "ACL2-USER", "ACL2"),
("INTERSECTP-EQUAL", "ACL2-USER", "ACL2"),
("INVERSE-OF-*", "ACL2-USER", "ACL2"),
("INVERSE-OF-+", "ACL2-USER", "ACL2"),
("INVISIBLE-FNS-TABLE", "ACL2-USER", "ACL2"),
("KEYWORD-PACKAGE", "ACL2-USER", "ACL2"),
("KEYWORD-VALUE-LISTP", "ACL2-USER", "ACL2"),
("KEYWORD-VALUE-LISTP-ASSOC-KEYWORD", "ACL2-USER", "ACL2"),
("KEYWORD-VALUE-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("KEYWORDP-FORWARD-TO-SYMBOLP", "ACL2-USER", "ACL2"),
("KNOWN-PACKAGE-ALIST", "ACL2-USER", "ACL2"),
("KNOWN-PACKAGE-ALISTP", "ACL2-USER", "ACL2"),
("KNOWN-PACKAGE-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP", "ACL2-USER",
"ACL2"),
("LD", "ACL2-USER", "ACL2"),
("LD-ERROR-ACTION", "ACL2-USER", "ACL2"),
("LD-ERROR-TRIPLES", "ACL2-USER", "ACL2"),
("LD-KEYWORD-ALIASES", "ACL2-USER", "ACL2"),
("LD-POST-EVAL-PRINT", "ACL2-USER", "ACL2"),
("LD-PRE-EVAL-FILTER", "ACL2-USER", "ACL2"),
("LD-PRE-EVAL-PRINT", "ACL2-USER", "ACL2"),
("LD-PROMPT", "ACL2-USER", "ACL2"),
("LD-QUERY-CONTROL-ALIST", "ACL2-USER", "ACL2"),
("LD-REDEFINITION-ACTION", "ACL2-USER", "ACL2"),
("LD-SKIP-PROOFSP", "ACL2-USER", "ACL2"),
("LD-VERBOSE", "ACL2-USER", "ACL2"),
("LEGAL-CASE-CLAUSESP", "ACL2-USER", "ACL2"),
("LEN", "ACL2-USER", "ACL2"),
("LEN-UPDATE-NTH", "ACL2-USER", "ACL2"),
("LIST*-MACRO", "ACL2-USER", "ACL2"),
("LIST-ALL-PACKAGE-NAMES", "ACL2-USER", "ACL2"),
("LIST-ALL-PACKAGE-NAMES-LST", "ACL2-USER", "ACL2"),
("LIST-MACRO", "ACL2-USER", "ACL2"),
("LOCAL", "ACL2-USER", "ACL2"),
("LOGIC", "ACL2-USER", "ACL2"),
("LOWER-CASE-P-CHAR-DOWNCASE", "ACL2-USER", "ACL2"),
("LOWER-CASE-P-FORWARD-TO-ALPHA-CHAR-P", "ACL2-USER", "ACL2"),
("LOWEST-TERMS", "ACL2-USER", "ACL2"),
("LP", "ACL2-USER", "ACL2"),
("MACRO-ALIASES", "ACL2-USER", "ACL2"),
("NTH-ALIASES", "ACL2-USER", "ACL2"),
("MAIN-TIMER", "ACL2-USER", "ACL2"),
("MAIN-TIMER-TYPE-PRESCRIPTION", "ACL2-USER", "ACL2"),
("MAKE-CHARACTER-LIST", "ACL2-USER", "ACL2"),
("MAKE-CHARACTER-LIST-MAKE-CHARACTER-LIST", "ACL2-USER", "ACL2"),
("MAKE-FMT-BINDINGS", "ACL2-USER", "ACL2"),
("MAKE-INPUT-CHANNEL", "ACL2-USER", "ACL2"),
("MAKE-LIST-AC", "ACL2-USER", "ACL2"),
("MAKE-MV-NTHS", "ACL2-USER", "ACL2"),
("MAKE-ORD", "ACL2-USER", "ACL2"),
("MAKE-OUTPUT-CHANNEL", "ACL2-USER", "ACL2"),
("MAKE-VAR-LST", "ACL2-USER", "ACL2"),
("MAKE-VAR-LST1", "ACL2-USER", "ACL2"),
("MAKUNBOUND-GLOBAL", "ACL2-USER", "ACL2"),
("MAXIMUM-LENGTH", "ACL2-USER", "ACL2"),
("MAY-NEED-SLASHES", "ACL2-USER", "ACL2"),
("MBE", "ACL2-USER", "ACL2"),
("MBT", "ACL2-USER", "ACL2"),
("MEMBER-EQ", "ACL2-USER", "ACL2"),
("MEMBER-EQUAL", "ACL2-USER", "ACL2"),
("MEMBER-SYMBOL-NAME", "ACL2-USER", "ACL2"),
("MFC", "ACL2-USER", "ACL2"),
("MINIMAL-THEORY", "ACL2-USER", "ACL2"),
("MONITOR", "ACL2-USER", "ACL2"),
("MONITORED-RUNES", "ACL2-USER", "ACL2"),
("MORE", "ACL2-USER", "ACL2"),
("MORE!", "ACL2-USER", "ACL2"),
("MORE-DOC", "ACL2-USER", "ACL2"),
("MUTUAL-RECURSION", "ACL2-USER", "ACL2"),
("MUTUAL-RECURSION-GUARDP", "ACL2-USER", "ACL2"),
("MV", "ACL2-USER", "ACL2"),
("MV-LET", "ACL2-USER", "ACL2"),
("MV-NTH", "ACL2-USER", "ACL2"),
("NATP", "ACL2-USER", "ACL2"),
("NEWLINE", "ACL2-USER", "ACL2"),
("NFIX", "ACL2-USER", "ACL2"),
("NIL-IS-NOT-CIRCULAR", "ACL2-USER", "ACL2"),
("NO-DUPLICATESP", "ACL2-USER", "ACL2"),
("NO-DUPLICATESP-EQUAL", "ACL2-USER", "ACL2"),
("NONNEGATIVE-INTEGER-QUOTIENT", "ACL2-USER", "ACL2"),
("NONNEGATIVE-PRODUCT", "ACL2-USER", "ACL2"),
("NONZERO-IMAGPART", "ACL2-USER", "ACL2"),
("NQTHM-TO-ACL2", "ACL2-USER", "ACL2"),
("NTH-0-CONS", "ACL2-USER", "ACL2"),
("NTH-0-READ-RUN-TIME-TYPE-PRESCRIPTION", "ACL2-USER", "ACL2"),
("NTH-ADD1", "ACL2-USER", "ACL2"),
("NTH-UPDATE-NTH", "ACL2-USER", "ACL2"),
("O<", "ACL2-USER", "ACL2"),
("O<=", "ACL2-USER", "ACL2"),
("O>", "ACL2-USER", "ACL2"),
("O>=", "ACL2-USER", "ACL2"),
("O-FINP", "ACL2-USER", "ACL2"),
("O-FIRST-COEFF", "ACL2-USER", "ACL2"),
("O-FIRST-EXPT", "ACL2-USER", "ACL2"),
("O-INFP", "ACL2-USER", "ACL2"),
("O-P", "ACL2-USER", "ACL2"),
("O-RST", "ACL2-USER", "ACL2"),
("OBSERVATION", "ACL2-USER", "ACL2"),
("ODDS", "ACL2-USER", "ACL2"),
("OK-IF", "ACL2-USER", "ACL2"),
("OOPS", "ACL2-USER", "ACL2"),
("OPEN-CHANNEL-LISTP", "ACL2-USER", "ACL2"),
("OPEN-CHANNEL1", "ACL2-USER", "ACL2"),
("OPEN-CHANNEL1-FORWARD-TO-TRUE-LISTP-AND-CONSP", "ACL2-USER", "ACL2"),
("OPEN-CHANNELS-P", "ACL2-USER", "ACL2"),
("OPEN-CHANNELS-P-FORWARD", "ACL2-USER", "ACL2"),
("OPEN-INPUT-CHANNEL", "ACL2-USER", "ACL2"),
("OPEN-INPUT-CHANNEL-ANY-P", "ACL2-USER", "ACL2"),
("OPEN-INPUT-CHANNEL-ANY-P1", "ACL2-USER", "ACL2"),
("OPEN-INPUT-CHANNEL-P", "ACL2-USER", "ACL2"),
("OPEN-INPUT-CHANNEL-P1", "ACL2-USER", "ACL2"),
("OPEN-INPUT-CHANNELS", "ACL2-USER", "ACL2"),
("OPEN-OUTPUT-CHANNEL", "ACL2-USER", "ACL2"),
("OPEN-OUTPUT-CHANNEL-ANY-P", "ACL2-USER", "ACL2"),
("OPEN-OUTPUT-CHANNEL-ANY-P1", "ACL2-USER", "ACL2"),
("OPEN-OUTPUT-CHANNEL-P", "ACL2-USER", "ACL2"),
("OPEN-OUTPUT-CHANNEL-P1", "ACL2-USER", "ACL2"),
("OPEN-OUTPUT-CHANNELS", "ACL2-USER", "ACL2"),
("OR-MACRO", "ACL2-USER", "ACL2"),
("ORDERED-SYMBOL-ALISTP", "ACL2-USER", "ACL2"),
("ORDERED-SYMBOL-ALISTP-ADD-PAIR", "ACL2-USER", "ACL2"),
("ORDERED-SYMBOL-ALISTP-ADD-PAIR-FORWARD", "ACL2-USER", "ACL2"),
("ORDERED-SYMBOL-ALISTP-FORWARD-TO-SYMBOL-ALISTP", "ACL2-USER", "ACL2"),
("ORDERED-SYMBOL-ALISTP-GETPROPS", "ACL2-USER", "ACL2"),
("ORDERED-SYMBOL-ALISTP-REMOVE-FIRST-PAIR", "ACL2-USER", "ACL2"),
("OUR-DIGIT-CHAR-P", "ACL2-USER", "ACL2"),
("PAIRLIS$", "ACL2-USER", "ACL2"),
("PAIRLIS2", "ACL2-USER", "ACL2"),
("PBT", "ACL2-USER", "ACL2"),
("PC", "ACL2-USER", "ACL2"),
("PCB", "ACL2-USER", "ACL2"),
("PCB!", "ACL2-USER", "ACL2"),
("PCS", "ACL2-USER", "ACL2"),
("PE", "ACL2-USER", "ACL2"),
("PE!", "ACL2-USER", "ACL2"),
("PEEK-CHAR$", "ACL2-USER", "ACL2"),
("PF", "ACL2-USER", "ACL2"),
("PL", "ACL2-USER", "ACL2"),
("POP-TIMER", "ACL2-USER", "ACL2"),
("POSITION-AC", "ACL2-USER", "ACL2"),
("POSITION-EQ", "ACL2-USER", "ACL2"),
("POSITION-EQ-AC", "ACL2-USER", "ACL2"),
("POSITION-EQUAL", "ACL2-USER", "ACL2"),
("POSITION-EQUAL-AC", "ACL2-USER", "ACL2"),
("POSITIVE", "ACL2-USER", "ACL2"),
("POSP", "ACL2-USER", "ACL2"),
("POWER-EVAL", "ACL2-USER", "ACL2"),
("PPROGN", "ACL2-USER", "ACL2"),
("PR", "ACL2-USER", "ACL2"),
("PR!", "ACL2-USER", "ACL2"),
("PREPROCESS", "ACL2-USER", "ACL2"),
("PRIN1$", "ACL2-USER", "ACL2"),
("PRIN1-WITH-SLASHES", "ACL2-USER", "ACL2"),
("PRIN1-WITH-SLASHES1", "ACL2-USER", "ACL2"),
("PRINC$", "ACL2-USER", "ACL2"),
("PRINT-OBJECT$", "ACL2-USER", "ACL2"),
("PRINT-RATIONAL-AS-DECIMAL", "ACL2-USER", "ACL2"),
("PRINT-TIMER", "ACL2-USER", "ACL2"),
("PROG2$", "ACL2-USER", "ACL2"),
("PROGRAM", "ACL2-USER", "ACL2"),
("PROOF-TREE", "ACL2-USER", "ACL2"),
("PROOFS-CO", "ACL2-USER", "ACL2"),
("PROPER-CONSP", "ACL2-USER", "ACL2"),
("PROPS", "ACL2-USER", "ACL2"),
("PROVE", "ACL2-USER", "ACL2"),
("PSEUDO-TERM-LISTP", "ACL2-USER", "ACL2"),
("PSEUDO-TERM-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("PSEUDO-TERMP", "ACL2-USER", "ACL2"),
("PSTACK", "ACL2-USER", "ACL2"),
("PUFF", "ACL2-USER", "ACL2"),
("PUFF*", "ACL2-USER", "ACL2"),
("PUSH-TIMER", "ACL2-USER", "ACL2"),
("PUSH-UNTOUCHABLE", "ACL2-USER", "ACL2"),
("PUT-ASSOC-EQ", "ACL2-USER", "ACL2"),
("PUT-ASSOC-EQUAL", "ACL2-USER", "ACL2"),
("PUT-GLOBAL", "ACL2-USER", "ACL2"),
("PUTPROP", "ACL2-USER", "ACL2"),
("QUOTEP", "ACL2-USER", "ACL2"),
("R-EQLABLE-ALISTP", "ACL2-USER", "ACL2"),
("RASSOC-EQ", "ACL2-USER", "ACL2"),
("RASSOC-EQUAL", "ACL2-USER", "ACL2"),
("RATIONAL-IMPLIES1", "ACL2-USER", "ACL2"),
("RATIONAL-IMPLIES2", "ACL2-USER", "ACL2"),
("RATIONAL-LISTP", "ACL2-USER", "ACL2"),
("RATIONAL-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("RATIONALP-*", "ACL2-USER", "ACL2"),
("RATIONALP-+", "ACL2-USER", "ACL2"),
("RATIONALP-EXPT-TYPE-PRESCRIPTION", "ACL2-USER", "ACL2"),
("RATIONALP-IMPLIES-ACL2-NUMBERP", "ACL2-USER", "ACL2"),
("RATIONALP-UNARY--", "ACL2-USER", "ACL2"),
("RATIONALP-UNARY-/", "ACL2-USER", "ACL2"),
("READ-BYTE$", "ACL2-USER", "ACL2"),
("READ-CHAR$", "ACL2-USER", "ACL2"),
("READ-FILE-LISTP", "ACL2-USER", "ACL2"),
("READ-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP", "ACL2-USER", "ACL2"),
("READ-FILE-LISTP1", "ACL2-USER", "ACL2"),
("READ-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP", "ACL2-USER", "ACL2"),
("READ-FILES", "ACL2-USER", "ACL2"),
("READ-FILES-P", "ACL2-USER", "ACL2"),
("READ-FILES-P-FORWARD-TO-READ-FILE-LISTP", "ACL2-USER", "ACL2"),
("READ-IDATE", "ACL2-USER", "ACL2"),
("READ-OBJECT", "ACL2-USER", "ACL2"),
("READ-RUN-TIME", "ACL2-USER", "ACL2"),
("READ-RUN-TIME-PRESERVES-STATE-P1", "ACL2-USER", "ACL2"),
("READABLE-FILE", "ACL2-USER", "ACL2"),
("READABLE-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP", "ACL2-USER", "ACL2"),
("READABLE-FILES", "ACL2-USER", "ACL2"),
("READABLE-FILES-LISTP", "ACL2-USER", "ACL2"),
("READABLE-FILES-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP", "ACL2-USER",
"ACL2"),
("READABLE-FILES-P", "ACL2-USER", "ACL2"),
("READABLE-FILES-P-FORWARD-TO-READABLE-FILES-LISTP", "ACL2-USER", "ACL2"),
("REAL/RATIONALP", "ACL2-USER", "ACL2"),
("REALFIX", "ACL2-USER", "ACL2"),
("REALPART-COMPLEX", "ACL2-USER", "ACL2"),
("REALPART-IMAGPART-ELIM", "ACL2-USER", "ACL2"),
("REBUILD", "ACL2-USER", "ACL2"),
("REDEF", "ACL2-USER", "ACL2"),
("REDEF!", "ACL2-USER", "ACL2"),
("REMOVE-DEFAULT-HINTS", "ACL2-USER", "ACL2"),
("REMOVE-DEFAULT-HINTS!", "ACL2-USER", "ACL2"),
("REMOVE-DUPLICATES-EQL", "ACL2-USER", "ACL2"),
("REMOVE-DUPLICATES-EQUAL", "ACL2-USER", "ACL2"),
("REMOVE-FIRST-PAIR", "ACL2-USER", "ACL2"),
("REMOVE-MACRO-ALIAS", "ACL2-USER", "ACL2"),
("REMOVE-NTH-ALIAS", "ACL2-USER", "ACL2"),
("RESET-LD-SPECIALS", "ACL2-USER", "ACL2"),
("RETRACT-WORLD", "ACL2-USER", "ACL2"),
("RETRIEVE", "ACL2-USER", "ACL2"),
("RFIX", "ACL2-USER", "ACL2"),
("RUN-TIMES", "ACL2-USER", "ACL2"),
("SET-BOGUS-MUTUAL-RECURSION-OK", "ACL2-USER", "ACL2"),
("SET-CBD", "ACL2-USER", "ACL2"),
("SET-CASE-SPLIT-LIMITATIONS", "ACL2-USER", "ACL2"),
("SET-COMPILE-FNS", "ACL2-USER", "ACL2"),
("SET-DEFAULT-HINTS", "ACL2-USER", "ACL2"),
("SET-DEFAULT-HINTS!", "ACL2-USER", "ACL2"),
("SET-DIFFERENCE-EQ", "ACL2-USER", "ACL2"),
("SET-DIFFERENCE-EQUAL", "ACL2-USER", "ACL2"),
("SET-DIFFERENCE-THEORIES", "ACL2-USER", "ACL2"),
("SET-ENFORCE-REDUNDANCY", "ACL2-USER", "ACL2"),
("SET-EQUALP-EQUAL", "ACL2-USER", "ACL2"),
("SET-GUARD-CHECKING", "ACL2-USER", "ACL2"),
("SET-IGNORE-OK", "ACL2-USER", "ACL2"),
("SET-INHIBIT-OUTPUT-LST", "ACL2-USER", "ACL2"),
("SET-INHIBIT-WARNINGS", "ACL2-USER", "ACL2"),
("SET-INVISIBLE-FNS-TABLE", "ACL2-USER", "ACL2"),
("SET-IRRELEVANT-FORMALS-OK", "ACL2-USER", "ACL2"),
("SET-MEASURE-FUNCTION", "ACL2-USER", "ACL2"),
("SET-NON-LINEARP", "ACL2-USER", "ACL2"),
("SET-STATE-OK", "ACL2-USER", "ACL2"),
("SET-TIMER", "ACL2-USER", "ACL2"),
("SET-VERIFY-GUARDS-EAGERNESS", "ACL2-USER", "ACL2"),
("SET-W", "ACL2-USER", "ACL2"),
("SET-WELL-FOUNDED-RELATION", "ACL2-USER", "ACL2"),
("SGETPROP", "ACL2-USER", "ACL2"),
("SHOW-BDD", "ACL2-USER", "ACL2"),
("SHOW-ACCUMULATED-PERSISTENCE", "ACL2-USER", "ACL2"),
("SHRINK-32-BIT-INTEGER-STACK", "ACL2-USER", "ACL2"),
("SHRINK-T-STACK", "ACL2-USER", "ACL2"),
("SIMPLIFY", "ACL2-USER", "ACL2"),
("SKIP-PROOFS", "ACL2-USER", "ACL2"),
("SOME-SLASHABLE", "ACL2-USER", "ACL2"),
("STABLE-UNDER-SIMPLIFICATIONP", "ACL2-USER", "ACL2"),
("STANDARD-CHAR-LISTP", "ACL2-USER", "ACL2"),
("STANDARD-CHAR-LISTP-APPEND", "ACL2-USER", "ACL2"),
("STANDARD-CHAR-LISTP-FORWARD-TO-CHARACTER-LISTP", "ACL2-USER", "ACL2"),
("STANDARD-CHAR-P-NTH", "ACL2-USER", "ACL2"),
("STANDARD-CO", "ACL2-USER", "ACL2"),
("STANDARD-OI", "ACL2-USER", "ACL2"),
("START-PROOF-TREE", "ACL2-USER", "ACL2"),
("STATE", "ACL2-USER", "ACL2"),
("STATE-GLOBAL-LET*-CLEANUP", "ACL2-USER", "ACL2"),
("STATE-GLOBAL-LET*-GET-GLOBALS", "ACL2-USER", "ACL2"),
("STATE-GLOBAL-LET*-PUT-GLOBALS", "ACL2-USER", "ACL2"),
("STATE-P", "ACL2-USER", "ACL2"),
("STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1", "ACL2-USER", "ACL2"),
("STATE-P1", "ACL2-USER", "ACL2"),
("STATE-P1-FORWARD", "ACL2-USER", "ACL2"),
("STATE-P1-UPDATE-MAIN-TIMER", "ACL2-USER", "ACL2"),
("STATE-P1-UPDATE-NTH-2-WORLD", "ACL2-USER", "ACL2"),
("STOP-PROOF-TREE", "ACL2-USER", "ACL2"),
("STANDARD-STRING-ALISTP", "ACL2-USER", "ACL2"),
("STANDARD-STRING-ALISTP-FORWARD-TO-ALISTP", "ACL2-USER", "ACL2"),
("STRING-APPEND", "ACL2-USER", "ACL2"),
("STRING-APPEND-LST", "ACL2-USER", "ACL2"),
("STRING-DOWNCASE1", "ACL2-USER", "ACL2"),
("STRING-EQUAL1", "ACL2-USER", "ACL2"),
("STRING-IS-NOT-CIRCULAR", "ACL2-USER", "ACL2"),
("STRING-LISTP", "ACL2-USER", "ACL2"),
("STRING-UPCASE1", "ACL2-USER", "ACL2"),
("STRING<-IRREFLEXIVE", "ACL2-USER", "ACL2"),
("STRING<-L", "ACL2-USER", "ACL2"),
("STRING<-L-ASYMMETRIC", "ACL2-USER", "ACL2"),
("STRING<-L-IRREFLEXIVE", "ACL2-USER", "ACL2"),
("STRING<-L-TRANSITIVE", "ACL2-USER", "ACL2"),
("STRING<-L-TRICHOTOMY", "ACL2-USER", "ACL2"),
("STRINGP-SYMBOL-PACKAGE-NAME", "ACL2-USER", "ACL2"),
("STRIP-CARS", "ACL2-USER", "ACL2"),
("STRIP-CDRS", "ACL2-USER", "ACL2"),
("SUBSEQ-LIST", "ACL2-USER", "ACL2"),
("SUBSETP-EQUAL", "ACL2-USER", "ACL2"),
("SUBSTITUTE-AC", "ACL2-USER", "ACL2"),
("SUMMARY", "ACL2-USER", "ACL2"),
("SYMBOL-<", "ACL2-USER", "ACL2"),
("SYMBOL-<-ASYMMETRIC", "ACL2-USER", "ACL2"),
("SYMBOL-<-IRREFLEXIVE", "ACL2-USER", "ACL2"),
("SYMBOL-<-TRANSITIVE", "ACL2-USER", "ACL2"),
("SYMBOL-<-TRICHOTOMY", "ACL2-USER", "ACL2"),
("SYMBOL-ALISTP", "ACL2-USER", "ACL2"),
("SYMBOL-ALISTP-FORWARD-TO-EQLABLE-ALISTP", "ACL2-USER", "ACL2"),
("SYMBOL-DOUBLET-LISTP", "ACL2-USER", "ACL2"),
("SYMBOL-EQUALITY", "ACL2-USER", "ACL2"),
("SYMBOL-LISTP", "ACL2-USER", "ACL2"),
("SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("SYMBOL-NAME-INTERN-IN-PACKAGE-OF-SYMBOL", "ACL2-USER", "ACL2"),
("SYMBOL-PACKAGE-NAME", "ACL2-USER", "ACL2"),
("SYMBOLP-INTERN-IN-PACKAGE-OF-SYMBOL", "ACL2-USER", "ACL2"),
("SYNP", "ACL2-USER", "ACL2"),
("SYNTAXP", "ACL2-USER", "ACL2"),
("SYS-CALL", "ACL2-USER", "ACL2"),
("SYS-CALL-STATUS", "ACL2-USER", "ACL2"),
("T-STACK", "ACL2-USER", "ACL2"),
("T-STACK-LENGTH", "ACL2-USER", "ACL2"),
("T-STACK-LENGTH1", "ACL2-USER", "ACL2"),
("TABLE", "ACL2-USER", "ACL2"),
("TABLE-ALIST", "ACL2-USER", "ACL2"),
("TAKE", "ACL2-USER", "ACL2"),
("THE-ERROR", "ACL2-USER", "ACL2"),
("THE-FIXNUM", "ACL2-USER", "ACL2"),
("THE-FIXNUM!", "ACL2-USER", "ACL2"),
("THEORY", "ACL2-USER", "ACL2"),
("THEORY-INVARIANT", "ACL2-USER", "ACL2"),
("THM", "ACL2-USER", "ACL2"),
("TIMER-ALISTP", "ACL2-USER", "ACL2"),
("TIMER-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-SYMBOL-ALISTP", "ACL2-USER",
"ACL2"),
("TOGGLE-PC-MACRO", "ACL2-USER", "ACL2"),
("TRACE$", "ACL2-USER", "ACL2"),
("TRANS", "ACL2-USER", "ACL2"),
("TRANS1", "ACL2-USER", "ACL2"),
("TRICHOTOMY", "ACL2-USER", "ACL2"),
("TRUE-LISTP", "ACL2-USER", "ACL2"),
("TRUE-LIST-LISTP", "ACL2-USER", "ACL2"),
("TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP-ASSOC-EQ", "ACL2-USER", "ACL2"),
("TRUE-LISTP-CADR-ASSOC-EQ-FOR-OPEN-CHANNELS-P", "ACL2-USER", "ACL2"),
("TRUE-LISTP-UPDATE-NTH", "ACL2-USER", "ACL2"),
("TYPED-IO-LISTP", "ACL2-USER", "ACL2"),
("TYPED-IO-LISTP-FORWARD-TO-TRUE-LISTP", "ACL2-USER", "ACL2"),
("U", "ACL2-USER", "ACL2"),
("UBT", "ACL2-USER", "ACL2"),
("UBT!", "ACL2-USER", "ACL2"),
("UNARY--", "ACL2-USER", "ACL2"),
("UNARY-/", "ACL2-USER", "ACL2"),
("UNARY-FUNCTION-SYMBOL-LISTP", "ACL2-USER", "ACL2"),
("UNICITY-OF-0", "ACL2-USER", "ACL2"),
("UNICITY-OF-1", "ACL2-USER", "ACL2"),
("UNION-EQ", "ACL2-USER", "ACL2"),
("UNION-EQUAL", "ACL2-USER", "ACL2"),
("UNION-THEORIES", "ACL2-USER", "ACL2"),
("UNIVERSAL-THEORY", "ACL2-USER", "ACL2"),
("UNMONITOR", "ACL2-USER", "ACL2"),
("UNSAVE", "ACL2-USER", "ACL2"),
("UNTRACE$", "ACL2-USER", "ACL2"),
("UPDATE-32-BIT-INTEGER-STACK", "ACL2-USER", "ACL2"),
("UPDATE-BIG-CLOCK-ENTRY", "ACL2-USER", "ACL2"),
("UPDATE-FILE-CLOCK", "ACL2-USER", "ACL2"),
("UPDATE-GLOBAL-TABLE", "ACL2-USER", "ACL2"),
("UPDATE-IDATES", "ACL2-USER", "ACL2"),
("UPDATE-LIST-ALL-PACKAGE-NAMES-LST", "ACL2-USER", "ACL2"),
("UPDATE-NTH", "ACL2-USER", "ACL2"),
("UPDATE-OPEN-INPUT-CHANNELS", "ACL2-USER", "ACL2"),
("UPDATE-OPEN-OUTPUT-CHANNELS", "ACL2-USER", "ACL2"),
("UPDATE-READ-FILES", "ACL2-USER", "ACL2"),
("UPDATE-RUN-TIMES", "ACL2-USER", "ACL2"),
("UPDATE-RUN-TIMES-PRESERVES-STATE-P1", "ACL2-USER", "ACL2"),
("UPDATE-T-STACK", "ACL2-USER", "ACL2"),
("UPDATE-USER-STOBJ-ALIST", "ACL2-USER", "ACL2"),
("UPDATE-USER-STOBJ-ALIST1", "ACL2-USER", "ACL2"),
("UPDATE-WRITTEN-FILES", "ACL2-USER", "ACL2"),
("UPPER-CASE-P-CHAR-UPCASE", "ACL2-USER", "ACL2"),
("UPPER-CASE-P-FORWARD-TO-ALPHA-CHAR-P", "ACL2-USER", "ACL2"),
("USER-STOBJ-ALIST", "ACL2-USER", "ACL2"),
("USER-STOBJ-ALIST1", "ACL2-USER", "ACL2"),
("VERBOSE-PSTACK", "ACL2-USER", "ACL2"),
("VERIFY", "ACL2-USER", "ACL2"),
("VERIFY-GUARDS", "ACL2-USER", "ACL2"),
("VERIFY-TERMINATION", "ACL2-USER", "ACL2"),
("W", "ACL2-USER", "ACL2"),
("WARNING!", "ACL2-USER", "ACL2"),
("WET", "ACL2-USER", "ACL2"),
("WITH-OUTPUT", "ACL2-USER", "ACL2"),
("WORLD", "ACL2-USER", "ACL2"),
("WORLDP", "ACL2-USER", "ACL2"),
("WORLDP-FORWARD-TO-ASSOC-EQ-EQUAL-ALISTP", "ACL2-USER", "ACL2"),
("WORMHOLE", "ACL2-USER", "ACL2"),
("WORMHOLE1", "ACL2-USER", "ACL2"),
("WRITABLE-FILE-LISTP", "ACL2-USER", "ACL2"),
("WRITABLE-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP", "ACL2-USER", "ACL2"),
("WRITABLE-FILE-LISTP1", "ACL2-USER", "ACL2"),
("WRITABLE-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP", "ACL2-USER",
"ACL2"),
("WRITE-BYTE$", "ACL2-USER", "ACL2"),
("WRITEABLE-FILES", "ACL2-USER", "ACL2"),
("WRITEABLE-FILES-P", "ACL2-USER", "ACL2"),
("WRITEABLE-FILES-P-FORWARD-TO-WRITABLE-FILE-LISTP", "ACL2-USER", "ACL2"),
("WRITTEN-FILE", "ACL2-USER", "ACL2"),
("WRITTEN-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP", "ACL2-USER", "ACL2"),
("WRITTEN-FILE-LISTP", "ACL2-USER", "ACL2"),
("WRITTEN-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP", "ACL2-USER",
"ACL2"),
("WRITTEN-FILES", "ACL2-USER", "ACL2"),
("WRITTEN-FILES-P", "ACL2-USER", "ACL2"),
("WRITTEN-FILES-P-FORWARD-TO-WRITTEN-FILE-LISTP", "ACL2-USER", "ACL2"),
("XARGS", "ACL2-USER", "ACL2"),
("XXXJOIN", "ACL2-USER", "ACL2"),
("ZERO", "ACL2-USER", "ACL2"),
("ZIP", "ACL2-USER", "ACL2"),
("ZP", "ACL2-USER", "ACL2"),
("&ALLOW-OTHER-KEYS", "ACL2-USER", "COMMON-LISP"),
("*PRINT-MISER-WIDTH*", "ACL2-USER", "COMMON-LISP"),
("&AUX", "ACL2-USER", "COMMON-LISP"),
("*PRINT-PPRINT-DISPATCH*", "ACL2-USER", "COMMON-LISP"),
("&BODY", "ACL2-USER", "COMMON-LISP"),
("*PRINT-PRETTY*", "ACL2-USER", "COMMON-LISP"),
("&ENVIRONMENT", "ACL2-USER", "COMMON-LISP"),
("*PRINT-RADIX*", "ACL2-USER", "COMMON-LISP"),
("&KEY", "ACL2-USER", "COMMON-LISP"),
("*PRINT-READABLY*", "ACL2-USER", "COMMON-LISP"),
("&OPTIONAL", "ACL2-USER", "COMMON-LISP"),
("*PRINT-RIGHT-MARGIN*", "ACL2-USER", "COMMON-LISP"),
("&REST", "ACL2-USER", "COMMON-LISP"),
("*QUERY-IO*", "ACL2-USER", "COMMON-LISP"),
("&WHOLE", "ACL2-USER", "COMMON-LISP"),
("*RANDOM-STATE*", "ACL2-USER", "COMMON-LISP"),
("*", "ACL2-USER", "COMMON-LISP"),
("*READ-BASE*", "ACL2-USER", "COMMON-LISP"),
("**", "ACL2-USER", "COMMON-LISP"),
("*READ-DEFAULT-FLOAT-FORMAT*", "ACL2-USER", "COMMON-LISP"),
("***", "ACL2-USER", "COMMON-LISP"),
("*READ-EVAL*", "ACL2-USER", "COMMON-LISP"),
("*BREAK-ON-SIGNALS*", "ACL2-USER", "COMMON-LISP"),
("*READ-SUPPRESS*", "ACL2-USER", "COMMON-LISP"),
("*COMPILE-FILE-PATHNAME*", "ACL2-USER", "COMMON-LISP"),
("*READTABLE*", "ACL2-USER", "COMMON-LISP"),
("*COMPILE-FILE-TRUENAME*", "ACL2-USER", "COMMON-LISP"),
("*STANDARD-INPUT*", "ACL2-USER", "COMMON-LISP"),
("*COMPILE-PRINT*", "ACL2-USER", "COMMON-LISP"),
("*STANDARD-OUTPUT*", "ACL2-USER", "COMMON-LISP"),
("*COMPILE-VERBOSE*", "ACL2-USER", "COMMON-LISP"),
("*TERMINAL-IO*", "ACL2-USER", "COMMON-LISP"),
("*DEBUG-IO*", "ACL2-USER", "COMMON-LISP"),
("*TRACE-OUTPUT*", "ACL2-USER", "COMMON-LISP"),
("*DEBUGGER-HOOK*", "ACL2-USER", "COMMON-LISP"),
("+", "ACL2-USER", "COMMON-LISP"),
("*DEFAULT-PATHNAME-DEFAULTS*", "ACL2-USER", "COMMON-LISP"),
("++", "ACL2-USER", "COMMON-LISP"),
("*ERROR-OUTPUT*", "ACL2-USER", "COMMON-LISP"),
("+++", "ACL2-USER", "COMMON-LISP"),
("*FEATURES*", "ACL2-USER", "COMMON-LISP"),
("-", "ACL2-USER", "COMMON-LISP"),
("*GENSYM-COUNTER*", "ACL2-USER", "COMMON-LISP"),
("/", "ACL2-USER", "COMMON-LISP"),
("*LOAD-PATHNAME*", "ACL2-USER", "COMMON-LISP"),
("//", "ACL2-USER", "COMMON-LISP"),
("*LOAD-PRINT*", "ACL2-USER", "COMMON-LISP"),
("///", "ACL2-USER", "COMMON-LISP"),
("*LOAD-TRUENAME*", "ACL2-USER", "COMMON-LISP"),
("/=", "ACL2-USER", "COMMON-LISP"),
("*LOAD-VERBOSE*", "ACL2-USER", "COMMON-LISP"),
("1+", "ACL2-USER", "COMMON-LISP"),
("*MACROEXPAND-HOOK*", "ACL2-USER", "COMMON-LISP"),
("1-", "ACL2-USER", "COMMON-LISP"),
("*MODULES*", "ACL2-USER", "COMMON-LISP"),
("<", "ACL2-USER", "COMMON-LISP"),
("*PACKAGE*", "ACL2-USER", "COMMON-LISP"),
("<=", "ACL2-USER", "COMMON-LISP"),
("*PRINT-ARRAY*", "ACL2-USER", "COMMON-LISP"),
("=", "ACL2-USER", "COMMON-LISP"),
("*PRINT-BASE*", "ACL2-USER", "COMMON-LISP"),
(">", "ACL2-USER", "COMMON-LISP"),
("*PRINT-CASE*", "ACL2-USER", "COMMON-LISP"),
(">=", "ACL2-USER", "COMMON-LISP"),
("*PRINT-CIRCLE*", "ACL2-USER", "COMMON-LISP"),
("ABORT", "ACL2-USER", "COMMON-LISP"),
("*PRINT-ESCAPE*", "ACL2-USER", "COMMON-LISP"),
("ABS", "ACL2-USER", "COMMON-LISP"),
("*PRINT-GENSYM*", "ACL2-USER", "COMMON-LISP"),
("ACONS", "ACL2-USER", "COMMON-LISP"),
("*PRINT-LENGTH*", "ACL2-USER", "COMMON-LISP"),
("ACOS", "ACL2-USER", "COMMON-LISP"),
("*PRINT-LEVEL*", "ACL2-USER", "COMMON-LISP"),
("ACOSH", "ACL2-USER", "COMMON-LISP"),
("*PRINT-LINES*", "ACL2-USER", "COMMON-LISP"),
("ADD-METHOD", "ACL2-USER", "COMMON-LISP"),
("ADJOIN", "ACL2-USER", "COMMON-LISP"),
("ATOM", "ACL2-USER", "COMMON-LISP"),
("BOUNDP", "ACL2-USER", "COMMON-LISP"),
("ADJUST-ARRAY", "ACL2-USER", "COMMON-LISP"),
("BASE-CHAR", "ACL2-USER", "COMMON-LISP"),
("BREAK", "ACL2-USER", "COMMON-LISP"),
("ADJUSTABLE-ARRAY-P", "ACL2-USER", "COMMON-LISP"),
("BASE-STRING", "ACL2-USER", "COMMON-LISP"),
("BROADCAST-STREAM", "ACL2-USER", "COMMON-LISP"),
("ALLOCATE-INSTANCE", "ACL2-USER", "COMMON-LISP"),
("BIGNUM", "ACL2-USER", "COMMON-LISP"),
("BROADCAST-STREAM-STREAMS", "ACL2-USER", "COMMON-LISP"),
("ALPHA-CHAR-P", "ACL2-USER", "COMMON-LISP"),
("BIT", "ACL2-USER", "COMMON-LISP"),
("BUILT-IN-CLASS", "ACL2-USER", "COMMON-LISP"),
("ALPHANUMERICP", "ACL2-USER", "COMMON-LISP"),
("BIT-AND", "ACL2-USER", "COMMON-LISP"),
("BUTLAST", "ACL2-USER", "COMMON-LISP"),
("AND", "ACL2-USER", "COMMON-LISP"),
("BIT-ANDC1", "ACL2-USER", "COMMON-LISP"),
("BYTE", "ACL2-USER", "COMMON-LISP"),
("APPEND", "ACL2-USER", "COMMON-LISP"),
("BIT-ANDC2", "ACL2-USER", "COMMON-LISP"),
("BYTE-POSITION", "ACL2-USER", "COMMON-LISP"),
("APPLY", "ACL2-USER", "COMMON-LISP"),
("BIT-EQV", "ACL2-USER", "COMMON-LISP"),
("BYTE-SIZE", "ACL2-USER", "COMMON-LISP"),
("APROPOS", "ACL2-USER", "COMMON-LISP"),
("BIT-IOR", "ACL2-USER", "COMMON-LISP"),
("CAAAAR", "ACL2-USER", "COMMON-LISP"),
("APROPOS-LIST", "ACL2-USER", "COMMON-LISP"),
("BIT-NAND", "ACL2-USER", "COMMON-LISP"),
("CAAADR", "ACL2-USER", "COMMON-LISP"),
("AREF", "ACL2-USER", "COMMON-LISP"),
("BIT-NOR", "ACL2-USER", "COMMON-LISP"),
("CAAAR", "ACL2-USER", "COMMON-LISP"),
("ARITHMETIC-ERROR", "ACL2-USER", "COMMON-LISP"),
("BIT-NOT", "ACL2-USER", "COMMON-LISP"),
("CAADAR", "ACL2-USER", "COMMON-LISP"),
("ARITHMETIC-ERROR-OPERANDS", "ACL2-USER", "COMMON-LISP"),
("BIT-ORC1", "ACL2-USER", "COMMON-LISP"),
("CAADDR", "ACL2-USER", "COMMON-LISP"),
("ARITHMETIC-ERROR-OPERATION", "ACL2-USER", "COMMON-LISP"),
("BIT-ORC2", "ACL2-USER", "COMMON-LISP"),
("CAADR", "ACL2-USER", "COMMON-LISP"),
("ARRAY", "ACL2-USER", "COMMON-LISP"),
("BIT-VECTOR", "ACL2-USER", "COMMON-LISP"),
("CAAR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-DIMENSION", "ACL2-USER", "COMMON-LISP"),
("BIT-VECTOR-P", "ACL2-USER", "COMMON-LISP"),
("CADAAR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-DIMENSION-LIMIT", "ACL2-USER", "COMMON-LISP"),
("BIT-XOR", "ACL2-USER", "COMMON-LISP"),
("CADADR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-DIMENSIONS", "ACL2-USER", "COMMON-LISP"),
("BLOCK", "ACL2-USER", "COMMON-LISP"),
("CADAR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-DISPLACEMENT", "ACL2-USER", "COMMON-LISP"),
("BOOLE", "ACL2-USER", "COMMON-LISP"),
("CADDAR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-ELEMENT-TYPE", "ACL2-USER", "COMMON-LISP"),
("BOOLE-1", "ACL2-USER", "COMMON-LISP"),
("CADDDR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-HAS-FILL-POINTER-P", "ACL2-USER", "COMMON-LISP"),
("BOOLE-2", "ACL2-USER", "COMMON-LISP"),
("CADDR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-IN-BOUNDS-P", "ACL2-USER", "COMMON-LISP"),
("BOOLE-AND", "ACL2-USER", "COMMON-LISP"),
("CADR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-RANK", "ACL2-USER", "COMMON-LISP"),
("BOOLE-ANDC1", "ACL2-USER", "COMMON-LISP"),
("CALL-ARGUMENTS-LIMIT", "ACL2-USER", "COMMON-LISP"),
("ARRAY-RANK-LIMIT", "ACL2-USER", "COMMON-LISP"),
("BOOLE-ANDC2", "ACL2-USER", "COMMON-LISP"),
("CALL-METHOD", "ACL2-USER", "COMMON-LISP"),
("ARRAY-ROW-MAJOR-INDEX", "ACL2-USER", "COMMON-LISP"),
("BOOLE-C1", "ACL2-USER", "COMMON-LISP"),
("CALL-NEXT-METHOD", "ACL2-USER", "COMMON-LISP"),
("ARRAY-TOTAL-SIZE", "ACL2-USER", "COMMON-LISP"),
("BOOLE-C2", "ACL2-USER", "COMMON-LISP"),
("CAR", "ACL2-USER", "COMMON-LISP"),
("ARRAY-TOTAL-SIZE-LIMIT", "ACL2-USER", "COMMON-LISP"),
("BOOLE-CLR", "ACL2-USER", "COMMON-LISP"),
("CASE", "ACL2-USER", "COMMON-LISP"),
("ARRAYP", "ACL2-USER", "COMMON-LISP"),
("BOOLE-EQV", "ACL2-USER", "COMMON-LISP"),
("CATCH", "ACL2-USER", "COMMON-LISP"),
("ASH", "ACL2-USER", "COMMON-LISP"),
("BOOLE-IOR", "ACL2-USER", "COMMON-LISP"),
("CCASE", "ACL2-USER", "COMMON-LISP"),
("ASIN", "ACL2-USER", "COMMON-LISP"),
("BOOLE-NAND", "ACL2-USER", "COMMON-LISP"),
("CDAAAR", "ACL2-USER", "COMMON-LISP"),
("ASINH", "ACL2-USER", "COMMON-LISP"),
("BOOLE-NOR", "ACL2-USER", "COMMON-LISP"),
("CDAADR", "ACL2-USER", "COMMON-LISP"),
("ASSERT", "ACL2-USER", "COMMON-LISP"),
("BOOLE-ORC1", "ACL2-USER", "COMMON-LISP"),
("CDAAR", "ACL2-USER", "COMMON-LISP"),
("ASSOC", "ACL2-USER", "COMMON-LISP"),
("BOOLE-ORC2", "ACL2-USER", "COMMON-LISP"),
("CDADAR", "ACL2-USER", "COMMON-LISP"),
("ASSOC-IF", "ACL2-USER", "COMMON-LISP"),
("BOOLE-SET", "ACL2-USER", "COMMON-LISP"),
("CDADDR", "ACL2-USER", "COMMON-LISP"),
("ASSOC-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("BOOLE-XOR", "ACL2-USER", "COMMON-LISP"),
("CDADR", "ACL2-USER", "COMMON-LISP"),
("ATAN", "ACL2-USER", "COMMON-LISP"),
("BOOLEAN", "ACL2-USER", "COMMON-LISP"),
("CDAR", "ACL2-USER", "COMMON-LISP"),
("ATANH", "ACL2-USER", "COMMON-LISP"),
("BOTH-CASE-P", "ACL2-USER", "COMMON-LISP"),
("CDDAAR", "ACL2-USER", "COMMON-LISP"),
("CDDADR", "ACL2-USER", "COMMON-LISP"),
("CLEAR-INPUT", "ACL2-USER", "COMMON-LISP"),
("COPY-TREE", "ACL2-USER", "COMMON-LISP"),
("CDDAR", "ACL2-USER", "COMMON-LISP"),
("CLEAR-OUTPUT", "ACL2-USER", "COMMON-LISP"),
("COS", "ACL2-USER", "COMMON-LISP"),
("CDDDAR", "ACL2-USER", "COMMON-LISP"),
("CLOSE", "ACL2-USER", "COMMON-LISP"),
("COSH", "ACL2-USER", "COMMON-LISP"),
("CDDDDR", "ACL2-USER", "COMMON-LISP"),
("CLRHASH", "ACL2-USER", "COMMON-LISP"),
("COUNT", "ACL2-USER", "COMMON-LISP"),
("CDDDR", "ACL2-USER", "COMMON-LISP"),
("CODE-CHAR", "ACL2-USER", "COMMON-LISP"),
("COUNT-IF", "ACL2-USER", "COMMON-LISP"),
("CDDR", "ACL2-USER", "COMMON-LISP"),
("COERCE", "ACL2-USER", "COMMON-LISP"),
("COUNT-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("CDR", "ACL2-USER", "COMMON-LISP"),
("COMPILATION-SPEED", "ACL2-USER", "COMMON-LISP"),
("CTYPECASE", "ACL2-USER", "COMMON-LISP"),
("CEILING", "ACL2-USER", "COMMON-LISP"),
("COMPILE", "ACL2-USER", "COMMON-LISP"),
("DEBUG", "ACL2-USER", "COMMON-LISP"),
("CELL-ERROR", "ACL2-USER", "COMMON-LISP"),
("COMPILE-FILE", "ACL2-USER", "COMMON-LISP"),
("DECF", "ACL2-USER", "COMMON-LISP"),
("CELL-ERROR-NAME", "ACL2-USER", "COMMON-LISP"),
("COMPILE-FILE-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("DECLAIM", "ACL2-USER", "COMMON-LISP"),
("CERROR", "ACL2-USER", "COMMON-LISP"),
("COMPILED-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("DECLARATION", "ACL2-USER", "COMMON-LISP"),
("CHANGE-CLASS", "ACL2-USER", "COMMON-LISP"),
("COMPILED-FUNCTION-P", "ACL2-USER", "COMMON-LISP"),
("DECLARE", "ACL2-USER", "COMMON-LISP"),
("CHAR", "ACL2-USER", "COMMON-LISP"),
("COMPILER-MACRO", "ACL2-USER", "COMMON-LISP"),
("DECODE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("CHAR-CODE", "ACL2-USER", "COMMON-LISP"),
("COMPILER-MACRO-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("DECODE-UNIVERSAL-TIME", "ACL2-USER", "COMMON-LISP"),
("CHAR-CODE-LIMIT", "ACL2-USER", "COMMON-LISP"),
("COMPLEMENT", "ACL2-USER", "COMMON-LISP"),
("DEFCLASS", "ACL2-USER", "COMMON-LISP"),
("CHAR-DOWNCASE", "ACL2-USER", "COMMON-LISP"),
("COMPLEX", "ACL2-USER", "COMMON-LISP"),
("DEFCONSTANT", "ACL2-USER", "COMMON-LISP"),
("CHAR-EQUAL", "ACL2-USER", "COMMON-LISP"),
("COMPLEXP", "ACL2-USER", "COMMON-LISP"),
("DEFGENERIC", "ACL2-USER", "COMMON-LISP"),
("CHAR-GREATERP", "ACL2-USER", "COMMON-LISP"),
("COMPUTE-APPLICABLE-METHODS", "ACL2-USER", "COMMON-LISP"),
("DEFINE-COMPILER-MACRO", "ACL2-USER", "COMMON-LISP"),
("CHAR-INT", "ACL2-USER", "COMMON-LISP"),
("COMPUTE-RESTARTS", "ACL2-USER", "COMMON-LISP"),
("DEFINE-CONDITION", "ACL2-USER", "COMMON-LISP"),
("CHAR-LESSP", "ACL2-USER", "COMMON-LISP"),
("CONCATENATE", "ACL2-USER", "COMMON-LISP"),
("DEFINE-METHOD-COMBINATION", "ACL2-USER", "COMMON-LISP"),
("CHAR-NAME", "ACL2-USER", "COMMON-LISP"),
("CONCATENATED-STREAM", "ACL2-USER", "COMMON-LISP"),
("DEFINE-MODIFY-MACRO", "ACL2-USER", "COMMON-LISP"),
("CHAR-NOT-EQUAL", "ACL2-USER", "COMMON-LISP"),
("CONCATENATED-STREAM-STREAMS", "ACL2-USER", "COMMON-LISP"),
("DEFINE-SETF-EXPANDER", "ACL2-USER", "COMMON-LISP"),
("CHAR-NOT-GREATERP", "ACL2-USER", "COMMON-LISP"),
("COND", "ACL2-USER", "COMMON-LISP"),
("DEFINE-SYMBOL-MACRO", "ACL2-USER", "COMMON-LISP"),
("CHAR-NOT-LESSP", "ACL2-USER", "COMMON-LISP"),
("CONDITION", "ACL2-USER", "COMMON-LISP"),
("DEFMACRO", "ACL2-USER", "COMMON-LISP"),
("CHAR-UPCASE", "ACL2-USER", "COMMON-LISP"),
("CONJUGATE", "ACL2-USER", "COMMON-LISP"),
("DEFMETHOD", "ACL2-USER", "COMMON-LISP"),
("CHAR/=", "ACL2-USER", "COMMON-LISP"),
("CONS", "ACL2-USER", "COMMON-LISP"),
("DEFPACKAGE", "ACL2-USER", "COMMON-LISP"),
("CHAR<", "ACL2-USER", "COMMON-LISP"),
("CONSP", "ACL2-USER", "COMMON-LISP"),
("DEFPARAMETER", "ACL2-USER", "COMMON-LISP"),
("CHAR<=", "ACL2-USER", "COMMON-LISP"),
("CONSTANTLY", "ACL2-USER", "COMMON-LISP"),
("DEFSETF", "ACL2-USER", "COMMON-LISP"),
("CHAR=", "ACL2-USER", "COMMON-LISP"),
("CONSTANTP", "ACL2-USER", "COMMON-LISP"),
("DEFSTRUCT", "ACL2-USER", "COMMON-LISP"),
("CHAR>", "ACL2-USER", "COMMON-LISP"),
("CONTINUE", "ACL2-USER", "COMMON-LISP"),
("DEFTYPE", "ACL2-USER", "COMMON-LISP"),
("CHAR>=", "ACL2-USER", "COMMON-LISP"),
("CONTROL-ERROR", "ACL2-USER", "COMMON-LISP"),
("DEFUN", "ACL2-USER", "COMMON-LISP"),
("CHARACTER", "ACL2-USER", "COMMON-LISP"),
("COPY-ALIST", "ACL2-USER", "COMMON-LISP"),
("DEFVAR", "ACL2-USER", "COMMON-LISP"),
("CHARACTERP", "ACL2-USER", "COMMON-LISP"),
("COPY-LIST", "ACL2-USER", "COMMON-LISP"),
("DELETE", "ACL2-USER", "COMMON-LISP"),
("CHECK-TYPE", "ACL2-USER", "COMMON-LISP"),
("COPY-PPRINT-DISPATCH", "ACL2-USER", "COMMON-LISP"),
("DELETE-DUPLICATES", "ACL2-USER", "COMMON-LISP"),
("CIS", "ACL2-USER", "COMMON-LISP"),
("COPY-READTABLE", "ACL2-USER", "COMMON-LISP"),
("DELETE-FILE", "ACL2-USER", "COMMON-LISP"),
("CLASS", "ACL2-USER", "COMMON-LISP"),
("COPY-SEQ", "ACL2-USER", "COMMON-LISP"),
("DELETE-IF", "ACL2-USER", "COMMON-LISP"),
("CLASS-NAME", "ACL2-USER", "COMMON-LISP"),
("COPY-STRUCTURE", "ACL2-USER", "COMMON-LISP"),
("DELETE-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("CLASS-OF", "ACL2-USER", "COMMON-LISP"),
("COPY-SYMBOL", "ACL2-USER", "COMMON-LISP"),
("DELETE-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("DENOMINATOR", "ACL2-USER", "COMMON-LISP"),
("EQ", "ACL2-USER", "COMMON-LISP"),
("DEPOSIT-FIELD", "ACL2-USER", "COMMON-LISP"),
("EQL", "ACL2-USER", "COMMON-LISP"),
("DESCRIBE", "ACL2-USER", "COMMON-LISP"),
("EQUAL", "ACL2-USER", "COMMON-LISP"),
("DESCRIBE-OBJECT", "ACL2-USER", "COMMON-LISP"),
("EQUALP", "ACL2-USER", "COMMON-LISP"),
("DESTRUCTURING-BIND", "ACL2-USER", "COMMON-LISP"),
("ERROR", "ACL2-USER", "COMMON-LISP"),
("DIGIT-CHAR", "ACL2-USER", "COMMON-LISP"),
("ETYPECASE", "ACL2-USER", "COMMON-LISP"),
("DIGIT-CHAR-P", "ACL2-USER", "COMMON-LISP"),
("EVAL", "ACL2-USER", "COMMON-LISP"),
("DIRECTORY", "ACL2-USER", "COMMON-LISP"),
("EVAL-WHEN", "ACL2-USER", "COMMON-LISP"),
("DIRECTORY-NAMESTRING", "ACL2-USER", "COMMON-LISP"),
("EVENP", "ACL2-USER", "COMMON-LISP"),
("DISASSEMBLE", "ACL2-USER", "COMMON-LISP"),
("EVERY", "ACL2-USER", "COMMON-LISP"),
("DIVISION-BY-ZERO", "ACL2-USER", "COMMON-LISP"),
("EXP", "ACL2-USER", "COMMON-LISP"),
("DO", "ACL2-USER", "COMMON-LISP"),
("EXPORT", "ACL2-USER", "COMMON-LISP"),
("DO*", "ACL2-USER", "COMMON-LISP"),
("EXPT", "ACL2-USER", "COMMON-LISP"),
("DO-ALL-SYMBOLS", "ACL2-USER", "COMMON-LISP"),
("EXTENDED-CHAR", "ACL2-USER", "COMMON-LISP"),
("DO-EXTERNAL-SYMBOLS", "ACL2-USER", "COMMON-LISP"),
("FBOUNDP", "ACL2-USER", "COMMON-LISP"),
("DO-SYMBOLS", "ACL2-USER", "COMMON-LISP"),
("FCEILING", "ACL2-USER", "COMMON-LISP"),
("DOCUMENTATION", "ACL2-USER", "COMMON-LISP"),
("FDEFINITION", "ACL2-USER", "COMMON-LISP"),
("DOLIST", "ACL2-USER", "COMMON-LISP"),
("FFLOOR", "ACL2-USER", "COMMON-LISP"),
("DOTIMES", "ACL2-USER", "COMMON-LISP"),
("FIFTH", "ACL2-USER", "COMMON-LISP"),
("DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("FILE-AUTHOR", "ACL2-USER", "COMMON-LISP"),
("DOUBLE-FLOAT-EPSILON", "ACL2-USER", "COMMON-LISP"),
("FILE-ERROR", "ACL2-USER", "COMMON-LISP"),
("DOUBLE-FLOAT-NEGATIVE-EPSILON", "ACL2-USER", "COMMON-LISP"),
("FILE-ERROR-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("DPB", "ACL2-USER", "COMMON-LISP"),
("FILE-LENGTH", "ACL2-USER", "COMMON-LISP"),
("DRIBBLE", "ACL2-USER", "COMMON-LISP"),
("FILE-NAMESTRING", "ACL2-USER", "COMMON-LISP"),
("DYNAMIC-EXTENT", "ACL2-USER", "COMMON-LISP"),
("FILE-POSITION", "ACL2-USER", "COMMON-LISP"),
("ECASE", "ACL2-USER", "COMMON-LISP"),
("FILE-STREAM", "ACL2-USER", "COMMON-LISP"),
("ECHO-STREAM", "ACL2-USER", "COMMON-LISP"),
("FILE-STRING-LENGTH", "ACL2-USER", "COMMON-LISP"),
("ECHO-STREAM-INPUT-STREAM", "ACL2-USER", "COMMON-LISP"),
("FILE-WRITE-DATE", "ACL2-USER", "COMMON-LISP"),
("ECHO-STREAM-OUTPUT-STREAM", "ACL2-USER", "COMMON-LISP"),
("FILL", "ACL2-USER", "COMMON-LISP"),
("ED", "ACL2-USER", "COMMON-LISP"),
("FILL-POINTER", "ACL2-USER", "COMMON-LISP"),
("EIGHTH", "ACL2-USER", "COMMON-LISP"),
("FIND", "ACL2-USER", "COMMON-LISP"),
("ELT", "ACL2-USER", "COMMON-LISP"),
("FIND-ALL-SYMBOLS", "ACL2-USER", "COMMON-LISP"),
("ENCODE-UNIVERSAL-TIME", "ACL2-USER", "COMMON-LISP"),
("FIND-CLASS", "ACL2-USER", "COMMON-LISP"),
("END-OF-FILE", "ACL2-USER", "COMMON-LISP"),
("FIND-IF", "ACL2-USER", "COMMON-LISP"),
("ENDP", "ACL2-USER", "COMMON-LISP"),
("FIND-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("ENOUGH-NAMESTRING", "ACL2-USER", "COMMON-LISP"),
("FIND-METHOD", "ACL2-USER", "COMMON-LISP"),
("ENSURE-DIRECTORIES-EXIST", "ACL2-USER", "COMMON-LISP"),
("FIND-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("ENSURE-GENERIC-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("FIND-RESTART", "ACL2-USER", "COMMON-LISP"),
("FIND-SYMBOL", "ACL2-USER", "COMMON-LISP"),
("GET-INTERNAL-RUN-TIME", "ACL2-USER", "COMMON-LISP"),
("FINISH-OUTPUT", "ACL2-USER", "COMMON-LISP"),
("GET-MACRO-CHARACTER", "ACL2-USER", "COMMON-LISP"),
("FIRST", "ACL2-USER", "COMMON-LISP"),
("GET-OUTPUT-STREAM-STRING", "ACL2-USER", "COMMON-LISP"),
("FIXNUM", "ACL2-USER", "COMMON-LISP"),
("GET-PROPERTIES", "ACL2-USER", "COMMON-LISP"),
("FLET", "ACL2-USER", "COMMON-LISP"),
("GET-SETF-EXPANSION", "ACL2-USER", "COMMON-LISP"),
("FLOAT", "ACL2-USER", "COMMON-LISP"),
("GET-UNIVERSAL-TIME", "ACL2-USER", "COMMON-LISP"),
("FLOAT-DIGITS", "ACL2-USER", "COMMON-LISP"),
("GETF", "ACL2-USER", "COMMON-LISP"),
("FLOAT-PRECISION", "ACL2-USER", "COMMON-LISP"),
("GETHASH", "ACL2-USER", "COMMON-LISP"),
("FLOAT-RADIX", "ACL2-USER", "COMMON-LISP"),
("GO", "ACL2-USER", "COMMON-LISP"),
("FLOAT-SIGN", "ACL2-USER", "COMMON-LISP"),
("GRAPHIC-CHAR-P", "ACL2-USER", "COMMON-LISP"),
("FLOATING-POINT-INEXACT", "ACL2-USER", "COMMON-LISP"),
("HANDLER-BIND", "ACL2-USER", "COMMON-LISP"),
("FLOATING-POINT-INVALID-OPERATION", "ACL2-USER", "COMMON-LISP"),
("HANDLER-CASE", "ACL2-USER", "COMMON-LISP"),
("FLOATING-POINT-OVERFLOW", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE", "ACL2-USER", "COMMON-LISP"),
("FLOATING-POINT-UNDERFLOW", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE-COUNT", "ACL2-USER", "COMMON-LISP"),
("FLOATP", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE-P", "ACL2-USER", "COMMON-LISP"),
("FLOOR", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE-REHASH-SIZE", "ACL2-USER", "COMMON-LISP"),
("FMAKUNBOUND", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE-REHASH-THRESHOLD", "ACL2-USER", "COMMON-LISP"),
("FORCE-OUTPUT", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE-SIZE", "ACL2-USER", "COMMON-LISP"),
("FORMAT", "ACL2-USER", "COMMON-LISP"),
("HASH-TABLE-TEST", "ACL2-USER", "COMMON-LISP"),
("FORMATTER", "ACL2-USER", "COMMON-LISP"),
("HOST-NAMESTRING", "ACL2-USER", "COMMON-LISP"),
("FOURTH", "ACL2-USER", "COMMON-LISP"),
("IDENTITY", "ACL2-USER", "COMMON-LISP"),
("FRESH-LINE", "ACL2-USER", "COMMON-LISP"),
("IF", "ACL2-USER", "COMMON-LISP"),
("FROUND", "ACL2-USER", "COMMON-LISP"),
("IGNORABLE", "ACL2-USER", "COMMON-LISP"),
("FTRUNCATE", "ACL2-USER", "COMMON-LISP"),
("IGNORE", "ACL2-USER", "COMMON-LISP"),
("FTYPE", "ACL2-USER", "COMMON-LISP"),
("IGNORE-ERRORS", "ACL2-USER", "COMMON-LISP"),
("FUNCALL", "ACL2-USER", "COMMON-LISP"),
("IMAGPART", "ACL2-USER", "COMMON-LISP"),
("FUNCTION", "ACL2-USER", "COMMON-LISP"),
("IMPORT", "ACL2-USER", "COMMON-LISP"),
("FUNCTION-KEYWORDS", "ACL2-USER", "COMMON-LISP"),
("IN-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("FUNCTION-LAMBDA-EXPRESSION", "ACL2-USER", "COMMON-LISP"),
("INCF", "ACL2-USER", "COMMON-LISP"),
("FUNCTIONP", "ACL2-USER", "COMMON-LISP"),
("INITIALIZE-INSTANCE", "ACL2-USER", "COMMON-LISP"),
("GCD", "ACL2-USER", "COMMON-LISP"),
("INLINE", "ACL2-USER", "COMMON-LISP"),
("GENERIC-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("INPUT-STREAM-P", "ACL2-USER", "COMMON-LISP"),
("GENSYM", "ACL2-USER", "COMMON-LISP"),
("INSPECT", "ACL2-USER", "COMMON-LISP"),
("GENTEMP", "ACL2-USER", "COMMON-LISP"),
("INTEGER", "ACL2-USER", "COMMON-LISP"),
("GET", "ACL2-USER", "COMMON-LISP"),
("INTEGER-DECODE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("GET-DECODED-TIME", "ACL2-USER", "COMMON-LISP"),
("INTEGER-LENGTH", "ACL2-USER", "COMMON-LISP"),
("GET-DISPATCH-MACRO-CHARACTER", "ACL2-USER", "COMMON-LISP"),
("INTEGERP", "ACL2-USER", "COMMON-LISP"),
("GET-INTERNAL-REAL-TIME", "ACL2-USER", "COMMON-LISP"),
("INTERACTIVE-STREAM-P", "ACL2-USER", "COMMON-LISP"),
("INTERN", "ACL2-USER", "COMMON-LISP"),
("LISP-IMPLEMENTATION-TYPE", "ACL2-USER", "COMMON-LISP"),
("INTERNAL-TIME-UNITS-PER-SECOND", "ACL2-USER", "COMMON-LISP"),
("LISP-IMPLEMENTATION-VERSION", "ACL2-USER", "COMMON-LISP"),
("INTERSECTION", "ACL2-USER", "COMMON-LISP"),
("LIST", "ACL2-USER", "COMMON-LISP"),
("INVALID-METHOD-ERROR", "ACL2-USER", "COMMON-LISP"),
("LIST*", "ACL2-USER", "COMMON-LISP"),
("INVOKE-DEBUGGER", "ACL2-USER", "COMMON-LISP"),
("LIST-ALL-PACKAGES", "ACL2-USER", "COMMON-LISP"),
("INVOKE-RESTART", "ACL2-USER", "COMMON-LISP"),
("LIST-LENGTH", "ACL2-USER", "COMMON-LISP"),
("INVOKE-RESTART-INTERACTIVELY", "ACL2-USER", "COMMON-LISP"),
("LISTEN", "ACL2-USER", "COMMON-LISP"),
("ISQRT", "ACL2-USER", "COMMON-LISP"),
("LISTP", "ACL2-USER", "COMMON-LISP"),
("KEYWORD", "ACL2-USER", "COMMON-LISP"),
("LOAD", "ACL2-USER", "COMMON-LISP"),
("KEYWORDP", "ACL2-USER", "COMMON-LISP"),
("LOAD-LOGICAL-PATHNAME-TRANSLATIONS", "ACL2-USER", "COMMON-LISP"),
("LABELS", "ACL2-USER", "COMMON-LISP"),
("LOAD-TIME-VALUE", "ACL2-USER", "COMMON-LISP"),
("LAMBDA", "ACL2-USER", "COMMON-LISP"),
("LOCALLY", "ACL2-USER", "COMMON-LISP"),
("LAMBDA-LIST-KEYWORDS", "ACL2-USER", "COMMON-LISP"),
("LOG", "ACL2-USER", "COMMON-LISP"),
("LAMBDA-PARAMETERS-LIMIT", "ACL2-USER", "COMMON-LISP"),
("LOGAND", "ACL2-USER", "COMMON-LISP"),
("LAST", "ACL2-USER", "COMMON-LISP"),
("LOGANDC1", "ACL2-USER", "COMMON-LISP"),
("LCM", "ACL2-USER", "COMMON-LISP"),
("LOGANDC2", "ACL2-USER", "COMMON-LISP"),
("LDB", "ACL2-USER", "COMMON-LISP"),
("LOGBITP", "ACL2-USER", "COMMON-LISP"),
("LDB-TEST", "ACL2-USER", "COMMON-LISP"),
("LOGCOUNT", "ACL2-USER", "COMMON-LISP"),
("LDIFF", "ACL2-USER", "COMMON-LISP"),
("LOGEQV", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGICAL-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGICAL-PATHNAME-TRANSLATIONS", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGIOR", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGNAND", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGNOR", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGNOT", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGORC1", "ACL2-USER", "COMMON-LISP"),
("LEAST-NEGATIVE-SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGORC2", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGTEST", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOGXOR", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LONG-FLOAT-EPSILON", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LONG-FLOAT-NEGATIVE-EPSILON", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LONG-SITE-NAME", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOOP", "ACL2-USER", "COMMON-LISP"),
("LEAST-POSITIVE-SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("LOOP-FINISH", "ACL2-USER", "COMMON-LISP"),
("LENGTH", "ACL2-USER", "COMMON-LISP"),
("LOWER-CASE-P", "ACL2-USER", "COMMON-LISP"),
("LET", "ACL2-USER", "COMMON-LISP"),
("MACHINE-INSTANCE", "ACL2-USER", "COMMON-LISP"),
("LET*", "ACL2-USER", "COMMON-LISP"),
("MACHINE-TYPE", "ACL2-USER", "COMMON-LISP"),
("MACHINE-VERSION", "ACL2-USER", "COMMON-LISP"),
("MASK-FIELD", "ACL2-USER", "COMMON-LISP"),
("MACRO-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("MAX", "ACL2-USER", "COMMON-LISP"),
("MACROEXPAND", "ACL2-USER", "COMMON-LISP"),
("MEMBER", "ACL2-USER", "COMMON-LISP"),
("MACROEXPAND-1", "ACL2-USER", "COMMON-LISP"),
("MEMBER-IF", "ACL2-USER", "COMMON-LISP"),
("MACROLET", "ACL2-USER", "COMMON-LISP"),
("MEMBER-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("MAKE-ARRAY", "ACL2-USER", "COMMON-LISP"),
("MERGE", "ACL2-USER", "COMMON-LISP"),
("MAKE-BROADCAST-STREAM", "ACL2-USER", "COMMON-LISP"),
("MERGE-PATHNAMES", "ACL2-USER", "COMMON-LISP"),
("MAKE-CONCATENATED-STREAM", "ACL2-USER", "COMMON-LISP"),
("METHOD", "ACL2-USER", "COMMON-LISP"),
("MAKE-CONDITION", "ACL2-USER", "COMMON-LISP"),
("METHOD-COMBINATION", "ACL2-USER", "COMMON-LISP"),
("MAKE-DISPATCH-MACRO-CHARACTER", "ACL2-USER", "COMMON-LISP"),
("METHOD-COMBINATION-ERROR", "ACL2-USER", "COMMON-LISP"),
("MAKE-ECHO-STREAM", "ACL2-USER", "COMMON-LISP"),
("METHOD-QUALIFIERS", "ACL2-USER", "COMMON-LISP"),
("MAKE-HASH-TABLE", "ACL2-USER", "COMMON-LISP"),
("MIN", "ACL2-USER", "COMMON-LISP"),
("MAKE-INSTANCE", "ACL2-USER", "COMMON-LISP"),
("MINUSP", "ACL2-USER", "COMMON-LISP"),
("MAKE-INSTANCES-OBSOLETE", "ACL2-USER", "COMMON-LISP"),
("MISMATCH", "ACL2-USER", "COMMON-LISP"),
("MAKE-LIST", "ACL2-USER", "COMMON-LISP"),
("MOD", "ACL2-USER", "COMMON-LISP"),
("MAKE-LOAD-FORM", "ACL2-USER", "COMMON-LISP"),
("MOST-NEGATIVE-DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-LOAD-FORM-SAVING-SLOTS", "ACL2-USER", "COMMON-LISP"),
("MOST-NEGATIVE-FIXNUM", "ACL2-USER", "COMMON-LISP"),
("MAKE-METHOD", "ACL2-USER", "COMMON-LISP"),
("MOST-NEGATIVE-LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("MOST-NEGATIVE-SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("MOST-NEGATIVE-SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-RANDOM-STATE", "ACL2-USER", "COMMON-LISP"),
("MOST-POSITIVE-DOUBLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-SEQUENCE", "ACL2-USER", "COMMON-LISP"),
("MOST-POSITIVE-FIXNUM", "ACL2-USER", "COMMON-LISP"),
("MAKE-STRING", "ACL2-USER", "COMMON-LISP"),
("MOST-POSITIVE-LONG-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-STRING-INPUT-STREAM", "ACL2-USER", "COMMON-LISP"),
("MOST-POSITIVE-SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-STRING-OUTPUT-STREAM", "ACL2-USER", "COMMON-LISP"),
("MOST-POSITIVE-SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("MAKE-SYMBOL", "ACL2-USER", "COMMON-LISP"),
("MUFFLE-WARNING", "ACL2-USER", "COMMON-LISP"),
("MAKE-SYNONYM-STREAM", "ACL2-USER", "COMMON-LISP"),
("MULTIPLE-VALUE-BIND", "ACL2-USER", "COMMON-LISP"),
("MAKE-TWO-WAY-STREAM", "ACL2-USER", "COMMON-LISP"),
("MULTIPLE-VALUE-CALL", "ACL2-USER", "COMMON-LISP"),
("MAKUNBOUND", "ACL2-USER", "COMMON-LISP"),
("MULTIPLE-VALUE-LIST", "ACL2-USER", "COMMON-LISP"),
("MAP", "ACL2-USER", "COMMON-LISP"),
("MULTIPLE-VALUE-PROG1", "ACL2-USER", "COMMON-LISP"),
("MAP-INTO", "ACL2-USER", "COMMON-LISP"),
("MULTIPLE-VALUE-SETQ", "ACL2-USER", "COMMON-LISP"),
("MAPC", "ACL2-USER", "COMMON-LISP"),
("MULTIPLE-VALUES-LIMIT", "ACL2-USER", "COMMON-LISP"),
("MAPCAN", "ACL2-USER", "COMMON-LISP"),
("NAME-CHAR", "ACL2-USER", "COMMON-LISP"),
("MAPCAR", "ACL2-USER", "COMMON-LISP"),
("NAMESTRING", "ACL2-USER", "COMMON-LISP"),
("MAPCON", "ACL2-USER", "COMMON-LISP"),
("NBUTLAST", "ACL2-USER", "COMMON-LISP"),
("MAPHASH", "ACL2-USER", "COMMON-LISP"),
("NCONC", "ACL2-USER", "COMMON-LISP"),
("MAPL", "ACL2-USER", "COMMON-LISP"),
("NEXT-METHOD-P", "ACL2-USER", "COMMON-LISP"),
("MAPLIST", "ACL2-USER", "COMMON-LISP"),
("NIL", "ACL2-USER", "COMMON-LISP"),
("NINTERSECTION", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-ERROR", "ACL2-USER", "COMMON-LISP"),
("NINTH", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-ERROR-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("NO-APPLICABLE-METHOD", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-NAME", "ACL2-USER", "COMMON-LISP"),
("NO-NEXT-METHOD", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-NICKNAMES", "ACL2-USER", "COMMON-LISP"),
("NOT", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-SHADOWING-SYMBOLS", "ACL2-USER", "COMMON-LISP"),
("NOTANY", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-USE-LIST", "ACL2-USER", "COMMON-LISP"),
("NOTEVERY", "ACL2-USER", "COMMON-LISP"),
("PACKAGE-USED-BY-LIST", "ACL2-USER", "COMMON-LISP"),
("NOTINLINE", "ACL2-USER", "COMMON-LISP"),
("PACKAGEP", "ACL2-USER", "COMMON-LISP"),
("NRECONC", "ACL2-USER", "COMMON-LISP"),
("PAIRLIS", "ACL2-USER", "COMMON-LISP"),
("NREVERSE", "ACL2-USER", "COMMON-LISP"),
("PARSE-ERROR", "ACL2-USER", "COMMON-LISP"),
("NSET-DIFFERENCE", "ACL2-USER", "COMMON-LISP"),
("PARSE-INTEGER", "ACL2-USER", "COMMON-LISP"),
("NSET-EXCLUSIVE-OR", "ACL2-USER", "COMMON-LISP"),
("PARSE-NAMESTRING", "ACL2-USER", "COMMON-LISP"),
("NSTRING-CAPITALIZE", "ACL2-USER", "COMMON-LISP"),
("PATHNAME", "ACL2-USER", "COMMON-LISP"),
("NSTRING-DOWNCASE", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-DEVICE", "ACL2-USER", "COMMON-LISP"),
("NSTRING-UPCASE", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-DIRECTORY", "ACL2-USER", "COMMON-LISP"),
("NSUBLIS", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-HOST", "ACL2-USER", "COMMON-LISP"),
("NSUBST", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-MATCH-P", "ACL2-USER", "COMMON-LISP"),
("NSUBST-IF", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-NAME", "ACL2-USER", "COMMON-LISP"),
("NSUBST-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-TYPE", "ACL2-USER", "COMMON-LISP"),
("NSUBSTITUTE", "ACL2-USER", "COMMON-LISP"),
("PATHNAME-VERSION", "ACL2-USER", "COMMON-LISP"),
("NSUBSTITUTE-IF", "ACL2-USER", "COMMON-LISP"),
("PATHNAMEP", "ACL2-USER", "COMMON-LISP"),
("NSUBSTITUTE-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("PEEK-CHAR", "ACL2-USER", "COMMON-LISP"),
("NTH", "ACL2-USER", "COMMON-LISP"),
("PHASE", "ACL2-USER", "COMMON-LISP"),
("NTH-VALUE", "ACL2-USER", "COMMON-LISP"),
("PI", "ACL2-USER", "COMMON-LISP"),
("NTHCDR", "ACL2-USER", "COMMON-LISP"),
("PLUSP", "ACL2-USER", "COMMON-LISP"),
("NULL", "ACL2-USER", "COMMON-LISP"),
("POP", "ACL2-USER", "COMMON-LISP"),
("NUMBER", "ACL2-USER", "COMMON-LISP"),
("POSITION", "ACL2-USER", "COMMON-LISP"),
("NUMBERP", "ACL2-USER", "COMMON-LISP"),
("POSITION-IF", "ACL2-USER", "COMMON-LISP"),
("NUMERATOR", "ACL2-USER", "COMMON-LISP"),
("POSITION-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("NUNION", "ACL2-USER", "COMMON-LISP"),
("PPRINT", "ACL2-USER", "COMMON-LISP"),
("ODDP", "ACL2-USER", "COMMON-LISP"),
("PPRINT-DISPATCH", "ACL2-USER", "COMMON-LISP"),
("OPEN", "ACL2-USER", "COMMON-LISP"),
("PPRINT-EXIT-IF-LIST-EXHAUSTED", "ACL2-USER", "COMMON-LISP"),
("OPEN-STREAM-P", "ACL2-USER", "COMMON-LISP"),
("PPRINT-FILL", "ACL2-USER", "COMMON-LISP"),
("OPTIMIZE", "ACL2-USER", "COMMON-LISP"),
("PPRINT-INDENT", "ACL2-USER", "COMMON-LISP"),
("OR", "ACL2-USER", "COMMON-LISP"),
("PPRINT-LINEAR", "ACL2-USER", "COMMON-LISP"),
("OTHERWISE", "ACL2-USER", "COMMON-LISP"),
("PPRINT-LOGICAL-BLOCK", "ACL2-USER", "COMMON-LISP"),
("OUTPUT-STREAM-P", "ACL2-USER", "COMMON-LISP"),
("PPRINT-NEWLINE", "ACL2-USER", "COMMON-LISP"),
("PACKAGE", "ACL2-USER", "COMMON-LISP"),
("PPRINT-POP", "ACL2-USER", "COMMON-LISP"),
("PPRINT-TAB", "ACL2-USER", "COMMON-LISP"),
("READ-CHAR", "ACL2-USER", "COMMON-LISP"),
("PPRINT-TABULAR", "ACL2-USER", "COMMON-LISP"),
("READ-CHAR-NO-HANG", "ACL2-USER", "COMMON-LISP"),
("PRIN1", "ACL2-USER", "COMMON-LISP"),
("READ-DELIMITED-LIST", "ACL2-USER", "COMMON-LISP"),
("PRIN1-TO-STRING", "ACL2-USER", "COMMON-LISP"),
("READ-FROM-STRING", "ACL2-USER", "COMMON-LISP"),
("PRINC", "ACL2-USER", "COMMON-LISP"),
("READ-LINE", "ACL2-USER", "COMMON-LISP"),
("PRINC-TO-STRING", "ACL2-USER", "COMMON-LISP"),
("READ-PRESERVING-WHITESPACE", "ACL2-USER", "COMMON-LISP"),
("PRINT", "ACL2-USER", "COMMON-LISP"),
("READ-SEQUENCE", "ACL2-USER", "COMMON-LISP"),
("PRINT-NOT-READABLE", "ACL2-USER", "COMMON-LISP"),
("READER-ERROR", "ACL2-USER", "COMMON-LISP"),
("PRINT-NOT-READABLE-OBJECT", "ACL2-USER", "COMMON-LISP"),
("READTABLE", "ACL2-USER", "COMMON-LISP"),
("PRINT-OBJECT", "ACL2-USER", "COMMON-LISP"),
("READTABLE-CASE", "ACL2-USER", "COMMON-LISP"),
("PRINT-UNREADABLE-OBJECT", "ACL2-USER", "COMMON-LISP"),
("READTABLEP", "ACL2-USER", "COMMON-LISP"),
("PROBE-FILE", "ACL2-USER", "COMMON-LISP"),
("REAL", "ACL2-USER", "COMMON-LISP"),
("PROCLAIM", "ACL2-USER", "COMMON-LISP"),
("REALP", "ACL2-USER", "COMMON-LISP"),
("PROG", "ACL2-USER", "COMMON-LISP"),
("REALPART", "ACL2-USER", "COMMON-LISP"),
("PROG*", "ACL2-USER", "COMMON-LISP"),
("REDUCE", "ACL2-USER", "COMMON-LISP"),
("PROG1", "ACL2-USER", "COMMON-LISP"),
("REINITIALIZE-INSTANCE", "ACL2-USER", "COMMON-LISP"),
("PROG2", "ACL2-USER", "COMMON-LISP"),
("REM", "ACL2-USER", "COMMON-LISP"),
("PROGN", "ACL2-USER", "COMMON-LISP"),
("REMF", "ACL2-USER", "COMMON-LISP"),
("PROGRAM-ERROR", "ACL2-USER", "COMMON-LISP"),
("REMHASH", "ACL2-USER", "COMMON-LISP"),
("PROGV", "ACL2-USER", "COMMON-LISP"),
("REMOVE", "ACL2-USER", "COMMON-LISP"),
("PROVIDE", "ACL2-USER", "COMMON-LISP"),
("REMOVE-DUPLICATES", "ACL2-USER", "COMMON-LISP"),
("PSETF", "ACL2-USER", "COMMON-LISP"),
("REMOVE-IF", "ACL2-USER", "COMMON-LISP"),
("PSETQ", "ACL2-USER", "COMMON-LISP"),
("REMOVE-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("PUSH", "ACL2-USER", "COMMON-LISP"),
("REMOVE-METHOD", "ACL2-USER", "COMMON-LISP"),
("PUSHNEW", "ACL2-USER", "COMMON-LISP"),
("REMPROP", "ACL2-USER", "COMMON-LISP"),
("QUOTE", "ACL2-USER", "COMMON-LISP"),
("RENAME-FILE", "ACL2-USER", "COMMON-LISP"),
("RANDOM", "ACL2-USER", "COMMON-LISP"),
("RENAME-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("RANDOM-STATE", "ACL2-USER", "COMMON-LISP"),
("REPLACE", "ACL2-USER", "COMMON-LISP"),
("RANDOM-STATE-P", "ACL2-USER", "COMMON-LISP"),
("REQUIRE", "ACL2-USER", "COMMON-LISP"),
("RASSOC", "ACL2-USER", "COMMON-LISP"),
("REST", "ACL2-USER", "COMMON-LISP"),
("RASSOC-IF", "ACL2-USER", "COMMON-LISP"),
("RESTART", "ACL2-USER", "COMMON-LISP"),
("RASSOC-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("RESTART-BIND", "ACL2-USER", "COMMON-LISP"),
("RATIO", "ACL2-USER", "COMMON-LISP"),
("RESTART-CASE", "ACL2-USER", "COMMON-LISP"),
("RATIONAL", "ACL2-USER", "COMMON-LISP"),
("RESTART-NAME", "ACL2-USER", "COMMON-LISP"),
("RATIONALIZE", "ACL2-USER", "COMMON-LISP"),
("RETURN", "ACL2-USER", "COMMON-LISP"),
("RATIONALP", "ACL2-USER", "COMMON-LISP"),
("RETURN-FROM", "ACL2-USER", "COMMON-LISP"),
("READ", "ACL2-USER", "COMMON-LISP"),
("REVAPPEND", "ACL2-USER", "COMMON-LISP"),
("READ-BYTE", "ACL2-USER", "COMMON-LISP"),
("REVERSE", "ACL2-USER", "COMMON-LISP"),
("ROOM", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-BIT-VECTOR", "ACL2-USER", "COMMON-LISP"),
("ROTATEF", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-BIT-VECTOR-P", "ACL2-USER", "COMMON-LISP"),
("ROUND", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-CONDITION", "ACL2-USER", "COMMON-LISP"),
("ROW-MAJOR-AREF", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-CONDITION-FORMAT-ARGUMENTS", "ACL2-USER", "COMMON-LISP"),
("RPLACA", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-CONDITION-FORMAT-CONTROL", "ACL2-USER", "COMMON-LISP"),
("RPLACD", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-ERROR", "ACL2-USER", "COMMON-LISP"),
("SAFETY", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-STRING", "ACL2-USER", "COMMON-LISP"),
("SATISFIES", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-STRING-P", "ACL2-USER", "COMMON-LISP"),
("SBIT", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-TYPE-ERROR", "ACL2-USER", "COMMON-LISP"),
("SCALE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-VECTOR", "ACL2-USER", "COMMON-LISP"),
("SCHAR", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-VECTOR-P", "ACL2-USER", "COMMON-LISP"),
("SEARCH", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-WARNING", "ACL2-USER", "COMMON-LISP"),
("SECOND", "ACL2-USER", "COMMON-LISP"),
("SIN", "ACL2-USER", "COMMON-LISP"),
("SEQUENCE", "ACL2-USER", "COMMON-LISP"),
("SINGLE-FLOAT", "ACL2-USER", "COMMON-LISP"),
("SERIOUS-CONDITION", "ACL2-USER", "COMMON-LISP"),
("SINGLE-FLOAT-EPSILON", "ACL2-USER", "COMMON-LISP"),
("SET", "ACL2-USER", "COMMON-LISP"),
("SINGLE-FLOAT-NEGATIVE-EPSILON", "ACL2-USER", "COMMON-LISP"),
("SET-DIFFERENCE", "ACL2-USER", "COMMON-LISP"),
("SINH", "ACL2-USER", "COMMON-LISP"),
("SET-DISPATCH-MACRO-CHARACTER", "ACL2-USER", "COMMON-LISP"),
("SIXTH", "ACL2-USER", "COMMON-LISP"),
("SET-EXCLUSIVE-OR", "ACL2-USER", "COMMON-LISP"),
("SLEEP", "ACL2-USER", "COMMON-LISP"),
("SET-MACRO-CHARACTER", "ACL2-USER", "COMMON-LISP"),
("SLOT-BOUNDP", "ACL2-USER", "COMMON-LISP"),
("SET-PPRINT-DISPATCH", "ACL2-USER", "COMMON-LISP"),
("SLOT-EXISTS-P", "ACL2-USER", "COMMON-LISP"),
("SET-SYNTAX-FROM-CHAR", "ACL2-USER", "COMMON-LISP"),
("SLOT-MAKUNBOUND", "ACL2-USER", "COMMON-LISP"),
("SETF", "ACL2-USER", "COMMON-LISP"),
("SLOT-MISSING", "ACL2-USER", "COMMON-LISP"),
("SETQ", "ACL2-USER", "COMMON-LISP"),
("SLOT-UNBOUND", "ACL2-USER", "COMMON-LISP"),
("SEVENTH", "ACL2-USER", "COMMON-LISP"),
("SLOT-VALUE", "ACL2-USER", "COMMON-LISP"),
("SHADOW", "ACL2-USER", "COMMON-LISP"),
("SOFTWARE-TYPE", "ACL2-USER", "COMMON-LISP"),
("SHADOWING-IMPORT", "ACL2-USER", "COMMON-LISP"),
("SOFTWARE-VERSION", "ACL2-USER", "COMMON-LISP"),
("SHARED-INITIALIZE", "ACL2-USER", "COMMON-LISP"),
("SOME", "ACL2-USER", "COMMON-LISP"),
("SHIFTF", "ACL2-USER", "COMMON-LISP"),
("SORT", "ACL2-USER", "COMMON-LISP"),
("SHORT-FLOAT", "ACL2-USER", "COMMON-LISP"),
("SPACE", "ACL2-USER", "COMMON-LISP"),
("SHORT-FLOAT-EPSILON", "ACL2-USER", "COMMON-LISP"),
("SPECIAL", "ACL2-USER", "COMMON-LISP"),
("SHORT-FLOAT-NEGATIVE-EPSILON", "ACL2-USER", "COMMON-LISP"),
("SPECIAL-OPERATOR-P", "ACL2-USER", "COMMON-LISP"),
("SHORT-SITE-NAME", "ACL2-USER", "COMMON-LISP"),
("SPEED", "ACL2-USER", "COMMON-LISP"),
("SIGNAL", "ACL2-USER", "COMMON-LISP"),
("SQRT", "ACL2-USER", "COMMON-LISP"),
("SIGNED-BYTE", "ACL2-USER", "COMMON-LISP"),
("STABLE-SORT", "ACL2-USER", "COMMON-LISP"),
("SIGNUM", "ACL2-USER", "COMMON-LISP"),
("STANDARD", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-ARRAY", "ACL2-USER", "COMMON-LISP"),
("STANDARD-CHAR", "ACL2-USER", "COMMON-LISP"),
("SIMPLE-BASE-STRING", "ACL2-USER", "COMMON-LISP"),
("STANDARD-CHAR-P", "ACL2-USER", "COMMON-LISP"),
("STANDARD-CLASS", "ACL2-USER", "COMMON-LISP"),
("SUBLIS", "ACL2-USER", "COMMON-LISP"),
("STANDARD-GENERIC-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("SUBSEQ", "ACL2-USER", "COMMON-LISP"),
("STANDARD-METHOD", "ACL2-USER", "COMMON-LISP"),
("SUBSETP", "ACL2-USER", "COMMON-LISP"),
("STANDARD-OBJECT", "ACL2-USER", "COMMON-LISP"),
("SUBST", "ACL2-USER", "COMMON-LISP"),
("STEP", "ACL2-USER", "COMMON-LISP"),
("SUBST-IF", "ACL2-USER", "COMMON-LISP"),
("STORAGE-CONDITION", "ACL2-USER", "COMMON-LISP"),
("SUBST-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("STORE-VALUE", "ACL2-USER", "COMMON-LISP"),
("SUBSTITUTE", "ACL2-USER", "COMMON-LISP"),
("STREAM", "ACL2-USER", "COMMON-LISP"),
("SUBSTITUTE-IF", "ACL2-USER", "COMMON-LISP"),
("STREAM-ELEMENT-TYPE", "ACL2-USER", "COMMON-LISP"),
("SUBSTITUTE-IF-NOT", "ACL2-USER", "COMMON-LISP"),
("STREAM-ERROR", "ACL2-USER", "COMMON-LISP"),
("SUBTYPEP", "ACL2-USER", "COMMON-LISP"),
("STREAM-ERROR-STREAM", "ACL2-USER", "COMMON-LISP"),
("SVREF", "ACL2-USER", "COMMON-LISP"),
("STREAM-EXTERNAL-FORMAT", "ACL2-USER", "COMMON-LISP"),
("SXHASH", "ACL2-USER", "COMMON-LISP"),
("STREAMP", "ACL2-USER", "COMMON-LISP"),
("SYMBOL", "ACL2-USER", "COMMON-LISP"),
("STRING", "ACL2-USER", "COMMON-LISP"),
("SYMBOL-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("STRING-CAPITALIZE", "ACL2-USER", "COMMON-LISP"),
("SYMBOL-MACROLET", "ACL2-USER", "COMMON-LISP"),
("STRING-DOWNCASE", "ACL2-USER", "COMMON-LISP"),
("SYMBOL-NAME", "ACL2-USER", "COMMON-LISP"),
("STRING-EQUAL", "ACL2-USER", "COMMON-LISP"),
("SYMBOL-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("STRING-GREATERP", "ACL2-USER", "COMMON-LISP"),
("SYMBOL-PLIST", "ACL2-USER", "COMMON-LISP"),
("STRING-LEFT-TRIM", "ACL2-USER", "COMMON-LISP"),
("SYMBOL-VALUE", "ACL2-USER", "COMMON-LISP"),
("STRING-LESSP", "ACL2-USER", "COMMON-LISP"),
("SYMBOLP", "ACL2-USER", "COMMON-LISP"),
("STRING-NOT-EQUAL", "ACL2-USER", "COMMON-LISP"),
("SYNONYM-STREAM", "ACL2-USER", "COMMON-LISP"),
("STRING-NOT-GREATERP", "ACL2-USER", "COMMON-LISP"),
("SYNONYM-STREAM-SYMBOL", "ACL2-USER", "COMMON-LISP"),
("STRING-NOT-LESSP", "ACL2-USER", "COMMON-LISP"),
("T", "ACL2-USER", "COMMON-LISP"),
("STRING-RIGHT-TRIM", "ACL2-USER", "COMMON-LISP"),
("TAGBODY", "ACL2-USER", "COMMON-LISP"),
("STRING-STREAM", "ACL2-USER", "COMMON-LISP"),
("TAILP", "ACL2-USER", "COMMON-LISP"),
("STRING-TRIM", "ACL2-USER", "COMMON-LISP"),
("TAN", "ACL2-USER", "COMMON-LISP"),
("STRING-UPCASE", "ACL2-USER", "COMMON-LISP"),
("TANH", "ACL2-USER", "COMMON-LISP"),
("STRING/=", "ACL2-USER", "COMMON-LISP"),
("TENTH", "ACL2-USER", "COMMON-LISP"),
("STRING<", "ACL2-USER", "COMMON-LISP"),
("TERPRI", "ACL2-USER", "COMMON-LISP"),
("STRING<=", "ACL2-USER", "COMMON-LISP"),
("THE", "ACL2-USER", "COMMON-LISP"),
("STRING=", "ACL2-USER", "COMMON-LISP"),
("THIRD", "ACL2-USER", "COMMON-LISP"),
("STRING>", "ACL2-USER", "COMMON-LISP"),
("THROW", "ACL2-USER", "COMMON-LISP"),
("STRING>=", "ACL2-USER", "COMMON-LISP"),
("TIME", "ACL2-USER", "COMMON-LISP"),
("STRINGP", "ACL2-USER", "COMMON-LISP"),
("TRACE", "ACL2-USER", "COMMON-LISP"),
("STRUCTURE", "ACL2-USER", "COMMON-LISP"),
("TRANSLATE-LOGICAL-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("STRUCTURE-CLASS", "ACL2-USER", "COMMON-LISP"),
("TRANSLATE-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("STRUCTURE-OBJECT", "ACL2-USER", "COMMON-LISP"),
("TREE-EQUAL", "ACL2-USER", "COMMON-LISP"),
("STYLE-WARNING", "ACL2-USER", "COMMON-LISP"),
("TRUENAME", "ACL2-USER", "COMMON-LISP"),
("TRUNCATE", "ACL2-USER", "COMMON-LISP"),
("VALUES-LIST", "ACL2-USER", "COMMON-LISP"),
("TWO-WAY-STREAM", "ACL2-USER", "COMMON-LISP"),
("VARIABLE", "ACL2-USER", "COMMON-LISP"),
("TWO-WAY-STREAM-INPUT-STREAM", "ACL2-USER", "COMMON-LISP"),
("VECTOR", "ACL2-USER", "COMMON-LISP"),
("TWO-WAY-STREAM-OUTPUT-STREAM", "ACL2-USER", "COMMON-LISP"),
("VECTOR-POP", "ACL2-USER", "COMMON-LISP"),
("TYPE", "ACL2-USER", "COMMON-LISP"),
("VECTOR-PUSH", "ACL2-USER", "COMMON-LISP"),
("TYPE-ERROR", "ACL2-USER", "COMMON-LISP"),
("VECTOR-PUSH-EXTEND", "ACL2-USER", "COMMON-LISP"),
("TYPE-ERROR-DATUM", "ACL2-USER", "COMMON-LISP"),
("VECTORP", "ACL2-USER", "COMMON-LISP"),
("TYPE-ERROR-EXPECTED-TYPE", "ACL2-USER", "COMMON-LISP"),
("WARN", "ACL2-USER", "COMMON-LISP"),
("TYPE-OF", "ACL2-USER", "COMMON-LISP"),
("WARNING", "ACL2-USER", "COMMON-LISP"),
("TYPECASE", "ACL2-USER", "COMMON-LISP"),
("WHEN", "ACL2-USER", "COMMON-LISP"),
("TYPEP", "ACL2-USER", "COMMON-LISP"),
("WILD-PATHNAME-P", "ACL2-USER", "COMMON-LISP"),
("UNBOUND-SLOT", "ACL2-USER", "COMMON-LISP"),
("WITH-ACCESSORS", "ACL2-USER", "COMMON-LISP"),
("UNBOUND-SLOT-INSTANCE", "ACL2-USER", "COMMON-LISP"),
("WITH-COMPILATION-UNIT", "ACL2-USER", "COMMON-LISP"),
("UNBOUND-VARIABLE", "ACL2-USER", "COMMON-LISP"),
("WITH-CONDITION-RESTARTS", "ACL2-USER", "COMMON-LISP"),
("UNDEFINED-FUNCTION", "ACL2-USER", "COMMON-LISP"),
("WITH-HASH-TABLE-ITERATOR", "ACL2-USER", "COMMON-LISP"),
("UNEXPORT", "ACL2-USER", "COMMON-LISP"),
("WITH-INPUT-FROM-STRING", "ACL2-USER", "COMMON-LISP"),
("UNINTERN", "ACL2-USER", "COMMON-LISP"),
("WITH-OPEN-FILE", "ACL2-USER", "COMMON-LISP"),
("UNION", "ACL2-USER", "COMMON-LISP"),
("WITH-OPEN-STREAM", "ACL2-USER", "COMMON-LISP"),
("UNLESS", "ACL2-USER", "COMMON-LISP"),
("WITH-OUTPUT-TO-STRING", "ACL2-USER", "COMMON-LISP"),
("UNREAD-CHAR", "ACL2-USER", "COMMON-LISP"),
("WITH-PACKAGE-ITERATOR", "ACL2-USER", "COMMON-LISP"),
("UNSIGNED-BYTE", "ACL2-USER", "COMMON-LISP"),
("WITH-SIMPLE-RESTART", "ACL2-USER", "COMMON-LISP"),
("UNTRACE", "ACL2-USER", "COMMON-LISP"),
("WITH-SLOTS", "ACL2-USER", "COMMON-LISP"),
("UNUSE-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("WITH-STANDARD-IO-SYNTAX", "ACL2-USER", "COMMON-LISP"),
("UNWIND-PROTECT", "ACL2-USER", "COMMON-LISP"),
("WRITE", "ACL2-USER", "COMMON-LISP"),
("UPDATE-INSTANCE-FOR-DIFFERENT-CLASS", "ACL2-USER", "COMMON-LISP"),
("WRITE-BYTE", "ACL2-USER", "COMMON-LISP"),
("UPDATE-INSTANCE-FOR-REDEFINED-CLASS", "ACL2-USER", "COMMON-LISP"),
("WRITE-CHAR", "ACL2-USER", "COMMON-LISP"),
("UPGRADED-ARRAY-ELEMENT-TYPE", "ACL2-USER", "COMMON-LISP"),
("WRITE-LINE", "ACL2-USER", "COMMON-LISP"),
("UPGRADED-COMPLEX-PART-TYPE", "ACL2-USER", "COMMON-LISP"),
("WRITE-SEQUENCE", "ACL2-USER", "COMMON-LISP"),
("UPPER-CASE-P", "ACL2-USER", "COMMON-LISP"),
("WRITE-STRING", "ACL2-USER", "COMMON-LISP"),
("USE-PACKAGE", "ACL2-USER", "COMMON-LISP"),
("WRITE-TO-STRING", "ACL2-USER", "COMMON-LISP"),
("USE-VALUE", "ACL2-USER", "COMMON-LISP"),
("Y-OR-N-P", "ACL2-USER", "COMMON-LISP"),
("USER-HOMEDIR-PATHNAME", "ACL2-USER", "COMMON-LISP"),
("YES-OR-NO-P", "ACL2-USER", "COMMON-LISP"),
("VALUES", "ACL2-USER", "COMMON-LISP"),
("ZEROP", "ACL2-USER", "COMMON-LISP"),
("&ALLOW-OTHER-KEYS", "ACL2", "COMMON-LISP"),
("*PRINT-MISER-WIDTH*", "ACL2", "COMMON-LISP"),
("&AUX", "ACL2", "COMMON-LISP"),
("*PRINT-PPRINT-DISPATCH*", "ACL2", "COMMON-LISP"),
("&BODY", "ACL2", "COMMON-LISP"),
("*PRINT-PRETTY*", "ACL2", "COMMON-LISP"),
("&ENVIRONMENT", "ACL2", "COMMON-LISP"),
("*PRINT-RADIX*", "ACL2", "COMMON-LISP"),
("&KEY", "ACL2", "COMMON-LISP"),
("*PRINT-READABLY*", "ACL2", "COMMON-LISP"),
("&OPTIONAL", "ACL2", "COMMON-LISP"),
("*PRINT-RIGHT-MARGIN*", "ACL2", "COMMON-LISP"),
("&REST", "ACL2", "COMMON-LISP"),
("*QUERY-IO*", "ACL2", "COMMON-LISP"),
("&WHOLE", "ACL2", "COMMON-LISP"),
("*RANDOM-STATE*", "ACL2", "COMMON-LISP"),
("*", "ACL2", "COMMON-LISP"),
("*READ-BASE*", "ACL2", "COMMON-LISP"),
("**", "ACL2", "COMMON-LISP"),
("*READ-DEFAULT-FLOAT-FORMAT*", "ACL2", "COMMON-LISP"),
("***", "ACL2", "COMMON-LISP"),
("*READ-EVAL*", "ACL2", "COMMON-LISP"),
("*BREAK-ON-SIGNALS*", "ACL2", "COMMON-LISP"),
("*READ-SUPPRESS*", "ACL2", "COMMON-LISP"),
("*COMPILE-FILE-PATHNAME*", "ACL2", "COMMON-LISP"),
("*READTABLE*", "ACL2", "COMMON-LISP"),
("*COMPILE-FILE-TRUENAME*", "ACL2", "COMMON-LISP"),
("*STANDARD-INPUT*", "ACL2", "COMMON-LISP"),
("*COMPILE-PRINT*", "ACL2", "COMMON-LISP"),
("*STANDARD-OUTPUT*", "ACL2", "COMMON-LISP"),
("*COMPILE-VERBOSE*", "ACL2", "COMMON-LISP"),
("*TERMINAL-IO*", "ACL2", "COMMON-LISP"),
("*DEBUG-IO*", "ACL2", "COMMON-LISP"),
("*TRACE-OUTPUT*", "ACL2", "COMMON-LISP"),
("*DEBUGGER-HOOK*", "ACL2", "COMMON-LISP"),
("+", "ACL2", "COMMON-LISP"),
("*DEFAULT-PATHNAME-DEFAULTS*", "ACL2", "COMMON-LISP"),
("++", "ACL2", "COMMON-LISP"),
("*ERROR-OUTPUT*", "ACL2", "COMMON-LISP"),
("+++", "ACL2", "COMMON-LISP"),
("*FEATURES*", "ACL2", "COMMON-LISP"),
("-", "ACL2", "COMMON-LISP"),
("*GENSYM-COUNTER*", "ACL2", "COMMON-LISP"),
("/", "ACL2", "COMMON-LISP"),
("*LOAD-PATHNAME*", "ACL2", "COMMON-LISP"),
("//", "ACL2", "COMMON-LISP"),
("*LOAD-PRINT*", "ACL2", "COMMON-LISP"),
("///", "ACL2", "COMMON-LISP"),
("*LOAD-TRUENAME*", "ACL2", "COMMON-LISP"),
("/=", "ACL2", "COMMON-LISP"),
("*LOAD-VERBOSE*", "ACL2", "COMMON-LISP"),
("1+", "ACL2", "COMMON-LISP"),
("*MACROEXPAND-HOOK*", "ACL2", "COMMON-LISP"),
("1-", "ACL2", "COMMON-LISP"),
("*MODULES*", "ACL2", "COMMON-LISP"),
("<", "ACL2", "COMMON-LISP"),
("*PACKAGE*", "ACL2", "COMMON-LISP"),
("<=", "ACL2", "COMMON-LISP"),
("*PRINT-ARRAY*", "ACL2", "COMMON-LISP"),
("=", "ACL2", "COMMON-LISP"),
("*PRINT-BASE*", "ACL2", "COMMON-LISP"),
(">", "ACL2", "COMMON-LISP"),
("*PRINT-CASE*", "ACL2", "COMMON-LISP"),
(">=", "ACL2", "COMMON-LISP"),
("*PRINT-CIRCLE*", "ACL2", "COMMON-LISP"),
("ABORT", "ACL2", "COMMON-LISP"),
("*PRINT-ESCAPE*", "ACL2", "COMMON-LISP"),
("ABS", "ACL2", "COMMON-LISP"),
("*PRINT-GENSYM*", "ACL2", "COMMON-LISP"),
("ACONS", "ACL2", "COMMON-LISP"),
("*PRINT-LENGTH*", "ACL2", "COMMON-LISP"),
("ACOS", "ACL2", "COMMON-LISP"),
("*PRINT-LEVEL*", "ACL2", "COMMON-LISP"),
("ACOSH", "ACL2", "COMMON-LISP"),
("*PRINT-LINES*", "ACL2", "COMMON-LISP"),
("ADD-METHOD", "ACL2", "COMMON-LISP"),
("ADJOIN", "ACL2", "COMMON-LISP"),
("ATOM", "ACL2", "COMMON-LISP"),
("BOUNDP", "ACL2", "COMMON-LISP"),
("ADJUST-ARRAY", "ACL2", "COMMON-LISP"),
("BASE-CHAR", "ACL2", "COMMON-LISP"),
("BREAK", "ACL2", "COMMON-LISP"),
("ADJUSTABLE-ARRAY-P", "ACL2", "COMMON-LISP"),
("BASE-STRING", "ACL2", "COMMON-LISP"),
("BROADCAST-STREAM", "ACL2", "COMMON-LISP"),
("ALLOCATE-INSTANCE", "ACL2", "COMMON-LISP"),
("BIGNUM", "ACL2", "COMMON-LISP"),
("BROADCAST-STREAM-STREAMS", "ACL2", "COMMON-LISP"),
("ALPHA-CHAR-P", "ACL2", "COMMON-LISP"),
("BIT", "ACL2", "COMMON-LISP"),
("BUILT-IN-CLASS", "ACL2", "COMMON-LISP"),
("ALPHANUMERICP", "ACL2", "COMMON-LISP"),
("BIT-AND", "ACL2", "COMMON-LISP"),
("BUTLAST", "ACL2", "COMMON-LISP"),
("AND", "ACL2", "COMMON-LISP"),
("BIT-ANDC1", "ACL2", "COMMON-LISP"),
("BYTE", "ACL2", "COMMON-LISP"),
("APPEND", "ACL2", "COMMON-LISP"),
("BIT-ANDC2", "ACL2", "COMMON-LISP"),
("BYTE-POSITION", "ACL2", "COMMON-LISP"),
("APPLY", "ACL2", "COMMON-LISP"),
("BIT-EQV", "ACL2", "COMMON-LISP"),
("BYTE-SIZE", "ACL2", "COMMON-LISP"),
("APROPOS", "ACL2", "COMMON-LISP"),
("BIT-IOR", "ACL2", "COMMON-LISP"),
("CAAAAR", "ACL2", "COMMON-LISP"),
("APROPOS-LIST", "ACL2", "COMMON-LISP"),
("BIT-NAND", "ACL2", "COMMON-LISP"),
("CAAADR", "ACL2", "COMMON-LISP"),
("AREF", "ACL2", "COMMON-LISP"),
("BIT-NOR", "ACL2", "COMMON-LISP"),
("CAAAR", "ACL2", "COMMON-LISP"),
("ARITHMETIC-ERROR", "ACL2", "COMMON-LISP"),
("BIT-NOT", "ACL2", "COMMON-LISP"),
("CAADAR", "ACL2", "COMMON-LISP"),
("ARITHMETIC-ERROR-OPERANDS", "ACL2", "COMMON-LISP"),
("BIT-ORC1", "ACL2", "COMMON-LISP"),
("CAADDR", "ACL2", "COMMON-LISP"),
("ARITHMETIC-ERROR-OPERATION", "ACL2", "COMMON-LISP"),
("BIT-ORC2", "ACL2", "COMMON-LISP"),
("CAADR", "ACL2", "COMMON-LISP"),
("ARRAY", "ACL2", "COMMON-LISP"),
("BIT-VECTOR", "ACL2", "COMMON-LISP"),
("CAAR", "ACL2", "COMMON-LISP"),
("ARRAY-DIMENSION", "ACL2", "COMMON-LISP"),
("BIT-VECTOR-P", "ACL2", "COMMON-LISP"),
("CADAAR", "ACL2", "COMMON-LISP"),
("ARRAY-DIMENSION-LIMIT", "ACL2", "COMMON-LISP"),
("BIT-XOR", "ACL2", "COMMON-LISP"),
("CADADR", "ACL2", "COMMON-LISP"),
("ARRAY-DIMENSIONS", "ACL2", "COMMON-LISP"),
("BLOCK", "ACL2", "COMMON-LISP"),
("CADAR", "ACL2", "COMMON-LISP"),
("ARRAY-DISPLACEMENT", "ACL2", "COMMON-LISP"),
("BOOLE", "ACL2", "COMMON-LISP"),
("CADDAR", "ACL2", "COMMON-LISP"),
("ARRAY-ELEMENT-TYPE", "ACL2", "COMMON-LISP"),
("BOOLE-1", "ACL2", "COMMON-LISP"),
("CADDDR", "ACL2", "COMMON-LISP"),
("ARRAY-HAS-FILL-POINTER-P", "ACL2", "COMMON-LISP"),
("BOOLE-2", "ACL2", "COMMON-LISP"),
("CADDR", "ACL2", "COMMON-LISP"),
("ARRAY-IN-BOUNDS-P", "ACL2", "COMMON-LISP"),
("BOOLE-AND", "ACL2", "COMMON-LISP"),
("CADR", "ACL2", "COMMON-LISP"),
("ARRAY-RANK", "ACL2", "COMMON-LISP"),
("BOOLE-ANDC1", "ACL2", "COMMON-LISP"),
("CALL-ARGUMENTS-LIMIT", "ACL2", "COMMON-LISP"),
("ARRAY-RANK-LIMIT", "ACL2", "COMMON-LISP"),
("BOOLE-ANDC2", "ACL2", "COMMON-LISP"),
("CALL-METHOD", "ACL2", "COMMON-LISP"),
("ARRAY-ROW-MAJOR-INDEX", "ACL2", "COMMON-LISP"),
("BOOLE-C1", "ACL2", "COMMON-LISP"),
("CALL-NEXT-METHOD", "ACL2", "COMMON-LISP"),
("ARRAY-TOTAL-SIZE", "ACL2", "COMMON-LISP"),
("BOOLE-C2", "ACL2", "COMMON-LISP"),
("CAR", "ACL2", "COMMON-LISP"),
("ARRAY-TOTAL-SIZE-LIMIT", "ACL2", "COMMON-LISP"),
("BOOLE-CLR", "ACL2", "COMMON-LISP"),
("CASE", "ACL2", "COMMON-LISP"),
("ARRAYP", "ACL2", "COMMON-LISP"),
("BOOLE-EQV", "ACL2", "COMMON-LISP"),
("CATCH", "ACL2", "COMMON-LISP"),
("ASH", "ACL2", "COMMON-LISP"),
("BOOLE-IOR", "ACL2", "COMMON-LISP"),
("CCASE", "ACL2", "COMMON-LISP"),
("ASIN", "ACL2", "COMMON-LISP"),
("BOOLE-NAND", "ACL2", "COMMON-LISP"),
("CDAAAR", "ACL2", "COMMON-LISP"),
("ASINH", "ACL2", "COMMON-LISP"),
("BOOLE-NOR", "ACL2", "COMMON-LISP"),
("CDAADR", "ACL2", "COMMON-LISP"),
("ASSERT", "ACL2", "COMMON-LISP"),
("BOOLE-ORC1", "ACL2", "COMMON-LISP"),
("CDAAR", "ACL2", "COMMON-LISP"),
("ASSOC", "ACL2", "COMMON-LISP"),
("BOOLE-ORC2", "ACL2", "COMMON-LISP"),
("CDADAR", "ACL2", "COMMON-LISP"),
("ASSOC-IF", "ACL2", "COMMON-LISP"),
("BOOLE-SET", "ACL2", "COMMON-LISP"),
("CDADDR", "ACL2", "COMMON-LISP"),
("ASSOC-IF-NOT", "ACL2", "COMMON-LISP"),
("BOOLE-XOR", "ACL2", "COMMON-LISP"),
("CDADR", "ACL2", "COMMON-LISP"),
("ATAN", "ACL2", "COMMON-LISP"),
("BOOLEAN", "ACL2", "COMMON-LISP"),
("CDAR", "ACL2", "COMMON-LISP"),
("ATANH", "ACL2", "COMMON-LISP"),
("BOTH-CASE-P", "ACL2", "COMMON-LISP"),
("CDDAAR", "ACL2", "COMMON-LISP"),
("CDDADR", "ACL2", "COMMON-LISP"),
("CLEAR-INPUT", "ACL2", "COMMON-LISP"),
("COPY-TREE", "ACL2", "COMMON-LISP"),
("CDDAR", "ACL2", "COMMON-LISP"),
("CLEAR-OUTPUT", "ACL2", "COMMON-LISP"),
("COS", "ACL2", "COMMON-LISP"),
("CDDDAR", "ACL2", "COMMON-LISP"),
("CLOSE", "ACL2", "COMMON-LISP"),
("COSH", "ACL2", "COMMON-LISP"),
("CDDDDR", "ACL2", "COMMON-LISP"),
("CLRHASH", "ACL2", "COMMON-LISP"),
("COUNT", "ACL2", "COMMON-LISP"),
("CDDDR", "ACL2", "COMMON-LISP"),
("CODE-CHAR", "ACL2", "COMMON-LISP"),
("COUNT-IF", "ACL2", "COMMON-LISP"),
("CDDR", "ACL2", "COMMON-LISP"),
("COERCE", "ACL2", "COMMON-LISP"),
("COUNT-IF-NOT", "ACL2", "COMMON-LISP"),
("CDR", "ACL2", "COMMON-LISP"),
("COMPILATION-SPEED", "ACL2", "COMMON-LISP"),
("CTYPECASE", "ACL2", "COMMON-LISP"),
("CEILING", "ACL2", "COMMON-LISP"),
("COMPILE", "ACL2", "COMMON-LISP"),
("DEBUG", "ACL2", "COMMON-LISP"),
("CELL-ERROR", "ACL2", "COMMON-LISP"),
("COMPILE-FILE", "ACL2", "COMMON-LISP"),
("DECF", "ACL2", "COMMON-LISP"),
("CELL-ERROR-NAME", "ACL2", "COMMON-LISP"),
("COMPILE-FILE-PATHNAME", "ACL2", "COMMON-LISP"),
("DECLAIM", "ACL2", "COMMON-LISP"),
("CERROR", "ACL2", "COMMON-LISP"),
("COMPILED-FUNCTION", "ACL2", "COMMON-LISP"),
("DECLARATION", "ACL2", "COMMON-LISP"),
("CHANGE-CLASS", "ACL2", "COMMON-LISP"),
("COMPILED-FUNCTION-P", "ACL2", "COMMON-LISP"),
("DECLARE", "ACL2", "COMMON-LISP"),
("CHAR", "ACL2", "COMMON-LISP"),
("COMPILER-MACRO", "ACL2", "COMMON-LISP"),
("DECODE-FLOAT", "ACL2", "COMMON-LISP"),
("CHAR-CODE", "ACL2", "COMMON-LISP"),
("COMPILER-MACRO-FUNCTION", "ACL2", "COMMON-LISP"),
("DECODE-UNIVERSAL-TIME", "ACL2", "COMMON-LISP"),
("CHAR-CODE-LIMIT", "ACL2", "COMMON-LISP"),
("COMPLEMENT", "ACL2", "COMMON-LISP"),
("DEFCLASS", "ACL2", "COMMON-LISP"),
("CHAR-DOWNCASE", "ACL2", "COMMON-LISP"),
("COMPLEX", "ACL2", "COMMON-LISP"),
("DEFCONSTANT", "ACL2", "COMMON-LISP"),
("CHAR-EQUAL", "ACL2", "COMMON-LISP"),
("COMPLEXP", "ACL2", "COMMON-LISP"),
("DEFGENERIC", "ACL2", "COMMON-LISP"),
("CHAR-GREATERP", "ACL2", "COMMON-LISP"),
("COMPUTE-APPLICABLE-METHODS", "ACL2", "COMMON-LISP"),
("DEFINE-COMPILER-MACRO", "ACL2", "COMMON-LISP"),
("CHAR-INT", "ACL2", "COMMON-LISP"),
("COMPUTE-RESTARTS", "ACL2", "COMMON-LISP"),
("DEFINE-CONDITION", "ACL2", "COMMON-LISP"),
("CHAR-LESSP", "ACL2", "COMMON-LISP"),
("CONCATENATE", "ACL2", "COMMON-LISP"),
("DEFINE-METHOD-COMBINATION", "ACL2", "COMMON-LISP"),
("CHAR-NAME", "ACL2", "COMMON-LISP"),
("CONCATENATED-STREAM", "ACL2", "COMMON-LISP"),
("DEFINE-MODIFY-MACRO", "ACL2", "COMMON-LISP"),
("CHAR-NOT-EQUAL", "ACL2", "COMMON-LISP"),
("CONCATENATED-STREAM-STREAMS", "ACL2", "COMMON-LISP"),
("DEFINE-SETF-EXPANDER", "ACL2", "COMMON-LISP"),
("CHAR-NOT-GREATERP", "ACL2", "COMMON-LISP"),
("COND", "ACL2", "COMMON-LISP"),
("DEFINE-SYMBOL-MACRO", "ACL2", "COMMON-LISP"),
("CHAR-NOT-LESSP", "ACL2", "COMMON-LISP"),
("CONDITION", "ACL2", "COMMON-LISP"),
("DEFMACRO", "ACL2", "COMMON-LISP"),
("CHAR-UPCASE", "ACL2", "COMMON-LISP"),
("CONJUGATE", "ACL2", "COMMON-LISP"),
("DEFMETHOD", "ACL2", "COMMON-LISP"),
("CHAR/=", "ACL2", "COMMON-LISP"),
("CONS", "ACL2", "COMMON-LISP"),
("DEFPACKAGE", "ACL2", "COMMON-LISP"),
("CHAR<", "ACL2", "COMMON-LISP"),
("CONSP", "ACL2", "COMMON-LISP"),
("DEFPARAMETER", "ACL2", "COMMON-LISP"),
("CHAR<=", "ACL2", "COMMON-LISP"),
("CONSTANTLY", "ACL2", "COMMON-LISP"),
("DEFSETF", "ACL2", "COMMON-LISP"),
("CHAR=", "ACL2", "COMMON-LISP"),
("CONSTANTP", "ACL2", "COMMON-LISP"),
("DEFSTRUCT", "ACL2", "COMMON-LISP"),
("CHAR>", "ACL2", "COMMON-LISP"),
("CONTINUE", "ACL2", "COMMON-LISP"),
("DEFTYPE", "ACL2", "COMMON-LISP"),
("CHAR>=", "ACL2", "COMMON-LISP"),
("CONTROL-ERROR", "ACL2", "COMMON-LISP"),
("DEFUN", "ACL2", "COMMON-LISP"),
("CHARACTER", "ACL2", "COMMON-LISP"),
("COPY-ALIST", "ACL2", "COMMON-LISP"),
("DEFVAR", "ACL2", "COMMON-LISP"),
("CHARACTERP", "ACL2", "COMMON-LISP"),
("COPY-LIST", "ACL2", "COMMON-LISP"),
("DELETE", "ACL2", "COMMON-LISP"),
("CHECK-TYPE", "ACL2", "COMMON-LISP"),
("COPY-PPRINT-DISPATCH", "ACL2", "COMMON-LISP"),
("DELETE-DUPLICATES", "ACL2", "COMMON-LISP"),
("CIS", "ACL2", "COMMON-LISP"),
("COPY-READTABLE", "ACL2", "COMMON-LISP"),
("DELETE-FILE", "ACL2", "COMMON-LISP"),
("CLASS", "ACL2", "COMMON-LISP"),
("COPY-SEQ", "ACL2", "COMMON-LISP"),
("DELETE-IF", "ACL2", "COMMON-LISP"),
("CLASS-NAME", "ACL2", "COMMON-LISP"),
("COPY-STRUCTURE", "ACL2", "COMMON-LISP"),
("DELETE-IF-NOT", "ACL2", "COMMON-LISP"),
("CLASS-OF", "ACL2", "COMMON-LISP"),
("COPY-SYMBOL", "ACL2", "COMMON-LISP"),
("DELETE-PACKAGE", "ACL2", "COMMON-LISP"),
("DENOMINATOR", "ACL2", "COMMON-LISP"),
("EQ", "ACL2", "COMMON-LISP"),
("DEPOSIT-FIELD", "ACL2", "COMMON-LISP"),
("EQL", "ACL2", "COMMON-LISP"),
("DESCRIBE", "ACL2", "COMMON-LISP"),
("EQUAL", "ACL2", "COMMON-LISP"),
("DESCRIBE-OBJECT", "ACL2", "COMMON-LISP"),
("EQUALP", "ACL2", "COMMON-LISP"),
("DESTRUCTURING-BIND", "ACL2", "COMMON-LISP"),
("ERROR", "ACL2", "COMMON-LISP"),
("DIGIT-CHAR", "ACL2", "COMMON-LISP"),
("ETYPECASE", "ACL2", "COMMON-LISP"),
("DIGIT-CHAR-P", "ACL2", "COMMON-LISP"),
("EVAL", "ACL2", "COMMON-LISP"),
("DIRECTORY", "ACL2", "COMMON-LISP"),
("EVAL-WHEN", "ACL2", "COMMON-LISP"),
("DIRECTORY-NAMESTRING", "ACL2", "COMMON-LISP"),
("EVENP", "ACL2", "COMMON-LISP"),
("DISASSEMBLE", "ACL2", "COMMON-LISP"),
("EVERY", "ACL2", "COMMON-LISP"),
("DIVISION-BY-ZERO", "ACL2", "COMMON-LISP"),
("EXP", "ACL2", "COMMON-LISP"),
("DO", "ACL2", "COMMON-LISP"),
("EXPORT", "ACL2", "COMMON-LISP"),
("DO*", "ACL2", "COMMON-LISP"),
("EXPT", "ACL2", "COMMON-LISP"),
("DO-ALL-SYMBOLS", "ACL2", "COMMON-LISP"),
("EXTENDED-CHAR", "ACL2", "COMMON-LISP"),
("DO-EXTERNAL-SYMBOLS", "ACL2", "COMMON-LISP"),
("FBOUNDP", "ACL2", "COMMON-LISP"),
("DO-SYMBOLS", "ACL2", "COMMON-LISP"),
("FCEILING", "ACL2", "COMMON-LISP"),
("DOCUMENTATION", "ACL2", "COMMON-LISP"),
("FDEFINITION", "ACL2", "COMMON-LISP"),
("DOLIST", "ACL2", "COMMON-LISP"),
("FFLOOR", "ACL2", "COMMON-LISP"),
("DOTIMES", "ACL2", "COMMON-LISP"),
("FIFTH", "ACL2", "COMMON-LISP"),
("DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("FILE-AUTHOR", "ACL2", "COMMON-LISP"),
("DOUBLE-FLOAT-EPSILON", "ACL2", "COMMON-LISP"),
("FILE-ERROR", "ACL2", "COMMON-LISP"),
("DOUBLE-FLOAT-NEGATIVE-EPSILON", "ACL2", "COMMON-LISP"),
("FILE-ERROR-PATHNAME", "ACL2", "COMMON-LISP"),
("DPB", "ACL2", "COMMON-LISP"),
("FILE-LENGTH", "ACL2", "COMMON-LISP"),
("DRIBBLE", "ACL2", "COMMON-LISP"),
("FILE-NAMESTRING", "ACL2", "COMMON-LISP"),
("DYNAMIC-EXTENT", "ACL2", "COMMON-LISP"),
("FILE-POSITION", "ACL2", "COMMON-LISP"),
("ECASE", "ACL2", "COMMON-LISP"),
("FILE-STREAM", "ACL2", "COMMON-LISP"),
("ECHO-STREAM", "ACL2", "COMMON-LISP"),
("FILE-STRING-LENGTH", "ACL2", "COMMON-LISP"),
("ECHO-STREAM-INPUT-STREAM", "ACL2", "COMMON-LISP"),
("FILE-WRITE-DATE", "ACL2", "COMMON-LISP"),
("ECHO-STREAM-OUTPUT-STREAM", "ACL2", "COMMON-LISP"),
("FILL", "ACL2", "COMMON-LISP"),
("ED", "ACL2", "COMMON-LISP"),
("FILL-POINTER", "ACL2", "COMMON-LISP"),
("EIGHTH", "ACL2", "COMMON-LISP"),
("FIND", "ACL2", "COMMON-LISP"),
("ELT", "ACL2", "COMMON-LISP"),
("FIND-ALL-SYMBOLS", "ACL2", "COMMON-LISP"),
("ENCODE-UNIVERSAL-TIME", "ACL2", "COMMON-LISP"),
("FIND-CLASS", "ACL2", "COMMON-LISP"),
("END-OF-FILE", "ACL2", "COMMON-LISP"),
("FIND-IF", "ACL2", "COMMON-LISP"),
("ENDP", "ACL2", "COMMON-LISP"),
("FIND-IF-NOT", "ACL2", "COMMON-LISP"),
("ENOUGH-NAMESTRING", "ACL2", "COMMON-LISP"),
("FIND-METHOD", "ACL2", "COMMON-LISP"),
("ENSURE-DIRECTORIES-EXIST", "ACL2", "COMMON-LISP"),
("FIND-PACKAGE", "ACL2", "COMMON-LISP"),
("ENSURE-GENERIC-FUNCTION", "ACL2", "COMMON-LISP"),
("FIND-RESTART", "ACL2", "COMMON-LISP"),
("FIND-SYMBOL", "ACL2", "COMMON-LISP"),
("GET-INTERNAL-RUN-TIME", "ACL2", "COMMON-LISP"),
("FINISH-OUTPUT", "ACL2", "COMMON-LISP"),
("GET-MACRO-CHARACTER", "ACL2", "COMMON-LISP"),
("FIRST", "ACL2", "COMMON-LISP"),
("GET-OUTPUT-STREAM-STRING", "ACL2", "COMMON-LISP"),
("FIXNUM", "ACL2", "COMMON-LISP"),
("GET-PROPERTIES", "ACL2", "COMMON-LISP"),
("FLET", "ACL2", "COMMON-LISP"),
("GET-SETF-EXPANSION", "ACL2", "COMMON-LISP"),
("FLOAT", "ACL2", "COMMON-LISP"),
("GET-UNIVERSAL-TIME", "ACL2", "COMMON-LISP"),
("FLOAT-DIGITS", "ACL2", "COMMON-LISP"),
("GETF", "ACL2", "COMMON-LISP"),
("FLOAT-PRECISION", "ACL2", "COMMON-LISP"),
("GETHASH", "ACL2", "COMMON-LISP"),
("FLOAT-RADIX", "ACL2", "COMMON-LISP"),
("GO", "ACL2", "COMMON-LISP"),
("FLOAT-SIGN", "ACL2", "COMMON-LISP"),
("GRAPHIC-CHAR-P", "ACL2", "COMMON-LISP"),
("FLOATING-POINT-INEXACT", "ACL2", "COMMON-LISP"),
("HANDLER-BIND", "ACL2", "COMMON-LISP"),
("FLOATING-POINT-INVALID-OPERATION", "ACL2", "COMMON-LISP"),
("HANDLER-CASE", "ACL2", "COMMON-LISP"),
("FLOATING-POINT-OVERFLOW", "ACL2", "COMMON-LISP"),
("HASH-TABLE", "ACL2", "COMMON-LISP"),
("FLOATING-POINT-UNDERFLOW", "ACL2", "COMMON-LISP"),
("HASH-TABLE-COUNT", "ACL2", "COMMON-LISP"),
("FLOATP", "ACL2", "COMMON-LISP"),
("HASH-TABLE-P", "ACL2", "COMMON-LISP"),
("FLOOR", "ACL2", "COMMON-LISP"),
("HASH-TABLE-REHASH-SIZE", "ACL2", "COMMON-LISP"),
("FMAKUNBOUND", "ACL2", "COMMON-LISP"),
("HASH-TABLE-REHASH-THRESHOLD", "ACL2", "COMMON-LISP"),
("FORCE-OUTPUT", "ACL2", "COMMON-LISP"),
("HASH-TABLE-SIZE", "ACL2", "COMMON-LISP"),
("FORMAT", "ACL2", "COMMON-LISP"),
("HASH-TABLE-TEST", "ACL2", "COMMON-LISP"),
("FORMATTER", "ACL2", "COMMON-LISP"),
("HOST-NAMESTRING", "ACL2", "COMMON-LISP"),
("FOURTH", "ACL2", "COMMON-LISP"),
("IDENTITY", "ACL2", "COMMON-LISP"),
("FRESH-LINE", "ACL2", "COMMON-LISP"),
("IF", "ACL2", "COMMON-LISP"),
("FROUND", "ACL2", "COMMON-LISP"),
("IGNORABLE", "ACL2", "COMMON-LISP"),
("FTRUNCATE", "ACL2", "COMMON-LISP"),
("IGNORE", "ACL2", "COMMON-LISP"),
("FTYPE", "ACL2", "COMMON-LISP"),
("IGNORE-ERRORS", "ACL2", "COMMON-LISP"),
("FUNCALL", "ACL2", "COMMON-LISP"),
("IMAGPART", "ACL2", "COMMON-LISP"),
("FUNCTION", "ACL2", "COMMON-LISP"),
("IMPORT", "ACL2", "COMMON-LISP"),
("FUNCTION-KEYWORDS", "ACL2", "COMMON-LISP"),
("IN-PACKAGE", "ACL2", "COMMON-LISP"),
("FUNCTION-LAMBDA-EXPRESSION", "ACL2", "COMMON-LISP"),
("INCF", "ACL2", "COMMON-LISP"),
("FUNCTIONP", "ACL2", "COMMON-LISP"),
("INITIALIZE-INSTANCE", "ACL2", "COMMON-LISP"),
("GCD", "ACL2", "COMMON-LISP"),
("INLINE", "ACL2", "COMMON-LISP"),
("GENERIC-FUNCTION", "ACL2", "COMMON-LISP"),
("INPUT-STREAM-P", "ACL2", "COMMON-LISP"),
("GENSYM", "ACL2", "COMMON-LISP"),
("INSPECT", "ACL2", "COMMON-LISP"),
("GENTEMP", "ACL2", "COMMON-LISP"),
("INTEGER", "ACL2", "COMMON-LISP"),
("GET", "ACL2", "COMMON-LISP"),
("INTEGER-DECODE-FLOAT", "ACL2", "COMMON-LISP"),
("GET-DECODED-TIME", "ACL2", "COMMON-LISP"),
("INTEGER-LENGTH", "ACL2", "COMMON-LISP"),
("GET-DISPATCH-MACRO-CHARACTER", "ACL2", "COMMON-LISP"),
("INTEGERP", "ACL2", "COMMON-LISP"),
("GET-INTERNAL-REAL-TIME", "ACL2", "COMMON-LISP"),
("INTERACTIVE-STREAM-P", "ACL2", "COMMON-LISP"),
("INTERN", "ACL2", "COMMON-LISP"),
("LISP-IMPLEMENTATION-TYPE", "ACL2", "COMMON-LISP"),
("INTERNAL-TIME-UNITS-PER-SECOND", "ACL2", "COMMON-LISP"),
("LISP-IMPLEMENTATION-VERSION", "ACL2", "COMMON-LISP"),
("INTERSECTION", "ACL2", "COMMON-LISP"),
("LIST", "ACL2", "COMMON-LISP"),
("INVALID-METHOD-ERROR", "ACL2", "COMMON-LISP"),
("LIST*", "ACL2", "COMMON-LISP"),
("INVOKE-DEBUGGER", "ACL2", "COMMON-LISP"),
("LIST-ALL-PACKAGES", "ACL2", "COMMON-LISP"),
("INVOKE-RESTART", "ACL2", "COMMON-LISP"),
("LIST-LENGTH", "ACL2", "COMMON-LISP"),
("INVOKE-RESTART-INTERACTIVELY", "ACL2", "COMMON-LISP"),
("LISTEN", "ACL2", "COMMON-LISP"),
("ISQRT", "ACL2", "COMMON-LISP"),
("LISTP", "ACL2", "COMMON-LISP"),
("KEYWORD", "ACL2", "COMMON-LISP"),
("LOAD", "ACL2", "COMMON-LISP"),
("KEYWORDP", "ACL2", "COMMON-LISP"),
("LOAD-LOGICAL-PATHNAME-TRANSLATIONS", "ACL2", "COMMON-LISP"),
("LABELS", "ACL2", "COMMON-LISP"),
("LOAD-TIME-VALUE", "ACL2", "COMMON-LISP"),
("LAMBDA", "ACL2", "COMMON-LISP"),
("LOCALLY", "ACL2", "COMMON-LISP"),
("LAMBDA-LIST-KEYWORDS", "ACL2", "COMMON-LISP"),
("LOG", "ACL2", "COMMON-LISP"),
("LAMBDA-PARAMETERS-LIMIT", "ACL2", "COMMON-LISP"),
("LOGAND", "ACL2", "COMMON-LISP"),
("LAST", "ACL2", "COMMON-LISP"),
("LOGANDC1", "ACL2", "COMMON-LISP"),
("LCM", "ACL2", "COMMON-LISP"),
("LOGANDC2", "ACL2", "COMMON-LISP"),
("LDB", "ACL2", "COMMON-LISP"),
("LOGBITP", "ACL2", "COMMON-LISP"),
("LDB-TEST", "ACL2", "COMMON-LISP"),
("LOGCOUNT", "ACL2", "COMMON-LISP"),
("LDIFF", "ACL2", "COMMON-LISP"),
("LOGEQV", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("LOGICAL-PATHNAME", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-LONG-FLOAT", "ACL2", "COMMON-LISP"),
("LOGICAL-PATHNAME-TRANSLATIONS", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("LOGIOR", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT", "ACL2", "COMMON-LISP"),
("LOGNAND", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("LOGNOR", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("LOGNOT", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("LOGORC1", "ACL2", "COMMON-LISP"),
("LEAST-NEGATIVE-SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("LOGORC2", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("LOGTEST", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-LONG-FLOAT", "ACL2", "COMMON-LISP"),
("LOGXOR", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("LONG-FLOAT", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-LONG-FLOAT", "ACL2", "COMMON-LISP"),
("LONG-FLOAT-EPSILON", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("LONG-FLOAT-NEGATIVE-EPSILON", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("LONG-SITE-NAME", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("LOOP", "ACL2", "COMMON-LISP"),
("LEAST-POSITIVE-SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("LOOP-FINISH", "ACL2", "COMMON-LISP"),
("LENGTH", "ACL2", "COMMON-LISP"),
("LOWER-CASE-P", "ACL2", "COMMON-LISP"),
("LET", "ACL2", "COMMON-LISP"),
("MACHINE-INSTANCE", "ACL2", "COMMON-LISP"),
("LET*", "ACL2", "COMMON-LISP"),
("MACHINE-TYPE", "ACL2", "COMMON-LISP"),
("MACHINE-VERSION", "ACL2", "COMMON-LISP"),
("MASK-FIELD", "ACL2", "COMMON-LISP"),
("MACRO-FUNCTION", "ACL2", "COMMON-LISP"),
("MAX", "ACL2", "COMMON-LISP"),
("MACROEXPAND", "ACL2", "COMMON-LISP"),
("MEMBER", "ACL2", "COMMON-LISP"),
("MACROEXPAND-1", "ACL2", "COMMON-LISP"),
("MEMBER-IF", "ACL2", "COMMON-LISP"),
("MACROLET", "ACL2", "COMMON-LISP"),
("MEMBER-IF-NOT", "ACL2", "COMMON-LISP"),
("MAKE-ARRAY", "ACL2", "COMMON-LISP"),
("MERGE", "ACL2", "COMMON-LISP"),
("MAKE-BROADCAST-STREAM", "ACL2", "COMMON-LISP"),
("MERGE-PATHNAMES", "ACL2", "COMMON-LISP"),
("MAKE-CONCATENATED-STREAM", "ACL2", "COMMON-LISP"),
("METHOD", "ACL2", "COMMON-LISP"),
("MAKE-CONDITION", "ACL2", "COMMON-LISP"),
("METHOD-COMBINATION", "ACL2", "COMMON-LISP"),
("MAKE-DISPATCH-MACRO-CHARACTER", "ACL2", "COMMON-LISP"),
("METHOD-COMBINATION-ERROR", "ACL2", "COMMON-LISP"),
("MAKE-ECHO-STREAM", "ACL2", "COMMON-LISP"),
("METHOD-QUALIFIERS", "ACL2", "COMMON-LISP"),
("MAKE-HASH-TABLE", "ACL2", "COMMON-LISP"),
("MIN", "ACL2", "COMMON-LISP"),
("MAKE-INSTANCE", "ACL2", "COMMON-LISP"),
("MINUSP", "ACL2", "COMMON-LISP"),
("MAKE-INSTANCES-OBSOLETE", "ACL2", "COMMON-LISP"),
("MISMATCH", "ACL2", "COMMON-LISP"),
("MAKE-LIST", "ACL2", "COMMON-LISP"),
("MOD", "ACL2", "COMMON-LISP"),
("MAKE-LOAD-FORM", "ACL2", "COMMON-LISP"),
("MOST-NEGATIVE-DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-LOAD-FORM-SAVING-SLOTS", "ACL2", "COMMON-LISP"),
("MOST-NEGATIVE-FIXNUM", "ACL2", "COMMON-LISP"),
("MAKE-METHOD", "ACL2", "COMMON-LISP"),
("MOST-NEGATIVE-LONG-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-PACKAGE", "ACL2", "COMMON-LISP"),
("MOST-NEGATIVE-SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-PATHNAME", "ACL2", "COMMON-LISP"),
("MOST-NEGATIVE-SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-RANDOM-STATE", "ACL2", "COMMON-LISP"),
("MOST-POSITIVE-DOUBLE-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-SEQUENCE", "ACL2", "COMMON-LISP"),
("MOST-POSITIVE-FIXNUM", "ACL2", "COMMON-LISP"),
("MAKE-STRING", "ACL2", "COMMON-LISP"),
("MOST-POSITIVE-LONG-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-STRING-INPUT-STREAM", "ACL2", "COMMON-LISP"),
("MOST-POSITIVE-SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-STRING-OUTPUT-STREAM", "ACL2", "COMMON-LISP"),
("MOST-POSITIVE-SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("MAKE-SYMBOL", "ACL2", "COMMON-LISP"),
("MUFFLE-WARNING", "ACL2", "COMMON-LISP"),
("MAKE-SYNONYM-STREAM", "ACL2", "COMMON-LISP"),
("MULTIPLE-VALUE-BIND", "ACL2", "COMMON-LISP"),
("MAKE-TWO-WAY-STREAM", "ACL2", "COMMON-LISP"),
("MULTIPLE-VALUE-CALL", "ACL2", "COMMON-LISP"),
("MAKUNBOUND", "ACL2", "COMMON-LISP"),
("MULTIPLE-VALUE-LIST", "ACL2", "COMMON-LISP"),
("MAP", "ACL2", "COMMON-LISP"),
("MULTIPLE-VALUE-PROG1", "ACL2", "COMMON-LISP"),
("MAP-INTO", "ACL2", "COMMON-LISP"),
("MULTIPLE-VALUE-SETQ", "ACL2", "COMMON-LISP"),
("MAPC", "ACL2", "COMMON-LISP"),
("MULTIPLE-VALUES-LIMIT", "ACL2", "COMMON-LISP"),
("MAPCAN", "ACL2", "COMMON-LISP"),
("NAME-CHAR", "ACL2", "COMMON-LISP"),
("MAPCAR", "ACL2", "COMMON-LISP"),
("NAMESTRING", "ACL2", "COMMON-LISP"),
("MAPCON", "ACL2", "COMMON-LISP"),
("NBUTLAST", "ACL2", "COMMON-LISP"),
("MAPHASH", "ACL2", "COMMON-LISP"),
("NCONC", "ACL2", "COMMON-LISP"),
("MAPL", "ACL2", "COMMON-LISP"),
("NEXT-METHOD-P", "ACL2", "COMMON-LISP"),
("MAPLIST", "ACL2", "COMMON-LISP"),
("NIL", "ACL2", "COMMON-LISP"),
("NINTERSECTION", "ACL2", "COMMON-LISP"),
("PACKAGE-ERROR", "ACL2", "COMMON-LISP"),
("NINTH", "ACL2", "COMMON-LISP"),
("PACKAGE-ERROR-PACKAGE", "ACL2", "COMMON-LISP"),
("NO-APPLICABLE-METHOD", "ACL2", "COMMON-LISP"),
("PACKAGE-NAME", "ACL2", "COMMON-LISP"),
("NO-NEXT-METHOD", "ACL2", "COMMON-LISP"),
("PACKAGE-NICKNAMES", "ACL2", "COMMON-LISP"),
("NOT", "ACL2", "COMMON-LISP"),
("PACKAGE-SHADOWING-SYMBOLS", "ACL2", "COMMON-LISP"),
("NOTANY", "ACL2", "COMMON-LISP"),
("PACKAGE-USE-LIST", "ACL2", "COMMON-LISP"),
("NOTEVERY", "ACL2", "COMMON-LISP"),
("PACKAGE-USED-BY-LIST", "ACL2", "COMMON-LISP"),
("NOTINLINE", "ACL2", "COMMON-LISP"),
("PACKAGEP", "ACL2", "COMMON-LISP"),
("NRECONC", "ACL2", "COMMON-LISP"),
("PAIRLIS", "ACL2", "COMMON-LISP"),
("NREVERSE", "ACL2", "COMMON-LISP"),
("PARSE-ERROR", "ACL2", "COMMON-LISP"),
("NSET-DIFFERENCE", "ACL2", "COMMON-LISP"),
("PARSE-INTEGER", "ACL2", "COMMON-LISP"),
("NSET-EXCLUSIVE-OR", "ACL2", "COMMON-LISP"),
("PARSE-NAMESTRING", "ACL2", "COMMON-LISP"),
("NSTRING-CAPITALIZE", "ACL2", "COMMON-LISP"),
("PATHNAME", "ACL2", "COMMON-LISP"),
("NSTRING-DOWNCASE", "ACL2", "COMMON-LISP"),
("PATHNAME-DEVICE", "ACL2", "COMMON-LISP"),
("NSTRING-UPCASE", "ACL2", "COMMON-LISP"),
("PATHNAME-DIRECTORY", "ACL2", "COMMON-LISP"),
("NSUBLIS", "ACL2", "COMMON-LISP"),
("PATHNAME-HOST", "ACL2", "COMMON-LISP"),
("NSUBST", "ACL2", "COMMON-LISP"),
("PATHNAME-MATCH-P", "ACL2", "COMMON-LISP"),
("NSUBST-IF", "ACL2", "COMMON-LISP"),
("PATHNAME-NAME", "ACL2", "COMMON-LISP"),
("NSUBST-IF-NOT", "ACL2", "COMMON-LISP"),
("PATHNAME-TYPE", "ACL2", "COMMON-LISP"),
("NSUBSTITUTE", "ACL2", "COMMON-LISP"),
("PATHNAME-VERSION", "ACL2", "COMMON-LISP"),
("NSUBSTITUTE-IF", "ACL2", "COMMON-LISP"),
("PATHNAMEP", "ACL2", "COMMON-LISP"),
("NSUBSTITUTE-IF-NOT", "ACL2", "COMMON-LISP"),
("PEEK-CHAR", "ACL2", "COMMON-LISP"),
("NTH", "ACL2", "COMMON-LISP"),
("PHASE", "ACL2", "COMMON-LISP"),
("NTH-VALUE", "ACL2", "COMMON-LISP"),
("PI", "ACL2", "COMMON-LISP"),
("NTHCDR", "ACL2", "COMMON-LISP"),
("PLUSP", "ACL2", "COMMON-LISP"),
("NULL", "ACL2", "COMMON-LISP"),
("POP", "ACL2", "COMMON-LISP"),
("NUMBER", "ACL2", "COMMON-LISP"),
("POSITION", "ACL2", "COMMON-LISP"),
("NUMBERP", "ACL2", "COMMON-LISP"),
("POSITION-IF", "ACL2", "COMMON-LISP"),
("NUMERATOR", "ACL2", "COMMON-LISP"),
("POSITION-IF-NOT", "ACL2", "COMMON-LISP"),
("NUNION", "ACL2", "COMMON-LISP"),
("PPRINT", "ACL2", "COMMON-LISP"),
("ODDP", "ACL2", "COMMON-LISP"),
("PPRINT-DISPATCH", "ACL2", "COMMON-LISP"),
("OPEN", "ACL2", "COMMON-LISP"),
("PPRINT-EXIT-IF-LIST-EXHAUSTED", "ACL2", "COMMON-LISP"),
("OPEN-STREAM-P", "ACL2", "COMMON-LISP"),
("PPRINT-FILL", "ACL2", "COMMON-LISP"),
("OPTIMIZE", "ACL2", "COMMON-LISP"),
("PPRINT-INDENT", "ACL2", "COMMON-LISP"),
("OR", "ACL2", "COMMON-LISP"),
("PPRINT-LINEAR", "ACL2", "COMMON-LISP"),
("OTHERWISE", "ACL2", "COMMON-LISP"),
("PPRINT-LOGICAL-BLOCK", "ACL2", "COMMON-LISP"),
("OUTPUT-STREAM-P", "ACL2", "COMMON-LISP"),
("PPRINT-NEWLINE", "ACL2", "COMMON-LISP"),
("PACKAGE", "ACL2", "COMMON-LISP"),
("PPRINT-POP", "ACL2", "COMMON-LISP"),
("PPRINT-TAB", "ACL2", "COMMON-LISP"),
("READ-CHAR", "ACL2", "COMMON-LISP"),
("PPRINT-TABULAR", "ACL2", "COMMON-LISP"),
("READ-CHAR-NO-HANG", "ACL2", "COMMON-LISP"),
("PRIN1", "ACL2", "COMMON-LISP"),
("READ-DELIMITED-LIST", "ACL2", "COMMON-LISP"),
("PRIN1-TO-STRING", "ACL2", "COMMON-LISP"),
("READ-FROM-STRING", "ACL2", "COMMON-LISP"),
("PRINC", "ACL2", "COMMON-LISP"),
("READ-LINE", "ACL2", "COMMON-LISP"),
("PRINC-TO-STRING", "ACL2", "COMMON-LISP"),
("READ-PRESERVING-WHITESPACE", "ACL2", "COMMON-LISP"),
("PRINT", "ACL2", "COMMON-LISP"),
("READ-SEQUENCE", "ACL2", "COMMON-LISP"),
("PRINT-NOT-READABLE", "ACL2", "COMMON-LISP"),
("READER-ERROR", "ACL2", "COMMON-LISP"),
("PRINT-NOT-READABLE-OBJECT", "ACL2", "COMMON-LISP"),
("READTABLE", "ACL2", "COMMON-LISP"),
("PRINT-OBJECT", "ACL2", "COMMON-LISP"),
("READTABLE-CASE", "ACL2", "COMMON-LISP"),
("PRINT-UNREADABLE-OBJECT", "ACL2", "COMMON-LISP"),
("READTABLEP", "ACL2", "COMMON-LISP"),
("PROBE-FILE", "ACL2", "COMMON-LISP"),
("REAL", "ACL2", "COMMON-LISP"),
("PROCLAIM", "ACL2", "COMMON-LISP"),
("REALP", "ACL2", "COMMON-LISP"),
("PROG", "ACL2", "COMMON-LISP"),
("REALPART", "ACL2", "COMMON-LISP"),
("PROG*", "ACL2", "COMMON-LISP"),
("REDUCE", "ACL2", "COMMON-LISP"),
("PROG1", "ACL2", "COMMON-LISP"),
("REINITIALIZE-INSTANCE", "ACL2", "COMMON-LISP"),
("PROG2", "ACL2", "COMMON-LISP"),
("REM", "ACL2", "COMMON-LISP"),
("PROGN", "ACL2", "COMMON-LISP"),
("REMF", "ACL2", "COMMON-LISP"),
("PROGRAM-ERROR", "ACL2", "COMMON-LISP"),
("REMHASH", "ACL2", "COMMON-LISP"),
("PROGV", "ACL2", "COMMON-LISP"),
("REMOVE", "ACL2", "COMMON-LISP"),
("PROVIDE", "ACL2", "COMMON-LISP"),
("REMOVE-DUPLICATES", "ACL2", "COMMON-LISP"),
("PSETF", "ACL2", "COMMON-LISP"),
("REMOVE-IF", "ACL2", "COMMON-LISP"),
("PSETQ", "ACL2", "COMMON-LISP"),
("REMOVE-IF-NOT", "ACL2", "COMMON-LISP"),
("PUSH", "ACL2", "COMMON-LISP"),
("REMOVE-METHOD", "ACL2", "COMMON-LISP"),
("PUSHNEW", "ACL2", "COMMON-LISP"),
("REMPROP", "ACL2", "COMMON-LISP"),
("QUOTE", "ACL2", "COMMON-LISP"),
("RENAME-FILE", "ACL2", "COMMON-LISP"),
("RANDOM", "ACL2", "COMMON-LISP"),
("RENAME-PACKAGE", "ACL2", "COMMON-LISP"),
("RANDOM-STATE", "ACL2", "COMMON-LISP"),
("REPLACE", "ACL2", "COMMON-LISP"),
("RANDOM-STATE-P", "ACL2", "COMMON-LISP"),
("REQUIRE", "ACL2", "COMMON-LISP"),
("RASSOC", "ACL2", "COMMON-LISP"),
("REST", "ACL2", "COMMON-LISP"),
("RASSOC-IF", "ACL2", "COMMON-LISP"),
("RESTART", "ACL2", "COMMON-LISP"),
("RASSOC-IF-NOT", "ACL2", "COMMON-LISP"),
("RESTART-BIND", "ACL2", "COMMON-LISP"),
("RATIO", "ACL2", "COMMON-LISP"),
("RESTART-CASE", "ACL2", "COMMON-LISP"),
("RATIONAL", "ACL2", "COMMON-LISP"),
("RESTART-NAME", "ACL2", "COMMON-LISP"),
("RATIONALIZE", "ACL2", "COMMON-LISP"),
("RETURN", "ACL2", "COMMON-LISP"),
("RATIONALP", "ACL2", "COMMON-LISP"),
("RETURN-FROM", "ACL2", "COMMON-LISP"),
("READ", "ACL2", "COMMON-LISP"),
("REVAPPEND", "ACL2", "COMMON-LISP"),
("READ-BYTE", "ACL2", "COMMON-LISP"),
("REVERSE", "ACL2", "COMMON-LISP"),
("ROOM", "ACL2", "COMMON-LISP"),
("SIMPLE-BIT-VECTOR", "ACL2", "COMMON-LISP"),
("ROTATEF", "ACL2", "COMMON-LISP"),
("SIMPLE-BIT-VECTOR-P", "ACL2", "COMMON-LISP"),
("ROUND", "ACL2", "COMMON-LISP"),
("SIMPLE-CONDITION", "ACL2", "COMMON-LISP"),
("ROW-MAJOR-AREF", "ACL2", "COMMON-LISP"),
("SIMPLE-CONDITION-FORMAT-ARGUMENTS", "ACL2", "COMMON-LISP"),
("RPLACA", "ACL2", "COMMON-LISP"),
("SIMPLE-CONDITION-FORMAT-CONTROL", "ACL2", "COMMON-LISP"),
("RPLACD", "ACL2", "COMMON-LISP"),
("SIMPLE-ERROR", "ACL2", "COMMON-LISP"),
("SAFETY", "ACL2", "COMMON-LISP"),
("SIMPLE-STRING", "ACL2", "COMMON-LISP"),
("SATISFIES", "ACL2", "COMMON-LISP"),
("SIMPLE-STRING-P", "ACL2", "COMMON-LISP"),
("SBIT", "ACL2", "COMMON-LISP"),
("SIMPLE-TYPE-ERROR", "ACL2", "COMMON-LISP"),
("SCALE-FLOAT", "ACL2", "COMMON-LISP"),
("SIMPLE-VECTOR", "ACL2", "COMMON-LISP"),
("SCHAR", "ACL2", "COMMON-LISP"),
("SIMPLE-VECTOR-P", "ACL2", "COMMON-LISP"),
("SEARCH", "ACL2", "COMMON-LISP"),
("SIMPLE-WARNING", "ACL2", "COMMON-LISP"),
("SECOND", "ACL2", "COMMON-LISP"),
("SIN", "ACL2", "COMMON-LISP"),
("SEQUENCE", "ACL2", "COMMON-LISP"),
("SINGLE-FLOAT", "ACL2", "COMMON-LISP"),
("SERIOUS-CONDITION", "ACL2", "COMMON-LISP"),
("SINGLE-FLOAT-EPSILON", "ACL2", "COMMON-LISP"),
("SET", "ACL2", "COMMON-LISP"),
("SINGLE-FLOAT-NEGATIVE-EPSILON", "ACL2", "COMMON-LISP"),
("SET-DIFFERENCE", "ACL2", "COMMON-LISP"),
("SINH", "ACL2", "COMMON-LISP"),
("SET-DISPATCH-MACRO-CHARACTER", "ACL2", "COMMON-LISP"),
("SIXTH", "ACL2", "COMMON-LISP"),
("SET-EXCLUSIVE-OR", "ACL2", "COMMON-LISP"),
("SLEEP", "ACL2", "COMMON-LISP"),
("SET-MACRO-CHARACTER", "ACL2", "COMMON-LISP"),
("SLOT-BOUNDP", "ACL2", "COMMON-LISP"),
("SET-PPRINT-DISPATCH", "ACL2", "COMMON-LISP"),
("SLOT-EXISTS-P", "ACL2", "COMMON-LISP"),
("SET-SYNTAX-FROM-CHAR", "ACL2", "COMMON-LISP"),
("SLOT-MAKUNBOUND", "ACL2", "COMMON-LISP"),
("SETF", "ACL2", "COMMON-LISP"),
("SLOT-MISSING", "ACL2", "COMMON-LISP"),
("SETQ", "ACL2", "COMMON-LISP"),
("SLOT-UNBOUND", "ACL2", "COMMON-LISP"),
("SEVENTH", "ACL2", "COMMON-LISP"),
("SLOT-VALUE", "ACL2", "COMMON-LISP"),
("SHADOW", "ACL2", "COMMON-LISP"),
("SOFTWARE-TYPE", "ACL2", "COMMON-LISP"),
("SHADOWING-IMPORT", "ACL2", "COMMON-LISP"),
("SOFTWARE-VERSION", "ACL2", "COMMON-LISP"),
("SHARED-INITIALIZE", "ACL2", "COMMON-LISP"),
("SOME", "ACL2", "COMMON-LISP"),
("SHIFTF", "ACL2", "COMMON-LISP"),
("SORT", "ACL2", "COMMON-LISP"),
("SHORT-FLOAT", "ACL2", "COMMON-LISP"),
("SPACE", "ACL2", "COMMON-LISP"),
("SHORT-FLOAT-EPSILON", "ACL2", "COMMON-LISP"),
("SPECIAL", "ACL2", "COMMON-LISP"),
("SHORT-FLOAT-NEGATIVE-EPSILON", "ACL2", "COMMON-LISP"),
("SPECIAL-OPERATOR-P", "ACL2", "COMMON-LISP"),
("SHORT-SITE-NAME", "ACL2", "COMMON-LISP"),
("SPEED", "ACL2", "COMMON-LISP"),
("SIGNAL", "ACL2", "COMMON-LISP"),
("SQRT", "ACL2", "COMMON-LISP"),
("SIGNED-BYTE", "ACL2", "COMMON-LISP"),
("STABLE-SORT", "ACL2", "COMMON-LISP"),
("SIGNUM", "ACL2", "COMMON-LISP"),
("STANDARD", "ACL2", "COMMON-LISP"),
("SIMPLE-ARRAY", "ACL2", "COMMON-LISP"),
("STANDARD-CHAR", "ACL2", "COMMON-LISP"),
("SIMPLE-BASE-STRING", "ACL2", "COMMON-LISP"),
("STANDARD-CHAR-P", "ACL2", "COMMON-LISP"),
("STANDARD-CLASS", "ACL2", "COMMON-LISP"),
("SUBLIS", "ACL2", "COMMON-LISP"),
("STANDARD-GENERIC-FUNCTION", "ACL2", "COMMON-LISP"),
("SUBSEQ", "ACL2", "COMMON-LISP"),
("STANDARD-METHOD", "ACL2", "COMMON-LISP"),
("SUBSETP", "ACL2", "COMMON-LISP"),
("STANDARD-OBJECT", "ACL2", "COMMON-LISP"),
("SUBST", "ACL2", "COMMON-LISP"),
("STEP", "ACL2", "COMMON-LISP"),
("SUBST-IF", "ACL2", "COMMON-LISP"),
("STORAGE-CONDITION", "ACL2", "COMMON-LISP"),
("SUBST-IF-NOT", "ACL2", "COMMON-LISP"),
("STORE-VALUE", "ACL2", "COMMON-LISP"),
("SUBSTITUTE", "ACL2", "COMMON-LISP"),
("STREAM", "ACL2", "COMMON-LISP"),
("SUBSTITUTE-IF", "ACL2", "COMMON-LISP"),
("STREAM-ELEMENT-TYPE", "ACL2", "COMMON-LISP"),
("SUBSTITUTE-IF-NOT", "ACL2", "COMMON-LISP"),
("STREAM-ERROR", "ACL2", "COMMON-LISP"),
("SUBTYPEP", "ACL2", "COMMON-LISP"),
("STREAM-ERROR-STREAM", "ACL2", "COMMON-LISP"),
("SVREF", "ACL2", "COMMON-LISP"),
("STREAM-EXTERNAL-FORMAT", "ACL2", "COMMON-LISP"),
("SXHASH", "ACL2", "COMMON-LISP"),
("STREAMP", "ACL2", "COMMON-LISP"),
("SYMBOL", "ACL2", "COMMON-LISP"),
("STRING", "ACL2", "COMMON-LISP"),
("SYMBOL-FUNCTION", "ACL2", "COMMON-LISP"),
("STRING-CAPITALIZE", "ACL2", "COMMON-LISP"),
("SYMBOL-MACROLET", "ACL2", "COMMON-LISP"),
("STRING-DOWNCASE", "ACL2", "COMMON-LISP"),
("SYMBOL-NAME", "ACL2", "COMMON-LISP"),
("STRING-EQUAL", "ACL2", "COMMON-LISP"),
("SYMBOL-PACKAGE", "ACL2", "COMMON-LISP"),
("STRING-GREATERP", "ACL2", "COMMON-LISP"),
("SYMBOL-PLIST", "ACL2", "COMMON-LISP"),
("STRING-LEFT-TRIM", "ACL2", "COMMON-LISP"),
("SYMBOL-VALUE", "ACL2", "COMMON-LISP"),
("STRING-LESSP", "ACL2", "COMMON-LISP"),
("SYMBOLP", "ACL2", "COMMON-LISP"),
("STRING-NOT-EQUAL", "ACL2", "COMMON-LISP"),
("SYNONYM-STREAM", "ACL2", "COMMON-LISP"),
("STRING-NOT-GREATERP", "ACL2", "COMMON-LISP"),
("SYNONYM-STREAM-SYMBOL", "ACL2", "COMMON-LISP"),
("STRING-NOT-LESSP", "ACL2", "COMMON-LISP"),
("T", "ACL2", "COMMON-LISP"),
("STRING-RIGHT-TRIM", "ACL2", "COMMON-LISP"),
("TAGBODY", "ACL2", "COMMON-LISP"),
("STRING-STREAM", "ACL2", "COMMON-LISP"),
("TAILP", "ACL2", "COMMON-LISP"),
("STRING-TRIM", "ACL2", "COMMON-LISP"),
("TAN", "ACL2", "COMMON-LISP"),
("STRING-UPCASE", "ACL2", "COMMON-LISP"),
("TANH", "ACL2", "COMMON-LISP"),
("STRING/=", "ACL2", "COMMON-LISP"),
("TENTH", "ACL2", "COMMON-LISP"),
("STRING<", "ACL2", "COMMON-LISP"),
("TERPRI", "ACL2", "COMMON-LISP"),
("STRING<=", "ACL2", "COMMON-LISP"),
("THE", "ACL2", "COMMON-LISP"),
("STRING=", "ACL2", "COMMON-LISP"),
("THIRD", "ACL2", "COMMON-LISP"),
("STRING>", "ACL2", "COMMON-LISP"),
("THROW", "ACL2", "COMMON-LISP"),
("STRING>=", "ACL2", "COMMON-LISP"),
("TIME", "ACL2", "COMMON-LISP"),
("STRINGP", "ACL2", "COMMON-LISP"),
("TRACE", "ACL2", "COMMON-LISP"),
("STRUCTURE", "ACL2", "COMMON-LISP"),
("TRANSLATE-LOGICAL-PATHNAME", "ACL2", "COMMON-LISP"),
("STRUCTURE-CLASS", "ACL2", "COMMON-LISP"),
("TRANSLATE-PATHNAME", "ACL2", "COMMON-LISP"),
("STRUCTURE-OBJECT", "ACL2", "COMMON-LISP"),
("TREE-EQUAL", "ACL2", "COMMON-LISP"),
("STYLE-WARNING", "ACL2", "COMMON-LISP"),
("TRUENAME", "ACL2", "COMMON-LISP"),
("TRUNCATE", "ACL2", "COMMON-LISP"),
("VALUES-LIST", "ACL2", "COMMON-LISP"),
("TWO-WAY-STREAM", "ACL2", "COMMON-LISP"),
("VARIABLE", "ACL2", "COMMON-LISP"),
("TWO-WAY-STREAM-INPUT-STREAM", "ACL2", "COMMON-LISP"),
("VECTOR", "ACL2", "COMMON-LISP"),
("TWO-WAY-STREAM-OUTPUT-STREAM", "ACL2", "COMMON-LISP"),
("VECTOR-POP", "ACL2", "COMMON-LISP"),
("TYPE", "ACL2", "COMMON-LISP"),
("VECTOR-PUSH", "ACL2", "COMMON-LISP"),
("TYPE-ERROR", "ACL2", "COMMON-LISP"),
("VECTOR-PUSH-EXTEND", "ACL2", "COMMON-LISP"),
("TYPE-ERROR-DATUM", "ACL2", "COMMON-LISP"),
("VECTORP", "ACL2", "COMMON-LISP"),
("TYPE-ERROR-EXPECTED-TYPE", "ACL2", "COMMON-LISP"),
("WARN", "ACL2", "COMMON-LISP"),
("TYPE-OF", "ACL2", "COMMON-LISP"),
("WARNING", "ACL2", "COMMON-LISP"),
("TYPECASE", "ACL2", "COMMON-LISP"),
("WHEN", "ACL2", "COMMON-LISP"),
("TYPEP", "ACL2", "COMMON-LISP"),
("WILD-PATHNAME-P", "ACL2", "COMMON-LISP"),
("UNBOUND-SLOT", "ACL2", "COMMON-LISP"),
("WITH-ACCESSORS", "ACL2", "COMMON-LISP"),
("UNBOUND-SLOT-INSTANCE", "ACL2", "COMMON-LISP"),
("WITH-COMPILATION-UNIT", "ACL2", "COMMON-LISP"),
("UNBOUND-VARIABLE", "ACL2", "COMMON-LISP"),
("WITH-CONDITION-RESTARTS", "ACL2", "COMMON-LISP"),
("UNDEFINED-FUNCTION", "ACL2", "COMMON-LISP"),
("WITH-HASH-TABLE-ITERATOR", "ACL2", "COMMON-LISP"),
("UNEXPORT", "ACL2", "COMMON-LISP"),
("WITH-INPUT-FROM-STRING", "ACL2", "COMMON-LISP"),
("UNINTERN", "ACL2", "COMMON-LISP"),
("WITH-OPEN-FILE", "ACL2", "COMMON-LISP"),
("UNION", "ACL2", "COMMON-LISP"),
("WITH-OPEN-STREAM", "ACL2", "COMMON-LISP"),
("UNLESS", "ACL2", "COMMON-LISP"),
("WITH-OUTPUT-TO-STRING", "ACL2", "COMMON-LISP"),
("UNREAD-CHAR", "ACL2", "COMMON-LISP"),
("WITH-PACKAGE-ITERATOR", "ACL2", "COMMON-LISP"),
("UNSIGNED-BYTE", "ACL2", "COMMON-LISP"),
("WITH-SIMPLE-RESTART", "ACL2", "COMMON-LISP"),
("UNTRACE", "ACL2", "COMMON-LISP"),
("WITH-SLOTS", "ACL2", "COMMON-LISP"),
("UNUSE-PACKAGE", "ACL2", "COMMON-LISP"),
("WITH-STANDARD-IO-SYNTAX", "ACL2", "COMMON-LISP"),
("UNWIND-PROTECT", "ACL2", "COMMON-LISP"),
("WRITE", "ACL2", "COMMON-LISP"),
("UPDATE-INSTANCE-FOR-DIFFERENT-CLASS", "ACL2", "COMMON-LISP"),
("WRITE-BYTE", "ACL2", "COMMON-LISP"),
("UPDATE-INSTANCE-FOR-REDEFINED-CLASS", "ACL2", "COMMON-LISP"),
("WRITE-CHAR", "ACL2", "COMMON-LISP"),
("UPGRADED-ARRAY-ELEMENT-TYPE", "ACL2", "COMMON-LISP"),
("WRITE-LINE", "ACL2", "COMMON-LISP"),
("UPGRADED-COMPLEX-PART-TYPE", "ACL2", "COMMON-LISP"),
("WRITE-SEQUENCE", "ACL2", "COMMON-LISP"),
("UPPER-CASE-P", "ACL2", "COMMON-LISP"),
("WRITE-STRING", "ACL2", "COMMON-LISP"),
("USE-PACKAGE", "ACL2", "COMMON-LISP"),
("WRITE-TO-STRING", "ACL2", "COMMON-LISP"),
("USE-VALUE", "ACL2", "COMMON-LISP"),
("Y-OR-N-P", "ACL2", "COMMON-LISP"),
("USER-HOMEDIR-PATHNAME", "ACL2", "COMMON-LISP"),
("YES-OR-NO-P", "ACL2", "COMMON-LISP"),
("VALUES", "ACL2", "COMMON-LISP"),
("ZEROP", "ACL2", "COMMON-LISP")
]
)`;


(*****************************************************************************)
(*     - LOOKUP y [(x1,y1,z1);...;(xn,yn,zn)] x  =  zi if x=xi and y=yi      *)
(*                                                     (scan from left)      *)
(*     - LOOKUP y [(x1,y1,z1);...;(xn,yn,zn)] x  =  y  if (x=/=xi or y=/=yi) *)
(*                                                     for any i             *)
(*****************************************************************************)
val LOOKUP_def =
 Define
  `(LOOKUP y [] _ = y) 
   /\
   (LOOKUP y ((x1,y1,z1)::a) x = 
     if (x=x1) /\ (y=y1) then z1 else LOOKUP y a x)`;

val BASIC_INTERN_def =
 Define
  `BASIC_INTERN sym_name pkg_name =
    sym (LOOKUP pkg_name ACL2_PACKAGE_ALIST sym_name) sym_name`;

(*****************************************************************************)
(* symbolp                                                                   *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* symbolp (x)                                                    *)
(*   (symbolp x))                                                            *)
(*****************************************************************************)
val symbolp_def =
 acl2Define "COMMON-LISP::SYMBOLP"
  `(symbolp (sym p n) = 
     if (BASIC_INTERN n p = sym p n) /\ ~(p = "") then t else nil)
   /\
   (symbolp _ = nil)`;

(*****************************************************************************)
(* bad-atom<=                                                                *)
(*                                                                           *)
(* ; For us, bad atoms are objects that look like symbols but whose          *)
(* ; combination of package name and symbol name are impossible for the      *)
(* ; given package system.                                                   *)
(*                                                                           *)
(* ; *1* definition (not helpful):                                           *)
(* (defun-*1* bad-atom<= (x y)                                               *)
(*   (cond ((and (bad-atom x) (bad-atom y))                                  *)
(*                                                                           *)
(* ; The following should never happen.                                      *)
(*                                                                           *)
(*          (error "We have called (the executable counterpart of)           *)
(*                  bad-atom<= on ~ ~s and ~s, but bad-atom<=                *)
(*                  has no Common Lisp definition."                          *)
(*                 x y))                                                     *)
(*         (t (gv bad-atom<= (x y) nil))))                                   *)
(*****************************************************************************)

(*****************************************************************************)
(* Pick a well-founded relation on s-expressions                             *)
(*****************************************************************************)
val SEXP_WF_LESS_def =
 Define `SEXP_WF_LESS = @R:sexp->sexp->bool. WF R`;

(*****************************************************************************)
(* ACL2_BAD_ATOM_LESS x y iff x is less then y in the well-founded relation  *)
(*****************************************************************************)
val bad_atom_less_equal_def =
 acl2Define "ACL2::BAD-ATOM<="
  `bad_atom_less_equal x y = if SEXP_WF_LESS x y then t else nil`;

(*****************************************************************************)
(* symbol-name                                                               *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* symbol-name (x)                                                *)
(*   (if (symbolp x)                                                         *)
(*       (symbol-name x)                                                     *)
(*     (gv symbol-name (x) "")))                                             *)
(*****************************************************************************)
val symbol_name_def =
 acl2Define "COMMON-LISP::SYMBOL-NAME"
  `(symbol_name (sym p n) = ite (symbolp (sym p n)) (str n) (str ""))
   /\
   (symbol_name _ = (str ""))`;

(*****************************************************************************)
(* symbol-package-name                                                       *)
(*                                                                           *)
(* ; *1* definition:                                                         *)
(* (defun-*1* symbol-package-name (x)                                        *)
(*   (if (symbolp x)                                                         *)
(*       (symbol-package-name x)                                             *)
(*     (gv symbol-package-name (x) "")))                                     *)
(*****************************************************************************)
val symbol_package_name_def =
 acl2Define "ACL2::SYMBOL-PACKAGE-NAME"
  `(symbol_package_name (sym p n) =
     ite (symbolp (sym p n)) (str p) (str ""))
   /\
   (symbol_package_name _ = (str ""))`;

(*****************************************************************************)
(* pkg-witness                                                               *)
(*                                                                           *)
(* ; *1* definition (not very helpful):                                      *)
(* (defun-*1* pkg-witness (pkg)                                              *)
(*   (if (stringp pkg)                                                       *)
(*       (if (find-non-hidden-package-entry                                  *)
(*            pkg (known-package-alist *the-live-state* ))                   *)
(*           (intern *pkg-witness-name* pkg)                                 *)
(*         (throw-raw-ev-fncall (list 'pkg-witness-er pkg)))                 *)
(*     (gv pkg-witness (pkg) nil)))                                          *)
(*                                                                           *)
(* ; Here, we treat the ACL2 constant *pkg-witness-name* as its value,       *)
(* ; the string "PKG-WITNESS" -- in fact, ACL2 treates constants             *)
(* ; (defconst events) much as it treats macros, in the sense that they      *)
(* ; are eliminated when passing to internal terms.                          *)
(*                                                                           *)
(* ; Note that ACL2 refuses to parse (pkg-witness pkg) unless pkg is an      *)
(* ; explicit string naming a package already known to ACL2.                 *)
(*****************************************************************************)
val pkg_witness_def =
 acl2Define "ACL2::PKG-WITNESS"
  `pkg_witness (str x) =
    let s = BASIC_INTERN "PKG-WITNESS" x in ite (symbolp s) s nil`;

(*****************************************************************************)
(* intern-in-package-of-symbol                                               *)
(*                                                                           *)
(* ; *1* definition::                                                        *)
(* (defun-*1* intern-in-package-of-symbol (x y)                              *)
(*   (if (and (stringp x)                                                    *)
(*            (symbolp y))                                                   *)
(*       (intern x (symbol-package y))                                       *)
(*     (gv intern (x y) nil)))                                               *)
(*                                                                           *)
(* ; Hand-optimized ACL2:                                                    *)
(* (defun-*1* intern-in-package-of-symbol (x y)                              *)
(*   (if (and (stringp x)                                                    *)
(*            (symbolp y))                                                   *)
(*       (intern x (symbol-package y))                                       *)
(*     nil))                                                                 *)
(*****************************************************************************)
val intern_in_package_of_symbol_def =
 acl2Define "ACL2::INTERN-IN-PACKAGE-OF-SYMBOL"
  `(intern_in_package_of_symbol (str x) (sym p n) =
     ite (symbolp (sym p n)) (BASIC_INTERN x p) nil)
   /\
   (intern_in_package_of_symbol _ _ = nil)`;

(*****************************************************************************)
(* Auxiliary definitions.                                                    *)
(*****************************************************************************)

(*****************************************************************************)
(* |= t, where t:sexp, means t is a theorem of ACL2                          *)
(*****************************************************************************)
val _ = set_fixity "|=" (TruePrefix 11);        (* Give "|=" weak precedence *)

val ACL2_TRUE_def =
 xDefine "ACL2_TRUE"
  `(|= p) = (ite (equal p nil) nil t = t)`;

val caar_def =
 Define
  `caar x = car(car x)`;

val cadr_def =
 Define
  `cadr x = car(cdr x)`;

val cdar_def =
 Define
  `cdar x = cdr(car x)`;

val cddr_def =
 Define
  `cddr x = cdr(cdr x)`;

val caaar_def =
 Define
  `caaar x = car(car(car x))`;

val cdaar_def =
 Define
  `cdaar x = cdr(car(car x))`;

val cadar_def =
 Define
  `cadar x = car(cdr(car x))`;

val cddar_def =
 Define
  `cddar x = cdr(cdr(car x))`;

val caadr_def =
 Define
  `caadr x = car(car(cdr x))`;

val cdadr_def =
 Define
  `cdadr x = cdr(car(cdr x))`;

val caddr_def =
 Define
  `caddr x = car(cdr(cdr x))`;

val cdddr_def =
 Define
  `cdddr x = cdr(cdr(cdr x))`;

val caaaar_def =
 Define
  `caaaar x = car(car(car(car x)))`;

val cadaar_def =
 Define
  `cadaar x = car(cdr(car(car x)))`;

val caadar_def =
 Define
  `caadar x = car(car(cdr(car x)))`;

val caddar_def =
 Define
  `caddar x = car(cdr(cdr(car x)))`;

val caaadr_def =
 Define
  `caaadr x = car(car(car(cdr x)))`;

val cadadr_def =
 Define
  `cadadr x = car(cdr(car(cdr x)))`;

val caaddr_def =
 Define
  `caaddr x = car(car(cdr(cdr x)))`;

val cadddr_def =
 Define
  `cadddr x = car(cdr(cdr(cdr x)))`;

val cdaaar_def =
 Define
  `cdaaar x = cdr(car(car(car x)))`;

val cddaar_def =
 Define
  `cddaar x = cdr(cdr(car(car x)))`;

val cdadar_def =
 Define
  `cdadar x = cdr(car(cdr(car x)))`;

val cdddar_def =
 Define
  `cdddar x = cdr(cdr(cdr(car x)))`;

val cdaadr_def =
 Define
  `cdaadr x = cdr(car(car(cdr x)))`;

val cddadr_def =
 Define
  `cddadr x = cdr(cdr(car(cdr x)))`;

val cdaddr_def =
 Define
  `cdaddr x = cdr(car(cdr(cdr x)))`;

val cddddr_def =
 Define
  `cddddr x = cdr(cdr(cdr(cdr x)))`;

val List_def =
 Define
  `(List[s] = cons s nil)
    /\
   (List(s::sl) = cons s (List sl))`;

val andl_def =
 Define
  `(andl[] = t)
   /\
   (andl[s] = s)
   /\
   (andl(x::y::l) = ite x (andl(y::l)) nil)`;

val andl_fold =
 store_thm
  ("andl_fold",
   ``(ite x y nil = andl[x;y]) /\ (andl[x; andl(y::l)] = andl(x::y::l))``,
   RW_TAC std_ss [andl_def,ite_def,List_def]);

val andl_append =
 store_thm
  ("andl_append",
   ``!l1 l2. andl(andl l1 :: l2) = andl(l1 ++ l2)``,
   Induct
    THEN RW_TAC list_ss [andl_def,ite_def,List_def]
    THENL
     [Cases_on `l2`
       THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``],
      Cases_on `h=nil`
       THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``]
       THENL
        [Cases_on `l1` THEN Cases_on `l2`
          THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``],
         Cases_on `l1`
          THEN RW_TAC list_ss [andl_def,ite_def,List_def,EVAL ``t=nil``]]]);

val andl_fold =
 store_thm
  ("andl_fold",
   ``(ite x y nil = andl[x;y])
     /\ 
     (andl[x; andl(y::l)] = andl(x::(y::l)))
     /\ 
     (andl(andl(x::y::l1)::l2) = andl(x::y::(l1++l2)))``,
   RW_TAC std_ss [andl_def,ite_def,List_def]
    THENL
     [Cases_on `l2`
       THEN RW_TAC std_ss [andl_def,ite_def,List_def],
      RW_TAC list_ss [andl_append]]);

val itel_def =
 Define
  `(itel [] val'               = val')
   /\
   (itel ((test,val)::sl) val' = ite test val (itel sl val'))`;

val itel_fold =
 store_thm
  ("itel_fold",
   ``(ite x y z = itel [(x,y)] z)
     /\
     (itel [p] (itel pl v) = itel (p::pl) v)``,
   Cases_on `p`
    THEN RW_TAC std_ss [itel_def,ite_def]);

val itel_append =
 store_thm
  ("itel_append",
   ``itel l1 (itel l2 v) = itel (l1 ++ l2) v``,
   Induct_on `l1`
    THEN RW_TAC list_ss [itel_def,ite_def]
    THEN Cases_on `h`
    THEN Cases_on `q=nil`
    THEN RW_TAC list_ss [itel_def,ite_def,List_def,EVAL ``t=nil``]);

val _ = export_acl2_theory();

