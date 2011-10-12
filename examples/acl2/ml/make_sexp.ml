(*****************************************************************************)
(* This file defines a type of s-expressions and various constants and       *)
(* functions on this type (t, nil, car, cdr, cons etc).                      *)
(*                                                                           *)
(* See Holmakefile for how this file is used                                 *)
(*                                                                           *)
(* One goal is to construct a model of ACL2 by proving the axioms in         *)
(* axioms.lisp.                                                              *)
(*                                                                           *)
(* File originally written by Mike Gordon and Matt Kaufmann;                 *)
(* now maintained by Mike Gordon.                                            *)
(*                                                                           *)
(*****************************************************************************)


(******************************************************************************
* Load theories
******************************************************************************)
quietdec := true;
map 
 load  
 ["complex_rationalTheory", "sexp"];
open complex_rationalTheory sexp;
Globals.checking_const_names := false;
quietdec := false;

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

val ACL2_PACKAGE_STRUCTURE = ref([] : (string * string * string)list);

use (Globals.HOLDIR ^ "/examples/acl2/ml/kpa-v2-9-3.ml");

val ACL2_PACKAGE_ALIST =
 time
  Define
  `ACL2_PACKAGE_ALIST =
    ^(make_package_structure_term (!ACL2_PACKAGE_STRUCTURE))`;

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
val _ = set_fixity "|=" (Prefix 11);        (* Give "|=" weak precedence *)

val ACL2_TRUE_def =
 xDefine "ACL2_TRUE"
  `(|= p) = (ite (equal p nil) nil t = t)`;

val _ = export_acl2_theory();

compile_theory();
