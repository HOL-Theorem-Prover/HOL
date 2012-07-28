(*---------------------------------------------------------------------------
            Tests of type specifications in HOL-Omega
                        Peter Vincent Homeier
                           April 16, 2011
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------

   This file contains exmples inspired by Tom Melham's 1993 paper,
   "The HOL Logic Extended with Quantification over Type Variables,"
   Formal Methods in System Design, vol. 3, Nos. 1-2 (August 1993), pp 7-24.

   In this paper, Melham describes the desire to add a definitional mechanism
   for type specification to the existing HOL facilities for constant definition,
   constant specification, and type definition.  He exhibits the issues using
   a definition of a abstract data type of non-empty bit-vectors, specified
   algebraically using two unit vectors "t" and "f" and an associative
   concatenation operator "c".  This new type is intended to characterize
   an initial algebra, so the defining property of the new type includes the
   condition that there is a unique homomorphism from the new type to any other
   type 'b with two elements "x" and "y" and an associative operation "op".

   Melham's paper clearly shows that this other type 'b must not be a free type
   of the specification, but in fact must be universally quantified in order for
   the next step, of realizing the hypothesized operators of the new abstract
   type as actual new constants, once the new type is created.

   HOL-Omega not only supports the universal quantification of terms by type
   variables, as needed above, but also provides an improved version of
   the type specification definitional principle over Melham's rule.
   The type specification rule suggested by Melham was

   Gamma_1 |- ?x.P x, Gamma_2 |- ('a ~~ (P:ty -> bool)) ==> Q
   ---------------------------------------------------------- 'a not in ty or P
               Gamma_1 U Gamma_2 |- Q[newty / 'a)

   where the notation 'a ~~ P' is an abbreviation for the assertion that there
   is a bijection between the values of type 'a and the set of values that
   satisfy P:

        ?f:'a -> ty. (!a1 a2. (f a1 = f a2) ==> (a1 = a2)) /\
                     (!r. P r = (?a. r = f a)).

   By contrast, the type specification rule supported by HOL-Omega is

                            |- ?:'a. Q
                       --------------------
                         |- Q[newty / 'a].

   Actually, the rule implmented in HOL-Omega is more general, in that it may
   introduce multiple new types simultaneously:

                       |- ?:'a_1 ... 'a_n. Q
         -------------------------------------------------
           |- Q[newty_1, ..., newty_n / 'a_1, ..., 'a_n].

   The following ML function is used to make type specifications:

        new_type_specification : string * string list * thm -> thm

   Evaluating

        new_type_specification("name", ["tau_1", ..., "tau_n"],
                               |- ?:'a_1 ... 'a_n. Q['a_1, ..., 'a_n])

   simultaneously introduces new types named tau_1, ..., tau_n satisfying the
   property

        |- Q[tau_1, ..., tau_n].

   This theorem is stored, with name "name", as a definition in the current
   theorey segment.

   A call to new_type_specification fails if:

     (i) the theorem argument has a non-empty assumption list;
    (ii) there are free variables or free type variables in the
         theorem argument;
   (iii) tau_1, ..., tau_n are not distinct names,
    (iv) the kind of some taui does not contain all the kind variables
         which occur in the term  ?:'a_1 ... 'a_n. Q['a_1, ..., 'a_n].

  ---------------------------------------------------------------------------*)

structure type_specScript =
struct

open HolKernel Parse boolLib bossLib

val _ = set_trace "Unicode" 0;

val _ = new_theory "type_spec";

val atype_exists = store_thm(
   "atype_exists",
   ``?:'a. T``,
   TY_EXISTS_TAC bool
   THEN ACCEPT_TAC TRUTH
  );

val atype_def = new_type_specification("atype",["atype"],atype_exists);

val two_type_exists = store_thm(
   "two_type_exists",
   ``?:'a. ?(x:'a) y. ~(x = y) /\ !z. (z = x) \/ (z = y)``,
   TY_EXISTS_TAC ``:bool``
   THEN EXISTS_TAC ``T``
   THEN EXISTS_TAC ``F``
   THEN REWRITE_TAC [BOOL_CASES_AX]
  );

val two_type_def = new_type_specification("two_type",["two"],two_type_exists);

val two_constants_spec =
  new_specification ("two_consts_spec",
                     [ "A2",
                       "B2" ],
                     two_type_def);

open sumTheory;

val clock3_def = Define
  `(clock3 (INL ()) = INR (INL ())) /\
   (clock3 (INR (INL ())) = INR (INR ())) /\
   (clock3 (INR (INR ())) = INL ())`;

val three_type_exists = store_thm(
   "three_type_exists",
   ``?:'a. ?x y z (gr:'a -> 'a -> bool).
        (~(x = y) /\ ~(x = z) /\ ~(y = z)) /\
        (!u. (u = x) \/ (u = y) \/ (u = z)) /\
        (gr x y /\ gr y z /\ gr z x)``,
   TY_EXISTS_TAC ``:one + one + one``
   THEN EXISTS_TAC ``INL () : one + one + one``
   THEN EXISTS_TAC ``INR (INL ()) : one + one + one``
   THEN EXISTS_TAC ``INR (INR ()) : one + one + one``
   THEN EXISTS_TAC ``\x y. y = clock3 x``
   THEN SIMP_TAC (bool_ss ++ sumSimps.SUM_ss) [clock3_def]
   THEN Cases
   THEN SIMP_TAC (bool_ss ++ sumSimps.SUM_ss) [oneTheory.one]
   THEN Cases_on `y`
   THEN SIMP_TAC (bool_ss ++ sumSimps.SUM_ss) [oneTheory.one]
  );

val three_type_def = new_type_specification("three_type",["three"],three_type_exists);

val rock_paper_scissors_spec =
  Rsyntax.new_specification
             { name    = "rock_paper_scissors_spec",
               consts  = [ {const_name="rock",      fixity=SOME Closefix},
                           {const_name="scissors",  fixity=SOME Closefix},
                           {const_name="paper",     fixity=SOME Closefix},
                           {const_name="beats",     fixity=SOME (Infix (NONASSOC,450))} ],
               sat_thm = three_type_def };


(* ---------------------------------------------- *)
(* Tom Melham's example of non-empty bit vectors  *)
(* This version done without the quotient library *)
(* ---------------------------------------------- *)

(* First, create the type of non-empty bit vectors *)

val P = ``\l:bool list. ~(l = [])``;

val NOT_CONS_NIL = listTheory.NOT_CONS_NIL;

val bits_inhab = TAC_PROOF(([],
   ``?l. ^P l``),
   EXISTS_TAC ``[T]``
   THEN BETA_TAC
   THEN REWRITE_TAC[NOT_CONS_NIL]
  );

val bits_def = new_type_definition ("bits", bits_inhab);

val bits_bijs = define_new_type_bijections
                    {name="bits_bijs",
                     ABS ="bits_ABS",
                     REP ="bits_REP",
                     tyax=bits_def};

(* definition "bits_bijs"; *)

val bits_REP_one_one = BETA_RULE (prove_rep_fn_one_one bits_bijs);
val bits_REP_onto    = BETA_RULE (prove_rep_fn_onto    bits_bijs);
val bits_ABS_one_one = BETA_RULE (prove_abs_fn_one_one bits_bijs);
val bits_ABS_onto    = BETA_RULE (prove_abs_fn_onto    bits_bijs);

val (bits_ABS_REP,bits_EQ_REP_ABS) = CONJ_PAIR (BETA_RULE bits_bijs);

val bits_REP_ABS = store_thm(
   "bits_REP_ABS",
   ``!r. ~(r = []) ==> (bits_REP (bits_ABS r) = r)``,
   REWRITE_TAC [bits_EQ_REP_ABS]
  );

val bits_REP_NOT_NULL = store_thm(
   "bits_REP_NOT_NULL",
   ``!a. ~(bits_REP a = [])``,
   SIMP_TAC list_ss [bits_REP_onto,bits_REP_one_one]
  );

(* Define the constants and operators of the new type "bits". *)

val t0_def = Define `t0 = bits_ABS [T]`;
val f0_def = Define `f0 = bits_ABS [F]`;
val c0_def = Define `c0 x y = bits_ABS (bits_REP x ++ bits_REP y)`;

val c0_assoc = store_thm(
   "c0_assoc",
   ``!x y z:bits. c0 x (c0 y z) = c0 (c0 x y) z``,
   SIMP_TAC list_ss [c0_def,bits_REP_ABS,bits_REP_NOT_NULL]
  );

(* A useful lemma. *)

val bits_CONS_EQ_REP_ABS_APPEND = store_thm(
   "bits_CONS_EQ_REP_ABS_APPEND",
   ``!x y ys. x :: y :: ys = bits_REP (bits_ABS [x]) ++ bits_REP (bits_ABS (y::ys))``,
   SIMP_TAC list_ss [bits_REP_ABS]
  );


val bits_cases = store_thm(
   "bits_cases",
   ``!b:bits. (b = t0) \/ (b = f0) \/ (?x y. b = c0 x y)``,
   ONCE_REWRITE_TAC [GSYM bits_ABS_REP]
   THEN REWRITE_TAC [t0_def,f0_def,c0_def]
   THEN SIMP_TAC list_ss [bits_REP_ABS,bits_ABS_one_one,bits_REP_NOT_NULL]
   THEN GEN_TAC
   THEN MP_TAC (SPEC ``b:bits`` bits_REP_NOT_NULL)
   THEN SPEC_TAC (``bits_REP b``,``l:bool list``)
   THEN Cases (* two subgoals *)
   THEN REWRITE_TAC[NOT_CONS_NIL] (* eliminates one subgoal *)
   THEN Cases_on `t` (* two subgoals *)
   THENL
     [ Cases_on `h` (* two subgoals *)
       THEN REWRITE_TAC [],

       SIMP_TAC list_ss []
       THEN EXISTS_TAC ``bits_ABS [h]``
       THEN EXISTS_TAC ``bits_ABS (h'::t')``
       THEN MATCH_ACCEPT_TAC bits_CONS_EQ_REP_ABS_APPEND
     ]
  );


val bits_induct = store_thm(
   "bits_induct",
   ``!P:bits -> bool.
       (P t0) /\
       (P f0) /\
       (!x y. P x /\ P y ==> P (c0 x y)) ==>
       (!b. P b)``,
   REWRITE_TAC [t0_def,f0_def,c0_def]
   THEN GEN_TAC THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM bits_ABS_REP]
   THEN GEN_TAC
   THEN MP_TAC (SPEC ``b:bits`` bits_REP_NOT_NULL)
   THEN SPEC_TAC (``bits_REP b``,``l:bool list``)
   THEN measureInduct_on `LENGTH l`
   THEN Cases_on `l` (* two subgoals *)
   THEN REWRITE_TAC[NOT_CONS_NIL] (* eliminates one subgoal *)
   THEN Cases_on `t` (* two subgoals *)
   THENL
     [ Cases_on `h` (* two subgoals *)
       THEN ASM_REWRITE_TAC [],

       REWRITE_TAC [bits_CONS_EQ_REP_ABS_APPEND]
       THEN ASM_SIMP_TAC list_ss []
     ]
  );

(* Define the combinator "bits_fold x y op"
   which creates a recursive function f
   which on the argument t0, returns x,
         on the argument f0, returns y,
     and on the argument c0 a b, returns op (f a) (f b).

   We do this in three stages:
     bit_fold1  (x:'b) (y:'b)    : bool -> 'b
     bits_fold1 (x:'b) (y:'b) op : bool list -> 'b
     bits_fold  (x:'b) (y:'b) op : bits -> 'b
*)

val bit_fold1_def = Define
  `(bit_fold1 x y T = x:'a) /\
   (bit_fold1 x y F = y)`;

val bits_fold1_def = Define
   `bits_fold1 (x:'b) (y:'b) (op:'b -> 'b -> 'b) (z :: zs) =
      if zs = []
        then bit_fold1 x y z
        else op (bit_fold1 x y z) (bits_fold1 x y op zs)`;

val bits_fold_def = Define
   `bits_fold (x:'b) y op z = bits_fold1 x y op (bits_REP z)`;

val bits_fold_scalars = store_thm(
   "bits_fold_scalars",
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       (bits_fold x y op t0 = x) /\
       (bits_fold x y op f0 = y)``,
   SIMP_TAC list_ss
     [bits_fold_def,t0_def,f0_def,bits_REP_ABS,bits_fold1_def,bit_fold1_def]
  );

(* f : bool list -> 'b is a homomorphism if and only if
   it causes this diagram to commute:

                          f x f
         list x list  ------------>   'b x 'b
              |                          |
           ++ |                          | op
              |                          |
              V                          V
            list      ------------>     'b
                            f
*)

(* load "res_quanLib"; *)
open res_quanLib;

val bits_fold1_is_homo = store_thm(
   "bits_fold1_is_homo",
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
       !(a :bool list) (b:bool list) :: (\v.~(v = [])).
           bits_fold1 x y op (a ++ b) =
           op (bits_fold1 x y op a) (bits_fold1 x y op b)``,
   REPEAT GEN_TAC
   THEN DISCH_TAC
   THEN SIMP_TAC (bool_ss ++ resq_SS) [pred_setTheory.IN_ABS]
   THEN Induct (* two subgoals *)
   THEN REWRITE_TAC [NOT_CONS_NIL] (* eliminates one subgoal *)
   THEN REWRITE_TAC [listTheory.APPEND,bits_fold1_def]
   THEN Cases_on `a` (* two subgoals *)
   THEN ASM_SIMP_TAC list_ss []
  );

(* f : bits -> 'b is a homomorphism if and only if
   it causes this diagram to commute:

                          f x f
         bits x bits  ------------>   'b x 'b
              |                          |
           c0 |                          | op
              |                          |
              V                          V
            bits      ------------>     'b
                            f
*)

val bits_fold_is_homo = store_thm(
   "bits_fold_is_homo",
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
       !a b.
           bits_fold x y op (c0 a b) =
           op (bits_fold x y op a) (bits_fold x y op b)``,
   SIMP_TAC (list_ss ++ resq_SS)
        [bits_fold_def,c0_def,bits_REP_ABS,bits_REP_NOT_NULL,
         pred_setTheory.IN_ABS,bits_fold1_is_homo]
  );

(*
  bits with (t0,f0,c0) is initial if there exists one and only one arrow
  from it to any type 'b with (x:'b,y:'b,op:'b->'b->'b) where op is associative,
  in the category of algebras where the arrows are homomorphisms.
*)

val bits_is_initial = store_thm(
   "bits_is_initial",
   ``!:'b. !(x:'b) (y:'b) (op:'b -> 'b -> 'b).
              (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
              ?!(fn:bits -> 'b).
                        (fn  t0           = x) /\
                        (fn  f0           = y) /\
                  (!a b. fn (c0 a b) = op (fn a) (fn b))``,
   REPEAT STRIP_TAC
   THEN SIMP_TAC bool_ss [EXISTS_UNIQUE_DEF]
   THEN CONJ_TAC
   THENL
     [ EXISTS_TAC ``bits_fold (x:'b) y op``
       THEN REWRITE_TAC[bits_fold_scalars]
       THEN POP_ASSUM MP_TAC
       THEN REWRITE_TAC[bits_fold_is_homo],

       Q.X_GEN_TAC `f`
       THEN Q.X_GEN_TAC `g`
       THEN STRIP_TAC
       THEN CONV_TAC FUN_EQ_CONV
       THEN HO_MATCH_MP_TAC bits_induct (* induct on b *)
       THEN REPEAT STRIP_TAC (* 3 subgoals *)
       THEN ASM_REWRITE_TAC []
     ]
  );

(*
g `!:'b. !(x:'b) (y:'b) (op:'b -> 'b -> 'b).
              (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
              ?!(fn:bits -> 'b).
                        (fn  t0           = x) /\
                        (fn  f0           = y) /\
                  (!a b. fn (c0 a b) = op (fn a) (fn b))`;
e (REPEAT STRIP_TAC);
e (SIMP_TAC bool_ss [EXISTS_UNIQUE_DEF]);
e (CONJ_TAC);
e (EXISTS_TAC ``bits_fold (x:'b) y op``);
e (REWRITE_TAC[bits_fold_scalars]);
e (POP_ASSUM MP_TAC THEN REWRITE_TAC[bits_fold_is_homo]);

e (Q.X_GEN_TAC `f` THEN Q.X_GEN_TAC `g`);
e (STRIP_TAC);
e (CONV_TAC FUN_EQ_CONV);
e (HO_MATCH_MP_TAC bits_induct);
e (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

*)

(* Now we can prove that there exists some type with such a set of
   operators (t,f,c), with c associative, and which is initial. *)

val vect_exists = store_thm(
   "vect_exists",
   ``?:'a.
       ?(t:'a) (f:'a) (c:'a -> 'a -> 'a).
         (!a1 a2 a3. c a1 (c a2 a3) = c (c a1 a2) a3) /\
         (!:'b.
            !(x:'b) (y:'b) (op:'b -> 'b -> 'b).
              (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
              ?!fn:'a -> 'b.         (fn t         = x) /\
                                     (fn f         = y) /\
                             (!a1 a2. fn (c a1 a2) = op (fn a1) (fn a2)))``,
   TY_EXISTS_TAC ``:bits``
   THEN EXISTS_TAC ``t0``
   THEN EXISTS_TAC ``f0``
   THEN EXISTS_TAC ``c0``
   THEN REWRITE_TAC [c0_assoc,bits_is_initial]
  );

(* Since such a type exists, we may now create it in the logic
   using the definitional principle of new type specification. *)

val vect_TY_SPEC = new_type_specification("vect",["vect"],vect_exists);

(* Now we may create the associated constants of the new type
   using the definitional principle of new constant specification. *)

(* New constant specification, tuple syntax: *)

val vect_consts_spec =
    new_specification ("vect_consts_spec",
                       [ "VT", "VF", "VCONCAT" ],
                       vect_TY_SPEC);


(* Alternative: New constant specification, record syntax:

val vect_consts_spec =
  Rsyntax.new_specification
             { name    = "vect_consts_spec",
               consts  = [ {const_name="VT",      fixity=SOME Parse.Closefix},
                           {const_name="VF",      fixity=SOME Parse.Closefix},
                           {const_name="VCONCAT", fixity=SOME (Infixl 480)} ],
               sat_thm = vect_def };

*)

val (VCONCAT_ASSOC, vect_is_initial) = CONJ_PAIR vect_consts_spec;

val (vect_fn_exists,vect_fn_unique) = CONJ_PAIR
      (CONV_RULE (Ho_Rewrite.ONCE_REWRITE_CONV [IMP_CONJ_THM] THENC
           DEPTH_CONV (FORALL_IMP_CONV ORELSEC TY_FORALL_IMP_CONV ORELSEC
                       FORALL_AND_CONV ORELSEC TY_FORALL_AND_CONV))
        (SIMP_RULE bool_ss [EXISTS_UNIQUE_DEF] vect_is_initial));

val _ = match [] ``VCONCAT``;

(* Can we actually prove recursion and induction from initiality? *)

(*

val vect_Axiom = store_thm(
   "vect_Axiom",
   ``!f0 f1 f2.
       (!x y z. f2 x (f2 y z) = f2 (f2 x y) z) ==>
       ?fn:vect -> 'a.
         (fn VT = f0) /\
         (fn VF = f1) /\
         !a0 a1. fn (VCONCAT a0 a1) = f2 (fn a0) (fn a1)``,
   REWRITE_TAC [vect_fn_exists]
  );

val EQT_ELIM_TAC :tactic = fn (asl,gl) =>
    ([(asl,mk_eq(gl,boolSyntax.T))],
     fn [th] => EQT_ELIM th);


val vect_induct1 = store_thm(
   "vect_induct1",
   ``!P:vect -> bool.
       (P VT) /\
       (P VF) /\
       (!x y. P x /\ P y = P (VCONCAT x y)) ==>
       (!b. P b)``,
   GEN_TAC THEN STRIP_TAC
   THEN REWRITE_TAC [FORALL_DEF]
   THEN BETA_TAC
   THEN HO_MATCH_MP_TAC (MATCH_MP vect_fn_unique CONJ_ASSOC)
   THEN EXISTS_TAC ``T : bool``
   THEN EXISTS_TAC ``T : bool``
   THEN ASM_REWRITE_TAC []
  );

val vect_induct = store_thm(
   "vect_induct",
   ``!P:vect -> bool.
      (!x y z. P
       (P VT) /\
       (P VF) /\
       (!x y. P x /\ P y ==> P (VCONCAT x y)) ==>
       (!b. P b)``,
   GEN_TAC THEN STRIP_TAC
   THEN REWRITE_TAC [FORALL_DEF]
   THEN BETA_TAC
   THEN HO_MATCH_MP_TAC (MATCH_MP vect_fn_unique CONJ_ASSOC)
   THEN EXISTS_TAC ``T : bool``
   THEN EXISTS_TAC ``T : bool``
   THEN ASM_REWRITE_TAC []
   THEN ONCE_REWRITE_TAC [GSYM bits_ABS_REP]
   THEN GEN_TAC
   THEN MP_TAC (SPEC ``b:bits`` bits_REP_NOT_NULL)
   THEN SPEC_TAC (``bits_REP b``,``l:bool list``)
   THEN measureInduct_on `LENGTH l`
   THEN Cases_on `l` (* two subgoals *)
   THEN REWRITE_TAC[NOT_CONS_NIL] (* eliminates one subgoal *)
   THEN Cases_on `t` (* two subgoals *)
   THENL
     [ Cases_on `h` (* two subgoals *)
       THEN ASM_REWRITE_TAC [],

       REWRITE_TAC [bits_CONS_EQ_REP_ABS_APPEND]
       THEN ASM_SIMP_TAC list_ss []
     ]
  );
*)



val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "type_spec";

val _ = export_theory();

end; (* structure type_specScript *)

