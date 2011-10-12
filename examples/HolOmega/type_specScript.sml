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

val _ = set_trace "Unicode" 1;

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


(* Tom Melham's examples of non-empty bit vectors *)

open quotientLib;

val APPEND_ASSOC = listTheory.APPEND_ASSOC;

val list_eq_def =
    Define `list_eq (x:bool list) y = ~(x=[]) /\ ~(y=[]) /\ (x=y)`;

val NOT_CONS_NIL = listTheory.NOT_CONS_NIL;

val list_eq_PEQUIV = store_thm(
   "list_eq_PEQUIV",
   ``PARTIAL_EQUIV list_eq``,
   SIMP_TAC list_ss [PARTIAL_EQUIV_def,list_eq_def,FUN_EQ_THM]
   THEN CONJ_TAC
   THENL
     [ EXISTS_TAC ``[T]``
       THEN SIMP_TAC list_ss [],

       PROVE_TAC []
     ]
  );

val list_eq_RSP = store_thm(
   "list_eq_RSP",
   ``!x1 y1 x2 y2.
       list_eq x1 x2 /\ list_eq y1 y2 ==>
       (list_eq x1 y1 = list_eq x2 y2)``,
   SIMP_TAC list_ss [list_eq_def]
  );

val APPEND_CONG = store_thm(
   "APPEND_CONG",
   ``!(x1:bool list) x2 y1 y2.
          list_eq x1 x2 /\ list_eq y1 y2 ==>
          list_eq (x1 ++ y1) (x2 ++ y2)``,
   SIMP_TAC list_ss [list_eq_def]
  );

open res_quanLib res_quanTheory;
val W_DEF = combinTheory.W_DEF;
val SPECIFICATION = pred_setTheory.SPECIFICATION;

val NONNIL_ASSOC = store_thm(
   "NONNIL_ASSOC",
   ``!(l1 :bool list) l2 l3 :: respects list_eq.
       list_eq
         (l1 ++ (l2 ++ l3))
         ((l1 ++ l2) ++ l3)``,
   SIMP_TAC (list_ss ++ resq_SS)
            [respects_def,W_DEF,SPECIFICATION,list_eq_def,APPEND_ASSOC]
  );

val examplefn_def = Define
  `(examplefn (x:'b) (y:'b) (op:'b -> 'b -> 'b) [] = x) /\
   (examplefn x y op [T] = x) /\
   (examplefn x y op [F] = y) /\
   (examplefn x y op (T :: zs) = op x (examplefn x y op zs)) /\
   (examplefn x y op (F :: zs) = op y (examplefn x y op zs))`;

val examplefn_respects = store_thm(
   "examplefn_respects",
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       examplefn x y op IN respects (list_eq ===> $=)``,
   SIMP_TAC bool_ss [IN_RESPECTS,FUN_REL,list_eq_def]
  );

val examplefn_ind = theorem "examplefn_ind";

val examplefn_cons = store_thm(
   "examplefn_cons",
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       !(a :bool) (b:bool list :: respects list_eq).
           examplefn x y op (a :: b) =
           op (examplefn x y op [a]) (examplefn x y op b)``,
   GEN_TAC THEN GEN_TAC THEN GEN_TAC
   THEN Cases (* two subgoals, a = T or F *)
   THEN CONV_TAC RES_FORALL_CONV
   THEN REWRITE_TAC[IN_RESPECTS,FUN_REL,list_eq_def]
   THEN Cases
   THEN SIMP_TAC list_ss [NOT_CONS_NIL,examplefn_def]
  );

val examplefn_cons1 = TAC_PROOF(([],
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       !(a :bool) (b:bool list).
           ~(b = []) ==>
           (examplefn x y op (a :: b) =
            op (examplefn x y op [a]) (examplefn x y op b))``),
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC (DISCH_ALL (RESQ_SPEC ``b:bool list``
                                    (SPEC_ALL examplefn_cons)))
   THEN ASM_REWRITE_TAC[IN_RESPECTS,list_eq_def]
  );

local open simpLib
in
val list_resq_ss = list_ss ++ resq_SS
end

val examplefn_homo = store_thm(
   "examplefn_homo",
   ``!(x :'b) (y:'b) (op:'b -> 'b -> 'b).
       (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
       !(a :bool list) (b:bool list) :: respects list_eq.
           examplefn x y op (a ++ b) =
           op (examplefn x y op a) (examplefn x y op b)``,
   GEN_TAC THEN GEN_TAC THEN GEN_TAC
   THEN DISCH_TAC
   THEN CONV_TAC RES_FORALL_CONV
   THEN REWRITE_TAC[IN_RESPECTS,FUN_REL,list_eq_def]
   THEN Induct
   THEN REWRITE_TAC [NOT_CONS_NIL]
   THEN GEN_TAC
   THEN Cases_on `a: bool list`
   THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_CONS_NIL])
   THENL
     [ SIMP_TAC list_ss [examplefn_cons],

       CONV_TAC RES_FORALL_CONV
       THEN GEN_TAC
       THEN POP_ASSUM (MP_TAC o CONV_RULE RES_FORALL_CONV)
       THEN REWRITE_TAC[IN_RESPECTS,list_eq_def]
       THEN ASM_SIMP_TAC list_ss [examplefn_cons1]
     ]
  );

val fn_cons = store_thm(
   "fn_cons",
   ``!(op:'b -> 'b -> 'b) (fn:bool list -> 'b).
        (!b1 b2 :: respects list_eq. fn (b1 ++ b2) = op (fn b1) (fn b2)) ==>
        !(a :bool) (b:bool list :: respects list_eq).
           fn (a :: b) = op (fn [a]) (fn b)``,
   REPEAT GEN_TAC
   THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
   THEN REWRITE_TAC[IN_RESPECTS,FUN_REL,list_eq_def]
   THEN STRIP_TAC
   THEN POP_ASSUM (fn th => ASM_SIMP_TAC list_ss [GSYM th])
  );

val _ = associate_restriction ("?!!", "RES_EXISTS_EQUIV");

val NONNIL_EXISTS_UNIQUE_FUN = store_thm(
   "NONNIL_EXISTS_UNIQUE_FUN",
   ``!:'b. !(x:'b) (y:'b) (op:'b -> 'b -> 'b).
              (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
              ?!!(fn:bool list -> 'b) :: (list_eq ===> $=).
                                     (fn [T]        = x) /\
                                     (fn [F]        = y) /\
         (!b1 b2 :: respects list_eq. fn (b1 ++ b2) = op (fn b1) (fn b2))``,
   REPEAT STRIP_TAC
   THEN SIMP_TAC bool_ss [RES_EXISTS_EQUIV_DEF]
   THEN CONJ_TAC
   THENL (* resq_SS, resq_ss *)
     [ CONV_TAC RES_EXISTS_CONV
       THEN EXISTS_TAC ``examplefn (x:'b) y op``
       THEN REWRITE_TAC[examplefn_respects]
       THEN REWRITE_TAC[examplefn_def]
       THEN POP_ASSUM MP_TAC
       THEN REWRITE_TAC[examplefn_homo],

       CONV_TAC RES_FORALL_CONV
       THEN CONV_TAC (ONCE_DEPTH_CONV RES_FORALL_CONV)
       THEN REWRITE_TAC[IN_RESPECTS,FUN_REL,list_eq_def]
       THEN SIMP_TAC bool_ss []
       THEN REPEAT GEN_TAC THEN STRIP_TAC
       THEN Induct
       THEN REWRITE_TAC[NOT_CONS_NIL]
       THEN Cases
       THEN POP_ASSUM MP_TAC
       THEN Cases_on `y'' = []`
       THEN ASM_REWRITE_TAC[]
       THEN DISCH_TAC
       THEN IMP_RES_THEN (MP_TAC o CONV_RULE (DEPTH_CONV RES_FORALL_CONV))
                         fn_cons
       THEN ASM_REWRITE_TAC [IN_RESPECTS,list_eq_def]
       THENL [ REPEAT (DISCH_THEN
                        (ASSUME_TAC o SPECL [``T``,``y'':bool list``])),
               REPEAT (DISCH_THEN
                        (ASSUME_TAC o SPECL [``F``,``y'':bool list``])) ]
       THEN POP_ASSUM MP_TAC
       THEN POP_ASSUM MP_TAC
       THEN ASM_SIMP_TAC bool_ss []
     ]
  );

val vT0_def = Define `vT0 = [T]`;
val vF0_def = Define `vF0 = [F]`;

val vT0_RSP = store_thm(
   "vT0_RSP",
   ``list_eq vT0 vT0``,
   SIMP_TAC list_ss [vT0_def,list_eq_def]
  );

val vF0_RSP = store_thm(
   "vF0_RSP",
   ``list_eq vF0 vF0``,
   SIMP_TAC list_ss [vF0_def,list_eq_def]
  );

val NONNIL_EXISTS_UNIQUE_FUN_1 =
   REWRITE_RULE (map GSYM [vT0_def,vF0_def])
                (TY_SPEC_ALL NONNIL_EXISTS_UNIQUE_FUN);

val _ = quotientLib.chatting := true;

val [concat_assoc,vect_exists_unique_fun] =
  define_quotient_types
    { types = [{name  = "vect0",
                equiv = list_eq_PEQUIV}],
      defs  = [{def_name = "vT_def",
                fname    = "vT",
                func     = ``vT0``,
                fixity   = SOME Parse.Closefix },
               {def_name = "vF_def",
                fname    = "vF",
                func     = ``vF0``,
                fixity   = SOME Parse.Closefix },
               {def_name = "concat_def",
                fname    = "concat",
                func     = ``APPEND : bool list -> bool list -> bool list``,
                fixity   = SOME (Infixl 480) } ],
      tyop_equivs    = [],
      tyop_quotients = [FUN_QUOTIENT],
      tyop_simps     = [FUN_MAP_I, FUN_REL_EQ],
      respects       = [APPEND_CONG, vT0_RSP, vF0_RSP],
      poly_preserves = [FORALL_PRS, EXISTS_UNIQUE_PRS],
      poly_respects  = [RES_FORALL_RSP, RES_EXISTS_EQUIV_RSP],
      old_thms       = [NONNIL_ASSOC, NONNIL_EXISTS_UNIQUE_FUN_1]
    };

val vect_exists = store_thm(
   "vect_exists",
   ``?:'a.
       ?(t:'a) (f:'a) (c:'a -> 'a -> 'a).
         (!b1 b2 b3. c b1 (c b2 b3) = c (c b1 b2) b3) /\
         (!:'b.
            !(x:'b) (y:'b) (op:'b -> 'b -> 'b).
              (!b1 b2 b3. op b1 (op b2 b3) = op (op b1 b2) b3) ==>
              ?!fn:'a -> 'b.         (fn t         = x) /\
                                     (fn f         = y) /\
                             (!b1 b2. fn (c b1 b2) = op (fn b1) (fn b2)))``,
   TY_EXISTS_TAC ``:vect0``
   THEN EXISTS_TAC ``vT``
   THEN EXISTS_TAC ``vF``
   THEN EXISTS_TAC ``$concat``
   THEN REWRITE_TAC [concat_assoc,vect_exists_unique_fun]
  );

val vect_def = new_type_specification("vect",["vect"],vect_exists);

(* New constant specification, tuple syntax:

val vect_constants_spec =
  new_specification ("vect_consts_spec",
                     [ "VT",
                       "VF",
                       "vconcat" ],
                     vect_def);
*)

(* New constant specification, record syntax: *)

val vect_constants_spec =
  Rsyntax.new_specification
             { name    = "vect_consts_spec",
               consts  = [ {const_name="VT",      fixity=SOME Parse.Closefix},
                           {const_name="VF",      fixity=SOME Parse.Closefix},
                           {const_name="vconcat", fixity=SOME (Infixl 480)} ],
               sat_thm = vect_def };




val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "type_spec";

val _ = export_theory();

end; (* structure type_specScript *)

