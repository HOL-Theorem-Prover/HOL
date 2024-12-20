
open HolKernel Parse boolLib bossLib; val _ = new_theory "milawa_logic";
open listTheory arithmeticTheory lisp_sexpTheory milawa_ordinalTheory;
open pred_setTheory combinTheory finite_mapTheory stringTheory;

(* ========================================================================== *)
(*                                                                            *)
(*   This theory defines (1) the syntax of the Milawa logic,                  *)
(*                       (2) its semantics and                                *)
(*                       (3) its axioms and inference rules.                  *)
(*                                                                            *)
(*   Towards the end we also prove soundness and theorem which states that    *)
(*   it is sound to add new definitions.                                      *)
(*                                                                            *)
(* ========================================================================== *)



val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(* PART 1: SYNTAX

   We start by defining the abstract syntax of valid Milawa terms and formulas. *)

val _ = Hol_datatype `
  logic_primitive_op =
    logic_CONS | logic_EQUAL | logic_LESS | logic_SYMBOL_LESS |
    logic_ADD | logic_SUB | logic_NOT | logic_RANK | logic_CONSP | logic_NATP |
    logic_SYMBOLP | logic_CAR | logic_CDR | logic_ORD_LESS | logic_ORDP | logic_IF`;

val _ = Hol_datatype `
  logic_func = mPrimitiveFun of logic_primitive_op
             | mFun of string`;

val _ = Hol_datatype `
  logic_term = mConst of SExp
             | mVar of string
             | mApp of logic_func => logic_term list
             | mLamApp of string list => logic_term => logic_term list`

val _ = Hol_datatype `
  formula = Or of formula => formula              (*  por*     *)
          | Not of formula                        (*  pnot*    *)
          | Equal of logic_term => logic_term     (*  pequal*  *)`;

(* Unfortunately, the above definition is not enough to completely define
   what correct syntax is. In particular, the folloing properties require
   a separate (term_ok) assertion:
     - all user-defined functions must have an entry in the context (ctxt)
     - the arity of function applications must be correct
     - all variables inside the body of mLamApp must be bound
     - the variable list in mLamApp must not contain duplicates
     - the number of arguments to mLamApp must match the parameter list

   A context (ctxt) is a finite mapping from function names (strings)
   to lists of formal parameters (strings) and either:
     - concrete function body (term), or
     - witness function for a certain expression and variable name. *)

val logic_term_size_def = fetch "-" "logic_term_size_def";

val free_vars_def = tDefine "free_vars" `
  (free_vars (mConst s) = []) /\
  (free_vars (mVar v) = [v]) /\
  (free_vars (mApp fc vs) = FLAT (MAP free_vars vs)) /\
  (free_vars (mLamApp xs z ys) = FLAT (MAP free_vars ys))`
 (WF_REL_TAC `measure logic_term_size`);

val primitive_arity_def = Define `
  (primitive_arity logic_CONSP = 1) /\
  (primitive_arity logic_NATP = 1) /\
  (primitive_arity logic_SYMBOLP = 1) /\
  (primitive_arity logic_CAR = 1) /\
  (primitive_arity logic_CDR = 1) /\
  (primitive_arity logic_ORDP = 1) /\
  (primitive_arity logic_NOT = 1) /\
  (primitive_arity logic_RANK = 1) /\
  (primitive_arity logic_IF = 3) /\
  (primitive_arity _ = 2:num)`;

val _ = Hol_datatype `
  func_body = (* body of normal function defition *)
              BODY_FUN of logic_term
            | (* expression, variable name, and semantic witness function *)
              WITNESS_FUN of logic_term => string
            | (* intermediate step in function definition *)
              NO_FUN`;

val _ = type_abbrev("context_type",
  ``:string |-> (string list # func_body # (SExp list -> SExp))``)

val func_arity_def = Define `
  (func_arity (ctxt:context_type) (mPrimitiveFun p) = SOME (primitive_arity p)) /\
  (func_arity ctxt (mFun f) = if f IN FDOM ctxt then SOME (LENGTH (FST (ctxt ' f))) else NONE)`;

val term_ok_def = tDefine "term_ok" `
  (term_ok ctxt (mConst s) = T) /\
  (term_ok ctxt (mVar v) = T) /\
  (term_ok ctxt (mApp fc vs) =
     (func_arity ctxt fc = SOME (LENGTH vs)) /\ EVERY (term_ok ctxt) vs) /\
  (term_ok ctxt (mLamApp xs y zs) =
     (LIST_TO_SET (free_vars y) SUBSET LIST_TO_SET xs) /\ ALL_DISTINCT xs /\
     EVERY (term_ok ctxt) zs /\ term_ok ctxt y /\ (LENGTH xs = LENGTH zs))`
 (WF_REL_TAC `measure (logic_term_size o SND)`);

val formula_ok_def = Define `
  (formula_ok ctxt (Not x) = formula_ok ctxt x) /\
  (formula_ok ctxt (Or x y) = formula_ok ctxt x /\ formula_ok ctxt y) /\
  (formula_ok ctxt (Equal t1 t2) = term_ok ctxt t1 /\ term_ok ctxt t2)`;


(* PART 2: Semantics

   We define the semantics of a formula as MilawaValid. For that we
   need a few auxilliary definitions. First we need a semantics for
   evaluation of terms. *)

val FunVarBind_def = Define `
  (FunVarBind [] args = (\x. Sym "NIL")) /\
  (FunVarBind (p::ps) [] = (\x. Sym "NIL")) /\
  (FunVarBind (p::ps) (a::as) = (p =+ a) (FunVarBind ps as))`;

val LISP_IF_def = Define `LISP_IF x y z = if isTrue x then y else z`;

val EVAL_PRIMITIVE_def = Define `
  (EVAL_PRIMITIVE logic_CONS xs = LISP_CONS (EL 0 xs) (EL 1 xs)) /\
  (EVAL_PRIMITIVE logic_EQUAL xs = LISP_EQUAL (EL 0 xs) (EL 1 xs)) /\
  (EVAL_PRIMITIVE logic_LESS xs = LISP_LESS (EL 0 xs) (EL 1 xs)) /\
  (EVAL_PRIMITIVE logic_SYMBOL_LESS xs = LISP_SYMBOL_LESS (EL 0 xs) (EL 1 xs)) /\
  (EVAL_PRIMITIVE logic_ADD xs = LISP_ADD (EL 0 xs) (EL 1 xs)) /\
  (EVAL_PRIMITIVE logic_SUB xs = LISP_SUB (EL 0 xs) (EL 1 xs)) /\
  (EVAL_PRIMITIVE logic_CONSP xs = LISP_CONSP (EL 0 xs)) /\
  (EVAL_PRIMITIVE logic_NATP xs = LISP_NUMBERP (EL 0 xs)) /\
  (EVAL_PRIMITIVE logic_SYMBOLP xs = LISP_SYMBOLP (EL 0 xs)) /\
  (EVAL_PRIMITIVE logic_NOT xs = LISP_TEST (EL 0 xs = Sym "NIL")) /\
  (EVAL_PRIMITIVE logic_RANK xs = Val (LSIZE (EL 0 xs))) /\
  (EVAL_PRIMITIVE logic_IF xs = LISP_IF (EL 0 xs) (EL 1 xs) (EL 2 xs)) /\
  (EVAL_PRIMITIVE logic_CAR xs = CAR (EL 0 xs)) /\
  (EVAL_PRIMITIVE logic_CDR xs = CDR (EL 0 xs)) /\
  (EVAL_PRIMITIVE logic_ORD_LESS xs = LISP_TEST (ORD_LT (EL 0 xs) (EL 1 xs))) /\
  (EVAL_PRIMITIVE logic_ORDP xs = LISP_TEST (ORDP (EL 0 xs)))`;

val EvalApp_def = Define `
  (EvalApp (mPrimitiveFun p,args,ctxt) = EVAL_PRIMITIVE p args) /\
  (EvalApp (mFun name,args,ctxt) =
     let (params,body,sem) = ctxt ' name in sem args)`;

val MEM_IMP_logic_term_size = prove(
  ``!xs x. MEM x xs ==> logic_term_size x < logic_term1_size xs``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,logic_term_size_def]
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC \\ RES_TAC \\ DECIDE_TAC);

val EvalTerm_def = tDefine "EvalTerm" `
  (EvalTerm (a,ctxt) (mConst c) = c) /\
  (EvalTerm (a,ctxt) (mVar v) = a v) /\
  (EvalTerm (a,ctxt) (mApp f args) =
     EvalApp (f,MAP (EvalTerm (a,ctxt)) args,ctxt)) /\
  (EvalTerm (a,ctxt) (mLamApp vs x ys) =
     let xs = MAP (EvalTerm (a,ctxt)) ys in
       EvalTerm (FunVarBind vs xs,ctxt) x)`
 (WF_REL_TAC `measure (logic_term_size o SND)`
  \\ SRW_TAC [] []
  \\ IMP_RES_TAC MEM_IMP_logic_term_size
  \\ REPEAT DECIDE_TAC
  \\ Cases_on `args` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,EL]
  \\ EVAL_TAC \\ DECIDE_TAC);

val EvalFormula_def = Define `
  (EvalFormula (a,ctxt) (Not f) = ~EvalFormula (a,ctxt) f) /\
  (EvalFormula (a,ctxt) (Or f1 f2) = EvalFormula (a,ctxt) f1 \/ EvalFormula (a,ctxt) f2) /\
  (EvalFormula (a,ctxt) (Equal t1 t2) = (EvalTerm (a,ctxt) t1 = EvalTerm (a,ctxt) t2))`;

(* A Milawa formula is considered to be valid if it is true for all
   variable instantiations, and syntacically well-formed. *)

val MilawaValid_def = Define `
  MilawaValid ctxt f = formula_ok ctxt f /\ !a. EvalFormula (a,ctxt) f`;

(* We require all functions in the context to be syntactically correct
   functions that do not to have any duplicate parameters and do not
   mention variables other than their respective formal
   parameters. Their semantic functions must satisfy the relevant
   property: functions that have a concrete body, and must satisfy the
   defining equation and witness functions must return a value that
   make a property true.

   Notice that normal function definitions need not exist. *)

val context_ok_def = Define `
  context_ok ctxt =
    (!fname params body sem.
       fname IN FDOM ctxt /\ (ctxt ' fname = (params,BODY_FUN body,sem)) ==>
       term_ok ctxt body /\ ALL_DISTINCT params /\
       LIST_TO_SET (free_vars body) SUBSET LIST_TO_SET params /\
       !i. sem (MAP i params) = EvalTerm (i,ctxt) body) /\
    (!fname params exp var sem.
       fname IN FDOM ctxt /\ (ctxt ' fname = (params,WITNESS_FUN exp var,sem)) ==>
       term_ok ctxt exp /\ ALL_DISTINCT (var::params) /\
       LIST_TO_SET (free_vars exp) SUBSET LIST_TO_SET (var::params) /\
       !args.
          (?v. isTrue (EvalTerm (FunVarBind (var::params) (v::args),ctxt) exp)) ==>
          isTrue (EvalTerm (FunVarBind (var::params) ((sem args)::args),ctxt) exp))`;


(* PART 3: Axioms and inference rules *)

(* --- Axioms --- *)

val natp = ``mApp (mPrimitiveFun logic_NATP)``
val symbolp = ``mApp (mPrimitiveFun logic_SYMBOLP)``
val consp = ``mApp (mPrimitiveFun logic_CONSP)``
val ordp = ``mApp (mPrimitiveFun logic_ORDP)``
val ord_less = ``mApp (mPrimitiveFun logic_ORD_LESS)``
val eequal = ``mApp (mPrimitiveFun logic_EQUAL)``
val ccons = ``mApp (mPrimitiveFun logic_CONS)``
val car = ``mApp (mPrimitiveFun logic_CAR)``
val cdr = ``mApp (mPrimitiveFun logic_CDR)``
val symbol_less = ``mApp (mPrimitiveFun logic_SYMBOL_LESS)``
val add = ``mApp (mPrimitiveFun logic_ADD)``
val sub = ``mApp (mPrimitiveFun logic_SUB)``
val less = ``mApp (mPrimitiveFun logic_LESS)``
val nnot = ``mApp (mPrimitiveFun logic_NOT)``
val rank = ``mApp (mPrimitiveFun logic_RANK)``
val ord_lt = ``mApp (mPrimitiveFun logic_ORD_LESS)``
val ordp = ``mApp (mPrimitiveFun logic_ORDP)``
val iff = ``mApp (mPrimitiveFun logic_IF)``
val t = ``mConst (Sym "T")``
val nnil = ``mConst (Sym "NIL")``
val pnot = ``Not``
val pequal = ``Equal``
val por = ``Or``
val a = ``mVar "A"``
val b = ``mVar "B"``
val c = ``mVar "C"``
val x = ``mVar "X"``
val y = ``mVar "Y"``
val z = ``mVar "Z"``
val x1 = ``mVar "X1"``
val x2 = ``mVar "X2"``
val x3 = ``mVar "X3"``
val y1 = ``mVar "Y1"``
val y2 = ``mVar "Y2"``
val y3 = ``mVar "Y3"``
val zero = ``mConst (Val 0)``
val one = ``mConst (Val 1)``
val aand = ``(\x y. mIf x y (mConst (Sym "NIL")))``

val MILAWA_AXIOMS_def = Define `
  MILAWA_AXIOMS = [
  (* Axiom 1. reflexivity *)
    (^pequal ^x ^x);
  (* Axiom 2. equality *)
    (^por (^pnot (^pequal ^x1 ^y1))
    (^por (^pnot (^pequal ^x2 ^y2))
    (^por (^pnot (^pequal ^x1 ^x2))
                 (^pequal ^y1 ^y2))));
  (* Axiom 3. t-not-nil *)
    (^pnot (^pequal ^t ^nnil));
  (* Axiom 4. equal-when-same *)
    (^por (^pnot (^pequal ^x ^y))
          (^pequal (^eequal [^x;^y]) ^t));
  (* Axiom 5. equal-when-diff *)
    (^por (^pequal ^x ^y)
          (^pequal (^eequal [^x;^y]) ^nnil));
  (* Axiom 6. if-when-nil *)
    (^por (^pnot (^pequal ^x ^nnil))
          (^pequal (^iff [^x;^y;^z]) ^z));
  (* Axiom 7. if-when-not-nil *)
    (^por (^pequal ^x ^nnil)
          (^pequal (^iff [^x;^y;^z]) ^y));
  (* Axiom 8. consp-of-cons *)
    (^pequal (^consp [^ccons [^x;^y]]) ^t);
  (* Axiom 9. car-of-cons *)
    (^pequal (^car [^ccons [^x;^y]]) ^x);
  (* Axiom 10. cdr-of-cons *)
    (^pequal (^cdr [^ccons [^x;^y]]) ^y);
  (* Axiom 11. consp-nil-or-t *)
    (^por (^pequal (^consp [^x]) ^nnil)
          (^pequal (^consp [^x]) ^t));
  (* Axiom 12. car-when-not-consp *)
    (^por (^pnot (^pequal (^consp [^x]) ^nnil))
          (^pequal (^car [^x]) ^nnil));
  (* Axiom 13. cdr-when-not-consp *)
    (^por (^pnot (^pequal (^consp [^x]) ^nnil))
         (^pequal (^cdr [^x]) ^nnil));
  (* Axiom 14. cons-of-car-and-cdr *)
    (^por (^pequal (^consp [^x]) ^nnil)
          (^pequal (^ccons [^car [^x]; ^cdr [^x]]) ^x));
  (* Axiom 15. symbolp-nil-or-t *)
    (^por (^pequal (^symbolp [^x]) ^nnil)
          (^pequal (^symbolp [^x]) ^t));
  (* Axiom 16. symbol-<-nil-or-t *)
    (^por (^pequal (^symbol_less [^x;^y]) ^nnil)
          (^pequal (^symbol_less [^x;^y]) ^t));
  (* Axiom 17. irreflexivity-of-symbol-< *)
    (^pequal (^symbol_less [^x;^x]) ^nnil);
  (* Axiom 18. antisymmetry-of-symbol-< *)
    (^por (^pequal (^symbol_less [^x;^y]) ^nnil)
          (^pequal (^symbol_less [^y;^x]) ^nnil));
  (* Axiom 19. transitivity-of-symbol-< *)
    (^por (^pequal (^symbol_less [^x;^y]) ^nnil)
    (^por (^pequal (^symbol_less [^y;^z]) ^nnil)
          (^pequal (^symbol_less [^x;^z]) ^t)));
  (* Axiom 20. trichotomy-of-symbol-< *)
    (^por (^pequal (^symbolp [^x]) ^nnil)
    (^por (^pequal (^symbolp [^y]) ^nnil)
    (^por (^pequal (^symbol_less [^x;^y]) ^t)
    (^por (^pequal (^symbol_less [^y;^x]) ^t)
          (^pequal ^x ^y)))));
  (* Axiom 21. symbol-<-completion-left *)
    (^por (^pequal (^symbolp [^x]) ^t)
          (^pequal (^symbol_less [^x;^y]) (^symbol_less [^nnil;^y])));
  (* Axiom 22. symbol-<-completion-right *)
    (^por (^pequal (^symbolp [^y]) ^t)
          (^pequal (^symbol_less [^x;^y]) (^symbol_less [^x;^nnil])));
  (* Axiom 23. disjoint-symbols-and-naturals *)
    (^por (^pequal (^symbolp [^x]) ^nnil)
          (^pequal (^natp [^x]) ^nnil));
  (* Axiom 24. disjoint-symbols-and-conses *)
    (^por (^pequal (^symbolp [^x]) ^nnil)
          (^pequal (^consp [^x]) ^nnil));
  (* Axiom 25. disjoint-naturals-and-conses *)
    (^por (^pequal (^natp [^x]) ^nnil)
          (^pequal (^consp [^x]) ^nnil));
  (* Axiom 26. natp-nil-or-t *)
    (^por (^pequal (^natp [^x]) ^nnil)
          (^pequal (^natp [^x]) ^t));
  (* Axiom 27. natp-of-plus *)
    (^pequal (^natp [^add [^a;^b]]) ^t);
  (* Axiom 28. commutativity-of-+ *)
    (^pequal (^add [^a;^b]) (^add [^b;^a]));
  (* Axiom 29. associativity-of-+ *)
    (^pequal (^add [^add [^a;^b];^c])
             (^add [^a;^add [^b;^c]]));
  (* Axiom 30. plus-when-not-natp-left *)
    (^por (^pequal (^natp [^a]) ^t)
    (^pequal (^add [^a;^b]) (^add [^zero;^b])));
  (* Axiom 31. plus-of-zero-when-natural *)
    (^por (^pequal (^natp [^a]) ^nnil)
          (^pequal (^add [^a;^zero]) ^a));
  (* Axiom 32. <-nil-or-t *)
    (^por (^pequal (^less [^x;^y]) ^nnil)
          (^pequal (^less [^x;^y]) ^t));
  (* Axiom 33. irreflexivity-of-< *)
    (^pequal (^less [^a;^a]) ^nnil);
  (* Axiom 34. less-of-zero-right *)
    (^pequal (^less [^a;^zero]) ^nnil);
  (* Axiom 35. less-of-zero-left-when-natp *)
    (^por (^pequal (^natp [^a]) ^nnil)
          (^pequal (^less [^zero;^a]) (^iff [^eequal [^a;^zero];^nnil;^t])));
  (* Axiom 36. less-completion-left *)
    (^por (^pequal (^natp [^a]) ^t)
          (^pequal (^less [^a;^b]) (^less [^zero;^b])));
  (* Axiom 37. less-completion-right *)
    (^por (^pequal (^natp [^b]) ^t)
          (^pequal (^less [^a;^b]) ^nnil));
  (* Axiom 38. transitivity-of-< *)
    (^por (^pequal (^less [^a;^b]) ^nnil)
    (^por (^pequal (^less [^b;^c]) ^nnil)
          (^pequal (^less [^a;^c]) ^t)));
  (* Axiom 39. trichotomy-of-<-when-natp *)
    (^por (^pequal (^natp [^a]) ^nnil)
    (^por (^pequal (^natp [^b]) ^nnil)
    (^por (^pequal (^less [^a;^b]) ^t)
    (^por (^pequal (^less [^b;^a]) ^t)
          (^pequal ^a ^b)))));
  (* Axiom 40. one-plus-trick *)
    (^por (^pequal (^less [^a;^b]) ^nnil)
          (^pequal (^less [^b;^add [^one;^a]]) ^nnil));
  (* Axiom 41. natural-less-than-one-is-zero *)
    (^por (^pequal (^natp [^a]) ^nnil)
    (^por (^pequal (^less [^a;^one]) ^nnil)
          (^pequal ^a ^zero)));
  (* Axiom 42. less-than-of-plus-and-plus *)
    (^pequal (^less [^add [^a;^b];^add [^a;^c]]) (^less [^b;^c]));
  (* Axiom 43. natp-of-minus *)
    (^pequal (^natp [^sub [^a;^b]]) ^t);
  (* Axiom 44. minus-when-subtrahend-as-large *)
    (^por (^pequal (^less [^b;^a]) ^t)
          (^pequal (^sub [^a;^b]) ^zero));
  (* Axiom 45. minus-cancels-summand-right *)
    (^pequal (^sub [^add [^a;^b];^b])
             (^iff [^natp [^a];^a;^zero]));
  (* Axiom 46. less-of-minus-left *)
    (^por (^pequal (^less [^b;^a]) ^nnil)
          (^pequal (^less [^sub [^a;^b];^c])
                   (^less [^a;^add [^b;^c]])));
  (* Axiom 47. less-of-minus-right *)
    (^pequal (^less [^a;^sub [^b;^c]])
             (^less [^add [^a;^c];^b]));
  (* Axiom 48. plus-of-minus-right *)
    (^por (^pequal (^less [^c;^b]) ^nnil)
          (^pequal (^add [^a;^sub [^b;^c]])
                   (^sub [^add [^a;^b];^c])));
  (* Axiom 49. minus-of-minus-right *)
    (^por (^pequal (^less [^c;^b]) ^nnil)
          (^pequal (^sub [^a;^sub [^b;^c]])
                   (^sub [^add [^a;^c];^b])));
  (* Axiom 50. minus-of-minus-left *)
    (^pequal (^sub [^sub [^a;^b];^c])
             (^sub [^a;^add [^b;^c]]));
  (* Axiom 51. equal-of-minus-property *)
    (^por (^pequal (^less [^b;^a]) ^nnil)
          (^pequal (^eequal [^sub [^a;^b];^c])
                   (^eequal [^a;^add [^b;^c]])));
  (* Axiom 52. closed-universe *)
    (^por (^pequal (^natp [^x]) ^t)
    (^por (^pequal (^symbolp [^x]) ^t)
          (^pequal (^consp [^x]) ^t)));
  (* Axiom 53. definition-of-not *)
    (^pequal (^nnot [^x]) (^iff [^x;^nnil;^t]));
  (* Axiom 54. definition-of-rank *)
    (^pequal (^rank [^x])
             (^iff [^consp [^x];
                    ^add [^one;^add [^rank [^car [^x]]; ^rank [^cdr [^x]]]];
                    ^zero]));
  (* Axiom 55. definition-of-ord< *)
    (^pequal (^ord_lt [^x;^y])
             (^iff [^nnot [^consp [^x]];
                    ^iff [^consp [^y]; ^t; (^less [^x;^y])];
             (^iff [^nnot [^consp [^y]];
                    ^nnil;
             (^iff [^nnot [^eequal [^car [^car [^x]]; ^car [^car [^y]]]];
                    ^ord_lt [^car [^car [^x]]; ^car [^car [^y]]];
             (^iff [^nnot [^eequal [^cdr [^car [^x]]; ^cdr [^car [^y]]]];
                    ^less [^cdr [^car [^x]]; ^cdr [^car [^y]]];
             (^iff [^t;^ord_lt [^cdr [^x];^cdr [^y]];^nnil])])])])]));
  (* Axiom 56. definition-of-ordp *)
    (^pequal (^ordp [^x])
             (^iff [^nnot [^consp [^x]];
                    ^natp [^x];
             (^iff [^consp [^car [^x]];
             (^iff [^ordp [^car [^car [^x]]];
             (^iff [^nnot [^eequal [^car [^car [^x]]; ^zero]];
             (^iff [^less [^zero; ^cdr [^car [^x]]];
             (^iff [^ordp [^cdr [^x]];
             (^iff [^consp [^cdr [^x]];
                    ^ord_lt [^car [^car [^cdr [^x]]]; ^car [^car [^x]]];
                    ^t]); ^nnil]); ^nnil]); ^nnil]); ^nnil]); ^nnil])]))]`;


(* --- Inference rules --- *)

val LOOKUP_def = Define `
  (LOOKUP x [] r = r) /\
  (LOOKUP x ((y,z)::ys) r = if x = y then z else LOOKUP x ys r)`;

val term_sub_def = tDefine "term_sub" `
  (term_sub ss (mConst s) = mConst s) /\
  (term_sub ss (mVar v) = LOOKUP v ss (mVar v)) /\
  (term_sub ss (mApp fc vs) = mApp fc (MAP (term_sub ss) vs)) /\
  (term_sub ss (mLamApp xs z ys) = mLamApp xs z (MAP (term_sub ss) ys))`
 (WF_REL_TAC `measure (logic_term_size o SND)`);

val formula_sub_def = Define `
  (formula_sub ss (Not x) = Not (formula_sub ss x)) /\
  (formula_sub ss (Or x y) = Or (formula_sub ss x) (formula_sub ss y)) /\
  (formula_sub ss (Equal t1 t2) = Equal (term_sub ss t1) (term_sub ss t2))`;

val or_not_equal_list_def = Define `
  (or_not_equal_list [] x = x) /\
  (or_not_equal_list ((t,s)::xs) x = Or (Not (Equal t s))
                                        (or_not_equal_list xs x))`;

val or_list_def = Define `
  (or_list [x] = x) /\
  (or_list (x::y::xs) = Or x (or_list (y::xs)))`;

val (MilawaTrue_rules,MilawaTrue_ind,MilawaTrue_cases) = Hol_reln `
  (* Associativity *)
  (!a b c ctxt.
     MilawaTrue ctxt (Or a (Or b c)) ==>
     MilawaTrue ctxt (Or (Or a b) c))
  /\
  (* Contraction *)
  (!a ctxt.
     MilawaTrue ctxt (Or a a) ==>
     MilawaTrue ctxt a)
  /\
  (* Cut *)
  (!a b c ctxt.
     MilawaTrue ctxt (Or a b) /\ MilawaTrue ctxt (Or (Not a) c) ==>
     MilawaTrue ctxt (Or b c))
  /\
  (* Expansion *)
  (!a b ctxt.
     formula_ok ctxt a /\
     MilawaTrue ctxt b ==>
     MilawaTrue ctxt (Or a b))
  /\
  (* Propositional Schema *)
  (!a ctxt.
     formula_ok ctxt a ==>
     MilawaTrue ctxt (Or (Not a) a))
  /\
  (* Functional Equality *)
  (!f ts_list ctxt result.
     (result = (or_not_equal_list ts_list (Equal (mApp f (MAP FST ts_list))
                                                 (mApp f (MAP SND ts_list))))) /\
     formula_ok ctxt result ==>
     MilawaTrue ctxt result)
  /\
  (* Instantiation *)
  (!a ss ctxt.
     formula_ok ctxt (formula_sub ss a) /\
     MilawaTrue ctxt a ==>
     MilawaTrue ctxt (formula_sub ss a))
  /\
  (* Beta-reduction *)
  (!a xs ys ctxt.
     formula_ok ctxt (Equal (mLamApp xs a ys) (term_sub (ZIP(xs,ys)) a)) ==>
     MilawaTrue ctxt (Equal (mLamApp xs a ys) (term_sub (ZIP(xs,ys)) a)))
  /\
  (* Base evaluation *)
  (!p args ctxt.
     (primitive_arity p = LENGTH args) ==>
     MilawaTrue ctxt (Equal (mApp (mPrimitiveFun p) (MAP mConst args))
                            (mConst (EVAL_PRIMITIVE p args))))
  /\
  (* Axioms *)
  (!a ctxt.
     MEM a MILAWA_AXIOMS ==>
     MilawaTrue ctxt a)
  /\
  (* User definitions *)
  (!f params body ctxt sem.
     f IN FDOM ctxt /\ (ctxt ' f = (params,BODY_FUN body,sem)) ==>
     MilawaTrue ctxt (Equal (mApp (mFun f) (MAP mVar params)) body))
  /\
  (* User witness function definitions *)
  (!f params exp var_name witness ctxt.
     f IN FDOM ctxt /\ (ctxt ' f = (params,WITNESS_FUN exp var_name,witness)) ==>
     MilawaTrue ctxt (Or (Equal exp ^nnil)
                         (Not (Equal (mLamApp (var_name::params) exp
                                     (mApp (mFun f) (MAP mVar params)::MAP mVar params))
                                     ^nnil))))
  /\
  (* Induction *)
  (!f qs_ss m ctxt.
     (* base case *)
     MilawaTrue ctxt (or_list (f::MAP FST qs_ss)) /\
     (* inductive step *)
     (!q ss. MEM (q,ss) qs_ss ==>
             MilawaTrue ctxt (or_list (f::Not q::MAP (\s. Not (formula_sub s f)) ss))) /\
     (* ordinal step *)
     MilawaTrue ctxt (Equal (^ordp [m]) (mConst (Sym "T"))) /\
     (* measure step *)
     (!q ss s. MEM (q,ss) qs_ss /\ MEM s ss ==>
               MilawaTrue ctxt (Or (Not q)
                                   (Equal (^ord_less [term_sub s m;m])
                                          (mConst (Sym "T")))))
     ==>
     MilawaTrue ctxt f)`;


(* Next we prove a sanity result: MilawaTrue can only derive
   syntactically valid formulas. *)

val MilawaAxiom_IMP_formula_ok = prove(
  ``!x ctxt. MEM x MILAWA_AXIOMS ==> formula_ok ctxt x``,
  SIMP_TAC std_ss [MILAWA_AXIOMS_def,MEM] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,
       func_arity_def,LENGTH,EVERY_DEF,primitive_arity_def]);

val PULL_FORALL_IMP = METIS_PROVE [] ``(p ==> !x. q x) = !x. p ==> q x``;

val term_ok_sub = store_thm("term_ok_sub",
  ``!a ss ctxt.
      term_ok ctxt a /\ EVERY (term_ok ctxt) (MAP SND ss) ==>
      term_ok ctxt (term_sub ss a)``,
  completeInduct_on `logic_term_size a` \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `a`
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term_sub_def,LENGTH_MAP])
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term_sub_def,LENGTH_MAP]
         \\ Induct_on `ss` \\ SIMP_TAC std_ss [EVERY_DEF,LOOKUP_def,term_ok_def]
         \\ Cases_on `h` \\ SIMP_TAC std_ss [EVERY_DEF,LOOKUP_def,term_ok_def]
         \\ SRW_TAC [] [])
  THEN1
   (FULL_SIMP_TAC std_ss [term_ok_def,term_sub_def,LENGTH_MAP,logic_term_size_def]
    \\ SIMP_TAC std_ss [EVERY_MEM,MEM_MAP] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!a.bbb` MATCH_MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ POP_ASSUM MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `l` \\ SRW_TAC [] [logic_term_size_def] \\ RES_TAC \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [term_ok_def,term_sub_def,LENGTH_MAP]
  \\ SIMP_TAC std_ss [EVERY_MEM,MEM_MAP] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ Q.PAT_X_ASSUM `!a.bbb` MATCH_MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,logic_term_size_def]
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `l0` \\ SRW_TAC [] [logic_term_size_def] \\ RES_TAC \\ DECIDE_TAC);

val formula_ok_sub = prove(
  ``!a ss ctxt.
      formula_ok ctxt a /\ EVERY (term_ok ctxt) (MAP SND ss) ==>
      formula_ok ctxt (formula_sub ss a)``,
  Induct \\ FULL_SIMP_TAC std_ss [formula_ok_def,formula_sub_def,term_ok_sub]);

val MAP_FST_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> (MAP FST (ZIP (xs,ys)) = xs)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP]);

val MAP_SND_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> (MAP SND (ZIP (xs,ys)) = ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP]);

val MilawaTrue_IMP_formula_ok = store_thm("MilawaTrue_IMP_formula_ok",
  ``!ctxt x. MilawaTrue ctxt x ==> context_ok ctxt ==> formula_ok ctxt x``,
  HO_MATCH_MP_TAC MilawaTrue_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,
       func_arity_def,LENGTH,EVERY_DEF,primitive_arity_def,
       MilawaAxiom_IMP_formula_ok,LENGTH_MAP]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def]
  \\ TRY (Cases_on `qs_ss` \\ FULL_SIMP_TAC std_ss [formula_ok_def,or_list_def,MAP] \\ NO_TAC)
  \\ FULL_SIMP_TAC std_ss [context_ok_def] \\ RES_TAC);


(* PART 4: Proof of soundness of the inference rules *)

val EvalTerm_Const_Var = prove(
  ``(EvalTerm (a,ctxt) (mConst x) = x) /\
    (EvalTerm (a,ctxt) (mVar v) = a v)``,
  SIMP_TAC std_ss [EvalTerm_def]);

val MOVE_EXISTS = METIS_PROVE []
  ``(?x. P x) /\ Q = ?x. P x /\ Q``

val EvalTerm_Primtives1 = prove(
  ``(EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_NATP) [x]) =
      LISP_NUMBERP (EvalTerm (a,ctxt) x)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_SYMBOLP) [x]) =
      LISP_SYMBOLP (EvalTerm (a,ctxt) x)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_CONSP) [x]) =
      LISP_CONSP (EvalTerm (a,ctxt) x)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_CAR) [x]) =
      CAR (EvalTerm (a,ctxt) x)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_CDR) [x]) =
      CDR (EvalTerm (a,ctxt) x)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_ORDP) [x]) =
      LISP_TEST (ORDP (EvalTerm (a,ctxt) x))) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_NOT) [x]) =
      LISP_TEST ((EvalTerm (a,ctxt) x) = Sym "NIL")) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_RANK) [x]) =
      Val (LSIZE (EvalTerm (a,ctxt) x)))``,
  SIMP_TAC (srw_ss()) [EvalApp_def,EVAL_PRIMITIVE_def,EvalTerm_def]);

val EvalTerm_Primtives2 = prove(
  ``(EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_CONS) [x;y]) =
      LISP_CONS (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_EQUAL) [x;y]) =
      LISP_EQUAL (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_LESS) [x;y]) =
      LISP_LESS (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_SYMBOL_LESS) [x;y]) =
      LISP_SYMBOL_LESS (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_ADD) [x;y]) =
      LISP_ADD (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_SUB) [x;y]) =
      LISP_SUB (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)) /\
    (EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_ORD_LESS) [x;y]) =
      LISP_TEST (ORD_LT (EvalTerm (a,ctxt) x) (EvalTerm (a,ctxt) y)))``,
  SIMP_TAC (srw_ss()) [EvalApp_def,EVAL_PRIMITIVE_def,EvalTerm_def]);

val EvalTerm_IF = prove(
  ``(EvalTerm (a,ctxt) (mApp (mPrimitiveFun logic_IF) [x;y;z]) =
     if EvalTerm (a,ctxt) x = Sym "NIL" then
       EvalTerm (a,ctxt) z else EvalTerm (a,ctxt) y)``,
  SIMP_TAC (srw_ss()) [EvalApp_def,EVAL_PRIMITIVE_def,EvalTerm_def,LISP_IF_def]
  \\ METIS_TAC [isTrue_def]);

val EvalTerm_CLAUSES = LIST_CONJ [EvalTerm_Primtives1,
  EvalTerm_Primtives2,EvalTerm_Const_Var,EvalTerm_IF]

val IF_T = prove(
  ``(((if b then Sym "T" else Sym "NIL") = Sym "T") = b) /\
    (((if b then Sym "NIL" else Sym "T") = Sym "T") = ~b) /\
    (((if b then Sym "NIL" else Sym "T") = Sym "NIL") = b) /\
    (((if b then Sym "T" else Sym "NIL") = Sym "NIL") = ~b) /\
    (((if b then Sym "T" else Sym "NIL") = (if b2 then Sym "T" else Sym "NIL")) = (b = b2))``,
  Cases_on `b` \\ Cases_on `b2` \\ EVAL_TAC);

val axioms_ss = rewrites [MilawaValid_def,formula_ok_def,EvalFormula_def,IF_T,
  term_ok_def,func_arity_def,primitive_arity_def,LENGTH,EVERY_DEF,EvalTerm_CLAUSES,
  DECIDE ``0<n = ~(n=0:num)``]

val NOT_T_NIL = EVAL ``Sym "T" = Sym "NIL"``

val lemmas = [string_lt_nonrefl,string_lt_antisym,string_lt_trans,string_lt_cases]

val MilawaAxiom_IMP_MilawaValid = prove(
  ``!ctxt x. MEM x MILAWA_AXIOMS ==> context_ok ctxt ==> MilawaValid ctxt x``,
  REWRITE_TAC [MILAWA_AXIOMS_def,MEM] \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC \\ METIS_TAC [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ Cases_on `a "Y"` \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ Cases_on `a "Y"` \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ Cases_on `a "Y"` \\ EVAL_TAC \\ METIS_TAC (lemmas))
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ Cases_on `a "C"` \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC \\ EVAL_TAC
         \\ FULL_SIMP_TAC (std_ss++axioms_ss) []
         \\ Cases_on `a "A"` \\ Cases_on `a "B"` \\ Cases_on `a "C"` \\ EVAL_TAC
         \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) []
         \\ REPEAT STRIP_TAC \\ Cases_on `a "X"` \\ EVAL_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) []
         \\ EVAL_TAC \\ SIMP_TAC std_ss [])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ Cases_on `a "X"` \\ EVAL_TAC \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ SIMP_TAC std_ss [Once ORD_LT_def]
         \\ FULL_SIMP_TAC std_ss [LISP_TEST_def,LISP_CONSP_def,LISP_EQUAL_def,LISP_LESS_def]
         \\ Cases_on `isDot (a "X")` \\ FULL_SIMP_TAC std_ss []
         \\ Cases_on `isDot (a "Y")` \\ FULL_SIMP_TAC std_ss []
         \\ Cases_on `CDR (CAR (a "X")) = CDR (CAR (a "Y"))`
         \\ FULL_SIMP_TAC std_ss [NOT_T_NIL]
         \\ Cases_on `CAR (CAR (a "X")) = CAR (CAR (a "Y"))`
         \\ FULL_SIMP_TAC std_ss [NOT_T_NIL])
  THEN1 (FULL_SIMP_TAC (std_ss++axioms_ss) [] \\ REPEAT STRIP_TAC
         \\ SIMP_TAC std_ss [Once ORDP_def]
         \\ FULL_SIMP_TAC std_ss [LISP_TEST_def,LISP_CONSP_def,LISP_EQUAL_def,LISP_LESS_def,LISP_NUMBERP_def]
         \\ Cases_on `isDot (a "X")` \\ FULL_SIMP_TAC std_ss []
         \\ Cases_on `isDot (CAR (a "X"))` \\ FULL_SIMP_TAC std_ss []
         \\ Cases_on `isDot (CAR (a "X"))` \\ FULL_SIMP_TAC std_ss [NOT_T_NIL]
         \\ Cases_on `ORDP (CAR (CAR (a "X")))`
         \\ FULL_SIMP_TAC std_ss [NOT_T_NIL,getVal_def]
         \\ Cases_on `CAR (CAR (a "X")) = Val 0` \\ FULL_SIMP_TAC std_ss [NOT_T_NIL]
         \\ Cases_on `0 < getVal (CDR (CAR (a "X")))` \\ FULL_SIMP_TAC std_ss [NOT_T_NIL]
         \\ Cases_on `ORDP (CDR (a "X"))` \\ FULL_SIMP_TAC std_ss [NOT_T_NIL]
         \\ Cases_on `isDot (CDR (a "X"))` \\ FULL_SIMP_TAC std_ss [NOT_T_NIL]));

val Milawa_SOUNDESS_LEMMA = prove(
  ``!xs. ((2 = LENGTH xs) = ?x1 x2. xs = [x1;x2]) /\
         ((1 = LENGTH xs) = ?x1. xs = [x1])``,
  Cases \\ SIMP_TAC (srw_ss()) [LENGTH,ADD1]
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) [LENGTH,ADD1]
  \\ Cases_on `t'` \\ SIMP_TAC (srw_ss()) [LENGTH,ADD1] \\ DECIDE_TAC)

val NOT_MEM_LOOKUP = prove(
  ``!ss s x. ~(MEM s (MAP FST ss)) ==> (LOOKUP s ss x = x)``,
  Induct \\ SIMP_TAC std_ss [LOOKUP_def] \\ Cases
  \\ ASM_SIMP_TAC std_ss [LOOKUP_def,MAP,MEM]);

val MEM_MAP_FST = prove(
  ``!ss. MEM s (MAP FST ss) ==>
         ?ys t zs. (ss = ys ++ (s,t)::zs) /\ ~(MEM s (MAP FST ys))``,
  Induct \\ SIMP_TAC std_ss [MEM,MAP] \\ STRIP_TAC
  \\ Cases_on `s = FST h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.LIST_EXISTS_TAC [`[]`,`SND h`,`ss`]
    \\ EVAL_TAC \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `h::ys'`
  \\ FULL_SIMP_TAC std_ss [APPEND,MEM,MAP] \\ METIS_TAC []);

val FunVarBindAux_def = Define `
  (FunVarBindAux [] args d = d) /\
  (FunVarBindAux (p::ps) [] d = (p =+ Sym "NIL") (FunVarBindAux ps [] d)) /\
  (FunVarBindAux (p::ps) (a::as) d = (p =+ a) (FunVarBindAux ps as d))`;

val FunVarBindAux_APPEND = prove(
  ``!ys f xs qs d.
      ~(MEM a (MAP FST ys)) ==>
      (FunVarBindAux (MAP FST ys ++ xs) (MAP f ys ++ qs) d a = FunVarBindAux xs qs d a) /\
      (LOOKUP a (ys ++ ts) c = LOOKUP a ts c)``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,MAP,FunVarBindAux_def,
     APPLY_UPDATE_THM,MEM,LOOKUP_def] \\ Cases \\ FULL_SIMP_TAC std_ss [LOOKUP_def]);

val EVERY_TERM_ok_sub = prove(
  ``!xs ctxt ss.
      EVERY (term_ok ctxt) xs /\ EVERY (term_ok ctxt) (MAP SND ss) ==>
      EVERY (term_ok ctxt) (MAP (\a. term_sub ss a) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,MAP] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC term_ok_sub \\ ASM_SIMP_TAC std_ss []);

val MAP_EQ_EQ = prove(
  ``!xs ys f.
      (MAP f xs = ys) = (LENGTH xs = LENGTH ys) /\
                        (!x y. MEM (x,y) (ZIP(xs,ys)) ==> (f x = y))``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC (srw_ss()) [LENGTH,ADD1] \\ METIS_TAC []);

val MEM_logic_term_size_alt = prove(
  ``!xs x. MEM x xs /\ EVERY (term_ok ctxt) xs ==>
           logic_term_size x < logic_term1_size xs /\ term_ok ctxt x``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,logic_term_size_def]
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC \\ RES_TAC \\ DECIDE_TAC);

val MEM_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) /\ MEM (x,y) (ZIP (xs,ys)) ==> MEM x xs``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MEM] \\ METIS_TAC []);

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``;

val IMP_MAP_EQ_MAP = prove(
  ``!xs. (!x. MEM x xs ==> (f x = g x)) ==> (MAP f xs = MAP g xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [MAP,MEM]);

val EvalTerm_sub = prove(
  ``!x a ss.
      EvalTerm (a,ctxt) (term_sub ss x) =
      EvalTerm (FunVarBindAux (MAP FST ss) (MAP (EvalTerm (a,ctxt) o SND) ss) a,ctxt) x``,
  completeInduct_on `logic_term_size x`
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `x`
  THEN1 (SIMP_TAC std_ss [EvalTerm_def,term_sub_def])
  THEN1
    (SIMP_TAC std_ss [EvalTerm_def,term_sub_def]
     \\ REVERSE (Cases_on `MEM s (MAP FST ss)`) THEN1
      (ASM_SIMP_TAC std_ss [NOT_MEM_LOOKUP,EvalTerm_def]
       \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`ss`,`xs`)
       \\ Induct \\ FULL_SIMP_TAC std_ss [MAP,FunVarBindAux_def,MEM]
       \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM])
    \\ IMP_RES_TAC MEM_MAP_FST
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,MAP,FunVarBindAux_APPEND]
    \\ FULL_SIMP_TAC std_ss [FunVarBindAux_def,APPLY_UPDATE_THM,LOOKUP_def])
  THEN1
   (SIMP_TAC std_ss [EvalTerm_def,term_sub_def,LENGTH_MAP]
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ FULL_SIMP_TAC std_ss [MAP_MAP_o,combinTheory.o_DEF]
    \\ MATCH_MP_TAC IMP_MAP_EQ_MAP \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM,logic_term_size_def]
    \\ FULL_SIMP_TAC std_ss [GSYM EVERY_MEM]
    \\ IMP_RES_TAC MEM_IMP_logic_term_size \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [EvalTerm_def,term_sub_def,LET_DEF,term_ok_def]
  \\ FULL_SIMP_TAC std_ss [MAP_MAP_o,combinTheory.o_DEF]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ MATCH_MP_TAC IMP_MAP_EQ_MAP \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM,logic_term_size_def]
  \\ IMP_RES_TAC MEM_IMP_logic_term_size \\ DECIDE_TAC);

val PULL_EXISTS_IMP = METIS_PROVE [] ``((?x. P x) ==> b) = !x. P x ==> b``

val MEM_logic_term_size_alt_alt = prove(
  ``!xs x. MEM x xs ==> logic_term_size x < logic_term1_size xs``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,logic_term_size_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val EvalFormula_sub = prove(
  ``!x a ss.
      EvalFormula (a,ctxt) (formula_sub ss x) =
      EvalFormula (FunVarBindAux (MAP FST ss) (MAP (EvalTerm (a,ctxt) o SND) ss) a,ctxt) x``,
  Induct \\ FULL_SIMP_TAC std_ss [EvalFormula_def,formula_sub_def,
    formula_ok_def,EvalTerm_sub]);

val LENGTH_EQ_3 = prove(
  ``((LENGTH args = 3) = ?x1 x2 x3. args = [x1;x2;x3]) /\
    ((3 = LENGTH args) = ?x1 x2 x3. args = [x1;x2;x3])``,
  Cases_on `args` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH]
  \\ Cases_on `t'` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH] \\ DECIDE_TAC);

val EvalTerm_CHANGE_INST = prove(
  ``!a ctxt body.
      (\(a,ctxt) body. !b.
        (!x. MEM x (free_vars body) ==> (a x = b x)) ==>
        (EvalTerm (a,ctxt) body = EvalTerm (b,ctxt) body)) (a,ctxt) body``,
  HO_MATCH_MP_TAC (fetch "-" "EvalTerm_ind")
  \\ SIMP_TAC std_ss [EvalTerm_def,free_vars_def,MEM]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (SIMP_TAC std_ss [LET_DEF]
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ MATCH_MP_TAC IMP_MAP_EQ_MAP \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ RES_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [MEM_FLAT]
    \\ Q.EXISTS_TAC `free_vars x'` \\ ASM_SIMP_TAC std_ss [MEM_MAP] \\ METIS_TAC [])
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ MATCH_MP_TAC IMP_MAP_EQ_MAP \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT] \\ METIS_TAC [MEM_MAP]) |> SIMP_RULE std_ss [];

val EL_LEMMA = CONJ (EVAL ``EL 0 (x::xs)``) (EVAL ``EL 1 (x::y::xs)``)

val formula_ok_or_not_equal_list = prove(
  ``!ts_list x.
      formula_ok ctxt (or_not_equal_list ts_list x) =
      EVERY (\(t,s). term_ok ctxt t /\ term_ok ctxt s) ts_list /\ formula_ok ctxt x``,
  Induct \\ SIMP_TAC std_ss [or_not_equal_list_def,EVERY_DEF] \\ Cases
  \\ ASM_SIMP_TAC std_ss [or_not_equal_list_def,EVERY_DEF,formula_ok_def] \\ METIS_TAC []);

val EvalFormula_or_not_equal_list = prove(
  ``!ts_list x.
      EvalFormula (a,ctxt) (or_not_equal_list ts_list x) =
      (EVERY (\(t,s). EvalTerm (a,ctxt) t = EvalTerm (a,ctxt) s) ts_list ==>
       EvalFormula (a,ctxt) x)``,
  Induct \\ SIMP_TAC std_ss [or_not_equal_list_def,EVERY_DEF] \\ Cases
  \\ ASM_SIMP_TAC std_ss [or_not_equal_list_def,EVERY_DEF,formula_ok_def,
       EvalFormula_def] \\ METIS_TAC []);

val or_list_EXPAND = prove(
  ``~(xs = []) ==> (or_list (x::xs) = Or x (or_list xs))``,
  Cases_on `xs` \\ SIMP_TAC std_ss [or_list_def] \\ METIS_TAC []);

val EvalFormula_or_list = prove(
  ``!xs. ~(xs = []) /\ EvalFormula (a,ctxt) (or_list xs) ==>
         ?y. MEM y xs /\ EvalFormula (a,ctxt) y``,
  Induct \\ SIMP_TAC (srw_ss()) [or_list_EXPAND] \\ REPEAT STRIP_TAC
  \\ Cases_on `xs` \\ FULL_SIMP_TAC (srw_ss()) [MEM,or_list_def,EvalFormula_def]
  \\ METIS_TAC []);

val EvalFormula_or_list_swap = prove(
  ``EvalFormula (a,ctxt) (or_list (x::y::xs)) =
    EvalFormula (a,ctxt) (or_list (y::x::xs))``,
  Cases_on `xs` \\ SIMP_TAC std_ss [EvalFormula_def,or_list_def] \\ METIS_TAC []);

val IMP_INTRO = METIS_PROVE [] ``~b \/ c = b ==> c``

val EvalFormula_MOVE = prove(
  ``!xs. EvalFormula (a,ctxt) (or_list (x::xs)) =
         EvalFormula (a,ctxt) (or_list (xs ++ [x]))``,
  Induct \\ SIMP_TAC std_ss [APPEND,EvalFormula_def] \\ Cases_on `xs`
  \\ FULL_SIMP_TAC std_ss [APPEND,EvalFormula_def,or_list_def,APPEND]
  \\ METIS_TAC []);

val EvalFormula_or_list_MAP_Not = prove(
  ``!xs x.
      EvalFormula (a,ctxt) (or_list (MAP (\s. Not (formula_sub s x)) xs ++ [x])) =
      (EVERY (\s. EvalFormula (a,ctxt) ((formula_sub s x))) xs ==>
       EvalFormula (a,ctxt) x)``,
  Induct \\ SIMP_TAC std_ss [EVERY_DEF,or_list_def,APPEND,MAP] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [or_list_EXPAND,EvalFormula_def] \\ METIS_TAC []);

val EvalTerm_IGNORE_FunVarBind = prove(
  ``LIST_TO_SET (free_vars body) SUBSET LIST_TO_SET params ==>
    (EvalTerm (FunVarBind params (MAP a params),ctxt) body =
     EvalTerm (a,ctxt) body)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC EvalTerm_CHANGE_INST \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `MEM x params` by FULL_SIMP_TAC std_ss [SUBSET_DEF]
  \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`x`,`x`) \\ Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`params`,`params`)
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct \\ SIMP_TAC std_ss [MEM,ALL_DISTINCT,MAP,FunVarBind_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `x = h` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]);

val LISP_TEST = prove(``!x. (LISP_TEST x = Sym "T") = x``,Cases \\ EVAL_TAC);

val MEM_formula_ok = prove(
  ``!z x. MEM x z /\ formula_ok ctxt (or_list (x1::x2::MAP f z)) ==>
          formula_ok ctxt (f x)``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,or_list_def,MAP] \\ Cases_on `z`
  \\ FULL_SIMP_TAC std_ss [MEM,or_list_def,MAP,formula_ok_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val FunVarBind_EQ_FunVarBindAux = prove(
  ``!xs ys x. MEM x xs /\ (LENGTH xs = LENGTH ys) ==>
              (FunVarBindAux xs ys a x = FunVarBind xs ys x)``,
  Induct \\ Cases_on `ys`
  \\ SIMP_TAC std_ss [FunVarBindAux_def,FunVarBind_def,MEM,LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC []);

val LISP_TEST_THM = prove(
  ``!b. ((LISP_TEST b = Sym "T") = b) /\ ((LISP_TEST b = Sym "NIL") = ~b) /\
        (isTrue (LISP_TEST b) = b)``,
  Cases \\ EVAL_TAC);

val IMP_MAP_EQ_MAP = prove(
  ``!xs. (!x. MEM x xs ==> (f x = g x)) ==> (MAP f xs = MAP g xs)``,
  Induct\\ SRW_TAC [] []);

val EvalTerm_SWAP_INST = prove(
  ``!a ctxt x b.
      (\(a,ctxt) x.
        (!v. MEM v (free_vars x) ==> (a v = b v)) /\ term_ok ctxt x ==>
        (EvalTerm (a,ctxt) x = EvalTerm (b,ctxt) x)) (a,ctxt) x``,
  HO_MATCH_MP_TAC (fetch "-" "EvalTerm_ind")
  \\ FULL_SIMP_TAC std_ss [EvalTerm_def,free_vars_def,MEM,LET_DEF,term_ok_def]
  \\ REPEAT STRIP_TAC THEN1
   (CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP,PULL_EXISTS_IMP]
    \\ sg `MAP (EvalTerm (a,ctxt)) args = MAP (EvalTerm (b,ctxt)) args`
    \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_MAP_EQ_MAP
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ METIS_TAC [])
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP,PULL_EXISTS_IMP]
  \\ `MAP (EvalTerm (a,ctxt)) ys = MAP (EvalTerm (b,ctxt)) ys` by
   (FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_MAP_EQ_MAP
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [];

val FunVarBind_MAP_EQ = prove(
  ``!params v a.
      ALL_DISTINCT params /\ MEM v params ==>
      (FunVarBind params (MAP a params) v = a v)``,
  Induct \\ FULL_SIMP_TAC std_ss [FunVarBind_def,MEM,ALL_DISTINCT,MAP]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [APPLY_UPDATE_THM]);

val Milawa_SOUNDESS = store_thm("Milawa_SOUNDESS",
  ``!ctxt x. MilawaTrue ctxt x ==> context_ok ctxt ==>
             MilawaValid ctxt x``,
  HO_MATCH_MP_TAC MilawaTrue_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def]
  THEN1 (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def]
         \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def]
         \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def]
         \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def]
         \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def]
         \\ METIS_TAC [])
  THEN1 (* function equality *)
   (REPEAT (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`x`,`x`) \\ SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_or_not_equal_list]
    \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EvalFormula_or_not_equal_list] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EvalFormula_def,LENGTH_MAP]
    \\ SIMP_TAC std_ss [EvalTerm_def,combinTheory.o_DEF,MAP_MAP_o]
    \\ `MAP (\x. EvalTerm (a,ctxt) (FST x)) ts_list =
        MAP (\x. EvalTerm (a,ctxt) (SND x)) ts_list` by
     (MATCH_MP_TAC IMP_MAP_EQ_MAP \\ Cases
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [LENGTH_MAP] \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss [LENGTH_EQ_3,rich_listTheory.EL_CONS,MAP,EL,HD,CONS_11]
    \\ FULL_SIMP_TAC std_ss [LENGTH_EQ_3,rich_listTheory.EL_CONS,MAP,EL,HD,CONS_11]
    \\ METIS_TAC [])
  THEN1 (* instantiation *)
   (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def,
      EvalFormula_sub])
  THEN1 (* beta reduction *)
   (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,EvalFormula_def,
      EvalFormula_sub,term_ok_def,EvalTerm_def,LET_DEF,EvalTerm_sub]
    \\ FULL_SIMP_TAC std_ss [MAP_SND_ZIP,MAP_FST_ZIP,MAP_o]
    \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC EvalTerm_CHANGE_INST
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ `(MAP (\a''. EvalTerm (a',ctxt) a'') ys) =
        (MAP (EvalTerm (a',ctxt)) ys)` by METIS_TAC []
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (GSYM FunVarBind_EQ_FunVarBindAux)
    \\ ASM_SIMP_TAC std_ss [LENGTH_MAP])
  THEN1 (* base evaluation *)
   (Cases_on `p` \\ FULL_SIMP_TAC std_ss [primitive_arity_def]
    \\ FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,term_ok_def,
         func_arity_def,primitive_arity_def,LENGTH_MAP,EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [Milawa_SOUNDESS_LEMMA,MAP,MEM,LENGTH_EQ_3]
    \\ FULL_SIMP_TAC (srw_ss()) [EvalFormula_def,EvalTerm_def,EvalApp_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def] \\ EVAL_TAC)
  THEN1 (* axioms *) (FULL_SIMP_TAC std_ss [MilawaAxiom_IMP_MilawaValid])
  THEN1 (* user-defined syntactic function *)
   (ASM_SIMP_TAC (srw_ss()) [MilawaValid_def,formula_ok_def,term_ok_def,EVERY_MEM,
      EvalFormula_def,EvalTerm_def,EvalApp_def,func_arity_def,LET_DEF]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [MEM_MAP] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [term_ok_def]
      \\ FULL_SIMP_TAC std_ss [context_ok_def] \\ RES_TAC)
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ FULL_SIMP_TAC std_ss [MAP_MAP_o,combinTheory.o_DEF,EvalTerm_def]
    \\ FULL_SIMP_TAC std_ss [context_ok_def]
    \\ RES_TAC \\ POP_ASSUM MP_TAC
    \\ REPEAT (Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC))
    \\ METIS_TAC [])
  THEN1 (* user-defined witness function *)
   (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,term_ok_def,
      LENGTH,LENGTH_MAP,EVERY_DEF] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def,context_ok_def] \\ RES_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [EvalFormula_def,EvalTerm_def,MAP,EvalApp_def,LET_DEF]
    \\ REPEAT STRIP_TAC \\ Cases_on `EvalTerm (a,ctxt) exp = Sym "NIL"`
    \\ ASM_SIMP_TAC std_ss [MAP_MAP_o,combinTheory.o_DEF,EvalTerm_def]
    \\ Q.PAT_X_ASSUM `context_ok ctxt` (fn th => ASSUME_TAC th THEN MP_TAC th)
    \\ SIMP_TAC std_ss [context_ok_def] \\ STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_X_ASSUM `!xx yy zz. bbb` (K ALL_TAC))
    \\ `?v. isTrue
      (EvalTerm (FunVarBind (var_name::params) (v::MAP a params),ctxt) exp)` by
     (Q.EXISTS_TAC `a var_name`
      \\ FULL_SIMP_TAC std_ss [LIST_TO_SET_THM,
        EvalTerm_IGNORE_FunVarBind
        |> Q.INST [`params`|->`v::vs`]
        |> SIMP_RULE std_ss [MAP,LIST_TO_SET_THM,ALL_DISTINCT],isTrue_def])
    \\ POP_ASSUM MP_TAC
    \\ POP_ASSUM (fn th => MP_TAC (Q.SPECL [`v`,`MAP a (params:string list)`] (ONCE_REWRITE_RULE [FUN_EQ_THM] th)))
    \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ `(\x. a x) = a` by METIS_TAC [] \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC [isTrue_def])
  THEN1 (* induction *)
   (FULL_SIMP_TAC std_ss [MilawaValid_def,formula_ok_def,term_ok_def,
      EVERY_DEF,func_arity_def,primitive_arity_def,LENGTH,GSYM CONJ_ASSOC]
    \\ Q.PAT_X_ASSUM `term_ok ctxt m` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    THEN1 (Cases_on `MAP FST qs_ss` \\ FULL_SIMP_TAC std_ss [or_list_def,formula_ok_def])
    \\ FULL_SIMP_TAC (srw_ss()) [EvalFormula_def,EvalTerm_def,
         EvalApp_def,EVAL_PRIMITIVE_def,LISP_TEST_THM]
    \\ `?y. EvalTerm (a,ctxt) m = y` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`y`,`y`)
    \\ HO_MATCH_MP_TAC (MATCH_MP relationTheory.WF_INDUCTION_THM WF_ORD_LESS)
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `qs_ss = []` THEN1 FULL_SIMP_TAC std_ss [or_list_def,MAP]
    \\ `~(MAP FST qs_ss = [])` by (Cases_on `qs_ss` \\ FULL_SIMP_TAC (srw_ss()) [MAP])
    \\ FULL_SIMP_TAC std_ss [or_list_EXPAND,EvalFormula_def]
    \\ REVERSE (Cases_on `EvalFormula (a,ctxt) (or_list (MAP FST qs_ss))`)
    THEN1 METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [formula_ok_def]
    \\ FULL_SIMP_TAC std_ss [EvalTerm_CLAUSES]
    \\ `?y z. MEM (y,z) qs_ss /\ EvalFormula (a,ctxt) y` by
     (`?y. MEM y (MAP FST qs_ss) /\ EvalFormula (a,ctxt) y` by METIS_TAC [EvalFormula_or_list]
      \\ FULL_SIMP_TAC std_ss [MEM_MAP] \\ Cases_on `y'`
      \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
    \\ Q.PAT_X_ASSUM `!q ss. bbb ==> bbbb` IMP_RES_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPEC `a`)
    \\ ONCE_REWRITE_TAC [EvalFormula_or_list_swap]
    \\ SIMP_TAC std_ss [or_list_def,EvalFormula_def,IMP_INTRO]
    \\ SIMP_TAC std_ss [EvalFormula_MOVE]
    \\ SIMP_TAC std_ss [EvalFormula_or_list_MAP_Not,AND_IMP_INTRO]
    \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!q ss s. bbb` (MP_TAC o Q.SPECL [`y`,`z`,`s`])
    \\ ASM_SIMP_TAC std_ss [IMP_INTRO] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPEC `a`) \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EvalTerm_sub,EvalFormula_sub]
    \\ STRIP_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [ORD_LESS_def]));

(* We now prove a corollary which provides an intuitive
   characterisation of soundness, namely that it is not possible to
   prove that NIL equals T. *)

val Milawa_NOT_NIL_EQUAL_T = store_thm("Milawa_NOT_NIL_EQUAL_T",
  ``!ctxt x.
       context_ok ctxt ==>
       ~(MilawaTrue ctxt (Equal (mConst (Sym "NIL"))
                                (mConst (Sym "T"))))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC Milawa_SOUNDESS
  \\ POP_ASSUM MP_TAC \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);


(* PART 5: Soundness of context extension -- adding a new definition *)

val MEM_logic_term_size_alt_LESS = prove(
  ``!xs x. MEM x xs ==> logic_term_size x < logic_term1_size xs``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,logic_term_size_def]
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC \\ RES_TAC \\ DECIDE_TAC);

val term_ok_FUPDATE = prove(
  ``!x. term_ok ctxt x /\ ~(fname IN FDOM ctxt) ==>
        term_ok (ctxt |+ (fname,params,f)) x``,
  completeInduct_on `logic_term_size x`
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [term_ok_def] THEN1
   (Cases_on `l0` \\ FULL_SIMP_TAC std_ss [func_arity_def]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC THEN1
     (Q.PAT_X_ASSUM `!x. b ==> b2 ==> b3` (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO])
      \\ FULL_SIMP_TAC std_ss [logic_term_size_def]
      \\ IMP_RES_TAC MEM_logic_term_size_alt_LESS \\ DECIDE_TAC)
    \\ `~(fname = s)` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM]
    \\ Q.PAT_X_ASSUM `!x. b ==> b2 ==> b3` (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [logic_term_size_def]
    \\ IMP_RES_TAC MEM_logic_term_size_alt_LESS \\ DECIDE_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. b ==> b2 ==> b3` (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [logic_term_size_def]
    \\ IMP_RES_TAC MEM_logic_term_size_alt_LESS \\ DECIDE_TAC));

val formula_ok_FUPDATE = prove(
  ``!x. formula_ok ctxt x /\ ~(fname IN FDOM ctxt) ==>
        formula_ok (ctxt |+ (fname,params,f)) x``,
  Induct \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_FUPDATE]);

val EvalTerm_FUPDATE = prove(
  ``!a ctxt exp.
      (\(a,ctxt) exp.
         (term_ok ctxt exp /\ ~(fname IN FDOM ctxt) ==>
         (EvalTerm (a,ctxt) exp = EvalTerm (a,ctxt |+ (fname,params,body,sem)) exp)))
           (a,ctxt) exp``,
  HO_MATCH_MP_TAC (fetch "-" "EvalTerm_ind") \\ SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [EvalTerm_def] \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (sg `MAP (\a''. EvalTerm (a,ctxt |+ (fname,params,body,sem)) a'') ys =
     MAP (\a''. EvalTerm (a,ctxt) a'') ys`
    \\ FULL_SIMP_TAC std_ss [LET_DEF,term_ok_def]
    \\ MATCH_MP_TAC IMP_MAP_EQ_MAP \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [term_ok_def] \\ METIS_TAC [EVERY_MEM])
  \\ `MAP (\a''. EvalTerm (a,ctxt |+ (fname,params,body,sem)) a'') args =
      MAP (\a''. EvalTerm (a,ctxt) a'') args` by
      (FULL_SIMP_TAC std_ss [LET_DEF,term_ok_def]
       \\ MATCH_MP_TAC (GEN_ALL IMP_MAP_EQ_MAP) \\ REPEAT STRIP_TAC
       \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM,markerTheory.Abbrev_def])
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `f`
  \\ FULL_SIMP_TAC std_ss [EvalApp_def,LET_DEF,FAPPLY_FUPDATE_THM,
       term_ok_def,func_arity_def] \\ METIS_TAC []) |> SIMP_RULE std_ss [];

val _ = save_thm("EvalTerm_FUPDATE",EvalTerm_FUPDATE);

val EvalFormula_FUPDATE = prove(
  ``!exp a ctxt.
      (formula_ok ctxt exp /\ ~(fname IN FDOM ctxt) ==>
      (EvalFormula (a,ctxt) exp = EvalFormula (a,ctxt |+ (fname,params,body,sem)) exp))``,
  Induct \\ ASM_SIMP_TAC std_ss [EvalFormula_def,formula_ok_def,GSYM EvalTerm_FUPDATE]);

(* adding a new definition does not break the derivations *)

val term_ok_IGNORE_SEM = store_thm("term_ok_IGNORE_SEM",
  ``!ctxt exp.
      term_ok (ctxt |+ (fname,params,body,sem)) exp =
      term_ok (ctxt |+ (fname,params,body,ARB)) exp``,
  HO_MATCH_MP_TAC (fetch "-" "term_ok_ind") \\ SIMP_TAC std_ss [term_ok_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
  \\ Cases_on `fc` \\ FULL_SIMP_TAC std_ss [func_arity_def,FDOM_FUPDATE]
  \\ FULL_SIMP_TAC std_ss [IN_INSERT,FAPPLY_FUPDATE_THM]
  \\ Cases_on `s = fname` \\ FULL_SIMP_TAC std_ss []);

val formula_ok_IGNORE_SEM = prove(
  ``!exp ctxt.
      formula_ok (ctxt |+ (fname,params,body,sem)) exp =
      formula_ok (ctxt |+ (fname,params,body,ARB)) exp``,
  Induct \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_IGNORE_SEM]);

val EvalTerm_IGNORE_BODY = store_thm("EvalTerm_IGNORE_BODY",
  ``!(ctxt:context_type) x a.
      (term_ok (ctxt |+ (name,params,body,sem)) x =
       term_ok (ctxt |+ (name,params,ARB,sem)) x) /\
      (EvalTerm (a,ctxt |+ (name,params,body,sem)) x =
       EvalTerm (a,ctxt |+ (name,params,ARB,sem)) x)``,
  HO_MATCH_MP_TAC (fetch "-" "term_ok_ind")
  \\ FULL_SIMP_TAC std_ss [EvalTerm_def,LET_DEF,term_ok_def]
  \\ REPEAT STRIP_TAC THEN1
   (Cases_on `fc` \\ FULL_SIMP_TAC std_ss [func_arity_def,LET_DEF,FAPPLY_FUPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ SRW_TAC [] [])
  THEN1
   (CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ `MAP (EvalTerm (a,ctxt |+ (name,params,body,sem))) vs =
        MAP (EvalTerm (a,ctxt |+ (name,params,ARB,sem))) vs` by (MATCH_MP_TAC IMP_MAP_EQ_MAP \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `fc` \\ FULL_SIMP_TAC std_ss [EvalApp_def,LET_DEF,FAPPLY_FUPDATE_THM]
    \\ Cases_on `s = name` \\ FULL_SIMP_TAC std_ss [])
  THEN1 (FULL_SIMP_TAC std_ss [EVERY_MEM])
  THEN1
   (CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ `MAP (EvalTerm (a,ctxt |+ (name,params,body,sem))) zs =
        MAP (EvalTerm (a,ctxt |+ (name,params,ARB,sem))) zs` by (MATCH_MP_TAC IMP_MAP_EQ_MAP \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [EvalApp_def,LET_DEF,FAPPLY_FUPDATE_THM]));

val EvalFormula_IGNORE_BODY = prove(
  ``!(ctxt:context_type) x a.
      (formula_ok (ctxt |+ (name,params,body,sem)) x =
       formula_ok (ctxt |+ (name,params,ARB,sem)) x) /\
      (EvalFormula (a,ctxt |+ (name,params,body,sem)) x =
       EvalFormula (a,ctxt |+ (name,params,ARB,sem)) x)``,
  STRIP_TAC \\ Induct
  \\ FULL_SIMP_TAC std_ss [EvalFormula_def,EvalTerm_IGNORE_BODY,formula_ok_def]);

fun TAC n =
   (SIMP_TAC std_ss [Once MilawaTrue_cases]
    \\ NTAC n DISJ2_TAC \\ TRY DISJ1_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ METIS_TAC [formula_ok_FUPDATE,term_ok_FUPDATE,EVERY_MEM,pairTheory.PAIR,
                  formula_ok_IGNORE_SEM,term_ok_IGNORE_SEM,EvalFormula_IGNORE_BODY,
                  fetch "-" "func_body_distinct",pairTheory.PAIR_EQ])

val MilawaTrue_new_definition = store_thm("MilawaTrue_new_definition",
  ``!ctxt x. MilawaTrue ctxt x ==> ~(name IN FDOM ctxt) ==>
             MilawaTrue (ctxt |+ (name,params,body,sem)) x``,
  HO_MATCH_MP_TAC MilawaTrue_ind \\ REPEAT STRIP_TAC
  THEN1 TAC 0 THEN1 TAC 1 THEN1 TAC 2 THEN1 TAC 3 THEN1 TAC 4 THEN1 TAC 5
  THEN1 TAC 6 THEN1 TAC 7 THEN1 TAC 8 THEN1 TAC 9 THEN1 TAC 10 THEN1 TAC 11
  \\ SIMP_TAC std_ss [Once MilawaTrue_cases]
  \\ NTAC 12 DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`qs_ss`,`m`]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC);

val MilawaTrue_IGNORE_SEM_LEMMA = prove(
  ``!ctxt' x.
      MilawaTrue ctxt' x ==> (ctxt' = (ctxt |+ (name,params,NO_FUN,s1))) ==>
      MilawaTrue (ctxt |+ (name,params,y,s2)) x``,
  HO_MATCH_MP_TAC MilawaTrue_ind \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  THEN1 TAC 0 THEN1 TAC 1 THEN1 TAC 2 THEN1 TAC 3 THEN1 TAC 4 THEN1 TAC 5
  THEN1 TAC 6 THEN1 TAC 7 THEN1 TAC 8 THEN1 TAC 9 THEN1 TAC 10 THEN1 TAC 11
  \\ SIMP_TAC std_ss [Once MilawaTrue_cases]
  \\ NTAC 12 DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`qs_ss`,`m`]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC)
  |> SIMP_RULE std_ss [];

val MilawaTrue_IGNORE_SEM = store_thm("MilawaTrue_IGNORE_SEM",
  ``MilawaTrue (ctxt |+ (name,params,NO_FUN,sem)) =
    MilawaTrue (ctxt |+ (name,params,NO_FUN,ARB))``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC [MilawaTrue_IGNORE_SEM_LEMMA]);

val MilawaTrue_REPLACE_NO_FUN = store_thm("MilawaTrue_REPLACE_NO_FUN",
  ``MilawaTrue (ctxt |+ (name,params,NO_FUN,sem)) x ==>
    MilawaTrue (ctxt |+ (name,params,b,sem)) x``,
  METIS_TAC [MilawaTrue_IGNORE_SEM_LEMMA]);


(* adding a new None definition does not break the context *)

val context_ok_None = store_thm("context_ok_None",
  ``!ctxt name params sem.
      context_ok ctxt /\ ~(name IN FDOM ctxt) ==>
      context_ok (ctxt |+ (name,params,NO_FUN,sem))``,
  FULL_SIMP_TAC (srw_ss()) [context_ok_def,FAPPLY_FUPDATE_THM,FDOM_FUPDATE]
  \\ NTAC 7 STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_IMP]
  \\ Cases_on `fname = name` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC (EvalTerm_FUPDATE |> GSYM |> GEN_ALL) \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [fetch "-" "func_body_distinct",pairTheory.PAIR_EQ,
                EvalTerm_FUPDATE,term_ok_FUPDATE]);

(* definition of Milawa's termination condition generator *)

val callmap_sub_def = Define `
  callmap_sub ss zs =
    MAP (\(xs,ys). (MAP (term_sub ss) xs, MAP (term_sub ss) ys)) zs`;

val MEM_logic_term_size = prove(
  ``!xs x. MEM x xs ==> logic_term_size x < logic_term1_size xs``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,logic_term_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

val callmap_def = tDefine "callmap" `
  (callmap name (mConst c) = []) /\
  (callmap name (mVar v) = []) /\
  (callmap (name:string) (mApp f xs) =
     if f = mPrimitiveFun logic_IF then
       (if LENGTH xs < 3 then [] else
          callmap name (EL 0 xs) ++
          MAP (\(x,y). (x,(EL 0 xs)::y)) (callmap name (EL 1 xs)) ++
          MAP (\(x,y). (x,(mApp (mPrimitiveFun logic_NOT) [EL 0 xs])::y)) (callmap name (EL 2 xs)))
     else if f = mFun name then
       (xs,[]) :: FLAT (MAP (callmap name) xs)
     else
       FLAT (MAP (callmap name) xs)) /\
  (callmap name (mLamApp vs x xs) =
     FLAT (MAP (callmap name) xs) ++
     callmap_sub (ZIP (vs,xs)) (callmap name x))`
 (WF_REL_TAC `measure (logic_term_size o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_logic_term_size
  \\ REPEAT DECIDE_TAC
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ SRW_TAC [] [logic_term_size_def] \\ DECIDE_TAC)

val progress_obligation_def = Define `
  progress_obligation t formals (actuals,rulers) =
    or_list (Equal (mApp (mPrimitiveFun logic_ORD_LESS) [term_sub (ZIP (formals,actuals)) t;t])
                            (mConst (Sym "T"))::
             MAP (\r. Equal r (mConst (Sym "NIL"))) rulers)`;

val termination_obligations_def = Define `
  termination_obligations name body formals m (* m is the measure *) =
    if (callmap name body = []) then [] else
      ((Equal (mApp (mPrimitiveFun logic_ORDP) [m]) (mConst (Sym "T")))::
        (MAP (progress_obligation m formals) (callmap name body)))`;

val no_rec_call_def = Define `
  no_rec_call name exp = (callmap name exp = [])`;

val is_tailrec_def = tDefine "is_tailrec" `
  (is_tailrec name (mConst c) = T) /\
  (is_tailrec name (mVar v) = T) /\
  (is_tailrec name (mApp f xs) =
     if (f = mPrimitiveFun logic_IF) /\ (3 <= LENGTH xs) then
       no_rec_call name (EL 0 xs) /\
       is_tailrec name (EL 1 xs) /\
       is_tailrec name (EL 2 xs)
     else
       EVERY (no_rec_call name) xs) /\
  (is_tailrec name (mLamApp vs x xs) =
     EVERY (no_rec_call name) xs /\ is_tailrec name x)`
 (WF_REL_TAC `measure (logic_term_size o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_logic_term_size
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ TRY (Cases_on `t`) \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ TRY (Cases_on `t'`) \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ EVAL_TAC \\ DECIDE_TAC);

(* definition of the condition a new definition must satisfy *)

val definition_ok_def = Define `
  (definition_ok (name,params,BODY_FUN body,ctxt) =
    term_ok (ctxt |+ (name,params,BODY_FUN body,ARB)) body /\
    ~(name IN FDOM ctxt) /\ ALL_DISTINCT params /\
    LIST_TO_SET (free_vars body) SUBSET LIST_TO_SET params /\
    ?m. EVERY (MilawaTrue (ctxt |+ (name,params,NO_FUN,ARB)))
          (termination_obligations name body params m)) /\
  (definition_ok (name,params,WITNESS_FUN exp var,ctxt) =
    term_ok ctxt exp /\ ~(name IN FDOM ctxt) /\ ALL_DISTINCT (var::params) /\
    LIST_TO_SET (free_vars exp) SUBSET LIST_TO_SET (var::params)) /\
  (definition_ok (name,params,NO_FUN,ctxt) =
    ~(name IN FDOM ctxt) /\ ALL_DISTINCT params)`;

(* We now define a big-step operational semantics used for term
   evaluation. This evaluation relation is able to talk about
   termination of a function, assuming all other functions
   terminate. *)

val (M_ev_rules,M_ev_ind,M_ev_cases) = Hol_reln `
 (!s a ctxt.
    M_ev name (mConst s,a,ctxt) s)
  /\
  (!x a ctxt.
    M_ev name (mVar x,a,ctxt) (a x))
  /\
  (!e1 e2 e3 s1 s a ctxt.
    M_ev name (e1,a,ctxt) s1 /\ ~isTrue s1 /\
    M_ev name (e3,a,ctxt) s
    ==>
    M_ev name (mApp (mPrimitiveFun logic_IF) [e1;e2;e3],a,ctxt) s)
  /\
  (!e1 e2 e3 s1 s a ctxt.
    M_ev name (e1,a,ctxt) s1 /\ isTrue s1 /\
    M_ev name (e2,a,ctxt) s
    ==>
    M_ev name (mApp (mPrimitiveFun logic_IF) [e1;e2;e3],a,ctxt) s)
  /\
  (!e xs ys ctxt a sl x.
    M_evl name (ys,a,ctxt) sl /\ (LENGTH xs = LENGTH ys) /\
    M_ev name (e,FunVarBind xs sl,ctxt) x
    ==>
    M_ev name (mLamApp xs e ys,a,ctxt) x)
  /\
  (!el args a fc ctxt x.
    M_evl name (el,a,ctxt) args /\ M_ap name (fc,args,ctxt) x /\
    ~(fc = mPrimitiveFun logic_IF)
    ==>
    M_ev name (mApp fc el,a,ctxt) x)
  /\
  (!p args ctxt.
    (primitive_arity p = LENGTH args)
    ==>
    M_ap name (mPrimitiveFun p,args,ctxt) (EVAL_PRIMITIVE p args))
  /\
  (!args fc ctxt body params sem.
    ~(fc = name) /\ fc IN FDOM ctxt /\ (ctxt ' fc = (params,body,sem)) /\
    (LENGTH params = LENGTH args)
    ==>
    M_ap name (mFun fc,args,ctxt) (sem args))
  /\
  (!args ctxt params exp x sem.
    (ctxt ' name = (params,BODY_FUN exp,sem)) /\ name IN FDOM ctxt /\
    (LENGTH params = LENGTH args) /\
    M_ev name (exp,FunVarBind params args,ctxt) x
    ==>
    M_ap name (mFun name,args,ctxt) x)
  /\
  (!a ctxt.
    M_evl name ([],a,ctxt) [])
  /\
  (!e el s sl a ctxt.
    M_ev name (e,a,ctxt) s /\ M_evl name (el,a,ctxt) sl
    ==>
    M_evl name (e::el,a,ctxt) (s::sl))`

val M_ev_DETERMINISTIC = store_thm("M_ev_DETERMINISTIC",
  ``(!x y. M_ev n x y  ==> !z. M_ev n x z  ==> (y = z)) /\
    (!x y. M_ap n x y  ==> !z. M_ap n x z  ==> (y = z)) /\
    (!x y. M_evl n x y ==> !z. M_evl n x z ==> (y = z))``,
  HO_MATCH_MP_TAC M_ev_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [M_ev_cases] \\ SRW_TAC [] [] \\ RES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []) |> SIMP_RULE std_ss [PULL_FORALL_IMP];

val Eval_M_ap_def = Define `Eval_M_ap n x = @y. M_ap n x y`;
val Eval_M_ev_def = Define `Eval_M_ev n x = @y. M_ev n x y`;

val EvalFun_def = Define `
  EvalFun name ctxt args = Eval_M_ap name (mFun name, args, ctxt)`;

val M_ev_EQ_LEMMA = prove(
  ``(!x y. M_ev n x y  ==>
           !body a1 ctxt a2.
              ((body,a2,ctxt) = x) ==>
              (!v. MEM v (free_vars body) ==> (a1 v = a2 v)) ==>
              M_ev n (body,a1,ctxt) y) /\
    (!x y. M_ap n x y  ==> M_ap n x y) /\
    (!x y. M_evl n x y ==>
           !body a1 ctxt a2.
              ((body,a2,ctxt) = x) ==>
              (!v. MEM v (FLAT (MAP free_vars body)) ==> (a1 v = a2 v)) ==>
              M_evl n (body,a1,ctxt) y)``,
  HO_MATCH_MP_TAC M_ev_ind \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ (FULL_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [M_ev_cases]
      \\ FULL_SIMP_TAC (srw_ss()) [free_vars_def,MEM]
      \\ POP_ASSUM MP_TAC \\ CONV_TAC (DEPTH_CONV ETA_CONV)
      \\ REPEAT STRIP_TAC \\ RES_TAC \\ TRY (Q.EXISTS_TAC `y`)
      \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []))
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO];

val M_ev_EQ = prove(
  ``(!v. MEM v (free_vars body) ==> (a1 v = a2 v)) ==>
    (M_ev f (body,a1,ctxt) y = M_ev f (body,a2,ctxt) y)``,
  METIS_TAC [M_ev_EQ_LEMMA]);

val M_ap_EQ_SEM_LEMMA = prove(
  ``(!x y. M_ev n x y ==>
           !body a1 ctxt.
              ((body,a1,ctxt) = x) ==>
              M_ev n (body,a1,ctxt |+ (n,FST (ctxt ' n), FST (SND (ctxt ' n)), zzz)) y) /\
    (!x y. M_ap n x y ==>
           !name args ctxt.
              ((name,args,ctxt) = x) ==>
              M_ap n (name,args,ctxt |+ (n,FST (ctxt ' n), FST (SND (ctxt ' n)), zzz)) y) /\
    (!x y. M_evl n x y ==>
           !body a1 ctxt.
              ((body,a1,ctxt) = x) ==>
              M_evl n (body,a1,ctxt |+ (n,FST (ctxt ' n), FST (SND (ctxt ' n)), zzz)) y)``,
  HO_MATCH_MP_TAC M_ev_ind \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [M_ev_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [free_vars_def,MEM,FAPPLY_FUPDATE_THM]
  \\ TRY (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [])
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO];

val M_ap_EQ_SEM = prove(
  ``(M_ap f (name,args,(ctxt |+ (f,params,BODY_FUN body,sem1))) y =
     M_ap f (name,args,(ctxt |+ (f,params,BODY_FUN body,sem2))) y)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (M_ap_EQ_SEM_LEMMA |> CONJUNCTS |> el 2)
  \\ FULL_SIMP_TAC (srw_ss()) []);

val funs_def = tDefine "funs" `
  (funs (mConst c) = []) /\
  (funs (mVar v) = []) /\
  (funs (mApp (mPrimitiveFun p) xs) = FLAT (MAP funs xs)) /\
  (funs (mApp (mFun n) xs) = n :: FLAT (MAP funs xs)) /\
  (funs (mLamApp vs x xs) = funs x ++ FLAT (MAP funs xs))`
 (WF_REL_TAC `measure logic_term_size`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_logic_term_size_alt_LESS \\ DECIDE_TAC)
 |> CONV_RULE (DEPTH_CONV ETA_CONV);

val M_ap_EQ_CTXT_THM = prove(
  ``(ctxt ' n = ctxt2 ' n) /\ n IN FDOM ctxt /\ n IN FDOM ctxt2 /\
    (!params body sem.
        (ctxt ' n = (params,BODY_FUN body,sem)) /\ n IN FDOM ctxt ==>
        !m. MEM m (funs body) ==>
            m IN FDOM ctxt /\ m IN FDOM ctxt2 /\ (ctxt ' m = ctxt2 ' m)) ==>
    (!x y. M_ev n x y ==>
           !body a1.
              ((body,a1,ctxt) = x) ==>
              (!m. MEM m (funs body) ==>
                   m IN FDOM ctxt /\ m IN FDOM ctxt2 /\ (ctxt ' m = ctxt2 ' m)) ==>
              M_ev n (body,a1,ctxt2) y) /\
    (!x y. M_ap n x y ==>
           !name args.
              ((name,args,ctxt) = x) ==>
              (!m. (name = mFun m) ==>
                   m IN FDOM ctxt /\ m IN FDOM ctxt2 /\ (ctxt ' m = ctxt2 ' m)) ==>
              M_ap n (name,args,ctxt2) y) /\
    (!x y. M_evl n x y ==>
           !body a1.
              ((body,a1,ctxt) = x) ==>
              (!m. MEM m (FLAT (MAP funs body)) ==>
                   m IN FDOM ctxt /\ m IN FDOM ctxt2 /\ (ctxt ' m = ctxt2 ' m)) ==>
              M_evl n (body,a1,ctxt2) y)``,
  STRIP_TAC
  \\ HO_MATCH_MP_TAC M_ev_ind \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [M_ev_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [free_vars_def,MEM,FAPPLY_FUPDATE_THM,funs_def]
  \\ TRY (Cases_on `fc:logic_func`)
  \\ FULL_SIMP_TAC (srw_ss()) [free_vars_def,MEM,FAPPLY_FUPDATE_THM,funs_def]
  \\ METIS_TAC []);

val M_ev_EQ_CTXT_LEMMA = save_thm("M_ev_EQ_CTXT_LEMMA",M_ap_EQ_CTXT_THM
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO]
  |> UNDISCH_ALL |> CONJUNCTS |> el 1 |> SPEC_ALL |> DISCH_ALL
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO]);

val M_ap_EQ_CTXT_LEMMA = M_ap_EQ_CTXT_THM
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO]
  |> UNDISCH_ALL |> CONJUNCTS |> el 2 |> SPEC_ALL |> DISCH_ALL
  |> SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO];

val GEN_LIST_K_SUC = prove(
  ``!n a. GENLIST (K a) (SUC n) = a::GENLIST (K a) n``,
  Induct THEN1 ASM_SIMP_TAC std_ss [GENLIST,SNOC]
  \\ SIMP_TAC std_ss [Once GENLIST]
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
  \\ SIMP_TAC std_ss [GENLIST] \\ SIMP_TAC std_ss [SNOC_APPEND,APPEND]);

val EvalFormula_or_list_MAP_EQUAL = prove(
  ``!r.
      EvalFormula (a,ctxt) (or_list
        (MAP (\r. Equal r (mConst (Sym "NIL"))) r ++ [x])) =
      (EVERY isTrue (MAP (EvalTerm (a,ctxt)) r) ==>
       EvalFormula (a,ctxt) x)``,
  Induct THEN1 SIMP_TAC std_ss [EVERY_DEF,MAP,GENLIST,LENGTH,ZIP,APPEND,or_list_def]
  \\ SIMP_TAC std_ss [GEN_LIST_K_SUC,EVERY_DEF,MAP,
       LENGTH,ZIP,APPEND,or_list_def]
  \\ SIMP_TAC (srw_ss()) [or_list_EXPAND,EvalFormula_def,EvalTerm_def,isTrue_def]
  \\ METIS_TAC []);

val callmap_LENGTH = prove(
  ``!name body p x.
      (ctxt ' name = (formals,xx,yy)) /\ name IN FDOM ctxt /\
      term_ok ctxt body /\ MEM (p,x) (callmap name body) ==>
      (LENGTH formals = LENGTH p)``,
  HO_MATCH_MP_TAC (fetch "-" "callmap_ind") \\ REVERSE (REPEAT STRIP_TAC)
  \\ FULL_SIMP_TAC std_ss [callmap_def,MEM] THEN1
   (FULL_SIMP_TAC std_ss [MEM_APPEND,MEM_FLAT,MEM_MAP]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [callmap_sub_def,MEM_MAP]
    \\ Cases_on `y`
    \\ FULL_SIMP_TAC std_ss [callmap_sub_def,MEM_MAP,LENGTH_MAP]
    \\ METIS_TAC [])
  \\ POP_ASSUM MP_TAC
  \\ Cases_on `f = mPrimitiveFun logic_IF` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `LENGTH xs < 3`
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,MEM_MAP,pairTheory.EXISTS_PROD]
    \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_CONS,EL,HD,term_ok_def,EVERY_DEF]
    \\ METIS_TAC [])
  \\ Cases_on `f = mFun name` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `ctxt ' name = sddd` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [MEM,term_ok_def,func_arity_def,MEM_FLAT,MEM_MAP]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM]);

val termination_obligations_INDUCT = prove(
  ``(ctxt ' name = (formals,BODY_FUN body,sem)) /\
    name IN FDOM ctxt /\ term_ok ctxt body ==>
    EVERY (\x. MilawaValid ctxt x)
     (termination_obligations name body formals m) ==>
    !P. (!a. EVERY (\ (actuals, rulers).
             EVERY isTrue (MAP (EvalTerm (a,ctxt)) rulers) ==>
               P (FunVarBindAux formals (MAP (EvalTerm (a,ctxt)) actuals) a)) (callmap name body) ==> P a) ==>
    !a. P a``,
  STRIP_TAC \\ SIMP_TAC std_ss [termination_obligations_def]
  \\ Cases_on `callmap name body = []` \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [MilawaValid_def,EvalFormula_def,term_ok_def,
       EvalTerm_def,MAP,EvalApp_def,EVAL_PRIMITIVE_def,EL,HD,LISP_TEST_THM,
       formula_ok_def,EVERY_DEF,func_arity_def,primitive_arity_def,LENGTH]
  \\ REPEAT STRIP_TAC
  \\ `?y. EvalTerm (a,ctxt) m = y` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`y`,`y`)
  \\ HO_MATCH_MP_TAC (MATCH_MP relationTheory.WF_INDUCTION_THM WF_ORD_LESS)
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP,EVERY_MEM,ORD_LESS_def]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP,pairTheory.FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [progress_obligation_def]
  \\ FULL_SIMP_TAC std_ss [EvalFormula_MOVE,EvalFormula_or_list_MAP_EQUAL]
  \\ FULL_SIMP_TAC std_ss [MilawaValid_def,EvalFormula_def,term_ok_def,
       EvalTerm_def,MAP,EvalApp_def,EVAL_PRIMITIVE_def,EL,HD,LISP_TEST_THM,
       formula_ok_def,EVERY_DEF,func_arity_def,primitive_arity_def,LENGTH,
       rich_listTheory.EL_CONS,EL,HD,EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP,pairTheory.FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [EvalTerm_sub] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!a. (!b. bbb) ==> P a` MATCH_MP_TAC \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ IMP_RES_TAC callmap_LENGTH \\ IMP_RES_TAC MAP_FST_ZIP \\ IMP_RES_TAC MAP_SND_ZIP
  \\ SIMP_TAC std_ss [GSYM MAP_MAP_o] \\ ASM_REWRITE_TAC []);

val EVERY_MAP_CONS = prove(
  ``EVERY P (MAP (\(x,y). (x,x1::y)) ys) =
    EVERY (\(x,y). P (x,x1::y)) ys``,
  SIMP_TAC std_ss [EVERY_MEM,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val M_evl_EQ_M_ev = prove(
  ``!xs ys a ctxt f.
      M_evl f (xs,a,ctxt) (MAP g xs) =
      EVERY (\x. M_ev f (x,a,ctxt) (g x)) xs``,
  Induct \\ SIMP_TAC std_ss [Once M_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY_IF_CONS = prove(
  ``!b. EVERY P (if b then x::xs else xs) ==> EVERY P xs``,
  Cases \\ FULL_SIMP_TAC std_ss [EVERY_DEF]);

val EVERY_FLAT = prove(
  ``!xs. EVERY P (FLAT xs) = EVERY (EVERY P) xs``,
  Induct \\ ASM_SIMP_TAC std_ss [FLAT,EVERY_DEF,EVERY_APPEND]);

val FunVarBindAux_EQ_FunVarBind = prove(
  ``!xs ys. MEM v xs ==>
            (FunVarBindAux xs ys a v = FunVarBind xs ys v)``,
  Induct \\ Cases_on `ys`
  \\ SIMP_TAC std_ss [MEM,FunVarBindAux_def,FunVarBind_def,LENGTH,ADD1,
       APPLY_UPDATE_THM] \\ STRIP_TAC THEN1
   (Cases_on `v = h` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `xs` \\ SIMP_TAC std_ss [FunVarBind_def]) THEN1
   (Cases_on `v = h'` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `xs` \\ SIMP_TAC std_ss [FunVarBind_def]));

val PULL_EXISTS_CONJ = METIS_PROVE []
  ``((?x. P x) /\ Q = ?x. P x /\ Q) /\ (Q /\ (?x. P x) = ?x. Q /\ P x)``

val MEM_LOOKUP = prove(
  ``!xs. MEM v (MAP FST xs) ==> ?z. MEM z (MAP SND xs) /\ (LOOKUP v xs y = z)``,
  Induct \\ SIMP_TAC std_ss [MAP,MEM,LOOKUP_def,pairTheory.FORALL_PROD]
  \\ METIS_TAC []);

val free_vars_sub = prove(
  ``!xs y x.
       MEM x (free_vars (term_sub xs y)) ==>
       MEM x (FLAT (MAP free_vars (MAP SND xs))) \/
       ~MEM x (MAP FST xs) /\ MEM x (free_vars y)``,
  HO_MATCH_MP_TAC (fetch "-" "term_sub_ind") \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [term_sub_def,free_vars_def,MEM])
  THEN1
   (FULL_SIMP_TAC std_ss [free_vars_def,MEM,term_sub_def]
    \\ REVERSE (Cases_on `MEM xs' (MAP FST xs)`)
    \\ FULL_SIMP_TAC std_ss [NOT_MEM_LOOKUP,free_vars_def,MEM]
    \\ IMP_RES_TAC MEM_LOOKUP
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `mVar xs'`)
    \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP] \\ METIS_TAC [])
  THEN1
   (FULL_SIMP_TAC std_ss [term_sub_def,free_vars_def,MEM_FLAT,MEM_MAP]
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [Once MEM_MAP] \\ SIMP_TAC std_ss [Once MEM_MAP]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ Cases_on `MEM x (MAP FST xs)` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MEM_MAP] \\ METIS_TAC [])
  THEN1
   (FULL_SIMP_TAC std_ss [term_sub_def,free_vars_def,MEM_FLAT,MEM_MAP]
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [Once MEM_MAP] \\ SIMP_TAC std_ss [Once MEM_MAP]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ Cases_on `MEM x (MAP FST xs)` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MEM_MAP] \\ METIS_TAC []));

val callmap_free_vars = prove(
  ``!f l q r.
       MEM (q,r) (callmap f l) /\ term_ok ctxt l ==>
       EVERY (\y. set (free_vars y) SUBSET set (free_vars l)) (r ++ q)``,
  HO_MATCH_MP_TAC (fetch "-" "callmap_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MEM,callmap_def] THEN1
   (Cases_on `f' = mPrimitiveFun logic_IF` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Cases_on `LENGTH xs < 3` \\ FULL_SIMP_TAC std_ss [MEM]
      \\ FULL_SIMP_TAC std_ss [func_arity_def,primitive_arity_def,LENGTH_EQ_3,term_ok_def]
      \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_CONS,EL,HD]
      \\ Q.PAT_X_ASSUM `xs = [x1;x2;x3]` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
      \\ FULL_SIMP_TAC std_ss [MEM_APPEND] \\ RES_TAC THEN1
       (FULL_SIMP_TAC std_ss [free_vars_def,EVERY_MEM,SUBSET_DEF,
          MEM_FLAT,MEM_MAP] \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [MEM])
      THEN1
       (FULL_SIMP_TAC std_ss [free_vars_def,EVERY_MEM,SUBSET_DEF,
          MEM_FLAT,MEM_MAP] \\ REPEAT STRIP_TAC
        \\ Cases_on `y` \\ FULL_SIMP_TAC std_ss []
        \\ NTAC 2 (POP_ASSUM MP_TAC)
        \\ FULL_SIMP_TAC std_ss [APPEND,MEM]
        \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
      THEN1
       (FULL_SIMP_TAC std_ss [free_vars_def,EVERY_MEM,SUBSET_DEF,
          MEM_FLAT,MEM_MAP] \\ REPEAT STRIP_TAC
        \\ Cases_on `y` \\ FULL_SIMP_TAC std_ss []
        \\ NTAC 2 (POP_ASSUM MP_TAC)
        \\ FULL_SIMP_TAC std_ss [APPEND,MEM]
        \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [free_vars_def,MEM_FLAT,MEM_MAP,MEM]
        \\ METIS_TAC []))
    \\ Cases_on `f' = mFun f` \\ FULL_SIMP_TAC std_ss [MEM]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,APPEND,free_vars_def]
    \\ FULL_SIMP_TAC std_ss [free_vars_def,EVERY_MEM,SUBSET_DEF,
           MEM_FLAT,MEM_MAP,term_ok_def,EVERY_MEM] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND] THEN1
   (FULL_SIMP_TAC std_ss [free_vars_def,EVERY_MEM,SUBSET_DEF,
          MEM_FLAT,MEM_MAP,term_ok_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [free_vars_def,EVERY_MEM,SUBSET_DEF,
          MEM_FLAT,MEM_MAP,term_ok_def,callmap_sub_def]
  \\ Cases_on `y` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_CONJ]
  \\ FULL_SIMP_TAC std_ss [GSYM MAP_APPEND,MEM_MAP]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!aa bb. bbb` (MP_TAC o Q.SPECL [`q'`,`r'`,`y'`])
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC free_vars_sub
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP_FST_ZIP,MAP_SND_ZIP]
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP] \\ METIS_TAC [])
  |> SIMP_RULE std_ss [EVERY_APPEND];

val EvalTerm_SIMP = prove(
  ``set (free_vars y) SUBSET set l1 ==>
    (EvalTerm (FunVarBindAux l1 ys b,ctxt) y =
     EvalTerm (FunVarBind l1 ys,ctxt) y)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC EvalTerm_CHANGE_INST \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC FunVarBindAux_EQ_FunVarBind
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]);

val M_ev_SIMP = prove(
  ``set (free_vars y) SUBSET set l1 ==>
    (M_ev f (y,FunVarBindAux l1 ys b,ctxt) x =
     M_ev f (y,FunVarBind l1 ys,ctxt) x)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC M_ev_EQ
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC FunVarBindAux_EQ_FunVarBind
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]);

val M_ev_TERMINATES_STEP = prove(
  ``f IN FDOM ctxt /\ (ctxt ' f = (params,BODY_FUN body,EvalFun f ctxt)) /\
    term_ok ctxt body /\ set (free_vars body) SUBSET set params /\
    ALL_DISTINCT params ==>
    !exp a.
      EVERY (\(actuals,rulers).
        EVERY isTrue (MAP (EvalTerm (a,ctxt)) rulers) ==>
          M_ev f
            (body,FunVarBindAux params (MAP (EvalTerm (a,ctxt)) actuals) a,ctxt)
            (EvalTerm (FunVarBindAux params (MAP (EvalTerm (a,ctxt)) actuals) a,ctxt) body))
               (callmap f exp) /\ term_ok ctxt exp ==>
      M_ev f (exp,a,ctxt) (EvalTerm (a,ctxt) exp)``,
  STRIP_TAC \\ STRIP_TAC \\ completeInduct_on `logic_term_size exp`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ Cases_on `exp`
  THEN1 SIMP_TAC (srw_ss()) [EvalTerm_def,Once M_ev_cases]
  THEN1 SIMP_TAC (srw_ss()) [EvalTerm_def,Once M_ev_cases]
  THEN1
   (FULL_SIMP_TAC std_ss [callmap_def]
    \\ Cases_on `l0 = mPrimitiveFun logic_IF` \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def,
        primitive_arity_def,LENGTH_EQ_3]
      \\ FULL_SIMP_TAC std_ss [callmap_def,EL,rich_listTheory.EL_CONS,HD,LENGTH,
           EVERY_APPEND,EvalTerm_def,EvalApp_def,EVAL_PRIMITIVE_def,MAP,LISP_IF_def]
      \\ ONCE_REWRITE_TAC [M_ev_cases] \\ SIMP_TAC (srw_ss()) []
      \\ Q.PAT_X_ASSUM `!exp.bbb` (fn th => ASSUME_TAC th THEN MP_TAC (Q.SPECL [`x1`,`a`] th))
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [EVERY_DEF,term_ok_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [EVERY_MEM,MEM])
      \\ REPEAT STRIP_TAC
      \\ `!x. M_ev f (x1,a,ctxt) x = (x = (EvalTerm (a,ctxt) x1))` by METIS_TAC [M_ev_DETERMINISTIC]
      \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `isTrue (EvalTerm (a,ctxt) x1)`
      \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN1
       (Q.PAT_X_ASSUM `!exp a.bbb` MATCH_MP_TAC
        \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
        \\ REVERSE STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [EVERY_MEM,MEM])
        \\ FULL_SIMP_TAC std_ss [EVERY_MAP_CONS,EVERY_DEF,MAP])
      THEN1
       (Q.PAT_X_ASSUM `!exp a.bbb` MATCH_MP_TAC
        \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
        \\ REVERSE STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [EVERY_MEM,MEM])
        \\ FULL_SIMP_TAC std_ss [EVERY_MAP_CONS,EVERY_DEF,MAP,
             EvalTerm_def,EvalApp_def,EVAL_PRIMITIVE_def,EL,HD,LISP_TEST_THM]
        \\ FULL_SIMP_TAC std_ss [isTrue_def]))
    \\ ONCE_REWRITE_TAC [M_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [EvalTerm_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ `M_evl f (l,a,ctxt) (MAP (EvalTerm (a,ctxt)) l)` by
     (SIMP_TAC std_ss [M_evl_EQ_M_ev] \\ SIMP_TAC std_ss [EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
      \\ Q.PAT_X_ASSUM `!exp a. bbb` MATCH_MP_TAC \\ STRIP_TAC
      THEN1 (EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size_alt_LESS \\ DECIDE_TAC)
      \\ IMP_RES_TAC EVERY_IF_CONS
      \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [EVERY_FLAT]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ SIMP_TAC std_ss [Once EVERY_MEM]
      \\ ASM_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM])
    \\ Q.EXISTS_TAC `MAP (EvalTerm (a,ctxt)) l` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `l0` THEN1
     (ONCE_REWRITE_TAC [M_ev_cases]
      \\ SIMP_TAC (srw_ss()) [EvalTerm_def,EvalApp_def]
      \\ FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def])
    \\ REVERSE (Cases_on `s = f`) \\ FULL_SIMP_TAC std_ss [] THEN1
     (SIMP_TAC std_ss [Once M_ev_cases]
      \\ FULL_SIMP_TAC (srw_ss()) [EvalApp_def,LET_DEF]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def]
      \\ Cases_on `ctxt ' s` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [EvalApp_def,LET_DEF,EVERY_DEF,MAP]
    \\ ASM_SIMP_TAC (srw_ss()) [Once M_ev_cases]
    \\ SIMP_TAC std_ss [EvalFun_def,Eval_M_ap_def]
    \\ SIMP_TAC std_ss [M_ev_cases |> SPEC_ALL |> CONJUNCTS |> el 2]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def]
    \\ Q.PAT_X_ASSUM `ctxt ' f = (params,BODY_FUN body,EvalFun f ctxt)` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `(!v. MEM v (free_vars body) ==>
             (FunVarBindAux params (MAP (EvalTerm (a,ctxt)) l) a v =
              FunVarBind params (MAP (EvalTerm (a,ctxt)) l) v))` by
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]
      \\ RES_TAC \\ MATCH_MP_TAC FunVarBindAux_EQ_FunVarBind
      \\ ASM_SIMP_TAC std_ss [LENGTH_MAP]
      \\ FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def]
      \\ METIS_TAC [pairTheory.FST])
    \\ METIS_TAC [M_ev_EQ])
  THEN1
   (FULL_SIMP_TAC std_ss [callmap_def,EVERY_APPEND]
    \\ SIMP_TAC (srw_ss()) [Once M_ev_cases]
    \\ `M_evl f (l0,a,ctxt) (MAP (EvalTerm (a,ctxt)) l0)` by
     (SIMP_TAC std_ss [M_evl_EQ_M_ev] \\ SIMP_TAC std_ss [EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
      \\ Q.PAT_X_ASSUM `!exp a. bbb` MATCH_MP_TAC \\ STRIP_TAC
      THEN1 (EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size_alt_LESS \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [EVERY_FLAT]
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,pairTheory.FORALL_PROD]
      \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM]
      \\ METIS_TAC [])
    \\ Q.EXISTS_TAC `MAP (EvalTerm (a,ctxt)) l0` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [term_ok_def,EvalTerm_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [logic_term_size_def]
    \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ Cases \\ SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
    \\ FULL_SIMP_TAC std_ss [callmap_sub_def,MEM_MAP,pairTheory.EXISTS_PROD]
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_IMP,MEM_MAP,EvalTerm_sub]
    \\ FULL_SIMP_TAC std_ss [MAP_FST_ZIP,GSYM MAP_MAP_o,MAP_SND_ZIP]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!xx yy. bbb` (MP_TAC o Q.SPECL [`q`,`r`])
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC callmap_free_vars
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ RES_TAC
      \\ IMP_RES_TAC SUBSET_TRANS \\ FULL_SIMP_TAC std_ss [EvalTerm_SIMP])
    \\ SIMP_TAC std_ss [MAP_MAP_o,combinTheory.o_DEF,EvalTerm_sub]
    \\ FULL_SIMP_TAC std_ss [MAP_FST_ZIP,GSYM MAP_MAP_o,MAP_SND_ZIP]
    \\ `(MAP (\x. EvalTerm (a,ctxt) (SND x)) (ZIP (l1,l0))) =
        (MAP (EvalTerm (a,ctxt)) l0)` by
     (MATCH_MP_TAC EQ_TRANS
      \\ Q.EXISTS_TAC `MAP (EvalTerm (a,ctxt) o SND) (ZIP (l1,l0))`
      \\ STRIP_TAC THEN1 SIMP_TAC std_ss [combinTheory.o_DEF]
      \\ ASM_SIMP_TAC std_ss [GSYM MAP_MAP_o,MAP_SND_ZIP])
    \\ FULL_SIMP_TAC std_ss [] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ `MAP (EvalTerm (FunVarBindAux l1 (MAP (EvalTerm (a,ctxt)) l0) a,ctxt)) q =
        MAP (EvalTerm (FunVarBind l1 (MAP (EvalTerm (a,ctxt)) l0),ctxt)) q` by
     (MATCH_MP_TAC IMP_MAP_EQ_MAP \\ REPEAT STRIP_TAC
      \\ RES_TAC \\ IMP_RES_TAC callmap_free_vars
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ RES_TAC
      \\ IMP_RES_TAC SUBSET_TRANS \\ FULL_SIMP_TAC std_ss [EvalTerm_SIMP])
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC EvalTerm_SIMP
    \\ ASM_SIMP_TAC std_ss [M_ev_SIMP] \\ ASM_REWRITE_TAC []
    \\ FULL_SIMP_TAC std_ss [EvalTerm_SIMP]));

val M_ev_TERMINATES = store_thm("M_ev_TERMINATES",
  ``f IN FDOM ctxt /\ (ctxt ' f = (params,BODY_FUN body,EvalFun f ctxt)) /\
    term_ok ctxt body /\ set (free_vars body) SUBSET set params /\
    ALL_DISTINCT params /\
    EVERY (\x. MilawaValid ctxt x)
          (termination_obligations f body params m) ==>
    !a. M_ev f (body,a,ctxt) (EvalTerm (a,ctxt) body)``,
  STRIP_TAC
  \\ MP_TAC (Q.INST [`name`|->`f`,`formals`|->`params`,
       `sem`|->`EvalFun f ctxt`] termination_obligations_INDUCT)
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM HO_MATCH_MP_TAC \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ METIS_TAC [M_ev_TERMINATES_STEP]);

val M_ev_REMOVE_FunVarBind = prove(
  ``set (free_vars y) SUBSET set xs ==>
    (M_ev f (y,FunVarBind xs (MAP a xs),ctxt) x = M_ev f (y,a,ctxt) x)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC M_ev_EQ
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]
  \\ RES_TAC \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`xs`,`xs`)
  \\ Induct \\ SIMP_TAC std_ss [MEM,MAP,FunVarBind_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [MEM,MAP,FunVarBind_def,APPLY_UPDATE_THM]);

val BODY_FUN_EXISTS = prove(
  ``f IN FDOM ctxt /\ (ctxt ' f = (params,BODY_FUN body,EvalFun f ctxt)) /\
    term_ok ctxt body /\ set (free_vars body) SUBSET set params /\
    ALL_DISTINCT params /\
    EVERY (\x. MilawaValid ctxt x) (termination_obligations f body params m) ==>
    !a. EvalFun f ctxt (MAP a params) = EvalTerm (a,ctxt) body``,
  REPEAT STRIP_TAC \\ MP_TAC M_ev_TERMINATES \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [EvalFun_def,Eval_M_ap_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once M_ev_cases]
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `a`)
  \\ ASM_SIMP_TAC std_ss [M_ev_REMOVE_FunVarBind]
  \\ METIS_TAC [M_ev_DETERMINISTIC]);

val EvalFun_IGNORE_SEM = store_thm("EvalFun_IGNORE_SEM",
  ``EvalFun fname (ctxt |+ (fname,params,BODY_FUN body,sem)) =
    EvalFun fname (ctxt |+ (fname,params,BODY_FUN body,ARB))``,
  SIMP_TAC std_ss [EvalFun_def,FUN_EQ_THM,Eval_M_ap_def]
  \\ FULL_SIMP_TAC std_ss [Q.INST [`sem2`|->`ARB`] M_ap_EQ_SEM])

val MAP_UPDATE_IGNORE = prove(
  ``!xs. ~MEM x xs ==> (MAP ((x =+ h) f) xs = MAP f xs)``,
  Induct \\ SRW_TAC [] [APPLY_UPDATE_THM]);

val MAP_FunVarBind_CANCEL = prove(
  ``!params args.
      (LENGTH params = LENGTH args) /\ ALL_DISTINCT params ==>
      (MAP (FunVarBind params args) params = args)``,
  Induct \\ Cases_on `args` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH,MAP]
  \\ FULL_SIMP_TAC std_ss [FunVarBind_def,APPLY_UPDATE_THM,CONS_11,
       ALL_DISTINCT,MAP_UPDATE_IGNORE]);

(* finishing the proof off *)

val EvalTerm_REDUCE_CTXT = prove(
  ``!a ctxt exp.
      (\(a,ctxt) exp.
        term_ok ctxt exp /\ ~(name IN FDOM ctxt) ==>
        (EvalTerm (a,ctxt |+ (name,params,body,sem)) exp = EvalTerm (a,ctxt) exp))
          (a,ctxt) exp``,
  MATCH_MP_TAC (fetch "-" "EvalTerm_ind")
  \\ FULL_SIMP_TAC std_ss [EvalTerm_def,LET_DEF] \\ REPEAT STRIP_TAC THEN1
   (`MAP (EvalTerm (a,ctxt |+ (name,params,body,sem))) args =
     MAP (EvalTerm (a,ctxt)) args` by
     (MATCH_MP_TAC IMP_MAP_EQ_MAP \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM])
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ Cases_on `f`
    \\ FULL_SIMP_TAC std_ss [term_ok_def,func_arity_def,EvalApp_def,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM] \\ METIS_TAC [])
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ `MAP (EvalTerm (a,ctxt |+ (name,params,body,sem))) ys =
      MAP (EvalTerm (a,ctxt)) ys` by
     (MATCH_MP_TAC IMP_MAP_EQ_MAP \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM])
  \\ FULL_SIMP_TAC std_ss [term_ok_def] \\ METIS_TAC []) |> SIMP_RULE std_ss [];

val term_ok_MEM_funs_IMP = store_thm("term_ok_MEM_funs_IMP",
  ``!ctxt body m. term_ok ctxt body /\ MEM m (funs body) ==> m IN FDOM ctxt``,
  HO_MATCH_MP_TAC (fetch "-" "term_ok_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [funs_def,MEM,MEM_APPEND,term_ok_def,EVERY_MEM,MEM_FLAT,MEM_MAP]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ Cases_on `fc`
  \\ FULL_SIMP_TAC std_ss [funs_def,MEM,MEM_APPEND,term_ok_def,EVERY_MEM,MEM_FLAT,MEM_MAP]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [func_arity_def]
  \\ METIS_TAC []);

val EvalFun_FUPDATE = store_thm("EvalFun_FUPDATE",
  ``fname' IN FDOM ctxt /\ ~(fname IN FDOM ctxt) /\
    (ctxt ' fname' = (params',BODY_FUN body',EvalFun fname' ctxt)) /\
    term_ok ctxt body' ==>
    (EvalFun fname' (ctxt |+ (fname,params,body,sem)) =
     EvalFun fname' ctxt)``,
  SIMP_TAC std_ss [EvalFun_def,FUN_EQ_THM,Eval_M_ap_def]
  \\ REPEAT STRIP_TAC \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ AP_TERM_TAC \\ SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL M_ap_EQ_CTXT_LEMMA)
    \\ Q.EXISTS_TAC `ctxt |+ (fname,params,body,sem)`
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ `~(fname = fname')` by METIS_TAC []
    \\ ASM_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC term_ok_MEM_funs_IMP \\ METIS_TAC [])
  THEN1
   (MATCH_MP_TAC (GEN_ALL M_ap_EQ_CTXT_LEMMA)
    \\ Q.EXISTS_TAC `ctxt` \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ REPEAT STRIP_TAC \\ `~(fname = fname')` by METIS_TAC []
    \\ ASM_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC term_ok_MEM_funs_IMP \\ METIS_TAC []));

val MilawaValid_IGNORE_SYNTAX = store_thm("MilawaValid_IGNORE_SYNTAX",
  ``MilawaValid (ctxt |+ (name,params,body,sem)) =
    MilawaValid (ctxt |+ (name,params,ARB,sem))``,
  FULL_SIMP_TAC std_ss [MilawaValid_def,FUN_EQ_THM,EvalFormula_IGNORE_BODY]);

val definition_ok_lemma = prove(
  ``!name params body ctxt.
      context_ok ctxt /\ definition_ok (name,params,body,ctxt) ==>
      context_ok (ctxt |+ (name,params,body,
        case body of
          NO_FUN => ARB
        | BODY_FUN l => EvalFun name (ctxt |+ (name,params,BODY_FUN l,ARB))
        | WITNESS_FUN l s => \args. @v. isTrue (EvalTerm (FunVarBind (s::params) (v::args),ctxt) l)))``,
  REPEAT STRIP_TAC \\ REVERSE (Cases_on `body`)
  THEN1 (METIS_TAC [context_ok_None,definition_ok_def])
  THEN1
   (Q.ABBREV_TAC `witness = \args. @v. isTrue (EvalTerm (FunVarBind (s::params) (v::args),ctxt) l)`
    \\ `~(name IN FDOM ctxt)` by FULL_SIMP_TAC std_ss [definition_ok_def]
    \\ FULL_SIMP_TAC std_ss [context_ok_def]
    \\ NTAC 2 STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_IMP]
    \\ REVERSE (Cases_on `fname = name`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
      \\ IMP_RES_TAC (EvalTerm_FUPDATE |> GSYM |> GEN_ALL) \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [fetch "-" "func_body_distinct",pairTheory.PAIR_EQ,
                EvalTerm_FUPDATE,term_ok_FUPDATE])
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC] THEN1
     (REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
      \\ IMP_RES_TAC (EvalTerm_FUPDATE |> GSYM |> GEN_ALL) \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [fetch "-" "func_body_distinct",pairTheory.PAIR_EQ,
                EvalTerm_FUPDATE,term_ok_FUPDATE])
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [definition_ok_def,ALL_DISTINCT,LIST_TO_SET_THM]
      \\ METIS_TAC [fetch "-" "func_body_distinct",pairTheory.PAIR_EQ,
                    EvalTerm_FUPDATE,term_ok_FUPDATE])
    \\ FULL_SIMP_TAC std_ss [definition_ok_def]
    \\ IMP_RES_TAC EvalTerm_REDUCE_CTXT \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `witness` \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  THEN1
   (`~(name IN FDOM ctxt)` by FULL_SIMP_TAC std_ss [definition_ok_def]
    \\ Q.PAT_X_ASSUM `context_ok ctxt` (fn th => MP_TAC th \\ ASSUME_TAC th)
    \\ SIMP_TAC std_ss [context_ok_def] \\ STRIP_TAC
    \\ REVERSE (NTAC 2 STRIP_TAC)
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_IMP]
    \\ REVERSE (Cases_on `fname = name`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
      \\ IMP_RES_TAC (EvalTerm_FUPDATE |> GSYM |> GEN_ALL) \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [fetch "-" "func_body_distinct",pairTheory.PAIR_EQ,
                EvalTerm_FUPDATE,term_ok_FUPDATE])
    \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC] THEN1
     (REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
      \\ IMP_RES_TAC (EvalTerm_FUPDATE |> GSYM |> GEN_ALL) \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [fetch "-" "func_body_distinct",pairTheory.PAIR_EQ,
                EvalTerm_FUPDATE,term_ok_FUPDATE])
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [definition_ok_def,ALL_DISTINCT,LIST_TO_SET_THM,
        term_ok_IGNORE_SEM])
    \\ Q.ABBREV_TAC `new_ctxt = ctxt |+
        (name,params,BODY_FUN l,
         EvalFun name (ctxt |+ (name,params,BODY_FUN l,ARB)))`
    \\ `EvalFun name (ctxt |+ (name,params,BODY_FUN l,ARB)) =
        EvalFun name new_ctxt` by (METIS_TAC [EvalFun_IGNORE_SEM])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [definition_ok_def]
    \\ MP_TAC (BODY_FUN_EXISTS
         |> Q.INST [`f`|->`name`,`ctxt`|->`new_ctxt`,`body`|->`l`])
    \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ REVERSE STRIP_TAC THEN1 METIS_TAC []
    \\ STRIP_TAC THEN1 (Q.UNABBREV_TAC `new_ctxt` \\ FULL_SIMP_TAC (srw_ss()) [FDOM_FUPDATE])
    \\ STRIP_TAC THEN1 METIS_TAC [FAPPLY_FUPDATE_THM,FDOM_FUPDATE]
    \\ STRIP_TAC
    THEN1 (Q.UNABBREV_TAC `new_ctxt` \\ FULL_SIMP_TAC std_ss [term_ok_IGNORE_SEM])
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ `MilawaTrue (ctxt |+ (name,params,NO_FUN,EvalFun name new_ctxt)) x` by (FULL_SIMP_TAC std_ss [MilawaTrue_IGNORE_SEM])
    \\ `context_ok (ctxt |+ (name,params,NO_FUN,EvalFun name new_ctxt))` by (MATCH_MP_TAC context_ok_None \\ FULL_SIMP_TAC std_ss [])
    \\ `MilawaValid (ctxt |+ (name,params,NO_FUN,EvalFun name new_ctxt)) x` by METIS_TAC [Milawa_SOUNDESS]
    \\ METIS_TAC [MilawaValid_IGNORE_SYNTAX]));

val definition_ok_thm = store_thm("definition_ok_thm",
  ``!name params body ctxt.
      context_ok ctxt /\ definition_ok (name,params,body,ctxt) ==>
      ?f. context_ok (ctxt |+ (name,params,body,f))``,
  METIS_TAC [definition_ok_lemma]);

val definition_ok_WITNESS_FUN = store_thm("definition_ok_WITNESS_FUN",
  ``!name params l s ctxt.
      context_ok ctxt /\ definition_ok (name,params,WITNESS_FUN l s,ctxt) ==>
      context_ok (ctxt |+ (name,params,WITNESS_FUN l s,\args. @v. isTrue (EvalTerm (FunVarBind (s::params) (v::args),ctxt) l)))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC
  (definition_ok_lemma
    |> SPEC_ALL |> Q.INST [`body`|->`WITNESS_FUN l s`]
    |> SIMP_RULE (srw_ss()) []) \\ FULL_SIMP_TAC std_ss []);

val definition_ok_BODY_FUN = store_thm("definition_ok_BODY_FUN",
  ``!name params l ctxt.
      context_ok ctxt /\ definition_ok (name,params,BODY_FUN l,ctxt) ==>
      context_ok (ctxt |+ (name,params,BODY_FUN l,EvalFun name (ctxt |+ (name,params,BODY_FUN l,ARB))))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC
  (definition_ok_lemma
    |> SPEC_ALL |> Q.INST [`body`|->`BODY_FUN l`]
    |> SIMP_RULE (srw_ss()) []) \\ FULL_SIMP_TAC std_ss []);

val _ = export_theory();
