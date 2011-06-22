(* ===================================================================== *)
(* FILE          : mk_list_thms.sml                                      *)
(* DESCRIPTION   : Theorems about lists. Translated from hol88.          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* HISTORY       : 22 March 1991                                         *)
(*                 Extended by Paul Curzon, University of Cambridge      *)
(*                 to maintain consistency with Wai Wongs HOL88 theory   *)
(*                                                                       *)
(*                 October'94 (KLS) minor rearrangements for             *)
(*                 library-ification of lists.                           *)
(*                 Feb'99 (KLS) changed name to be different (ignoring   *)
(*                 case distinctions) from listTheory.                   *)
(* ===================================================================== *)

structure rich_listScript =
struct

local open operatorTheory listTheory in end;

open HolKernel Parse boolLib numLib Prim_rec simpLib boolSimps;

infix THEN THENL ORELSE;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;
val list_Axiom = listTheory.list_Axiom;
val list_Axiom_old = listTheory.list_Axiom_old;
val let_CONV = PairedLambda.let_CONV;
val arith_ss = bool_ss ++ numSimps.ARITH_ss ++ numSimps.REDUCE_ss
val list_ss  = arith_ss ++ listSimps.LIST_ss

val _ = new_theory "rich_list";

fun new_list_rec_definition (name,tm) =
  new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm};

(* Permutation of universal quantifications                             *)

fun chk_var vl v = (is_var v andalso (mem v vl)) ;

val FORALL_PERM_CONV =
  let val forall_perm_rule =
              fn tms => fn thm => GENL tms (SPEC_ALL thm)
  in
   fn tms => fn tm =>
     let val (vs,body) =  strip_forall tm
     in if (all (chk_var vs) tms)
        then let val vs' = tms @ (subtract vs tms)
                 val th1 = DISCH_ALL (forall_perm_rule vs' (ASSUME tm))
                 val th2 = DISCH_ALL (forall_perm_rule vs
                                        (ASSUME(list_mk_forall(vs',body))))
             in IMP_ANTISYM_RULE th1 th2
             end
        else raise HOL_ERR{origin_structure = "",
                           origin_function = "FORALL_PERM_CONV",
                           message = "not all variables are quantified"}
     end
  end;

val FORALL_PERM_TAC =
  fn tms => fn (asm,gl) =>
    CONV_TAC (FORALL_PERM_CONV tms) (asm,gl);



(* Fetch a few theorems from prim_rec.th                                *)

val INV_SUC_EQ =  prim_recTheory.INV_SUC_EQ;
val LESS_REFL =  prim_recTheory.LESS_REFL;
val SUC_LESS =  prim_recTheory.SUC_LESS;
val NOT_LESS_0 =  prim_recTheory.NOT_LESS_0;
val LESS_MONO =  prim_recTheory.LESS_MONO;
val LESS_SUC_REFL =  prim_recTheory.LESS_SUC_REFL;
val LESS_SUC =  prim_recTheory.LESS_SUC;
val LESS_THM =  prim_recTheory.LESS_THM;
val LESS_SUC_IMP =  prim_recTheory.LESS_SUC_IMP;
val LESS_0 =  prim_recTheory.LESS_0;
val EQ_LESS =  prim_recTheory.EQ_LESS;
val SUC_ID =  prim_recTheory.SUC_ID;
val NOT_LESS_EQ =  prim_recTheory.NOT_LESS_EQ;
val LESS_NOT_EQ =  prim_recTheory.LESS_NOT_EQ;
val LESS_SUC_SUC =  prim_recTheory.LESS_SUC_SUC;
val PRE =  prim_recTheory.PRE;
val num_Axiom =   prim_recTheory.num_Axiom;

(* Fetch a few things from arithmetic.th                                *)

val LESS_OR_EQ =   arithmeticTheory.LESS_OR_EQ;
val ADD =   arithmeticTheory.ADD;
val SUB =   arithmeticTheory.SUB;
val ADD_SUC =   arithmeticTheory.ADD_SUC;
val ADD_CLAUSES =   arithmeticTheory.ADD_CLAUSES;
val ADD_SYM =   arithmeticTheory.ADD_SYM;
val LESS_MONO_EQ =   arithmeticTheory.LESS_MONO_EQ;
val SUC_SUB1 =   arithmeticTheory.SUC_SUB1;
val LESS_ADD =   arithmeticTheory.LESS_ADD;
val SUB_0 =   arithmeticTheory.SUB_0;
val LESS_TRANS =   arithmeticTheory.LESS_TRANS;
val ADD1 =   arithmeticTheory.ADD1;
val ADD_0 =   arithmeticTheory.ADD_0;
val LESS_ANTISYM =   arithmeticTheory.LESS_ANTISYM;
val LESS_LESS_SUC =   arithmeticTheory.LESS_LESS_SUC;
val LESS_SUC_EQ_COR =   arithmeticTheory.LESS_SUC_EQ_COR;
val LESS_OR =   arithmeticTheory.LESS_OR;
val OR_LESS =   arithmeticTheory.OR_LESS;
val LESS_EQ =   arithmeticTheory.LESS_EQ;
val LESS_NOT_SUC =   arithmeticTheory.LESS_NOT_SUC;
val LESS_EQ_ANTISYM =   arithmeticTheory.LESS_EQ_ANTISYM;
val LESS_EQ_ADD =   arithmeticTheory.LESS_EQ_ADD;
val NOT_LESS =   arithmeticTheory.NOT_LESS;
val SUB_EQ_0 =   arithmeticTheory.SUB_EQ_0;
val ADD_ASSOC =   arithmeticTheory.ADD_ASSOC;
val SUB_ADD =   arithmeticTheory.SUB_ADD;
val ADD_EQ_0 =   arithmeticTheory.ADD_EQ_0;
val ADD_INV_0_EQ =   arithmeticTheory.ADD_INV_0_EQ;
val LESS_SUC_NOT =   arithmeticTheory.LESS_SUC_NOT;
val LESS_MONO_ADD =   arithmeticTheory.LESS_MONO_ADD;
val LESS_MONO_ADD_EQ =   arithmeticTheory.LESS_MONO_ADD_EQ;
val EQ_MONO_ADD_EQ =   arithmeticTheory.EQ_MONO_ADD_EQ;
val LESS_EQ_MONO_ADD_EQ =   arithmeticTheory.LESS_EQ_MONO_ADD_EQ;
val LESS_EQ_TRANS =   arithmeticTheory.LESS_EQ_TRANS;
val LESS_EQ_LESS_EQ_MONO =   arithmeticTheory.LESS_EQ_LESS_EQ_MONO;
val LESS_EQ_REFL =   arithmeticTheory.LESS_EQ_REFL;
val LESS_IMP_LESS_OR_EQ =   arithmeticTheory.LESS_IMP_LESS_OR_EQ;
val LESS_MONO_MULT =   arithmeticTheory.LESS_MONO_MULT;
val LESS_0_CASES =   arithmeticTheory.LESS_0_CASES;
val ZERO_LESS_EQ =   arithmeticTheory.ZERO_LESS_EQ;
val LESS_EQ_MONO =   arithmeticTheory.LESS_EQ_MONO;
val LESS_OR_EQ_ADD =   arithmeticTheory.LESS_OR_EQ_ADD;
val SUC_NOT =   arithmeticTheory.SUC_NOT;
val SUB_MONO_EQ =   arithmeticTheory.SUB_MONO_EQ;
val SUB_LESS_EQ =   arithmeticTheory.SUB_LESS_EQ;
val LESS_EQUAL_ANTISYM =   arithmeticTheory.LESS_EQUAL_ANTISYM;
val SUB_LESS_0 =   arithmeticTheory.SUB_LESS_0;
val SUB_LESS_OR =   arithmeticTheory.SUB_LESS_OR;
val LESS_ADD_SUC =   arithmeticTheory.LESS_ADD_SUC;
val LESS_SUB_ADD_LESS =   arithmeticTheory.LESS_SUB_ADD_LESS;
val ADD_SUB =   arithmeticTheory.ADD_SUB;
val LESS_EQ_ADD_SUB =   arithmeticTheory.LESS_EQ_ADD_SUB;
val SUB_EQUAL_0 =   arithmeticTheory.SUB_EQUAL_0;
val LESS_EQ_SUB_LESS =   arithmeticTheory.LESS_EQ_SUB_LESS;
val NOT_SUC_LESS_EQ =   arithmeticTheory.NOT_SUC_LESS_EQ;
val SUB_SUB =   arithmeticTheory.SUB_SUB;
val LESS_IMP_LESS_ADD =   arithmeticTheory.LESS_IMP_LESS_ADD;
val LESS_EQ_IMP_LESS_SUC =   arithmeticTheory.LESS_EQ_IMP_LESS_SUC;
val SUB_LESS_EQ_ADD =   arithmeticTheory.SUB_LESS_EQ_ADD;
val LESS_LESS_CASES =   arithmeticTheory.LESS_LESS_CASES;
val LESS_EQ_0 =   arithmeticTheory.LESS_EQ_0;
val EQ_LESS_EQ =   arithmeticTheory.EQ_LESS_EQ;
val ADD_MONO_LESS_EQ =   arithmeticTheory.ADD_MONO_LESS_EQ;
val NOT_SUC_LESS_EQ_0 =   arithmeticTheory.NOT_SUC_LESS_EQ_0;
val PRE_SUC_EQ =   arithmeticTheory.PRE_SUC_EQ;
val NOT_LEQ =   arithmeticTheory.NOT_LEQ;
val NOT_NUM_EQ =   arithmeticTheory.NOT_NUM_EQ;
val NOT_GREATER =   arithmeticTheory.NOT_GREATER;
val NOT_GREATER_EQ =   arithmeticTheory.NOT_GREATER_EQ;
val SUC_ONE_ADD =   arithmeticTheory.SUC_ONE_ADD;
val SUC_ADD_SYM =   arithmeticTheory.SUC_ADD_SYM;
val NOT_SUC_ADD_LESS_EQ =   arithmeticTheory.NOT_SUC_ADD_LESS_EQ;
val MULT_LESS_EQ_SUC =   arithmeticTheory.MULT_LESS_EQ_SUC;
val PRE_SUB1 =   arithmeticTheory.PRE_SUB1;
val SUB_PLUS =   arithmeticTheory.SUB_PLUS;
val GREATER_EQ =   arithmeticTheory.GREATER_EQ;

(* Fetch a few things from num.th                                       *)

val INV_SUC = numTheory.INV_SUC;
val NOT_SUC = numTheory.NOT_SUC;
val INDUCTION = numTheory.INDUCTION;

(* Fetch a few definitions and theorems from "operator".                *)

val ASSOC_DEF =  operatorTheory.ASSOC_DEF;
val COMM_DEF =  operatorTheory.COMM_DEF;
val FCOMM_DEF =  operatorTheory.FCOMM_DEF;
val RIGHT_ID_DEF =  operatorTheory.RIGHT_ID_DEF;
val LEFT_ID_DEF =  operatorTheory.LEFT_ID_DEF;
val MONOID_DEF =  operatorTheory.MONOID_DEF;
val ASSOC_CONJ =  operatorTheory.ASSOC_CONJ;
val ASSOC_DISJ =  operatorTheory.ASSOC_DISJ;
val FCOMM_ASSOC =  operatorTheory.FCOMM_ASSOC;

(* Fetch a few definitions and theorems from combin.th                  *)

val o_DEF = combinTheory.o_DEF;
val o_THM = combinTheory.o_THM;
val I_THM = combinTheory.I_THM;

val UNCURRY_DEF = pairTheory.UNCURRY_DEF;

(* List induction                                                       *)
(* |- P NIL /\ (!l. P l ==> !x. P(CONS x l)) ==> (!x. P x)              *)
val list_INDUCT = store_thm("list_INDUCT",
 --`!P. P [] /\ (!l. P l ==> !x:'a. P(CONS x l)) ==> (!l. P l)`--,
 REWRITE_TAC[listTheory.list_INDUCT]);

(* Create a tactic.                                                     *)
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

val num_CONV = Num_conv.num_CONV;

(* --------------------------------------------------------------------- *)
(* Definitions of NULL, HD and TL.                                       *)
(* --------------------------------------------------------------------- *)

val NULL_DEF = store_thm("NULL_DEF",
--`(NULL ([]:'a list) = T) /\
   !(x:'a) l. NULL (CONS x l) = F`--,
 REWRITE_TAC[listTheory.NULL_DEF]);

val HD = store_thm("HD",   --`!(x:'a) l. HD (CONS x l) = x`--,
   REWRITE_TAC[listTheory.HD]);

val TL = store_thm("TL",   --`!(x:'a) l. TL (CONS x l) = l`--,
   REWRITE_TAC[listTheory.TL]);




(*----------------------------------------------------------------*)
(*- Alternative list constructor---adding element to the tail end-*)
(*----------------------------------------------------------------*)


val SNOC = save_thm("SNOC", listTheory.SNOC)


(*-------------------------------------------------------------- *)
(* Reductions                                                    *)
(* Spec:                                                         *)
(*      FOLDR f [x0;x1;...;xn-1] e = f(x0,f(x1,...f(xn-1,e)...)) *)
(*      FOLDL f e [x0;x1;...;xn-1] = f(...f(f(e,x0),x1),...xn-1) *)
(*-------------------------------------------------------------- *)
val FOLDR = save_thm("FOLDR", listTheory.FOLDR);
val FOLDL = save_thm("FOLDL", listTheory.FOLDL);



(*--------------------------------------------------------------*)
(* Filter                                                       *)
(* Spec:                                                        *)
(*      FILTER P [x0; ...; xn-1] = [...;xi;...]                 *)
(*        where P xi holds for all xi in the resulting list     *)
(*--------------------------------------------------------------*)
val FILTER = save_thm("FILTER", listTheory.FILTER);



(*--------------------------------------------------------------*)
(* Cumulation                                                   *)
(*--------------------------------------------------------------*)
val SCANL = new_list_rec_definition("SCANL",
    (--`(!f e. SCANL (f:'b->'a->'b) e [] = [e]) /\
        (!f e x l. SCANL f e (CONS x l) = CONS e (SCANL f (f e x) l))`--));

val SCANR = new_list_rec_definition("SCANR",
    (--`(!f e. SCANR (f:'a->'b->'b) e [] = [e]) /\
        (!f e x l. SCANR (f:'a->'b->'b) e (CONS x l) =
           CONS (f x (HD (SCANR f e l))) (SCANR f e l))`--));


(*--------------------------------------------------------------*)
(* Concatenation of two lists                                   *)
(* Spec:                                                        *)
(*   APPEND [x0;...;xn-1] [x'0;...;x'm-1] =                     *)
(*       [x0;...;xn-1;x'0;...;x'm-1]                            *)
(*--------------------------------------------------------------*)

val APPEND = store_thm("APPEND",
  --`(!l:'a list.    APPEND [] l = l) /\
     (!l1 l2 (x:'a). APPEND (CONS x l1) l2 = CONS x (APPEND l1 l2))`--,
  REWRITE_TAC[listTheory.APPEND]);

(*--------------------------------------------------------------*)
(* Concatenation of a list of lists                             *)
(* Spec:                                                        *)
(*      FLAT [[x00;...;x0n-1];...;[xp-10;...;xp-1n-1]] =        *)
(*              [x00;...;x0n-1;...;xp-10;...;xp-1n-1]           *)
(*--------------------------------------------------------------*)

val FLAT = store_thm("FLAT",
 --`((FLAT:'a list list -> 'a list) [] = []) /\
    (!(x:'a list) l. FLAT (CONS x l) = APPEND x (FLAT l))`--,
 REWRITE_TAC[listTheory.FLAT]);

(*--------------------------------------------------------------*)
(* Concatenation of a list of lists                             *)
(* Spec:                                                        *)
(*  LENGTH [x0;...;xn-1] = n                                    *)
(*--------------------------------------------------------------*)

val LENGTH = store_thm("LENGTH",
 --`(           LENGTH ([]:'a list) = 0) /\
    (!(x:'a) l. LENGTH (CONS x l) = SUC (LENGTH l))`--,
 REWRITE_TAC[listTheory.LENGTH]);

(*--------------------------------------------------------------*)
(* Apply a function to all elements of a list                   *)
(* Spec:                                                        *)
(*  MAP f [x0;...;xn-1] = [f x0;...; f xn-1]                    *)
(*--------------------------------------------------------------*)

val MAP = store_thm("MAP",
 --`(!(f:'a -> 'b). MAP f [] = []) /\
    (!f (x:'a) l. MAP f (CONS x l) = CONS ((f x):'b) (MAP f l))`--,
 REWRITE_TAC[listTheory.MAP]);

(* ---------------------------------------------------------------------*)
(* Definition of a function                                             *)
(*                                                                      *)
(*   MAP2 : ('a -> 'b -> 'c) -> 'a list ->  'b list ->  'c list         *)
(*                                                                      *)
(* for mapping a curried binary function down a pair of lists:          *)
(*                                                                      *)
(* |- (!f. MAP2 f[][] = []) /\                                          *)
(*   (!f x1 l1 x2 l2.                                                   *)
(*      MAP2 f(CONS x1 l1)(CONS x2 l2) = CONS(f x1 x2)(MAP2 f 11 l2))   *)
(*                                                                      *)
(* [TFM 92.04.21]                                                       *)
(* ---------------------------------------------------------------------*)

val MAP2 = store_thm("MAP2",
 --`(!(f:'a->'b->'c). MAP2 f [] [] = []) /\
    (!(f:'a->'b->'c) x1 l1 x2 l2.
       MAP2 f(CONS x1 l1)(CONS x2 l2) = CONS(f x1 x2)(MAP2 f l1 l2))`--,
 REWRITE_TAC[listTheory.MAP2]);

(*--------------------------------------------------------------*)
(* Predicates                                                   *)
(* Spec:                                                        *)
(*   ALL_EL P [x0;...;xn-1] = T, iff P xi = T for i=0,...,n-1   *)
(*                            F, otherwise                      *)
(*--------------------------------------------------------------*)

(* alias "ALL_EL" to EVERY in list theory *)
val ALL_EL = save_thm("ALL_EL", listTheory.EVERY_DEF);
val _ = overload_on("ALL_EL", ``EVERY``);
val _ = overload_on("EVERY", ``EVERY``);

(*--------------------------------------------------------------*)
(* Spec:                                                        *)
(*   SOME_EL P [x0;...;xn-1] = T, iff P xi = T for some i       *)
(*                             F, otherwise                     *)
(*--------------------------------------------------------------*)

(* alias "SOME_EL" to EXISTS in list theory *)
val SOME_EL = save_thm("SOME_EL", listTheory.EXISTS_DEF);
val _ = overload_on("SOME_EL", ``EXISTS``);
val _ = overload_on("EXISTS", ``EXISTS``);

(*--------------------------------------------------------------*)
(* Spec:                                                        *)
(*   IS_EL x [x0;...;xn-1] = T, iff ?xi. x = xi for i=0,...,n-1 *)
(*                            F, otherwise                      *)
(*--------------------------------------------------------------*)

(* overload "IS_EL" to listTheory$MEM, and prove this next theorem
   as consequence *)
val _ = overload_on("IS_EL", ``list$MEM``);
val _ = overload_on("MEM", ``list$MEM``);
val IS_EL_DEF = store_thm(
  "IS_EL_DEF",
  ``!(x:'a) l. IS_EL x l = SOME_EL ($= x) l``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [SOME_EL, listTheory.MEM]);

val AND_EL_DEF = new_definition("AND_EL_DEF", ``AND_EL = ALL_EL I``);

val OR_EL_DEF = new_definition("OR_EL_DEF", ``OR_EL = SOME_EL I``);

(*--------------------------------------------------------------*)
(* Segments                                                     *)
(* Spec:                                                        *)
(*      FIRSTN m [x0;...;xn-1] = [x0;...;xm-1]                  *)
(*      BUTFIRSTN m [x0;...;xn-1] = [xm;...;xn-1]               *)
(*      LASTN m [x0;...;xn-1] = [xn-m;...;xn-1]                 *)
(*      BUTLASTN m [x0;...;xn-1] = [x0;...;xn-m]                *)
(*      BUTLAST [x0;...;xn-1] = [x0;...;xn-2]                   *)
(*      LAST [x0;...;xn-1] = [xn-1]                             *)
(*--------------------------------------------------------------*)

open BasicProvers
val _ = overload_on ("FIRSTN", ``list$TAKE``)
val _ = overload_on ("TAKE", ``list$TAKE``)
           (* makes TAKE preferred printing form *)

val FIRSTN = store_thm(
  "FIRSTN",
  ``(!l : 'a list.     FIRSTN 0 l = []) /\
    (!n x l : 'a list. FIRSTN (SUC n) (CONS x l) = CONS x (FIRSTN n l))``,
  SRW_TAC [][]);

val _ = overload_on ("BUTFIRSTN", ``list$DROP``)
val _ = overload_on ("DROP", ``list$DROP``)

val BUTFIRSTN = store_thm(
  "BUTFIRSTN",
  ``(!l : 'a list.     BUTFIRSTN 0 l = l) /\
    (!n x l : 'a list. BUTFIRSTN (SUC n) (CONS x l) = BUTFIRSTN n l)``,
  SRW_TAC [][]);

(*----------------------------------------------------------------*)
(*- Segment                                                     -*)
(*- Spec:                                                       -*)
(*-     SEG m k [x0,...xk,...xk+m-1,...,xn] = [xk,...,xk+m-1]   -*)
(*----------------------------------------------------------------*)
val SEG =
    let val SEG_exists = prove(
    (--`?SEG. (!k (l:'a list). SEG 0 k l = []) /\
       (!m x l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
       (!m k x l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)`--),
    EXISTS_TAC (--`\m k (l:'a list). (FIRSTN:num -> 'a list -> 'a list) m
        ((BUTFIRSTN:num -> 'a list -> 'a list) k l)`--)
    THEN BETA_TAC THEN REWRITE_TAC[FIRSTN,BUTFIRSTN])
    in
    Rsyntax.new_specification{name = "SEG",
                      sat_thm = SEG_exists,
                      consts =  [{const_name = "SEG", fixity = NONE}]
                     }
    end;

(*----------------------------------------------------------------*)
(*- LAST and BUTLAST is analogous to HD and TL at the end of list-*)
(*----------------------------------------------------------------*)

open BasicProvers

(* establish BUTLAST as an alias for FRONT *)
val _ = overload_on("BUTLAST", ``FRONT``);
val _ = overload_on("FRONT", ``FRONT``);

val LENGTH_SNOC = save_thm("LENGTH_SNOC", listTheory.LENGTH_SNOC)
val LAST = save_thm("LAST", listTheory.LAST_SNOC)
val BUTLAST = save_thm("BUTLAST", listTheory.FRONT_SNOC)

val LASTN =
    let val thm1 = prove_rec_fn_exists num_Axiom
        (--`(lastn 0 (l:('a)list) = []) /\
         (lastn (SUC n) l = SNOC (LAST l) (lastn n (BUTLAST l)))`--)
    val thm = prove(
        (--`?lastn. (!l:'a list. lastn 0 l = []) /\
         (!n (x:'a) l. lastn (SUC n) (SNOC x l) = SNOC x (lastn n l))`--),
        STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC (--`lastn:num->('a)list->('a)list`--)
        THEN ASM_REWRITE_TAC[LAST,BUTLAST])
   in
    Rsyntax.new_specification{name = "LASTN",
                      sat_thm = thm,
                      consts =  [{const_name = "LASTN", fixity = NONE}]
                     }
   end;

val BUTLASTN =
    let val thm1 = prove_rec_fn_exists num_Axiom
        (--`(butlastn 0 l = (l:('a)list)) /\
         (butlastn (SUC n) l = butlastn n (BUTLAST l))`--)
    val thm = prove(
        (--`?butlastn. (!l:'a list. butlastn 0 l = l) /\
         (!n (x:'a) l. butlastn (SUC n) (SNOC x l) = butlastn n l)`--),
        STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC (--`butlastn:num->('a)list->('a)list`--)
        THEN ASM_REWRITE_TAC[BUTLAST])
    in
    Rsyntax.new_specification{name = "BUTLASTN",
                      sat_thm = thm,
                      consts =  [{const_name = "BUTLASTN", fixity = NONE}]
                     }
    end;

(*--------------------------------------------------------------*)
(* Index of elements                                            *)
(* Spec:                                                        *)
(*      EL k [x0;...xk;...;xn-1] = xk                           *)
(*      ELL k [xn-1;...xk;...;x0] = xk                          *)
(*--------------------------------------------------------------*)


val EL = store_thm("EL",
--`(!l:'a list. EL 0 l = HD l) /\
   (!n (l:'a list). EL (SUC n) l = EL n (TL l))`--,
  REWRITE_TAC[listTheory.EL]);

val ELL = new_recursive_definition
      {name = "ELL",
       rec_axiom = num_Axiom,
       def = --`(!l:'a list. ELL 0 (l:'a list) = LAST l) /\
                (!l:'a list. ELL (SUC n) l = ELL n (BUTLAST l))`--};


(*--------------------------------------------------------------*)
(* Predicates between lists                                     *)
(* Spec:                                                        *)
(*      IS_PREFIX l1 l2 = T, iff ?l. l1 = APPEND l2 l           *)
(*      IS_SUFFIX l1 l2 = T, iff ?l. l1 = APPEND l l2           *)
(*      IS_SUBLIST l1 l2 = T,                                   *)
(*                  iff ?l l'. l1 = APPEND l (APPEND l2 l')     *)
(*                                                              *)
(*      SPLITP P [x0;...xk;...;xn-1] =                          *)
(*           ([x0;...;x(k-1)],[xk;...;xn-1])                    *)
(*              where P xi = F for all i < k and P xk = T       *)
(*                                                              *)
(*      PREFIX P [x0;...xk;...;xn-1] = [x0;...xk-1]             *)
(*              where P xk = F and P xi = T for i = 0,...,k-1   *)
(*      SUFFIX P [x0;...xk;...;xn-1] = [xk+1;...xn-1]           *)
(*              where P xk = F and P xi = T for i = k+1,...,n-1 *)
(*--------------------------------------------------------------*)

val _ = overload_on ("IS_PREFIX", ``\x y. isPREFIX y x``)
val _ = remove_ovl_mapping "<<=" {Name="isPREFIX", Thy = "list"}
val _ = overload_on ("<<=", ``\x y. isPREFIX x y``)
(* second call makes the infix the preferred printing form *)

val IS_PREFIX = save_thm("IS_PREFIX",
  let val [c1,c2,c3] = CONJUNCTS listTheory.isPREFIX_THM
  in
      LIST_CONJ [GEN ``l:'a list`` c1,
                 (CONV_RULE (RENAME_VARS_CONV ["x", "l"]) o
                  GENL [``h:'a``, ``t:'a list``]) c2,
                 (CONV_RULE (RENAME_VARS_CONV ["x1", "l1", "x2", "l2"]) o
                  GENL [``h2:'a``, ``t2:'a list``, ``h1:'a``, ``t1:'a list``] o
                  CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])))
                 c3]
  end)

(*---------------------------------------------------------------*)

val SNOC_APPEND = save_thm("SNOC_APPEND", listTheory.SNOC_APPEND);
val REVERSE_DEF = listTheory.REVERSE_DEF
val REVERSE_REVERSE = listTheory.REVERSE_REVERSE

val REVERSE = save_thm ( "REVERSE", listTheory.REVERSE_SNOC_DEF );
val REVERSE_SNOC = save_thm ("REVERSE_SNOC", listTheory.REVERSE_SNOC);

val REVERSE_APPEND = save_thm("REVERSE_APPEND", listTheory.REVERSE_APPEND);

val REVERSE_REVERSE = save_thm("REVERSE_REVERSE", REVERSE_REVERSE);

val SNOC_Axiom = save_thm("SNOC_Axiom", listTheory.SNOC_Axiom);

val NOT_NULL_SNOC = store_thm(
  "NOT_NULL_SNOC",
  (--`!(x:'a) l. ~NULL(SNOC x l)`--),
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,NULL_DEF])

val IS_SUFFIX = let
  val lemma = prove(
    (--`?fn.
           (!l. fn l [] = T) /\
           (!(x:'a) l. fn [] (SNOC x l) = F) /\
           (!(x1:'a) l1 (x2:'a) l2. fn (SNOC x1 l1) (SNOC x2 l2) =
                                      (x1 = x2) /\ (fn l1 l2))`--),
    let val th = prove_rec_fn_exists SNOC_Axiom
          (--`(fn l [] = T) /\
              (fn l (SNOC (x:'a) t) =
                (if (NULL l) then F else ((LAST l) = x) /\ (fn (BUTLAST l) t)))`--)
    in
        STRIP_ASSUME_TAC th THEN
        EXISTS_TAC (--`fn:'a list -> 'a list -> bool`--)
        THEN ASM_REWRITE_TAC[BUTLAST,LAST,NULL_DEF,NOT_NULL_SNOC]
    end)
  in
    Rsyntax.new_specification
        {consts = [{const_name = "IS_SUFFIX", fixity = NONE}],
         name = "IS_SUFFIX",
         sat_thm = lemma
        }
  end;

val IS_SUBLIST =
    let val lemma = prove(
        (--`?fn. (!l:'a list. fn l [] = T) /\
          (!(x:'a) l. fn [] (CONS x l) = F) /\
          (!x1 l1 x2 l2. fn (CONS x1 l1) (CONS x2 l2) =
           ((x1 = x2) /\ (IS_PREFIX l1 l2)) \/ (fn l1 (CONS x2 l2)))`--),
        let val th = prove_rec_fn_exists list_Axiom
            (--`(fn [] (l:'a list) = (if NULL l then T else F)) /\
             (fn (CONS x t) l =
                (if (NULL l) then T else
                 (((x = (HD l)) /\ (IS_PREFIX t (TL l))) \/ (fn t l))))`--)
        in
        STRIP_ASSUME_TAC th THEN EXISTS_TAC (--`fn:'a list -> 'a list -> bool`--)
        THEN ASM_REWRITE_TAC[HD,TL,NULL_DEF]
        THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HD,TL,NULL_DEF]
        end)
    in
    Rsyntax.new_specification
        {consts = [{const_name = "IS_SUBLIST", fixity = NONE}],
         name = "IS_SUBLIST",
         sat_thm = lemma
        }
    end;

val SPLITP = new_recursive_definition
      {name = "SPLITP",
       rec_axiom = list_Axiom,
       def = --`(!P. SPLITP P [] = ([],[])) /\
                (!P x l. SPLITP P (CONS (x:'a) l) =
                  (if P x then ([], CONS x l) else
                    ((CONS x (FST(SPLITP P l))), (SND (SPLITP P l)))))`--};

val PREFIX_DEF = new_definition("PREFIX_DEF",
    (--`PREFIX P (l:'a list) = FST (SPLITP ($~ o P) l)`--));

val SUFFIX_DEF = new_definition("SUFFIX_DEF",
    (--`!P (l:'a list). SUFFIX P l = FOLDL (\l' x. if P x then SNOC x l' else []) [] l`--));

(*--------------------------------------------------------------*)
(* List of pairs                                                *)
(* Spec:                                                        *)
(*  ZIP([x0;...;xn-1],[y0;...;yn-1]) = [(x0,y0;...;(xn-1,yn-1)] *)
(*  UNZIP[(x0,y0;...;(xn-1,yn-1)]=([x0;...;xn-1],[y0;...;yn-1]) *)
(*  UNZIP_FST [(x0,y0;...;(xn-1,yn-1)] = [x0;...;xn-1]          *)
(*  UNZIP_SND [(x0,y0;...;(xn-1,yn-1)] = [y0;...;yn-1]          *)
(*--------------------------------------------------------------*)

val ZIP = listTheory.ZIP;
val UNZIP = listTheory.UNZIP;

val UNZIP_FST_DEF = new_definition("UNZIP_FST_DEF",
    (--`!l:('a#'b)list. UNZIP_FST l = FST(UNZIP l)`--));

val UNZIP_SND_DEF = new_definition("UNZIP_SND_DEF",
    (--`!l:('a#'b)list. UNZIP_SND l = SND(UNZIP l)`--));




(*--------------------------------------------------------------*)
(* List of natural numbers                                      *)
(* Spec:                                                        *)
(*  SUM [x0;...;xn-1] = x0 + ... + xn-1                         *)
(*--------------------------------------------------------------*)

val SUM = store_thm("SUM",
--`(SUM [] = 0) /\ (!x l. SUM (CONS x l) = x + SUM l)`--,
 REWRITE_TAC[listTheory.SUM]);

(*--------------------------------------------------------------*)
(* List generator                                               *)
(* Spec:                                                        *)
(*  REPLICATE n x = [x;....;x] (n repeate elements)             *)
(*  COUNT_LIST n = [0;....;n-1]                                 *)
(*--------------------------------------------------------------*)

val GENLIST = save_thm("GENLIST",listTheory.GENLIST);

val REPLICATE = new_recursive_definition
      {name = "REPLICATE",
       rec_axiom =  num_Axiom,
       def = --`(REPLICATE 0 (x:'a) = []) /\
                (REPLICATE (SUC n) x = CONS x (REPLICATE n x))`--};

val COUNT_LIST = Lib.with_flag (computeLib.auto_import_definitions, false)
  TotalDefn.Define`
   (COUNT_LIST 0 = []) /\
   (COUNT_LIST (SUC n) = 0::MAP SUC (COUNT_LIST n))`;




(* Some tail recursive versions -- for evaluation *)

val SPLITP_AUX_def = TotalDefn.Define`
  (SPLITP_AUX acc P [] = (acc,[])) /\
  (SPLITP_AUX acc P (h::t) =
    if P h then
      (acc, h::t)
    else
      SPLITP_AUX (acc ++ [h]) P t)`;

val COUNT_LIST_AUX_def = TotalDefn.Define`
  (COUNT_LIST_AUX 0 l = l) /\
  (COUNT_LIST_AUX (SUC n) l = COUNT_LIST_AUX n (n::l))`;

(* --------------------------------------------------------------------------
 * Theorems from the basic list theory.
 *---------------------------------------------------------------------------*)

val NULL = store_thm ("NULL",
 --`NULL (NIL :'a list) /\ (!x l. ~NULL(CONS (x:'a) l))`--,
   REWRITE_TAC [listTheory.NULL]);


val list_CASES = save_thm ("list_CASES", listTheory.list_CASES);

val CONS_11 = store_thm("CONS_11",
 --`!(x:'a) l x' l'. (CONS x l = CONS x' l') = (x = x') /\ (l = l')`--,
 REWRITE_TAC[listTheory.CONS_11]);


val NOT_NIL_CONS = store_thm("NOT_NIL_CONS",
 --`!(x:'a) l. ~([] = CONS x l)`--,
 REWRITE_TAC[listTheory.NOT_NIL_CONS]);


(* !x l. ~(CONS x l = [])   *)
val NOT_CONS_NIL = save_thm("NOT_CONS_NIL",
   CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);


val LIST_NOT_EQ = store_thm("LIST_NOT_EQ",
 --`!l1 l2. ~(l1 = l2) ==> !x1:'a. !x2. ~(CONS x1 l1 = CONS x2 l2)`--,
 REWRITE_TAC[listTheory.LIST_NOT_EQ]);


val NOT_EQ_LIST = store_thm("NOT_EQ_LIST",
 --`!x1:'a. !x2. ~(x1 = x2) ==> !l1 l2. ~(CONS x1 l1 = CONS x2 l2)`--,
 REWRITE_TAC[listTheory.NOT_EQ_LIST]);


val EQ_LIST = store_thm("EQ_LIST",
 --`!x1:'a.!x2.(x1=x2) ==> !l1 l2. (l1 = l2) ==> (CONS x1 l1 = CONS x2 l2)`--,
 REWRITE_TAC[listTheory.EQ_LIST]);

(*    CONS |- !l. ~(NULL l) ==> (CONS (HD l) (TL l) = l) *)
val CONS = save_thm("CONS", listTheory.CONS);

(* APPEND_ASSOC |- !l1 l2 l3.APPEND l1(APPEND l2 l3) = APPEND(APPEND l1 l2)3 *)
val APPEND_ASSOC = save_thm("APPEND_ASSOC", listTheory.APPEND_ASSOC);

(*  LENGTH_APPEND |- !l1 l2. LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2 *)
val LENGTH_APPEND = save_thm("LENGTH_APPEND", listTheory.LENGTH_APPEND);

(* MAP_APPEND |- !f l1 l2. MAP f(APPEND l1 l2) = APPEND(MAP f l1) (MAP f l2) *)
val MAP_APPEND = save_thm("MAP_APPEND", listTheory.MAP_APPEND);

(*    LENGTH_MAP |- !l f. LENGTH (MAP f l) = LENGTH l *)
val LENGTH_MAP = save_thm("LENGTH_MAP", listTheory.LENGTH_MAP);

(* Deleted by Paul Curzon, for some reason
 * (*    EVERY_EL |- !l P. EVERY P l = (!n. n < LENGTH l ==> P (EL n l)) *)
 * val EVERY_EL = save_thm("EVERY_EL", listTheory.EVERY_EL);
 *
 * (*    EVERY_CONJ |- !l. EVERY (\x. P x /\ Q x) l = EVERY P l /\ EVERY Q l *)
 * val EVERY_CONJ = save_thm("EVERY_CONJ", listTheory.EVERY_CONJ);
 *****************************************************************************)

(*    LENGTH_NIL |- !l. (LENGTH l = 0) = l = [] *)
val LENGTH_NIL = save_thm("LENGTH_NIL", listTheory.LENGTH_NIL);

val LENGTH_CONS = store_thm("LENGTH_CONS",
 --`!l n. (LENGTH l = SUC n) =
          ?x:'a. ?l'. (LENGTH l' = n) /\ (l = CONS x l')`--,
 REWRITE_TAC[listTheory.LENGTH_CONS]);

(*
val LENGTH_EQ_SUC = store_thm("LENGTH_EQ_SUC",
 --`!(P:'a list->bool)  (n:num).
      (!l. (LENGTH l = SUC n) ==> P l) =
      (!l. (LENGTH l = n) ==> (\l. !x:'a. P (CONS x l)) l)`--,
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH],
     DISCH_TAC THEN
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [LENGTH,NOT_NIL_CONS,NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      ASM_REWRITE_TAC [LENGTH,INV_SUC_EQ,CONS_11] THEN
      REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);
*)

(* val LENGTH_EQ_CONS = save_thm("LENGTH_EQ_CONS",
                              listTheory.LENGTH_EQ_CONS);
*)

(*    LENGTH_EQ_NIL |- !P. (!l. (LENGTH l = 0) ==> P l) = P [] *)
val LENGTH_EQ_NIL = save_thm("LENGTH_EQ_NIL", listTheory.LENGTH_EQ_NIL);



(* Added by PC 11 May 94 *)
val LENGTH_MAP2 = store_thm("LENGTH_MAP2",
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     (!f:'a->'b->'c. (LENGTH(MAP2 f l1 l2) = LENGTH l1) /\
      (LENGTH(MAP2 f l1 l2) = LENGTH l2))`--),
    LIST_INDUCT_TAC THENL[
      LIST_INDUCT_TAC THENL[
        DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
        THEN REWRITE_TAC[LENGTH],
        GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
        THEN REWRITE_TAC[SUC_NOT]],
      GEN_TAC THEN LIST_INDUCT_TAC THENL[
        PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[NOT_SUC],
        GEN_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
        THEN PURE_ONCE_REWRITE_TAC[LENGTH]
        THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ]
        THEN DISCH_TAC THEN RES_THEN ASSUME_TAC THEN GEN_TAC
        THEN CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);

(*-==============================================================-*)
(*- More Theorems about lists                                    -*)
(*-==============================================================-*)

val NULL_EQ_NIL = store_thm ("NULL_EQ_NIL",
    (--`!l:('a)list .  NULL l = (l = [])`--),
    GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `l` list_CASES)
    THEN REWRITE_TAC [NULL,NOT_CONS_NIL]);

val LENGTH_EQ = store_thm ("LENGTH_EQ",
    (--`! (x:'a list) y. (x = y) ==> (LENGTH x = LENGTH y)`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []);

val LENGTH_NOT_NULL = store_thm("LENGTH_NOT_NULL",
    (--`!(l:('a)list). (0 < LENGTH l) = (~(NULL l))`--),
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC [LENGTH,NULL,NOT_LESS_0],
      REWRITE_TAC [LENGTH,NULL,LESS_0]]);

val SNOC_INDUCT = save_thm("SNOC_INDUCT", listTheory.SNOC_INDUCT);
val SNOC_CASES =  save_thm("SNOC_CASES", listTheory.SNOC_CASES);

val NOT_NULL_SNOC = prove(
    (--`!(x:'a) l. ~NULL(SNOC x l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,NULL]);

(* NOT_NIL_SNOC = |- !x l. ~([] = SNOC x l) *)
val NOT_NIL_SNOC = store_thm("NOT_NIL_SNOC",
    (--`!(x:'a) l. ~([] = SNOC x l)`--),
   REWRITE_TAC (map valOf (prove_constructors_distinct SNOC_Axiom)));

(* NOT_SNOC_NIL = |- !x l. ~(SNOC x l = []) *)
val NOT_SNOC_NIL = save_thm("NOT_SNOC_NIL",
    GSYM NOT_NIL_SNOC);

val SNOC_11 =  save_thm("SNOC_11",
                        valOf (hd (prove_constructors_one_one SNOC_Axiom)));

val SNOC_EQ_LENGTH_EQ = store_thm ("SNOC_EQ_LENGTH_EQ",
    (--`!x1 (l1:('a)list) x2 l2.
         ((SNOC x1 l1) = (SNOC x2 l2)) ==> (LENGTH l1 = LENGTH l2)`--),
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (AP_TERM (--`LENGTH:('a)list -> num`--))
    THEN RULE_ASSUM_TAC(REWRITE_RULE [LENGTH_SNOC,LENGTH,EQ_MONO_ADD_EQ,ADD1])
    THEN FIRST_ASSUM ACCEPT_TAC);

val SNOC_REVERSE_CONS = store_thm ("SNOC_REVERSE_CONS",
   (--`!(x:'a) l. (SNOC x l) = REVERSE (CONS x (REVERSE l))`--),
  let val th =
    GEN_ALL (REWRITE_RULE [REVERSE_REVERSE]
     (AP_TERM (--`REVERSE:('a)list -> ('a)list`--) (SPEC_ALL REVERSE_SNOC)))
  in
    REWRITE_TAC[th]
  end);

val MAP_SNOC  = save_thm("MAP_SNOC", listTheory.MAP_SNOC);

val FOLDR_SNOC = store_thm("FOLDR_SNOC",
    (--`!(f:'a->'b->'b) e x l. FOLDR f e (SNOC x l) = FOLDR f (f x e) l`--),
    REPEAT (FILTER_GEN_TAC (--`l:'a list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,FOLDR]
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);

val FOLDL_SNOC = save_thm("FOLDL_SNOC", listTheory.FOLDL_SNOC);

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

val FOLDR_FOLDL = store_thm("FOLDR_FOLDL",
    (--`!(f:'a->'a->'a) e. MONOID f e ==> !l. FOLDR f e l = FOLDL f e l`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[MONOID_DEF,ASSOC_DEF,LEFT_ID_DEF,RIGHT_ID_DEF]
    THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL, FOLDR]
    THEN FIRST_ASSUM SUBST1_TAC THEN GEN_TAC
    THEN SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--)) THEN SNOC_INDUCT_TAC THENL[
      ASM_REWRITE_TAC[FOLDL],
      PURE_ONCE_REWRITE_TAC[FOLDL_SNOC] THEN GEN_TAC
      THEN ASM_REWRITE_TAC[]]);

val LENGTH_FOLDR = store_thm("LENGTH_FOLDR",
    (--`!l:'a list. LENGTH l = FOLDR (\x l'. SUC l') 0 l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,FOLDR]
    THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]);

val LENGTH_FOLDL = store_thm("LENGTH_FOLDL",
    (--`!l:'a list. LENGTH l = FOLDL (\l' x. SUC l') 0 l`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC,FOLDL_SNOC] THENL[
      REWRITE_TAC[LENGTH,FOLDL],
      CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
      THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
      THEN ASM_REWRITE_TAC[]]);

val MAP_FOLDR = store_thm("MAP_FOLDR",
    (--`!(f:'a->'b) l. MAP f l = FOLDR (\x l'. CONS (f x) l') [] l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,FOLDR]
    THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]);

val MAP_FOLDL = store_thm("MAP_FOLDL",
    (--`!(f:'a->'b) l. MAP f l = FOLDL (\l' x. SNOC (f x) l') [] l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[MAP_SNOC,FOLDL_SNOC] THENL[
      REWRITE_TAC[FOLDL,MAP],
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC (DEPTH_CONV BETA_CONV)
      THEN GEN_TAC THEN REFL_TAC]);

val MAP_o = save_thm("MAP_o", listTheory.MAP_o);

val MAP_MAP_o = save_thm("MAP_MAP_o", listTheory.MAP_MAP_o);

val FILTER_FOLDR = store_thm("FILTER_FOLDR",
    (--`!P (l:'a list). FILTER P l = FOLDR (\x l'. if P x then CONS x l' else l') [] l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER,FOLDR]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]);

val FILTER_SNOC = store_thm("FILTER_SNOC",
    (--`!P (x:'a) l. FILTER P (SNOC x l) =
        (if P x then SNOC x (FILTER P l) else FILTER P l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER,SNOC]
    THEN GEN_TAC THEN REPEAT COND_CASES_TAC
    THEN ASM_REWRITE_TAC[SNOC]);

val FILTER_FOLDL = store_thm("FILTER_FOLDL",
    (--`!P (l:'a list). FILTER P l = FOLDL (\l' x. if P x then SNOC x l' else l') [] l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[FILTER,FOLDL],
      REWRITE_TAC[FILTER_SNOC,FOLDL_SNOC]
      THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);

val FILTER_COMM = store_thm("FILTER_COMM",
    (--`!f1 f2 (l:'a list). FILTER f1 (FILTER f2 l) = FILTER f2 (FILTER f1 l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);

val FILTER_IDEM = store_thm("FILTER_IDEM",
    (--`!f (l:'a list). FILTER f (FILTER f l) = FILTER f l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);

val FILTER_MAP = store_thm("FILTER_MAP",
    (--`!f1 (f2:'a->'b) (l:'a list).
     FILTER f1 (MAP f2 l) = MAP f2 (FILTER (f1 o f2) l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER,MAP]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[o_THM]
    THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER,MAP]);

val LENGTH_FILTER_LEQ = Q.store_thm("LENGTH_FILTER_LEQ",
  `!P l. LENGTH (FILTER P l) <= LENGTH l`,
  Induct_on `l`
  THEN SRW_TAC [] [numLib.DECIDE ``!a b. a <= b ==> a <= SUC b``]);

val EL_FILTER = Q.prove(
  `!i l P. i < LENGTH (FILTER P l) ==> P (EL i (FILTER P l))`,
  Induct_on `l`
  THEN SRW_TAC [] []
  THEN Cases_on `i`
  THEN SRW_TAC [numSimps.ARITH_ss] []);

val FILTER_EQ_lem = Q.prove(
  `!l l2 P h. ~P h ==> (FILTER P l <> h :: l2)`,
  SRW_TAC [] [listTheory.LIST_EQ_REWRITE]
  THEN Cases_on `LENGTH (FILTER P l) = 0`
  THEN SRW_TAC [] []
  THEN DISJ2_TAC
  THEN Q.EXISTS_TAC `0`
  THEN SRW_TAC [numSimps.ARITH_ss] []
  THEN `0 < LENGTH (FILTER P l)` by numLib.DECIDE_TAC
  THEN IMP_RES_TAC EL_FILTER
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN metisLib.METIS_TAC []);

val FILTER_EQ = Q.store_thm("FILTER_EQ",
  `!P1 P2 l.
     (FILTER P1 l = FILTER P2 l) =
     (!x. MEM x l ==> (P1 x = P2 x))`,
  Induct_on `l` THEN SRW_TAC [] [] THEN metisLib.METIS_TAC [FILTER_EQ_lem]);

(*- 18 Nov. 93 -*)
val LENGTH_SEG = store_thm("LENGTH_SEG",
    (--`!n k (l:'a list). ((n + k) <= (LENGTH l)) ==> (LENGTH (SEG n k l) = n)`--),
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[SEG,LENGTH],
      REWRITE_TAC[SEG,LENGTH],
      LIST_INDUCT_TAC THENL[
        REWRITE_TAC[LENGTH,ADD_0,LESS_OR_EQ,NOT_SUC,NOT_LESS_0],
        REWRITE_TAC[SEG,LENGTH,ADD,LESS_EQ_MONO,INV_SUC_EQ]
        THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o (SPEC (--`0`--)))],
      LIST_INDUCT_TAC THENL[
        REWRITE_TAC[LENGTH,ADD,LESS_OR_EQ,NOT_SUC,NOT_LESS_0],
        REWRITE_TAC[LENGTH,SEG,(GSYM ADD_SUC),LESS_EQ_MONO]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);

val APPEND_NIL = store_thm("APPEND_NIL",
    (--`(!l:('a)list . APPEND l [] = l) /\ (!l:('a)list . APPEND [] l = l)`--),
    CONJ_TAC THENL
       [LIST_INDUCT_TAC,ALL_TAC] THEN ASM_REWRITE_TAC [APPEND]);

val APPEND_SNOC = save_thm("APPEND_SNOC", listTheory.APPEND_SNOC);

val APPEND_FOLDR = store_thm("APPEND_FOLDR",
    (--`!(l1:'a list) l2. APPEND l1 l2  = FOLDR CONS l2 l1`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND,FOLDR]);

val APPEND_FOLDL = store_thm("APPEND_FOLDL",
    (--`!(l1:'a list) l2. APPEND l1 l2  = FOLDL (\l' x. SNOC x l') l1 l2`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
     REWRITE_TAC[APPEND_NIL,FOLDL],
     ASM_REWRITE_TAC[APPEND_SNOC,FOLDL_SNOC] THEN GEN_TAC
     THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN REFL_TAC]);

val FOLDR_APPEND = store_thm("FOLDR_APPEND",
    (--`!(f:'a->'b->'b) e l1 l2.
     FOLDR f e (APPEND l1 l2) = FOLDR f (FOLDR f e l2) l1`--),
    FORALL_PERM_TAC[(--`l2:'a list`--)] THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[APPEND_NIL,FOLDR],
      REWRITE_TAC[APPEND_SNOC,FOLDR_SNOC] THEN REPEAT GEN_TAC
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val FOLDL_APPEND = store_thm("FOLDL_APPEND",
    (--`!(f:'a->'b->'a) e l1 l2.
     FOLDL f e (APPEND l1 l2) = FOLDL f (FOLDL f e l1) l2`--),
    FORALL_PERM_TAC[(--`l1:'b list`--)] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[APPEND,FOLDL] THEN REPEAT GEN_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);


val CONS_APPEND = store_thm("CONS_APPEND",
    (--`!(x:'a) l. CONS x l = APPEND [x] l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[APPEND_NIL],
      ASM_REWRITE_TAC[APPEND_SNOC,(GSYM(CONJUNCT2 SNOC))]]);

val ASSOC_APPEND = store_thm ("ASSOC_APPEND",
    (--`ASSOC (APPEND:'a list -> 'a list -> 'a list)`--),
    REWRITE_TAC[ASSOC_DEF,APPEND_ASSOC]);

val RIGHT_ID_APPEND_NIL = prove(
    (--`RIGHT_ID APPEND ([]:'a list)`--),
    REWRITE_TAC[RIGHT_ID_DEF,APPEND,APPEND_NIL]);

val LEFT_ID_APPEND_NIL = prove(
    (--`LEFT_ID APPEND ([]:'a list)`--),
    REWRITE_TAC[LEFT_ID_DEF,APPEND,APPEND_NIL]);

val MONOID_APPEND_NIL = store_thm ("MONOID_APPEND_NIL",
    (--`MONOID APPEND ([]:'a list)`--),
    REWRITE_TAC[MONOID_DEF,APPEND,APPEND_NIL,APPEND_ASSOC,
            LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF]);

val APPEND_LENGTH_EQ = save_thm("APPEND_LENGTH_EQ", listTheory.APPEND_LENGTH_EQ)
val APPEND_11_LENGTH = save_thm ("APPEND_11_LENGTH",
                                 listTheory.APPEND_11_LENGTH)

val FILTER_APPEND = store_thm("FILTER_APPEND",
    (--`!f l1 (l2:'a list).
     FILTER f (APPEND l1 l2) = APPEND (FILTER f l1) (FILTER f l2)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER,APPEND]
    THEN REPEAT GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[APPEND]);

val FLAT_SNOC = store_thm("FLAT_SNOC",
    (--`!(x:'a list) l. FLAT (SNOC x l) = APPEND (FLAT l) x`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT,SNOC,APPEND,APPEND_NIL,APPEND_ASSOC]);

val FLAT_FOLDR = store_thm("FLAT_FOLDR",
    (--`!l:'a list list. FLAT l = FOLDR APPEND [] l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,FOLDR]);

val FLAT_FOLDL = store_thm("FLAT_FOLDL",
    (--`!l:'a list list. FLAT l = FOLDL APPEND [] l`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[FLAT,FOLDL],
      ASM_REWRITE_TAC[FLAT_SNOC,FOLDL_SNOC]]);

val LENGTH_FLAT = store_thm("LENGTH_FLAT",
    (--`!l:'a list list. LENGTH(FLAT l) = SUM (MAP LENGTH l)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[FLAT] THENL[
      REWRITE_TAC[LENGTH,MAP,SUM],
      ASM_REWRITE_TAC[LENGTH_APPEND,MAP,SUM]]);

val REVERSE_FOLDR = store_thm("REVERSE_FOLDR",
    (--`!l:'a list. REVERSE l = FOLDR SNOC [] l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE,FOLDR]);

val REVERSE_FOLDL = store_thm("REVERSE_FOLDL",
    (--`!l:'a list. REVERSE l = FOLDL (\l' x. CONS x l') [] l`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[REVERSE,FOLDL],
      REWRITE_TAC[REVERSE_SNOC,FOLDL_SNOC]
      THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);

val LENGTH_REVERSE = save_thm("LENGTH_REVERSE", listTheory.LENGTH_REVERSE)

val REVERSE_EQ_NIL = save_thm("REVERSE_EQ_NIL", listTheory.REVERSE_EQ_NIL)

val ALL_EL_SNOC = save_thm("ALL_EL_SNOC", listTheory.EVERY_SNOC);

val ALL_EL_CONJ = store_thm("ALL_EL_CONJ",
     (--`!P Q l. ALL_EL (\x:'a. P x /\ Q x) l = (ALL_EL P l /\ ALL_EL Q l)`--),
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [ALL_EL] THEN BETA_TAC
     THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN FIRST_ASSUM ACCEPT_TAC);

val ALL_EL_MAP = store_thm("ALL_EL_MAP",
    (--`!P (f:'a->'b) l. ALL_EL P (MAP f l) = ALL_EL (P o f) l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC [ALL_EL,MAP] THEN ASM_REWRITE_TAC [o_DEF]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val ALL_EL_APPEND = store_thm("ALL_EL_APPEND",
    (--`!P (l1:('a)list) l2.
     (ALL_EL P (APPEND l1 l2)) = ((ALL_EL P l1) /\ (ALL_EL P l2))`--),
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND,ALL_EL]
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [CONJ_ASSOC]);

val SOME_EL_SNOC = save_thm("SOME_EL_SNOC", listTheory.EXISTS_SNOC);

val NOT_ALL_EL_SOME_EL = store_thm("NOT_ALL_EL_SOME_EL",
    (--`!P (l:'a list). ~(ALL_EL P l) = SOME_EL ($~ o P) l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,SOME_EL]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM,o_THM]
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);

val NOT_SOME_EL_ALL_EL = store_thm("NOT_SOME_EL_ALL_EL",
    (--`!P (l:'a list). ~(SOME_EL P l) = ALL_EL ($~ o P) l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,SOME_EL]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM,o_THM]
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);

val IS_EL = store_thm("IS_EL",
    (--`(!x:'a. IS_EL x[] = F) /\
     (!(y:'a) x l. IS_EL y(CONS x l) = (y = x) \/ IS_EL y l)`--),
    REWRITE_TAC[IS_EL_DEF,SOME_EL] THEN REPEAT GEN_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN REFL_TAC);

val IS_EL_SNOC = save_thm("IS_EL_SNOC", listTheory.MEM_SNOC);

val SUM_SNOC = save_thm("SUM_SNOC", listTheory.SUM_SNOC);

val SUM_FOLDR = store_thm("SUM_FOLDR",
    (--`!l:num list. SUM l = FOLDR $+ 0 l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[SUM,FOLDR,ADD]
    THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);

val SUM_FOLDL = store_thm("SUM_FOLDL",
    (--`!l:num list. SUM l = FOLDL $+ 0 l`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[SUM,FOLDL],
      REWRITE_TAC[SUM_SNOC,FOLDL_SNOC]
      THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
      THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC]);


val IS_PREFIX_APPEND = store_thm("IS_PREFIX_APPEND",
    (--`!l1 l2:'a list. (IS_PREFIX l1 l2 = (?l. l1 = APPEND l2 l))`--),
    LIST_INDUCT_TAC THENL[
     LIST_INDUCT_TAC THENL[
      REWRITE_TAC[IS_PREFIX,APPEND]
      THEN EXISTS_TAC (--`[]:'a list`--) THEN REFL_TAC,
      REWRITE_TAC[IS_PREFIX,APPEND,GSYM NOT_CONS_NIL]],
     GEN_TAC THEN LIST_INDUCT_TAC THENL[
      REWRITE_TAC[IS_PREFIX,APPEND]
      THEN EXISTS_TAC (--`CONS (x:'a) l1`--) THEN REFL_TAC,
(* **list_Axiom** variable dependancy *)
(*      THEN EXISTS_TAC (--`CONS (h:'a) l1`--) THEN REFL_TAC, *)
      ASM_REWRITE_TAC[IS_PREFIX,APPEND,CONS_11] THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);

val IS_SUFFIX_APPEND = store_thm("IS_SUFFIX_APPEND",
    (--`!l1 l2:'a list. (IS_SUFFIX l1 l2 = (?l. l1 = APPEND l l2))`--),
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[IS_SUFFIX,APPEND_NIL]
      THEN EXISTS_TAC (--`[]:'a list`--) THEN REFL_TAC,
      REWRITE_TAC[IS_SUFFIX,APPEND_SNOC]
      THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
      THEN REWRITE_TAC[GSYM NULL_EQ_NIL,NOT_NULL_SNOC]],
     GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[IS_SUFFIX,APPEND_NIL]
      THEN EXISTS_TAC (--`SNOC (x:'a) l1`--) THEN REFL_TAC,
      ASM_REWRITE_TAC[IS_SUFFIX,APPEND_SNOC,SNOC_11] THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);

val IS_SUBLIST_APPEND = store_thm("IS_SUBLIST_APPEND",
 --`!l1 l2:'a list. IS_SUBLIST l1 l2 = (?l l'. l1 = APPEND l(APPEND l2 l'))`--,
    let val NOT_NIL_APPEND_CONS2 = prove(
        (--`!l1 (l2:'a list) x. ~([] = (APPEND l1 (CONS x l2)))`--),
        LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN REPEAT GEN_TAC
        THEN MATCH_ACCEPT_TAC (GSYM NOT_CONS_NIL))
   in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'a list`--))
    THEN LIST_INDUCT_TAC THENL[
        REWRITE_TAC[IS_SUBLIST,APPEND]
        THEN MAP_EVERY EXISTS_TAC [(--`[]:'a list`--), (--`[]:'a list`--)]
        THEN REWRITE_TAC[APPEND],
        GEN_TAC THEN REWRITE_TAC[IS_SUBLIST,APPEND,NOT_NIL_APPEND_CONS2],
        REWRITE_TAC[IS_SUBLIST,APPEND]
        THEN MAP_EVERY EXISTS_TAC [(--`[x]:'a list`--), (--`l1:'a list`--)]
(* **list_Axiom** variable dependancy *)
(*      THEN MAP_EVERY EXISTS_TAC [(--`[h]:'a list`--), (--`l1:'a list`--)] *)
        THEN MATCH_ACCEPT_TAC CONS_APPEND,
        GEN_TAC THEN REWRITE_TAC[IS_SUBLIST] THEN EQ_TAC
        THEN ONCE_ASM_REWRITE_TAC[IS_PREFIX_APPEND] THENL[
          STRIP_TAC THENL[
            MAP_EVERY EXISTS_TAC [(--`[]:'a list`--), (--`l:'a list`--)]
            THEN ASM_REWRITE_TAC[APPEND],
            MAP_EVERY EXISTS_TAC [(--`(CONS x l):'a list`--),
                                  (--`l':'a list`--)]
(* **list_Axiom** variable dependancy *)
(*          MAP_EVERY EXISTS_TAC [(--`(CONS h l):'a list`--),
                                  (--`l':'a list`--)] *)
            THEN ONCE_ASM_REWRITE_TAC[APPEND] THEN REFL_TAC],
          CONV_TAC LEFT_IMP_EXISTS_CONV THEN LIST_INDUCT_TAC THENL[
            REWRITE_TAC[APPEND,CONS_11] THEN STRIP_TAC THEN DISJ1_TAC
            THEN ASM_REWRITE_TAC[IS_PREFIX_APPEND]
            THEN EXISTS_TAC (--`l':'a list`--) THEN REFL_TAC,
            GEN_TAC THEN REWRITE_TAC[APPEND,CONS_11]
            THEN STRIP_TAC THEN DISJ2_TAC
            THEN MAP_EVERY EXISTS_TAC [(--`l:'a list`--), (--`l':'a list`--)]
            THEN FIRST_ASSUM ACCEPT_TAC]]]
    end);

val IS_PREFIX_IS_SUBLIST = store_thm("IS_PREFIX_IS_SUBLIST",
    (--`!l1 l2:'a list. IS_PREFIX l1 l2 ==> IS_SUBLIST l1 l2`--),
    LIST_INDUCT_TAC THEN TRY (FILTER_GEN_TAC (--`l2:'a list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[IS_PREFIX,IS_SUBLIST]
    THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);

val IS_SUFFIX_IS_SUBLIST = store_thm("IS_SUFFIX_IS_SUBLIST",
    (--`!l1 l2:'a list. IS_SUFFIX l1 l2 ==> IS_SUBLIST l1 l2`--),
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND,IS_SUBLIST_APPEND]
    THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN MAP_EVERY EXISTS_TAC [(--`l:'a list`--), (--`[]:'a list`--)]
    THEN REWRITE_TAC[APPEND_NIL]);

val IS_PREFIX_REVERSE = store_thm("IS_PREFIX_REVERSE",
--`!l1 l2:'a list. IS_PREFIX (REVERSE l1) (REVERSE l2) = IS_SUFFIX l1 l2`--,
    let val NOT_NIL_APPEND_SNOC2 = prove(
        (--`!l1 (l2:'a list) x. ~([] = (APPEND l1 (SNOC x l2)))`--),
        LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND_SNOC] THEN REPEAT GEN_TAC
        THEN MATCH_ACCEPT_TAC NOT_NIL_SNOC)
    in
    SNOC_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'a list`--))
    THEN SNOC_INDUCT_TAC THENL[
        REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE,IS_PREFIX]
        THEN EXISTS_TAC (--`[]:'a list`--) THEN REWRITE_TAC[APPEND],
        GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE,REVERSE_SNOC,
                                 IS_PREFIX]
        THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC
        THEN REWRITE_TAC[APPEND,NOT_NIL_APPEND_SNOC2],
        REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE,APPEND_NIL,IS_PREFIX]
        THEN EXISTS_TAC (--`SNOC (x:'a) l1`--) THEN REFL_TAC,
        GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE_SNOC,IS_PREFIX]
        THEN PURE_ONCE_ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[IS_SUFFIX_APPEND,APPEND_SNOC,SNOC_11]
        THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN REFL_TAC]
    end);

val IS_SUFFIX_REVERSE = save_thm("IS_SUFFIX_REVERSE",
 (* `!l1 l2:'a list. IS_SUFFIX (REVERSE l1) (REVERSE l2) = IS_PREFIX l1 l2` *)
    GEN_ALL(SYM (REWRITE_RULE[REVERSE_REVERSE]
    (SPECL [(--`REVERSE(l1:'a list)`--), (--`REVERSE(l2:'a list)`--)]
           IS_PREFIX_REVERSE))));

val IS_SUFFIX_CONS2_E = store_thm(
  "IS_SUFFIX_CONS2_E",
  ``IS_SUFFIX s (h::t) ==> IS_SUFFIX s t``,
  SRW_TAC [][IS_SUFFIX_APPEND] THEN
  metisLib.METIS_TAC [listTheory.APPEND, listTheory.APPEND_ASSOC]);

val IS_SUFFIX_REFL = store_thm(
  "IS_SUFFIX_REFL",
  ``IS_SUFFIX l l``,
  SRW_TAC [][IS_SUFFIX_APPEND] THEN
  metisLib.METIS_TAC [listTheory.APPEND]);
val _ = export_rewrites ["IS_SUFFIX_REFL"]


val IS_SUBLIST_REVERSE = store_thm("IS_SUBLIST_REVERSE",
--`!l1 l2:'a list. IS_SUBLIST (REVERSE l1) (REVERSE l2) = IS_SUBLIST l1 l2`--,
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUBLIST_APPEND]
    THEN EQ_TAC THEN STRIP_TAC THENL[
      MAP_EVERY EXISTS_TAC [(--`REVERSE(l':'a list)`--),
                            (--`REVERSE(l:'a list)`--)]
      THEN FIRST_ASSUM (SUBST1_TAC o
         (REWRITE_RULE[REVERSE_REVERSE,REVERSE_APPEND]) o
         (AP_TERM (--`REVERSE:'a list -> 'a list`--)))
      THEN REWRITE_TAC[APPEND_ASSOC],
      FIRST_ASSUM SUBST1_TAC
      THEN REWRITE_TAC[REVERSE_APPEND,APPEND_ASSOC]
      THEN MAP_EVERY EXISTS_TAC [(--`REVERSE(l':'a list)`--),
                                 (--`REVERSE(l:'a list)`--)]
      THEN REFL_TAC]);

val PREFIX_FOLDR = store_thm("PREFIX_FOLDR",
--`!P (l:'a list). PREFIX P l = FOLDR (\x l'. if P x then CONS x l' else []) [] l`--,
    GEN_TAC THEN  REWRITE_TAC[PREFIX_DEF]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDR,SPLITP]
    THEN GEN_TAC THEN REWRITE_TAC[o_THM] THEN BETA_TAC
    THEN ASM_CASES_TAC (--`(P:'a->bool) x`--) THEN ASM_REWRITE_TAC[]);
(* **list_Axiom** variable dependancy *)
(*    THEN ASM_CASES_TAC (--`(P:'a->bool) h`--) THEN ASM_REWRITE_TAC[]); *)

val PREFIX = store_thm("PREFIX",
   (--`(!P:'a->bool. PREFIX P [] = []) /\
    (!P (x:'a) l. PREFIX P (CONS x l) = (if P x then CONS x (PREFIX P l) else []))`--),
    REWRITE_TAC[PREFIX_FOLDR,FOLDR]
    THEN REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);

val IS_PREFIX_PREFIX = store_thm("IS_PREFIX_PREFIX",
    (--`!P (l:'a list). IS_PREFIX l (PREFIX P l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[IS_PREFIX,PREFIX]
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_PREFIX]);

val LENGTH_SCANL = store_thm("LENGTH_SCANL",
    (--`!(f:'b->'a->'b) e l. LENGTH(SCANL f e l) = SUC (LENGTH l)`--),
    FORALL_PERM_TAC [(--`l:'a list`--)] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SCANL,LENGTH]
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);

val LENGTH_SCANR = store_thm("LENGTH_SCANR",
    (--`!(f:'a->'b->'b) e l. LENGTH(SCANR f e l) = SUC (LENGTH l)`--),
    FORALL_PERM_TAC [(--`l:'a list`--)] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SCANR] THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[LENGTH]);


val COMM_MONOID_FOLDL = store_thm("COMM_MONOID_FOLDL",
    (--`!f:'a->'a->'a. COMM f ==>
      !e'. MONOID f e' ==>
       (!e l. FOLDL f e l = f e (FOLDL f e' l))`--),
    REWRITE_TAC[MONOID_DEF,ASSOC_DEF,LEFT_ID_DEF,COMM_DEF]
    THEN REPEAT STRIP_TAC THEN SPEC_TAC ((--`e:'a`--),(--`e:'a`--))
    THEN SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--))
    THEN LIST_INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[FOLDL] THENL[
      GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM),
      REPEAT GEN_TAC THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC[t])
      THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC[t])
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM)] );

val COMM_MONOID_FOLDR = store_thm("COMM_MONOID_FOLDR",
    (--`!f:'a->'a->'a. COMM f ==>
      !e'. (MONOID f e') ==>
       (!e l. FOLDR f e l = f e (FOLDR f e' l))`--),
    REWRITE_TAC[MONOID_DEF,ASSOC_DEF,LEFT_ID_DEF,COMM_DEF]
    THEN GEN_TAC THEN DISCH_THEN
      (fn th_sym => GEN_TAC THEN DISCH_THEN
        (fn th_assoc_etc =>
                let val th_assoc = CONJUNCT1 th_assoc_etc
                    val th_ident = CONJUNCT2(CONJUNCT2 th_assoc_etc)
                in
                GEN_TAC THEN LIST_INDUCT_TAC
                THEN PURE_ONCE_REWRITE_TAC[FOLDR] THENL[
                 PURE_ONCE_REWRITE_TAC[th_sym]
                 THEN MATCH_ACCEPT_TAC (GSYM th_ident),
                 REPEAT GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
                 THEN PURE_ONCE_REWRITE_TAC[th_ident]
                 THEN PURE_ONCE_REWRITE_TAC[th_assoc]
                 THEN AP_THM_TAC THEN AP_TERM_TAC
                 THEN MATCH_ACCEPT_TAC (GSYM th_sym)]
                end)) );


val FCOMM_FOLDR_APPEND = store_thm("FCOMM_FOLDR_APPEND",
--`!(g:'a->'a->'a) (f:'b->'a->'a).
   FCOMM g f
   ==> !e. LEFT_ID g e
       ==> !l1 l2. FOLDR f e (APPEND l1 l2)
                 = g (FOLDR f e l1) (FOLDR f e l2)`--,
    REWRITE_TAC[FCOMM_DEF,LEFT_ID_DEF] THEN REPEAT GEN_TAC
    THEN REPEAT DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND,FOLDR]);

val FCOMM_FOLDL_APPEND = store_thm("FCOMM_FOLDL_APPEND",
--`!(f:'a->'b->'a) (g:'a->'a->'a). FCOMM f g ==>
   !e. RIGHT_ID g e ==>
   !l1 l2. FOLDL f e (APPEND l1 l2) = g (FOLDL f e l1) (FOLDL f e l2)`--,
    REWRITE_TAC[FCOMM_DEF,RIGHT_ID_DEF] THEN REPEAT GEN_TAC
    THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN GEN_TAC
    THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[APPEND_NIL,APPEND_SNOC,FOLDL_SNOC,FOLDL]);


val MONOID_FOLDR_APPEND_FOLDR = prove(
    (--`!(f:'a->'a->'a) e. MONOID f e ==>
     (!l1 l2. FOLDR f e (APPEND l1 l2) = f (FOLDR f e l1) (FOLDR f e l2))`--),
    REWRITE_TAC[MONOID_DEF,GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);

val MONOID_FOLDL_APPEND_FOLDL = prove(
    (--`!(f:'a->'a->'a) e. MONOID f e ==>
      (!l1 l2. FOLDL f e (APPEND l1 l2) = f (FOLDL f e l1) (FOLDL f e l2))`--),
    REWRITE_TAC[MONOID_DEF,GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);


val FOLDL_SINGLE = store_thm("FOLDL_SINGLE",
    (--`!(f:'a->'b->'a) e x. FOLDL f e [x] = f e x`--),
    REWRITE_TAC[FOLDL]);

val FOLDR_SINGLE = store_thm("FOLDR_SINGLE",
    (--`!(f:'a->'b->'b) e x. FOLDR f e [x] = f x e`--),
    REWRITE_TAC[FOLDR]);


val FOLDR_CONS_NIL = store_thm("FOLDR_CONS_NIL",
    (--`!(l:'a list). FOLDR CONS [] l = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDR]);

val FOLDL_SNOC_NIL = store_thm("FOLDL_SNOC_NIL",
    (--`!(l:'a list). FOLDL (\xs x. SNOC x xs) [] l = l`--),
    SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL,FOLDL_SNOC]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val FOLDR_FOLDL_REVERSE = store_thm("FOLDR_FOLDL_REVERSE",
    (--`!(f:'a->'b->'b) e l.
       FOLDR f e l = FOLDL (\x y. f y x) e (REVERSE l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDR,FOLDL,REVERSE,FOLDL_SNOC]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val FOLDL_FOLDR_REVERSE = store_thm("FOLDL_FOLDR_REVERSE",
    (--`!(f:'a->'b->'a) e l.
       FOLDL f e l = FOLDR (\x y. f y x) e (REVERSE l)`--),
    GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,FOLDR,FOLDL,REVERSE_SNOC,FOLDR_SNOC]
    THEN BETA_TAC THEN ASM_REWRITE_TAC[FOLDL_SNOC]);

val FOLDR_REVERSE = store_thm("FOLDR_REVERSE",
    (--`!(f:'a->'b->'b) e l.
       FOLDR f e (REVERSE l) = FOLDL (\x y. f y x) e l`--),
    REWRITE_TAC[FOLDR_FOLDL_REVERSE,REVERSE_REVERSE]);

val FOLDL_REVERSE = store_thm("FOLDL_REVERSE",
    (--`!(f:'a->'b->'a) e l.
       FOLDL f e (REVERSE l) = FOLDR (\x y. f y x) e l`--),
    REWRITE_TAC[FOLDL_FOLDR_REVERSE,REVERSE_REVERSE]);


val FOLDR_MAP = store_thm("FOLDR_MAP",
    (--`!(f:'a->'a->'a) e (g:'b ->'a) l.
       FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDL,MAP,FOLDR] THEN BETA_TAC
    THEN REWRITE_TAC[]);

val FOLDL_MAP = store_thm("FOLDL_MAP",
    (--`!(f:'a->'a->'a) e (g:'b ->'a) l.
       FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[MAP,FOLDL,FOLDL_SNOC,MAP_SNOC,FOLDR]
    THEN BETA_TAC THEN REWRITE_TAC[]);


val ALL_EL_FOLDR = store_thm("ALL_EL_FOLDR",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDR (\x l'. P x /\ l') T l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL_EL,FOLDR,MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val ALL_EL_FOLDL = store_thm("ALL_EL_FOLDL",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDL (\l' x. l' /\ P x) T l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[ALL_EL,FOLDL,MAP],
      ASM_REWRITE_TAC[ALL_EL_SNOC,FOLDL_SNOC,MAP_SNOC]]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val SOME_EL_FOLDR = store_thm("SOME_EL_FOLDR",
    (--`!P (l:'a list). SOME_EL P l = FOLDR (\x l'. P x \/ l') F l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SOME_EL,MAP,FOLDR] THEN
    BETA_TAC THEN REWRITE_TAC[]);

val SOME_EL_FOLDL = store_thm("SOME_EL_FOLDL",
    (--`!P (l:'a list). SOME_EL P l = FOLDL (\l' x. l' \/ P x) F l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[SOME_EL,MAP,FOLDL],
      REWRITE_TAC[SOME_EL_SNOC,MAP_SNOC,FOLDL_SNOC]
      THEN BETA_TAC THEN GEN_TAC
      THEN FIRST_ASSUM SUBST1_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM] );

val ALL_EL_FOLDR_MAP = store_thm("ALL_EL_FOLDR_MAP",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDR $/\  T (MAP P l)`--),
    REWRITE_TAC[ALL_EL_FOLDR,FOLDR_MAP]);

val ALL_EL_FOLDL_MAP = store_thm("ALL_EL_FOLDL_MAP",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDL $/\  T (MAP P l)`--),
    REWRITE_TAC[ALL_EL_FOLDL,FOLDL_MAP]);

val SOME_EL_FOLDR_MAP = store_thm("SOME_EL_FOLDR_MAP",
    (--`!(P:'a->bool) l. SOME_EL P l = FOLDR $\/ F (MAP P l)`--),
    REWRITE_TAC[SOME_EL_FOLDR,FOLDR_MAP]);

val SOME_EL_FOLDL_MAP = store_thm("SOME_EL_FOLDL_MAP",
    (--`!(P:'a->bool) l. SOME_EL P l = FOLDL $\/ F (MAP P l)`--),
    REWRITE_TAC[SOME_EL_FOLDL,FOLDL_MAP]);


val FOLDR_FILTER = store_thm("FOLDR_FILTER",
    (--`!(f:'a->'a->'a) e (P:'a -> bool) l.
       FOLDR f e (FILTER P l) = FOLDR (\x y. if P x then f x y else y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDL, FILTER, FOLDR] THEN BETA_TAC
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FOLDR]);

val FOLDL_FILTER = store_thm("FOLDL_FILTER",
    (--`!(f:'a->'a->'a) e (P:'a -> bool) l.
       FOLDL f e (FILTER P l) = FOLDL (\x y. if P y then f x y else x) e l`--),
     GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
     THEN ASM_REWRITE_TAC[FOLDL,FOLDR_SNOC,FOLDL_SNOC,FILTER,FOLDR,FILTER_SNOC]
     THEN BETA_TAC THEN GEN_TAC THEN COND_CASES_TAC
     THEN ASM_REWRITE_TAC[FOLDL_SNOC]);

val ASSOC_FOLDR_FLAT = store_thm("ASSOC_FOLDR_FLAT",
    (--`!(f:'a->'a->'a). ASSOC f ==>
     (! e. LEFT_ID f e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR f e (MAP (FOLDR f e) l)))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,MAP,FOLDR]
    THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);

val ASSOC_FOLDL_FLAT = store_thm("ASSOC_FOLDL_FLAT",
    (--`!(f:'a->'a->'a). ASSOC f ==>
     (! e. RIGHT_ID f e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL f e (MAP (FOLDL f e) l)))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT_SNOC,MAP_SNOC,MAP,FLAT,FOLDL_SNOC]
    THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);

val MAP_FLAT = store_thm("MAP_FLAT",
    (--`!(f:'a->'b) l. MAP f (FLAT l) = FLAT (MAP  (MAP f) l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,MAP,MAP_APPEND]);

val FILTER_FLAT = store_thm("FILTER_FLAT",
    (--`!(P:'a->bool) l. FILTER P (FLAT l) = FLAT (MAP (FILTER P) l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[FLAT,MAP,FILTER,FILTER_APPEND]);


val SOME_EL_MAP = store_thm("SOME_EL_MAP",
    (--`!P (f:'a->'b) l. SOME_EL P (MAP f l) = SOME_EL (P o f) l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL[
      REWRITE_TAC [SOME_EL,MAP],
      REWRITE_TAC [SOME_EL,MAP] THEN ASM_REWRITE_TAC [o_DEF]
      THEN BETA_TAC THEN REWRITE_TAC[]]);


val SOME_EL_APPEND = store_thm("SOME_EL_APPEND",
    (--`!P (l1:('a)list) l2.
     (SOME_EL P (APPEND l1 l2)) = ((SOME_EL P l1) \/ (SOME_EL P l2))`--),
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND,SOME_EL]
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [DISJ_ASSOC]);

val SOME_EL_DISJ = store_thm("SOME_EL_DISJ",
    (--`!P Q (l:'a list).
     SOME_EL (\x. P x \/ Q x) l = SOME_EL P l \/ SOME_EL Q l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SOME_EL] THEN GEN_TAC THEN BETA_TAC
    THEN POP_ASSUM SUBST1_TAC THEN CONV_TAC (AC_CONV (DISJ_ASSOC,DISJ_SYM)));

val IS_EL_APPEND = store_thm("IS_EL_APPEND",
    (--`!(l1:('a)list) l2 x.
     (IS_EL x (APPEND l1 l2)) = ((IS_EL x l1) \/ (IS_EL x l2))`--),
    REWRITE_TAC[IS_EL_DEF,SOME_EL_APPEND]);

val IS_EL_FOLDR = store_thm("IS_EL_FOLDR",
    (--`!(y:'a) l. IS_EL y l = FOLDR (\x l'. (y = x) \/ l') F l`--),
    REWRITE_TAC[IS_EL_DEF, SOME_EL_FOLDR,FOLDR_MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val IS_EL_FOLDL = store_thm("IS_EL_FOLDL",
    (--`!(y:'a) l. IS_EL y l = FOLDL (\l' x. l' \/ (y = x)) F l`--),
    REWRITE_TAC[IS_EL_DEF,SOME_EL_FOLDL,FOLDL_MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val NULL_FOLDR = store_thm("NULL_FOLDR",
    (--`!(l:'a list). NULL l = FOLDR (\x l'. F) T l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[NULL_DEF,FOLDR]);


val NULL_FOLDL = store_thm("NULL_FOLDL",
    (--`!(l:'a list). NULL l = FOLDL (\x l'. F) T l`--),
    SNOC_INDUCT_TAC THEN
    REWRITE_TAC[NULL_DEF,FOLDL_SNOC,NULL_EQ_NIL,FOLDL, GSYM NOT_NIL_SNOC]);


val MAP_REVERSE = store_thm("MAP_REVERSE",
    (--`!(f:'a -> 'b) l. MAP f (REVERSE l) = REVERSE (MAP f l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE,MAP,MAP_SNOC]);

val FILTER_REVERSE = store_thm("FILTER_REVERSE",
    (--`!(P:'a -> bool) l. FILTER P (REVERSE l) = REVERSE (FILTER P l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,FILTER,FILTER_SNOC]
    THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REVERSE]);

val SEG_LENGTH_ID = store_thm("SEG_LENGTH_ID",
    (--`!l:'a list. SEG (LENGTH l) 0 l = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,SEG]);

val SEG_SUC_CONS = store_thm("SEG_SUC_CONS",
    (--`!m n l (x:'a). (SEG m (SUC n) (CONS x l) = SEG m n l)`--),
    INDUCT_TAC THEN REWRITE_TAC[SEG]);

val SEG_0_SNOC = store_thm("SEG_0_SNOC",
--`!m l (x:'a). (m <= (LENGTH l)) ==> (SEG m 0 (SNOC x l) = SEG m 0 l)`--,
    INDUCT_TAC THENL[
        REWRITE_TAC[SEG],
        LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH] THENL[
            REWRITE_TAC[LESS_OR_EQ,NOT_SUC,NOT_LESS_0],
            REWRITE_TAC[SNOC,SEG,LESS_EQ_MONO]
            THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val BUTLASTN_SEG = store_thm("BUTLASTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (BUTLASTN n l = SEG (LENGTH l - n) 0 l)`--),
    INDUCT_TAC THEN REWRITE_TAC[BUTLASTN,SUB_0,SEG_LENGTH_ID]
    THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,BUTLASTN] THENL[
        REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
        THEN MATCH_MP_TAC (GSYM SEG_0_SNOC)
        THEN MATCH_ACCEPT_TAC SUB_LESS_EQ]);

val LASTN_CONS = store_thm("LASTN_CONS",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (!x. LASTN n (CONS x l) = LASTN n l)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN] THEN SNOC_INDUCT_TAC THENL[
        REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LENGTH_SNOC,(GSYM(CONJUNCT2 SNOC)),LESS_EQ_MONO]
        THEN REPEAT STRIP_TAC THEN RES_TAC
        THEN ASM_REWRITE_TAC[LASTN]]);

val LENGTH_LASTN = store_thm("LENGTH_LASTN",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> (LENGTH (LASTN n l) = n)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN,LENGTH] THEN SNOC_INDUCT_TAC
    THENL[
        REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LENGTH_SNOC,LASTN,LESS_EQ_MONO]
        THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC]);

val LASTN_LENGTH_ID = store_thm("LASTN_LENGTH_ID",
    (--`!l:'a list. LASTN (LENGTH l) l = l`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,LASTN]
    THEN GEN_TAC THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val LASTN_LASTN = store_thm("LASTN_LASTN",
    (--`!l:'a list.!n m. (m <= LENGTH l) ==>
    (n <= m) ==> (LASTN n (LASTN m l) = LASTN n l)`--),
    SNOC_INDUCT_TAC THENL[
        REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0]
        THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC
        THEN REWRITE_TAC[NOT_LESS_0,LASTN],
        GEN_TAC THEN REPEAT INDUCT_TAC
        THEN REWRITE_TAC[LENGTH_SNOC,LASTN,LESS_EQ_MONO,ZERO_LESS_EQ] THENL[
            REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
            REPEAT DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val NOT_SUC_LESS_EQ_0 = prove((--`!n. ~(SUC n <= 0)`--),
    REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC]);

val FIRSTN_LENGTH_ID = store_thm("FIRSTN_LENGTH_ID",
    (--`!l:'a list. FIRSTN (LENGTH l) l = l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,FIRSTN]
    THEN GEN_TAC THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val FIRSTN_SNOC = store_thm("FIRSTN_SNOC",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (!x. FIRSTN n (SNOC x l) = FIRSTN n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FIRSTN,LENGTH] THENL[
        REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LESS_EQ_MONO,SNOC,FIRSTN]
        THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]);

val BUTLASTN_LENGTH_NIL = store_thm("BUTLASTN_LENGTH_NIL",
    (--`!l:'a list. BUTLASTN (LENGTH l) l = []`--),
    SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,BUTLASTN]);

val BUTLASTN_SUC_BUTLAST = store_thm("BUTLASTN_SUC_BUTLAST",
    (--`!n (l:('a)list). (n < (LENGTH l)) ==>
     (BUTLASTN (SUC n) l =  BUTLASTN n (BUTLAST l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0,BUTLASTN,BUTLAST]);

val BUTLASTN_BUTLAST = store_thm("BUTLASTN_BUTLAST",
    (--`!n (l:('a)list). (n < (LENGTH l)) ==>
     (BUTLASTN n (BUTLAST l) = BUTLAST (BUTLASTN n l))`--),
    INDUCT_TAC THEN REWRITE_TAC[BUTLASTN] THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_LESS_0,
        LESS_MONO_EQ,BUTLASTN,BUTLAST]
    THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SUC_BUTLAST
    THEN RES_TAC);

val LENGTH_BUTLASTN = store_thm("LENGTH_BUTLASTN",
    (--`!n (l:('a)list). (n <= LENGTH l) ==>
     (LENGTH (BUTLASTN n l) = LENGTH l - n)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[BUTLASTN,SUB_0] THENL[
        REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,SUB_MONO_EQ]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val ADD_SUC_lem =
   let val l = CONJUNCTS ADD_CLAUSES
   in
        GEN_ALL (TRANS (el 4 l) (SYM (el 3 l)))
   end ;

val BUTLASTN_BUTLASTN = store_thm("BUTLASTN_BUTLASTN",
    (--`!m n (l:'a list).  ((n + m) <= LENGTH l) ==>
     (BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l)`--),
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,ADD,ADD_0,BUTLASTN] THENL[
        REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,ADD_SUC_lem]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val APPEND_BUTLASTN_LASTN = store_thm ("APPEND_BUTLASTN_LASTN",
    (--`!n (l:('a)list) . (n <= LENGTH l) ==>
     (APPEND (BUTLASTN n l) (LASTN n l) = l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[BUTLASTN,LASTN,APPEND,APPEND_NIL] THENL[
        REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
        REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,APPEND_SNOC]
        THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC]);


val APPEND_FIRSTN_LASTN = store_thm("APPEND_FIRSTN_LASTN",
  (--`!m n (l:'a list). ((m + n) = (LENGTH l)) ==>
         (APPEND (FIRSTN n l) (LASTN m l) = l)`--),
    let val ADD_EQ_LESS_EQ = prove((--`!m n p. ((n + m) = p) ==> (m <= p)`--),
      REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM)
      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
      THEN MATCH_ACCEPT_TAC LESS_EQ_ADD)
    in
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,ADD,ADD_0,FIRSTN,LASTN,
        APPEND,APPEND_NIL,SUC_NOT,NOT_SUC] THENL[
        GEN_TAC THEN DISCH_THEN SUBST1_TAC
        THEN SUBST1_TAC (SYM(SPEC_ALL LENGTH_SNOC))
        THEN MATCH_ACCEPT_TAC FIRSTN_LENGTH_ID,
        PURE_ONCE_REWRITE_TAC[INV_SUC_EQ] THEN GEN_TAC
        THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LASTN_LENGTH_ID],
        PURE_ONCE_REWRITE_TAC[INV_SUC_EQ,ADD_SUC_lem,APPEND_SNOC]
        THEN REPEAT STRIP_TAC THEN IMP_RES_TAC ADD_EQ_LESS_EQ
        THEN IMP_RES_TAC FIRSTN_SNOC THEN RES_TAC
        THEN ASM_REWRITE_TAC[]]
    end);

val BUTLASTN_APPEND2 = store_thm ("BUTLASTN_APPEND2",
    (--`!n l1 (l2:'a list). (n <= LENGTH l2) ==>
     (BUTLASTN n (APPEND l1 l2) = APPEND l1 (BUTLASTN n l2))`--),
    INDUCT_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTLASTN,NOT_SUC_LESS_EQ_0,APPEND_SNOC]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO]);

(*--------------------------------------------------------------------------*)
(* !l2 l1. BUTLASTN (LENGTH l2) (APPEND l1 l2) = l1                         *)
(*--------------------------------------------------------------------------*)

val BUTLASTN_LENGTH_APPEND = save_thm("BUTLASTN_LENGTH_APPEND",
    GENL[(--`l2:'a list`--),(--`l1:'a list`--)]
     (REWRITE_RULE[LESS_EQ_REFL,BUTLASTN_LENGTH_NIL,APPEND_NIL]
     (SPECL[(--`LENGTH (l2:'a list)`--),(--`l1:'a list`--),(--`l2:'a list`--)]
           BUTLASTN_APPEND2)));

val LASTN_LENGTH_APPEND = store_thm("LASTN_LENGTH_APPEND",
    (--`!(l2:'a list) l1. LASTN (LENGTH l2) (APPEND l1 l2) = l2`--),
    SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,APPEND,APPEND_SNOC,LASTN]
    THEN ASM_REWRITE_TAC[BUTLAST,LAST,SNOC_APPEND]);

val BUTLASTN_CONS = store_thm("BUTLASTN_CONS",
    (--`!n l. (n <= (LENGTH l)) ==>
     (!x:'a. BUTLASTN n(CONS x l) = CONS x(BUTLASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,BUTLASTN,GSYM(CONJUNCT2 SNOC)]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO]);

(* added by Michael Norrish, 15 Feb 2000 *)
val LAST_CONS = save_thm("LAST_CONS", listTheory.LAST_CONS);
val BUTLAST_CONS = save_thm("BUTLAST_CONS", listTheory.FRONT_CONS);

(*  |- !l x. BUTLASTN(LENGTH l)(CONS x l) = [x] *)
val BUTLASTN_LENGTH_CONS = save_thm("BUTLASTN_LENGTH_CONS",
    let val thm1 =
     SPECL [(--`LENGTH (l:'a list)`--),(--`l:'a list`--)] BUTLASTN_CONS
    in
    GEN_ALL(REWRITE_RULE[LESS_EQ_REFL,BUTLASTN_LENGTH_NIL] thm1)
    end);

val LAST_LASTN_LAST = store_thm("LAST_LASTN_LAST",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> (0 < n) ==>
     (LAST(LASTN n l) = LAST l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LASTN,LAST]);

val BUTLASTN_LASTN_NIL = store_thm("BUTLASTN_LASTN_NIL",
    (--`!n. !l:'a list. n <= (LENGTH l) ==> (BUTLASTN n (LASTN n l) = [])`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN (fn t => SUBST_OCCS_TAC [([1],SYM t)]) LENGTH_LASTN
    THEN MATCH_ACCEPT_TAC BUTLASTN_LENGTH_NIL);

val LASTN_BUTLASTN = store_thm("LASTN_BUTLASTN",
    (--`!n m. !l:'a list. ((n + m) <= LENGTH l) ==>
     (LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l))`--),
    let val ADD_SUC_SYM = GEN_ALL (SYM (TRANS
        (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC)))
    in
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,ADD,ADD_0,LASTN,BUTLASTN]
    THEN REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO] THENL[
        DISCH_TAC THEN CONV_TAC SYM_CONV THEN IMP_RES_TAC BUTLASTN_LASTN_NIL,
         PURE_ONCE_REWRITE_TAC[ADD_SUC_SYM] THEN DISCH_TAC THEN RES_TAC]
    end);

val BUTLASTN_LASTN = store_thm("BUTLASTN_LASTN",
    (--`!m n. !l:'a list. ((m <= n) /\ (n <= LENGTH l)) ==>
     (BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l))`--),
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0,NOT_SUC_LESS_EQ_0,SUB_0,BUTLASTN,LASTN]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,SUB_MONO_EQ]);

val LASTN_1 = store_thm("LASTN_1",
    (--`!l:'a list. ~(l = []) ==> (LASTN 1 l = [LAST l])`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LASTN,APPEND_NIL,SNOC,LAST]);

val BUTLASTN_1 = store_thm("BUTLASTN_1",
    (--`!l:'a list. ~(l = []) ==> (BUTLASTN 1 l = BUTLAST l)`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[BUTLAST,BUTLASTN]);

val BUTLASTN_APPEND1 = store_thm("BUTLASTN_APPEND1",
--`!l2 n. (LENGTH l2 <= n) ==>
   !l1:'a list. BUTLASTN n (APPEND l1 l2) = BUTLASTN (n - (LENGTH l2)) l1`--,
    SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,APPEND,APPEND_SNOC,APPEND_NIL,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,BUTLASTN,SUB_MONO_EQ]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val LASTN_APPEND2 = store_thm("LASTN_APPEND2",
    (--`!n (l2:'a list). n <= (LENGTH l2) ==>
     (!l1. LASTN n (APPEND l1 l2) = LASTN n l2)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,LASTN,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,LASTN,APPEND_SNOC]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LASTN_APPEND1 = store_thm("LASTN_APPEND1",
--`!(l2:'a list) n. (LENGTH l2) <= n ==>
   !l1. LASTN n (APPEND l1 l2) = APPEND (LASTN (n - (LENGTH l2)) l1) l2`--,
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,
        APPEND,APPEND_SNOC,APPEND_NIL,LASTN,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LASTN,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LASTN_MAP = store_thm("LASTN_MAP",
    (--`!n l. (n <= LENGTH l) ==>
     (!(f:'a->'b). LASTN n (MAP f l) = MAP f (LASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LASTN,MAP,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LENGTH_SNOC,LASTN,MAP_SNOC,LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val BUTLASTN_MAP = store_thm("BUTLASTN_MAP",
    (--`!n l. (n <= LENGTH l) ==>
     (!(f:'a->'b). BUTLASTN n (MAP f l) = MAP f (BUTLASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTLASTN,MAP,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LENGTH_SNOC,BUTLASTN,MAP_SNOC,LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val ALL_EL_LASTN = store_thm("ALL_EL_LASTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     (!m. m <= (LENGTH l) ==> ALL_EL P (LASTN m l))`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,LENGTH]
    THEN GEN_TAC THENL[
        REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0]
        THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_EL,LASTN],
        REWRITE_TAC[ALL_EL_SNOC,LENGTH_SNOC] THEN STRIP_TAC
        THEN INDUCT_TAC THENL[
            REWRITE_TAC[ALL_EL,LASTN],
            REWRITE_TAC[ALL_EL_SNOC,LASTN,LESS_EQ_MONO]
            THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val ALL_EL_BUTLASTN = store_thm("ALL_EL_BUTLASTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     (!m. m <= (LENGTH l) ==> ALL_EL P (BUTLASTN m l))`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,LENGTH]
    THEN GEN_TAC THENL[
        REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0]
        THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_EL,BUTLASTN],
        REWRITE_TAC[ALL_EL_SNOC,LENGTH_SNOC] THEN STRIP_TAC
        THEN INDUCT_TAC THENL[
            DISCH_TAC THEN ASM_REWRITE_TAC[ALL_EL_SNOC,BUTLASTN],
            REWRITE_TAC[ALL_EL_SNOC,BUTLASTN,LESS_EQ_MONO]
            THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val LENGTH_FIRSTN = store_thm ("LENGTH_FIRSTN",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> (LENGTH (FIRSTN n l) = n)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,FIRSTN,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC);

val FIRSTN_FIRSTN = store_thm("FIRSTN_FIRSTN",
    (--`!m (l:'a list). (m <= LENGTH l) ==>
    !n. (n <= m) ==> (FIRSTN n (FIRSTN m l) = FIRSTN n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,FIRSTN] THENL[
        GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
        THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,FIRSTN],
        REWRITE_TAC[NOT_SUC_LESS_EQ_0],
        GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC
        THEN INDUCT_TAC THEN REWRITE_TAC[FIRSTN]
        THEN REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC THEN RES_TAC
        THEN ASM_REWRITE_TAC[]]);

val LENGTH_BUTFIRSTN = store_thm("LENGTH_BUTFIRSTN",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (LENGTH (BUTFIRSTN n l) = LENGTH l - n)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,SUB_0,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val BUTFIRSTN_LENGTH_NIL = store_thm("BUTFIRSTN_LENGTH_NIL",
    (--`!l:'a list. BUTFIRSTN (LENGTH l) l = []`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,BUTFIRSTN]);

val BUTFIRSTN_APPEND1 = store_thm("BUTFIRSTN_APPEND1",
    (--`!n (l1:'a list). (n <= LENGTH l1) ==>
     !l2. BUTFIRSTN n (APPEND l1 l2) = APPEND (BUTFIRSTN n l1) l2`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[APPEND,BUTFIRSTN]);

val BUTFIRSTN_APPEND2 = store_thm("BUTFIRSTN_APPEND2",
    (--`!(l1:'a list) n. ((LENGTH l1) <= n) ==>
     !l2. BUTFIRSTN n (APPEND l1 l2) = BUTFIRSTN (n - (LENGTH l1)) l2`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,BUTFIRSTN,APPEND,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC
        [NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,BUTFIRSTN,SUB_MONO_EQ]);

val BUTFIRSTN_BUTFIRSTN = store_thm("BUTFIRSTN_BUTFIRSTN",
    (--`!n m (l:'a list). ((n + m) <= LENGTH l) ==>
     (BUTFIRSTN n(BUTFIRSTN m l) = BUTFIRSTN (n + m) l)`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,NOT_SUC_LESS_EQ_0,NOT_LESS_0,ADD,ADD_0]
    THEN REWRITE_TAC[ADD_SUC_lem,LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val APPEND_FIRSTN_BUTFIRSTN = store_thm("APPEND_FIRSTN_BUTFIRSTN",
    (--`!n (l:'a list). (n <= LENGTH l) ==>
     (APPEND (FIRSTN n l) (BUTFIRSTN n l) = l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,FIRSTN,BUTFIRSTN,APPEND,NOT_SUC_LESS_EQ_0]
    THEN PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN GEN_TAC
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LASTN_SEG = store_thm("LASTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
                          (LASTN n l = SEG n (LENGTH l - n) l)`--),
    let val SUB_SUC = prove(
      (--`!k m. (m < k) ==> (k - m = SUC (k - SUC m))`--),
      CONV_TAC numLib.ARITH_CONV)
    in
    INDUCT_TAC THEN REWRITE_TAC[LASTN,SUB_0,SEG] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LASTN,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN IMP_RES_TAC LESS_OR_EQ THENL[
        IMP_RES_THEN SUBST1_TAC SUB_SUC
        THEN PURE_ONCE_REWRITE_TAC[SEG] THEN IMP_RES_TAC LESS_EQ
        THEN RES_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC LASTN_CONS
        THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC[SUB_EQUAL_0]
        THEN SUBST1_TAC(SYM(SPECL[(--`x:'a`--),(--`l:'a list`--)]
                                 (CONJUNCT2 LENGTH)))
(* **list_Axiom** variable dependancy *)
(*      THEN SUBST1_TAC(SYM(SPECL[(--`h:'a`--),(--`l:'a list`--)]
                                 (CONJUNCT2 LENGTH))) *)
        THEN REWRITE_TAC[SEG_LENGTH_ID,LASTN_LENGTH_ID]]
    end);

val FIRSTN_SEG = store_thm("FIRSTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==> (FIRSTN n l = SEG n 0 l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,FIRSTN,SEG,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val BUTFIRSTN_SEG = store_thm("BUTFIRSTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (BUTFIRSTN n l = SEG (LENGTH l - n) n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,SEG,NOT_SUC_LESS_EQ_0,
        LESS_EQ_MONO,SUB_0,SEG_LENGTH_ID]
    THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN ASM_REWRITE_TAC[SUB_MONO_EQ,SEG_SUC_CONS]);

val APPEND_BUTLAST_LAST  = store_thm("APPEND_BUTLAST_LAST",
    (--`!l:'a list. ~(l = []) ==> (APPEND (BUTLAST l) [(LAST l)] = l)`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SNOC_NIL,BUTLAST,LAST,SNOC_APPEND]);

val BUTFIRSTN_SNOC = store_thm("BUTFIRSTN_SNOC",
    (--`!n (l:'a list). (n <= LENGTH l) ==>
     (!x. BUTFIRSTN n (SNOC x l) = SNOC x (BUTFIRSTN n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,SNOC,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val APPEND_BUTLASTN_BUTFIRSTN = store_thm("APPEND_BUTLASTN_BUTFIRSTN",
    (--`!m n (l:'a list). ((m + n) = (LENGTH l)) ==>
     (APPEND (BUTLASTN m l) (BUTFIRSTN n l) = l)`--),
    let val ADD_EQ_LESS_EQ =
     prove((--`!m n p. ((m+n)=p) ==> (m<=p)`--),
      REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
      ASM_REWRITE_TAC[LESS_EQ_ADD])
    in
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,APPEND,ADD,ADD_0,NOT_SUC,SUC_NOT,SNOC,
        NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,INV_SUC_EQ] THENL[
        REWRITE_TAC[BUTLASTN,BUTFIRSTN,APPEND],
        GEN_TAC THEN DISCH_THEN SUBST1_TAC
        THEN SUBST1_TAC (SYM(SPECL[(--`x:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH)))
(* **list_Axiom** variable dependancy *)
(*      THEN SUBST1_TAC (SYM(SPECL[(--`h:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH)))    *)
        THEN REWRITE_TAC[BUTFIRSTN_LENGTH_NIL,BUTLASTN,APPEND_NIL],
        GEN_TAC THEN DISCH_THEN SUBST1_TAC
        THEN SUBST1_TAC (SYM(SPECL[(--`x:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH)))
(* **list_Axiom** variable dependancy *)
(*      THEN SUBST1_TAC (SYM(SPECL[(--`h:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH))) *)
        THEN REWRITE_TAC[BUTLASTN_LENGTH_NIL,BUTFIRSTN,APPEND],
        GEN_TAC THEN DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[BUTFIRSTN]
        THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_SUC_lem])
        THEN IMP_RES_TAC ADD_EQ_LESS_EQ THEN IMP_RES_TAC BUTLASTN_CONS
        THEN ASM_REWRITE_TAC[APPEND,CONS_11] THEN RES_TAC]
    end);

val SEG_SEG = store_thm("SEG_SEG",
    (--`!n1 m1 n2 m2 (l:'a list).
     (((n1 + m1) <= (LENGTH l)) /\ ((n2 + m2) <= n1)) ==>
     (SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l)`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THENL[
        GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO,CONS_11]
        THEN STRIP_TAC THEN SUBST_OCCS_TAC[([3],SYM(SPEC(--`0`--)ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC[([2],SYM(SPEC(--`m2:num`--)(CONJUNCT1 ADD)))]
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
        THEN SUBST_OCCS_TAC[([2],SYM(SPEC(--`m1:num`--)ADD_0))]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[LESS_EQ_MONO,ADD_0],

        PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN STRIP_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL[
            PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC_lem]
            THEN FIRST_ASSUM ACCEPT_TAC,
            ASM_REWRITE_TAC[ADD,LESS_EQ_MONO]]]);

val SEG_APPEND1 = store_thm("SEG_APPEND1",
    (--`!n m (l1:'a list). ((n + m) <= LENGTH l1) ==>
     (!l2. SEG n m (APPEND l1 l2) = SEG n m l1)`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THEN GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO,APPEND,SEG,CONS_11] THENL[
        DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[ADD_0],
        PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SEG_APPEND2 = store_thm("SEG_APPEND2",
    (--`!l1:'a list. !m n l2.
     (LENGTH l1 <= m) /\ (n <= LENGTH l2) ==>
     (SEG n m (APPEND l1 l2) = SEG n (m - (LENGTH l1)) l2)`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`m:num`--))
    THEN REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THEN REPEAT GEN_TAC THEN REWRITE_TAC[SUB_0,APPEND,SEG]
    THEN REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ] THEN STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH,LESS_EQ_MONO]);

val SEG_FIRSTN_BUTFIRSTN = store_thm("SEG_FIRSTN_BUTFISTN",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m l = FIRSTN n (BUTFIRSTN m l))`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,ADD,ADD_0,
        SEG,FIRSTN,BUTFIRSTN,LESS_EQ_MONO,CONS_11] THENL[
        MATCH_ACCEPT_TAC (GSYM FIRSTN_SEG),
        PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SEG_APPEND = store_thm("SEG_APPEND",
    (--`!m (l1:'a list) n l2. (m < LENGTH l1) /\ ((LENGTH l1) <= (n + m)) /\
      ((n + m) <= ((LENGTH l1) + (LENGTH l2))) ==>
      (SEG n m (APPEND l1 l2) =
        APPEND (SEG ((LENGTH l1) - m) m l1) (SEG ((n + m)-(LENGTH l1)) 0 l2))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`n:num`--))
    THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0,SUB_0]
    THEN REWRITE_TAC
        [LESS_EQ_MONO,SUB_0,SUB_MONO_EQ,APPEND,SEG,NOT_SUC_LESS_EQ_0,CONS_11]
    THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_0,SUB_0])
    THENL[
        DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
        THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
        THEN REWRITE_TAC[SEG,APPEND_NIL,SUB_EQUAL_0],
        STRIP_TAC THEN DISJ_CASES_TAC (SPEC (--`LENGTH (l1:'a list)`--)LESS_0_CASES)
        THENL[
            POP_ASSUM (ASSUME_TAC o SYM) THEN IMP_RES_TAC LENGTH_NIL
            THEN ASM_REWRITE_TAC[APPEND,SEG,SUB_0],
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]],
        DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
        THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
        THEN REWRITE_TAC[SEG,APPEND_NIL,SUB_EQUAL_0],
        REWRITE_TAC[LESS_MONO_EQ,GSYM NOT_LESS] THEN STRIP_TAC THEN RES_TAC,
        DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
        THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
        THEN REWRITE_TAC[SEG,APPEND_NIL,SUB_EQUAL_0]
        THEN REWRITE_TAC[ADD_SUC_lem,ADD_SUB,SEG],
        REWRITE_TAC[LESS_MONO_EQ,SEG_SUC_CONS] THEN STRIP_TAC
        THEN PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[GSYM ADD_SUC_lem,LENGTH]]);


val SEG_LENGTH_SNOC = store_thm("SEG_LENGTH_SNOC",
    (--`!(l:'a list) x. SEG 1 (LENGTH l) (SNOC x l) = [x]`--),
    CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,SNOC,SEG]);

val SEG_SNOC = store_thm("SEG_SNOC",
    (--`!n m (l:'a list). ((n + m) <= LENGTH l) ==>
     !x. SEG n m (SNOC x l) = SEG n m l`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,ADD,ADD_0,SNOC,SEG] THENL[
        REWRITE_TAC[CONS_11,LESS_EQ_MONO] THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],
        REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN DISCH_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

val ELL_SEG = store_thm("ELL_SEG",
    (--`!n (l:'a list). (n < LENGTH l) ==>
     (ELL n l = HD(SEG 1 (PRE(LENGTH l - n)) l))`--),
    let val SUC_PRE = prove((--`!n . (0 < n) ==> ((SUC (PRE n)) = n)`--),
      REPEAT STRIP_TAC THEN  (ACCEPT_TAC (REWRITE_RULE[]
          (MATCH_MP (SPECL[(--`PRE n`--),(--`n:num`--)] PRE_SUC_EQ)
                 (ASSUME (--`0 < n`--)) ))))
    in
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_LESS_0] THENL[
        REWRITE_TAC[PRE,SUB_0,ELL,LAST,SEG_LENGTH_SNOC,HD],
        REWRITE_TAC[LESS_MONO_EQ,ELL,BUTLAST,SUB_MONO_EQ]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
        THEN CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN MATCH_MP_TAC SEG_SNOC
        THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
        THEN PURE_ONCE_REWRITE_TAC[GSYM ADD1]
        THEN IMP_RES_TAC SUB_LESS_0 THEN IMP_RES_THEN SUBST1_TAC SUC_PRE
        THEN MATCH_ACCEPT_TAC SUB_LESS_EQ]
    end);

val SNOC_FOLDR = store_thm ("SNOC_FOLDR",
    (--`!(x:'a) l. SNOC x l = FOLDR CONS [x] l `--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDR,SNOC]);

val IS_EL_FOLDR_MAP = store_thm("IS_EL_FOLDR_MAP",
    (--`!(x:'a) l. IS_EL x l = FOLDR $\/ F (MAP ($= x) l)`--),
    REWRITE_TAC[IS_EL_FOLDR,FOLDR_MAP]);

val IS_EL_FOLDL_MAP = store_thm("IS_EL_FOLDL_MAP",
    (--`!(x:'a) l. IS_EL x l = FOLDL $\/ F (MAP ($= x) l)`--),
    REWRITE_TAC[IS_EL_FOLDL,FOLDL_MAP]);

val FILTER_FILTER = store_thm("FILTER_FILTER",
    (--`!P Q (l:'a list). FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN BETA_TAC THEN GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[FILTER]);

val FCOMM_FOLDR_FLAT = store_thm("FCOMM_FOLDR_FLAT",
    (--`!(g:'a->'a->'a) (f:'b->'a->'a). FCOMM g f ==>
     (! e. LEFT_ID g e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR g e (MAP (FOLDR f e) l)))`--),
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT,MAP,FOLDR]
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);

val FCOMM_FOLDL_FLAT = store_thm("FCOMM_FOLDL_FLAT",
    (--`!(f:'a->'b->'a) (g:'a->'a->'a). FCOMM f g ==>
     (! e. RIGHT_ID g e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL g e (MAP (FOLDL f e) l)))`--),
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN DISCH_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT_SNOC,MAP_SNOC,MAP,FLAT,FOLDL_SNOC,FOLDL]
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);

val FOLDR1 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. (FOLDR f (f x e) l = f x (FOLDR f e l)))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[REVERSE, FOLDR] THEN ONCE_REWRITE_TAC
    [ASSUME (--`!a b c. (f:'a->'a->'a) a (f b c) = f b (f a c)`--)]
    THEN REWRITE_TAC[ASSUME(--`FOLDR (f:'a->'a->'a)(f x e) l = f x (FOLDR f e l)`--)]);

val FOLDL1 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. (FOLDL f (f e x) l = f (FOLDL f e l) x))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[REVERSE, FOLDL, FOLDL_SNOC]
    THEN ONCE_REWRITE_TAC
    [ASSUME (--`!a b c. (f:'a->'a->'a) (f a b) c = f (f a c) b`--)]
    THEN REWRITE_TAC[ASSUME(--`FOLDL(f:'a->'a->'a)(f e x) l = f (FOLDL f e l) x`--)]);

val FOLDR_REVERSE2 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. FOLDR f e (REVERSE l) = FOLDR f e l)`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE, FOLDR, FOLDR_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN ASM_REWRITE_TAC[]);

val FOLDR_MAP_REVERSE = store_thm("FOLDR_MAP_REVERSE",
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e (g:'b->'a) l. FOLDR f e (MAP g (REVERSE l)) = FOLDR f e (MAP g l))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE, FOLDR, FOLDR_SNOC,MAP,MAP_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN ASM_REWRITE_TAC[]);

val FOLDR_FILTER_REVERSE = store_thm("FOLDR_FILTER_REVERSE",
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e (P:'a->bool) l.
           FOLDR f e (FILTER P (REVERSE l)) = FOLDR f e (FILTER P l))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE, FOLDR, FOLDR_SNOC,FILTER,FILTER_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN GEN_TAC THEN COND_CASES_TAC THENL[
        ASM_REWRITE_TAC[ FOLDR, FOLDR_SNOC,FILTER,FILTER_SNOC]
        THEN ASM_REWRITE_TAC[GSYM FILTER_REVERSE],
        ASM_REWRITE_TAC[ FOLDR, FOLDR_SNOC,FILTER,FILTER_SNOC]]);

val FOLDL_REVERSE2 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l)`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,REVERSE_SNOC, FOLDL, FOLDL_SNOC]
    THEN IMP_RES_TAC FOLDL1 THEN ASM_REWRITE_TAC[]);

val COMM_ASSOC_LEM1 = prove(
    (--`!(f:'a->'a->'a). COMM f ==> (ASSOC f ==>
      (!a b c. f a (f b c) = f b (f a c)))`--),
    REWRITE_TAC[ASSOC_DEF] THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[] THEN SUBST1_TAC(SPECL [(--`a:'a`--),(--`b:'a`--)]
      (REWRITE_RULE [COMM_DEF] (ASSUME (--`COMM (f:'a->'a->'a)`--))))
    THEN REWRITE_TAC[]);

val COMM_ASSOC_LEM2 = prove(
    (--`!(f:'a->'a->'a). COMM f ==> (ASSOC f ==>
      (!a b c. f (f a b) c = f (f a c) b))`--),
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC
      [GSYM (REWRITE_RULE[ASSOC_DEF] (ASSUME (--`ASSOC (f:'a->'a->'a)`--)))]
    THEN SUBST1_TAC(SPECL [(--`b:'a`--),(--`c:'a`--)]
      (REWRITE_RULE [COMM_DEF] (ASSUME (--`COMM (f:'a->'a->'a)`--))))
    THEN REWRITE_TAC[]);

val COMM_ASSOC_FOLDR_REVERSE = store_thm("COMM_ASSOC_FOLDR_REVERSE",
    (--`!f:'a->'a->'a.
         COMM f ==> ASSOC f
          ==> !e l. FOLDR f e (REVERSE l) = FOLDR f e l`--),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDR_REVERSE2
    THEN REPEAT GEN_TAC
    THEN IMP_RES_TAC COMM_ASSOC_LEM1
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val COMM_ASSOC_FOLDL_REVERSE = store_thm("COMM_ASSOC_FOLDL_REVERSE",
    (--`!f:'a->'a->'a. COMM f ==> (ASSOC f ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l))`--),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDL_REVERSE2
    THEN IMP_RES_TAC COMM_ASSOC_LEM2
    THEN REPEAT GEN_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);



(*<------------------------------------------------------------>*)
val ELL_LAST = store_thm("ELL_LAST",
    (--`!l:'a list. ~(NULL l) ==> (ELL 0 l = LAST l)`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[NULL],
      REPEAT STRIP_TAC THEN REWRITE_TAC[ELL]]);

val ELL_0_SNOC = store_thm("ELL_0_SNOC",
    (--`!l:'a list. !x. (ELL 0 (SNOC x l) = x)`--),
     REPEAT GEN_TAC THEN REWRITE_TAC[ELL,LAST]);

val ELL_SNOC = store_thm("ELL_SNOC",
    (--`!n. (0 < n) ==> !x (l:'a list).ELL n (SNOC x l) = ELL (PRE n) l`--),
    INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0],
      REWRITE_TAC[ELL,BUTLAST,PRE,LESS_0]]);

(* |- !n x (l:'a list). (ELL (SUC n) (SNOC x l) = ELL n l) *)
val ELL_SUC_SNOC = save_thm("ELL_SUC_SNOC",
    GEN_ALL(PURE_ONCE_REWRITE_RULE[PRE]
    (MP (SPEC (--`SUC n`--) ELL_SNOC) (SPEC_ALL LESS_0))));

val ELL_CONS = store_thm("ELL_CONS",
    (--`!n (l:'a list). n < (LENGTH l) ==> (!x. ELL n (CONS x l) = ELL n l)`--),
    let val SNOC_lem = GSYM(CONJUNCT2 SNOC)
    in
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0,LENGTH]
    THENL[
        REPEAT STRIP_TAC THEN REWRITE_TAC[SNOC_lem,ELL_0_SNOC],
        GEN_TAC THEN REWRITE_TAC[LENGTH_SNOC,LESS_MONO_EQ,
            ELL_SUC_SNOC,SNOC_lem]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]
    end);

val ELL_LENGTH_CONS = store_thm("ELL_LENGTH_CONS",
    (--`!l:'a list. !x. (ELL (LENGTH l) (CONS x l) = x)`--),
    let val LAST_EL = (* (--`!x:'a. LAST [x] = x`--) *)
    GEN_ALL(REWRITE_RULE[SNOC](SPECL[(--`x:'a`--),(--`[]:'a list`--)]LAST))
    in
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[ELL,LENGTH,LAST_EL],
      REWRITE_TAC[ELL,LENGTH_SNOC,BUTLAST,(GSYM(CONJUNCT2 SNOC))]
      THEN POP_ASSUM ACCEPT_TAC]
    end);

val ELL_LENGTH_SNOC = store_thm("ELL_LENGTH_SNOC",
    (--`!l:'a list. !x. (ELL (LENGTH l) (SNOC x l) = (if NULL l then x else HD l))`--),
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC[ELL_0_SNOC,LENGTH,NULL],
      REWRITE_TAC[ELL_SUC_SNOC,LENGTH,HD,NULL,ELL_LENGTH_CONS]]);

val ELL_APPEND2 = store_thm("ELL_APPEND2",
    (--`!n l2. n < LENGTH l2 ==> !l1:'a list. ELL n (APPEND l1 l2) = ELL n l2`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THEN REWRITE_TAC[APPEND_SNOC,ELL_0_SNOC,ELL_SUC_SNOC,
        LENGTH_SNOC,LESS_MONO_EQ] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_APPEND1 = store_thm("ELL_APPEND1",
    (--`!l2 n. LENGTH l2 <= n ==>
     !l1:'a list. ELL n (APPEND l1 l2) = ELL (n - LENGTH l2) l1`--),
    SNOC_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`n:num`--))
    THEN INDUCT_TAC THEN REWRITE_TAC
        [LENGTH,LENGTH_SNOC,SUB_0,APPEND_NIL,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,ELL_SUC_SNOC,SUB_MONO_EQ,APPEND_SNOC]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_PRE_LENGTH = store_thm("ELL_PRE_LENGTH",
    (--`!l:'a list. ~(l = []) ==> (ELL (PRE(LENGTH l)) l  = HD l)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,PRE]
    THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ELL_LENGTH_CONS,HD]);

val EL_LENGTH_SNOC = save_thm("EL_LENGTH_SNOC", listTheory.EL_LENGTH_SNOC);

val EL_PRE_LENGTH = store_thm("EL_PRE_LENGTH",
    (--`!l:'a list. ~(l = []) ==> (EL (PRE(LENGTH l)) l  = LAST l)`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC,PRE,LAST,EL_LENGTH_SNOC]);

val EL_SNOC = save_thm("EL_SNOC", listTheory.EL_SNOC);

val LESS_PRE_SUB_LESS = prove((--`!n m. (m < n) ==> (PRE(n - m) < n)`--),
    let val PRE_K_K = prove((--`!k . (0<k) ==> (PRE k < k)`--),
      INDUCT_THEN INDUCTION MP_TAC THEN
      REWRITE_TAC [LESS_REFL,LESS_0,PRE,LESS_SUC_REFL])
    in
    REPEAT INDUCT_TAC THENL[
        REWRITE_TAC[NOT_LESS_0],
        REWRITE_TAC[NOT_LESS_0],
        REWRITE_TAC[SUB_0,PRE_K_K],
        REWRITE_TAC[LESS_MONO_EQ,SUB_MONO_EQ]
        THEN REWRITE_TAC[LESS_THM]
        THEN STRIP_TAC THEN DISJ2_TAC THEN RES_TAC]
    end);

val EL_ELL = store_thm("EL_ELL",
    (--`!n (l:'a list). n < LENGTH l ==> (EL n l = ELL (PRE((LENGTH l) - n)) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
        REWRITE_TAC[PRE,EL,ELL_LENGTH_CONS,HD,SUB_0],
        REWRITE_TAC[EL,TL,LESS_MONO_EQ,SUB_MONO_EQ]
        THEN GEN_TAC THEN DISCH_TAC
        THEN MAP_EVERY IMP_RES_TAC [LESS_PRE_SUB_LESS,ELL_CONS]
        THEN RES_TAC THEN ASM_REWRITE_TAC[]]);

val EL_LENGTH_APPEND = store_thm("EL_LENGTH_APPEND",
  (--`!(l2:('a)list) (l1:('a)list) .
      ~(NULL l2)==> ( EL (LENGTH l1) (APPEND l1 l2) = HD l2)`--),
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH,APPEND,EL,TL,NULL]
  THEN REPEAT STRIP_TAC THEN RES_TAC);

val ELL_EL = store_thm("ELL_EL",
    (--`!n (l:'a list). n < LENGTH l ==> (ELL n l = EL (PRE((LENGTH l) - n)) l)`--),
    let val lem = prove((--`!n m. n < m ==> ?k. (m - n = SUC k) /\ k < m`--),
        REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THENL[
            REWRITE_TAC[SUB_0] THEN DISCH_TAC
            THEN EXISTS_TAC (--`m:num`--) THEN REWRITE_TAC[LESS_SUC_REFL],
            ASM_REWRITE_TAC[LESS_MONO_EQ,SUB_MONO_EQ]
            THEN DISCH_TAC THEN RES_TAC THEN EXISTS_TAC (--`k:num`--)
            THEN IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC[]])
    in
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
        REWRITE_TAC[SUB_0,ELL_0_SNOC,LENGTH_SNOC,PRE,EL_LENGTH_SNOC],
        REWRITE_TAC[LENGTH_SNOC,ELL_SUC_SNOC,SUB_MONO_EQ,LESS_MONO_EQ]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
        THEN MATCH_MP_TAC (GSYM EL_SNOC)
        THEN IMP_RES_TAC lem THEN ASM_REWRITE_TAC[PRE]]
    end);

val ELL_MAP = store_thm("ELL_MAP",
    (--`!n l (f:'a->'b). n < (LENGTH l) ==> (ELL n (MAP f l) = f (ELL n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
        REWRITE_TAC[ELL_0_SNOC,MAP_SNOC],
        REWRITE_TAC[LENGTH_SNOC,ELL_SUC_SNOC,MAP_SNOC,LESS_MONO_EQ]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val LENGTH_BUTLAST = store_thm("LENGTH_BUTLAST",
    (--`!l:'a list. ~(l = []) ==> (LENGTH(BUTLAST l) = PRE(LENGTH l))`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC,BUTLAST,PRE]);

val BUTFIRSTN_LENGTH_APPEND = store_thm("BUTFIRSTN_LENGTH_APPEND",
    (--`!l1 l2:'a list. BUTFIRSTN(LENGTH l1)(APPEND l1 l2) = l2`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,BUTFIRSTN,APPEND]);

val FIRSTN_APPEND1 = store_thm("FIRSTN_APPEND1",
    (--`!n (l1:'a list). n <= (LENGTH l1) ==>
     !l2. FIRSTN n (APPEND l1 l2) = FIRSTN n l1`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC
        [LENGTH,NOT_SUC_LESS_EQ_0,FIRSTN,APPEND,CONS_11,LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val FIRSTN_APPEND2 = store_thm("FIRSTN_APPEND2",
    (--`!(l1:'a list) n. (LENGTH l1) <= n ==>
     !l2. FIRSTN n (APPEND l1 l2) = APPEND l1 (FIRSTN (n - (LENGTH l1)) l2)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,APPEND,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,
        LESS_EQ_MONO,SUB_MONO_EQ,FIRSTN,CONS_11]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val FIRSTN_LENGTH_APPEND = store_thm("FIRSTN_LENGTH_APPEND",
    (--`!(l1:'a list) l2. FIRSTN (LENGTH l1) (APPEND l1 l2) = l1`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,FIRSTN,APPEND]);

(*<---------------------------------------------------------------------->*)

val REVERSE_FLAT = store_thm("REVERSE_FLAT",
   (--`!l:'a list list. REVERSE (FLAT l) = FLAT(REVERSE(MAP REVERSE l))`--),
   LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE,FLAT,MAP]
   THEN ASM_REWRITE_TAC[REVERSE_APPEND,FLAT_SNOC]);

val MAP_COND = prove(
   (--`!(f:'a-> 'b) c l1 l2.
        (MAP f (if c then l1 else l2)) = (if c then (MAP f l1) else (MAP f l2))`--),
   REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`c:bool`--) THEN ASM_REWRITE_TAC[]);

val MAP_FILTER = store_thm("MAP_FILTER",
   (--`!(f:'a -> 'a) P l.
        (!x. P (f x) = P x) ==>
             (MAP f (FILTER P l) = FILTER P (MAP f l))`--),
   GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,FILTER]
   THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MAP_COND,MAP]
   THEN RES_THEN SUBST1_TAC THEN REFL_TAC);

val FLAT_APPEND = store_thm("FLAT_APPEND",
    (--`!l1 l2:'a list list.
         FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND,FLAT]
    THEN ASM_REWRITE_TAC[APPEND_ASSOC]);

val FLAT_REVERSE = store_thm("FLAT_REVERSE",
    (--`!l:'a list list. FLAT (REVERSE l) = REVERSE (FLAT (MAP REVERSE l))`--),
    LIST_INDUCT_TAC THEN  REWRITE_TAC[FLAT,REVERSE,MAP]
    THEN ASM_REWRITE_TAC[FLAT_SNOC,REVERSE_APPEND,REVERSE_REVERSE]);

val FLAT_FLAT = store_thm("FLAT_FLAT",
    (--`!l:'a list list list. FLAT (FLAT l) = FLAT(MAP FLAT l)`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,FLAT_APPEND,MAP]);

val ALL_EL_REVERSE = store_thm("ALL_EL_REVERSE",
    (--`!P (l:'a list). ALL_EL P (REVERSE l) = ALL_EL P l`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[ALL_EL,REVERSE,ALL_EL_SNOC]
    THEN GEN_TAC THEN MATCH_ACCEPT_TAC CONJ_SYM);

val SOME_EL_REVERSE = store_thm("SOME_EL_REVERSE",
    (--`!P (l:'a list). SOME_EL P (REVERSE l) = SOME_EL P l`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SOME_EL,REVERSE,SOME_EL_SNOC]
    THEN GEN_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM);

val ALL_EL_SEG = store_thm("ALL_EL_SEG",
    (--`!P (l:'a list). ALL_EL P l ==>
     !m k. (m + k) <= (LENGTH l) ==> ALL_EL P (SEG m k l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,SEG,LENGTH] THENL[
      REPEAT INDUCT_TAC
      THEN REWRITE_TAC[ADD,ADD_0,NOT_SUC_LESS_EQ_0,SEG,ALL_EL],

      GEN_TAC THEN STRIP_TAC THEN REPEAT INDUCT_TAC
      THEN REWRITE_TAC[ADD,ADD_0,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,SEG,ALL_EL]
      THENL[
        mesonLib.ASM_MESON_TAC [ADD_CLAUSES],
        let val lem = SPEC(--`k:num`--) (GEN (--`n:num`--)
            (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))))
        in
        SUBST1_TAC lem THEN DISCH_TAC THEN RES_TAC
        end]]);

val ALL_EL_FIRSTN = store_thm("ALL_EL_FIRSTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     !m. m <= (LENGTH l) ==> ALL_EL P (FIRSTN m l)`--),
    REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC FIRSTN_SEG
    THEN IMP_RES_THEN MATCH_MP_TAC ALL_EL_SEG
    THEN ASM_REWRITE_TAC[ADD_0]);

val ALL_EL_BUTFIRSTN = store_thm("ALL_EL_BUTFIRSTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     !m. m <= (LENGTH l) ==> ALL_EL P (BUTFIRSTN m l)`--),
    REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC BUTFIRSTN_SEG
    THEN IMP_RES_THEN MATCH_MP_TAC ALL_EL_SEG
    THEN IMP_RES_THEN SUBST1_TAC SUB_ADD
    THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);

val SOME_EL_SEG = store_thm("SOME_EL_SEG",
    (--`!m k (l:'a list). (m + k) <= (LENGTH l) ==>
     !P. SOME_EL P (SEG m k l) ==> SOME_EL P l`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SOME_EL,SEG,LENGTH,ADD,ADD_0,NOT_SUC_LESS_EQ_0]
    THEN GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO] THENL[
      FIRST_ASSUM (ASSUME_TAC o (REWRITE_RULE[ADD_0]) o (SPEC(--`0`--)))
      THEN REPEAT STRIP_TAC THENL[
        DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        DISJ2_TAC THEN RES_TAC],
        let val lem = SPEC(--`k:num`--) (GEN (--`n:num`--)
            (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))))
       in
        SUBST1_TAC lem THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC
       end]);

val SOME_EL_FIRSTN = store_thm("SOME_EL_FIRSTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
        !P.  SOME_EL P (FIRSTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC FIRSTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN ASM_REWRITE_TAC[ADD_0]);

val SOME_EL_BUTFIRSTN = store_thm("SOME_EL_BUTFIRSTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
     !P. SOME_EL P (BUTFIRSTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTFIRSTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN IMP_RES_THEN SUBST1_TAC SUB_ADD
    THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);

val SOME_EL_LASTN = store_thm("SOME_EL_LASTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
     !P. SOME_EL P (LASTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC LASTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN IMP_RES_THEN SUBST1_TAC SUB_ADD THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);

val SOME_EL_BUTLASTN = store_thm("SOME_EL_BUTLASTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
     !P. SOME_EL P (BUTLASTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN PURE_ONCE_REWRITE_TAC[ADD_0]
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val IS_EL_REVERSE = store_thm("IS_EL_REVERSE",
    (--`!(x:'a) l. IS_EL x (REVERSE l) = IS_EL x l`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,IS_EL,IS_EL_SNOC]);

val IS_EL_FILTER = store_thm("IS_EL_FILTER",
    (--`!P (x:'a). P x ==> !l. IS_EL x (FILTER P l) = IS_EL x l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER,IS_EL] THEN GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[IS_EL] THEN EQ_TAC THENL[
        DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN RES_TAC]);

val IS_EL_SEG = store_thm("IS_EL_SEG",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     !x. IS_EL x (SEG n m l) ==> IS_EL x l`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[ADD,ADD_0,NOT_SUC_LESS_EQ_0,LENGTH,IS_EL,
        SEG,LESS_EQ_MONO] THEN GEN_TAC THENL[
        DISCH_TAC THEN FIRST_ASSUM (IMP_RES_TAC o
            (REWRITE_RULE[ADD_0]) o (SPEC(--`0`--)))
        THEN GEN_TAC THEN DISCH_THEN (DISJ_CASES_THEN2
            (fn t => DISJ1_TAC THEN ACCEPT_TAC t)
            (fn t => DISJ2_TAC THEN ASSUME_TAC t THEN RES_TAC)),
        let val lem = (GEN_ALL
            (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))))
        in
        PURE_ONCE_REWRITE_TAC[lem] THEN REPEAT STRIP_TAC
        THEN DISJ2_TAC THEN RES_TAC
        end]);

val IS_EL_SOME_EL = store_thm("IS_EL_SOME_EL",
    (--`!(x:'a) l. IS_EL x l = SOME_EL ($= x) l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[IS_EL,SOME_EL]);

val IS_EL_FIRSTN = store_thm("IS_EL_FIRSTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (FIRSTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_FIRSTN);

val IS_EL_BUTFIRSTN = store_thm("IS_EL_BUTFIRSTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (BUTFIRSTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_BUTFIRSTN);

val IS_EL_BUTLASTN = store_thm("IS_EL_BUTLASTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (BUTLASTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_BUTLASTN);

val IS_EL_LASTN = store_thm("IS_EL_LASTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (LASTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_LASTN);


val ZIP_SNOC = store_thm("ZIP_SNOC",
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !(x1:'a) (x2:'b).
      ZIP((SNOC x1 l1), (SNOC x2 l2)) = SNOC (x1,x2) (ZIP(l1,l2))`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,ZIP,LENGTH,NOT_SUC,SUC_NOT]
    THEN REWRITE_TAC[INV_SUC_EQ,CONS_11] THEN REPEAT STRIP_TAC
    THEN RES_THEN MATCH_ACCEPT_TAC);

val UNZIP_SNOC = store_thm("UNZIP_SNOC",
    (--`!(x:'a # 'b) l.
     UNZIP(SNOC x l) = (SNOC(FST x)(FST(UNZIP l)), SNOC(SND x)(SND(UNZIP l)))`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC,UNZIP]);

val LENGTH_ZIP = save_thm("LENGTH_ZIP", listTheory.LENGTH_ZIP);

val LENGTH_UNZIP_FST = store_thm("LENGTH_UNZIP_FST",
    (--`!l:('a # 'b)list. LENGTH (UNZIP_FST l) = LENGTH l`--),
    PURE_ONCE_REWRITE_TAC[UNZIP_FST_DEF]
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP,LENGTH]);

val LENGTH_UNZIP_SND = store_thm("LENGTH_UNZIP_SND",
    (--`!l:('a # 'b)list. LENGTH (UNZIP_SND l) = LENGTH l`--),
    PURE_ONCE_REWRITE_TAC[UNZIP_SND_DEF]
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP,LENGTH]);

val ZIP_UNZIP = save_thm("ZIP_UNZIP", listTheory.ZIP_UNZIP);

val UNZIP_ZIP = save_thm("UNZIP_ZIP", listTheory.UNZIP_ZIP);

val SUM_APPEND = save_thm("SUM_APPEND", listTheory.SUM_APPEND);

val SUM_REVERSE = store_thm("SUM_REVERSE",
    (--`!l. SUM (REVERSE l) = SUM l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM,REVERSE,SUM_SNOC]
    THEN MATCH_ACCEPT_TAC ADD_SYM);

val SUM_FLAT = store_thm("SUM_FLAT",
    (--`!l. SUM (FLAT l) = SUM (MAP SUM l)`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM,FLAT,MAP,SUM_APPEND]);

val EL_APPEND1 = store_thm("EL_APPEND1",
    (--`!n l1 (l2:'a list). n < (LENGTH l1) ==> (EL n (APPEND l1 l2) = EL n l1)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[EL,APPEND,HD,TL,LENGTH,NOT_LESS_0,LESS_MONO_EQ]);

val EL_APPEND2 = store_thm("EL_APPEND2",
    (--`!(l1:'a list) n. (LENGTH l1) <= n ==>
     !l2. EL n (APPEND l1 l2) = EL (n - (LENGTH l1)) l2`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,APPEND,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[EL,APPEND,HD,TL,
        LENGTH,NOT_SUC_LESS_EQ_0,SUB_MONO_EQ,LESS_EQ_MONO]);

val EL_MAP = save_thm("EL_MAP", listTheory.EL_MAP);

val EL_CONS = store_thm("EL_CONS",
    (--`!n. 0 < n ==> !(x:'a) l. EL n (CONS x l) = EL (PRE n) l`--),
    INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0,EL,HD,TL,PRE]);

val EL_SEG = store_thm("EL_SEG",
    (--`!n (l:'a list). n < (LENGTH l) ==> (EL n l = HD (SEG 1 n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REWRITE_TAC[SEG,HD]
    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REFL_TAC);

val EL_IS_EL = store_thm("EL_IS_EL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (IS_EL (EL n l) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ,IS_EL]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC);

val TL_SNOC = store_thm("TL_SNOC",
    (--`!(x:'a) l. TL(SNOC x l) = (if (NULL l) then [] else SNOC x (TL l))`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC,TL,NULL]);

val SUB_SUC_LESS = prove(
    (--`!m n. (n < m) ==> (m - (SUC n)) < m`--),
    INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0,SUB_MONO_EQ]
    THEN INDUCT_TAC THENL[
        REWRITE_TAC[SUB_0,LESS_SUC_REFL],
        REWRITE_TAC[LESS_MONO_EQ] THEN DISCH_TAC THEN RES_TAC
        THEN IMP_RES_TAC LESS_SUC]);

val EL_REVERSE = save_thm("EL_REVERSE", listTheory.EL_REVERSE)

val EL_REVERSE_ELL = store_thm("EL_REVERSE_ELL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (EL n (REVERSE l) = ELL n l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,REVERSE_SNOC,
        EL,ELL,HD,TL,LAST,BUTLAST,NOT_LESS_0,LESS_MONO_EQ,SUB_0]);

val ELL_LENGTH_APPEND = store_thm("ELL_LENGTH_APPEND",
    (--`!(l1:('a)list) (l2:('a)list).
      ~(NULL l1)==> (ELL (LENGTH l2) (APPEND l1 l2) = LAST l1)`--),
    GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC
        [LENGTH,LENGTH_SNOC,APPEND_SNOC,APPEND_NIL,ELL,TL,BUTLAST]);

val ELL_IS_EL = store_thm("ELL_IS_EL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (IS_EL (ELL n l) l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN
    ASM_REWRITE_TAC[NOT_LESS_0, LESS_MONO_EQ, LENGTH_SNOC, ELL_0_SNOC,
                    IS_EL_SNOC, ELL_SUC_SNOC, LENGTH] THEN
    REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC);

val ELL_REVERSE = store_thm("ELL_REVERSE",
    (--`!n (l:'a list). n < (LENGTH l) ==>
     (ELL n (REVERSE l) = ELL (PRE(LENGTH l - n)) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,REVERSE,SUB_0,ELL,LAST,
        BUTLAST,NOT_LESS_0,LESS_MONO_EQ,PRE,ELL_LENGTH_CONS,SUB_MONO_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    THEN MATCH_MP_TAC (GSYM ELL_CONS)
    THEN REWRITE_TAC(PRE_SUB1 :: (map GSYM [SUB_PLUS,ADD1]))
    THEN IMP_RES_TAC SUB_SUC_LESS);

val ELL_REVERSE_EL = store_thm("ELL_REVERSE_EL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (ELL n (REVERSE l) = EL n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,REVERSE,REVERSE_SNOC,
        EL,ELL,HD,TL,LAST,BUTLAST,NOT_LESS_0,LESS_MONO_EQ,SUB_0]);


val LESS_EQ_SPLIT =
    let val asm_thm = ASSUME (--`(m + n) <= p`--)
    in
    GEN_ALL(DISCH_ALL
     (CONJ(MP(SPECL [(--`n:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
              (CONJ (SUBS [SPECL [(--`n:num`--),(--`m:num`--)] ADD_SYM]
                     (SPECL [(--`n:num`--),(--`m:num`--)] LESS_EQ_ADD)) asm_thm))
          (MP (SPECL [(--`m:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
               (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))))
   end;

val SUB_GREATER_EQ_ADD = prove(
    (--`!p n m. (p >= n) ==> (((p - n) >= m) = (p >= (m + n)))`--),
    REWRITE_TAC[
      SYM (SPEC (--`n:num`--) (SPEC (--`p-n`--) (SPEC (--`m:num`--)
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (fn th => ASSUME_TAC
      (MP (SPEC (--`n:num`--) (SPEC (--`p:num`--) SUB_ADD))
          (REWRITE_RULE[SPEC (--`n:num`--) (SPEC (--`p:num`--) GREATER_EQ)] th)))
    THEN SUBST_TAC[(SPEC_ALL ADD_SYM)] THEN ASM_REWRITE_TAC[]);

(* SUB_LESS_EQ_ADD = |- !p n m. n <= p ==> (m <= (p - n) = (m + n) <= p) *)
val SUB_LESS_EQ_ADD = (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);

val FIRSTN_BUTLASTN = store_thm("FIRSTN_BUTLASTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (FIRSTN n l = BUTLASTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[FIRSTN,BUTLASTN_LENGTH_NIL,SUB_0]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,FIRSTN,LENGTH,
        SUB_0,BUTLASTN,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BUTLASTN_CONS
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val BUTLASTN_FIRSTN = store_thm("BUTLASTN_FIRSTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTLASTN n l = FIRSTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[FIRSTN,BUTLASTN_LENGTH_NIL,SUB_0]
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LENGTH,LENGTH_SNOC,
        SUB_0,BUTLASTN,FIRSTN,FIRSTN_LENGTH_ID,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIRSTN_SNOC
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val LASTN_BUTFIRSTN = store_thm("LASTN_BUTFIRSTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (LASTN n l = BUTFIRSTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN,BUTFIRSTN_LENGTH_NIL,SUB_0]
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LASTN,LENGTH,
        LENGTH_SNOC,SUB_0,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BUTFIRSTN_SNOC
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val BUTFIRSTN_LASTN = store_thm("BUTFIRSTN_LASTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTFIRSTN n l = LASTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN_LENGTH_ID,BUTFIRSTN,SUB_0]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LASTN,LENGTH,
        BUTFIRSTN,SUB_0,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LASTN_CONS
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val SUB_ADD_lem = prove(
    (--`!l n m. (n + m) <= l ==> ((l - (n + m)) + n = l - m)`--),
    CONV_TAC numLib.ARITH_CONV)

val SEG_LASTN_BUTLASTN = store_thm("SEG_LASTN_BUTLASTN",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m l = LASTN n (BUTLASTN ((LENGTH l) - (n + m)) l))`--),
    let val th2 = SUBS [(REWRITE_RULE[SUB_LESS_EQ]
        (SPECL[(--`(LENGTH (l:'a list)) - m`--), (--`l:'a list`--)]
           LENGTH_LASTN))]
        (SPECL[(--`n:num`--),(--`LASTN((LENGTH l) - m)(l:'a list)`--)]
           FIRSTN_BUTLASTN)
        val  th3 = UNDISCH_ALL (SUBS[UNDISCH_ALL
        (SPECL[(--`LENGTH(l:'a list)`--),(--`m:num`--),(--`n:num`--)]SUB_LESS_EQ_ADD)] th2)
        val th4 = PURE_ONCE_REWRITE_RULE[ADD_SYM](REWRITE_RULE[
        UNDISCH_ALL(SPECL[(--`LENGTH(l:'a list)`--),(--`n:num`--),(--`m:num`--)]SUB_ADD_lem),
        SUB_LESS_EQ]
        (PURE_ONCE_REWRITE_RULE[ADD_SYM](SPECL
        [(--`n:num`--),(--`(LENGTH (l:'a list)) - (n + m)`--),(--`l:'a list`--)]LASTN_BUTLASTN)))
    in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN IMP_RES_THEN SUBST1_TAC SEG_FIRSTN_BUTFIRSTN
    THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN SUBST1_TAC (UNDISCH_ALL(SPECL[(--`m:num`--),(--`l:'a list`--)] BUTFIRSTN_LASTN))
    THEN SUBST1_TAC th3 THEN REWRITE_TAC[GSYM SUB_PLUS]
    THEN SUBST_OCCS_TAC[([1],(SPEC_ALL ADD_SYM))]
    THEN CONV_TAC SYM_CONV THEN ACCEPT_TAC th4
    end);

val BUTFIRSTN_REVERSE = store_thm("BUTFIRSTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTFIRSTN n (REVERSE l) = REVERSE(BUTLASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,
        LENGTH,LENGTH_SNOC,BUTFIRSTN,BUTLASTN,LESS_EQ_MONO,REVERSE_SNOC]);

val BUTLASTN_REVERSE = store_thm("BUTLASTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTLASTN n (REVERSE l) = REVERSE(BUTFIRSTN n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,
        LENGTH,BUTFIRSTN,BUTLASTN,LESS_EQ_MONO,REVERSE]);

val LASTN_REVERSE = store_thm("LASTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (LASTN n (REVERSE l) = REVERSE(FIRSTN n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,
        LENGTH,FIRSTN,LASTN,LESS_EQ_MONO,REVERSE,SNOC_11]);

val FIRSTN_REVERSE = store_thm("FIRSTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (FIRSTN n (REVERSE l) = REVERSE(LASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,LENGTH,LENGTH_SNOC,
        FIRSTN,LASTN,LESS_EQ_MONO,REVERSE,REVERSE_SNOC,CONS_11]);

val SEG_REVERSE = store_thm("SEG_REVERSE",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m (REVERSE l) =  REVERSE(SEG n (LENGTH l - (n + m)) l))`--),
    let val LEN_REV = (SPEC(--`l:'a list`--) LENGTH_REVERSE)
    val SUB_LE_ADD =
        SPECL[(--`LENGTH(l:'a list)`--),(--`m:num`--),(--`n:num`--)]SUB_LESS_EQ_ADD
    val SEG_lem = REWRITE_RULE[SUB_LESS_EQ](PURE_ONCE_REWRITE_RULE[ADD_SYM]
        (SUBS[UNDISCH_ALL(SPEC_ALL(SPEC(--`LENGTH(l:'a list)`--) SUB_ADD_lem))]
         (PURE_ONCE_REWRITE_RULE[ADD_SYM]
          (SPECL[(--`n:num`--),(--`LENGTH(l:'a list) -(n+m)`--),(--`l:'a list`--)]
            SEG_LASTN_BUTLASTN))))
    val lem = PURE_ONCE_REWRITE_RULE[ADD_SUB](PURE_ONCE_REWRITE_RULE[ADD_SYM]
        (SPEC (--`LENGTH(l:'a list)`--)
         (UNDISCH_ALL(SPECL[(--`LENGTH(l:'a list)`--),(--`m:num`--)]SUB_SUB))))    in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP  SEG_FIRSTN_BUTFIRSTN)
        o (SUBS[SYM LEN_REV]))
    THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN IMP_RES_THEN SUBST1_TAC (SPECL[(--`m:num`--),(--`l:'a list`--)]BUTFIRSTN_REVERSE)
    THEN FIRST_ASSUM
        (ASSUME_TAC o (MP(SPECL[(--`m:num`--),(--`(l:'a list)`--)]LENGTH_BUTLASTN)))
    THEN FIRST_ASSUM (fn t =>  ASSUME_TAC (SUBS[t]
        (SPECL[(--`n:num`--),(--`BUTLASTN m (l:'a list)`--)]FIRSTN_REVERSE)))
    THEN FIRST_ASSUM (SUBST_ALL_TAC o (MP SUB_LE_ADD))
    THEN RES_THEN SUBST1_TAC THEN AP_TERM_TAC
    THEN SUBST1_TAC SEG_lem THEN SUBST1_TAC lem THEN REFL_TAC
    end);

(*<---------------------------------------------------------------->*)
val LENGTH_GENLIST = save_thm("LENGTH_GENLIST",listTheory.LENGTH_GENLIST);

val LENGTH_REPLICATE = store_thm("LENGTH_REPLICATE",
    (--`!n (x:'a). LENGTH(REPLICATE n x) = n`--),
    INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE,LENGTH]);

val IS_EL_REPLICATE = store_thm("IS_EL_REPLICATE",
    (--`!n. 0 < n ==> !x:'a. IS_EL x (REPLICATE n x)`--),
    INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0,IS_EL,REPLICATE]);

val ALL_EL_REPLICATE = store_thm("ALL_EL_REPLICATE",
    (--`!(x:'a) n. ALL_EL ($= x) (REPLICATE n x)`--),
    GEN_TAC THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS_0,ALL_EL,REPLICATE]);


val AND_EL_FOLDL = save_thm("AND_EL_FOLDL",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[ALL_EL_FOLDL,I_THM](AP_THM AND_EL_DEF (--`l:bool list`--)))));

val AND_EL_FOLDR = save_thm("AND_EL_FOLDR",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[ALL_EL_FOLDR,I_THM](AP_THM AND_EL_DEF (--`l:bool list`--)))));

val OR_EL_FOLDL = save_thm("OR_EL_FOLDL",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[SOME_EL_FOLDL,I_THM](AP_THM OR_EL_DEF (--`l:bool list`--)))));

val OR_EL_FOLDR = save_thm("OR_EL_FOLDR",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[SOME_EL_FOLDR,I_THM](AP_THM OR_EL_DEF (--`l:bool list`--)))));

val MAP2_ZIP = save_thm("MAP2_ZIP", listTheory.MAP2_ZIP);
val ZIP = save_thm("ZIP", listTheory.ZIP);
val UNZIP = save_thm("UNZIP", listTheory.UNZIP);





(*---------------------------------------------------------------------------
   A bunch of properties relating to the use of IS_PREFIX as a partial order
 ---------------------------------------------------------------------------*)

open simpLib;

val IS_PREFIX_NIL = store_thm
  ("IS_PREFIX_NIL",
   ``!(x:'a list). IS_PREFIX x [] /\ (IS_PREFIX [] x = (x = []))``,
   STRIP_TAC
   THEN MP_TAC (Q.SPEC `x` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN PROVE_TAC [NOT_NIL_CONS]);

val IS_PREFIX_REFL = store_thm
  ("IS_PREFIX_REFL",
   ``!(x:'a list). IS_PREFIX x x``,
   INDUCT_THEN list_INDUCT MP_TAC
   THEN SIMP_TAC boolSimps.bool_ss [IS_PREFIX]);

val IS_PREFIX_ANTISYM = store_thm
  ("IS_PREFIX_ANTISYM",
   ``!(x:'a list) y. IS_PREFIX y x /\ IS_PREFIX x y ==> (x = y)``,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN ONCE_REWRITE_TAC [IS_PREFIX]
   THEN PROVE_TAC []);

val IS_PREFIX_TRANS = store_thm
  ("IS_PREFIX_TRANS",
   ``!(x:'a list) y z. IS_PREFIX x y /\ IS_PREFIX y z ==> IS_PREFIX x z``,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN MP_TAC (Q.SPEC `z` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX_NIL]
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN PROVE_TAC []);

val IS_PREFIX_BUTLAST = store_thm
  ("IS_PREFIX_BUTLAST",
   ``!x:'a y. IS_PREFIX (x::y) (BUTLAST (x::y))``,
   REPEAT GEN_TAC
   THEN Q.SPEC_TAC (`x`, `x`)
   THEN Q.SPEC_TAC (`y`, `y`)
   THEN INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [BUTLAST_CONS, IS_PREFIX]);

val IS_PREFIX_LENGTH = store_thm
  ("IS_PREFIX_LENGTH",
   ``!(x:'a list) y. IS_PREFIX y x ==> LENGTH x <= LENGTH y``,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [LENGTH, ZERO_LESS_EQ]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, LENGTH, LESS_EQ_MONO]);

val IS_PREFIX_LENGTH_ANTI = store_thm
  ("IS_PREFIX_LENGTH_ANTI",
   ``!(x:'a list) y. IS_PREFIX y x /\ (LENGTH x = LENGTH y) = (x = y)``,
   (INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN1 PROVE_TAC [LENGTH_NIL, IS_PREFIX_REFL])
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `y` list_CASES)
   THEN STRIP_TAC
   THENL [ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, LENGTH, LESS_EQ_MONO]
          THEN PROVE_TAC [NOT_CONS_NIL],
          ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, LENGTH, CONS_11]
          THEN PROVE_TAC [numTheory.INV_SUC, IS_PREFIX_REFL]]);

val IS_PREFIX_SNOC = store_thm
  ("IS_PREFIX_SNOC",
   ``!(x:'a) y z. IS_PREFIX (SNOC x y) z = IS_PREFIX y z \/ (z = SNOC x y)``,
   GEN_TAC
   THEN GEN_TAC
   THEN Q.SPEC_TAC (`x`, `x`)
   THEN Q.SPEC_TAC (`y`, `y`)
   THEN INDUCT_THEN list_INDUCT ASSUME_TAC
   THENL [REPEAT GEN_TAC
          THEN MP_TAC (Q.SPEC `z` list_CASES)
          THEN STRIP_TAC
          THEN ASM_SIMP_TAC boolSimps.bool_ss
               [SNOC, IS_PREFIX_NIL, IS_PREFIX, CONS_11, NOT_CONS_NIL]
          THEN PROVE_TAC [],
          REPEAT GEN_TAC
          THEN MP_TAC (Q.SPEC `z` list_CASES)
          THEN STRIP_TAC
          THEN ASM_SIMP_TAC boolSimps.bool_ss
               [SNOC, IS_PREFIX_NIL, IS_PREFIX, CONS_11, NOT_CONS_NIL]
          THEN PROVE_TAC []]);

val IS_PREFIX_APPEND1 = store_thm
  ("IS_PREFIX_APPEND1",
   ``!a b c. IS_PREFIX c (APPEND a b) ==> IS_PREFIX c a``,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, APPEND]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `c` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN PROVE_TAC []);

val IS_PREFIX_APPEND2 = store_thm
  ("IS_PREFIX_APPEND2",
   ``!a b c. IS_PREFIX (APPEND b c) a ==> IS_PREFIX b a \/ IS_PREFIX a b``,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX]
   THEN REPEAT GEN_TAC
   THEN MP_TAC (Q.SPEC `b` list_CASES)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [IS_PREFIX, APPEND]
   THEN PROVE_TAC []);

val IS_PREFIX_APPENDS = store_thm
  ("IS_PREFIX_APPENDS",
   ``!a b c. IS_PREFIX (APPEND a c) (APPEND a b) = IS_PREFIX c b``,
   INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss [APPEND, IS_PREFIX]);

val MAP_GENLIST = save_thm("MAP_GENLIST", listTheory.MAP_GENLIST);
val EL_GENLIST = save_thm("EL_GENLIST", listTheory.EL_GENLIST);
val HD_GENLIST = save_thm("HD_GENLIST", listTheory.HD_GENLIST);
val GENLIST_FUN_EQ = save_thm("GENLIST_FUN_EQ", listTheory.GENLIST_FUN_EQ);
val GENLIST_APPEND = save_thm("GENLIST_APPEND", listTheory.GENLIST_APPEND);
val EVERY_GENLIST = save_thm("EVERY_GENLIST",listTheory.EVERY_GENLIST);
val EXISTS_GENLIST = save_thm ("EXISTS_GENLIST", listTheory.EXISTS_GENLIST);
val TL_GENLIST = save_thm ("TL_GENLIST",listTheory.TL_GENLIST);
val ZIP_GENLIST = save_thm("ZIP_GENLIST",listTheory.ZIP_GENLIST);
val GENLIST_CONS = save_thm("GENLIST_CONS",listTheory.GENLIST_CONS);

(*---------------------------------------------------------------------------
   A list of numbers
 ---------------------------------------------------------------------------*)

val COUNT_LIST_compute = save_thm ("COUNT_LIST_compute",
    CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV COUNT_LIST);

val COUNT_LIST_GENLIST = store_thm ("COUNT_LIST_GENLIST",
``!n. COUNT_LIST n = GENLIST I n``,
Induct_on `n` THENL [
   SIMP_TAC std_ss [GENLIST, COUNT_LIST],
   ASM_SIMP_TAC std_ss [COUNT_LIST, GENLIST_CONS, MAP_GENLIST]
]);

val LENGTH_COUNT_LIST = store_thm ("LENGTH_COUNT_LIST",
``!n. LENGTH (COUNT_LIST n) = n``,
SIMP_TAC std_ss [COUNT_LIST_GENLIST, LENGTH_GENLIST]);

val EL_COUNT_LIST = store_thm ("EL_COUNT_LIST",
``!m n. m < n ==> (EL m (COUNT_LIST n) = m)``,
SIMP_TAC std_ss [COUNT_LIST_GENLIST, EL_GENLIST]);

val MEM_COUNT_LIST = store_thm ("MEM_COUNT_LIST",
``!m n. MEM m (COUNT_LIST n) = (m < n)``,
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [listTheory.MEM_EL, EL_COUNT_LIST, 
   LENGTH_COUNT_LIST, EL_COUNT_LIST]);

val COUNT_LIST_SNOC = store_thm ("COUNT_LIST_SNOC",
``(COUNT_LIST 0 = []) /\
  (!n. COUNT_LIST (SUC n) = SNOC n (COUNT_LIST n))``,
SIMP_TAC std_ss [COUNT_LIST_GENLIST, GENLIST]);

val COUNT_LIST___COUNT = store_thm ("COUNT_LIST___COUNT",
``!n. LIST_TO_SET (COUNT_LIST n) = count n``,
Induct_on `n` THENL [
   SIMP_TAC std_ss [pred_setTheory.COUNT_ZERO, COUNT_LIST, listTheory.LIST_TO_SET_THM],
   ASM_SIMP_TAC std_ss [COUNT_LIST_SNOC, pred_setTheory.COUNT_SUC,
      listTheory.LIST_TO_SET_APPEND, listTheory.SNOC_APPEND, listTheory.LIST_TO_SET_THM] THEN
   SIMP_TAC std_ss [pred_setTheory.IN_UNION, pred_setTheory.IN_SING, 
       pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT] THEN
   PROVE_TAC[]
]);

val COUNT_LIST___ADD = store_thm ("COUNT_LIST___ADD",
``!n m. COUNT_LIST (n + m) = (COUNT_LIST n) ++ (MAP (\n'. n' + n) (COUNT_LIST m))``,
Induct_on `n` THENL [
   SIMP_TAC std_ss [COUNT_LIST, listTheory.APPEND, listTheory.MAP_ID],

   GEN_TAC THEN
   REWRITE_TAC[COUNT_LIST_SNOC] THEN
   `SUC n + m = n + SUC m` by DECIDE_TAC THEN
   ASM_SIMP_TAC std_ss [COUNT_LIST, MAP, MAP_MAP_o, combinTheory.o_DEF,
      SNOC_APPEND, GSYM APPEND_ASSOC, APPEND] THEN
   SIMP_TAC std_ss [arithmeticTheory.ADD_CLAUSES]
]);


(*---------------------------------------------------------------------------
   General theorems about lists. From Anthony Fox's and Thomas Tuerk's theories.
   Added by Thomas Tuerk
 ---------------------------------------------------------------------------*)

val EL_BUTFIRSTN = store_thm("EL_BUTFIRSTN",
  ``!m n l. m + n < LENGTH l ==>
      (EL m (BUTFIRSTN n l) = EL (m + n) l)``,
  Induct_on `l` THEN SIMP_TAC list_ss [] THEN
  Cases_on `n` THEN FULL_SIMP_TAC list_ss [BUTFIRSTN,ADD_CLAUSES]);

val SNOC_EL_FIRSTN = store_thm("SNOC_EL_FIRSTN",
  ``!n l. n < LENGTH l ==> (SNOC (EL n l) (FIRSTN n l) = FIRSTN (SUC n) l)``,
  Induct_on `n` THEN Cases_on `l` THEN ASM_SIMP_TAC list_ss [SNOC,FIRSTN]);

val ZIP_FIRSTN_LEQ = store_thm("ZIP_FIRSTN_LEQ",
  ``!n a b. n <= LENGTH a /\ LENGTH a <= LENGTH b ==>
     (ZIP (FIRSTN n a,FIRSTN n b) = FIRSTN n (ZIP (a,FIRSTN (LENGTH a) b)))``,
  Induct_on `n` THEN ASM_SIMP_TAC list_ss [FIRSTN] THEN
  Cases_on `a` THEN Cases_on `b` THEN ASM_SIMP_TAC list_ss [FIRSTN,ZIP]);

val ZIP_FIRSTN = store_thm("ZIP_FIRSTN",
  ``!n a b. n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
     (ZIP (FIRSTN n a,FIRSTN n b) = FIRSTN n (ZIP (a,b)))``,
  SIMP_TAC arith_ss [ZIP_FIRSTN_LEQ,FIRSTN_LENGTH_ID]);

val EL_FIRSTN = store_thm("EL_FIRSTN",
  ``!n x l. x < n /\ n <= LENGTH l ==> (EL x (FIRSTN n l) = EL x l)``,
  Induct_on `n` THEN ASM_SIMP_TAC list_ss [FIRSTN] THEN
  Cases_on `x` THEN Cases_on `l` THEN ASM_SIMP_TAC list_ss [FIRSTN]);

val ZIP_APPEND = store_thm("ZIP_APPEND",
  ``!a b c d. (LENGTH a = LENGTH b) /\
              (LENGTH c = LENGTH d) ==>
              (ZIP (a,b) ++ ZIP (c,d) = ZIP (a ++ c,b ++ d))``,
  Induct_on `b` THEN1 SIMP_TAC list_ss [LENGTH_NIL] THEN
  Induct_on `d` THEN1 SIMP_TAC list_ss [LENGTH_NIL] THEN
  Induct_on `a` THEN1 SIMP_TAC list_ss [LENGTH_NIL] THEN
  Induct_on `c` THEN1 SIMP_TAC list_ss [LENGTH_NIL] THEN
  MAP_EVERY Q.X_GEN_TAC [`h1`,`h2`,`h3`,`h4`] THEN
  RW_TAC list_ss [] THEN
  `LENGTH (h1::c) = LENGTH (h3::d)` by ASM_SIMP_TAC list_ss [] THEN
  `ZIP (a,b) ++ ZIP (h1::c,h3::d) = ZIP (a ++ h1::c,b ++ h3::d)`
      by ASM_SIMP_TAC list_ss [] THEN
  FULL_SIMP_TAC list_ss []);


val APPEND_ASSOC_CONS = store_thm (
"APPEND_ASSOC_CONS",
``!l1 h l2 l3.
  (l1 ++ (h::l2) ++ l3 =
   l1 ++ h::(l2++l3))``,
   REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]);

val APPEND_SNOC1 = store_thm("APPEND_SNOC1",
  ``!l1 x l2. SNOC x l1 ++ l2 = l1 ++ x::l2``,
  PROVE_TAC [SNOC_APPEND,CONS_APPEND, APPEND_ASSOC]);

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

val FOLDL_MAP2 = store_thm("FOLDL_MAP2",
  ``!f e g l. FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l``,
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
   THEN ASM_REWRITE_TAC[MAP,FOLDL,FOLDL_SNOC,MAP_SNOC,FOLDR]
   THEN BETA_TAC THEN REWRITE_TAC[]);

val SPLITP_EVERY = store_thm("SPLITP_EVERY",
  ``!P l. EVERY (\x. ~P x) l ==> (SPLITP P l = (l, []))``,
  Induct_on `l` THEN SRW_TAC [] [SPLITP]);

val SPLITP_AUX_lem1 = Q.prove(
  `!P acc l h.
     ~P h ==>
     (h::FST (SPLITP_AUX acc P l) = FST (SPLITP_AUX (h::acc) P l))`,
  Induct_on `l` THEN SRW_TAC [] [SPLITP_AUX_def]);

val SPLITP_AUX_lem2 = Q.prove(
  `!P acc1 acc2 l. SND (SPLITP_AUX acc1 P l) = SND (SPLITP_AUX acc2 P l)`,
  Induct_on `l` THEN SRW_TAC [] [SPLITP_AUX_def]);

val SPLITP_AUX = Q.prove(
  `!P l. SPLITP P l = SPLITP_AUX [] P l`,
  Induct_on `l`
  THEN SRW_TAC [] [SPLITP_AUX_def, SPLITP, SPLITP_AUX_lem1]
  THEN metisLib.METIS_TAC [SPLITP_AUX_lem2, pairTheory.PAIR]);

val SPLITP_AUX = save_thm("SPLITP_AUX",
  REWRITE_RULE [GSYM FUN_EQ_THM] SPLITP_AUX);

val MEM_FRONT = store_thm ("MEM_FRONT",
  ``!l e y. MEM y (FRONT (e::l)) ==> MEM y (e::l)``,
Induct_on `l` THEN FULL_SIMP_TAC list_ss [DISJ_IMP_THM]);

val FRONT_APPEND = store_thm ("FRONT_APPEND",
  ``FRONT (l1 ++ e::l2) = l1++FRONT(e::l2)``,
Induct_on `l1` THEN ASM_SIMP_TAC list_ss [listTheory.FRONT_DEF])

val FRONT_LENGTH = store_thm ("FRONT___LENGTH",
  ``!l. ~(l = []) ==> (LENGTH (FRONT l) = PRE (LENGTH l))``,
  Induct_on `l` THEN FULL_SIMP_TAC list_ss [listTheory.FRONT_DEF, COND_RATOR, COND_RAND] THEN
  Cases_on `l` THEN SIMP_TAC arith_ss [LENGTH]);

val EL_FRONT = store_thm ("EL_FRONT",
  ``!l n. ((n < LENGTH (FRONT l)) /\ ~(NULL l)) ==>
           (EL n (FRONT l) = EL n l)``,
  Induct_on `l` THEN REWRITE_TAC[NULL] THEN
  Cases_on `l` THEN FULL_SIMP_TAC list_ss [NULL, FRONT_LENGTH] THEN
  Cases_on `n` THEN ASM_SIMP_TAC list_ss []);

val LAST_APPEND = store_thm ("LAST_APPEND",
  ``!e l1 l2. LAST (l1 ++ (e::l2)) = LAST (e::l2)``,
  Induct_on `l1` THEN ASM_SIMP_TAC list_ss [listTheory.LAST_DEF]);

val MAP_EQ_f = save_thm ("MAP_EQ_f", listTheory.MAP_EQ_f);

val MEM_LAST = store_thm ("MEM_LAST",
  ``!e l. MEM (LAST (e::l)) (e::l)``,
  Induct_on `l` THEN ASM_SIMP_TAC arith_ss [LAST_CONS, Once listTheory.MEM]);


val BUTFIRSTN_CONS_EL = store_thm ("BUTFIRSTN_CONS_EL",
  ``!n. (n < LENGTH l) ==> ((BUTFIRSTN n l) = (EL n l) :: (BUTFIRSTN (SUC n) l))``,

  Induct_on `l` THEN1 SIMP_TAC list_ss [] THEN
  Cases_on `n` THEN ASM_SIMP_TAC list_ss []);


val ALL_DISTINCT_SNOC = save_thm("ALL_DISTINCT_SNOC", listTheory.ALL_DISTINCT_SNOC)

val MEM_LAST_FRONT = store_thm (
   "MEM_LAST_FRONT",
``!e l h. MEM e l /\ ~(e = LAST (h::l)) ==>
          MEM e (FRONT (h::l))``,

Induct_on `l` THEN
FULL_SIMP_TAC list_ss [COND_RATOR, COND_RAND, listTheory.FRONT_DEF, listTheory.LAST_DEF] THEN
PROVE_TAC[]);


(*---------------------------------------------------------------------------
   LIST_ELEM_COUNT and REPLACE_ELEMENT
   Added by Thomas Tuerk
 ---------------------------------------------------------------------------*)

val LIST_ELEM_COUNT_DEF = new_definition("LIST_ELEM_COUNT_DEF",
    ``LIST_ELEM_COUNT e l = LENGTH (FILTER (\x. x = e) l)``);

val LIST_ELEM_COUNT_THM = store_thm ("LIST_ELEM_COUNT_THM",
  ``(!e. LIST_ELEM_COUNT e [] = 0) /\
    (!e l1 l2. LIST_ELEM_COUNT e (l1++l2) = LIST_ELEM_COUNT e l1 + LIST_ELEM_COUNT e l2) /\
    (!e h l. (h = e) ==> (LIST_ELEM_COUNT e (h::l) = SUC (LIST_ELEM_COUNT e l))) /\
    (!e h l. ~(h = e) ==> (LIST_ELEM_COUNT e (h::l) = LIST_ELEM_COUNT e l))``,
SIMP_TAC list_ss [LIST_ELEM_COUNT_DEF, FILTER_APPEND]);

val LIST_ELEM_COUNT_MEM = store_thm ("LIST_ELEM_COUNT_MEM",
  ``!e l. (LIST_ELEM_COUNT e l > 0) = (MEM e l)``,
  Induct_on `l` THEN
  FULL_SIMP_TAC list_ss [LIST_ELEM_COUNT_DEF,
                         COND_RAND, COND_RATOR] THEN
  PROVE_TAC[]);



local
   val REPLACE_ELEMENT_exists = prove (``?fn.
                (!e:'a n:num. fn e n ([]:'a list) = []:'a list) /\
                (!e x l. fn e 0 (x::l) = e::l) /\
                (!e n x l. fn e (SUC n) (x::l) = CONS x (fn e n l))``,
                REPEAT STRIP_TAC THEN
                STRIP_ASSUME_TAC (ISPECL [``(\x1 x2. []):'a -> num -> 'a list``,
                ``\(x:'a) (l:'a list) (r:'a->num->'a list) (e:'a) (n:num). if n = 0 then e::l else
				     (CONS x (r e (PRE n)):'a list)``] list_Axiom) THEN
                Q.EXISTS_TAC `\x1 x2 x3. fn x3 x1 x2` THEN
                ASM_SIMP_TAC arith_ss []);
in

   val REPLACE_ELEMENT_DEF = Rsyntax.new_specification{name = "REPLACE_ELEMENT_DEF",
                      sat_thm = REPLACE_ELEMENT_exists,
                      consts =  [{const_name = "REPLACE_ELEMENT", fixity = NONE}]
                     };
end;

val REPLACE_ELEMENT_SEM = store_thm (
  "REPLACE_ELEMENT_SEM",
  ``(!e:'a n l. (LENGTH (REPLACE_ELEMENT e n l) = LENGTH l)) /\
    (!e:'a n l p. p < LENGTH l ==>
            (EL p (REPLACE_ELEMENT e n l) =
             if (p = n) then e else EL p l))``,

CONJ_TAC THEN Induct_on `n` THEN Cases_on `l` THEN
ASM_SIMP_TAC arith_ss [REPLACE_ELEMENT_DEF, LENGTH] THEN
Cases_on `p` THEN ASM_SIMP_TAC arith_ss [EL, HD, TL]);


(*---------------------------------------------------------------------------*)
(* Add evaluation theorems to computeLib.the_compset                         *)
(*---------------------------------------------------------------------------*)

val COUNT_LIST_AUX_lem = Q.prove(
  `!n l1 l2. COUNT_LIST_AUX n l1 ++ l2 = COUNT_LIST_AUX n (l1 ++ l2)`,
  Induct THEN SRW_TAC [] [COUNT_LIST_AUX_def]);

val COUNT_LIST_AUX = Q.store_thm("COUNT_LIST_AUX",
  `!n. COUNT_LIST n = COUNT_LIST_AUX n []`,
  Induct THEN SRW_TAC [] [COUNT_LIST_GENLIST, GENLIST, COUNT_LIST_AUX_def]
  THEN FULL_SIMP_TAC (srw_ss()) [COUNT_LIST_GENLIST, COUNT_LIST_AUX_lem]);

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val ELL_compute = save_thm("ELL_compute", SUC_RULE ELL);
val SEG_compute = save_thm("SEG_compute", SUC_RULE SEG);
val FIRSTN_compute = save_thm("FIRSTN_compute", SUC_RULE FIRSTN);
val GENLIST_compute = save_thm("GENLIST_compute", SUC_RULE GENLIST);
val BUTFIRSTN_compute = save_thm("BUTFIRSTN_compute", SUC_RULE BUTFIRSTN);
val IS_SUFFIX_compute = save_thm("IS_SUFFIX_compute", GSYM IS_PREFIX_REVERSE);
val REPLICATE_compute = save_thm("REPLICATE_compute", SUC_RULE REPLICATE);

val BUTLASTN_compute = Q.store_thm("BUTLASTN_compute",
  `!n l. BUTLASTN n l =
     let m = LENGTH l in
       if n <= m then FIRSTN (m - n) l
       else FAIL BUTLASTN ^(mk_var("longer than list",bool)) n l`,
  SRW_TAC [boolSimps.LET_ss] [combinTheory.FAIL_THM,BUTLASTN_FIRSTN]);

val LASTN_compute = Q.store_thm("LASTN_compute",
  `!n l. LASTN n l =
     let m = LENGTH l in
       if n <= m then BUTFIRSTN (m - n) l
       else FAIL LASTN ^(mk_var("longer than list",bool)) n l`,
  SRW_TAC [boolSimps.LET_ss] [combinTheory.FAIL_THM,LASTN_BUTFIRSTN]);

val _ = computeLib.add_persistent_funs
 [("AND_EL_DEF", AND_EL_DEF),
  ("BUTFIRSTN_compute", BUTFIRSTN_compute),
  ("BUTLASTN_compute", BUTLASTN_compute),
  ("ELL_compute", ELL_compute),
  ("FIRSTN_compute", FIRSTN_compute),
  ("COUNT_LIST_AUX", COUNT_LIST_AUX),
  ("IS_SUBLIST", IS_SUBLIST),
  ("IS_SUFFIX_compute", IS_SUFFIX_compute),
  ("LASTN_compute", LASTN_compute),
  ("OR_EL_DEF", OR_EL_DEF),
  ("PREFIX_DEF", PREFIX_DEF),
  ("REPLICATE_compute", REPLICATE_compute),
  ("SCANL", SCANL),
  ("SCANR", SCANR),
  ("SEG_compute", SEG_compute),
  ("SNOC", SNOC),
  ("SPLITP_AUX", SPLITP_AUX),
  ("SUFFIX_DEF", SUFFIX_DEF),
  ("UNZIP_FST_DEF", UNZIP_FST_DEF),
  ("UNZIP_SND_DEF", UNZIP_SND_DEF)];

val _ = export_theory();

end
