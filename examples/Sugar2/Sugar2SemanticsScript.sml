(*****************************************************************************)
(* Create "Sugar2SemanticsTheory" containing abstract syntax and semantics   *)
(* of the basic language, following the Accellera documentation              *)
(*****************************************************************************)

(******************************************************************************
* In the Sugar 2 documentation: 
*
*    http://www.haifa.il.ibm.com/projects/verification/sugar/literature.html
* 
* a model is a quintuple (S,S0,R,P,L) where
* 
*  - S  is a set of states
*  - S0 is a subset of S, the initial states
*  - R  is a transition relation 
*  - P  is a set of atomic proposition
*  - L  maps each state to the set of propositions true in that state
* 
******************************************************************************)

(******************************************************************************
* Load theory of paths and additional definitions of functions on lists 
* (commented out for compilation)
******************************************************************************)
(*
load "PathTheory"; load "rich_listTheory"; load "intLib";
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open Globals HolKernel Parse boolLib;
infixr 3 -->;
infix 8 by;
infix &&;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open bossLib;

(******************************************************************************
* Open theories of paths and lists
******************************************************************************)
open PathTheory listTheory rich_listTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

(******************************************************************************
* Start a new theory called Sugar2Semantics
******************************************************************************)
val _ = new_theory "Sugar2Semantics";

(******************************************************************************
* Boolean expressions (added B_TRUE for use in definition of F_SEM)
******************************************************************************)
val bexp_def =
 Hol_datatype
  `bexp = B_PROP   of 'a                    (* atomic proposition            *)
        | B_TRUE                            (* truth                         *)
        | B_NOT    of bexp                  (* negation: \neg p              *)
        | B_AND    of bexp # bexp`;         (* conjunction: r1 \wedge r2     *)

(******************************************************************************
* Sugar Extended Regular Expressions (SEREs) 
******************************************************************************)
val sere_def =
 Hol_datatype
  `sere = S_BOOL        of 'a bexp               (* boolean expression       *)
        | S_CAT         of sere # sere           (* r1 ;  r2                 *)
        | S_FUSION      of sere # sere           (* r1 :  r2                 *)
        | S_OR          of sere # sere           (* r1 |  r2                 *)
        | S_RIG_AND     of sere # sere           (* r1 && r2                 *)
        | S_FLEX_AND    of sere # sere           (* r1 & r2                  *)
        | S_REPEAT      of sere                  (* r[*]                     *)
        | S_CLOCK       of sere # 'a bexp`;      (* r@clk                    *)

(******************************************************************************
* Formulas of Sugar Foundation Language (FL)
******************************************************************************)
val fl_def =
 Hol_datatype
  `fl = F_BOOL         of 'a bexp                (* boolean expression       *)
      | F_NOT          of fl                     (* \neg f                   *)
      | F_AND          of fl # fl                (* f1 \wedge f2             *)
      | F_NEXT         of fl                     (* X! f                     *)
      | F_UNTIL        of fl # fl                (* [f1 U f2]                *)
      | F_SUFFIX_IMP   of 'a sere # fl           (* {r}(f)                   *)
      | F_STRONG_IMP   of 'a sere # 'a sere      (* r1 |-> r2!               *)
      | F_WEAK_IMP     of 'a sere # 'a sere      (* r1 |-> r2                *)
      | F_ABORT        of fl # 'a bexp           (* f abort b                *)
      | F_WEAK_CLOCK   of fl # 'a bexp           (* r@clk                    *)
      | F_STRONG_CLOCK of fl # 'a bexp`;         (* r@clk!                   *)

(******************************************************************************
* Formulas of Sugar Optional Branching Extension (OBE)
******************************************************************************)
val obe_def =
 Hol_datatype
  `obe = O_BOOL        of 'a bexp                (* boolean expression       *)
       | O_NOT         of obe                    (* \neg f                   *)
       | O_AND         of obe # obe              (* f1 \wedge f2             *)
       | O_EX          of obe                    (* EX f                     *)
       | O_EU          of obe # obe              (* E[f1 U f2]               *)
       | O_EG          of obe`;                  (* EG f                     *)

(******************************************************************************
* Stop ``S`` parsing to the S-combinator
******************************************************************************)
val _ = hide "S";

(******************************************************************************
* Selectors for components of a model M = (S,S0,R,P,L)
******************************************************************************)

val getS_def  = Define `getS  (S,S0,R,P,L) = S`;
val getS0_def = Define `getS0 (S,S0,R,P,L) = S0`;
val getR_def  = Define `getR  (S,S0,R,P,L) = R`;
val getP_def  = Define `getP  (S,S0,R,P,L) = P`;
val getL_def  = Define `getL  (S,S0,R,P,L) = L`;

(******************************************************************************
* B_SEM M l b means "l |= b" 
* and also that b only contains atomic propositions in getP M
******************************************************************************)
val B_SEM_def =
 Define
  `(B_SEM M l (B_PROP(p:'p)) = p IN (getP M) /\ p IN l)
   /\
   (B_SEM M l B_TRUE         = T)
   /\
   (B_SEM M l (B_NOT b)      = ~(B_SEM M l b))
   /\
   (B_SEM M l (B_AND(b1,b2)) = B_SEM M l b1 /\ B_SEM M l b2)`;

(******************************************************************************
* S_SEM M w c r means "w is in the language of r in context c"
******************************************************************************)
val S_SEM_def =
 Define
  `(S_SEM M w c (S_BOOL b) = 
     ?n. n >= 1                                               /\ 
         (LENGTH w = n)                                       /\ 
         (!i. 1 <= i /\ i < n ==> B_SEM M (EL (i-1) w) (B_NOT c)) /\
         B_SEM M (EL (n-1) w) (B_AND(c,b)))
   /\
   (S_SEM M w c (S_CAT(r1,r2)) = 
     ?w1 w2. (w = w1 <> w2) /\ S_SEM M w1 c r1 /\ S_SEM M w2 c r2)
   /\
   (S_SEM M w c (S_FUSION(r1,r2)) = 
     ?w1 w2 l. (w = w1 <> [l] <> w2) /\ 
               S_SEM M (w1<>[l]) c r1 /\ S_SEM M ([l]<>w2) c r2) 
   /\
   (S_SEM M w c (S_OR(r1,r2)) = 
     S_SEM M w c r1 \/ S_SEM M w c r2) 
   /\
   (S_SEM M w c (S_RIG_AND(r1,r2)) = 
     S_SEM M w c r1 /\ S_SEM M w c r2) 
   /\
   (S_SEM M w c (S_FLEX_AND(r1,r2)) = 
     ?w1 w2. (w = w1 <> w2) /\ 
             ((S_SEM M w c r1 /\ S_SEM M w1 c r2) 
              \/
              (S_SEM M w c r2 /\ S_SEM M w1 c r1) ))
   /\
   (S_SEM M w c (S_REPEAT r) = 
     ?wlist. (w = CONCAT wlist) /\ EVERY (\w. S_SEM M w c r) wlist)
   /\
   (S_SEM M w c (S_CLOCK(r,c1)) =
     S_SEM M w c1 r)`;

(******************************************************************************
* Contexts (strong or weak clock)
******************************************************************************)
val context_def =
 Hol_datatype
  `context = STRONG_CLOCK  of 'a bexp       (* strong clock: c!              *)
           | WEAK_CLOCK    of 'a bexp`;     (* weak clock:  c                *)

(******************************************************************************
* FIRST_RISE M p c i  =  LHAT(p(0,i))  |=T=  {(\neg c)[*];c}
* (i is the first rising edge of clock c in path p)
******************************************************************************)
val FIRST_RISE_def =
 Define
  `FIRST_RISE M p c i =
    S_SEM
     M
     (MAP (getL M) (PATH_SEG p (0,i)))
     B_TRUE
     (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))`;

(******************************************************************************
* NEXT_RISE M p c (i,j)  =   Lhat(p(i,j))  |=T=  {(\neg c)[*];c}
* (i is the first rising edge after j of clock c in path p)
******************************************************************************)
val NEXT_RISE_def =
 Define
  `NEXT_RISE M p c (i,j) =
    S_SEM
     M
     (MAP (getL M) (PATH_SEG p (i,j)))
     B_TRUE
     (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))`;

(******************************************************************************
* L and \hat{L}
******************************************************************************)
val L_def    = Define `L M = getL M`;
val LHAT_def = Define `LHAT M = MAP (getL M)`;

(******************************************************************************
* Definition due to Konrad Slind that uses
* cunning feature of TFL to prove that F_SEM is total
******************************************************************************)
val F_SEM_defn = 
  Hol_defn 
  "F_SEM"
  `(F_SEM M p (STRONG_CLOCK c) (F_BOOL b) = 
      ?i. FIRST_RISE M p c i /\ B_SEM M (L M (PATH_EL p i)) b)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_NOT f) = 
      ~(F_SEM M p (WEAK_CLOCK c) f))
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_AND(f1,f2)) = 
      ?i. FIRST_RISE M p c i                      /\ 
          F_SEM M (RESTN p i) (STRONG_CLOCK c) f1 /\
          F_SEM M (RESTN p i) (STRONG_CLOCK c) f2)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_NEXT f) = 
      ?i. FIRST_RISE M p c i                           /\ 
          (IS_FINITE_PATH p ==> i < PATH_LENGTH p - 1) /\
          F_SEM M (RESTN p (i+1)) (STRONG_CLOCK c) f)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_UNTIL(f1,f2)) = 
      ?i k. k >= i                                               /\
            (IS_FINITE_PATH p ==> k < PATH_LENGTH p)             /\
            FIRST_RISE M p c i                                   /\
            F_SEM M (RESTN p k) (WEAK_CLOCK B_TRUE) (F_BOOL c)   /\  
            F_SEM M (RESTN p k) (STRONG_CLOCK c) f2              /\
            !j. i <= j /\ j < k /\ 
              F_SEM M (RESTN p j) (WEAK_CLOCK B_TRUE) (F_BOOL c) 
              ==>
              F_SEM M (RESTN p j) (STRONG_CLOCK c) f1)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_SUFFIX_IMP(r,f)) = 
      ?i. FIRST_RISE M p c i /\ 
          !j. S_SEM M (LHAT M (PATH_SEG p (i,j))) c r
              ==>
              F_SEM M (RESTN p j) (STRONG_CLOCK c) f)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2)) = 
      ?i. FIRST_RISE M p c i /\ 
          !j. S_SEM M (LHAT M (PATH_SEG p (i,j))) c r1
              ==>
              ?k. S_SEM M (LHAT M (PATH_SEG p (j,k))) c r2)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
     F_SEM M p (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2))
      \/
     (F_SEM M p (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2))
      /\
      !j. (IS_FINITE_PATH p ==> j < PATH_LENGTH p)
          ==>
          ?k. NEXT_RISE M p c (j,k)))
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_ABORT (f,b)) =
      ?i. FIRST_RISE M p c i /\
          (F_SEM M (RESTN p i) (STRONG_CLOCK c) f 
           \/
           ?j p'. 
             F_SEM M (RESTN p j) (WEAK_CLOCK B_TRUE) (F_BOOL(B_AND(c,b))) /\ 
             F_SEM M (PATH_CAT(PATH_SEG p (i,j-1),p')) (STRONG_CLOCK c) f))
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_WEAK_CLOCK(f,c1)) =   
      F_SEM M p (WEAK_CLOCK c1) f)
    /\
    (F_SEM M p (STRONG_CLOCK c) (F_STRONG_CLOCK(f,c1)) =   
      F_SEM M p (STRONG_CLOCK c1) f)
    /\ 
(******************************************************************************
* Start of weak clock clauses
******************************************************************************)
   (F_SEM M p (WEAK_CLOCK c) (F_BOOL b) =
     (!i. FIRST_RISE M p c i ==> B_SEM M (L M (PATH_EL p i)) b))
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_NOT f) = 
      ~(F_SEM M p (STRONG_CLOCK c) f)) 
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_AND(f1,f2)) = 
      !i. FIRST_RISE M p c i
          ==>
          (F_SEM M (RESTN p i) (WEAK_CLOCK c) f1 /\
           F_SEM M (RESTN p i) (WEAK_CLOCK c) f2))
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_NEXT f) = 
      !i. FIRST_RISE M p c i 
          ==>
          (IS_FINITE_PATH p ==> i < PATH_LENGTH p - 1)
          /\
          F_SEM M (RESTN p (i+1)) (WEAK_CLOCK c) f)
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_UNTIL(f1,f2)) = 
      F_SEM M p (STRONG_CLOCK c) (F_UNTIL(f1,f2))  
      \/
      (?k. !l. l > k
               ==>
               F_SEM M (RESTN p l) (WEAK_CLOCK B_TRUE) (F_BOOL(B_NOT c))   /\ 
               !j. j <= k 
                   ==>
                   F_SEM M (RESTN p j) (WEAK_CLOCK B_TRUE) (F_BOOL c)
                   ==>
                   F_SEM M (RESTN p j) (WEAK_CLOCK c) f1))
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_SUFFIX_IMP(r,f)) = 
      !i. FIRST_RISE M p c i ==>
          !j. S_SEM M (LHAT M (PATH_SEG p (i,j))) c r
              ==>
              F_SEM M (RESTN p j) (WEAK_CLOCK c) f)
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_STRONG_IMP(r1,r2)) = 
      F_SEM M p (STRONG_CLOCK c) (F_STRONG_IMP(r1,r2))  
      \/
      (F_SEM M p (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)) 
       /\
       ?k. !l. l > k 
               ==> 
               F_SEM M (RESTN p l) (WEAK_CLOCK B_TRUE) (F_BOOL(B_NOT c))))
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_WEAK_IMP(r1,r2)) = 
      !i. FIRST_RISE M p c i
          ==>
          !j. S_SEM M (LHAT M (PATH_SEG p (i,j))) c r1
              ==>
              ((?k. S_SEM M (LHAT M (PATH_SEG p (j,k))) c r2)
               \/
               !k. (IS_FINITE_PATH p ==> k < PATH_LENGTH p)
                   ==>
                   ?w. S_SEM M (LHAT M (PATH_SEG p (j,k)) <> w) c r2))
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_ABORT (f,b)) =
      !i. FIRST_RISE M p c i 
          ==>
          (F_SEM M (RESTN p i) (WEAK_CLOCK c) f 
           \/
           ?j p'. 
            F_SEM M (RESTN p j) (WEAK_CLOCK B_TRUE) (F_BOOL(B_AND(c,b)))
            /\
            F_SEM M (PATH_CAT(PATH_SEG p (i,j-1),p')) (WEAK_CLOCK c) f))
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_WEAK_CLOCK(f,c1)) =   
      F_SEM M p (WEAK_CLOCK c1) f)
    /\
    (F_SEM M p (WEAK_CLOCK c) (F_STRONG_CLOCK(f,c1)) =   
      F_SEM M p (STRONG_CLOCK c1) f)`;

val new_fl_size_def = 
 Define `(new_fl_size (F_BOOL _) = 0) /\
         (new_fl_size other      = fl_size (\a.0) other)`;

val new_context_size_def = 
  Define `(new_context_size (STRONG_CLOCK _) = 0) /\
          (new_context_size (WEAK_CLOCK _) = 1)`;

val (F_SEM_def, F_SEM_ind) = Count.apply Defn.tprove
 (F_SEM_defn,
  WF_REL_TAC `inv_image ($< LEX $<) 
                (\(u,v,w,x). 
                   (if (?c d. ((w = WEAK_CLOCK c) /\ (x = F_WEAK_IMP d)) \/
                              ((w = STRONG_CLOCK c) /\ (x = F_STRONG_IMP d)))
                        then 0 else new_fl_size x, 
                      new_context_size w))`
   THEN EVAL_TAC THEN RW_TAC arith_ss [DECIDE (Term `0 < 1 + x`)]
   THEN ((Cases_on `f` THEN EVAL_TAC THEN DECIDE_TAC) ORELSE
         (Cases_on `f1` THEN EVAL_TAC THEN DECIDE_TAC) ORELSE
         (Cases_on `f2` THEN EVAL_TAC THEN DECIDE_TAC)));

val _ = save_thm("F_SEM_def",F_SEM_def);
val _ = save_thm("F_SEM_ind",F_SEM_ind);

(******************************************************************************
* PATH M p is true iff p is a path with respect to transition relation getR M
******************************************************************************)
val PATH_def = Define `PATH M p = !n. (getR M)(PATH_EL p n, PATH_EL p (n+1))`;

(******************************************************************************
* O_SEM M s f means "M, s |= f" 
******************************************************************************)
val O_SEM_def =
 Define
  `(O_SEM M s (O_BOOL b) = B_SEM M (L M s) b)
   /\
   (O_SEM M s (O_NOT f) = ~(O_SEM M s f)) 
   /\
   (O_SEM M s (O_AND(f1,f2)) = O_SEM M s f1 /\ O_SEM M s f2)
   /\
   (O_SEM M s (O_EX f) = 
     ?p. PATH M p                                 /\ 
         (IS_FINITE_PATH p ==> 1 < PATH_LENGTH p) /\ 
         (PATH_EL p 0 = s) /\ O_SEM M (PATH_EL p 1) f)
   /\
   (O_SEM M s (O_EU(f1,f2)) = 
     ?p. PATH M p          /\ 
         (PATH_EL p 0 = s) /\ 
         ?k. (IS_FINITE_PATH p ==> k < PATH_LENGTH p) /\
             O_SEM M (PATH_EL p k) f2                 /\ 
             !j. j < k ==> O_SEM M (PATH_EL p j) f1)
   /\
   (O_SEM M s (O_EG f) = 
     ?p. PATH M p /\ 
         (PATH_EL p 0 = s) /\
         !j. (IS_FINITE_PATH p ==> j < PATH_LENGTH p) ==> O_SEM M (PATH_EL p j) f)`;

val _ = export_theory();







