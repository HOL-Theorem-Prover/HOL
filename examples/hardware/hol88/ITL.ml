
%----------------------------------------------------------------------------%
% The stuff in this file is just `doodlings` and does not work!              %
%----------------------------------------------------------------------------%

new_theory`ITL`;;

% Test if an interval function only depends on the start time
  of the interval %

new_definition
 (`IS_SIG`,
  "IS_SIG (X:num->num->*) = ?f. !m n. X m n = f m");;

% Make an interval function out of a signal %

new_definition
 (`MK_SIG`, 
  "MK_SIG (f:num->*) = \m (n:num). f m");;

% Test if an interval function is a constant function %

new_definition
 (`IS_STATIC`,
  "IS_STATIC (X:num->num->*) = ?c. !m n. X m n = c");;

% Make an interval function out of a constant %

new_definition
 (`MK_STATIC`,
  "MK_STATIC (c:*) = \m:num.\n:num. c");;

% The ITL next operator for expressions. This is called "O" in Ben's papers
  but I use that name for the next operator for formulas (see below) %

new_definition
 (`NEXT`,
  "NEXT (X:num->num->*) = \m n. X (m+1) n");;

% ITL Equality %

new_infix_definition
 (`==`,
  "== (X:num->num->*) (Y:num->num->*) = \m n. ((X m n) = (Y m n))");;

% ITL negation %

new_definition
 (`NOT`,
  "NOT (X:num->num->bool) = \m n. ~(X m n)");;

% ITL conjunction %

new_infix_definition
 (`AND`, 
  "AND (X:num->num->bool) (Y:num->num->bool) = 
   \m n. (X m n) /\ (Y m n)");;

% The ITL next operator for formulas %

new_definition
 (`O`,
  "O X = \m n. (n > m) /\ X (m+1) n");;

% The ITL always operator %

new_definition
 (`BOX`,
  "BOX X = \m n. !i. (m <= i) /\ (i <= n) ==> X i n");;

% ITL chop operator (";" in Ben's notation - HOL won't allow ";" to be
  made an infix) %

new_infix_definition
 (`THEN`,
  "THEN X Y = \m n. ?i. (m<=i) /\ (i<=n) /\ (X m i) /\ (Y i n)");;

% ITL existential quantification %

new_binder_definition
 (`EXISTS`,
  "EXISTS (P:(num->num->*)->num->num->bool) = \m n. ?X. (P X m n)");;

% The ITL validity predicate ("|=" in standard notation) %

new_definition
 (`VALID`,
  "VALID (X:num->num->bool) = !m n. X m n");;


% Now for some derived constants and operators %

new_definition(`TRUE` , "TRUE  = MK_STATIC T");;
new_definition(`FALSE`, "FALSE = MK_STATIC F");;

new_definition(`ZERO`, "ZERO = MK_STATIC 0");;
new_definition(`ONE` , "ONE  = MK_STATIC 1");;
new_definition(`TWO` , "TWO  = MK_STATIC 2");;

new_infix_definition
 (`OR`,
  "OR X Y = NOT(NOT X AND NOT Y)");;

new_infix_definition
 (`IMPLIES`,
  "IMPLIES X Y = NOT X OR Y");;

new_definition
 (`EMPTY`,
  "EMPTY = NOT(O TRUE)");;

new_definition
 (`SKIP`,
  "SKIP = O EMPTY");;

new_infix_definition
 (`GETS`,
  "GETS (X:num->num->*) (Y:num->num->*) =
    BOX(NOT EMPTY IMPLIES (NEXT X == Y))");;

% ITL stability operator %

new_definition
 (`STABLE`,
  "STABLE(X:num->num->*) = X GETS X");;

new_definition
 (`FIN`,
  "FIN X = BOX(EMPTY IMPLIES X)");;

hide_constant `S`;;

new_infix_definition
 (`-->`,
  "--> (X:num->num->*) (Y:num->num->*) =
    EXISTS S. IS_STATIC S AND (S == X) AND FIN(S == Y)");;
  
% Some useful lemmas %

let defs = 
 maptok 
  (definition `ITL`)
  `IS_SIG MK_SIG IS_STATIC MK_STATIC NEXT == NOT AND O BOX THEN
   EXISTS VALID TRUE FALSE ZERO ONE TWO OR IMPLIES EMPTY GETS STABLE`;;

let TRUE_SEM  = prove_thm(`TRUE_SEM` , "TRUE  = \m n. T", REWRITE_TAC defs)
and FALSE_SEM = prove_thm(`FALSE_SEM`, "FALSE = \m n. F", REWRITE_TAC defs)
and ZERO_SEM  = prove_thm(`ZERO_SEM` , "ZERO  = \m n. 0", REWRITE_TAC defs)
and ONE_SEM   = prove_thm(`ONE_SEM`  , "ONE   = \m n. 1", REWRITE_TAC defs)
and TWO_SEM   = prove_thm(`TWO_SEM`  , "TWO   = \m n. 2", REWRITE_TAC defs);;

let OR_SEM =
 prove_thm
  (`OR_SEM`,
   "OR (X:num->num->bool) (Y:num->num->bool) = \m n. (X m n) \/ (Y m n)",
   REWRITE_TAC defs
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM]);;

let OR_IMP_THM =
 prove_thm
  (`OR_IMP_THM`,
   "(~t1 \/ t2) = (t1 ==> t2)",
   BOOL_CASES_TAC "t1:bool"
    THEN REWRITE_TAC[]);;

let IMPLIES_SEM =
 prove_thm
  (`IMPLIES_SEM`,
   "IMPLIES (X:num->num->bool) (Y:num->num->bool) = 
    \m n. (X m n) ==> (Y m n)",
   REWRITE_TAC(OR_SEM.defs)
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[OR_IMP_THM]);;

let EMPTY_SEM =
 prove_thm
  (`EMPTY_SEM`,
   "EMPTY = \m n. n<=m",
   REWRITE_TAC(TRUE_SEM.defs)
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[NOT_LESS;GREATER]);;

let IMP_CONJ_THM =
prove_thm
 (`IMP_CONJ_THM`,
  "(t1 ==> t2 ==> t3) = (t1 /\ t2 ==> t3)",
  BOOL_CASES_TAC "t1:bool"
   THEN REWRITE_TAC[]);;

let LESS_AND_LESS_EQ_THM =
 prove_thm
  (`LESS_AND_LESS_EQ_THM`,
   "m <= n /\ m < n = m < n",
   EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[LESS_OR_EQ]);;

let GETS_SEM =
 prove_thm
  (`GETS_SEM`,
   "GETS (X:num->num->*) (Y:num->num->*) =
    \m n. !i. (m<=i) /\ (i<n) ==> (X(SUC i)n = Y i n)",
   REWRITE_TAC(EMPTY_SEM.IMPLIES_SEM.defs)
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC
          [ADD1;IMP_CONJ_THM;
           GREATER;LESS_AND_LESS_EQ_THM;SYM(SPEC_ALL CONJ_ASSOC)]);;

% The following is not yet done

let STABLE_SEM_LEMMA
 prove_thm
  (`STABLE_SEM_LEMMA`,
   "STABLE (X:num->num->*) m n = !i. (m<=i) /\ (i<=n) ==> (X i n = X m n)",
   REWRITE_TAC [definition `ITL` `STABLE`;GETS_SEM]
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]

Need to prove:


5 subgoals
"X(SUC(SUC i))n = X(SUC i)n"
    [ "!i. m <= i /\ i <= n ==> (X i n = X m n)" ]
    [ "m <= i /\ i < n ==> (X(SUC i)n = X i n)" ]
    [ "m = SUC i" ]
    [ "(SUC i) < n" ]

"X(SUC(SUC i))n = X(SUC i)n"
    [ "!i. m <= i /\ i <= n ==> (X i n = X m n)" ]
    [ "m <= i /\ i < n ==> (X(SUC i)n = X i n)" ]
    [ "m < (SUC i)" ]
    [ "(SUC i) < n" ]

"X(SUC 0)n = X 0 n"
    [ "!i. m <= i /\ i <= n ==> (X i n = X m n)" ]
    [ "m = 0" ]
    [ "0 < n" ]

"X n n = X m n"
    [ "!i. m <= i /\ i < n ==> (X(SUC i)n = X i n)" ]
    [ "m <= i /\ i <= n ==> (X i n = X m n)" ]
    [ "m < (SUC i)" ]
    [ "SUC i = n" ]

"X(SUC i)n = X m n"
    [ "!i. m <= i /\ i < n ==> (X(SUC i)n = X i n)" ]
    [ "m <= i /\ i <= n ==> (X i n = X m n)" ]
    [ "m < (SUC i)" ]
    [ "(SUC i) < n" ]


let STABLE_SEM
 prove_thm
  (`STABLE_SEM`,
   "STABLE (X:num->num->*) = \m n. !i. (m<=i) /\ (i<=n) ==> (X i n = X m n)",
   REWRITE_TAC [definition `ITL` `STABLE`;GETS_SEM]

must prove:

"(\m n. !i. m <= i /\ i < n ==> (X(SUC i)n = X i n)) =
 (\m n. !i. m <= i /\ i <= n ==> (X i n = X m n))"
%


% Now we prove a theorem suggested by Ben %

let SUB_REFL =
 prove_thm
  (`SUB_REFL`,
   "!m. (m - m) = 0",
   INDUCT_TAC
    THEN REWRITE_TAC[SUB;LESS_SUC_REFL]);;

let SUC_SUB_LEMMA =
 prove_thm
  (`SUC_SUB_LEMMA`,
   "(n <= m) ==> ((SUC m) - n = (m - n) + 1)",
   REWRITE_TAC[SUB;ADD1;SYM(SPEC_ALL NOT_LESS)]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]);;

% Some arithmetic operators %

new_infix_definition
 (`++`,
  "++ X Y = \m n. (X m n) + (Y m n)");;

new_infix_definition
 (`**`,
  "** X Y = \m n. (X m n) * (Y m n)");;

let defs_sem = 
 [IMPLIES_SEM;GETS_SEM] @
 subtract defs (maptok (definition `ITL`) `IMPLIES GETS`) @
 maptok (definition `ITL`) `++ **`;;

prove_thm
 (`BENS_THM`,
  "VALID (EXISTS X. (X == ZERO) AND (X GETS (X ++ ONE)))",
  REWRITE_TAC defs_sem
   THEN CONV_TAC(DEPTH_CONV BETA_CONV)
   THEN REPEAT GEN_TAC
   THEN EXISTS_TAC"\m' n.(m'-m)"
   THEN CONV_TAC(DEPTH_CONV BETA_CONV)
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC LESS_EQ_TRANS
   THEN IMP_RES_TAC SUC_SUB_LEMMA
   THEN REWRITE_TAC[SUB_REFL]);;

let g:goal =
 ([], "VALID(((I == ZERO)          AND
              (J == ZERO)          AND
              (I GETS (I ++ ONE))  AND
              (J GETS (J ++ TWO))) IMPLIES
              BOX(J == (TWO ** I)))");;

% Proof not yet done ... feel free to finish it!

prove_thm
 (`ROGERS_THM`,
  "VALID(((I == ZERO)          AND
          (J == ZERO)          AND
          (I GETS (I ++ ONE))  AND
          (J GETS (J ++ TWO))) IMPLIES
          BOX(J == (TWO ** I)))",
  REWRITE_TAC defs_sem
   THEN CONV_TAC(DEPTH_CONV BETA_CONV)
   THEN REPEAT GEN_TAC
   THEN REPEAT STRIP_TAC
   THEN INDUCT_TAC

%
