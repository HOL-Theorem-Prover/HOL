(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(*---------------------------------------------------------------------------*)

app load ["stringLib", "metisLib"]; open metisLib;

(*---------------------------------------------------------------------------*)
(* Misc. syntax modifications                                                *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);

(*---------------------------------------------------------------------------*)
(* Concatenate a list of lists                                               *)
(*---------------------------------------------------------------------------*)

val CONCAT_def =
 Define `(CONCAT [] = []) /\ (CONCAT(l::ll) = l <> CONCAT ll)`;


val NULL_EQ_NIL = Q.prove
(`!l. NULL l = (l = [])`,
 Cases THEN RW_TAC list_ss []);

val CONCAT_NIL = Q.prove
(`!wlist. (CONCAT wlist = []) = EVERY NULL wlist`,
 Induct THEN RW_TAC list_ss [CONCAT_def,NULL_EQ_NIL]);

(*---------------------------------------------------------------------------*)
(* Datatype of regular expressions                                           *)
(*---------------------------------------------------------------------------*)

Hol_datatype `regexp = Any                       (* Any character *)
                     | Epsilon                   (* Empty string *)
                     | Atom of char              (* Specific character *)
                     | Or of regexp => regexp    (* Union *)
                     | Then of regexp => regexp  (* Concatenation *)
                     | Repeat of regexp`;        (* Iterated concat, >= 0 *)

(*---------------------------------------------------------------------------*)
(* Following mysterious invocations remove old-style syntax for conditionals *)
(* from the grammar and thus allow | to be used for "or" patterns.           *)
(*---------------------------------------------------------------------------*)

val _ = remove_termtok{term_name = "COND",tok="=>"};  
val _ = overload_on ("|", Term`$Or`);
val _ = overload_on ("#", Term`$Then`);

val _ = set_fixity "|" (Infixr 501);
val _ = set_fixity "#" (Infixr 601);


(*---------------------------------------------------------------------------*)
(* Checker - as a tail recursion.                                            *)
(*---------------------------------------------------------------------------*)

val match_defn = Hol_defn "match"
  `(match [] l               = SOME l)                            /\
   (match (Epsilon::t) l     = match t l)                         /\ 
   (match (Any::t) (_::u)    = match t u)                         /\
   (match (Any::t)    []     = NONE)                              /\
   (match (Atom c::t) []     = NONE)                              /\
   (match (Atom c::t) (h::u) = if h=c then match t u else NONE)   /\
   (match (r1 | r2::t) l     = if match (r1::t) l = SOME [] 
                               then SOME [] else match (r2::t) l) /\
   (match (r1 # r2::t) l     = match (r1::r2::t) l)               /\
   (match (Repeat r::t) l    = 
      if match t l = SOME [] then SOME []  (* match r 0 times *)
      else        (* either NONE, or didn't munch all of l *)
         case match [r] l 
          of NONE -> NONE (* couldn't match an r *)
          || SOME l' ->   (* matched an r *)
               if LENGTH l' < LENGTH l   (* and consumed some of l *)
                  then match (Repeat r::t) l'
                  else NONE)`;

(*---------------------------------------------------------------------------*)
(* Packaged up.                                                              *)
(*---------------------------------------------------------------------------*)

val check_def = Define `check r s = (match [r] (EXPLODE s) = SOME [])`;

(*---------------------------------------------------------------------------
     Termination of match. We need a subsidiary measure function on 
     regexps which makes a 2-argument regexp bigger than a 
     list of 2 regexps. Adapted from a similar termination proof
     for Wang's algorithm in  tfl/examples/proplog.
 ---------------------------------------------------------------------------*)

val Meas_def = Define 
    `(Meas Any   = 0)
 /\  (Meas (Atom c)  = 0)
 /\  (Meas (x | y)  = Meas x + Meas y + 2)
 /\  (Meas (x # y)  = Meas x + Meas y + 2)
 /\  (Meas (Repeat r)  = SUC (Meas r))`;


val (match_def, match_ind) = Defn.tprove
(match_defn,
 WF_REL_TAC `measure (list_size Meas) LEX (measure LENGTH)`
 THEN RW_TAC list_ss [Meas_def, listTheory.list_size_def]);

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

fun CHECK r s = Count.apply EVAL 
                  (Term `check ^r ^(stringSyntax.fromMLstring s)`);

val One = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "1"))`)));
val Two = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "2"))`)));
val a = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "a"))`)));
val b = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "b"))`)));
val c = rhs(concl(EVAL(Term`Atom(HD(EXPLODE "c"))`)));

val r0 = Term `^One # ^Two`;
val r1 = Term `Repeat (^One # ^Two)`
val r2 = Term `Repeat Any # ^One`;
val r3 = Term `^r2 # ^r1`;

(* val true  = *) CHECK r0 "12";
(* val true  = *) CHECK r1 "12";
(* val true  = *) CHECK r1 "1212";
(* val true  = *) CHECK r1 "121212121212121212121212";
(* val false = *) CHECK r1 "12123";
(* val false = *) CHECK r2 "";
(* val true  = *) CHECK r2 "1";
(* val true  = *) CHECK r2 "0001";
(* val false = *) CHECK r2 "0002";
(* val true  = *) CHECK r3 "00011212";
(* val false = *) CHECK r3 "00011213";
(* val true  = *) CHECK (Term`Repeat(Repeat Any)`) "";
(* val true  = *) CHECK (Term`Repeat(Repeat Any)`) "0";
(* val true  = *) CHECK (Term`Repeat(Repeat Any)`) "0123";
(* val true  = *) CHECK (Term`Repeat (Any # Repeat Any)`) "0";
(* val true  = *) CHECK (Term`Repeat (Any # Repeat Any)`) "01";
(* val true  = *) CHECK (Term`Repeat (Any # Repeat Any)`) "012";
(* val true  = *) CHECK (Term`^a # Repeat(^a | ^b) # Repeat(^b # ^a)`) "abba";

(* At most 2 a's. Alphabet = {a,b} *)
val AtMostTwo_a = Term `Repeat ^b 
                     |  Repeat ^b # (^a | ^a # Repeat ^b # ^a) # Repeat ^b`;
CHECK AtMostTwo_a "";
CHECK AtMostTwo_a "b";
CHECK AtMostTwo_a "a";
CHECK AtMostTwo_a "aa";
CHECK AtMostTwo_a "ab";
CHECK AtMostTwo_a "ba";
CHECK AtMostTwo_a "bb";
CHECK AtMostTwo_a "abbbbabbbb";
CHECK AtMostTwo_a "bbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
(* false *) CHECK AtMostTwo_a "abbbbabbbab";

(* Exactly 2 a's. Alphabet = {a,b} *)
val ExactlyTwo_a = Term `Repeat ^b # ^a # Repeat ^b # ^a # Repeat ^b`;

(* false *) CHECK ExactlyTwo_a "";
(* false *) CHECK ExactlyTwo_a "b";
(* false *) CHECK ExactlyTwo_a "a";
(* true *)  CHECK ExactlyTwo_a "aa";
(* false *) CHECK ExactlyTwo_a "ab";
(* false *) CHECK ExactlyTwo_a "ba";
(* false *) CHECK ExactlyTwo_a "bb";
CHECK ExactlyTwo_a "abbbbabbbb";
CHECK ExactlyTwo_a "bbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbab";
(* false *) CHECK ExactlyTwo_a "abbbbabbbab";

(* All strings of length 0-3 *)
val UpTo3 = Term `Epsilon | Any | Any#Any | Any#Any#Any`;

CHECK UpTo3 "";
CHECK UpTo3 "b";
CHECK UpTo3 "a";
CHECK UpTo3 "aa";
(* false *) CHECK UpTo3 "abbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

(* All strings with no occurrences of aa or bb *)
val NoRepeats = Term `Any | Repeat (^a # ^b) | Repeat (^b # ^a)`;

CHECK NoRepeats "";
CHECK NoRepeats "a";
CHECK NoRepeats "b";
(* false *) CHECK NoRepeats "aa";
CHECK NoRepeats "ab";
CHECK NoRepeats "ba";
(* false *) CHECK NoRepeats "bb";
CHECK NoRepeats "ababababababababababababababababababababababababababab";
(* false *) 
CHECK NoRepeats "abababababababababababbababababababababababababababab";

(*---------------------------------------------------------------------------*)
(* Correctness with the standard semantics (from mjcg)                       *)
(*                                                                           *)
(* Sugar style semantics of regular expressions                              *)
(*                                                                           *)
(* sem r w means regular expression r matches word w (represented as a list) *)
(*---------------------------------------------------------------------------*)

val sem_def =
 Define
  `(sem Any w        = ?x. w = [x])                                    /\
   (sem Epsilon w    = (w = []))                                       /\
   (sem (Atom c) w   = (w = [c]))                                      /\
   (sem (r1|r2) w    = sem r1 w \/ sem r2 w)                           /\
   (sem (r1#r2) w    = ?w1 w2. (w = w1<>w2) /\ sem r1 w1 /\ sem r2 w2) /\
   (sem (Repeat r) w = ?wlist. (w = CONCAT wlist) /\ EVERY (sem r) wlist)`;

(*
val (sem_rules,sem_induct,sem_cases) = Hol_reln
   `semreln Epsilon []
 /\ (!x. semreln Any [x])
 /\ (!c. semreln (Atom c) [c])
 /\ (!r1 r2 w. semreln r1 w ==> semreln (r1|r2) w)
 /\ (!r1 r2 w. semreln r2 w ==> semreln (r1|r2) w)
 /\ (!r1 r2 w1 w2. semreln r1 w1 /\ 
                   semreln r2 w2 ==> semreln (r1#r2) (w1<>w2))
 /\ (!r wlist. EVERY (semreln r) wlist ==> semreln (Repeat r) (CONCAT wlist))`;
*)

(*
g `!r w. semreln r w ==> (match [r] w = SOME[])`;
expandf (HO_MATCH_MP_TAC sem_induct);
e (REPEAT CONJ_TAC);
(*1*)
e (RW_TAC std_ss [match_def]);
(*2*)
e (RW_TAC std_ss [match_def]);
(*3*)
e (RW_TAC std_ss [match_def]);
(*4*)
e (RW_TAC std_ss [match_def]);
(*5*)
e (RW_TAC std_ss [match_def]);
(*6*)
e (RW_TAC std_ss [match_def]);
*)

val EpsilonID = Q.prove
(`!r w. (sem (r # Epsilon) w = sem r w) /\ (sem (Epsilon # r) w = sem r w)`,
 Induct THEN EVAL_TAC THEN RW_TAC list_ss []);

val Then_ASSOC = Count.apply Q.prove
(`!r1 r2 r3 w. sem (r1 # (r2 # r3)) w = sem ((r1 # r2) # r3) w`,
  Cases THENL
  [EVAL_TAC THEN REPEAT GEN_TAC THEN EQ_TAC 
    THEN RW_TAC list_ss [] THEN EVAL_TAC THENL
    [Q.EXISTS_TAC `x::w1'` THEN Q.EXISTS_TAC `w2'` THEN RW_TAC list_ss [] THEN
     Q.EXISTS_TAC `[x]` THEN Q.EXISTS_TAC `w1'` THEN RW_TAC list_ss [],
     Q.EXISTS_TAC `[x]` THEN Q.EXISTS_TAC `w2'<>w2` 
       THEN RW_TAC list_ss [] THEN METIS_TAC []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC `c::w1` THEN Q.EXISTS_TAC `w2'` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC `w2'<>w2` THEN RW_TAC list_ss [] THEN METIS_TAC []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC`w1<>w1'` THEN Q.EXISTS_TAC`w2'` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC`w1` THEN Q.EXISTS_TAC`w1'` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC`w1<>w1'` THEN Q.EXISTS_TAC`w2'` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC`w1` THEN Q.EXISTS_TAC `w1'` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC`w1'` THEN Q.EXISTS_TAC`w2'<>w2` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC `w2'` THEN Q.EXISTS_TAC `w2` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC`w1'` THEN Q.EXISTS_TAC`w2'<>w2` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC`w2'` THEN Q.EXISTS_TAC`w2` THEN RW_TAC list_ss []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC `(w1'<>w2')<>w1''` THEN Q.EXISTS_TAC `w2''` 
        THEN RW_TAC list_ss [] 
        THEN Q.EXISTS_TAC `w1'<>w2'` THEN Q.EXISTS_TAC `w1''`
        THEN RW_TAC list_ss [] THEN METIS_TAC[],
      Q.EXISTS_TAC `(w1''<>w2'')` THEN Q.EXISTS_TAC `w2'<>w2` 
        THEN RW_TAC list_ss [] THEN METIS_TAC []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC `(CONCAT wlist <> w1')` THEN Q.EXISTS_TAC `w2'`
        THEN RW_TAC list_ss [] THEN 
      Q.EXISTS_TAC `CONCAT wlist` THEN Q.EXISTS_TAC `w1'` THEN METIS_TAC[],
      Q.EXISTS_TAC `CONCAT wlist` THEN Q.EXISTS_TAC `w2'<>w2`
        THEN RW_TAC list_ss [] THEN METIS_TAC[]]]);

val Or_lemma = Q.prove
(`!r1 r2 r3. sem ((r1 | r2) # r3) w = sem (r1 # r3) w \/ sem (r2 # r3) w`,
 RW_TAC list_ss [sem_def] THEN PROVE_TAC []);


val TAKE_def = Define
  `(TAKE 0 l = SOME(l:'a list,[]:'a list)) /\
   (TAKE (SUC n) (h::t) = OPTION_MAP (CONS h##I) (TAKE n t)) /\
   (TAKE (SUC n) [] = NONE)`;

val TAKE_ind = fetch "-" "TAKE_ind";

val TAKE_APPEND_THM = Q.prove
(`!n l l1 l2. (SOME(l1,l2) = TAKE n l) ==> (l = l1<>l2)`,
 recInduct TAKE_ind THEN REPEAT CONJ_TAC 
   THEN RW_TAC list_ss [TAKE_def] 
   THEN Cases_on `TAKE n t`
   THEN FULL_SIMP_TAC list_ss []
   THEN Cases_on `x` THEN FULL_SIMP_TAC list_ss [combinTheory.I_THM]);


val lem1 = Q.prove
(`!rlist w1 w2. (match rlist w1 = SOME w2) ==> LENGTH w2 <= LENGTH w1`,
 recInduct match_ind THEN REPEAT CONJ_TAC THENL
 [EVAL_TAC THEN RW_TAC list_ss [],
  EVAL_TAC THEN RW_TAC list_ss [],
  EVAL_TAC THEN RW_TAC list_ss [] THEN RES_TAC THEN DECIDE_TAC,
  EVAL_TAC THEN RW_TAC list_ss [],
  EVAL_TAC THEN RW_TAC list_ss [],
  RW_TAC list_ss [match_def] THEN  RES_TAC THEN DECIDE_TAC,
  EVAL_TAC THEN RW_TAC list_ss [],
  EVAL_TAC THEN RW_TAC list_ss [],
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [match_def] 
    THEN GEN_TAC THEN CASE_TAC THEN RW_TAC list_ss [] 
    THEN RES_TAC THEN DECIDE_TAC]);


g`!rlist w w1 w2. (match rlist w = SOME w2) 
                  ==> 
               ?w1. (w=w1<>w2) /\ (match rlist w1 = SOME [])`;
e (recInduct match_ind THEN REPEAT CONJ_TAC);
(*1*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*2*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*3*)
e (EVAL_TAC THEN RW_TAC list_ss []);
e (RES_TAC THEN RW_TAC list_ss []);
e (Q.EXISTS_TAC `v0::w1` THEN EVAL_TAC THEN ASM_REWRITE_TAC []);
(*4*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*5*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*6*)
e (RW_TAC list_ss [match_def]);
e (RES_TAC THEN RW_TAC list_ss []);
e (Q.EXISTS_TAC `c::w1` THEN EVAL_TAC THEN ASM_REWRITE_TAC []);
(*7*)
e (EVAL_TAC THEN RW_TAC list_ss []);
e (RES_TAC THEN RW_TAC list_ss []);
(*8*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*9*)
e (REPEAT STRIP_TAC);
e (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [match_def]));
e (RW_TAC list_ss []);
(*9.1*)
e (Q.EXISTS_TAC `l` THEN RW_TAC list_ss []);
e (ONCE_REWRITE_TAC [match_def]);
e (RW_TAC list_ss []);
(*9.2*)
e (POP_ASSUM MP_TAC THEN CASE_TAC);
e (RW_TAC list_ss []);
e (RES_TAC);
e (Q.EXISTS_TAC `w1<>w1'` THEN RW_TAC list_ss []);
(*9.2.1*)
e (METIS_TAC [listTheory.APPEND_11]);
(*9.2.2*)
e (FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss []);
e (POP_ASSUM (K ALL_TAC));
?????

val APPEND_ID_THM = Q.prove
(`!l1 l2. ((l1<>l2 = l1) = (l2=[])) /\
          ((l1<>l2 = l2) = (l1=[]))`,
Induct THEN EVAL_TAC THEN ASM_REWRITE_TAC []
  THEN GEN_TAC THEN Cases THEN RW_TAC list_ss [] THEN DISJ2_TAC 
  THEN SPOSE_NOT_THEN (MP_TAC o Q.AP_TERM `LENGTH`)
  THEN RW_TAC list_ss []);

g`!l w r1 r2. (l = [r1]) ==> 
         (match l w = NONE) ==> (sem (Repeat r1 # r2) w = sem r2 w)`;
e (recInduct match_ind THEN SIMP_TAC list_ss [] THEN REPEAT CONJ_TAC);
e (EVAL_TAC THEN RW_TAC list_ss []);
e (EVAL_TAC THEN RW_TAC list_ss []);
e (EVAL_TAC THEN RW_TAC list_ss [] THEN EQ_TAC THEN RW_TAC list_ss []
   THEN Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [CONCAT_def]);
e (EVAL_TAC THEN RW_TAC list_ss [] THEN EQ_TAC THEN RW_TAC list_ss []
   THEN Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [CONCAT_def]);
e (RW_TAC list_ss [match_def,sem_def] THEN EQ_TAC THEN RW_TAC list_ss []);
(*1*)
e (Cases_on `wlist`);
(*1.1*)
e (FULL_SIMP_TAC list_ss [CONCAT_def]);
(*1.2*)
e (FULL_SIMP_TAC list_ss [CONCAT_def,sem_def]);
*(2*)
e (Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `h::u` THEN RW_TAC list_ss []);
e (Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [CONCAT_def]);
e (RW_TAC list_ss [match_def,sem_def] THEN EQ_TAC THEN RW_TAC list_ss []);
e (`?u1 u2. (CONCAT wlist <> w2 = u1 <> u2) /\
                (?wlist. (u1 = CONCAT wlist) /\ EVERY (sem r2) wlist) /\
                sem r2' u2 =
             sem r2' (CONCAT wlist <> w2)` by METIS_TAC []);
e (POP_ASSUM (SUBST_ALL_TAC o SYM));

(* GOOD TRY ... founders on Or patterns (which are goofy) *)

g`!rlist w. (match rlist w = NONE) 
            ==> !w1 w2. (w = w1<>w2) 
                        ==> ~sem (FOLDR Then Epsilon rlist) w1`;
e (recInduct match_ind THEN REPEAT CONJ_TAC);
(*1*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*2*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*3*)
e (EVAL_TAC THEN RW_TAC list_ss []);
e (RW_TAC list_ss [GSYM IMP_DISJ_THM]);
e (RES_TAC);
e (Cases_on `w1'` THEN RW_TAC list_ss []);
e (RW_TAC list_ss [GSYM IMP_DISJ_THM]);
e (FULL_SIMP_TAC list_ss []);
(*4*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*5*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*6*)
e (RW_TAC list_ss [match_def,sem_def,GSYM IMP_DISJ_THM]
   THEN FULL_SIMP_TAC list_ss []);
(*7*)
e (RW_TAC list_ss [Or_lemma,match_def]); 
e (EVAL_TAC THEN RW_TAC list_ss []);
e (RW_TAC list_ss [GSYM IMP_DISJ_THM]);
e RES_TAC;
e (POP_ASSUM (MP_TAC o Q.SPECL [`w2`,`w1'<>w2'`]));
e (REWRITE_TAC [GSYM IMP_DISJ_THM]);

val REGL_def = Define `regl rlist = FOLDR Then Epsilon rlist`;

val EpsilonREGL = Q.prove
(`!t. sem (regl (Epsilon::t)) = sem (regl t)`,
 GEN_TAC THEN CONV_TAC FUN_EQ_CONV 
 THEN RW_TAC list_ss [REGL_def,EpsilonID]);

val MATCH_OR_NONE = Q.prove
(`!p q rst l. 
   (match (p|q :: rst) l = NONE) ==> (match (p::rst) l = NONE) /\
                                     (match (q::rst) l = NONE)`,
 EVAL_TAC THEN RW_TAC list_ss []);

g`!rlist w r. ~(w=[]) /\ (match rlist w = NONE) 
               ==> 
              ~sem (Repeat (regl rlist)) w`;
e (recInduct match_ind THEN REPEAT CONJ_TAC);
(*1*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*2*)
e (RW_TAC list_ss [match_def, sem_def, GSYM IMP_DISJ_THM,EpsilonREGL]);
(*3*)
e (EVAL_TAC THEN RW_TAC list_ss [GSYM IMP_DISJ_THM]);
e (RES_THEN (MP_TAC o Q.SPEC `[TL (CONCAT wlist)]`));
e (EVAL_TAC);
e (RW_TAC list_ss []);
e (Cases_on `wlist` THEN 
   FULL_SIMP_TAC list_ss [listTheory.EXISTS_DEF,CONCAT_def]
   THEN RW_TAC list_ss []);
e (RW_TAC list_ss [match_def, sem_def, GSYM IMP_DISJ_THM,REGL_def]);
e (Cases_on `wlist` THEN 
   FULL_SIMP_TAC list_ss [listTheory.EXISTS_DEF,CONCAT_def]
   THEN RW_TAC list_ss []);
e DISJ2_TAC;
(*4*)
e (RW_TAC list_ss [match_def, sem_def, GSYM IMP_DISJ_THM]);
e (RULE_ASSUM_TAC SYM);
e (FULL_SIMP_TAC list_ss [CONCAT_NIL]);
e (Cases_on `wlist` THEN RW_TAC list_ss [listTheory.EXISTS_DEF]);
e (FULL_SIMP_TAC list_ss []);
FOO;

g`!rlist w. sem (FOLDR Then Epsilon rlist) w = (match rlist w = SOME [])`;
e (recInduct match_ind THEN REPEAT CONJ_TAC);
(*1*)
e (EVAL_TAC THEN RW_TAC std_ss []);
(*2*)
e (EVAL_TAC THEN RW_TAC std_ss [] THEN EQ_TAC THEN RW_TAC list_ss []);
(*3*)
e (EVAL_TAC THEN RW_TAC list_ss [] THEN EQ_TAC);
(*3.1*)
e (RW_TAC list_ss [] THEN FULL_SIMP_TAC list_ss []);
(*3.2*)
e (RW_TAC std_ss []);
e (Q.EXISTS_TAC `[v0]`);
e (Q.EXISTS_TAC `u`);
e (RW_TAC list_ss []);
(*4*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*5*)
e (EVAL_TAC THEN RW_TAC list_ss []);
(*6*)
e (RW_TAC list_ss [match_def,sem_def]);
(*7*)
e (RW_TAC list_ss [match_def,sem_def]);
(*7.1*)
e (Q.EXISTS_TAC `w1`);
e (Q.EXISTS_TAC `w2`);
e (RW_TAC list_ss []);
(*7.2*)
e (RW_TAC list_ss [] THEN METIS_TAC[]);
(*8*)
e (RW_TAC std_ss [match_def,sem_def]);
e (POP_ASSUM (SUBST_ALL_TAC o GSYM));
e (RW_TAC list_ss [Then_ASSOC]);
(*9*)
e (RW_TAC list_ss [] THEN ONCE_REWRITE_TAC [match_def] 
    THEN RW_TAC std_ss [] THENL [ALL_TAC, CASE_TAC THEN RW_TAC list_ss []]);
(*9.1*)
e (RW_TAC list_ss [sem_def]);
e (Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `l`);
e (EVAL_TAC);
e (CONJ_TAC THENL [Q.EXISTS_TAC `[]`, ALL_TAC] 
   THEN RW_TAC list_ss [CONCAT_def]);
(*9.2*)
e (`~sem r l` by METIS_TAC [EpsilonID]);
e (`~sem (FOLDR $# Epsilon t) l` by METIS_TAC []);
e (EVAL_TAC);
e (RW_TAC list_ss []);
e (Cases_on `w1`);
(*9.2.1*)
e (RW_TAC list_ss [GSYM IMP_DISJ_THM]);
e (PROVE_TAC []);
(*9.2.2*)
e (RW_TAC list_ss [GSYM IMP_DISJ_THM]);
e (FULL_SIMP_TAC list_ss []);
e (RW_TAC list_ss []);
!!!
(*9.3*)
(*9.4*)


(* Another try ... incorrect, because you may match w1, by rlist
   and then also match w1@w2, again by rlist.
*)
g`!rlist w w1 w2. 
    (w=w1<>w2) ==> (sem (FOLDR Then Epsilon rlist) w1 
                 = (match rlist w = SOME w2))`;
e (recInduct match_ind THEN REPEAT CONJ_TAC);
(*1*)
e (EVAL_TAC THEN RW_TAC list_ss [] THEN METIS_TAC [APPEND_ID_THM]);
(*2*)
e (EVAL_TAC THEN RW_TAC std_ss [] THEN EQ_TAC 
    THEN RW_TAC list_ss [] THEN METIS_TAC []);
(*3*)
e (EVAL_TAC THEN RW_TAC list_ss [] THEN EQ_TAC);
(*3.1*)
e (RW_TAC list_ss []);
e (FULL_SIMP_TAC list_ss []);
e (RW_TAC list_ss []);
e (METIS_TAC []);
(*3.2*)
e (RW_TAC std_ss []);
e (Cases_on `w1` THEN FULL_SIMP_TAC list_ss []
   THENL [Cases_on `w2`, ALL_TAC] THEN RW_TAC list_ss []);
(*3.2.1*)
e (IMP_RES_TAC lem1); 
e (FULL_SIMP_TAC list_ss []);
(*3.2.2*)
e (Q.EXISTS_TAC `[h]` THEN RW_TAC list_ss [] THEN PROVE_TAC []);
(*4*)
e EVAL_TAC;
e (RW_TAC list_ss []);
(*5*)
e EVAL_TAC;
e (RW_TAC list_ss []);
(*6*)
e (RW_TAC list_ss [match_def,sem_def,GSYM IMP_DISJ_THM] 
   THEN FULL_SIMP_TAC list_ss []);
e (Cases_on `w1` THEN FULL_SIMP_TAC list_ss []);
e (Cases_on `w2` THEN FULL_SIMP_TAC list_ss []);
e (RW_TAC list_ss []);
e (STRIP_TAC THEN IMP_RES_TAC lem1 THEN FULL_SIMP_TAC list_ss []);
(*7*)
e (RW_TAC list_ss [Or_lemma]);
e (RW_TAC list_ss [match_def]);
(*7.1*)
e (Q.PAT_ASSUM `~x ==> y` (K ALL_TAC));
e (`sem (r1 # FOLDR $# Epsilon t) (w1<>w2)` 
     by PROVE_TAC [listTheory.APPEND_NIL]);
e (EQ_TAC THEN RW_TAC list_ss []);
(*7.1.1*)
e (Q.PAT_ASSUM `$! M` (MP_TAC o Q.SPECL [`w1`, `w2`]));
e (RW_TAC list_ss []);
(*7.1.2*)
>>>>
e (Q.PAT_ASSUM `$! M` (fn th => MP_TAC (Q.SPECL [`w1<>w2`, `[]`] th) 
                        THEN RW_TAC list_ss [] THEN ASSUME_TAC th));
e (POP_ASSUM (MP_TAC o REWRITE_RULE [listTheory.APPEND_NIL]
                     o Q.SPECL [`w1<>w2`, `[]`]));
e (FULL_SIMP_TAC list_ss [sem_def] THEN RW_TAC list_ss []);
e (DISCH_THEN (MP_TAC o Q.SPECL [`w1`, `w2''`]));
e (RW_TAC list_ss []);
e (FULL_SIMP_TAC list_ss []);
e (Q.PAT_ASSUM `match x y = SOME []` MP_TAC);
e (POP_ASSUM (ASSUME_TAC o SYM));
e (`?w1' w2. (w1 = w1' <> w2) /\ sem r1 w1' /\ sem (FOLDR $# Epsilon t) w2`
    by ALL_TAC);
e (Q.EXISTS_TAC `w1'` THEN Q.EXISTS_TAC `w2'` THEN RW_TAC list_ss []);

e (Q.PAT_ASSUM `$! M` (fn th => MP_TAC (Q.SPECL [`w1'<>w2'<>w2`, `[]`] th) 
                        THEN RW_TAC list_ss [] THEN ASSUME_TAC th));
e (POP_ASSUM (SUBST_ALL_TAC o SYM));
(*7.1.3*)
e (FULL_SIMP_TAC list_ss []);

(*7.2*)
e (EQ_TAC THEN RW_TAC list_ss []);
>>>
(*8*)
e (RW_TAC list_ss [match_def,sem_def]);
e (POP_ASSUM (SUBST_ALL_TAC o GSYM));
e (RW_TAC list_ss []);
e (METIS_TAC [Then_ASSOC]);
(*9*)
e (RW_TAC list_ss []);
e (ONCE_REWRITE_TAC [match_def]);
e (RW_TAC list_ss [sem_def]);
(*9.1*)
e (Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `l`);
e (EVAL_TAC);
e (CONJ_TAC THENL [Q.EXISTS_TAC `[]`, ALL_TAC] 
   THEN RW_TAC list_ss [CONCAT_def]);
(*9.2*)
e (CASE_TAC THEN RW_TAC list_ss []);
??? from here down
(*9.2.1*)
e (RW_TAC std_ss [GSYM IMP_DISJ_THM]);
e (`~sem r (w1<>w2)` by METIS_TAC [EpsilonID]);
e (`~sem (FOLDR $# Epsilon t) (w1 <> w2)` by METIS_TAC []);
(*9.2.2*)
e (`sem r l = (x=[])` by METIS_TAC [EpsilonID]);
e (`~sem (FOLDR $# Epsilon t) l` by METIS_TAC []);
e (`(match (Repeat r::t) x = SOME []) = sem (Repeat r # FOLDR $# Epsilon t) x`
  by METIS_TAC []);
e (POP_ASSUM SUBST_ALL_TAC);
e (REWRITE_TAC [sem_def]);
e (EQ_TAC THEN RW_TAC list_ss []);
(*9.2.3*)

val sem_match =
 store_thm
  ("sem_match",
   ``!r w. sem r w = (match [r] w = SOME[])``,
   Induct
    THENL
     [(* Any      *)
      Cases_on `w` THEN RW_TAC list_ss [sem_def,match_def],
      (* Epsilon  *)
      Cases_on `w` THEN RW_TAC list_ss [sem_def,match_def],
      (* Atom c   *))
      Cases_on `w` THEN RW_TAC list_ss [sem_def,match_def],
      (* r | r'   *)
      Cases_on `w` THEN RW_TAC list_ss [sem_def,match_def],
      (* r # r'   *)
!!    Needs a lemma
      (* Repeat r *)
!!    Needs a lemma       ])`;
