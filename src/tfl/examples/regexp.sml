(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(*---------------------------------------------------------------------------*)

app load ["stringLib", "metisLib"]; 
open metisLib pairTheory combinTheory listTheory;

(*---------------------------------------------------------------------------*)
(* Make list append into an infix recognized by the parser                   *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);

(*---------------------------------------------------------------------------*)
(* Misc. theorems                                                            *)
(*---------------------------------------------------------------------------*)

val IN_THM = Q.prove
(`!x. P x = x IN P`,
 RW_TAC bool_ss [boolTheory.IN_DEF]);
 
val APPEND_ID_THM = Q.prove
(`!l1 l2. ((l1<>l2 = l1) = (l2=[])) /\
          ((l1<>l2 = l2) = (l1=[]))`,
Induct THEN EVAL_TAC THEN ASM_REWRITE_TAC []
  THEN GEN_TAC THEN Cases THEN RW_TAC list_ss [] THEN DISJ2_TAC 
  THEN SPOSE_NOT_THEN (MP_TAC o Q.AP_TERM `LENGTH`)
  THEN RW_TAC list_ss []);

val APPEND_CONS = Q.prove
(`!h t. [h]<>t = h::t`,
 RW_TAC list_ss []);

val NULL_EQ_NIL = Q.prove
(`!l. NULL l = (l = [])`,
 Cases THEN RW_TAC list_ss []);

val LENGTH_EQ_ONE = Q.prove
(`!l. (LENGTH l = 1) = ?x. l = [x]`,
 Cases THEN RW_TAC list_ss [] THEN
 Cases_on `t` THEN RW_TAC list_ss []);

val MEM_TL = Q.prove
(`!x l. ~NULL l ==> MEM x (TL l) ==> MEM x l`,
 Induct_on `l` THEN RW_TAC list_ss []);

val FIRST_EXISTS_THM = Q.prove
(`!P L. EXISTS P L ==>
      ?prefix w suffix. 
        (L = prefix <> [w] <> suffix) /\ EVERY ($~ o P) prefix /\ P w`,
 GEN_TAC THEN Induct THEN RW_TAC list_ss []
  THEN FULL_SIMP_TAC list_ss [EXISTS_DEF] THEN RW_TAC list_ss []
  THENL [MAP_EVERY Q.EXISTS_TAC [`[]`, `h`, `L`] THEN RW_TAC list_ss [],
         RES_TAC THEN Cases_on `P h` THENL
         [MAP_EVERY Q.EXISTS_TAC [`[]`, `h`, `L`] THEN RW_TAC list_ss [],
          MAP_EVERY Q.EXISTS_TAC [`h::prefix`, `w`, `suffix`] THEN 
          RW_TAC list_ss [combinTheory.o_DEF]]]);

val EXISTS_ELIM_THM = Q.prove
(`!P l. EXISTS P l = ?x. MEM x l /\ x IN P`,
 GEN_TAC THEN Induct 
         THEN RW_TAC list_ss [EXISTS_DEF]
         THEN PROVE_TAC [IN_THM]);

val EVERY_ELIM_THM = Q.prove
(`!P l. EVERY P l = !x. MEM x l ==> x IN P`,
 GEN_TAC THEN Induct 
         THEN RW_TAC list_ss [EVERY_DEF]
         THEN PROVE_TAC [IN_THM]);

(*---------------------------------------------------------------------------*)
(* Concatenate a list of lists                                               *)
(*---------------------------------------------------------------------------*)

val CONCAT_def = Define 
  `(CONCAT []     = []) /\ 
   (CONCAT(l::ll) = l <> CONCAT ll)`;

val CONCAT_EQ_NIL = Q.prove
(`!wlist. (CONCAT wlist = []) = EVERY NULL wlist`,
 Induct THEN RW_TAC list_ss [CONCAT_def,NULL_EQ_NIL]);

val NULL_CONCAT_THM = Q.prove
(`!L. NULL (CONCAT L) = EVERY NULL L`,
 PROVE_TAC [CONCAT_EQ_NIL, NULL_EQ_NIL]);

val CONCAT_APPEND_DISTRIB = Q.prove
(`!l1 l2. CONCAT (l1 <> l2) = CONCAT l1 <> CONCAT l2`,
 Induct THEN RW_TAC list_ss [CONCAT_def]);


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
(* Sugar style semantics of regular expressions (from mjcg)                  *)
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


(*---------------------------------------------------------------------------*)
(* All ways to split a list in 2 pieces                                      *)
(*---------------------------------------------------------------------------*)

val ALL_SPLITS_def = Define
  `(ALL_SPLITS (l,[])   = [(l,[])]) /\
   (ALL_SPLITS (l,h::t) = (l,h::t)::ALL_SPLITS(l<>[h],t))`;

val SPLITS_def = Define `SPLITS l = ALL_SPLITS ([],l)`;

(*---------------------------------------------------------------------------*)
(* Testing 

    EVAL (Term`SPLITS [1;2;3;4]`);
    EVAL (Term`SPLITS [1;2;3;4;5;6;7;8;9]`);
    EVAL (Term`LENGTH (SPLITS [1;2;3;4;5;6;7;8;9;
                               1;2;3;4;5;6;7;8;9;
                               1;2;3;4;5;6;7;8;9])`);
*)
(*---------------------------------------------------------------------------*)

val ALL_SPLITS_LEMMA = Q.prove
(`!l1 l2 l3 l4. MEM (l3,l4) (ALL_SPLITS (l1,l2)) ==> (l1<>l2 = l3<>l4)`,
 Induct_on `l2` THEN RW_TAC list_ss [ALL_SPLITS_def] THEN 
 METIS_TAC [APPEND,APPEND_ASSOC]);

val SPLITS_APPEND = Q.prove
(`!l l1 l2. MEM (l1,l2) (SPLITS l) ==> (l1<>l2 = l)`,
 RW_TAC list_ss [SPLITS_def] THEN 
 METIS_TAC [ALL_SPLITS_LEMMA,APPEND]);

val MEM_ALL_SPLITS_ID = Q.prove
(`!x. MEM x (ALL_SPLITS x)`,
 Cases THEN Cases_on `r` THEN RW_TAC list_ss [ALL_SPLITS_def]);

val MEM_ALL_SPLITS_LEM = Q.prove
(`!l1 l2 w1 w2. (l2 = w1<>w2) ==> MEM (l1<>w1,w2) (ALL_SPLITS (l1, l2))`,
 recInduct (fetch "-" "ALL_SPLITS_ind")
   THEN RW_TAC list_ss [ALL_SPLITS_def,APPEND_ID_THM]
   THEN Cases_on `w1` THEN FULL_SIMP_TAC list_ss []
   THEN PROVE_TAC [APPEND_ASSOC,APPEND_CONS]);

val MEM_ALL_SPLITS = Q.prove
(`!w1 w2.  MEM (w1,w2) (ALL_SPLITS ([],w1<>w2))`,
 PROVE_TAC [MEM_ALL_SPLITS_LEM, CONJUNCT1 APPEND]);

val MEM_SPLITS = Q.prove
(`!w1 w2.  MEM (w1,w2) (SPLITS (w1<>w2))`,
 PROVE_TAC [MEM_ALL_SPLITS, SPLITS_def]);

val MEM_TL_SPLITS = Q.prove
(`!w1 w2. ~NULL w1 ==> MEM(w1,w2) (TL (SPLITS (w1<>w2)))`,
 RW_TAC list_ss [SPLITS_def, ALL_SPLITS_def]
   THEN Cases_on `w1` THEN FULL_SIMP_TAC list_ss [ALL_SPLITS_def]
   THEN ONCE_REWRITE_TAC [GSYM APPEND_CONS]
   THEN PURE_REWRITE_TAC [APPEND_NIL]
   THEN RW_TAC list_ss [SIMP_RULE bool_ss [] MEM_ALL_SPLITS_LEM]);

val SPLITS_LENGTH = Q.prove
(`!l l1 l2. MEM (l1,l2) (SPLITS l) ==> (LENGTH l1 + LENGTH l2 = LENGTH l)`,
 METIS_TAC [SPLITS_APPEND,LENGTH_APPEND]);

val SPLITS_NON_EMPTY = Q.prove
(`!l. ~NULL (SPLITS l)`,
 RW_TAC list_ss [SPLITS_def] THEN 
 Induct_on `l` THEN RW_TAC list_ss [ALL_SPLITS_def]);

val lem = Q.prove
(`!l1 l2 l3 s1 s2. 
         MEM (s1,s2) (ALL_SPLITS (l1,l2))
          ==> 
         ?s3. MEM (s3,s2) (ALL_SPLITS (l3,l2))`,
Induct_on `l2` THEN RW_TAC list_ss [ALL_SPLITS_def] THEN PROVE_TAC []);

val MEM_ALL_SPLITS_LENGTH = Q.prove 
(`!l s1 s2. ~NULL l ==> MEM (s1,s2) (TL (SPLITS l)) ==> LENGTH s2 < LENGTH l`,
 REWRITE_TAC [SPLITS_def] THEN 
 Induct THEN RW_TAC list_ss [ALL_SPLITS_def]
 THEN Cases_on `l`
 THEN FULL_SIMP_TAC list_ss [ALL_SPLITS_def]
 THEN METIS_TAC [lem, DECIDE (Term `x < y ==> x < SUC y`)]);



(*---------------------------------------------------------------------------*)
(* Checker - from a tech. report of Simon Thompson                           *)
(*---------------------------------------------------------------------------*)

val match_defn = Hol_defn 
   "match"
  `(match Epsilon l  = NULL l)
/\ (match Any l      = (LENGTH l = 1))
/\ (match (Atom c) l = (l = [c]))
/\ (match (r1|r2) l  = match r1 l \/ match r2 l) 
/\ (match (r1#r2) l  = EXISTS (\(s1,s2). match r1 s1 /\ match r2 s2) (SPLITS l))
/\ (match (Repeat r) l = 
      if NULL l then T 
      else EXISTS (\(s1,s2). match r s1 /\ match (Repeat r) s2) 
                  (TL(SPLITS l)))`;

val (match_def, match_ind) = Defn.tprove
(match_defn,
 WF_REL_TAC `measure regexp_size LEX (measure LENGTH)`
 THEN RW_TAC list_ss [fetch "-" "regexp_size_def"]
 THEN PROVE_TAC [MEM_ALL_SPLITS_LENGTH]);

(*---------------------------------------------------------------------------*)
(* Correctness of the matcher                                                *)
(*---------------------------------------------------------------------------*)

val sem_match = Q.store_thm ("sem_match",
 `!r w. sem r w = match r w`,
 recInduct match_ind THEN REPEAT CONJ_TAC THENL
 [(* Any     *) RW_TAC list_ss [sem_def,match_def,NULL_EQ_NIL],
  (* Epsilon *) RW_TAC list_ss [sem_def,match_def,LENGTH_EQ_ONE],
  (* Atom c  *) RW_TAC list_ss [sem_def,match_def],
  (* r | r'  *) RW_TAC list_ss [sem_def,match_def],
  (* r # r'  *) RW_TAC list_ss [sem_def,match_def,EXISTS_ELIM_THM,GSYM IN_THM] 
    THEN EQ_TAC THEN RW_TAC list_ss [] THENL 
    [Q.EXISTS_TAC `(w1,w2)` 
      THEN SIMP_TAC list_ss [MEM_SPLITS] THEN PROVE_TAC [MEM_SPLITS],
     Cases_on`x` THEN FULL_SIMP_TAC list_ss [] THEN PROVE_TAC[SPLITS_APPEND]],
  (* Repeat r *)
   RW_TAC list_ss [sem_def]
    THEN ONCE_REWRITE_TAC [match_def] 
    THEN RW_TAC list_ss [EXISTS_ELIM_THM]
    THEN Cases_on `NULL l` THENL 
    [RW_TAC list_ss [] THEN Q.EXISTS_TAC `[]` THEN 
     RW_TAC list_ss [CONCAT_def] THEN PROVE_TAC [NULL_EQ_NIL],
     FULL_SIMP_TAC list_ss [GSYM IN_THM] THEN EQ_TAC THEN 
     RW_TAC list_ss [EXISTS_PROD] THENL
     [`EXISTS ($~ o NULL) wlist` by PROVE_TAC [NULL_CONCAT_THM,NOT_EVERY] THEN
      IMP_RES_TAC FIRST_EXISTS_THM THEN 
      RULE_ASSUM_TAC (SIMP_RULE list_ss [o_DEF]) THEN 
      `sem r w /\ EVERY (sem r) suffix` by FULL_SIMP_TAC list_ss [EVERY_APPEND]
        THEN 
      `CONCAT wlist = CONCAT (w::suffix)` 
             by (RW_TAC list_ss [CONCAT_APPEND_DISTRIB,CONCAT_def] THEN 
                 RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV ETA_CONV)) THEN
                 METIS_TAC[NULL_CONCAT_THM,APPEND,NULL_EQ_NIL]) THEN
      `MEM (w,CONCAT suffix) (TL(SPLITS(CONCAT wlist)))`
                 by RW_TAC list_ss [CONCAT_def, MEM_TL_SPLITS] THEN 
      PROVE_TAC []
      ,
      `?wlist. (p_2=CONCAT wlist) /\ EVERY (sem r) wlist` by PROVE_TAC[] THEN 
      Q.EXISTS_TAC `p_1::wlist` THEN RW_TAC list_ss [CONCAT_def] THEN 
      PROVE_TAC [MEM_TL,SPLITS_NON_EMPTY,SPLITS_APPEND]]]]);

(*---------------------------------------------------------------------------*)
(* Misc. semantics lemmas                                                    *)
(*---------------------------------------------------------------------------*)

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



(*---------------------------------------------------------------------------*)
(* Examples of the matcher: it's slow!                                       *)
(*---------------------------------------------------------------------------*)
(*
fun CHECK r s = Count.apply EVAL 
                  (Term `match ^r (EXPLODE ^(stringSyntax.fromMLstring s))`);

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
(* true *)  CHECK ExactlyTwo_a "abbbbabbbb";
(* true *)  CHECK ExactlyTwo_a 
               "bbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbab";
(* false *) CHECK ExactlyTwo_a "abbbbabbbab";

(* All strings of length 0-3 *)
val UpTo3 = Term `Epsilon | Any | Any#Any | Any#Any#Any`;

(* true *) CHECK UpTo3 "";
(* true *) CHECK UpTo3 "b";
(* true *) CHECK UpTo3 "a";
(* true *) CHECK UpTo3 "aa";
(* false *) CHECK UpTo3 "abbbbabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

(* All strings with no occurrences of aa or bb *)
val NoRepeats = Term `Any | Repeat (^a # ^b) | Repeat (^b # ^a)`;

(* true *)  CHECK NoRepeats "";
(* true *)  CHECK NoRepeats "a";
(* true *)  CHECK NoRepeats "b";
(* false *) CHECK NoRepeats "aa";
(* true *)  CHECK NoRepeats "ab";
(* true *)  CHECK NoRepeats "ba";
(* false *) CHECK NoRepeats "bb";
(* true *)  CHECK NoRepeats 
              "ababababababababababababababababababababababababababab";
(* false *) CHECK NoRepeats 
              "abababababababababababbababababababababababababababab";

*)
(*---------------------------------------------------------------------------*)
