
open HolKernel boolLib bossLib Parse pred_setTheory pairTheory wordsTheory;
val _ = new_theory "set_sep";


infix \\
val op \\ = op THEN;


(* ---- definitions ---- *)

val one_def    = Define `one x = \s. (s = {x})`;
val emp_def    = Define `emp = \s. (s = {})`;
val cond_def   = Define `cond c = \s. (s = {}) /\ c`;
val SEP_F_def  = Define `SEP_F s = F`;
val SEP_T_def  = Define `SEP_T s = T`;
val SPLIT_def  = Define `SPLIT (s:'a set) (u,v) = (u UNION v = s) /\ DISJOINT u v`;
val STAR_def   = Define `STAR p q = (\s. ?u v. SPLIT s (u,v) /\ p u /\ q v)`;
val SEP_EQ_def = Define `SEP_EQ x = \s. s = x`;

val SEP_EXISTS = new_binder_definition("SEP_EXISTS",
  ``($SEP_EXISTS) = \f s:'a set. $? (\y. f y s)``);

val SEP_HIDE_def = Define `SEP_HIDE p = SEP_EXISTS x. p x`;
val SEP_DISJ_def = Define `SEP_DISJ p q = (\s. p s \/ q s)`;

val _ = overload_on ("*",Term`STAR`);
val _ = overload_on ("~",Term`SEP_HIDE`);
val _ = overload_on ("\\/",Term`SEP_DISJ`);

val sidecond_def = Define `sidecond = cond`;
val precond_def  = Define `precond = cond`;

val SEP_IMP_def  = Define `SEP_IMP p q = !s. p s ==> q s`;

val fun2set_def = Define `fun2set (f:'b->'a,d) =  { (a,f a) | a IN d }`;

val SEP_ARRAY_def = Define `
  (SEP_ARRAY p i a [] = emp) /\
  (SEP_ARRAY p i a (x::xs) = p a x * SEP_ARRAY p i (a + i:'a word) xs)`;


(* ---- theorems ---- *)

val SPLIT_ss = rewrites [SPLIT_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,SEP_EQ_def,
                         EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,IN_DIFF];

val SPLIT_TAC = FULL_SIMP_TAC (pure_ss++SPLIT_ss) [] \\ METIS_TAC [];

val STAR_SYM = store_thm("STAR_COMM",
  ``!p:'a set->bool q. p * q = q * p``,
  REWRITE_TAC [STAR_def,SPLIT_def,DISJOINT_DEF]
  \\ METIS_TAC [UNION_COMM,INTER_COMM,CONJ_SYM,CONJ_ASSOC]);

val STAR_ASSOC_LEMMA = prove(
  ``!x p:'a set->bool q r. (p * (q * r)) x ==> ((p * q) * r) x``,
  SIMP_TAC std_ss [STAR_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `u UNION u'` \\ Q.EXISTS_TAC `v'`
  \\ STRIP_TAC THEN1 SPLIT_TAC
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `u'` \\ SPLIT_TAC);

val STAR_ASSOC = store_thm("STAR_ASSOC",
  ``!p:'a set->bool q r. p * (q * r) = (p * q) * r``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] \\ METIS_TAC [STAR_ASSOC_LEMMA,STAR_SYM]);

val SEP_CLAUSES = store_thm("SEP_CLAUSES",
  ``!p q t c c'.
       (((SEP_EXISTS v. p v) * q)  = SEP_EXISTS v. p v * q) /\
       ((q * (SEP_EXISTS v. p v))  = SEP_EXISTS v. q * p v) /\
       (((SEP_EXISTS v. p v) \/ q) = SEP_EXISTS v. p v \/ q) /\
       ((q \/ (SEP_EXISTS v. p v)) = SEP_EXISTS v. q \/ p v) /\
       ((SEP_EXISTS v. q) = q) /\  ((SEP_EXISTS v. p v * cond (v = x)) = p x) /\
       (q \/ SEP_F = q) /\ (SEP_F \/ q = q) /\ (SEP_F * q = SEP_F) /\ (q * SEP_F = SEP_F) /\
       (r \/ r = r) /\ (q * (r \/ t) = q * r \/ q * t) /\ ((r \/ t) * q = r * q \/ t * q) /\
       (cond c \/ cond c' = cond (c \/ c')) /\ (cond c * cond c' = cond (c /\ c')) /\
       (cond T = emp) /\ (cond F = SEP_F) /\  (emp * q = q) /\ (q * emp = q)``,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS,STAR_def,SEP_DISJ_def,cond_def,SEP_F_def,emp_def]
  \\ SPLIT_TAC);

val SEP_EXISTS_COND = save_thm("SEP_EXISTS_COND",
  (GEN_ALL o GSYM o Q.INST [`q`|->`cond c`] o hd o 
   CONJUNCTS o SPEC_ALL) SEP_CLAUSES);

val SEP_EXISTS_THM = store_thm("SEP_EXISTS_THM",
 ``(SEP_EXISTS x. p x) s = ?x. p x s``,    
  SIMP_TAC std_ss [SEP_EXISTS]); 

val SPLIT_LEMMA = prove(
  ``!s t v. SPLIT s (t,v) = (v = s DIFF t) /\ t SUBSET s``,SPLIT_TAC);

val cond_STAR = store_thm("cond_STAR",
  ``!c s p. ((cond c * p) s = c /\ p s) /\ ((p * cond c) s = c /\ p s)``,
  Cases \\ SIMP_TAC std_ss [SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_F_def]);

val one_STAR = store_thm("one_STAR",
  ``!x s p. (one x * p) s = x IN s /\ p (s DELETE x)``,
  SIMP_TAC std_ss [STAR_def,one_def,SPLIT_LEMMA,DELETE_DEF,INSERT_SUBSET,EMPTY_SUBSET]);

val EQ_STAR = store_thm("EQ_STAR",
  ``!p s t. (SEP_EQ t * p) s = p (s DIFF t) /\ t SUBSET s``,
  SIMP_TAC std_ss [SEP_EQ_def,STAR_def,SPLIT_LEMMA] \\ METIS_TAC []);

val SEP_IMP_REFL = store_thm("SEP_IMP_REFL",
  ``!p. SEP_IMP p p``,
  SIMP_TAC std_ss [SEP_IMP_def]);

val SEP_IMP_TRANS = store_thm("SEP_IMP_TRANS",
  ``!p q r. SEP_IMP p q /\ SEP_IMP q r ==> SEP_IMP p r``,
  SIMP_TAC std_ss [SEP_IMP_def] \\ METIS_TAC []);

val SEP_IMP_FRAME = store_thm("SEP_IMP_FRAME",
  ``!p q. SEP_IMP p q ==> !r. SEP_IMP (p * r) (q * r)``,
  SIMP_TAC std_ss [SEP_IMP_def,STAR_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `v` \\ METIS_TAC []);

val SEP_IMP_MOVE_COND = store_thm("SEP_IMP_MOVE_COND",
  ``!c p q. SEP_IMP (p * cond c) q = c ==> SEP_IMP p q``,
  Cases \\ SIMP_TAC bool_ss [SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_F_def]);

val SEP_IMP_emp = store_thm("SEP_IMP_emp",
  ``!p. SEP_IMP emp p = p {}``,SIMP_TAC std_ss [SEP_IMP_def,emp_def]);

val SEP_IMP_cond = store_thm("SEP_IMP_cond",
  ``!g h. SEP_IMP (cond g) (cond h) = g ==> h``,
  SIMP_TAC std_ss [SEP_IMP_def,cond_def]);

val SEP_IMP_STAR = store_thm("SEP_IMP_STAR",
  ``!p p' q q'. SEP_IMP p p' /\ SEP_IMP q q' ==> SEP_IMP (p * q) (p' * q')``,
  SIMP_TAC std_ss [SEP_IMP_def,STAR_def] \\ METIS_TAC []);

val SEP_IMP_DISJ = store_thm("SEP_IMP_DISJ",
  ``!p p' q q'. SEP_IMP p p' /\ SEP_IMP q q' ==> SEP_IMP (p \/ q) (p' \/ q')``,
  SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def] \\ METIS_TAC []);

val SEP_IMP_EQ = store_thm("SEP_IMP_EQ",
  ``!p q. (p = q) = SEP_IMP p q /\ SEP_IMP q p``,
  FULL_SIMP_TAC bool_ss [SEP_IMP_def,FUN_EQ_THM] \\ METIS_TAC []);

val SEP_IMP_EXISTS_EXISTS = store_thm("SEP_IMP_EXISTS_EXISTS",
  ``(!x. SEP_IMP (p x) (q x)) ==> SEP_IMP ($SEP_EXISTS p) ($SEP_EXISTS q)``,
  SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ REPEAT STRIP_TAC 
  \\ Q.EXISTS_TAC `y` \\ ASM_SIMP_TAC std_ss []);

val SEP_IMP_SEP_HIDE = store_thm("SEP_IMP_SEP_HIDE",
  ``!p x. SEP_IMP (p x) (~p)``,
  SIMP_TAC std_ss [SEP_IMP_def,SEP_HIDE_def,SEP_EXISTS_THM] THEN METIS_TAC []);

val SPLIT_EQ = store_thm("SPLIT_EQ",
  ``!s u v. SPLIT s (u,v) = (u SUBSET s) /\ (v = s DIFF u)``,
  SIMP_TAC std_ss [SPLIT_def,SUBSET_DEF,EXTENSION,IN_DIFF,IN_UNION,
    DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER] \\ METIS_TAC []);

val fun2set_thm = store_thm("fun2set_thm",
  ``!f d a x. fun2set (f:'b->'a,d) (a,x) = (f a = x) /\ a IN d``,
  REWRITE_TAC [SIMP_RULE std_ss [IN_DEF] GSPECIFICATION,fun2set_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss [pairTheory.EXISTS_PROD]);

val read_fun2set = store_thm("read_fun2set",
  ``!a x p f. (one (a,x) * p) (fun2set (f,d)) ==> (f a = x) /\ a IN d``,
  SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm]);

val write_fun2set = store_thm("write_fun2set",
  ``!y a x p f. (one (a,x) * p) (fun2set (f,d)) ==> (p * one (a,y)) (fun2set ((a =+ y) f,d))``,
  SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm,combinTheory.APPLY_UPDATE_THM]
  \\ ONCE_REWRITE_TAC [STAR_SYM]
  \\ SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm,combinTheory.APPLY_UPDATE_THM]
  \\ NTAC 4 STRIP_TAC \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (t /\ p x ==> p y)``)
  \\ SIMP_TAC std_ss [EXTENSION] \\ Cases
  \\ SIMP_TAC std_ss [fun2set_thm,IN_DELETE]
  \\ SIMP_TAC std_ss [fun2set_thm,IN_DELETE,IN_DEF]
  \\ Cases_on `q = a` \\ ASM_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val fun2set_NEQ = store_thm("fun2set_NEQ",
  ``!a b x y f g p. (one (a,x) * one (b,y) * p) (fun2set (f,g)) ==> ~(a = b)``,
  REWRITE_TAC [GSYM STAR_ASSOC,one_STAR,IN_DELETE,PAIR_EQ,fun2set_def]
  \\ SIMP_TAC std_ss [GSPECIFICATION]);

val fun2set_DIFF = store_thm("fun2set_DIFF",
  ``!f x y. fun2set (f,x) DIFF fun2set (f,y) = fun2set (f,x DIFF y)``,
  SIMP_TAC std_ss [fun2set_def,EXTENSION,IN_DIFF,GSPECIFICATION]
  \\ SIMP_TAC std_ss [FORALL_PROD,PAIR_EQ] \\ METIS_TAC [])

val SUBSET_fun2set = store_thm("SUBSET_fun2set",
  ``!v df f:'a->'b. v SUBSET fun2set (f,df) ==> ?z. v = fun2set (f,z)``,
  REPEAT STRIP_TAC \\ Q.EXISTS_TAC `{ x | (x,f x) IN v }`
  \\ FULL_SIMP_TAC std_ss [fun2set_def,EXTENSION,GSPECIFICATION,SUBSET_DEF]
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD] \\ METIS_TAC []);

val fun2set_EMPTY = store_thm("fun2set_EMPTY",
  ``!f df. (fun2set (f,df) = {}) = (df = {})``,
  SIMP_TAC std_ss [fun2set_def,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY])

val IN_fun2set = store_thm("IN_fun2set",
  ``!a y h dh. (a,y) IN fun2set (h,dh) = (h a = y) /\ a IN dh``,
  SIMP_TAC std_ss [fun2set_def,GSPECIFICATION] \\ METIS_TAC []);

val fun2set_DELETE = store_thm("fun2set_DELETE",
  ``!a h dh. fun2set (h,dh) DELETE (a, h a) = fun2set (h,dh DELETE a)``,
  SIMP_TAC std_ss [fun2set_def,GSPECIFICATION,IN_DELETE,EXTENSION,
                   FORALL_PROD] THEN METIS_TAC []);

val SEP_ARRAY_APPEND = store_thm("SEP_ARRAY_APPEND",
  ``!xs ys p i a. 
      SEP_ARRAY p i a (xs ++ ys) =
      SEP_ARRAY p i a xs * SEP_ARRAY p i (a + n2w (LENGTH xs) * i) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [SEP_ARRAY_def,STAR_ASSOC,
    listTheory.APPEND,listTheory.LENGTH,SEP_CLAUSES,WORD_MULT_CLAUSES,WORD_ADD_0]
  \\ SIMP_TAC std_ss [arithmeticTheory.ADD1,WORD_MULT_CLAUSES,GSYM word_add_n2w,
       AC WORD_ADD_ASSOC WORD_ADD_COMM]);  

val SEP_REWRITE_THM = store_thm("SEP_REWRITE_THM",
  ``!q p x y. (!s. q s ==> (x = y)) ==> (q * p x = q * p y) /\ (p x * q = p y * q)``,
  SIMP_TAC std_ss [FUN_EQ_THM,STAR_def] THEN REPEAT STRIP_TAC THEN METIS_TAC []);

val cond_CONJ = store_thm("cond_CONJ",
  ``cond (c /\ d) = (cond c * cond d) : 'a set set``,
  SIMP_TAC std_ss [SEP_CLAUSES]);

val _ = export_theory();

