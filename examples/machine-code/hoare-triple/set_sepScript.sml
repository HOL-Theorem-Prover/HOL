Theory set_sep
Ancestors
  pred_set pair words

val _ = ParseExtras.temp_loose_equality()

(* ---- definitions ---- *)

Definition one_def:      one x = \s. (s = {x})
End
Definition emp_def:      emp = \s. (s = {})
End
Definition cond_def:     cond c = \s. (s = {}) /\ c
End
Definition SEP_F_def:    SEP_F s = F
End
Definition SEP_T_def:    SEP_T s = T
End
Definition SPLIT_def:    SPLIT (s:'a set) (u,v) ⇔ (u ∪ v = s) ∧ DISJOINT u v
End
Definition STAR_def:     STAR p q = (\s. ?u v. SPLIT s (u,v) /\ p u /\ q v)
End
Definition SEP_EQ_def:   SEP_EQ x = \s. s = x
End

val SEP_EXISTS = new_binder_definition("SEP_EXISTS",
  ``($SEP_EXISTS) = \f s:'a set. $? (\y. f y s)``);

Definition SEP_HIDE_def:   SEP_HIDE p = SEP_EXISTS x. p x
End
Definition SEP_DISJ_def:   SEP_DISJ p q = (\s. p s \/ q s)
End

val _ = overload_on ("*",Term`STAR`);
val _ = overload_on ("~",Term`SEP_HIDE`);
val _ = overload_on ("\\/",Term`SEP_DISJ`);

Definition sidecond_def:   sidecond = cond
End
Definition precond_def:    precond = cond
End

Definition SEP_IMP_def:    SEP_IMP p q = !s. p s ==> q s
End

Definition fun2set_def:   fun2set (f:'b->'a,d) =  { (a,f a) | a IN d }
End

Definition SEP_ARRAY_def:
  (SEP_ARRAY p i a [] = emp) /\
  (SEP_ARRAY p i a (x::xs) = p a x * SEP_ARRAY p i (a + i:'a word) xs)
End


(* ---- theorems ---- *)

val SPLIT_ss = rewrites [SPLIT_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,SEP_EQ_def,
                         EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,IN_DIFF];

val SPLIT_TAC = FULL_SIMP_TAC (pure_ss++SPLIT_ss) [] \\ METIS_TAC [];

Theorem STAR_COMM:
    !p:'a set->bool q. p * q = q * p
Proof
  REWRITE_TAC [STAR_def,SPLIT_def,DISJOINT_DEF]
  \\ METIS_TAC [UNION_COMM,INTER_COMM,CONJ_SYM,CONJ_ASSOC]
QED

val STAR_ASSOC_LEMMA = prove(
  ``!x p:'a set->bool q r. (p * (q * r)) x ==> ((p * q) * r) x``,
  SIMP_TAC std_ss [STAR_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `u UNION u'` \\ Q.EXISTS_TAC `v'`
  \\ STRIP_TAC THEN1 SPLIT_TAC
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `u'` \\ SPLIT_TAC);

Theorem STAR_ASSOC:
    !p:'a set->bool q r. p * (q * r) = (p * q) * r
Proof
  ONCE_REWRITE_TAC [FUN_EQ_THM] \\ METIS_TAC [STAR_ASSOC_LEMMA,STAR_COMM]
QED

Theorem SEP_CLAUSES:
    !p q t c c'.
       (((SEP_EXISTS v. p v) * q)  = SEP_EXISTS v. p v * q) /\
       ((q * (SEP_EXISTS v. p v))  = SEP_EXISTS v. q * p v) /\
       (((SEP_EXISTS v. p v) \/ q) = SEP_EXISTS v. p v \/ q) /\
       ((q \/ (SEP_EXISTS v. p v)) = SEP_EXISTS v. q \/ p v) /\
       ((SEP_EXISTS v. q) = q) /\  ((SEP_EXISTS v. p v * cond (v = x)) = p x) /\
       (q \/ SEP_F = q) /\ (SEP_F \/ q = q) /\ (SEP_F * q = SEP_F) /\ (q * SEP_F = SEP_F) /\
       (r \/ r = r) /\ (q * (r \/ t) = q * r \/ q * t) /\ ((r \/ t) * q = r * q \/ t * q) /\
       (cond c \/ cond c' = cond (c \/ c')) /\ (cond c * cond c' = cond (c /\ c')) /\
       (cond T = emp) /\ (cond F = SEP_F) /\  (emp * q = q) /\ (q * emp = q)
Proof
  ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS,STAR_def,SEP_DISJ_def,cond_def,SEP_F_def,emp_def]
  \\ SPLIT_TAC
QED

val SEP_EXISTS_COND = save_thm("SEP_EXISTS_COND",
  (GEN_ALL o GSYM o Q.INST [`q`|->`cond c`] o hd o
   CONJUNCTS o SPEC_ALL) SEP_CLAUSES);

Theorem SEP_EXISTS_THM:
   (SEP_EXISTS x. p x) s = ?x. p x s
Proof
  SIMP_TAC std_ss [SEP_EXISTS]
QED

val SPLIT_LEMMA = prove(
  ``!s t v. SPLIT s (t,v) = (v = s DIFF t) /\ t SUBSET s``,SPLIT_TAC);

Theorem cond_STAR:
    !c s p. ((cond c * p) s = c /\ p s) /\ ((p * cond c) s = c /\ p s)
Proof
  Cases \\ SIMP_TAC std_ss [SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_F_def]
QED

Theorem one_STAR:
    !x s p. (one x * p) s = x IN s /\ p (s DELETE x)
Proof
  SIMP_TAC std_ss [STAR_def,one_def,SPLIT_LEMMA,DELETE_DEF,INSERT_SUBSET,EMPTY_SUBSET]
QED

Theorem EQ_STAR:
    !p s t. (SEP_EQ t * p) s = p (s DIFF t) /\ t SUBSET s
Proof
  SIMP_TAC std_ss [SEP_EQ_def,STAR_def,SPLIT_LEMMA] \\ METIS_TAC []
QED

Theorem SEP_IMP_REFL:
    !p. SEP_IMP p p
Proof
  SIMP_TAC std_ss [SEP_IMP_def]
QED

Theorem SEP_IMP_TRANS:
    !p q r. SEP_IMP p q /\ SEP_IMP q r ==> SEP_IMP p r
Proof
  SIMP_TAC std_ss [SEP_IMP_def] \\ METIS_TAC []
QED

Theorem SEP_IMP_FRAME:
    !p q. SEP_IMP p q ==> !r. SEP_IMP (p * r) (q * r)
Proof
  SIMP_TAC std_ss [SEP_IMP_def,STAR_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `v` \\ METIS_TAC []
QED

Theorem SEP_IMP_MOVE_COND:
    !c p q. SEP_IMP (p * cond c) q = c ==> SEP_IMP p q
Proof
  Cases \\ SIMP_TAC bool_ss [SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_F_def]
QED

Theorem SEP_IMP_emp:
    !p. SEP_IMP emp p = p {}
ProofSIMP_TAC std_ss [SEP_IMP_def,emp_def]
QED

Theorem SEP_IMP_cond:
    !g h. SEP_IMP (cond g) (cond h) = g ==> h
Proof
  SIMP_TAC std_ss [SEP_IMP_def,cond_def]
QED

Theorem SEP_IMP_STAR:
    !p p' q q'. SEP_IMP p p' /\ SEP_IMP q q' ==> SEP_IMP (p * q) (p' * q')
Proof
  SIMP_TAC std_ss [SEP_IMP_def,STAR_def] \\ METIS_TAC []
QED

Theorem SEP_IMP_DISJ:
    !p p' q q'. SEP_IMP p p' /\ SEP_IMP q q' ==> SEP_IMP (p \/ q) (p' \/ q')
Proof
  SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def] \\ METIS_TAC []
QED

Theorem SEP_IMP_EQ:
    !p q. (p = q) = SEP_IMP p q /\ SEP_IMP q p
Proof
  FULL_SIMP_TAC bool_ss [SEP_IMP_def,FUN_EQ_THM] \\ METIS_TAC []
QED

Theorem SEP_IMP_EXISTS_EXISTS:
    (!x. SEP_IMP (p x) (q x)) ==> SEP_IMP ($SEP_EXISTS p) ($SEP_EXISTS q)
Proof
  SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `y` \\ ASM_SIMP_TAC std_ss []
QED

Theorem SEP_IMP_SEP_HIDE:
    !p x. SEP_IMP (p x) (~p)
Proof
  SIMP_TAC std_ss [SEP_IMP_def,SEP_HIDE_def,SEP_EXISTS_THM] THEN METIS_TAC []
QED

Theorem SEP_IMP_PRE_DISJ:
    !p1 p2 q. SEP_IMP (p1 \/ p2) q = SEP_IMP p1 q /\ SEP_IMP p2 q
Proof
  SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def] \\ METIS_TAC []
QED

Theorem SEP_IMP_PRE_EXISTS:
    !p q. SEP_IMP (SEP_EXISTS x. p x) q = !x. SEP_IMP (p x) q
Proof
  SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []
QED

Theorem SEP_DISJ_COMM:
    !p q. p \/ q = SEP_DISJ q p
Proof
  SIMP_TAC std_ss [SEP_DISJ_def,FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
QED

Theorem SEP_DISJ_ASSOC:
    !p q r. SEP_DISJ (SEP_DISJ p q) r = p \/ (q \/ r)
Proof
  SIMP_TAC std_ss [SEP_DISJ_def,FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
QED

Theorem SPLIT_EQ:
    !s u v. SPLIT s (u,v) = (u SUBSET s) /\ (v = s DIFF u)
Proof
  SIMP_TAC std_ss [SPLIT_def,SUBSET_DEF,EXTENSION,IN_DIFF,IN_UNION,
    DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER] \\ METIS_TAC []
QED

Theorem fun2set_thm:
    !f d a x. fun2set (f:'b->'a,d) (a,x) = (f a = x) /\ a IN d
Proof
  REWRITE_TAC [SIMP_RULE std_ss [IN_DEF] GSPECIFICATION,fun2set_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss [pairTheory.EXISTS_PROD]
QED

Theorem read_fun2set:
    !a x p f. (one (a,x) * p) (fun2set (f,d)) ==> (f a = x) /\ a IN d
Proof
  SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm]
QED

Theorem write_fun2set:
    !y a x p f. (one (a,x) * p) (fun2set (f,d)) ==> (p * one (a,y)) (fun2set ((a =+ y) f,d))
Proof
  SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm,combinTheory.APPLY_UPDATE_THM]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [one_STAR,IN_DEF,fun2set_thm,combinTheory.APPLY_UPDATE_THM]
  \\ NTAC 4 STRIP_TAC \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (t /\ p x ==> p y)``)
  \\ SIMP_TAC std_ss [EXTENSION] \\ Cases
  \\ SIMP_TAC std_ss [fun2set_thm,IN_DELETE]
  \\ SIMP_TAC std_ss [fun2set_thm,IN_DELETE,IN_DEF]
  \\ Cases_on `q = a` \\ ASM_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  \\ METIS_TAC []
QED

Theorem fun2set_eq:
    !f g d. (fun2set (f, d) = fun2set (g, d)) = (!a. a IN d ==> (f a = g a))
Proof
   SRW_TAC [] [FUN_EQ_THM]
   \\ EQ_TAC
   \\ REPEAT STRIP_TAC
   THENL [
      Q.PAT_X_ASSUM `!x. P` (Q.SPEC_THEN `(a, f a)` ASSUME_TAC),
      Cases_on `x` \\ Cases_on `q IN d`
   ]
   \\ REV_FULL_SIMP_TAC std_ss [fun2set_thm]
QED

Theorem one_fun2set:
    !a x p f. (one (a,x) * p) (fun2set (f,d)) =
              (f a = x) /\ a IN d /\ p (fun2set (f,d DELETE a))
Proof
  SIMP_TAC std_ss [fun2set_def,one_STAR,GSPECIFICATION] \\ REPEAT STRIP_TAC
  \\ Cases_on `f a = x` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `a IN d` \\ ASM_SIMP_TAC std_ss [] \\ AP_TERM_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_DELETE,FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []
QED

Theorem fun2set_NEQ:
    !a b x y f g p. (one (a,x) * one (b,y) * p) (fun2set (f,g)) ==> ~(a = b)
Proof
  REWRITE_TAC [GSYM STAR_ASSOC,one_STAR,IN_DELETE,PAIR_EQ,fun2set_def]
  \\ SIMP_TAC std_ss [GSPECIFICATION]
QED

Theorem fun2set_DIFF:
    !f x y. fun2set (f,x) DIFF fun2set (f,y) = fun2set (f,x DIFF y)
Proof
  SIMP_TAC std_ss [fun2set_def,EXTENSION,IN_DIFF,GSPECIFICATION]
  \\ SIMP_TAC std_ss [FORALL_PROD,PAIR_EQ] \\ METIS_TAC []
QED

Theorem SUBSET_fun2set:
    !v df f:'a->'b. v SUBSET fun2set (f,df) ==> ?z. v = fun2set (f,z)
Proof
  REPEAT STRIP_TAC \\ Q.EXISTS_TAC `{ x | (x,f x) IN v }`
  \\ FULL_SIMP_TAC std_ss [fun2set_def,EXTENSION,GSPECIFICATION,SUBSET_DEF]
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD] \\ METIS_TAC []
QED

Theorem fun2set_EMPTY:
    !f df. (fun2set (f,df) = {}) = (df = {})
Proof
  SIMP_TAC std_ss [fun2set_def,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
QED

Theorem IN_fun2set:
    !a y h dh. (a,y) IN fun2set (h,dh) = (h a = y) /\ a IN dh
Proof
  SIMP_TAC std_ss [fun2set_def,GSPECIFICATION] \\ METIS_TAC []
QED

Theorem fun2set_DELETE:
    !a h dh. fun2set (h,dh) DELETE (a, h a) = fun2set (h,dh DELETE a)
Proof
  SIMP_TAC std_ss [fun2set_def,GSPECIFICATION,IN_DELETE,EXTENSION,
                   FORALL_PROD] THEN METIS_TAC []
QED

val SPLIT_fun2set_IMP = prove(
  ``SPLIT (fun2set (f,df)) (u,v) ==>
    (u = fun2set(f,df DIFF { x | (x,f x) IN v }))``,
  SIMP_TAC std_ss [SPLIT_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,NOT_IN_EMPTY,
      DISJOINT_DEF,IN_INTER,fun2set_def,GSPECIFICATION,IN_DIFF]
  \\ METIS_TAC []);

val SPLIT_SYM_IMP = prove(
  ``SPLIT x (u,v) ==> SPLIT x (v,u) ``,
  SIMP_TAC std_ss [SPLIT_def,DISJOINT_DEF] \\ METIS_TAC [UNION_COMM,INTER_COMM]);

Theorem fun2set_STAR_IMP:
    (p * q) (fun2set (f,df)) ==>
    ?x y. p (fun2set (f,df DIFF y)) /\ q (fun2set (f,df DIFF x))
Proof
  SIMP_TAC std_ss [STAR_def] \\ REPEAT STRIP_TAC \\ IMP_RES_TAC SPLIT_SYM_IMP
  \\ IMP_RES_TAC SPLIT_fun2set_IMP \\ METIS_TAC []
QED

Theorem one_fun2set_IMP:
    (one (a,x)) (fun2set (f,df)) ==> (f a = x) /\ a IN df
Proof
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (REWRITE_RULE [SEP_CLAUSES] (Q.SPECL [`a`,`x`,`emp`] one_fun2set))
QED

Theorem DIFF_UNION:
    !x y z. x DIFF y DIFF z = x DIFF (y UNION z)
Proof
  SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION] \\ METIS_TAC []
QED

Theorem SEP_ARRAY_APPEND:
    !xs ys p i a.
      SEP_ARRAY p i a (xs ++ ys) =
      SEP_ARRAY p i a xs * SEP_ARRAY p i (a + n2w (LENGTH xs) * i) ys
Proof
  Induct \\ ASM_SIMP_TAC std_ss [SEP_ARRAY_def,STAR_ASSOC,
    listTheory.APPEND,listTheory.LENGTH,SEP_CLAUSES,WORD_MULT_CLAUSES,WORD_ADD_0]
  \\ SIMP_TAC std_ss [arithmeticTheory.ADD1,WORD_MULT_CLAUSES,GSYM word_add_n2w,
       AC WORD_ADD_ASSOC WORD_ADD_COMM]
QED

Theorem SEP_REWRITE_THM:
    !q p x y. (!s. q s ==> (x = y)) ==> (q * p x = q * p y) /\ (p x * q = p y * q)
Proof
  SIMP_TAC std_ss [FUN_EQ_THM,STAR_def] THEN REPEAT STRIP_TAC THEN METIS_TAC []
QED

Theorem cond_CONJ:
    cond (c /\ d) = (cond c * cond d) : 'a set set
Proof
  SIMP_TAC std_ss [SEP_CLAUSES]
QED

Theorem IMP_IMP:
    !b c d.b /\ (c ==> d) ==> ((b ==> c) ==> d)
Proof
  METIS_TAC []
QED

