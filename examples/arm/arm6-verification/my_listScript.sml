(* load "rich_listTheory"; *)
Theory my_list
Ancestors
  list rich_list arithmetic
Libs
  Q

(* ------------------------------------------------------------------------- *)

val op >- = op THEN1;

(* ------------------------------------------------------------------------- *)

Theorem LIST_EQ:
   !a b. (LENGTH a = LENGTH b) /\
         (!x. x < LENGTH a ==> (EL x a = EL x b)) ==>
         (a = b)
Proof
  Induct_on `b` >- SIMP_TAC list_ss [LENGTH_NIL]
    \\ Induct_on `a` \\ RW_TAC list_ss []
    >- POP_ASSUM (fn th => PROVE_TAC [(SIMP_RULE list_ss [] o SPEC `0`) th])
    \\ POP_ASSUM (fn th => PROVE_TAC
         [(GEN_ALL o SIMP_RULE list_ss [] o SPEC `SUC x`) th])
QED

Theorem NULL_SNOC:
   !l x. ~NULL (SNOC x l)
Proof
  Cases \\ SIMP_TAC list_ss [SNOC]
QED

Theorem FILTER_ALL:
   !l. (!n. n < LENGTH l ==> ~P (EL n l)) ==> (FILTER P l = [])
Proof
  Induct \\ RW_TAC list_ss []
    >- (EXISTS_TAC `0` \\ ASM_SIMP_TAC list_ss [])
    \\ POP_ASSUM (fn th => PROVE_TAC
         [(GEN_ALL o SIMP_RULE list_ss [] o SPEC `SUC n`) th])
QED

Theorem FILTER_NONE:
   !l. (!n. n < LENGTH l ==> P (EL n l)) ==> (FILTER P l = l)
Proof
  Induct \\ RW_TAC list_ss []
    >- POP_ASSUM (fn th => ASM_SIMP_TAC std_ss
         [(GEN_ALL o SIMP_RULE list_ss [] o SPEC `SUC n`) th])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE list_ss [] o SPEC `0`)
QED

Theorem MAP_GENLIST:
   !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n
Proof
  Induct_on `n` \\ ASM_SIMP_TAC list_ss [GENLIST,MAP_SNOC]
QED

Theorem EL_GENLIST:
   !f n x. x < n ==> (EL x (GENLIST f n) = f x)
Proof
  Induct_on `n` >- SIMP_TAC arith_ss []
    \\ REPEAT STRIP_TAC \\ REWRITE_TAC [GENLIST]
    \\ Cases_on `x < n`
    \\ POP_ASSUM (fn th => ASSUME_TAC
           (SUBS [(GSYM o SPECL [`f`,`n`]) LENGTH_GENLIST] th)
              \\ ASSUME_TAC th)
    >- ASM_SIMP_TAC bool_ss [EL_SNOC]
    \\ `x = LENGTH (GENLIST f n)` by FULL_SIMP_TAC arith_ss [LENGTH_GENLIST]
    \\ ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC]
    \\ REWRITE_TAC [LENGTH_GENLIST]
QED

val HD_GENLIST = save_thm("HD_GENLIST",
  (SIMP_RULE arith_ss [EL] o SPECL [`f`,`SUC n`,`0`]) EL_GENLIST);

Theorem GENLIST_FUN_EQ:
   !n f g. (!x. x < n ==> (f x = g x)) ==> (GENLIST f n = GENLIST g n)
Proof
  metisLib.METIS_TAC [LIST_EQ,GSYM EL_GENLIST,LENGTH_GENLIST]
QED

Theorem EL_BUTFIRSTN:
   !m n l. m + n < LENGTH l ==>
      (EL m (BUTFIRSTN n l) = EL (m + n) l)
Proof
  Induct_on `l` \\ RW_TAC list_ss [] \\ Cases_on `n`
    \\ FULL_SIMP_TAC list_ss [BUTFIRSTN,ADD_CLAUSES]
QED

Theorem SNOC_EL_FIRSTN:
   !n l. n < LENGTH l ==> (SNOC (EL n l) (FIRSTN n l) = FIRSTN (SUC n) l)
Proof
  Induct \\ Cases_on `l` \\ ASM_SIMP_TAC list_ss [SNOC,FIRSTN]
QED

Theorem ZIP_FIRSTN_LEQ:
   !n a b. n <= LENGTH a /\ LENGTH a <= LENGTH b ==>
     (ZIP (FIRSTN n a,FIRSTN n b) = FIRSTN n (ZIP (a,FIRSTN (LENGTH a) b)))
Proof
  Induct \\ ASM_SIMP_TAC list_ss [FIRSTN]
    \\ Cases \\ Cases \\ ASM_SIMP_TAC list_ss [FIRSTN,ZIP]
QED

Theorem ZIP_FIRSTN:
   !n a b. n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
     (ZIP (FIRSTN n a,FIRSTN n b) = FIRSTN n (ZIP (a,b)))
Proof
  SIMP_TAC arith_ss [ZIP_FIRSTN_LEQ,FIRSTN_LENGTH_ID]
QED

Theorem EL_FIRSTN:
   !n x l. x < n /\ n <= LENGTH l ==> (EL x (FIRSTN n l) = EL x l)
Proof
  Induct \\ ASM_SIMP_TAC list_ss [FIRSTN]
    \\ Cases \\ Cases \\ ASM_SIMP_TAC list_ss [FIRSTN]
QED

Theorem LENGTH_TL:
   !l. 0 < LENGTH l ==> (LENGTH (TL l) = LENGTH l - 1)
Proof
  Cases \\ SIMP_TAC list_ss []
QED

Theorem ZIP_APPEND:
   !a b c d. (LENGTH a = LENGTH b) /\
             (LENGTH c = LENGTH d) ==>
             (ZIP (a,b) ++ ZIP (c,d) = ZIP (a ++ c,b ++ d))
Proof
  Induct_on `b` >- SIMP_TAC list_ss [LENGTH_NIL]
    \\ Induct_on `d` >- SIMP_TAC list_ss [LENGTH_NIL]
    \\ Induct_on `a` >- SIMP_TAC list_ss [LENGTH_NIL]
    \\ Induct_on `c` >- SIMP_TAC list_ss [LENGTH_NIL]
    \\ MAP_EVERY X_GEN_TAC [`h1`,`h2`,`h3`,`h4`]
    \\ RW_TAC list_ss []
    \\ `LENGTH (h1::c) = LENGTH (h3::d)`
      by ASM_SIMP_TAC list_ss []
    \\ `ZIP (a,b) ++ ZIP (h1::c,h3::d) = ZIP (a ++ h1::c,b ++ h3::d)`
      by ASM_SIMP_TAC list_ss []
    \\ FULL_SIMP_TAC list_ss []
QED

Theorem ZIP_GENLIST:
   !l f n. (LENGTH l = n) ==>
     (ZIP (l,GENLIST f n) = GENLIST (\x. (EL x l,f x)) n)
Proof
  REPEAT STRIP_TAC
    \\ `LENGTH (ZIP (l,GENLIST f n)) = LENGTH (GENLIST (\x. (EL x l,f x)) n)`
    by metisLib.METIS_TAC [LENGTH_GENLIST,LENGTH_ZIP]
    \\ IMP_RES_TAC LIST_EQ
    \\ POP_ASSUM MATCH_MP_TAC
    \\ RW_TAC arith_ss [LENGTH_GENLIST,LENGTH_ZIP,listTheory.EL_ZIP,EL_GENLIST]
QED

Theorem GENLIST_APPEND:
   !f a b. GENLIST f (a + b) = (GENLIST f b) ++ (GENLIST (\t. f (t + b)) a)
Proof
  Induct_on `a`
    \\ ASM_SIMP_TAC list_ss [GENLIST,APPEND_SNOC,arithmeticTheory.ADD_CLAUSES]
QED

Theorem NULL_LENGTH:
   !l. NULL l = (LENGTH l = 0)
Proof
  Cases \\ METIS_TAC [LENGTH,NULL,SUC_NOT]
QED

Theorem APPEND_SNOC1:
   !l1 x l2. SNOC x l1 ++ l2 = l1 ++ x::l2
Proof
  METIS_TAC [SNOC_APPEND,CONS_APPEND, APPEND_ASSOC]
QED

(* ------------------------------------------------------------------------- *)

