(* app load ["metisLib"] *)
open HolKernel boolLib bossLib Q listTheory rich_listTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "my_list";

(* -------------------------------------------------------- *)

val LIST_EQ = store_thm("LIST_EQ",
  `!a b. (LENGTH a = LENGTH b) /\
         (!x. x < LENGTH a ==> (EL x a = EL x b)) ==>
         (a = b)`,
  Induct_on `b` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
    THEN Induct_on `a` THEN RW_TAC list_ss []
    THEN1 POP_ASSUM (fn th => PROVE_TAC [(SIMP_RULE list_ss [] o SPEC `0`) th])
    THEN POP_ASSUM (fn th => PROVE_TAC [(GEN_ALL o SIMP_RULE list_ss [] o SPEC `SUC x`) th])
);

val NULL_SNOC = store_thm("NULL_SNOC",
  `!l x. ~NULL (SNOC x l)`,
  Cases THEN SIMP_TAC list_ss [SNOC]
);

val FILTER_ALL = store_thm("FILTER_ALL",
  `!l. (!n. n < LENGTH l ==> ~P (EL n l)) ==> (FILTER P l = [])`,
  Induct THEN RW_TAC list_ss []
    THEN1 (EXISTS_TAC `0` THEN ASM_SIMP_TAC list_ss [])
    THEN POP_ASSUM (fn th => PROVE_TAC [(GEN_ALL o SIMP_RULE list_ss [] o SPEC `SUC n`) th])
);

val FILTER_NONE = store_thm("FILTER_NONE",
  `!l. (!n. n < LENGTH l ==> P (EL n l)) ==> (FILTER P l = l)`,
  Induct THEN RW_TAC list_ss []
    THEN1 POP_ASSUM (fn th => ASM_SIMP_TAC std_ss [(GEN_ALL o SIMP_RULE list_ss [] o SPEC `SUC n`) th])
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE list_ss [] o SPEC `0`)
);

val MAP_GENLIST = store_thm("MAP_GENLIST",
  `!f g n. MAP f (GENLIST g n) = GENLIST (f o g) n`,
  Induct_on `n` THEN ASM_SIMP_TAC list_ss [GENLIST,MAP_SNOC]
);

val EL_GENLIST = store_thm("EL_GENLIST",
  `!f n x. x < n ==> (EL x (GENLIST f n) = f x)`,
  Induct_on `n` THEN1 SIMP_TAC arith_ss []
    THEN REPEAT STRIP_TAC THEN REWRITE_TAC [GENLIST]
    THEN Cases_on `x < n`
    THEN POP_ASSUM (fn th => ASSUME_TAC (SUBS [(GSYM o SPECL [`f`,`n`]) LENGTH_GENLIST] th)
                        THEN ASSUME_TAC th)
    THEN1 ASM_SIMP_TAC bool_ss [EL_SNOC]
    THEN `x = LENGTH (GENLIST f n)` by FULL_SIMP_TAC arith_ss [LENGTH_GENLIST]
    THEN ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC]
    THEN REWRITE_TAC [LENGTH_GENLIST]
);

val GENLIST_FUN_EQ = store_thm("GENLIST_FUN_EQ",
  `!n f g. (!x. x < n ==> (f x = g x)) ==> (GENLIST f n = GENLIST g n)`,
  metisLib.METIS_TAC [LIST_EQ,GSYM EL_GENLIST,LENGTH_GENLIST]
);

val SNOC_EL_FIRSTN = store_thm("SNOC_EL_FIRSTN",
  `!n l. n < LENGTH l ==> (SNOC (EL n l) (FIRSTN n l) = FIRSTN (SUC n) l)`,
  Induct THEN Cases_on `l` THEN ASM_SIMP_TAC list_ss [SNOC,FIRSTN]
);

val ZIP_FIRSTN_LEQ = store_thm("ZIP_FIRSTN_LEQ",
  `!n a b. n <= LENGTH a /\ LENGTH a <= LENGTH b ==>
             (ZIP (FIRSTN n a,FIRSTN n b) = FIRSTN n (ZIP (a,FIRSTN (LENGTH a) b)))`,
  Induct THEN ASM_SIMP_TAC list_ss [FIRSTN]
    THEN Cases THEN Cases THEN ASM_SIMP_TAC list_ss [FIRSTN,ZIP]
);

val ZIP_FIRSTN = store_thm("ZIP_FIRSTN",
  `!n a b. n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
             (ZIP (FIRSTN n a,FIRSTN n b) = FIRSTN n (ZIP (a,b)))`,
  SIMP_TAC arith_ss [ZIP_FIRSTN_LEQ,FIRSTN_LENGTH_ID]
);

val EL_FIRSTN = store_thm("EL_FIRSTN",
  `!n x l. x < n /\ n <= LENGTH l ==> (EL x (FIRSTN n l) = EL x l)`,
  Induct THEN ASM_SIMP_TAC list_ss [FIRSTN]
    THEN Cases THEN Cases THEN ASM_SIMP_TAC list_ss [FIRSTN]
);

val LENGTH_TL = store_thm("LENGTH_TL",
  `!l. 0 < LENGTH l ==> (LENGTH (TL l) = LENGTH l - 1)`,
  Cases THEN SIMP_TAC list_ss []
);

val ZIP_APPEND = store_thm("ZIP_APPEND",
  `!a b c d. (LENGTH a = LENGTH b) /\
             (LENGTH c = LENGTH d) ==>
             (ZIP (a,b) ++ ZIP (c,d) = ZIP (a ++ c,b ++ d))`,
  Induct_on `b` THEN1 SIMP_TAC list_ss [LENGTH_NIL]    THEN Induct_on `d` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
    THEN Induct_on `a` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
    THEN Induct_on `c` THEN1 SIMP_TAC list_ss [LENGTH_NIL]
    THEN RW_TAC list_ss []    THEN NTAC 3 (PAT_ASSUM `!a c d. P` (K ALL_TAC))
    THEN `LENGTH (h::c) = LENGTH (h'::d)` by ASM_SIMP_TAC list_ss []
    THEN PAT_ASSUM `!a c d. P` (SPECL_THEN [`a`,`h::c`,`h'::d`] IMP_RES_TAC)
    THEN FULL_SIMP_TAC list_ss []
);

val ZIP_GENLIST = store_thm("ZIP_GENLIST",
  `!l f n. (LENGTH l = n) ==>
     (ZIP (l,GENLIST f n) = GENLIST (\x. (EL x l,f x)) n)`,
  REPEAT STRIP_TAC
    THEN `LENGTH (ZIP (l,GENLIST f n)) = LENGTH (GENLIST (\x. (EL x l,f x)) n)`
      by metisLib.METIS_TAC [LENGTH_GENLIST,LENGTH_ZIP]
    THEN IMP_RES_TAC LIST_EQ
    THEN POP_ASSUM MATCH_MP_TAC
    THEN RW_TAC arith_ss [LENGTH_GENLIST,LENGTH_ZIP,listTheory.EL_ZIP,EL_GENLIST]
);

val GENLIST_APPEND = store_thm("GENLIST_APPEND",
  `!f a b. GENLIST f (a + b) = (GENLIST f b) ++ (GENLIST (\t. f (t + b)) a)`,
  Induct_on `a`
    THEN ASM_SIMP_TAC list_ss [GENLIST,APPEND_SNOC,arithmeticTheory.ADD_CLAUSES]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
