structure permScript =
struct


open HolKernel basicHol90Lib listTheory listXTheory bossLib;
infix THEN THENL |-> ;
infix 8 by;

val _ = new_theory"perm";


(*---------------------------------------------------------------------------*
 * What's a permutation? This definition uses universal quantification to    *
 * define it. There are other ways, which could be compared to this, e.g.    *
 * as an inductive definition, or as a particular kind of function.          *
 *---------------------------------------------------------------------------*)

val perm_def = Define
  `perm L1 L2 = !x. filter ($= x) L1 = filter ($= x) L2`;


val perm_refl = Q.store_thm
("perm_refl",
    `!L. perm L L`,
    PROVE_TAC[perm_def]);


val perm_intro = Q.store_thm
("perm_intro",
    `!x y. (x=y) ==> perm x y`,
    PROVE_TAC[perm_refl]);


val perm_trans =  
Q.store_thm
("perm_trans",
  `transitive perm`,
 RW_TAC list_ss [TCTheory.transitive_def] 
  THEN PROVE_TAC[perm_def]);


val trans_permute = save_thm
("trans_permute",
 REWRITE_RULE [TCTheory.transitive_def] perm_trans);


val perm_sym = 
Q.store_thm
("perm_sym",
  `!l1 l2. perm l1 l2 = perm l2 l1`,
PROVE_TAC [perm_def]);


val perm_cong = 
Q.store_thm
("perm_cong",
`!(L1:'a list) L2 L3 L4. 
     perm L1 L3 /\ 
     perm L2 L4
     ==> perm (APPEND L1 L2) (APPEND L3 L4)`,
PROVE_TAC [perm_def,filter_append_distrib]);

val cons_append = PROVE [APPEND] `!L h. CONS h L = APPEND [h] L`;

val perm_mono = 
Q.store_thm
("perm_mono",
`!l1 l2 x. perm l1 l2 ==> perm (CONS x l1) (CONS x l2)`,
PROVE_TAC [cons_append,perm_cong, perm_refl]);


val perm_cons_iff = 
let val lem = 
Q.prove`perm (CONS x l1) (CONS x l2) ==> perm l1 l2`
(RW_TAC list_ss [perm_def,filter_def]
   THEN POP_ASSUM (MP_TAC o Q.SPEC`x'`)
   THEN RW_TAC list_ss [])
in 
  save_thm ("perm_cons_iff",
            GEN_ALL(IMP_ANTISYM_RULE lem (SPEC_ALL perm_mono)))
end;

val perm_nil = 
Q.store_thm
("perm_nil",
 `!L. (perm L [] = (L=[])) /\ 
      (perm [] L = (L=[]))`,
Cases THEN RW_TAC list_ss [perm_def,filter_def]
 THEN Q.EXISTS_TAC `h`
 THEN RW_TAC list_ss []);


val lem = Q.prove
 `!h l1 l2. APPEND (filter ($=h) l1) (CONS h l2)
            = CONS h (APPEND (filter ($=h) l1) l2)`
(Induct_on `l1` 
   THEN RW_TAC list_ss [filter_def] 
   THEN PROVE_TAC[]);


val perm_append = 
Q.store_thm
("perm_append",
 `!l1 l2. perm (APPEND l1 l2) (APPEND l2 l1)`,
RW_TAC list_ss [perm_def,filter_append_distrib]
  THEN Induct_on `l1` 
  THEN RW_TAC list_ss [filter_def,lem]
  THEN PROVE_TAC[]);;


val cons_perm = 
Q.store_thm
("cons_perm",
`!x L M N. perm L (APPEND M N) 
            ==> 
          perm (CONS x L) (APPEND M (CONS x N))`,
RW_TAC bool_ss []
 THEN MATCH_MP_TAC trans_permute
 THEN PROVE_TAC [perm_mono, perm_append, APPEND, trans_permute]);


val append_perm_sym = 
Q.store_thm
("append_perm_sym",
`!A B C. perm (APPEND A B) C ==> perm (APPEND B A) C`,
PROVE_TAC [trans_permute, perm_append]);

val perm_split = 
Q.store_thm
("perm_split",
`!P l. perm l (APPEND (filter P l) (filter (~ o P) l))`,
RW_TAC bool_ss [combinTheory.o_DEF]
 THEN Induct_on `l`
 THEN RW_TAC list_ss [filter_def,perm_refl] 
 THEN PROVE_TAC [APPEND,perm_mono,cons_perm]);


(*---------------------------------------------------------------------------
    Directly performs one "sorting step" between 2 non-empty lists that 
    are permutations of each other.
 *---------------------------------------------------------------------------*)

val perm_sort_step = Q.prove
`!l h t. perm (CONS h t) l ==> ?rst. CONS h rst = filter ($=h) l`
(RW_TAC list_ss [perm_def,filter_def] 
  THEN POP_ASSUM (MP_TAC o Q.SPEC`h`)
  THEN RW_TAC bool_ss []
  THEN PROVE_TAC[]);


val perm_step = Q.prove
`!l h t. perm (CONS h t) l 
          ==> ?u. perm l (CONS h u) /\ 
                  (LENGTH l = LENGTH (CONS h u))`
(RW_TAC bool_ss []
  THEN IMP_RES_TAC perm_sort_step
  THEN Q.EXISTS_TAC `APPEND rst (filter ($~ o $= h) l)`
  THEN PROVE_TAC [APPEND, length_append_filter,perm_split]);


val perm_length = Q.store_thm("perm_length",
`!l1 l2. perm l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
Induct 
  THEN RW_TAC list_ss [perm_nil]
  THEN IMP_RES_TAC perm_step
  THEN `perm l1 u` by PROVE_TAC [trans_permute,perm_cons_iff]
  THEN RW_TAC list_ss []);


val _ = export_theory();

end;
