(*---------------------------------------------------------------------------
          Theory of list permutations
 ---------------------------------------------------------------------------*)
Theory perm
Ancestors
  list

(*---------------------------------------------------------------------------*
 * What's a permutation? This definition uses universal quantification to    *
 * define it. There are other ways, which could be compared to this, e.g.    *
 * as an inductive definition, or as a particular kind of function.          *
 *---------------------------------------------------------------------------*)

Definition PERM_def:   PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2
End


Theorem PERM_refl:
     !L. PERM L L
Proof
    PROVE_TAC[PERM_def]
QED


Theorem PERM_intro:
     !x y. (x=y) ==> PERM x y
Proof
    PROVE_TAC[PERM_refl]
QED


Theorem PERM_trans:
   transitive PERM
Proof
 RW_TAC list_ss [relationTheory.transitive_def]
  THEN PROVE_TAC[PERM_def]
QED


Theorem PERM_trans1 =
 REWRITE_RULE [relationTheory.transitive_def] PERM_trans;


Theorem PERM_sym:
   !l1 l2. PERM l1 l2 = PERM l2 l1
Proof
PROVE_TAC [PERM_def]
QED

val FILTER_APPEND_distrib = Q.prove(
`!P L M. FILTER P (APPEND L M) = APPEND (FILTER P L) (FILTER P M)`,
Induct_on `L` THEN RW_TAC list_ss [FILTER]);

Theorem PERM_cong:
 !(L1:'a list) L2 L3 L4.
     PERM L1 L3 /\
     PERM L2 L4
     ==> PERM (APPEND L1 L2) (APPEND L3 L4)
Proof
PROVE_TAC [PERM_def,FILTER_APPEND_distrib]
QED

val CONS_APPEND = PROVE [APPEND] (Term`!L h. h::L = APPEND [h] L`);

Theorem PERM_mono:
 !l1 l2 x. PERM l1 l2 ==> PERM (x::l1) (x::l2)
Proof
PROVE_TAC [CONS_APPEND,PERM_cong, PERM_refl]
QED


val PERM_CONS_iff =
let val lem =
Q.prove(`PERM (x::l1) (x::l2) ==> PERM l1 l2`,
RW_TAC list_ss [PERM_def,FILTER]
   THEN POP_ASSUM (MP_TAC o Q.SPEC`x'`)
   THEN RW_TAC list_ss [])
in
  save_thm ("PERM_CONS_iff",
            GEN_ALL(IMP_ANTISYM_RULE lem (SPEC_ALL PERM_mono)))
end;

Theorem PERM_nil:
  !L. (PERM L [] = (L=[])) /\
      (PERM [] L = (L=[]))
Proof
Cases THEN RW_TAC list_ss [PERM_def,FILTER]
 THEN Q.EXISTS_TAC `h`
 THEN RW_TAC list_ss []
QED


val lem = Q.prove(
 `!h l1 l2. APPEND (FILTER ($=h) l1) (h::l2)
            = h::APPEND (FILTER ($=h) l1) l2`,
Induct_on `l1`
   THEN RW_TAC list_ss [FILTER]
   THEN PROVE_TAC[]);


Theorem PERM_APPEND:
  !l1 l2. PERM (APPEND l1 l2) (APPEND l2 l1)
Proof
RW_TAC list_ss [PERM_def,FILTER_APPEND_distrib]
  THEN Induct_on `l1`
  THEN RW_TAC list_ss [FILTER,lem]
  THEN PROVE_TAC[]
QED


Theorem CONS_PERM:
 !x L M N. PERM L (APPEND M N)
            ==>
          PERM (x::L) (APPEND M (x::N))
Proof
RW_TAC bool_ss []
 THEN MATCH_MP_TAC PERM_trans1
 THEN PROVE_TAC [PERM_mono, PERM_APPEND, APPEND, PERM_trans1]
QED


Theorem APPEND_PERM_sym:
 !A B C. PERM (APPEND A B) C ==> PERM (APPEND B A) C
Proof
PROVE_TAC [PERM_trans1, PERM_APPEND]
QED

Theorem PERM_split:
 !P l. PERM l (APPEND (FILTER P l) (FILTER ($~ o P) l))
Proof
RW_TAC bool_ss [combinTheory.o_DEF]
 THEN Induct_on `l`
 THEN RW_TAC list_ss [FILTER,PERM_refl]
 THEN PROVE_TAC [APPEND,PERM_mono,CONS_PERM]
QED


(*---------------------------------------------------------------------------
    Directly performs one "sorting step" between 2 non-empty lists that
    are permutations of each other.
 *---------------------------------------------------------------------------*)

val PERM_sort_step = Q.prove
(`!l h t. PERM (h::t) l ==> ?rst. h::rst = FILTER ($=h) l`,
RW_TAC list_ss [PERM_def,FILTER]
  THEN POP_ASSUM (MP_TAC o Q.SPEC`h`)
  THEN RW_TAC bool_ss []
  THEN PROVE_TAC[]);


val LENGTH_APPEND_FILTER = Q.prove
(`!L. LENGTH L = LENGTH (APPEND (FILTER P L) (FILTER ($~ o P) L))`,
Induct
 THEN RW_TAC list_ss [FILTER, combinTheory.o_DEF]
 THEN PROVE_TAC []);

val PERM_step = Q.prove
(`!l h t. PERM (h::t) l
            ==>
          ?u. PERM l (h::u) /\ (LENGTH l = LENGTH (h::u))`,
RW_TAC bool_ss []
  THEN IMP_RES_TAC PERM_sort_step
  THEN Q.EXISTS_TAC `APPEND rst (FILTER ($~ o $= h) l)`
  THEN PROVE_TAC [APPEND, LENGTH_APPEND_FILTER,PERM_split]);


Theorem PERM_LENGTH:
 !l1 l2. PERM l1 l2 ==> (LENGTH l1 = LENGTH l2)
Proof
Induct
  THEN RW_TAC list_ss [PERM_nil]
  THEN IMP_RES_TAC PERM_step
  THEN `PERM l1 u` by PROVE_TAC [PERM_trans1,PERM_CONS_iff]
  THEN RW_TAC list_ss []
QED

