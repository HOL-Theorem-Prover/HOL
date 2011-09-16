structure ind_typeScript =
struct

open HolKernel boolLib Prim_rec Parse simpLib boolSimps
     numTheory prim_recTheory arithmeticTheory InductiveDefinition;

val hol_ss = bool_ss ++ numSimps.old_ARITH_ss ++ numSimps.REDUCE_ss

val lhand = rand o rator
val AND_FORALL_THM = GSYM FORALL_AND_THM;
val GEN_REWRITE_TAC = fn c => fn thl =>
   Rewrite.GEN_REWRITE_TAC c Rewrite.empty_rewrites thl


val _ = new_theory "ind_type";

(* ------------------------------------------------------------------------- *)
(* Abstract left inverses for binary injections (we could construct them...) *)
(* ------------------------------------------------------------------------- *)

val INJ_INVERSE2 = store_thm(
  "INJ_INVERSE2",
  ``!P:'A->'B->'C.
     (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) = (x1 = x2) /\ (y1 = y2)) ==>
     ?X Y. !x y. (X(P x y) = x) /\ (Y(P x y) = y)``,
  GEN_TAC THEN DISCH_TAC THEN
  Q.EXISTS_TAC `\z:'C. @x:'A. ?y:'B. P x y = z` THEN
  Q.EXISTS_TAC `\z:'C. @y:'B. ?x:'A. P x y = z` THEN
  REPEAT GEN_TAC THEN ASM_SIMP_TAC hol_ss []);

(* ------------------------------------------------------------------------- *)
(* Define an injective pairing function on ":num".                           *)
(* ------------------------------------------------------------------------- *)

val NUMPAIR = new_definition(
  "NUMPAIR",
  Term`NUMPAIR x y = (2 EXP x) * (2 * y + 1)`);

val NUMPAIR_INJ_LEMMA = store_thm(
  "NUMPAIR_INJ_LEMMA",
  ``!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)``,
  REWRITE_TAC[NUMPAIR] THEN REPEAT(numLib.INDUCT_TAC THEN GEN_TAC) THEN
  ASM_SIMP_TAC hol_ss [EXP, GSYM MULT_ASSOC, EQ_MULT_LCANCEL,
                       NOT_SUC, GSYM NOT_SUC, INV_SUC_EQ] THEN
  TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
  DISCH_THEN(MP_TAC o Q.AP_TERM `EVEN`) THEN
  SIMP_TAC hol_ss [EVEN_MULT, EVEN_ADD]);

val NUMPAIR_INJ = store_thm (
  "NUMPAIR_INJ",
  ``!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2) /\ (y1 = y2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP NUMPAIR_INJ_LEMMA) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NUMPAIR] THEN
  SIMP_TAC hol_ss [EQ_MULT_LCANCEL, EQ_ADD_RCANCEL, EXP_EQ_0]);

val NUMPAIR_DEST = Rsyntax.new_specification {
  consts = [{const_name = "NUMFST", fixity = NONE},
            {const_name = "NUMSND", fixity = NONE}],
  name = "NUMPAIR_DEST",
  sat_thm = MATCH_MP INJ_INVERSE2 NUMPAIR_INJ};

(* ------------------------------------------------------------------------- *)
(* Also, an injective map bool->num->num (even easier!)                      *)
(* ------------------------------------------------------------------------- *)

val NUMSUM = new_definition("NUMSUM",
  Term`NUMSUM b x = if b then SUC(2 * x) else 2 * x`);

val NUMSUM_INJ = store_thm(
  "NUMSUM_INJ",
  Term`!b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2) /\ (x1 = x2)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[NUMSUM]) THEN
  DISCH_THEN(fn th => MP_TAC th THEN MP_TAC(Q.AP_TERM `EVEN` th)) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[EVEN, EVEN_DOUBLE] THEN
  SIMP_TAC hol_ss [INV_SUC_EQ, EQ_MULT_LCANCEL]);

val NUMSUM_DEST = Rsyntax.new_specification{
  consts = [{const_name = "NUMLEFT", fixity = NONE},
            {const_name = "NUMRIGHT", fixity = NONE}],
  name = "NUMSUM_DEST",
  sat_thm = MATCH_MP INJ_INVERSE2 NUMSUM_INJ};

(* ------------------------------------------------------------------------- *)
(* Injection num->Z, where Z == num->A->bool.                                *)
(* ------------------------------------------------------------------------- *)

val INJN = new_definition(
  "INJN",
  Term`INJN (m:num) = \(n:num) (a:'a). n = m`);

val INJN_INJ = store_thm (
  "INJN_INJ",
  ``!n1 n2. (INJN n1 :num->'a->bool = INJN n2) = (n1 = n2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o C Q.AP_THM `n1:num` o REWRITE_RULE[INJN]) THEN
  DISCH_THEN(MP_TAC o C Q.AP_THM `a:'a`) THEN SIMP_TAC bool_ss []);

(* ------------------------------------------------------------------------- *)
(* Injection A->Z, where Z == num->A->bool.                                  *)
(* ------------------------------------------------------------------------- *)

val INJA = new_definition(
  "INJA",
  Term`INJA (a:'a) = \(n:num) b. b = a`);

val INJA_INJ = store_thm(
  "INJA_INJ",
  ``!a1 a2. (INJA a1 = INJA a2) = (a1:'a = a2)``,
  REPEAT GEN_TAC THEN SIMP_TAC bool_ss [INJA, FUN_EQ_THM] THEN
  EQ_TAC THENL [
    DISCH_THEN(MP_TAC o Q.SPEC `a1:'a`) THEN REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Injection (num->Z)->Z, where Z == num->A->bool.                           *)
(* ------------------------------------------------------------------------- *)

val INJF = new_definition(
  "INJF",
  Term`INJF (f:num->(num->'a->bool)) = \n. f (NUMFST n) (NUMSND n)`);

val INJF_INJ = store_thm(
  "INJF_INJ",
  ``!f1 f2. (INJF f1 :num->'a->bool = INJF f2) = (f1 = f2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY Q.X_GEN_TAC [`n:num`, `m:num`, `a:'a`] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[INJF]) THEN
  DISCH_THEN(MP_TAC o C Q.AP_THM `a:'a` o C Q.AP_THM `NUMPAIR n m`) THEN
  SIMP_TAC bool_ss [NUMPAIR_DEST]);

(* ------------------------------------------------------------------------- *)
(* Injection Z->Z->Z, where Z == num->A->bool.                               *)
(* ------------------------------------------------------------------------- *)

val INJP = new_definition(
  "INJP",
  Term`INJP f1 f2:num->'a->bool =
        \n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a`);

val INJP_INJ = store_thm(
  "INJP_INJ",
  Term`!(f1:num->'a->bool) f1' f2 f2'.
        (INJP f1 f2 = INJP f1' f2') = (f1 = f1') /\ (f2 = f2')`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  SIMP_TAC bool_ss [AND_FORALL_THM] THEN
  Q.X_GEN_TAC `n:num` THEN POP_ASSUM(MP_TAC o REWRITE_RULE[INJP]) THEN
  DISCH_THEN(MP_TAC o GEN ``b:bool`` o C Q.AP_THM `NUMSUM b n`) THEN
  DISCH_THEN(fn th => MP_TAC(Q.SPEC `T` th) THEN MP_TAC(Q.SPEC `F` th)) THEN
  SIMP_TAC (bool_ss ++ ETA_ss) [NUMSUM_DEST]);

(* ------------------------------------------------------------------------- *)
(* Now, set up "constructor" and "bottom" element.                           *)
(* ------------------------------------------------------------------------- *)

val ZCONSTR = new_definition(
  "ZCONSTR",
  ``ZCONSTR c i r :num->'a->bool =
       INJP (INJN (SUC c)) (INJP (INJA i) (INJF r))``);

val ZBOT = new_definition(
  "ZBOT",
  Term`ZBOT = INJP (INJN 0) (@z:num->'a->bool. T)`);

val ZCONSTR_ZBOT = store_thm(
  "ZCONSTR_ZBOT",
  Term`!c i r. ~(ZCONSTR c i r :num->'a->bool = ZBOT)`,
  REWRITE_TAC[ZCONSTR, ZBOT, INJP_INJ, INJN_INJ, NOT_SUC]);

(* ------------------------------------------------------------------------- *)
(* Carve out an inductively defined set.                                     *)
(* ------------------------------------------------------------------------- *)

val (ZRECSPACE_RULES,ZRECSPACE_INDUCT,ZRECSPACE_CASES) =
  IndDefLib.Hol_reln
   `ZRECSPACE (ZBOT:num->'a->bool) /\
    (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r))`;

local fun new_basic_type_definition tyname (mkname, destname) thm =
       let val (pred, witness) = dest_comb(concl thm)
           val predty = type_of pred
           val dom_ty = #1 (dom_rng predty)
           val x = mk_var("x", dom_ty)
           val witness_exists = EXISTS
              (mk_exists(x, mk_comb(pred, x)),witness) thm
           val tyax = new_type_definition(tyname,witness_exists)
           val (mk_dest, dest_mk) = CONJ_PAIR(define_new_type_bijections
               {name=(tyname^"_repfns"), ABS=mkname, REP=destname, tyax=tyax})
       in
         (SPEC_ALL mk_dest, SPEC_ALL dest_mk)
       end
in
val recspace_tydef =
  new_basic_type_definition "recspace"
      ("mk_rec","dest_rec") (CONJUNCT1 ZRECSPACE_RULES)
end;

(* ------------------------------------------------------------------------- *)
(* Define lifted constructors.                                               *)
(* ------------------------------------------------------------------------- *)

val BOTTOM = new_definition(
  "BOTTOM",
  Term`BOTTOM = mk_rec (ZBOT:num->'a->bool)`);

val CONSTR = new_definition(
  "CONSTR",
  Term`CONSTR c i r : 'a recspace = mk_rec (ZCONSTR c i (\n. dest_rec(r n)))`);

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

val MK_REC_INJ = store_thm(
  "MK_REC_INJ",
  ``!x y. (mk_rec x :'a recspace = mk_rec y)
         ==> (ZRECSPACE x /\ ZRECSPACE y ==> (x = y))``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[snd recspace_tydef] THEN
  DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[]);

val DEST_REC_INJ = store_thm(
  "DEST_REC_INJ",
  ``!x y. (dest_rec x = dest_rec y) = (x:'a recspace = y)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o Q.AP_TERM `mk_rec:(num->'a->bool)->'a recspace`) THEN
  REWRITE_TAC[fst recspace_tydef]);

(* ------------------------------------------------------------------------- *)
(* Show that the set is freely inductively generated.                        *)
(* ------------------------------------------------------------------------- *)

val CONSTR_BOT = store_thm(
  "CONSTR_BOT",
  ``!c i r. ~(CONSTR c i r :'a recspace = BOTTOM)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSTR, BOTTOM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MK_REC_INJ) THEN
  REWRITE_TAC[ZCONSTR_ZBOT, ZRECSPACE_RULES] THEN
  MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES) THEN
  SIMP_TAC bool_ss [fst recspace_tydef, snd recspace_tydef]);

val CONSTR_INJ = store_thm(
  "CONSTR_INJ",
  ``!c1 i1 r1 c2 i2 r2. (CONSTR c1 i1 r1 :'a recspace = CONSTR c2 i2 r2) =
                        (c1 = c2) /\ (i1 = i2) /\ (r1 = r2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[CONSTR]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MK_REC_INJ) THEN
  W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 lhand o snd) THENL [
    CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES) THEN
    SIMP_TAC bool_ss [fst recspace_tydef, snd recspace_tydef],
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ZCONSTR] THEN
    REWRITE_TAC[INJP_INJ, INJN_INJ, INJF_INJ, INJA_INJ] THEN
    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN
    REWRITE_TAC[INV_SUC_EQ, DEST_REC_INJ]
  ]);

val CONSTR_IND = store_thm(
  "CONSTR_IND",
  ``!P. P(BOTTOM) /\
        (!c i r. (!n. P(r n)) ==> P(CONSTR c i r)) ==>
        !x:'a recspace. P(x)``,
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPEC `\z:num->'a->bool. ZRECSPACE(z) /\ P(mk_rec z)`
         ZRECSPACE_INDUCT) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ZRECSPACE_RULES, GSYM BOTTOM] THEN
  W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 lhand o snd) THENL [
    REPEAT GEN_TAC THEN SIMP_TAC bool_ss [FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THENL [
      MATCH_MP_TAC(CONJUNCT2 ZRECSPACE_RULES) THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM (fn implhs =>
        FIRST_ASSUM (fn imp => (MP_TAC (HO_MATCH_MP imp implhs)))) THEN
      REWRITE_TAC[CONSTR] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[snd recspace_tydef]) THEN
      ASM_SIMP_TAC (bool_ss ++ ETA_ss) []
    ],
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o Q.SPEC `dest_rec (x:'a recspace)`) THEN
    REWRITE_TAC[fst recspace_tydef] THEN
    REWRITE_TAC[tautLib.TAUT_PROVE ``(a ==> a /\ b) = (a ==> b)``] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[fst recspace_tydef, snd recspace_tydef]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Now prove the recursion theorem (this subcase is all we need).            *)
(* ------------------------------------------------------------------------- *)

val CONSTR_REC = store_thm(
  "CONSTR_REC",
  ``!Fn:num->'a->(num->'a recspace)->(num->'b)->'b.
      ?f. (!c i r. f (CONSTR c i r) = Fn c i r (\n. f (r n)))``,
  REPEAT STRIP_TAC THEN
  (MP_TAC o prove_nonschematic_inductive_relations_exist bool_monoset)
    ``(Z:'a recspace->'b->bool) BOTTOM b /\
     (!c i r y. (!n. Z (r n) (y n)) ==> Z (CONSTR c i r) (Fn c i r y))`` THEN
  DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  Q.SUBGOAL_THEN `!x. ?!y. (Z:'a recspace->'b->bool) x y` MP_TAC THENL [
    W(MP_TAC o HO_PART_MATCH rand CONSTR_IND o snd) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THENL [
      FIRST_ASSUM
        (fn t => GEN_REWRITE_TAC BINDER_CONV [GSYM t]) THEN
      REWRITE_TAC[GSYM CONSTR_BOT, EXISTS_UNIQUE_REFL],
      DISCH_THEN(MP_TAC o SIMP_RULE bool_ss [EXISTS_UNIQUE_THM,FORALL_AND_THM])
      THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(MP_TAC o SIMP_RULE bool_ss [SKOLEM_THM]) THEN
      DISCH_THEN(Q.X_CHOOSE_THEN `y:num->'b` ASSUME_TAC) THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      FIRST_ASSUM(fn th => CHANGED_TAC(ONCE_REWRITE_TAC[GSYM th])) THEN
      CONJ_TAC THENL [
        Q.EXISTS_TAC
           `(Fn:num->'a->(num->'a recspace)->(num->'b)->'b) c i r y` THEN
        REWRITE_TAC[CONSTR_BOT, CONSTR_INJ, GSYM CONJ_ASSOC] THEN
        SIMP_TAC hol_ss [RIGHT_EXISTS_AND_THM] THEN
        Q.EXISTS_TAC `y:num->'b` THEN ASM_REWRITE_TAC[],
        REWRITE_TAC[CONSTR_BOT, CONSTR_INJ, GSYM CONJ_ASSOC] THEN
        SIMP_TAC hol_ss [RIGHT_EXISTS_AND_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT AP_TERM_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
        Q.X_GEN_TAC `w:num` THEN FIRST_ASSUM MATCH_MP_TAC THEN
        Q.EXISTS_TAC `w` THEN ASM_REWRITE_TAC[]
      ]
    ],
    REWRITE_TAC[UNIQUE_SKOLEM_ALT] THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `fn:'a recspace->'b` (ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `fn:'a recspace->'b` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
    FIRST_ASSUM(fn th => GEN_REWRITE_TAC I [GSYM th]) THEN
    SIMP_TAC bool_ss []
  ]);

(* ------------------------------------------------------------------------- *)
(* The following is useful for coding up functions casewise.                 *)
(* ------------------------------------------------------------------------- *)

val FCONS = new_recursive_definition {
  rec_axiom = num_Axiom,
  name = "FCONS",
  def = ``(!a f. FCONS (a:'a) f 0 = a) /\
          (!a f n. FCONS (a:'a) f (SUC n) = f n)``};

val FCONS_UNDO = prove(
  ``!f:num->'a. f = FCONS (f 0) (f o SUC)``,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  numLib.INDUCT_TAC THEN REWRITE_TAC[FCONS, combinTheory.o_THM]);

val FNIL = new_definition("FNIL", ``FNIL (n:num) = (ARB:'a)``);

(*---------------------------------------------------------------------------*)
(* Destructor-style FCONS equation                                           *)
(*---------------------------------------------------------------------------*)

val FCONS_DEST = Q.store_thm
("FCONS_DEST",
 `FCONS a f n = if n = 0 then a else f (n-1)`,
 BasicProvers.Cases_on `n` THEN ASM_SIMP_TAC numLib.arith_ss [FCONS]);

(* ------------------------------------------------------------------------- *)
(* Convenient definitions for type isomorphism.                              *)
(* ------------------------------------------------------------------------- *)

val ISO = new_definition(
  "ISO",
  Term`ISO (f:'a->'b) (g:'b->'a) = (!x. f(g x) = x) /\ (!y. g(f y) = y)`);

(* ------------------------------------------------------------------------- *)
(* Composition theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

val ISO_REFL = store_thm(
  "ISO_REFL",
  Term`ISO (\x:'a. x) (\x. x)`,
  SIMP_TAC bool_ss [ISO]);

open mesonLib
val ISO_FUN = store_thm(
  "ISO_FUN",
  Term`ISO (f:'a->'c) f' /\ ISO (g:'b->'d) g' ==>
       ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a)))`,
  REWRITE_TAC [ISO] THEN SIMP_TAC bool_ss [ISO, FUN_EQ_THM]);
  (* bug in the simplifier requires first rewrite to be performed *)

(* ------------------------------------------------------------------------- *)
(* The use we make of isomorphism when finished.                             *)
(* ------------------------------------------------------------------------- *)

val ISO_USAGE = store_thm(
  "ISO_USAGE",
  Term`ISO f g ==>
         (!P. (!x. P x) = (!x. P(g x))) /\
         (!P. (?x. P x) = (?x. P(g x))) /\
         (!a b. (a = g b) = (f a = b))`,
  SIMP_TAC bool_ss [ISO, FUN_EQ_THM] THEN MESON_TAC[]);

(* ----------------------------------------------------------------------
    Remove constants from top-level name-space
   ---------------------------------------------------------------------- *)

val _ = app (fn s => remove_ovl_mapping s {Name = s, Thy = "ind_type"})
            ["NUMPAIR", "NUMSUM", "INJN", "INJA", "INJF", "INJP",
             "FCONS", "ZCONSTR", "ZBOT", "BOTTOM", "CONSTR", "FNIL", "ISO"]

local open OpenTheoryMap in
  val ns = ["HOL4","Datatype"]
  fun c x = OpenTheory_const_name{const={Thy="ind_type",Name=x},name=(ns,x)}
  val _ = OpenTheory_tyop_name{tyop={Thy="ind_type",Tyop="recspace"},name=(ns,"recspace")}
  val _ = c "CONSTR"
  val _ = c "FCONS"
  val _ = c "FNIL"
  val _ = c "BOTTOM"
end

val _ = export_theory();

end;
