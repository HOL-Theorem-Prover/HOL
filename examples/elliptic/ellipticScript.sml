(* ========================================================================= *)
(* Create "ellipticTheory" setting up the theory of elliptic curves          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
val () = loadPath := [] @ !loadPath;
val () = app load
  ["Algebra",
   "bossLib", "metisLib", "res_quanTools",
   "optionTheory", "listTheory",
   "arithmeticTheory", "dividesTheory", "gcdTheory",
   "pred_setTheory", "pred_setSyntax",
  "primalityTools", "fieldTools"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib res_quanTools;
open optionTheory listTheory arithmeticTheory dividesTheory gcdTheory;
open pred_setTheory;
open primalityTools;
open groupTheory groupTools fieldTheory fieldTools;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "elliptic".                                     *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "elliptic";

val ERR = mk_HOL_ERR "elliptic";
val Bug = mlibUseful.Bug;
val Error = ERR "";

val Bug = fn s => (print ("\n\nBUG: " ^ s ^ "\n\n"); Bug s);

(* ------------------------------------------------------------------------- *)
(* Sort out the parser.                                                      *)
(* ------------------------------------------------------------------------- *)

val () = Parse.add_infix ("/", 600, HOLgrammars.LEFT);

(* ------------------------------------------------------------------------- *)
(* Show oracle tags.                                                         *)
(* ------------------------------------------------------------------------- *)

val () = show_tags := true;

(* ------------------------------------------------------------------------- *)
(* The subtype context.                                                      *)
(* ------------------------------------------------------------------------- *)

val context = field_context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = Tactical.prove;
(***
fun bool_compare (true,false) = LESS
  | bool_compare (false,true) = GREATER
  | bool_compare _ = EQUAL;

fun trace_conv name conv tm =
    let
      val th = conv tm
      val () = (print (name ^ ": "); print_thm th; print "\n")
    in
      th
    end
    handle e as HOL_ERR _ =>
      (print (name ^ ": "); print_term tm; print " --> HOL_ERR\n"; raise e)

fun trans_conv c th =
    let
      val (_,tm) = dest_eq (concl th)
      val th' = c tm
    in
      TRANS th th'
    end;
***)
val norm_rule =
    SIMP_RULE (simpLib.++ (pureSimps.pure_ss, resq_SS))
      [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
       AND_IMP_INTRO, GSYM CONJ_ASSOC];

fun match_tac th =
    let
      val th = norm_rule th
      val (_,tm) = strip_forall (concl th)
    in
      (if is_imp tm then MATCH_MP_TAC else MATCH_ACCEPT_TAC) th
    end;
(***
val clean_assumptions =
    let
      fun eq x y = aconv (concl x) (concl y)
    in
      POP_ASSUM_LIST (STRIP_ASSUME_TAC o LIST_CONJ o rev o op_mk_set eq)
    end;

fun flexible_solver solver cond =
    let
      val cond_th = solver cond
      val cond_tm = concl cond_th
    in
      if cond_tm = cond then cond_th
      else if cond_tm = mk_eq (cond,T) then EQT_ELIM cond_th
      else raise Bug "flexible_solver: solver didn't prove condition"
    end;

fun cond_rewr_conv rewr =
    let
      val rewr = SPEC_ALL (norm_rule rewr)
      val rewr_tm = concl rewr
      val (no_cond,eq) =
          case total dest_imp_only rewr_tm of
            NONE => (true,rewr_tm)
          | SOME (_,eq) => (false,eq)
      val pat = lhs eq
    in
      fn solver => fn tm =>
      let
        val sub = match_term pat tm
        val th = INST_TY_TERM sub rewr
      in
        if no_cond then th
        else MP th (flexible_solver solver (rand (rator (concl th))))
      end
    end;

fun cond_rewrs_conv ths =
    let
      val solver_convs = map cond_rewr_conv ths
      fun mk_conv solver solver_conv = solver_conv solver
    in
      fn solver => FIRST_CONV (map (mk_conv solver) solver_convs)
    end;

fun repeat_rule (rule : rule) th =
    repeat_rule rule (rule th) handle HOL_ERR _ => th;

fun first_rule [] _ = raise ERR "first_rule" ""
  | first_rule ((rule : rule) :: rules) th =
    rule th handle HOL_ERR _ => first_rule rules th;

val dest_in = dest_binop pred_setSyntax.in_tm (ERR "dest_in" "");

val is_in = can dest_in;

val abbrev_tm = ``Abbrev``;

fun dest_abbrev tm =
    let
      val (c,t) = dest_comb tm
      val () = if same_const c abbrev_tm then () else raise ERR "dest_abbrev" ""
    in
      dest_eq t
    end;

val is_abbrev = can dest_abbrev;

fun solver_conv_to_simpset_conv solver_conv =
    let
      val {name : string, key : term, conv : conv -> conv} = solver_conv
      val key = SOME ([] : term list, key)
      and conv = fn c => fn tms : term list => conv (c tms)
      and trace = 2
    in
      {name = name, key = key, conv = conv, trace = trace}
    end;

(* ------------------------------------------------------------------------- *)
(* Helper theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

val THREE = DECIDE ``3 = SUC 2``;

val DIV_THEN_MULT = store_thm
  ("DIV_THEN_MULT",
   ``!p q. SUC q * (p DIV SUC q) <= p``,
   NTAC 2 STRIP_TAC
   ++ Know `?r. p = (p DIV SUC q) * SUC q + r`
   >> (Know `0 < SUC q` >> DECIDE_TAC
       ++ PROVE_TAC [DIVISION])
   ++ STRIP_TAC
   ++ Suff `p = SUC q * (p DIV SUC q) + r`
   >> (POP_ASSUM_LIST (K ALL_TAC) ++ DECIDE_TAC)
   ++ PROVE_TAC [MULT_COMM]);

val MOD_EXP = store_thm
  ("MOD_EXP",
   ``!a n m. 0 < m ==> (((a MOD m) ** n) MOD m = (a ** n) MOD m)``,
   RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [EXP]
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC std_ss [MOD_MOD]);

val MULT_EXP = store_thm
  ("MULT_EXP",
   ``!a b n. (a * b) ** n = (a ** n) * (b ** n)``,
   RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [EXP, EQ_MULT_LCANCEL, GSYM MULT_ASSOC]
   ++ RW_TAC std_ss
        [EXP, ONCE_REWRITE_RULE [MULT_COMM] EQ_MULT_LCANCEL, MULT_ASSOC]
   ++ METIS_TAC [MULT_COMM]);

val EXP_EXP = store_thm
  ("EXP_EXP",
   ``!a b c. (a ** b) ** c = a ** (b * c)``,
   RW_TAC std_ss []
   ++ Induct_on `b`
   ++ RW_TAC std_ss [EXP, MULT, EXP_1]
   ++ RW_TAC std_ss [MULT_EXP, EXP_ADD]
   ++ METIS_TAC [MULT_COMM]);
***)
val EL_ETA = store_thm
  ("EL_ETA",
   ``!l1 l2.
       (LENGTH l1 = LENGTH l2) /\ (!n. n < LENGTH l1 ==> (EL n l1 = EL n l2)) =
       (l1 = l2)``,
   Induct
   >> (Cases ++ RW_TAC arith_ss [LENGTH])
   ++ STRIP_TAC
   ++ Cases
   ++ RW_TAC arith_ss [LENGTH]
   ++ REVERSE (Cases_on `h = h'`)
   >> (RW_TAC std_ss []
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC arith_ss [EL, HD])
   ++ RW_TAC arith_ss []
   ++ Q.PAT_ASSUM `!x. P x` (fn th => REWRITE_TAC [GSYM th])
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `SUC n`)
       ++ RW_TAC arith_ss [EL, TL])
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `n < SUC X` MP_TAC
   ++ Cases_on `n`
   ++ RW_TAC arith_ss [EL, HD, TL]);

val el_append = store_thm
  ("el_append",
   ``!n p q.
       n < LENGTH p + LENGTH q ==>
       (EL n (APPEND p q) =
        if n < LENGTH p then EL n p else EL (n - LENGTH p) q)``,
   Induct
   ++ Cases
   ++ RW_TAC arith_ss [EL, HD, TL, APPEND, LENGTH]);

(* ========================================================================= *)
(* Vector spaces                                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("vector", Type `:'a list`);

val dimension_def = Define `dimension = (LENGTH : 'a vector -> num)`;

val coord_def = Define `coord = (EL : num -> 'a vector -> 'a)`;

val coords_def = Define `coords (v : 'a vector) = { i | i < dimension v }`;

val vector_space_def = Define
  `vector_space (f : 'a field) n =
   { v | (dimension v = n) /\ !i :: coords v. coord i v IN f.carrier }`;

val origin_def = Define
  `(origin (f : 'a field) 0 = []) /\
   (origin (f : 'a field) (SUC n) = field_zero f :: origin f n)`;

val nonorigin_def = Define
  `nonorigin (f : 'a field) =
   { v | v IN vector_space f (dimension v) /\ ~(v = origin f (dimension v)) }`;

val vector_space_origin = store_thm
  ("vector_space_origin",
   ``!f :: Field. !n. origin f n IN vector_space f n``,
   RW_TAC resq_ss
     [vector_space_def, dimension_def, coord_def, GSYM EVERY_EL,
      coords_def, GSPECIFICATION]
   >> (Induct_on `n` ++ RW_TAC std_ss [origin_def, LENGTH])
   ++ Induct_on `n`
   ++ RW_TAC std_ss [origin_def, EVERY_DEF, field_zero_carrier]);

val origin_eq = store_thm
  ("origin_eq",
   ``!f n p.
       (p = origin f n) =
       (dimension p = n) /\ !i :: coords p. coord i p = field_zero f``,
   RW_TAC resq_ss
     [dimension_def, coord_def, GSYM EVERY_EL, coords_def, GSPECIFICATION]
   ++ Q.SPEC_TAC (`p`,`p`)
   ++ (Induct_on `n`
       ++ RW_TAC std_ss [origin_def, LENGTH_NIL, LENGTH_CONS])
   >> (EQ_TAC ++ RW_TAC std_ss [EVERY_DEF])
   ++ EQ_TAC
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [EVERY_DEF]
   ++ METIS_TAC []);

val origin_eq' = store_thm
  ("origin_eq'",
   ``!f n p.
       (origin f n = p) =
       (dimension p = n) /\ !i :: coords p. coord i p = field_zero f``,
   METIS_TAC [origin_eq]);

val nonorigin_alt = store_thm
  ("nonorigin_alt",
   ``!f p.
       p IN nonorigin f =
       EVERY (\x. x IN f.carrier) p /\
       ~(EVERY (\x. x = field_zero f) p)``,
   RW_TAC resq_ss
     [nonorigin_def, GSPECIFICATION, dimension_def, coords_def, coord_def,
      vector_space_def, origin_eq, GSYM EVERY_EL]);

(* ========================================================================= *)
(* Projective geometry                                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

(* Tuned to always be an equivalence relation on type 'a when f is a Field *)
val project_def = Define
  `project (f : 'a field) v1 v2 =
   (v1 = v2) \/
   (v1 IN nonorigin f /\ v2 IN nonorigin f /\
    (dimension v1 = dimension v2) /\
    ?c :: (f.carrier). !i :: coords v1.
      field_mult f c (coord i v1) = coord i v2)`;

(* Must use the primitive GSPEC to get around the set binding heuristic *)
val projective_space_def = Define
  `projective_space (f : 'a field) n =
   GSPEC (\v. (project f v, v IN (vector_space f (n + 1) INTER nonorigin f)))`;

val affine_def = Define `affine f v = project f (v ++ [field_one f])`;

val project_refl = store_thm
  ("project_refl",
   ``!f p. project f p p``,
   RW_TAC std_ss [project_def]);

val project_refl' = store_thm
  ("project_refl'",
   ``!f p q. (p = q) ==> project f p q``,
   METIS_TAC [project_refl]);

val project_sym = store_thm
  ("project_sym",
   ``!f :: Field. !p1 p2. project f p1 p2 ==> project f p2 p1``,
   SIMP_TAC resq_ss [project_def, nonorigin_def, vector_space_def]
   ++ RW_TAC std_ss [GSPECIFICATION, coords_def, dimension_def, coord_def]
   ++ DISJ2_TAC
   ++ RW_TAC std_ss []
   ++ Know `c IN field_nonzero f`
   >> (RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ STRIP_TAC
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `~(p2 = X)` MP_TAC
       ++ RW_TAC resq_ss
            [origin_eq, EVERY_EL, dimension_def, coords_def,
             coord_def, GSPECIFICATION]
       ++ Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `i`)
       ++ RW_TAC std_ss [field_mult_lzero])
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `field_inv f c`
   ++ RW_TAC alg_ss []
   ++ match_tac field_mult_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `c`
   ++ RW_TAC alg_ss []
   ++ Q.PAT_ASSUM `!i. i < LENGTH p2 ==> X` (MP_TAC o Q.SPEC `i`)
   ++ RW_TAC alg_ss []);

val project_trans = store_thm
  ("project_trans",
   ``!f :: Field. !p1 p2 p3.
       project f p1 p2 /\ project f p2 p3 ==> project f p1 p3``,
   SIMP_TAC resq_ss [project_def, nonorigin_def, vector_space_def]
   ++ RW_TAC std_ss [GSPECIFICATION, coords_def, dimension_def, coord_def]
   << [METIS_TAC [],
       METIS_TAC [],
       DISJ2_TAC
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `field_mult f c' c`
       ++ RW_TAC std_ss [field_mult_carrier]
       ++ RW_TAC std_ss [field_mult_assoc]]);

val project_eq = store_thm
  ("project_eq",
   ``!f :: Field. !v1 v2.
       ((project f v1 = project f v2) = project f v1 v2)``,
   RW_TAC resq_ss []
   ++ MATCH_MP_TAC EQ_SYM
   ++ Q.SPEC_TAC (`v2`,`v2`)
   ++ Q.SPEC_TAC (`v1`,`v1`)
   ++ SIMP_TAC std_ss [GSYM relationTheory.ALT_equivalence]
   ++ RW_TAC std_ss [relationTheory.equivalence_def]
   << [RW_TAC std_ss [relationTheory.reflexive_def]
       ++ METIS_TAC [project_refl],
       RW_TAC std_ss [relationTheory.symmetric_def]
       ++ METIS_TAC [project_sym],
       RW_TAC std_ss [relationTheory.transitive_def]
       ++ METIS_TAC [project_trans]]);

val affine_eq = store_thm
  ("affine_eq",
   ``!f :: Field. !v1 v2. (affine f v1 = affine f v2) = (v1 = v2)``,
   RW_TAC resq_ss [project_eq, affine_def, project_def, APPEND_11]
   ++ REVERSE EQ_TAC >> RW_TAC std_ss []
   ++ RW_TAC resq_ss
        [dimension_def, coords_def, GSPECIFICATION, nonorigin_alt, coord_def]
   ++ REPEAT (Q.PAT_ASSUM `~(EVERY P L)` (K ALL_TAC))
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [EVERY_APPEND, LENGTH_APPEND, LENGTH, GSYM ADD1, EVERY_DEF]
   ++ RW_TAC std_ss [GSYM EL_ETA]
   ++ Suff `c = field_one f`
   >> (Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `n`)
       ++ RW_TAC arith_ss [el_append]
       ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
       ++ MATCH_MP_TAC EQ_SYM
       ++ match_tac field_mult_lone
       ++ Q.PAT_ASSUM `EVERY P v1` MP_TAC
       ++ RW_TAC std_ss [EVERY_EL])
   ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `LENGTH v1`)
   ++ RW_TAC arith_ss [el_append, LENGTH, EL, HD]
   ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ MATCH_MP_TAC EQ_SYM
   ++ match_tac field_mult_rone
   ++ RW_TAC std_ss []);

(* ========================================================================= *)
(* Elliptic curves                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `curve =
   <| field : 'a field;
      a1 : 'a;
      a2 : 'a;
      a3 : 'a;
      a4 : 'a;
      a6 : 'a |>`;

val curve_accessors = fetch "-" "curve_accessors";

val curve_b2_def = Define
  `curve_b2 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   a1 ** 2 + & 4 * a2`;

val curve_b4_def = Define
  `curve_b4 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $* = field_mult f in
   let a1 = e.a1 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   a1 * a3 + & 2 * a4`;

val curve_b6_def = Define
  `curve_b6 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a3 = e.a3 in
   let a6 = e.a6 in
   a3 ** 2 + & 4 * a6`;

val curve_b8_def = Define
  `curve_b8 e =
   let f = e.field in
   let $& = field_num f in
   let $+ = field_add f in
   let $- = field_sub f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   let a6 = e.a6 in
   a1 ** 2 * a6 + & 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 ** 2 - a4 ** 2`;

val discriminant_def = Define
  `discriminant e =
   let f = e.field in
   let $& = field_num f in
   let $- = field_sub f in
   let $* = field_mult f in
   let $** = field_exp f in
   let b2 = curve_b2 e in
   let b4 = curve_b4 e in
   let b6 = curve_b6 e in
   let b8 = curve_b8 e in
   & 9 * b2 * b4 * b6 - b2 * b2 * b8 - & 8 * b4 ** 3 - & 27 * b6 ** 2`;

val non_singular_def = Define
  `non_singular e = ~(discriminant e = field_zero e.field)`;

val Curve_def = Define
  `Curve =
   { e |
     e.field IN Field /\
     e.a1 IN e.field.carrier /\
     e.a2 IN e.field.carrier /\
     e.a3 IN e.field.carrier /\
     e.a4 IN e.field.carrier /\
     e.a6 IN e.field.carrier /\
     non_singular e }`;

val curve_points_def = Define
  `curve_points e =
   let f = e.field in
   let $+ = field_add f in
   let $* = field_mult f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   let a6 = e.a6 in
   GSPEC (\ (x,y,z).
     (project f [x; y; z],
      [x; y; z] IN nonorigin f /\
      (y ** 2 * z + a1 * x * y * z + a3 * y * z ** 2 =
       x ** 3 + a2 * x ** 2 * z + a4 * x * z ** 2 + a6 * z ** 3)))`;

val curve_zero_def = Define
  `curve_zero e =
   project e.field
     [field_zero e.field; field_one e.field; field_zero e.field]`;

val affine_case_def = Define
  `affine_case e z f p =
   if p = curve_zero e then z
   else @t. ?x y. (p = affine e.field [x; y]) /\ (t = f x y)`;

val curve_neg_def = Define
  `curve_neg e =
   let f = e.field in
   let $~ = field_neg f in
   let $+ = field_add f in
   let $- = field_sub f in
   let $* = field_mult f in
   let a1 = e.a1 in
   let a3 = e.a3 in
   affine_case e (curve_zero e)
     (\x1 y1.
        let x = x1 in
        let y = ~y1 - a1 * x1 - a3 in
        affine f [x; y])`;

val curve_double_def = Define
  `curve_double e =
   let f = e.field in
   let $& = field_num f in
   let $~ = field_neg f in
   let $+ = field_add f in
   let $- = field_sub f in
   let $* = field_mult f in
   let $/ = field_div f in
   let $** = field_exp f in
   let a1 = e.a1 in
   let a2 = e.a2 in
   let a3 = e.a3 in
   let a4 = e.a4 in
   let a6 = e.a6 in
   affine_case e (curve_zero e)
     (\x1 y1.
        let d = & 2 * y1 + a1 * x1 + a3 in
        if d = field_zero f then curve_zero e
        else
          let l = (& 3 * x1 ** 2 + & 2 * a2 * x1 + a4 - a1 * y1) / d in
          let m = (~(x1 ** 3) + a4 * x1 + & 2 * a6 - a3 * y1) / d in
          let x = l ** 2 + a1 * l - a2 - &2 * x1 in
          let y = ~(l + a1) * x - m - a3 in
          affine e.field [x; y])`;

val curve_add_def = Define
  `curve_add e p1 p2 =
   if p1 = p2 then curve_double e p1
   else
     let f = e.field in
     let $& = field_num f in
     let $~ = field_neg f in
     let $+ = field_add f in
     let $- = field_sub f in
     let $* = field_mult f in
     let $/ = field_div f in
     let $** = field_exp f in
     let a1 = e.a1 in
     let a2 = e.a2 in
     let a3 = e.a3 in
     let a4 = e.a4 in
     let a6 = e.a6 in
     affine_case e p2
       (\x1 y1.
          affine_case e p1
            (\x2 y2.
               if x1 = x2 then curve_zero e
               else
                 let d = x2 - x1 in
                 let l = (y2 - y1) / d in
                 let m = (y1 * x2 - y2 * x1) / d in
                 let x = l ** 2 + a1 * l - a2 - x1 - x2 in
                 let y = ~(l + a1) * x - m - a3 in
                 affine e.field [x; y]) p2) p1`;

val curve_mult_def = Define
  `(curve_mult (e : 'a curve) p 0 = curve_zero e) /\
   (curve_mult (e : 'a curve) p (SUC n) = curve_add e p (curve_mult e p n))`;

val curve_group_def = Define
  `curve_group e =
   <| carrier := curve_points e;
      id := curve_zero e;
      inv := curve_neg e;
      mult := curve_add e |>`;

val curve_field = store_thm
  ("curve_field",
   ``!e :: Curve. e.field IN Field``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 curve_field context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_a1_carrier = store_thm
  ("curve_a1_carrier",
   ``!e :: Curve. e.a1 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 curve_a1_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_a2_carrier = store_thm
  ("curve_a2_carrier",
   ``!e :: Curve. e.a2 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 curve_a2_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_a3_carrier = store_thm
  ("curve_a3_carrier",
   ``!e :: Curve. e.a3 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 curve_a3_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_a4_carrier = store_thm
  ("curve_a4_carrier",
   ``!e :: Curve. e.a4 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 curve_a4_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_a6_carrier = store_thm
  ("curve_a6_carrier",
   ``!e :: Curve. e.a6 IN e.field.carrier``,
   RW_TAC resq_ss [Curve_def, GSPECIFICATION]);

val context = subtypeTools.add_reduction2 curve_a6_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_cases = store_thm
  ("curve_cases",
   ``!e :: Curve. !p :: curve_points e.
       (p = curve_zero e) \/
       ?x y :: (e.field.carrier). p = affine e.field [x; y]``,
   RW_TAC resq_ss
     [curve_points_def, curve_zero_def,
      GSPECIFICATION, LET_DEF, affine_def, APPEND]
   ++ POP_ASSUM MP_TAC
   ++ Know `?x1 y1 z1. x = (x1,y1,z1)`
   >> METIS_TAC [pairTheory.ABS_PAIR_THM]
   ++ STRIP_TAC
   ++ RW_TAC alg_ss [project_eq]
   ++ Q.PAT_ASSUM `X IN Y` MP_TAC
   ++ RW_TAC resq_ss
        [nonorigin_def, GSPECIFICATION, coords_def, dimension_def,
         vector_space_def, coord_def, GSYM EVERY_EL, EVERY_DEF]
   ++ Cases_on `z1 = field_zero e.field`
   << [RW_TAC std_ss []
       ++ DISJ1_TAC
       ++ Q.PAT_ASSUM `X = Y` MP_TAC
       ++ RW_TAC alg_ss []
       ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
       ++ RW_TAC resq_ss
            [origin_eq, dimension_def, coords_def, GSPECIFICATION,
             coord_def, GSYM EVERY_EL, EVERY_DEF]
       ++ RW_TAC resq_ss
            [project_def, nonorigin_alt, EVERY_DEF, field_one_carrier,
             field_one_zero, dimension_def, LENGTH]
       ++ DISJ2_TAC
       ++ Know `y1 IN field_nonzero e.field`
       >> RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ RW_TAC alg_ss []
       ++ Q.EXISTS_TAC `field_inv e.field y1`
       ++ RW_TAC alg_ss
            [coords_def, GSPECIFICATION, dimension_def, LENGTH]
       ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))`
       >> DECIDE_TAC
       ++ STRIP_TAC
       ++ RW_TAC bool_ss [EL, HD, TL, coord_def]
       ++ RW_TAC alg_ss [],
       Q.PAT_ASSUM `X = Y` (K ALL_TAC)
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `field_mult e.field (field_inv e.field z1) x1`
       ++ Know `z1 IN field_nonzero e.field`
       >> RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ RW_TAC alg_ss []
       ++ Q.EXISTS_TAC `field_mult e.field (field_inv e.field z1) y1`
       ++ RW_TAC alg_ss []
       ++ RW_TAC resq_ss
            [project_def, nonorigin_alt, EVERY_DEF, dimension_def, LENGTH]
       ++ RW_TAC alg_ss []
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `field_inv e.field z1`
       ++ RW_TAC alg_ss
            [coords_def, dimension_def, LENGTH, coord_def, GSPECIFICATION]
       ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))`
       >> DECIDE_TAC
       ++ STRIP_TAC
       ++ RW_TAC bool_ss [EL, HD, TL, coord_def]
       ++ RW_TAC alg_ss []]);

local
  val case_th =
      CONV_RULE
        (RES_FORALL_CONV THENC
         QUANT_CONV
           (RAND_CONV RES_FORALL_CONV THENC
            RIGHT_IMP_FORALL_CONV THENC
            QUANT_CONV
              (REWR_CONV AND_IMP_INTRO))) curve_cases;

  fun cases_on e p = MP_TAC (SPECL [e,p] case_th);
in
  fun ec_cases_on e p (asl,g) =
      let
        val fvs = free_varsl (g :: asl)
        val e_tm = Parse.parse_in_context fvs e
        and p_tm = Parse.parse_in_context fvs p
      in
        cases_on e_tm p_tm
      end (asl,g);
end;

val curve_distinct = store_thm
  ("curve_distinct",
   ``!e :: Curve. !x y.
       ~(curve_zero e = affine e.field [x; y])``,
   RW_TAC resq_ss
     [affine_case_def, affine_def, Curve_def, GSPECIFICATION,
      curve_zero_def, APPEND, project_eq]
   ++ STRIP_TAC
   ++ FULL_SIMP_TAC resq_ss
        [project_def, field_zero_one, coords_def, GSPECIFICATION,
         dimension_def, coord_def, LENGTH]
   >> (POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [field_zero_one])
   ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `SUC (SUC 0)`)
   ++ RW_TAC arith_ss [EL, HD, TL, field_mult_rzero, field_zero_one]);

val affine_case = store_thm
  ("affine_case",
   ``!e :: Curve. !z f.
       (affine_case e z f (curve_zero e) = z) /\
       !x y. affine_case e z f (affine e.field [x; y]) = f x y``,
   RW_TAC resq_ss
     [affine_case_def, affine_eq, Curve_def, GSPECIFICATION,
      curve_distinct]);

(*
val curve_quadratic = store_thm
  ("curve_quadratic",
   ``!e :: Curve. !x1 y1 y2 :: (e.field.carrier).
       let f = e.field in
       let $~ = field_neg f in
       let $+ = field_add f in
       let $* = field_mult f in
       let a1 = e.a1 in
       let a3 = e.a3 in
       affine [x1; y1] IN curve_points e /\
       affine [x1; y2] IN curve_points e ==>
       (y2 = y1) \/ (y2 = ~(y1 + a1 * x1 + a3))``,
*)

val curve_zero_eq = store_thm
  ("curve_zero_eq",
   ``!e :: Curve. !x y z :: (e.field.carrier).
       (project e.field [x; y; z] = curve_zero e) =
       (x = field_zero e.field) /\
       ~(y = field_zero e.field) /\
       (z = field_zero e.field)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss
        [GSPECIFICATION, curve_zero_def,
         project_eq, project_def, nonorigin_alt, EVERY_DEF, dimension_def,
         LENGTH, field_zero_carrier, field_one_carrier, field_one_zero,
         coords_def, coord_def]
   ++ RW_TAC resq_ss [GSPECIFICATION]
   ++ REVERSE (Cases_on `x = field_zero e.field`)
   >> (RW_TAC std_ss []
       ++ REVERSE (Cases_on `c IN e.field.carrier`)
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC (PROVE [] ``(~c ==> F) ==> c``)
       ++ STRIP_TAC
       ++ Know `~(c = field_zero e.field)`
       >> (STRIP_TAC
           ++ Q.PAT_ASSUM `~X` MP_TAC
           ++ RW_TAC std_ss []
           ++ Q.EXISTS_TAC `SUC 0`
           ++ RW_TAC std_ss [EL, HD, TL]
           ++ RW_TAC alg_ss [])
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~?x. P x` MP_TAC
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC alg_ss [EL, HD, TL])
   ++ REVERSE (Cases_on `z = field_zero e.field`)
   >> (RW_TAC std_ss []
       ++ REVERSE (Cases_on `c IN e.field.carrier`)
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC (PROVE [] ``(~c ==> F) ==> c``)
       ++ STRIP_TAC
       ++ Know `~(c = field_zero e.field)`
       >> (STRIP_TAC
           ++ Q.PAT_ASSUM `~X` MP_TAC
           ++ RW_TAC std_ss []
           ++ Q.EXISTS_TAC `SUC 0`
           ++ RW_TAC std_ss [EL, HD, TL]
           ++ RW_TAC alg_ss [])
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~?x. P x` MP_TAC
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `SUC (SUC 0)`
       ++ RW_TAC alg_ss [EL, HD, TL])
   ++ RW_TAC alg_ss []
   ++ Cases_on `y = field_zero e.field`
   ++ RW_TAC alg_ss []
   ++ DISJ2_TAC
   ++ Know `y IN field_nonzero e.field`
   >> RW_TAC alg_ss [field_nonzero_alt]
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `field_inv e.field y`
   ++ RW_TAC alg_ss []
   ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC alg_ss [EL, HD, TL]);

val curve_zero_eq' = store_thm
  ("curve_zero_eq'",
   ``!e :: Curve. !x y z :: (e.field.carrier).
       (curve_zero e = project e.field [x; y; z]) =
       (x = field_zero e.field) /\
       ~(y = field_zero e.field) /\
       (z = field_zero e.field)``,
   RW_TAC std_ss [curve_zero_eq]);

val curve_neg_optimized = store_thm
  ("curve_neg_optimized",
   ``!e :: Curve. !x1 y1 z1 :: (e.field.carrier).
       project e.field [x1; y1; z1] IN curve_points e ==>
       (curve_neg e (project e.field [x1; y1; z1]) =
        let f = e.field in
        let $~ = field_neg f in
        let $+ = field_add f in
        let $* = field_mult f in
        let a1 = e.a1 in
        let a3 = e.a3 in
        let x = x1 in
        let y = ~(y1 + a1 * x1 + a3 * z1) in
        let z = z1 in
        project f [x; y; z])``,
   RW_TAC resq_ss [LET_DEF, curve_neg_def]
   ++ Know `e IN Curve` >> RW_TAC std_ss []
   ++ REWRITE_TAC [Curve_def]
   ++ RW_TAC std_ss [GSPECIFICATION]
   ++ ec_cases_on `e` `project e.field [x1; y1; z1]`
   ++ RW_TAC resq_ss []
   >> (RW_TAC std_ss [affine_case]
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [curve_zero_eq]
       ++ RW_TAC std_ss [field_mult_rzero, field_add_rzero]
       ++ RW_TAC std_ss [curve_zero_eq', field_neg_carrier]
       ++ RW_TAC std_ss [field_neg_eq_swap, field_neg_zero])
   ++ RW_TAC std_ss [affine_case]
   ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
   ++ ASM_SIMP_TAC resq_ss [affine_def, APPEND, project_eq]
   ++ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [project_def]))
   ++ RW_TAC resq_ss
        [dimension_def, coords_def, coord_def, LENGTH, GSPECIFICATION]
   >> (MATCH_MP_TAC project_refl'
       ++ RW_TAC std_ss []
       ++ RW_TAC alg_ss' [])
   ++ Know `~(c = field_zero e.field)`
   >> (STRIP_TAC
       ++ Q.PAT_ASSUM `X IN nonorigin Y` MP_TAC
       ++ Q.PAT_ASSUM `!i. P i`
            (fn th => MP_TAC (Q.SPEC `0` th)
                      ++ MP_TAC (Q.SPEC `SUC 0` th)
                      ++ MP_TAC (Q.SPEC `SUC (SUC 0)` th))
       ++ RW_TAC std_ss
            [EL, HD, TL, nonorigin_alt, field_mult_lzero, field_one_carrier,
             EVERY_DEF])
   ++ STRIP_TAC
   ++ Know `~(z1 = field_zero e.field)`
   >> (STRIP_TAC
       ++ Q.PAT_ASSUM `!i. P i` (MP_TAC o Q.SPEC `SUC (SUC 0)`)
       ++ RW_TAC std_ss
            [EL, HD, TL, field_entire, field_one_carrier, field_one_zero])
   ++ STRIP_TAC
   ++ RW_TAC resq_ss
        [project_def, GSPECIFICATION, dimension_def, LENGTH, nonorigin_alt,
         EVERY_DEF, coords_def, coord_def, field_one_carrier, field_one_zero]
   ++ DISJ2_TAC
   ++ CONJ_TAC >> RW_TAC alg_ss []
   ++ CONJ_TAC >> RW_TAC alg_ss []
   ++ Q.EXISTS_TAC `z1`
   ++ RW_TAC std_ss [field_mult_carrier]
   ++ Q.PAT_ASSUM `!i. P i` (fn th => MP_TAC (Q.SPEC `0` th)
                                      ++ MP_TAC (Q.SPEC `SUC 0` th)
                                      ++ MP_TAC (Q.SPEC `SUC (SUC 0)` th))
   ++ RW_TAC std_ss [EL, HD, TL]
   ++ Know `(i = 0) \/ (i = SUC 0) \/ (i = SUC (SUC 0))` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC std_ss [EL, HD, TL, field_mult_rone]
   ++ RW_TAC alg_ss' [field_distrib]);

val curve_affine = store_thm
  ("curve_affine",
   ``!e :: Curve. !x y :: (e.field.carrier).
       affine e.field [x; y] IN curve_points e =
       let f = e.field in
       let $+ = field_add f in
       let $* = field_mult f in
       let $** = field_exp f in
       let a1 = e.a1 in
       let a2 = e.a2 in
       let a3 = e.a3 in
       let a4 = e.a4 in
       let a6 = e.a6 in
       y ** 2 + a1 * x * y + a3 * y =
       x ** 3 + a2 * x ** 2 + a4 * x + a6``,
   RW_TAC resq_ss
     [curve_points_def, LET_DEF, affine_def, GSPECIFICATION, APPEND]
   ++ REVERSE EQ_TAC
   >> (RW_TAC alg_ss []
       ++ Q.EXISTS_TAC `(x, y, field_one e.field)`
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC alg_ss [nonorigin_alt, EVERY_DEF])
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Know `?x1 y1 z1. x' = (x1,y1,z1)`
   >> METIS_TAC [pairTheory.ABS_PAIR_THM]
   ++ STRIP_TAC
   ++ RW_TAC alg_ss []
   ++ Q.PAT_ASSUM `X IN Y` MP_TAC
   ++ RW_TAC std_ss [nonorigin_alt]
   ++ Q.PAT_ASSUM `EVERY P L` MP_TAC
   ++ RW_TAC std_ss [EVERY_DEF]
   ++ Q.PAT_ASSUM `project X Y = Z` (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
   ++ RW_TAC alg_ss [project_eq, project_def]
   >> (Q.PAT_ASSUM `X = Y` MP_TAC
       ++ RW_TAC alg_ss' [])
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC resq_ss
        [dimension_def, coords_def, coord_def, LENGTH, GSPECIFICATION]
   ++ Q.PAT_ASSUM `!i. P i` (fn th => MP_TAC (Q.SPEC `0` th)
                                      ++ MP_TAC (Q.SPEC `SUC 0` th)
                                      ++ MP_TAC (Q.SPEC `SUC (SUC 0)` th))
   ++ RW_TAC std_ss [EL, HD, TL]
   ++ Know `c IN field_nonzero e.field`
   >> (RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `X = field_one Y` MP_TAC
       ++ RW_TAC alg_ss [])
   ++ Know `z1 IN field_nonzero e.field`
   >> (RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `X = field_one Y` MP_TAC
       ++ RW_TAC alg_ss [])
   ++ RW_TAC std_ss []
   ++ Know `c = field_inv e.field z1`
   >> (match_tac field_mult_rcancel_imp
       ++ Q.EXISTS_TAC `e.field`
       ++ Q.EXISTS_TAC `z1`
       ++ ASM_REWRITE_TAC []
       ++ RW_TAC alg_ss [])
   ++ RW_TAC std_ss []
   ++ match_tac field_mult_lcancel_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ Q.EXISTS_TAC `field_exp e.field z1 3`
   ++ REPEAT (Q.PAT_ASSUM `X = Y` MP_TAC)
   ++ RW_TAC alg_ss' [field_distrib]);

val curve_affine_reduce_3 = store_thm
  ("curve_affine_reduce_3",
   ``!e :: Curve. !x y :: (e.field.carrier).
       affine e.field [x; y] IN curve_points e =
       (field_exp e.field x 3 =
        field_add e.field
          (field_neg e.field e.a6)
          (field_add e.field
            (field_mult e.field e.a3 y)
            (field_add e.field
              (field_exp e.field y 2)
              (field_add e.field
                (field_neg e.field (field_mult e.field e.a4 x))
                (field_add e.field
                  (field_mult e.field e.a1 (field_mult e.field x y))
                  (field_neg e.field
                    (field_mult e.field e.a2 (field_exp e.field x 2))))))))``,
   RW_TAC resq_ss []
   ++ CONV_TAC (RAND_CONV (REWR_CONV EQ_SYM_EQ))
   ++ RW_TAC alg_ss [curve_affine, LET_DEF]
   ++ RW_TAC alg_ss' []);

local
  val exp_tm = ``field_exp e.field (x : 'a)``;

  val context_tms = strip_conj
      ``e IN Curve /\ (x : 'a) IN e.field.carrier /\ y IN e.field.carrier``;

  val affine_tm = ``affine e.field [(x : 'a); y] IN curve_points e``;

  val context_ths = map ASSUME context_tms;

  val affine = ASSUME affine_tm;

  val reduce_3_eq =
      (repeat UNDISCH o SPEC_ALL)
        (CONV_RULE
           (REDEPTH_CONV (RES_FORALL_CONV ORELSEC
                          HO_REWR_CONV (GSYM RIGHT_FORALL_IMP_THM) ORELSEC
                          REWR_CONV (GSYM AND_IMP_INTRO)))
         curve_affine_reduce_3);

  val reduce_3 = EQ_MP reduce_3_eq affine;

  fun reduce_n 3 = [reduce_3]
    | reduce_n n =
      let
        val reduce_ths = reduce_n (n - 1)
        val n1_tm = numLib.term_of_int (n - 1)
        val suc_th = reduceLib.SUC_CONV (numSyntax.mk_suc n1_tm)
        val reduce_tm = mk_comb (exp_tm, numLib.term_of_int n)
        val reduce_th =
            (RAND_CONV (REWR_CONV (SYM suc_th)) THENC
             REWR_CONV (CONJUNCT2 field_exp_def) THENC
             RAND_CONV (REWR_CONV (hd reduce_ths)) THENC
             with_flag (ORACLE_field_poly,true)
             (Count.apply
                (SIMP_CONV (field_poly_ss context reduce_ths) context_ths)))
              reduce_tm
      in
        reduce_th :: reduce_ths
      end;

  val weakening_th = PROVE [] ``(a ==> b) ==> (a = a /\ b)``;
in
  fun curve_affine_reduce_n n =
      let
        val th = DISCH affine_tm (LIST_CONJ (tl (rev (reduce_n n))))
        val th = MATCH_MP weakening_th th
        val th = CONV_RULE (RAND_CONV (LAND_CONV (K reduce_3_eq))) th
        val th = foldl (uncurry DISCH) th (rev context_tms)
      in
        th
      end;
end;

val curve_affine_reduce = save_thm
  ("curve_affine_reduce",
   with_flag (subtypeTools.ORACLE,true)
   (Count.apply curve_affine_reduce_n) 12);

val curve_zero_carrier = store_thm
  ("curve_zero_carrier",
   ``!e :: Curve. curve_zero e IN curve_points e``,
   RW_TAC resq_ss [curve_zero_def, curve_points_def, LET_DEF, GSPECIFICATION]
   ++ Q.EXISTS_TAC `(field_zero e.field, field_one e.field, field_zero e.field)`
   ++ RW_TAC alg_ss [nonorigin_alt, EVERY_DEF]);

val context = subtypeTools.add_reduction2 curve_zero_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_neg_carrier = Count.apply store_thm
  ("curve_neg_carrier",
   ``!e :: Curve. !p :: curve_points e. curve_neg e p IN curve_points e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_neg_def, LET_DEF]
   ++ RW_TAC alg_ss [affine_case]
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ ASM_SIMP_TAC alg_ss [curve_affine, LET_DEF]
   ++ RW_TAC alg_ss' [field_distrib, field_binomial_2]);

val context = subtypeTools.add_reduction2 curve_neg_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_double_carrier = Count.apply store_thm
  ("curve_double_carrier",
   ``!e :: Curve. !p :: curve_points e. curve_double e p IN curve_points e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_double_def]
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss []
   ++ RW_TAC alg_ss [affine_case]
   ++ RW_TAC alg_ss []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC alg_ss [field_nonzero_eq, curve_affine, LET_DEF]
   ++ match_tac field_sub_eq_zero_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_TAC `x'`
   ++ Q.UNABBREV_TAC `y'`
   ++ Q.UNABBREV_TAC `l`
   ++ Q.UNABBREV_TAC `m`
   ++ Count.apply (RW_TAC (field_div_elim_ss context) [])
   ++ Q.UNABBREV_TAC `d`
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ ASM_SIMP_TAC alg_ss [curve_affine_reduce]
   ++ with_flag (ORACLE_field_poly,true)
      (with_flag (subtypeTools.ORACLE,true)
       (Count.apply (ASM_SIMP_TAC (field_poly_basis_ss context) []))));

val context = subtypeTools.add_reduction2 curve_double_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_add_carrier = Count.apply store_thm
  ("curve_add_carrier",
   ``!e :: Curve. !p q :: curve_points e. curve_add e p q IN curve_points e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ ec_cases_on `e` `q`
   ++ RW_TAC resq_ss [curve_add_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC alg_ss [affine_case]
   ++ RW_TAC alg_ss []
   ++ Know `~(d = field_zero e.field)`
   >> (Q.UNABBREV_TAC `d`
       ++ RW_TAC alg_ss [field_sub_eq_zero])
   ++ RW_TAC alg_ss [field_nonzero_eq, curve_affine, LET_DEF]
   ++ match_tac field_sub_eq_zero_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_TAC `x''`
   ++ Q.UNABBREV_TAC `y''`
   ++ Q.UNABBREV_TAC `l`
   ++ Q.UNABBREV_TAC `m`
   ++ Count.apply (RW_TAC (field_div_elim_ss context) [])
   ++ Q.UNABBREV_TAC `d`
   ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ Q.PAT_ASSUM `affine X Y IN Z` MP_TAC
   ++ ASM_SIMP_TAC alg_ss [curve_affine_reduce]
   ++ SIMP_TAC bool_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC]
   ++ with_flag (ORACLE_field_poly,true)
      (with_flag (subtypeTools.ORACLE,true)
       (Count.apply (ASM_SIMP_TAC (field_poly_basis_ss context) []))));

val context = subtypeTools.add_reduction2 curve_add_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_double_zero = store_thm
  ("curve_double_zero",
   ``!e :: Curve. curve_double e (curve_zero e) = curve_zero e``,
   RW_TAC resq_ss []
   ++ RW_TAC resq_ss [curve_double_def]
   ++ normalForms.REMOVE_ABBR_TAC
   ++ RW_TAC std_ss []
   ++ RW_TAC alg_ss [affine_case]);

val context = subtypeTools.add_rewrite2 curve_double_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_add_lzero = store_thm
  ("curve_add_lzero",
   ``!e :: Curve. !p :: curve_points e. curve_add e (curve_zero e) p = p``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_add_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC alg_ss [affine_case]);

val context = subtypeTools.add_rewrite2 curve_add_lzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_add_lneg = store_thm
  ("curve_add_lneg",
   ``!e :: Curve. !p :: curve_points e.
       curve_add e (curve_neg e p) p = curve_zero e``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ RW_TAC resq_ss [curve_add_def, curve_neg_def, LET_DEF]
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_ALL_TAC
   ++ RW_TAC alg_ss [affine_case]
   ++ Q.PAT_ASSUM `X = Y` MP_TAC
   ++ RW_TAC alg_ss [affine_case, affine_eq]
   ++ RW_TAC alg_ss [curve_double_def, LET_DEF, affine_case, curve_distinct]
   ++ Q.PAT_ASSUM `X = Y` MP_TAC
   ++ PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ]
   ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
   ++ RW_TAC alg_ss' []);

val context = subtypeTools.add_rewrite2 curve_add_lneg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_add_comm = Count.apply store_thm
  ("curve_add_comm",
   ``!e :: Curve. !p q :: curve_points e. curve_add e p q = curve_add e q p``,
   RW_TAC resq_ss []
   ++ Cases_on `p = q` >> RW_TAC alg_ss []
   ++ RW_TAC alg_ss [curve_add_def]
   ++ Q.UNABBREV_ALL_TAC
   ++ ec_cases_on `e` `p`
   ++ ec_cases_on `e` `q`
   ++ RW_TAC resq_ss []
   ++ RW_TAC alg_ss [affine_case]
   ++ RW_TAC alg_ss []
   ++ ASM_SIMP_TAC alg_ss [affine_eq]
   ++ Suff `(x''' = x'') /\ ((x''' = x'') ==> (y''' = y''))`
   >> RW_TAC std_ss []
   ++ Know `~(d = field_zero e.field)`
   >> (Q.UNABBREV_TAC `d`
       ++ RW_TAC alg_ss [field_sub_eq_zero])
   ++ Know `~(d' = field_zero e.field)`
   >> (Q.UNABBREV_TAC `d'`
       ++ RW_TAC alg_ss [field_sub_eq_zero])
   ++ RW_TAC alg_ss [field_nonzero_eq]
   ++ match_tac field_sub_eq_zero_imp
   ++ Q.EXISTS_TAC `e.field`
   ++ RW_TAC alg_ss []
   ++ Q.UNABBREV_TAC `x''`
   ++ Q.UNABBREV_TAC `y''`
   ++ Q.UNABBREV_TAC `l`
   ++ Q.UNABBREV_TAC `m`
   ++ TRY (Q.UNABBREV_TAC `x'''`)
   ++ Q.UNABBREV_TAC `y'''`
   ++ Q.UNABBREV_TAC `l'`
   ++ Q.UNABBREV_TAC `m'`
   ++ Count.apply (RW_TAC (field_div_elim_ss context) [])
   ++ Q.UNABBREV_TAC `d`
   ++ Q.UNABBREV_TAC `d'`
   ++ with_flag (ORACLE_field_poly,true)
      (with_flag (subtypeTools.ORACLE,true)
       (Count.apply (ASM_SIMP_TAC (field_poly_ss context []) []))));

val curve_add_rzero = store_thm
  ("curve_add_rzero",
   ``!e :: Curve. !p :: curve_points e. curve_add e p (curve_zero e) = p``,
   METIS_TAC [curve_add_lzero,curve_add_comm,curve_zero_carrier]);

val context = subtypeTools.add_rewrite2 curve_add_rzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val curve_add_rneg = store_thm
  ("curve_add_rneg",
   ``!e :: Curve. !p :: curve_points e.
       curve_add e p (curve_neg e p) = curve_zero e``,
   METIS_TAC [curve_add_lneg,curve_add_comm,curve_neg_carrier]);

val context = subtypeTools.add_rewrite2 curve_add_rneg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(***
val curve_add_assoc = store_thm
  ("curve_add_assoc",
   ``!e :: Curve. !p q r :: curve_points e.
        curve_add e p (curve_add e q r) = curve_add e (curve_add e p q) r``,
   RW_TAC resq_ss []
   ++ ec_cases_on `e` `p`
   ++ ASM_SIMP_TAC alg_ss []
   ++ STRIP_TAC >> RW_TAC alg_ss [curve_add_lzero]
   ++ ec_cases_on `e` `q`
   ++ ASM_SIMP_TAC alg_ss []
   ++ STRIP_TAC >> RW_TAC alg_ss [curve_add_lzero, curve_add_rzero]
   ++ ec_cases_on `e` `r`
   ++ ASM_SIMP_TAC alg_ss []
   ++ STRIP_TAC >> RW_TAC alg_ss [curve_add_rzero]
   ++ (Cases_on `p = q` ++ Cases_on `q = r`)
   >> (METIS_TAC [curve_add_comm,curve_add_carrier])
   ++ RW_TAC alg_ss []
   ++ clean_assumptions




   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC resq_ss []
   ++ RW_TAC alg_ss
        [curve_add_def, curve_double_def, affine_case, LET_DEF,
         affine_eq, curve_distinct]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC alg_ss
        [curve_add_def, curve_double_def, affine_case, LET_DEF,
         affine_eq, curve_distinct]

   ++ Q.UNABBREV_ALL_TAC
   ++ ec_cases_on `e` `p`
   ++ ec_cases_on `e` `q`
   ++ RW_TAC resq_ss []

val curve_group = store_thm
  ("curve_group",
   ``!e :: Curve. curve_group e IN AbelianGroup``,
   RW_TAC resq_ss
     [curve_group_def, AbelianGroup_def, Group_def,
      GSPECIFICATION, combinTheory.K_THM]
   ++ RW_TAC alg_ss []
, curve_zero_carrier,
      curve_add_carrier, curve]
   << [


val context = subtypeTools.add_reduction2 curve_group context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;
***)

(***
val curve_mult_eval = prove
  (``!e :: Curve. !p :: curve_points e. !n.
       curve_mult e p n =
       if n = 0 then curve_zero e
       else
         let p' = curve_double e p in
         let n' = n DIV 2 in
         if EVEN n then curve_mult e p' n'
         else curve_add e p (curve_mult e p' n')``,
   proof should just reference group_exp_eval
***)

(***
val curve_hom_field = store_thm
  ("curve_hom_field",
   ``!f1 f2 :: Field. !f :: FieldHom f1 f2. !e :: Curve.
       project_map f IN
       GroupHom (curve_group e) (curve_group (curve_map f e))``,
***)

(***
(* ------------------------------------------------------------------------- *)
(* Examples                                                                  *)
(* ------------------------------------------------------------------------- *)

(*** Testing the primality checker
val prime_65537 = Count.apply prove
  (``65537 IN Prime``,
   RW_TAC std_ss [Prime_def, GSPECIFICATION]
   ++ CONV_TAC prime_checker_conv);
***)

(* From exercise VI.2.3 of Koblitz (1987) *)

val example_prime_def = Define `example_prime = 751`;

val example_field_def = Define `example_field = GF example_prime`;

val example_curve_def = Define
  `example_curve = curve example_field 0 0 1 (example_prime - 1) 0`;

val context = subtypeTools.add_rewrite2 example_prime_def context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val context = subtypeTools.add_rewrite2 example_field_def context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example_prime = lemma
  (``example_prime IN Prime``,
   RW_TAC alg_ss [Prime_def, GSPECIFICATION]
   ++ CONV_TAC prime_checker_conv);

val context =
    subtypeTools.add_reduction2 (SIMP_RULE alg_ss [] example_prime) context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example_field = lemma
  (``example_field IN Field``,
   RW_TAC alg_ss []);

val context =
    subtypeTools.add_reduction2 (SIMP_RULE alg_ss [] example_field) context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example_curve = lemma
  (``example_curve IN Curve``,
   RW_TAC alg_ss
     [example_curve_def, Curve_def, GSPECIFICATION, discriminant_def,
      non_singular_def, LET_DEF] ++
   RW_TAC alg_ss
     [LET_DEF, GF_alt, curve_b2_def, curve_b4_def,
      curve_b6_def, curve_b8_def, field_exp_small] ++
   CONV_TAC EVAL);

val context = subtypeTools.add_reduction2 example_curve context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example_curve_field = lemma
  (``example_curve.field = example_field``,
   RW_TAC std_ss [curve_accessors, example_curve_def]);

fun example_curve_pt pt = lemma
  (``^pt IN curve_points example_curve``,
   RW_TAC std_ss [GSYM example_curve_field]
   ++ MP_TAC (Q.ISPEC `example_curve` (CONV_RULE RES_FORALL_CONV curve_affine))
   ++ SIMP_TAC alg_ss []
   ++ RW_TAC alg_ss [example_curve_def, LET_DEF]
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss [GF_alt]);

val execute_conv =
    SIMP_CONV
      alg_ss
      [GSYM example_curve_field, curve_neg_def, curve_add_def,
       curve_double_def, affine_case, LET_DEF] THENC
    SIMP_CONV
      alg_ss
      [example_curve_def, curve_accessors, GF_alt, affine_eq, CONS_11] THENC
    RAND_CONV EVAL;

val pt1 = ``affine example_field [361; 383]``
and pt2 = ``affine example_field [241; 605]``;

val pt1_on_example_curve = example_curve_pt pt1
and pt2_on_example_curve = example_curve_pt pt2;

Count.apply execute_conv ``curve_neg example_curve ^pt1``;
Count.apply example_curve_pt (rhs (concl it));

Count.apply execute_conv ``curve_add example_curve ^pt1 ^pt2``;
Count.apply example_curve_pt (rhs (concl it));

Count.apply execute_conv ``curve_double example_curve ^pt1``;
Count.apply example_curve_pt (rhs (concl it));

(* ------------------------------------------------------------------------- *)
(* A formalized version of random binary maps in HOL.                        *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `randomMap =
     Leaf
   | Node of num => randomMap => 'a => 'b => randomMap`;

val emptyMap_def = Define `emptyMap : ('a,'b) randomMap = Leaf`;

val singletonMap_def = Define
  `singletonMap p a b : ('a,'b) randomMap = Node p Leaf a b Leaf`;

(* ------------------------------------------------------------------------- *)
(* Compilable versions of multiword operations                               *)
(* ------------------------------------------------------------------------- *)

fun compilable_multiword_operations words bits =

(* ------------------------------------------------------------------------- *)
(* Compilable versions of elliptic curve operations                          *)
(* ------------------------------------------------------------------------- *)

fun compilable_curve_operations prime words bits =
    let
      val {inject,add,mod,...} = compilable_multiword_operations words bits
    in
    end;

val curve_add_example_def = Define
  `curve_add_example (x_1_1 : word5) x_1_2 y_1_1 y_1_2 x_2_1 x_2_2 y_2_1 y_2_2 =
     let x_1 = FCP i. if i=0 then x_1_1 else x_1_2 in
     let y_1 = FCP i. if i=0 then y_1_1 else y_1_2 in
     let x_2 = FCP i. if i=0 then x_2_1 else x_1_2 in
     let y_2 = FCP i. if i=0 then y_2_1 else y_2_2 in
     curve_add
       ec
       (affine (GF 751) [mw2n x_1; mw2n y_1])
       (affine (GF 751) [mw2n x_2; mw2n y_2])`;

val curve_add_example_compilable =
    CONV_RULE (RAND_CONV execute_conv) curve_add_example_def;
***)

val () = export_theory ();
