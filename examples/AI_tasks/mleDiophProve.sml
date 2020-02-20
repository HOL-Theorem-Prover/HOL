(* ========================================================================= *)
(* FILE          : mleDiophProve.sml                                         *)
(* DESCRIPTION   : Verifying that a set corresponds to its description by    *)
(*                 a Diophantine equation.                                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleDiophProve :> mleDiophProve =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory 
pred_setTheory numSyntax

val ERR = mk_HOL_ERR "mleDiophProve"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Useful terms and provers
   ------------------------------------------------------------------------- *)

val pred = mk_var ("p",``:num -> bool``)
val vk = mk_var ("k",``:num``)
val vx = mk_var ("x",``:num``)
val vy = mk_var ("y",``:num``)
val vz = mk_var ("z",``:num``)
val vn = mk_var ("n",``:num``)
val cP = mk_var ("p",``:num -> bool``);
val cQ = mk_var ("q",``:num -> bool``);

val disj16 = list_mk_disj 
  (List.tabulate (16, fn i => (mk_eq (vn,term_of_int i))));
  
val tm16 = term_of_int 16
fun mod16 x = mk_mod (x,tm16)
fun less16 x = mk_less (x,tm16)
fun eq0 x = mk_eq (mod16 x, zero_tm)
fun diff0 x = mk_neg (mk_eq (mod16 x, zero_tm))
fun rep16 x = {redex = x, residue = mod16 x}

fun PROVE_EVAL tm = EQT_ELIM (EVAL tm)

fun inst_v16 v thm = INST [{redex = v, residue = mk_mod (v,tm16)}] thm

(* -------------------------------------------------------------------------
   Case distinction theorems
   ------------------------------------------------------------------------- *)

val goal:goal = ([], mk_eq (``n < 16``, disj16));

fun CASES_LEFT_TAC goal = 
  let val v = hd (free_vars_lr (snd goal)) in
    (SPEC_TAC (v,v) THEN Cases THENL [simp [],ALL_TAC]) goal
  end

val LESS16 = TAC_PROOF (([],mk_eq (less16 vn,disj16)), 
   NTAC 16 CASES_LEFT_TAC THEN simp []);

val MOD16 = 
  let val thm = TAC_PROOF (([],``n MOD 16 < 16``), simp []) in
    MATCH_MP (fst (EQ_IMP_RULE LESS16)) thm
  end

val plenum = List.tabulate (16, fn x => mk_comb(cP,term_of_int x))
val plgen = mk_imp (list_mk_conj plenum, mk_comb(cP,vn))
val PRED16 = PROVE_HYP MOD16 
   (inst_v16 vn (TAC_PROOF (([disj16],plgen), METIS_TAC [])));

(* -------------------------------------------------------------------------
   Proves that a solution exists
   ------------------------------------------------------------------------- *)

val triplesubl =
  let 
    val l = List.tabulate (16,I)
    val triplel = map triple_of_list (cartesian_productl [l,l,l])
    fun f (a,b,c) = 
      [{redex = vx, residue = term_of_int a},
       {redex = vy, residue = term_of_int b},
       {redex = vz, residue = term_of_int c}]
  in
    map f triplel
  end
 
fun EXISTS_TRIPLE_TAC (xw,yw,zw) goal =
  let
    val sub = [{redex = vx, residue = xw},
               {redex = vy, residue = yw},
               {redex = vz, residue = zw}]
    val thm = PROVE_EVAL (subst sub (snd (strip_exists (snd goal))))
  in
    (EXISTS_TAC xw THEN EXISTS_TAC yw THEN EXISTS_TAC zw THEN ACCEPT_TAC thm)
    goal
  end

fun POLY_EXISTS_SOL poly =
  let
    val poly16 = subst (map rep16 [vx,vy,vz]) poly
    val instl = map_assoc (C subst poly) triplesubl
    fun is_provable x = term_eq T (rhs (concl (EVAL (eq0 x))))
    val (sub,_) = valOf (List.find (is_provable o snd) instl)
    val (xw,yw,zw) = triple_of_list (map #residue sub)
  in
    TAC_PROOF (([], list_mk_exists ([vx,vy,vz],eq0 poly16)),
               EXISTS_TRIPLE_TAC (xw,yw,zw))
  end

(* 
load "mleDiophProve"; open mleDiophProve;
val poly = ``2 + 14 * x * y * z``; 
val thm = POLY_EXISTS_SOL poly;
*)

(* -------------------------------------------------------------------------
   Proves that a solution does not exist
   ------------------------------------------------------------------------- *)

fun enumvar v tm = (tm, List.tabulate (16, 
  fn x => subst [{redex = v, residue = term_of_int x}] tm))

fun forall_enum v (gen,thml) =
  let
    val instthm = INST [{redex = cP, residue = mk_abs (v, diff0 gen)},
                        {redex = vn, residue = v}] PRED16
    val convthm = UNDISCH (CONV_RULE (TOP_DEPTH_CONV BETA_CONV) instthm)
  in
    PROVE_HYP (LIST_CONJ thml) convthm
  end

fun forall_enumz (gen,thml) = 
  forall_enum vz (gen,thml)
fun forall_enumy (gen,thml) = 
  forall_enum vy (subst [rep16 vz] gen, thml)
fun forall_enumx (gen,thml) = 
  forall_enum vx (subst (map rep16 [vy,vz]) gen, thml)

fun POLY_NEG_EXISTS_SOL poly =
  let
    val polyx = [enumvar vx poly]
    val polyxy = map_snd (map (enumvar vy)) polyx
    val polyxyz = (map_snd (map_snd (map (enumvar vz)))) polyxy
    val polyxyzthm = 
      (map_snd (map_snd (map_snd (map (PROVE_EVAL o diff0))))) polyxyz
    val polyxythm = map_snd (map_snd (map forall_enumz)) polyxyzthm
    val polyxthm = map_snd (map forall_enumy) polyxythm
    val polythm = singleton_of_list (map forall_enumx polyxthm)
    val poly16 = subst (map rep16 [vx,vy,vz]) poly
    val negex = mk_neg (list_mk_exists ([vx,vy,vz], eq0 poly16))
    val convthm = normalForms.PURE_NNF_CONV negex
  in
    MP (snd (EQ_IMP_RULE convthm)) (GENL [vx,vy,vz] polythm)
  end

(* 
load "mleDiophProve"; open mleDiophProve;
val poly = ``1 + 14 * x * y * z``;
val thm = POLY_NEG_EXISTS_SOL poly;
*)

(* -------------------------------------------------------------------------
   Express the verified formula as an equality between sets
   ------------------------------------------------------------------------- *)

val PQ16 = 
  let
    fun mk_pq i = 
      mk_eq (mk_comb (cP, term_of_int i), mk_comb (cQ, term_of_int i));
    val pqconjl = list_mk_conj (List.tabulate (16,mk_pq));
    val goal = ([pqconjl],``(\k. k < 16 /\ p k) = (\n. n < 16 /\ q n)``) 
  in
    TAC_PROOF 
      (goal, ABS_TAC THEN CONV_TAC (REWRITE_CONV [LESS16]) THEN METIS_TAC [])
  end

val PQSET16 = 
  let val thm = METIS_PROVE [] 
     ``(p : num -> bool) = q ==> {u | p u} = {v | q v}``
  in
    HO_MATCH_MP thm PQ16
  end

fun ENUMSET il = 
  let 
    val disj = list_mk_disj (map (fn x => mk_eq (vn,term_of_int x)) il)
    val a = pred_setSyntax.mk_set_spec (vn,disj)
    val b = pred_setSyntax.mk_set (map term_of_int il)
  in
    TAC_PROOF (([],mk_eq (a,b)), simp [EXTENSION,IN_SING,IN_INSERT])  
  end

fun CONJLESS16 il =
  let 
    val disj = list_mk_disj (map (fn x => mk_eq (vn,term_of_int x)) il)
    val disjless = mk_conj (less16 vn, disj)  
  in
    TAC_PROOF (([],mk_eq (disjless,disj)), METIS_TAC [LESS16])  
  end

(* -------------------------------------------------------------------------
   Prove that the two predicates are equal on the same input
   ------------------------------------------------------------------------- *)

fun PROVE_PQEQ poly il k =
  let
    val disj = list_mk_disj (map (fn x => mk_eq (vn,term_of_int x)) il)
    val qdef = mk_abs (vn, disj)
    val poly16 = subst (map rep16 [vx,vy,vz]) poly
    val pdef = mk_abs (vk, list_mk_exists ([vx,vy,vz], eq0 poly16))
    val convthm = BETA_CONV (mk_comb (pdef,term_of_int k))
    val thm1 = 
      let val polyk = subst [{redex = vk, residue = term_of_int k}] poly in
        if mem k il 
        then POLY_EXISTS_SOL polyk
        else POLY_NEG_EXISTS_SOL polyk
      end
    val thm1' = PURE_ONCE_REWRITE_RULE [SYM convthm] thm1 
    val qtm = mk_comb (qdef,term_of_int k)
    val tac = CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN DECIDE_TAC
    val thm2 = if mem k il
               then TAC_PROOF (([],qtm), tac)
               else TAC_PROOF (([],mk_neg qtm), tac)
    val predeq = mk_eq (mk_comb (pdef,term_of_int k),
                        mk_comb (qdef,term_of_int k))
  in
    METIS_PROVE [thm1',thm2] predeq
  end

(* -------------------------------------------------------------------------
   Verify that the polynomial describes the set
   ------------------------------------------------------------------------- *)

fun DIOPH_PROVE (poly,il) =
  let 
    val pql = List.tabulate (16, PROVE_PQEQ poly il)
    val pq = LIST_CONJ pql
    val pdef = (rator o lhs o concl o hd) pql
    val qdef = (rator o rhs o concl o hd) pql
    val inst = (INST [{redex = cP, residue = pdef}, 
                      {redex = cQ, residue = qdef}] PQSET16)
    val seteq = PROVE_HYP pq inst
    val reduce = CONV_RULE (TOP_DEPTH_CONV BETA_CONV) seteq    
    val rmless16 = PURE_ONCE_REWRITE_RULE [CONJLESS16 il] reduce
  in
    PURE_ONCE_REWRITE_RULE [ENUMSET il] rmless16
  end

(*
load "mleDiophProve"; open mleDiophProve;
val poly = ``k + 14 * x * y * z``;
val il = [0,2,4,6,8,10,12,14];
val thm = DIOPH_PROVE poly il;
*)

(* -------------------------------------------------------------------------
   Verify the solutions produced during evaluation.
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mleDiophLib"; open mleDiophLib;
load "mleDiophSynt"; open mleDiophSynt;
load "mleDiophProve"; open mleDiophProve;

val dir2 = HOLDIR ^ "/examples/AI_tasks/dioph_results_nolimit/test_tnn";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val boardl = mapfilter (valOf o #3) (List.tabulate (200,g)); length boardl;
val pairl = map (fn (a,b,_) => (veri_of_poly a, graph_to_il b)) boardl;

fun f i x = (print_endline (its i); DIOPH_PROVE x);
val (thml,t) = add_time (mapi f) pairl; length thml;

fun f_charl cl = case cl of
  [] => []
  | [a] => [a]
  | a :: b :: m => if Char.isSpace a andalso Char.isSpace b
                   then f (b :: m)
                   else if Char.isSpace a 
                   then #" " :: f ( b :: m)
val minspace = implode o f o explode;
val _ = writel (dir2 ^ "/__theorems") (map (minspace o string_of_goal o dest_thm) thml);
*)

end (* struct *)

