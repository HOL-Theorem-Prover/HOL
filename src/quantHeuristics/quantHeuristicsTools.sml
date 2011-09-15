(*=====================================================================  *)
(* FILE          : quantHeuristicsTools.sml                              *)
(* DESCRIPTION   : some general tools that are later used by             *)
(*                 quantHeuristicsLib                                    *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : December 2008                                         *)
(* ===================================================================== *)


structure quantHeuristicsTools :> quantHeuristicsTools =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
load "ConseqConv"
show_assums := true;
quietdec := true;
*)

open HolKernel Parse boolLib Drule ConseqConv quantHeuristicsTheory

(*
quietdec := false;
*)


(*---------------------------------------------------------
 *      A |-  t1 = t2
 * ---------------------------- (v not free in A)
 *  A |- (?v. t1)  =  (?v. t2)
 *---------------------------------------------------------*)

fun EQ_EXISTS_INTRO (v,thm) =
  AP_TERM (inst [alpha |-> (type_of v)] (boolSyntax.existential)) (ABS v thm);

(*---------------------------------------------------------
 *      A |-  t1 = t2
 * ---------------------------- (v not free in A)
 *  A |- (!v. t1) = (!v. t2)
 *---------------------------------------------------------*)
fun EQ_FORALL_INTRO (v,thm) =
  AP_TERM (inst [alpha |-> (type_of v)] (boolSyntax.universal)) (ABS v thm);


(*---------------------------------------------------------
 *      A |-  t1 ==> t2
 * ---------------------------- (v not free in A)
 *  A |- (?v. t1) ==> (?v. t2)
 *---------------------------------------------------------*)

fun IMP_EXISTS_INTRO (v,thm) =
   HO_MATCH_MP boolTheory.MONO_EXISTS (GEN v thm)


(*---------------------------------------------------------
 *      A |-  t1 ==> t2
 * ---------------------------- (v not free in A)
 *  A |- (!v. t1) ==> (!v. t2)
 *---------------------------------------------------------*)
fun IMP_FORALL_INTRO (v,thm) =
   HO_MATCH_MP boolTheory.MONO_ALL (GEN v thm)


(*---------------------------------------------------------
 *   t1 ==> t2 ==> t3
 * ------------------------
 *    t1 /\ t2 ==> t3
 *---------------------------------------------------------*)
fun AND_IMP_INTRO_CONV t =
let
   val (t1, t23) = dest_imp t
   val (t2, t3) = dest_imp t23
in
   SPECL [t1,t2,t3] AND_IMP_INTRO
end;


(*---------------------------------------------------------
 *       t
 * ------------------------
 *    T ==> t
 *---------------------------------------------------------*)
val true_imp_elim_thm = prove (``(T ==> b) = b``, REWRITE_TAC[]);

val TRUE_IMP_ELIM_CONV  =
   TRY_CONV (REWR_CONV true_imp_elim_thm)


(*---------------------------------------------------------
 *    t1 /\ t2 ==> t3
 * ------------------------
 *   t1 ==> t2 ==> t3
 *---------------------------------------------------------*)

val AND_IMP_ELIM_CONV = TRY_CONV (REWR_CONV (GSYM AND_IMP_INTRO))
fun LIST_AND_IMP_ELIM_CONV t =
let
   val (p, a) = dest_imp_only t;
in
   if (is_conj p) then (AND_IMP_ELIM_CONV THENC LIST_AND_IMP_ELIM_CONV) t else
   if (p = T) then (TRUE_IMP_ELIM_CONV THENC LIST_AND_IMP_ELIM_CONV) t else
   (RAND_CONV LIST_AND_IMP_ELIM_CONV) t
end handle HOL_ERR _ => raise UNCHANGED;


(*---------------------------------------------------------
 *      A |-  t1 ==> t2
 * ------------------------------
 *  A |- (x /\ t1) ==> (x /\ t2)
 *---------------------------------------------------------*)
fun LEFT_IMP_AND_INTRO_RULE x thm =
let
   val (t1, t2) = dest_imp (concl thm)
   val thm2 = SPECL [x,t1,t2] quantHeuristicsTheory.LEFT_IMP_AND_INTRO
in
   MP thm2 thm
end;


(*---------------------------------------------------------
 *      A |-  t1 ==> t2
 * ------------------------------
 *  A |- (t1 /\ x) ==> (t2 /\ x)
 *---------------------------------------------------------*)
fun RIGHT_IMP_AND_INTRO_RULE x thm =
let
   val (t1, t2) = dest_imp (concl thm)
   val thm2 = SPECL [x,t1,t2] quantHeuristicsTheory.RIGHT_IMP_AND_INTRO
in
   MP thm2 thm
end;


(*---------------------------------------------------------
 *      A |-  t1 ==> t2
 * ------------------------------
 *  A |- (x \/ t1) ==> (x \/ t2)
 *---------------------------------------------------------*)
fun LEFT_IMP_OR_INTRO_RULE x thm =
let
   val (t1, t2) = dest_imp (concl thm)
   val thm2 = SPECL [x,t1,t2] quantHeuristicsTheory.LEFT_IMP_OR_INTRO
in
   MP thm2 thm
end;


(*---------------------------------------------------------
 *      A |-  t1 ==> t2
 * ------------------------------
 *  A |- (t1 \/ x) ==> (t2 \/ x)
 *---------------------------------------------------------*)
fun RIGHT_IMP_OR_INTRO_RULE x thm =
let
   val (t1, t2) = dest_imp (concl thm)
   val thm2 = SPECL [x,t1,t2] quantHeuristicsTheory.RIGHT_IMP_OR_INTRO
in
   MP thm2 thm
end;



(*---------------------------------------------------------
 *   t
 * -----
 *  ~~t
 *---------------------------------------------------------*)
fun NEG_NEG_INTRO_CONV t = ISPEC t (GSYM satTheory.NOT_NOT);

(*---------------------------------------------------------
 *  ~~t
 * -----
 *   t
 *---------------------------------------------------------*)
fun NEG_NEG_ELIM_CONV t =
    (ISPEC (dest_neg (dest_neg t)) satTheory.NOT_NOT) handle HOL_ERR _ => raise UNCHANGED;


(*---------------------------------------------------------
 *  ~(!x1 ... xn. P)
 * ------------------
 *   ?x1 ... xn. ~P
 *---------------------------------------------------------*)
fun NOT_FORALL_LIST_CONV tm =
  (NOT_FORALL_CONV THENC TRY_CONV (QUANT_CONV NOT_FORALL_LIST_CONV)) tm

(*---------------------------------------------------------
 *  ~(?x1 ... xn. P)
 * ------------------
 *   !x1 ... xn. ~P
 *---------------------------------------------------------*)
fun NOT_EXISTS_LIST_CONV tm =
  (NOT_EXISTS_CONV THENC TRY_CONV (QUANT_CONV NOT_EXISTS_LIST_CONV)) tm;


(*---------------------------------------------------------
 * Strips n leading quantifiers and applies conv underneath
 *---------------------------------------------------------*)
fun STRIP_NUM_QUANT_CONV 0 conv = conv
  | STRIP_NUM_QUANT_CONV n conv =
    QUANT_CONV (STRIP_NUM_QUANT_CONV (n-1) conv)


(*---------------------------------------------------------
 *  ~(?x1 ... xn xn+1... xm. P)
 * -----------------------------
 *   !x1 ... xn ~?xn+1 ...xm. P
 *---------------------------------------------------------*)
fun BOUNDED_NOT_EXISTS_LIST_CONV 0 tm = ALL_CONV tm
  | BOUNDED_NOT_EXISTS_LIST_CONV n tm =
  (NOT_EXISTS_CONV THENC (QUANT_CONV
                         (BOUNDED_NOT_EXISTS_LIST_CONV (n-1)))) tm;


(*repeats a conversion up to a given number of times*)
fun BOUNDED_REPEATC 0 conv tm = ALL_CONV tm
  | BOUNDED_REPEATC n conv tm =
    ((QCHANGED_CONV conv THENC (BOUNDED_REPEATC (n-1) conv)) ORELSEC ALL_CONV) tm;


(*---------------------------------------------------------
 *  ?x1 ... xn. ~P
 * ----------------
 *  ~!x1 ... xn. P
 *---------------------------------------------------------*)
fun EXISTS_NOT_LIST_CONV tm =
  (TRY_CONV (QUANT_CONV EXISTS_NOT_LIST_CONV) THENC
   EXISTS_NOT_CONV) tm;

(*---------------------------------------------------------
 *  !x1 ... xn. ~P
 * ----------------
 *  ~?x1 ... xn. P
 *---------------------------------------------------------*)
fun FORALL_NOT_LIST_CONV tm =
  (TRY_CONV (QUANT_CONV FORALL_NOT_LIST_CONV) THENC
   FORALL_NOT_CONV) tm;



(*---------------------------------------------------------
 *  !x. P x   ?x. P x
 * --------- ---------  for x not free in P
 *     P         P
 *---------------------------------------------------------*)
fun QUANT_SIMP_CONV t =
    if (is_exists t) then
       let
          val (v,b) = dest_exists t;
          val _ = if mem v (free_vars b) then raise UNCHANGED else ();
       in
          HO_PART_MATCH lhs boolTheory.EXISTS_SIMP t
       end
    else if (is_forall t) then
       let
          val (v,b) = dest_forall t;
          val _ = if mem v (free_vars b) then raise UNCHANGED else ();
       in
          HO_PART_MATCH lhs boolTheory.FORALL_SIMP t
       end
    else raise UNCHANGED;



(*---------------------------------------------------------
 *  ~(A \/ B)    ~(A /\ B)    ~A /\ ~B     ~A \/ ~B
 * -----------  -----------  -----------  -----------
 *  ~A /\ ~B     ~A \/ ~B     ~(A \/ B)    ~(A /\ B)
 *---------------------------------------------------------*)
local
   val thmL = CONJUNCTS (SPEC_ALL DE_MORGAN_THM)
   val thm_and = GEN_ALL (el 1 thmL)
   val thm_or = GEN_ALL (el 2 thmL)
in
    fun NOT_OR_CONV t =
    let
       val (t1,t2) = dest_disj (dest_neg t);
    in
       SPECL [t2,t1] thm_or
    end;

    fun NOT_AND_CONV t =
    let
       val (t1,t2) = dest_conj (dest_neg t);
    in
       SPECL [t2,t1] thm_and
    end;


    fun AND_NOT_CONV t =
    let
       val (t1,t2) = dest_conj t;
    in
       SPECL [dest_neg t2,dest_neg t1] (GSYM thm_or)
    end;

    fun OR_NOT_CONV t =
    let
       val (t1,t2) = dest_disj t;
    in
       SPECL [dest_neg t2,dest_neg t1] (GSYM thm_and)
    end;

end;


(*----------------------------------------------------------
 * A tiny wrapper around REWR_CONV. This version allows
 * multiple theorems and considers the BODY_CONJUNCTS of
 * these theorems.
 *---------------------------------------------------------*)
fun TOP_ONCE_REWRITE_CONV thmL =
   let
      val thmL' = flatten (map BODY_CONJUNCTS thmL)
   in
      fn t => (tryfind (fn thm => REWR_CONV thm t) thmL')
   end handle HOL_ERR _ => raise UNCHANGED;


(*----------------------------------------------------------
 * VARIANT_CONV fvL renames all bound variables in a term
 * to ensure that they are distinct to each other and the
 * variables in fvL. Similar VARIANT_TAC does the same for
 * goals.
 *
 * Examples:
 * VARIANT_CONV []          ``(!n:num. P n) /\ (!n:num. Q n)``
 *                       -->  (!n.     P n) /\ (!n'.    Q n)
 *
 * VARIANT_CONV [``n:num``] ``(!n:num. P n) /\ (!n:num. Q n)``
 *                       -->  (!n'.    P n) /\ (!n''.   Q n)
 *---------------------------------------------------------*)

local
fun vc vL t =
   case dest_term t of
       VAR  _        => (vL, NONE)
     | CONST _       => (vL, NONE)
     | COMB (t1, t2) =>
       let
          val (vL' , thm1_opt) = vc vL t1;
          val (vL'', thm2_opt) = vc vL' t2;
          val thm_opt = if not (isSome thm1_opt orelse isSome thm2_opt) then NONE else
              let
                 val thm1 = if (isSome thm1_opt) then valOf thm1_opt else REFL t1;
                 val thm2 = if (isSome thm2_opt) then valOf thm2_opt else REFL t2;
              in
                 SOME (MK_COMB (thm1, thm2))
              end;
       in
          (vL'', thm_opt)
       end
     | LAMB (v, _) =>
       let
          val v' = variant vL v;
          val (thm_v_opt,b) =
              if aconv v v' then (NONE,body t) else
              let
                 val thm_v = ALPHA_CONV v' t;
                 val b = body (rhs (concl thm_v))
              in
                 (SOME thm_v, b)
              end;
          val (vL' , thm_b_opt) = vc (v'::vL) b;
          val thm_opt = if not (isSome thm_v_opt orelse isSome thm_b_opt) then NONE else
              let
                 val thm_v = if (isSome thm_v_opt) then valOf thm_v_opt else REFL t;
                 val thm_b = if (isSome thm_b_opt) then valOf thm_b_opt else REFL b;
              in
                 SOME (TRANS thm_v (ABS v' thm_b))
              end;
       in
         (v'::vL', thm_opt)
       end;
in
   fun VARIANT_CONV fvL t =
   let
       val (_, thm_opt) = vc (append fvL (free_vars t)) t;
   in
      if isSome thm_opt then valOf thm_opt else raise UNCHANGED
   end;



   fun VARIANT_TAC fvL (asm, t) =
   let
       val fvL0 = append fvL (flatten (map free_vars (t::asm)));

       fun vc_asms fvL [] = ([],[])
         | vc_asms fvL (asm::L) =
             let
                val (fvL', thm_opt) = (vc fvL asm);
                val thm = if isSome thm_opt then valOf thm_opt else REFL asm;
                val t' = rhs (concl thm);
                val (tL, thmL) = vc_asms fvL' L;
             in
                ((t'::tL),(thm::thmL))
             end
       val (t',asm', t_thm,asm_thms) =
           let
              val (xx,yy) = vc_asms fvL0 (t::(rev asm))
           in
              (hd xx, tl xx, hd yy, tl yy)
           end;

       val new_goal = (rev asm', t');
       (*val goal_thm = mk_thm new_goal*)

       fun valid goal_thm =
           let
              val thm0 = EQ_MP (GSYM t_thm) goal_thm
              fun asm_mp (a_thm,thm0) =
                let
                  val a_imp_thm = (fst (EQ_IMP_RULE a_thm))
                  val thm1 = DISCH (snd (dest_imp (concl a_imp_thm))) thm0
                  val thm2 = MP thm1 (UNDISCH a_imp_thm)
                in
                  thm2
                end;
           in
              foldl asm_mp thm0 asm_thms
           end;
   in
      ([new_goal], fn thmL => (valid (hd thmL)))
   end;
end



(*******************************************************
 * min_var_occur_CONV v t tries to minimize the number of
 * occurences of the variable v in t.
 *
 * As a simple example
 * min_var_occur_CONV ``x:num`` ``P /\ (f x = f 2) /\ Q (f x) /\ Z``
 * results in                     P /\ (f x = f 2) /\ Q (f 2) /\ Z
 *******************************************************)

local

datatype context_rw_type =
 crw_conj | crw_disj | crw_unknown;

fun crw_negate crw_conj = crw_disj
  | crw_negate crw_disj = crw_conj
  | crw_negate crw_unknown = crw_unknown;


fun dest_disj_imp t =
   dest_disj t handle HOL_ERR _ =>
   let val (a,b) = dest_imp_only t in
       (mk_neg a, b) end

val is_disj_imp = can dest_disj_imp;

fun crw_strip rwt t =
  if (is_conj t andalso not (rwt = crw_disj)) then
     let
        val (t1,t2) = dest_conj t;
        val (l1,_) = crw_strip crw_conj t1;
        val (l2,_) = crw_strip crw_conj t2;
     in
        (append l1 l2, crw_conj)
     end
  else if (is_disj_imp t andalso not (rwt = crw_conj)) then
     let
        val (t1,t2) = dest_disj_imp t;
        val (l1,_) = crw_strip crw_disj t1;
        val (l2,_) = crw_strip crw_disj t2;
     in
        (append l1 l2, crw_disj)
     end
  else if (is_neg t) then
     let
        val t1 = dest_neg t;
        val rwt1 = crw_negate rwt;
        val (l1,rwt2) = crw_strip rwt1 t1;
        val rwt3 = crw_negate rwt2;
     in
        (l1, rwt3)
     end
  else (if is_eq t andalso (rwt = crw_conj) then [t] else
        if type_of t = bool then [mk_eq(t,
             if rwt = crw_conj then T else F)] else [], rwt)


(*
   val t = ``~~((a \/ P) /\ (f x = f 2) /\ Q (f x) /\ Z)``
   val t = ``~~((a \/ P) /\ (f x = f 2) /\ (f x = f 2) /\ Q (f x) /\ Z)``
   val t = ``~~((a \/ P) /\ (f 2 = f x) /\ Q (f x) /\ Z)``
   val t = ``(P /\ (f x = f 2)) ==> Q (f x)``
   val t = ``~(P x) /\ (f x = f 2) /\ ((P x) \/ A)``
   val t = ``(P \/ ~(f x = f 2)) \/ ~(x = 5)``

val v = ``x:num``
min_var_occur_CONV v t
*)

fun crw_SINGLE_STEP_CONV (rw, turned) t =
let
   val (l,r) = dest_eq rw;

   val dummy_var = genvar bool;
   val org_rw_term = if same_const r T orelse same_const r F then l else
       if turned then mk_eq (r,l) else rw;

   val t1 = subst_occs [[1]] [org_rw_term |-> dummy_var] t
   val t2 = subst [l |-> r] t1
   val t3 = subst [dummy_var |-> org_rw_term] t2;

   val eq_t = mk_eq (t, t3);

   val thm_t = EQT_ELIM (REWRITE_CONV [ASSUME org_rw_term] eq_t)
   val thm_f = EQT_ELIM (REWRITE_CONV (
        let val athm = ASSUME (mk_neg org_rw_term) in
        [athm, GSYM athm] end) eq_t);

   val thm = DISJ_CASES (ISPEC org_rw_term boolTheory.EXCLUDED_MIDDLE) thm_t thm_f
in
   thm
end handle HOL_ERR _ => raise UNCHANGED;

fun crw_TOP_CONV P t =
let
   val (eql, rwt) = crw_strip crw_unknown t;
   val _ = if (rwt = crw_unknown) then raise UNCHANGED else ();

   fun turn_eq rw =
      let val (l,r) = dest_eq rw in mk_eq (r,l) end;

   fun check_rw P rw =
      case P rw of
         NONE => NONE
       | SOME false => SOME (rw,false)
       | SOME true  => SOME (turn_eq rw, true)

   val eql' = map valOf (filter isSome (map (check_rw P) eql));
   val convL = map crw_SINGLE_STEP_CONV eql';
   val _ = if null convL then raise UNCHANGED else ();
in
   EVERY_CONV convL t
end;


fun crw_CONV P = TOP_SWEEP_CONV (CHANGED_CONV (crw_TOP_CONV P));

in

val min_var_occur_CONV =
let
   fun P v rw =
   let
      val (l,r) = dest_eq rw;
      val lf = free_in v l;
      val rf = free_in v r;
   in
      if (is_conj l) orelse (is_disj_imp l) then NONE else
      if lf andalso (not rf) then SOME false else
      if (not lf) andalso rf then SOME true else
      NONE
   end;
in
   fn v => (crw_CONV (P v))
end;
end



(*******************************************************
 * match_term_var v t1 t2
 * searches for an instantiation i, such that
 * replacing v with i in t1 leads to t2, i.e. such that
 * t1 [v/i] = t2.
 *
 * If such an i is found, it is returned. Otherwise,
 * an HOL_ERR exception is thrown.
 *******************************************************)

fun match_term_var v t1 t2 =
let
    val (s,t) = match_term t1 t2;
    val _ = if (t = []) then () else Feedback.fail ();
    val _ = if (s = []) then Feedback.fail () else ();
    val i = hd s;
    val _ = if (s = [i]) then () else Feedback.fail ();

    val _ = if (#redex i = v) then () else Feedback.fail ();
in
    #residue i
end;




(*******************************************************
 * avoid_vL and rename_vL are supposed to be lists of
 * variables.
 *
 * list_variant avoid_vL rename_vL
 *
 * returns a list of variants of the variable in rename_vL
 * such that they are all distinct to the variables in avoid_vL
 * and each other. The resulting substitution is returned as well.
 *
 *
 * EXAMPLE:
 *    list_variant [``x``] [``x``, ``x'``, ``y``]  -->
 *    ([``x'``, ``x''``, ``y``], [``x`` |-> ``x'``, ``x'`` |-> ``x''``])
 *
 * for comparison
 *    map (variant [``x``]) [``x``, ``x'``, ``y``]  -->
 *    [``x'``, ``x'``, ``y``]  (both the same!!!)
 *
 *******************************************************)

fun list_variant avoid_vL rename_vL =
let
   val (_,sub,fvL') =
      foldl (fn (fv, (vL,sub,fvL)) =>
	  let
             val fv' = variant vL fv;
             val vL' = fv'::vL;
             val fvL' = fv'::fvL;
             val sub' = if (fv = fv') then sub else
			(fv |-> fv')::sub;
          in
             (vL',sub',fvL')
          end) (avoid_vL,[],[]) rename_vL;
in
  (rev fvL', sub)
end;


end
