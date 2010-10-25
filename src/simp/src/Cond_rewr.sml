structure Cond_rewr :> Cond_rewr =
struct

open HolKernel boolLib liteLib Trace;

type controlled_thm = BoundedRewrites.controlled_thm

fun WRAP_ERR x = STRUCT_WRAP "Cond_rewr" x;
fun ERR x      = STRUCT_ERR "Cond_rewr" x;

val stack_limit = ref 4;

val track_rewrites = ref false;
val used_rewrites  = ref [] : thm list ref;

(* -----------------------------------------------------------------------*
 * A total ordering on terms.  The behaviour of the simplifier depends    *
 * on this, so don't change it without thinking.                          *
 *                                                                        *
 * Based on some code in Isabelle.                                        *
 *                                                                        *
 * A strict (not reflexive) linear well-founded AC-compatible ordering    *
 * for terms.                                                             *
 *                                                                        *
 * Modified by DRS to have certain AC properties.  Vars are always        *
 * bigger than constants (hence move to the right).  They are             *
 * also bigger than unary comb functions.  They can't be bigger than      *
 * 2 or more argument functions as AC rewriting then loops (you           *
 * need var < f(var2,var3))                                               *
 * -----------------------------------------------------------------------*)

fun size_of_term tm =
     case dest_term tm
      of LAMB(Bvar,Body) => 1 + size_of_term Body
       | COMB(Rator,Rand) => size_of_term Rator + size_of_term Rand
       | _ => 1

fun op lex_cmp (cmp1, cmp2) ((a1,b1), (a2,b2)) =
    case cmp1 (a1, a2) of
      EQUAL => cmp2 (b1, b2)
    | x => x
infix lex_cmp

fun dest_hd env t =
    case dest_term t of
      VAR (s, ty) => let
      in
        case Binarymap.peek(env, t) of
          NONE => (((s, ""), 0), ty)
        | SOME n => ((("", ""), ~n), Type.alpha)
      end
    | CONST {Name, Thy, Ty} => (((Name, Thy), 1), Ty)
    | LAMB (bv, body) => ((("", ""), 2), type_of bv)
    | COMB _ => ((("", ""), 3), Type.alpha) (* should never happen *)

fun hd_compare (env1, env2) (t1, t2) =
    (String.compare lex_cmp String.compare lex_cmp Int.compare
     lex_cmp Type.compare)
    (dest_hd env1 t1, dest_hd env2 t2)

fun ac_term_ord0 n (e as (env1, env2)) (tm1, tm2) = let
  val cmp = ac_term_ord0 n e
in
  case Int.compare (size_of_term tm1, size_of_term tm2) of
    EQUAL => let
    in
      if is_abs tm1 then
        if is_abs tm2 then let
            val (bv1, bdy1) = dest_abs tm1
            val (bv2, bdy2) = dest_abs tm2
          in
            case Type.compare(type_of bv1, type_of bv2) of
              EQUAL => let
                val env1' = Binarymap.insert(env1, bv1, n)
                val env2' = Binarymap.insert(env2, bv2, n)
              in
                ac_term_ord0 (n + 1) (env1', env2') (bdy1, bdy2)
              end
            | x => x
          end
        else GREATER
      else if is_abs tm2 then LESS
      else let
          val (f, xs) = strip_comb tm1
          val (g, ys) = strip_comb tm2
        in
          (hd_compare e lex_cmp Int.compare lex_cmp list_compare cmp)
          (((f, length xs), xs), ((g, length ys), ys))
        end
    end
  | x => x
end
val empty_dict = Binarymap.mkDict Term.compare
val ac_term_ord = ac_term_ord0 0 (empty_dict, empty_dict)

(* bad old implementation, has a loop between

  (x + y) + 1  >  x + (y + 1)  >  x + (1 + y)  >  1 + (x + y)  >  (x + y) + 1

 remembering that 1 is really NUMERAL (NUMERAL_BIT1 ALT_ZERO)

fun ac_term_ord(tm1,tm2) =
   case (dest_term tm1, dest_term tm2) of
      (VAR _,CONST _) => GREATER
    | (VAR _, COMB (Rator,Rand)) => if is_comb Rator then LESS else GREATER
    | (CONST _, VAR _) => LESS
    | (COMB (Rator,Rand), VAR _) => if is_comb Rator then GREATER else LESS
    | (VAR v1, VAR v2) => String.compare(fst v1, fst v2)
    | (CONST c1, CONST c2) =>
        (case String.compare(#Name c1,#Name c2)
          of EQUAL => String.compare(#Thy c1,#Thy c2)
           | other => other)
    | (dt1,dt2) =>
      (case Int.compare (size_of_term tm1,size_of_term tm2) of
       EQUAL =>
         (case (dt1,dt2) of
            (LAMB l1,LAMB l2) => ac_term_ord(snd l1, snd l2)
          | _ => let val (con,args) = strip_comb tm1
                     val (con2,args2) = strip_comb tm2
                 in case ac_term_ord (con,con2) of
                    EQUAL => list_ord ac_term_ord (args,args2)
                  | ord => ord
                 end)
       | ord => ord)

*)

   (* ---------------------------------------------------------------------
    * COND_REWR_CONV
    * ---------------------------------------------------------------------*)

   fun vperm(tm1,tm2) =
    case (dest_term tm1, dest_term tm2)
     of (VAR v1,VAR v2)   => (snd v1 = snd v2)
      | (LAMB t1,LAMB t2) => vperm(snd t1, snd t2)
      | (COMB t1,COMB t2) => vperm(fst t1,fst t2) andalso vperm(snd t1,snd t2)
      | (x,y) => (x = y)

   fun is_var_perm(tm1,tm2) =
       vperm(tm1,tm2) andalso set_eq (free_vars tm1) (free_vars tm2)

   fun COND_REWR_CONV th bounded =
      let val eqn = snd (strip_imp (concl th))
          val isperm = is_var_perm (dest_eq eqn)
          val instth = HO_PART_MATCH (lhs o snd o strip_imp) th
                       handle HOL_ERR _ => ERR("COND_REWR_CONV",
                         "bad theorem argument (not a conditional equation)")
      in
      fn solver => fn stack => fn tm =>
       (let val conditional_eqn = instth tm
            val (conditions,eqn) = strip_imp (concl conditional_eqn)
	    val _ = if exists (C (op_mem aconv) stack) conditions
			then (trace(1, TEXT "looping - cut");
                              failwith "looping!") else ()
	    val _ = if length stack + length conditions > (!stack_limit)
                    then (trace(1, TEXT "looping - stack limit reached");
                          failwith "stack limit") else ()
            val (l,r) = dest_eq eqn
            val _ =
              if Term.aconv l r then
                (trace(4, IGNORE ("Rewrite loops", conditional_eqn));
                 failwith "looping rewrite")
              else ()

            val _ = if isperm andalso ac_term_ord(l, r) <> GREATER andalso
                       not bounded
                    then
                      (trace(4, IGNORE("possibly looping",conditional_eqn));
                       failwith "permutative rewr: not applied")
                    else ()
            val _ = if null conditions then ()
                    else trace(if isperm then 2 else 1, REWRITING(tm,th))
	    val new_stack = conditions@stack
            fun solver' condition =
                 let val _   = trace(2,SIDECOND_ATTEMPT condition)
                     val res = solver new_stack condition
                      handle e as HOL_ERR _
                       =>  (trace(1,SIDECOND_NOT_SOLVED condition); raise e)
                 in trace(2,SIDECOND_SOLVED res);
                    res
                 end
            val condition_thms = map solver' conditions
            val disch_eqn = rev_itlist (C MP) condition_thms conditional_eqn
            val final_thm = if (l = tm) then disch_eqn
                            else TRANS (ALPHA tm l) disch_eqn
            val _ = if null conditions then
              trace(if isperm then 2 else 1, REWRITING(tm,th))
                    else ()
            val _ = if null stack andalso !track_rewrites
                      then used_rewrites := th :: !used_rewrites
                      else ()
        in trace(if isperm then 3 else 2,PRODUCE(tm,"rewrite",final_thm));
	    final_thm
        end
        handle e => WRAP_ERR("COND_REWR_CONV (application)",e))
      end
      handle e  => WRAP_ERR("COND_REWR_CONV (construction) ",e);


val BOUNDED_t = mk_thy_const {Thy = "bool", Name = "BOUNDED",
                              Ty = bool --> bool}
fun loops th = let
  val (l,r) = dest_eq (concl th)
in
  can (find_term (equal l)) r
end handle HOL_ERR _ => failwith "loops"


(*-------------------------------------------------------------------------
 * IMP_CONJ_THM
 * IMP_CONJ_RULE
 * CONJ_DISCH
 *
 * CONJ_DISCH discharges a list of assumptions, and conjoins them as
 * a single antecedent.
 *
 * EXAMPLE
 *
 * CONJ_DISCH [`P:bool`,`Q:bool`] (mk_thm([`P:bool`,`Q:bool`,`R:bool`],`T`));
 * val it = [R] |- P /\ Q ==> T : thm
 *------------------------------------------------------------------------*)


val CONJ_DISCH =
  let val IMP_CONJ_RULE =
      let val (t1,t2,t3) = triple_of_list(fst(strip_forall(concl AND_IMP_INTRO)))
          val IMP_CONJ_THM = fst(EQ_IMP_RULE (SPEC_ALL AND_IMP_INTRO))
      in fn th =>
        let val (p,qr) = dest_imp(concl th)
            val (q,r) = dest_imp qr
        in MP (INST [t1 |-> p, t2 |-> q, t3 |-> r] IMP_CONJ_THM) th
        end
      end;
  in fn asms => fn th =>
    itlist (fn tm => (fn th => IMP_CONJ_RULE th
                      handle HOL_ERR _ => th) o DISCH tm)
    asms th
  end;



  (* ----------------------------------------------------------------------
   * IMP_EQ_CANON
   *
   * Put a theorem into canonical form as a conditional equality.
   *
   * Makes the set of rewrites from a given theorem.
   * Split a theorem into a list of theorems suitable for rewriting:
   *   1. Specialize all variables (SPEC_ALL).
   *   2. Move all conditions into assumptions
   *   3. Then do the following:
   *     A |- t1 /\ t2     -->    [A |- t1 ; A |- t2]
   *   4. Then A |- t --> [A |- t = T]
   *           A |- ~(t1 = t2) -> [A |- (t1 = t2) = F; A |- (t2 = t1) = F]
   *           A |- ~t --> A |- [t = F]
   *           A |- F --> thrown away  (hmmm... a bit suss)
   *           A |- T --> thrown away
   *   5. Discharge all conditions as one single conjoined condition.
   *   6. Existentially quantify variables free in the conditions
   *      but not free in the equation.
   *
   * EXAMPLES
   *
   * IMP_EQ_CANON [mk_thm([],`foo (s1,s2) ==> P s2`];
   * IMP_EQ_CANON (mk_thm([],`foo (s1,s2) ==> (v1 = v2)`));
   * ----------------------------------------------------------------------*)
(* new version of this due to is_imp/negation problem in hol90 *)

fun UNDISCH_ALL th =
  if is_imp (concl th) then UNDISCH_ALL (UNDISCH th)
  else th;;

val truth_tm = boolSyntax.T
val false_tm = boolSyntax.F
val Abbrev_tm = prim_mk_const {Name = "Abbrev", Thy = "marker"}
val x_eq_false = SPEC (mk_eq(genvar bool, false_tm)) FALSITY

fun IMP_EQ_CANON (thm,bnd) = let
  val conditions = #1 (strip_imp (concl thm))
  val undisch_thm = UNDISCH_ALL thm
  val conc = concl undisch_thm
  fun IMP_EQ_CANONb th = IMP_EQ_CANON (th, bnd)
  val undisch_rewrites =
      if (is_eq conc) then
        if loops undisch_thm andalso bnd = BoundedRewrites.UNBOUNDED then
          (trace(1,IGNORE("looping rewrite (but adding EQT versions)",thm));
           [(EQT_INTRO undisch_thm, bnd), (EQT_INTRO (SYM undisch_thm), bnd)])
        else let
            val base =
                if null (subtract (free_vars (rhs conc))
                                  (free_varsl (lhs conc::hyp thm)))
		then undisch_thm
		else
                  (trace(1,IGNORE("rewrite with existential vars (adding \
                                  \EQT version(s))",thm));
                   EQT_INTRO undisch_thm)
            val flip_eqp = let val (l,r) = dest_eq (concl base)
                           in
                             is_eq l andalso not (is_eq r)
                           end
          in
            if flip_eqp then
              [(base, bnd),
               (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) base, bnd)]
            else [(base,bnd)]
          end
      else if is_conj conc then
        undisch_thm |> CONJ_PAIR
                    |> (IMP_EQ_CANONb ## IMP_EQ_CANONb)
                    |> op @
      else if is_forall conc then
        undisch_thm |> SPEC_VAR |> snd |> IMP_EQ_CANONb
      else if is_neg conc then
        if is_eq (dest_neg conc) then
          [(EQF_INTRO undisch_thm, bnd), (EQF_INTRO (GSYM undisch_thm), bnd)]
        else [(EQF_INTRO undisch_thm, bnd)]
      else if conc = truth_tm then
        (trace(2,IGNORE ("pointless rewrite",thm)); [])
      else if conc = false_tm then [(MP x_eq_false undisch_thm, bnd)]
      else if is_comb conc andalso same_const (rator conc) Abbrev_tm then
        if is_eq (rand conc) then
          undisch_thm |> CONV_RULE (REWR_CONV markerTheory.Abbrev_def)
                      |> SYM
                      |> IMP_EQ_CANONb
        else []
      else [(EQT_INTRO undisch_thm, bnd)]
in
  map (fn (th,bnd) => (CONJ_DISCH conditions th, bnd)) undisch_rewrites
end handle e => WRAP_ERR("IMP_EQ_CANON",e);


fun QUANTIFY_CONDITIONS (thm, bnd) =
    if is_imp (concl thm) then let
        val free_in_eqn = (free_vars (snd(dest_imp (concl thm))))
        val free_in_thm = (free_vars (concl thm))
        val free_in_hyp = free_varsl (hyp thm)
        val free_in_conditions =
            subtract (subtract free_in_thm free_in_eqn) free_in_hyp
        fun quantify fv = CONV_RULE (HO_REWR_CONV LEFT_FORALL_IMP_THM) o GEN fv
        val quan_thm = itlist quantify free_in_conditions thm
      in
        [(quan_thm, bnd)]
      end
    else [(thm, bnd)]
 handle e => WRAP_ERR("QUANTIFY_CONDITIONS",e)

fun imp_canon_munge acc antthlist =
    case antthlist of
      [] => acc
    | ((ants, th, bnd) :: rest) =>
      imp_canon_munge ((List.foldl (uncurry DISCH) th ants, bnd) :: acc) rest

fun IMP_CANON acc thl =
    case thl of
      [] => imp_canon_munge [] acc
    | (ants, th, bnd)::ths => let
        val w = concl th
      in
        if is_conj w then let
            val (th1, th2) = CONJ_PAIR th
          in
            IMP_CANON acc ((ants, th1, bnd) :: (ants, th2, bnd) :: ths)
          end
        else if is_imp w then let
            val (ant,c) = dest_imp w
          in
            if is_conj ant then let
                val (conj1,conj2) = dest_conj ant
                val newth =
                    DISCH conj1 (DISCH conj2 (MP th (CONJ (ASSUME conj1)
                                                          (ASSUME conj2))))
              in
                IMP_CANON acc ((ants, newth, bnd) :: ths)
              end
            else if is_disj ant then let
                val (disj1,disj2) = dest_disj ant
                val newth1 = DISCH disj1 (MP th (DISJ1 (ASSUME disj1) disj2))
                val newth2 = DISCH disj2 (MP th (DISJ2 disj1 (ASSUME disj2)))
              in
                IMP_CANON acc
                          ((ants, newth1, bnd) :: (ants, newth2, bnd) :: ths)
              end
            else if is_exists ant then let
                val (Bvar,Body) = dest_exists ant
                val bv' = variant (thm_frees th) Bvar
                val body' = subst [Bvar |-> bv'] Body
                val newth =
                    DISCH body' (MP th (EXISTS(ant, bv') (ASSUME body')))
              in
                IMP_CANON acc ((ants, newth, bnd) :: ths)
              end
            else if c = boolSyntax.F then
              IMP_CANON ((ants, NOT_INTRO th, bnd) :: acc) ths
              (* we want [.] |- F theorems to rewrite to [.] |- x = F,
                 done above in IMP_EQ_CANON, but we don't want this to
                 be done for |- P ==> F, which would set up a rewrite
                 of the form |- P ==> (x = F), which would match any
                 boolean term and force endless attempts to prove P.
                 Instead, convert to |- ~P *)
            else
              IMP_CANON acc ((ant::ants, UNDISCH th, bnd)::ths)
          end
        else if is_forall w then
          IMP_CANON acc ((ants, SPEC_ALL th, bnd) :: ths)
        else if is_res_forall w then let
            val newth = CONV_RULE (REWR_CONV RES_FORALL_THM THENC
                                   QUANT_CONV (RAND_CONV BETA_CONV)) th
          in
            IMP_CANON acc ((ants, newth, bnd) :: ths)
          end
        else IMP_CANON ((ants, th, bnd)::acc) ths
      end

val IMP_CANON = (fn (th,bnd) => IMP_CANON [] [([], th, bnd)])

infix oo;
fun f oo g = fn x => flatten (map f (g x));

fun mk_cond_rewrs l =
    (QUANTIFY_CONDITIONS oo IMP_EQ_CANON oo IMP_CANON) l
    handle e as HOL_ERR _ => WRAP_ERR("mk_cond_rewrs",e);

end;


(* TESTS:
 SIMP_CONV sum_ss [] (--`ISL y ==> (y = INL (OUTL y))`--);


val th1 = ASSUME (--`!(x:num) (y:num). Q x y ==> R x`--);

    SIMP_CONV (merge_ss [bool_ss,SATISFY_ss]) [th1] (--`Q 1 3 ==> R 1`--);



*)
