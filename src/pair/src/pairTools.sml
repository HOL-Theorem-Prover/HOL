structure pairTools :> pairTools =
struct

open HolKernel Parse boolLib pairSyntax pairTheory;

val PERR = mk_HOL_ERR "pairTools";

(*---------------------------------------------------------------------------
 *
 *     (x = (v1,...,vn))       |- M[(v1,...,vn)]
 *    ---------------------------------------------
 *      ?v1 ... vn. x = (v1,...,vn) |- M[x]
 *
 *---------------------------------------------------------------------------*)

fun VSTRUCT_ABS bind th =
  let fun CHOOSER v (tm,thm) =
        let val ex_tm = mk_exists(v,tm)
        in (ex_tm, CHOOSE(v, ASSUME ex_tm) thm)
        end
      val L = strip_pair (rand bind)
  in snd(itlist CHOOSER L (bind, SUBS[SYM(ASSUME bind)] th))
  end;


(*---------------------------------------------------------------------------
 *
 *              `x`   `<varstruct>`
 *        --------------------------------
 *          |- ?v1..vn. x = <varstruct>
 *
 *---------------------------------------------------------------------------*)

local val pthm = GSYM pairTheory.PAIR
in
fun PAIR_EX x vstruct =
 let fun pair_exists node value thm =
      if Term.is_var value
      then EXISTS (mk_exists(value,subst[node|->value] (concl thm)), node) thm
      else
      let val (V,(l,r)) = (I##dest_eq)(strip_exists(concl thm))
          val v = genvar(type_of node)
          val template = list_mk_exists(V,mk_eq(l, subst[node|->v] r))
          val expansion = ISPEC node pthm
          val pthm' = Thm.SUBST[v |-> expansion] template thm
          val (node1, node2) = dest_pair(rhs(concl expansion))
          val (value1,value2) = dest_pair value
      in pair_exists node1 value1 (pair_exists node2 value2 pthm')
      end
      handle HOL_ERR _ => raise PERR "PAIR_EX" ""
 in
   pair_exists x vstruct (REFL x)
 end
end



(*---------------------------------------------------------------------------
 * Generalize a free tuple (vstr) into a universally quantified variable (a).
 * There must be a faster way! Note however that the notion of "freeness" for
 * a tuple is different than for a variable: if variables in the tuple also
 * occur in any other place than an occurrences of the tuple, they aren't
 * "free" (which is thus probably the wrong word to use).
 *---------------------------------------------------------------------------*)

fun PGEN a vstr th =
   GEN a (if is_var vstr
          then Thm.INST [vstr |-> a] th
          else PROVE_HYP (PAIR_EX a vstr) (VSTRUCT_ABS (mk_eq(a,vstr)) th))

fun PGEN_TAC vars (asl:Term.term list,tm) =
 let val (v,_) = dest_forall tm
     val tm'   = beta_conv(mk_comb(rand tm,vars))
 in
   ([(asl,tm')], fn [th] => PGEN v vars th
                     | _ => raise PERR "PGEN_TAC" "validation")
 end;

(*---------------------------------------------------------------------------
       |- f <vstr> = g <vstr>
      ------------------------ PFUN_EQ_RULE
              |- f = g
 ---------------------------------------------------------------------------*)

local val expected = PERR "PFUN_EQ_RULE" "expected f <vstruct> = g <vstruct>"
      val SIMP = Rewrite.PURE_ONCE_REWRITE_RULE[GSYM FUN_EQ_THM]
in
fun PFUN_EQ_RULE th =
 let val ((_,v1),(_,v2))
       = with_exn ((dest_comb##dest_comb) o dest_eq o concl) th expected
 in if v1=v2
      then SIMP (PGEN (genvar (type_of v1)) v1 th)
      else raise expected
 end
end;


(*---------------------------------------------------------------------------*
 *            v    (|- !v_1...v_n. M[v_1...v_n])                             *
 *   TUPLE   -------------------------------------------------               *
 *              !v. M[FST v, FST(SND v), ... SND(SND ... v)]                 *
 *---------------------------------------------------------------------------*)

local fun trav tm A =
         trav (mk_fst tm) (trav (mk_snd tm) A) handle HOL_ERR _ => (tm::A)
in
fun TUPLE v thm = GEN v (SPECL (trav v []) thm)

fun TUPLE_TAC vtuple:tactic = fn (asl,w) =>
   let val (Bvar,Body) = dest_forall w
       val w1 = subst [Bvar |-> vtuple] Body
       val w2 = list_mk_forall(strip_pair vtuple,w1)
   in ([(asl,w2)],
       fn [th] => PURE_REWRITE_RULE[pairTheory.PAIR] (TUPLE Bvar th))
   end
end;


(*---------------------------------------------------------------------------
 * Builds a list of projection terms for "rhs", based on structure
 * of "tuple".

       fun flat_vstruct0 tuple rhs =
          if (is_var tuple) then [rhs]
          else let val {fst,snd} = dest_pair tuple
               in flat_vstruct0 fst (mk_fst rhs) @
                  flat_vstruct0 snd (mk_snd rhs)
               end;

 * That was the clean implementation. Now for the one that gets used, we
 * add an extra field to the return value, so that it can be made into
 * an equality.
 *---------------------------------------------------------------------------*)

fun flat_vstruct tuple rhs =
  let 
    (* behaviour of mk_fst and mk_snd should match PairedLambda.GEN_BETA_CONV in LET_INTRO *)
    val mk_fst = fn tm => if is_pair tm then #1 (dest_pair tm) else mk_fst tm
    val mk_snd = fn tm => if is_pair tm then #2 (dest_pair tm) else mk_snd tm
    fun flat tuple (v,rhs) =
      if is_var tuple then [(tuple, rhs)]
      else let val (fst,snd) = dest_pair tuple
           in  flat fst (v, mk_fst rhs) @
               flat snd (v, mk_snd rhs)
           end
  in map mk_eq (flat tuple (genvar alpha,rhs))
  end;


(*---------------------------------------------------------------------------
 *
 *              Gamma |- (<vstruct> = M) ==> N
 *     --------------------------------------------------
 *              Gamma |- let <vstruct> = M in N
 *
 *---------------------------------------------------------------------------*)

local val LET_THM1 = GSYM LET_THM
      val PAIR_RW = PURE_REWRITE_RULE [pairTheory.PAIR]
      fun lhs_repl th = (lhs(concl th) |-> th)
in
fun LET_INTRO thm =
  let val (ant,conseq) = dest_imp(concl thm)
      val (lhs,rhs) = dest_eq ant
      val bindings = flat_vstruct lhs rhs
      val thl = map ASSUME bindings
      val th0 = UNDISCH thm
      val th1 = SUBS thl th0
      val Bredex = mk_comb(mk_pabs(lhs,conseq),rhs)
      val th2 = EQ_MP (GSYM(PairedLambda.GEN_BETA_CONV Bredex)) th1
      val th3 = PURE_ONCE_REWRITE_RULE[LET_THM1] th2
      val vstruct_thm = SUBST_CONV (map lhs_repl thl) lhs lhs;
      val th4 = PROVE_HYP (PAIR_RW vstruct_thm) th3
  in
  rev_itlist (fn bind => fn th =>
                 let val th' = DISCH bind th
                     val (lhs,rhs) = dest_eq bind
                 in MP (Thm.INST [lhs |-> rhs] th') (REFL rhs) end)
               bindings th4
  end
end;


(*---------------------------------------------------------------------------
 * Returns the variants and the "away" list augmented with the variants.
 *---------------------------------------------------------------------------*)

fun unpabs tm =
   let val (vstr,body) = dest_pabs tm
       val V = free_vars_lr vstr
   in list_mk_abs(V,body)
   end;


local
fun dot 0 vstr tm away = (vstr,tm)
  | dot n vstr tm away =
    let val (Bvar,Body) = dest_abs tm
        val v' = variant away Bvar
        val tm'  = beta_conv(mk_comb(tm, v'))
        val vstr' = subst[Bvar |-> v'] vstr
    in dot (n-1) vstr' tm' (v'::away)
    end
in
(*---------------------------------------------------------------------------
 * Alpha convert to ensure that variables bound by the "let" are not
 * free in the assumptions of the goal. Alpha-convert in reverse on way
 * back from achieving the goal.
 *---------------------------------------------------------------------------*)

val LET_INTRO_TAC :tactic =
fn  (asl,w) =>
  let val (func,arg) = dest_let w
      val func' = unpabs func
      val (vstr,body) = dest_pabs func
      val away0 = Lib.op_union aconv (free_vars func) (free_varsl asl)
      val (vstr', body') = dot (length (free_vars vstr)) vstr func' away0
      val bind = mk_eq(vstr', arg)
  in
  ([(asl,mk_imp(bind,body'))],
   fn [th] => let val let_thm = LET_INTRO th
               in EQ_MP (ALPHA (concl let_thm) w) let_thm end)
  end
end;

(*---------------------------------------------------------------------------
 * Test.
 *
    set_goal([Term`x:bool`, Term`x':bool`],
             Term`let (x':bool,(x:bool)) = M in x'' x x' : bool`);
 *
 *
 *  g`!P x M N. (!x. x=M ==> P(N x)) ==> P(let (x = M) in N)`;
 *
 *---------------------------------------------------------------------------*)


fun LET_EQ_TAC thml =
  Ho_Rewrite.PURE_REWRITE_TAC thml
  THEN REPEAT (LET_INTRO_TAC THEN DISCH_TAC);

(*---------------------------------------------------------------------------
   Eliminate tupled quantification

       -----------------------------------  TUPLED_QUANT_CONV `<Q><vstr>. P`
       |- <Q><vstr>. P = <Q> v1 ... vn. P

   where <Q> is one of {?,!} and <vstruct> is a varstruct made
   from the variables v1,...,vn.

   This is slightly imprecise: some of the rewrites done by CONV will
   be attempted everywhere in the term. To make them happen just in
   the quantifier prefix is a little more work (but not much).
 ---------------------------------------------------------------------------*)


val is_uncurry_tm  = same_const pairSyntax.uncurry_tm
val is_universal   = same_const boolSyntax.universal
val is_existential = same_const boolSyntax.existential;


local
  val CONV = Ho_Rewrite.PURE_REWRITE_CONV [ELIM_UNCURRY] THENC
             DEPTH_CONV BETA_CONV THENC
             Ho_Rewrite.PURE_REWRITE_CONV [ELIM_PEXISTS,ELIM_PFORALL]
  fun dest_tupled_quant tm =
    case total dest_comb tm
     of NONE => NONE
      | SOME(f,x) =>
        if is_comb x andalso is_uncurry_tm (rator x)
        then if is_existential f then SOME (dest_exists, list_mk_exists) else
             if is_universal f   then SOME (dest_forall, list_mk_forall)
             else NONE
        else NONE
  fun ndest_quant dquant 0 tm = ([],tm)
    | ndest_quant dquant n tm = 
       let val (v,M) = dquant tm
           val (V,body) = ndest_quant dquant (n-1) M
       in (v::V,body)
       end
in
fun ELIM_TUPLED_QUANT_CONV tm =
 case dest_tupled_quant tm
  of NONE => raise PERR "TUPLED_QUANT_CONV" ""
   | SOME (dest_quant, list_mk_quant) =>
     let val V = strip_pair(fst(dest_pabs(rand tm)))
         val thm = CONV tm
         val rside = rhs (concl thm)
         val (W,body) = ndest_quant dest_quant (length V) rside
     in TRANS thm
          (ALPHA rside
              (list_mk_quant(V, subst(map2 (curry op|->) W V) body)))
 end
end ;

end
