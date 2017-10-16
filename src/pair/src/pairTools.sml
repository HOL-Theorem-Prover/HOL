structure pairTools :> pairTools =
struct

open HolKernel Parse boolLib pairSyntax pairTheory PairRules;

val PERR = mk_HOL_ERR "pairTools";

(* recursively expand variables with pair type *)
local
  val name_of = fst o dest_var
  fun rename_tac v1 v2 =
    FULL_STRUCT_CASES_TAC
      (EXISTS (mk_exists(v2,(mk_eq(v1,v2))),v1) (REFL v1))
  fun split_tac p a d =
    FULL_STRUCT_CASES_TAC
      (CONV_RULE (RENAME_VARS_CONV [name_of a, name_of d])
         (ISPEC p pair_CASES))
in
  fun PairCases_on q g = let
    val fvs = free_varsl(snd g::fst g)
    val mk_var = variant fvs o mk_var
    val v = parse_in_context fvs q
  in
    if is_var v then let
      val (sv,ty) = dest_var v
      val n = let val n = ref 0 in fn()=> !n before n := !n+1 end
      fun split_tacs v tya tyd = let
        fun try_split s ty = let
          val v = mk_var((name_of v)^s,ty)
        in (v,
            case total dest_prod ty of
              NONE =>
                (fn()=> rename_tac v (mk_var(sv^(Int.toString(n())),ty)))
            | SOME (tya, tyd) =>
                (fn()=> split_tacs v tya tyd))
        end
        val (va,ka) = try_split "a" tya
        val (vd,kd) = try_split "d" tyd
      in
        split_tac v va vd
        THEN ka() THEN kd()
      end
    in
      case total dest_prod (type_of v) of
        NONE => raise PERR "PairCases_on" "Not of pair type"
      | SOME (tya, tyd) => split_tacs v tya tyd
    end g
    else raise PERR "PairCases_on" "Not a variable"
  end
end

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
 in
   if aconv v1 v2 then SIMP (PGEN (genvar (type_of v1)) v1 th)
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
      fun hd1 [th] = th
        | hd1 _ = raise Bind
in
fun TUPLE v thm = GEN v (SPECL (trav v []) thm)

fun TUPLE_TAC vtuple:tactic = fn (asl,w) =>
   let val (Bvar,Body) = dest_forall w
       val w1 = subst [Bvar |-> vtuple] Body
       val w2 = list_mk_forall(strip_pair vtuple,w1)
   in ([(asl,w2)],
       PURE_REWRITE_RULE[pairTheory.PAIR] o TUPLE Bvar o hd1)
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
   fn ths => let val let_thm = LET_INTRO (hd ths)
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
 * Eliminate PABS
 *

       -----------------------------------  PABS_ELIM_CONV (\<vstr>. P vstr)
       |- \<vstr>. P <vstr> = \x. P x
 *
 *---------------------------------------------------------------------------*)

local
   fun UNCURRY_ELIM_CONV t =
      ((REWR_CONV ELIM_UNCURRY) THENC
       (ABS_CONV (
          RATOR_CONV (
             ((RATOR_CONV UNCURRY_ELIM_CONV) THENC
             BETA_CONV THENC
             UNCURRY_ELIM_CONV)) THENC
          BETA_CONV))) t
      handle HOL_ERR _ => raise UNCHANGED;
in

fun PABS_ELIM_CONV t =
  if (pairSyntax.is_pabs t) then (UNCURRY_ELIM_CONV t) else raise UNCHANGED;

end


(*---------------------------------------------------------------------------
 * Introduces PABS
 *

       -----------------------------------  PABS_ELIM_CONV <vstr> (\x. P x)
       |- \x. P x = \<vstr>. P vstr
 *
 *---------------------------------------------------------------------------*)

fun PABS_INTRO_CONV vstruct tt = let
   val (vstruct', _) = variant_of_term (free_vars tt) vstruct
   val new_t = mk_comb (tt, vstruct')
   val thm0 = (BETA_CONV THENC
               REWRITE_CONV[pairTheory.FST, pairTheory.SND]) new_t

   val thm1 = PairRules.PABS vstruct' thm0
   val thm2 = CONV_RULE (LHS_CONV PairRules.PETA_CONV) thm1
in
   thm2
end;

(*---------------------------------------------------------------------------
   Eliminate tupled quantification

       -----------------------------------  TUPLED_QUANT_CONV `<Q><vstr>. P`
       |- <Q><vstr>. P = <Q> v1 ... vn. P

   where <Q> is one of {?,!} and <vstruct> is a varstruct made
   from the variables v1,...,vn.
 ---------------------------------------------------------------------------*)


val is_uncurry_tm  = same_const pairSyntax.uncurry_tm
val is_universal   = same_const boolSyntax.universal
val is_existential = same_const boolSyntax.existential;

local
  val ELIM_PEXISTS2 = prove (``(?p:('a#'b). P (FST p) (SND p) p) = ?p1 p2. P p1 p2 (p1,p2)``,
                         CONV_TAC (LHS_CONV (HO_REWR_CONV EXISTS_PROD)) THEN
                         REWRITE_TAC[FST, SND])
  val ELIM_PFORALL2 = prove (``(!p:('a#'b). P (FST p) (SND p) p) = !p1 p2. P p1 p2 (p1,p2)``,
                         CONV_TAC (LHS_CONV (HO_REWR_CONV FORALL_PROD)) THEN
                         REWRITE_TAC[FST, SND]);

  val ELIM_PEXISTS_CONV = HO_REWR_CONV ELIM_PEXISTS2;
  val ELIM_PFORALL_CONV = HO_REWR_CONV ELIM_PFORALL2;

  fun dest_tupled_quant tm =
    case total dest_comb tm
     of NONE => NONE
      | SOME(f,x) =>
        if is_comb x andalso is_uncurry_tm (rator x)
        then if is_existential f then SOME ELIM_PEXISTS_CONV else
             if is_universal f   then SOME ELIM_PFORALL_CONV
             else NONE
        else NONE

  fun PQUANT_ELIM_CONV quant_elim vc =
      if (is_var vc) then (RAND_CONV (ALPHA_CONV vc)) else
      let
         val (vc1, vc2) = pairSyntax.dest_pair vc;
         val conv = (quant_elim THENC
                    (QUANT_CONV (PQUANT_ELIM_CONV quant_elim vc2)) THENC
                    (PQUANT_ELIM_CONV quant_elim vc1));
      in
         conv
      end;
in
   fun ELIM_TUPLED_QUANT_CONV tm =
      case dest_tupled_quant tm
         of NONE => raise PERR "TUPLED_QUANT_CONV" ""
          | SOME (quant_elim) =>
               ((RAND_CONV PABS_ELIM_CONV) THENC
                PQUANT_ELIM_CONV quant_elim (fst (dest_pabs(rand tm)))) tm

   fun SPLIT_QUANT_CONV vc tm =
      let
         val quant_elim =
                 if is_universal (rator tm) then ELIM_PFORALL_CONV else
                 if is_existential (rator tm) then ELIM_PEXISTS_CONV else
                 raise PERR "SPLIT_QUANT_CONV" ""
         val (v, _) = dest_abs (rand tm) handle HOL_ERR _ => raise PERR "SPLIT_QUANT_CONV" ""
         val _ = if (type_of vc = type_of v) then () else raise PERR "SPLIT_QUANT_CONV" "";
      in
         PQUANT_ELIM_CONV quant_elim vc tm
      end;
end;



local
  val PFORALL_THM2 = prove (
    ``!P:'a->'b->bool. (!x. $! (P x)) = $! (UNCURRY P)``,
    GEN_TAC THEN
    Q.SUBGOAL_THEN `P = (\x y. P x y)`
       (fn thm => ONCE_ASM_REWRITE_TAC [thm])
    THEN1 (REWRITE_TAC [FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC[]) THEN
    BETA_TAC THEN REWRITE_TAC [PFORALL_THM]);

  val PEXISTS_THM2 = prove (
    ``!P:'a->'b->bool. (?x. $? (P x)) = $? (UNCURRY P)``,
    GEN_TAC THEN
    Q.SUBGOAL_THEN `P = (\x y. P x y)`
       (fn thm => ONCE_ASM_REWRITE_TAC [thm])
    THEN1 (REWRITE_TAC [FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC[]) THEN
    BETA_TAC THEN REWRITE_TAC [PEXISTS_THM]);
in
  fun PEXISTS_INTRO_CONV tm =
      (((TRY_CONV ELIM_TUPLED_QUANT_CONV) THENC
        (QUANT_CONV PEXISTS_INTRO_CONV) THENC
        (HO_REWR_CONV PEXISTS_THM2)) tm) handle HOL_ERR _ => raise UNCHANGED

  fun PFORALL_INTRO_CONV tm =
      (((TRY_CONV ELIM_TUPLED_QUANT_CONV) THENC
        (QUANT_CONV PFORALL_INTRO_CONV) THENC
        (HO_REWR_CONV PFORALL_THM2)) tm) handle HOL_ERR _ => raise UNCHANGED

  fun INTRO_TUPLED_QUANT_CONV tm =
      if is_universal (rator tm) then PFORALL_INTRO_CONV tm else
      if is_existential (rator tm) then PEXISTS_INTRO_CONV tm else
         raise PERR "INTRO_TUPLED_QUANT_CONV" ""
end;


end
