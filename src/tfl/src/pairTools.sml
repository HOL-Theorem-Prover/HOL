structure pairTools :> pairTools =
struct

 open HolKernel Parse basicHol90Lib Let_conv boolTools;
 infix |-> --> ## THEN;

 type term = Term.term
 type thm = Thm.thm
 type conv = Abbrev.conv


 fun PERR func mesg = HOL_ERR{origin_structure = "PairTools",
                              origin_function = func, message = mesg};

(*---------------------------------------------------------------------------
 * Arbitrary abstraction handling.
 *---------------------------------------------------------------------------*)
fun mk_aabs(vstr,body) = mk_abs{Bvar=vstr,Body=body}
                         handle _ => mk_pabs{varstruct = vstr, body = body};

fun list_mk_aabs (vstrl,tm) =
    itlist (fn vstr => fn tm => mk_aabs(vstr,tm)) vstrl tm;

fun dest_aabs tm =
   let val {Bvar,Body} = dest_abs tm
   in (Bvar,Body)
   end handle _ => let val {varstruct,body} = dest_pabs tm
                   in (varstruct,body)
                   end;

fun strip_aabs tm =
   let val (vstr,body) = dest_aabs tm
       val (bvs, core) = strip_aabs body
   in (vstr::bvs, core)
   end
   handle _ => ([],tm);

val betaConv = Let_conv.GEN_BETA_CONV;

fun mk_fst tm =
  let val ty = type_of tm
      val {Tyop="prod",Args=[alpha,beta]} = dest_type ty
      val FST = mk_const{Name="FST", Ty=mk_type{Tyop="fun",Args=[ty,alpha]}}
  in
    mk_comb{Rator=FST, Rand = tm}
  end;

fun mk_snd tm =
  let val ty = type_of tm
      val {Tyop="prod",Args=[alpha,beta]} = dest_type ty
      val SND = mk_const{Name="SND", Ty=mk_type{Tyop="fun",Args=[ty,beta]}}
  in
    mk_comb{Rator=SND, Rand = tm}
  end;


(*---------------------------------------------------------------------------
 *
 *     (x = (v1,...,vn))       |- M[(v1,...,vn)]
 *    ---------------------------------------------
 *      ?v1 ... vn. x = (v1,...,vn) |- M[x]
 *
 *---------------------------------------------------------------------------*)
fun VSTRUCT_ABS bind th =
  let fun CHOOSER v (tm,thm) =
        let val ex_tm = mk_exists{Bvar=v,Body=tm}
        in (ex_tm, CHOOSE(v, ASSUME ex_tm) thm)
        end
      val L = rev (free_vars (Dsyntax.rhs bind))
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
     fun mk_eq (x,y) = Dsyntax.mk_eq{lhs=x, rhs=y}
     fun dest_pair M = let val {fst,snd} = Dsyntax.dest_pair M in (fst,snd) end
     fun mk_exists(v,M) = Dsyntax.mk_exists{Bvar=v, Body=M}
in
fun PAIR_EX x vstruct =
let fun pair_exists node value thm =
    if (is_var value)
    then EXISTS(mk_exists(value, subst[node|->value] (concl thm)), node) thm
    else
    let val (vlist,{lhs,rhs}) = (I##dest_eq)(strip_exists(concl thm))
        val v = genvar(type_of node)
        val template = list_mk_exists(vlist,mk_eq(lhs, subst[node|->v] rhs))
        val expansion = ISPEC node pthm
        val (node1, node2) = dest_pair(Dsyntax.rhs(concl expansion))
        val pthm' = SUBST[v |-> expansion] template thm
        val (value1,value2) = dest_pair value
    in pair_exists node1 value1 (pair_exists node2 value2 pthm')
    end handle _ => raise PERR "PAIR_EX" ""
in
  pair_exists x vstruct (REFL x)
end end



(*---------------------------------------------------------------------------
 * Generalize a free tuple (vstr) into a universally quantified variable (a).
 * There must be a faster way! Note however that the notion of "freeness" for
 * a tuple is different than for a variable: if variables in the tuple also
 * occur in any other place than an occurrences of the tuple, they aren't
 * "free" (which is thus probably the wrong word to use).
 *---------------------------------------------------------------------------*)

fun PGEN a vstr th =
   GEN a (if (is_var vstr)
          then INST [vstr |-> a] th
          else PROVE_HYP (PAIR_EX a vstr)
                         (VSTRUCT_ABS (mk_eq{lhs=a, rhs=vstr}) th));


(*---------------------------------------------------------------------------*
 *            v    (|- !v_1...v_n. M[v_1...v_n])                             *
 *   TUPLE   -------------------------------------------------               *
 *              !v. M[FST v, FST(SND v), ... SND(SND ... v)]                 *
 *---------------------------------------------------------------------------*)
local fun mk_comb(M,N) = Term.mk_comb{Rator=M,Rand=N}
      fun mk_const(s,ty) = Term.mk_const{Name=s,Ty=ty}
      fun trav tm =
        let fun itr tm A =
           let val ty = type_of tm
               val {Tyop = "prod", Args = [ty1,ty2]} = Type.dest_type ty
           in itr (mk_comb(mk_const("FST", ty-->ty1), tm))
                  (itr(mk_comb(mk_const("SND", ty-->ty2),tm)) A)
           end handle _ => (tm::A)
        in itr tm [] end
      fun full_strip_pair tm =
        let fun strip tm A =
            if (is_pair tm)
            then let val {fst,snd} = dest_pair tm
                  in strip fst (strip snd A) end
            else (tm::A)
        in strip tm [] end
in
fun TUPLE v thm = GEN v (SPECL (trav v) thm)
fun TUPLE_TAC vtuple:tactic = fn (asl,w) =>
   let val {Bvar,Body} = dest_forall w
       val w1 = Term.subst [Bvar |-> vtuple] Body
       val w2 = list_mk_forall(full_strip_pair vtuple,w1)
   in ([(asl,w2)],
       fn [th] => PURE_REWRITE_RULE[pairTheory.PAIR](TUPLE Bvar th))
   end
end;


(*---------------------------------------------------------------------------
 * Builds a list of projection terms for "rhs", based on structure
 * of "tuple". Not used.

fun flat_vstruct0 tuple rhs =
  if (is_var tuple) then [rhs]
  else let val {fst,snd} = dest_pair tuple
       in flat_vstruct0 fst (mk_fst rhs) @ flat_vstruct0 snd (mk_snd rhs)
       end;
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * That was the clean implementation. Now for the one that gets used, we
 * add an extra field to the return value, so that it can be made into
 * an equality.
 *---------------------------------------------------------------------------*)
local val dum = mk_var{Name="__dummy__", Ty=Type`:'a`}
      fun mk_eek(l,r)= Dsyntax.mk_eq{lhs=l, rhs=r}
in
fun flat_vstruct tuple rhs =
  let fun flat tuple (v,rhs) =
      if (is_var tuple) then [(tuple, rhs)]
      else let val {fst,snd} = dest_pair tuple
           in   flat fst (v, mk_fst rhs) @ flat snd (v, mk_snd rhs)
           end
  in map mk_eek (flat tuple (dum,rhs))
  end
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
      fun lhs_repl th = (Dsyntax.lhs(concl th) |-> th)
in
fun LET_INTRO thm =
  let val {ant,conseq} = dest_imp(concl thm)
      val {lhs,rhs} = dest_eq ant
      val bindings = flat_vstruct lhs rhs
      val thl = map ASSUME bindings
      val th0 = UNDISCH thm
      val th1 = SUBS thl th0
      val Bredex = mk_comb{Rator=mk_aabs(lhs,conseq),Rand=rhs}
      val th2 = EQ_MP (GSYM(GEN_BETA_CONV Bredex)) th1
      val th3 = PURE_ONCE_REWRITE_RULE[LET_THM1] th2
      val vstruct_thm = SUBST_CONV (map lhs_repl thl) lhs lhs;
      val th4 = PROVE_HYP (PAIR_RW vstruct_thm) th3
  in
  rev_itlist (fn bind => fn th =>
                 let val th' = DISCH bind th
                     val {lhs,rhs} = dest_eq bind
                 in MP (INST [lhs |-> rhs] th') (REFL rhs) end)
               bindings th4
  end
end;


(*---------------------------------------------------------------------------
 * Returns the variants and the "away" list augmented with the variants.
 *---------------------------------------------------------------------------*)
fun unpabs tm =
   let val (vstr,body) = dest_aabs tm
       val V = free_vars_lr vstr
   in list_mk_abs(V,body)
   end;


local
fun dot 0 vstr tm away = (vstr,tm)
  | dot n vstr tm away =
    let val {Bvar,Body} = dest_abs tm
        val v' = variant away Bvar
        val tm'  = beta_conv(mk_comb{Rator=tm, Rand=v'})
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
  let val {func,arg} = dest_let w
      val func' = unpabs func
      val (vstr,body) = dest_aabs func
      val away0 = Lib.op_union aconv (free_vars func) (free_varsl asl)
      val (vstr', body') = dot (length (free_vars vstr)) vstr func' away0
      val bind = mk_eq{lhs=vstr', rhs=arg}
  in
  ([(asl,mk_imp{ant=bind,conseq=body'})],
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


(*---------------------------------------------------------------------------
 * Handling lets
 *
 * The following is support for "pulling" lets to the top level of the term;
 * and a tactic that will then plunk the let-binding on the assumptions.
 * Pulling lets to the top level is done via higher-order rewriting.
 *---------------------------------------------------------------------------*)
val PULL_LET2 = prove
(Term`!(P:'c->bool) (M:'a#'b) N.
    P (let (x,y) = M in N x y) = (let (x,y) = M in P (N x y))`,
REWRITE_TAC[boolTheory.LET_DEF] THEN GEN_TAC
 THEN TUPLE_TAC(Term`(x,y):'a#'b`)
 THEN CONV_TAC (DEPTH_CONV GEN_BETA_CONV)
 THEN REWRITE_TAC[]);

val PULL_LET3X2 = prove
(Term`!(P:'g->bool) (M:('a#'b)#('c#'d)#('e#'f)) N.
    P (let ((v1,v2),(v3,v4),(v5,v6)) = M in N v1 v2 v3 v4 v5 v6)
 = (let ((v1,v2),(v3,v4),(v5,v6)) = M in P (N v1 v2 v3 v4 v5 v6))`,
REWRITE_TAC[boolTheory.LET_DEF] THEN GEN_TAC THEN BETA_TAC
 THEN TUPLE_TAC(Term`((v1,v2),(v3,v4),(v5,v6)):('a#'b)#('c#'d)#('e#'f)`)
 THEN CONV_TAC (DEPTH_CONV GEN_BETA_CONV)
 THEN REWRITE_TAC[]);

end;
