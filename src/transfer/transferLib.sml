structure transferLib :> transferLib =
struct

val PART_MATCH' = mp_then.PART_MATCH'
val op $ = Portable.$

datatype var_flavour = Unification | Constrained
fun flavour_to_pfx Unification = "U" | flavour_to_pfx Constrained = "C"
local
  val c = Counter.make()
  fun new_var flv vnm = flavour_to_pfx flv ^ vnm ^ Int.toString (c())
in
fun gspec_all flavour th =
    let
      val (vs, bod) = strip_forall $ concl th
      fun foldthis (v, th) =
          let
            val (nm, ty) = dest_var v
          in
            SPEC(mk_var(new_var flavour nm, ty)) th
          end
    in
      List.foldl foldthis th vs
    end
val GUSPEC_ALL = gspec_all Unification
fun gcspec_all t =
    let fun recurse A t =
            case Lib.total dest_forall t of
                NONE => (List.rev A, t)
              | SOME (v,bod) =>
                let
                  val (vnm, ty) = dest_var v
                  val v' = mk_var(new_var Constrained vnm, ty)
                in
                  recurse (v'::A) (subst[v |-> v'] bod)
                end
    in
      recurse [] t
    end
fun mk_uvar(nm,ty) = mk_var(new_var Unification nm, ty)
end
fun is_uvar v = String.sub(v |> dest_var |> #1, 0) = #"?" handle _ => false

fun pmk_const c =
    case Preterm.term_to_preterm [] c (Pretype.Env.empty) of
        errormonad.Some (_, pt) => pt
      | _ => raise Fail "No conversion"
val pconj = pmk_const boolSyntax.conjunction
val pdisj = pmk_const boolSyntax.disjunction
val piff =
    pmk_const (mk_thy_const{Name = "=", Thy = "min",
                            Ty = bool --> bool --> bool})
val pneg = pmk_const boolSyntax.negation
fun pmk_comb(t1,t2) = Preterm.Comb{Locn = locn.Loc_None, Rator = t1, Rand = t2}
fun plist_mk_comb(f, args) =
    case args of
        [] => f
      | pt::rest => plist_mk_comb(pmk_comb(f,pt), rest)

fun pmk_conj (pt1, pt2) = plist_mk_comb(pconj, [pt1, pt2])
fun pmk_disj (pt1, pt2) = plist_mk_comb(pdisj, [pt1, pt2])
fun pmk_neg pt = pmk_comb(pneg, pt)
fun pmk_var (nm, i) = Preterm.Var{Locn = locn.Loc_None,
                                  Name = nm, Ty = Pretype.UVar i}
fun pmk_abs (v, b) = Preterm.Abs{Body = b, Bvar = v, Locn = locn.Loc_None}

local
open stmonad
infix >* >>-
val op>>- =  op >-
fun (m1 >* m2) = lift2 (fn x => fn y => (x,y)) m1 m2
type env = (term, preterm) Binarymap.dict * int
type 'a t = env -> env * 'a
fun getmap E = (E, #1 E)
val newconst : preterm t = fn (vmap, i) =>
    ((vmap, i + 1), pmk_var("UC" ^ Int.toString i, i))
fun newvar bv (m:'a t) : (preterm * 'a) t = fn (vmap,i) =>
    let val pv = pmk_var("UV" ^ Int.toString i, i)
        val vmap' = Binarymap.insert(vmap, bv, pv)
        val ((vmap'',i'), result) = m (vmap', i + 1)
    in
      ((vmap, i'), (pv, result))
    end
in
val env0:env = (Binarymap.mkDict Term.compare, 0)
fun build_preterm ct : Preterm.preterm t =
  (* if is_conj ct then
    let
      val (cl,cr) = dest_conj ct
    in
      lift pmk_conj (build_preterm cl >* build_preterm cr)
    end
  else if is_neg ct then lift pmk_neg (build_preterm (dest_neg ct))
  else  *)
    let
      fun varmap ct e =
          case Binarymap.peek(e,ct) of
              NONE => raise Fail ("Free variable: "^term_to_string ct)
            | SOME pt => return pt
    in
      case dest_term ct of
          VAR _ => getmap >>- varmap ct
        | CONST _ => newconst
        | COMB(t1,t2) => lift pmk_comb (build_preterm t1 >* build_preterm t2)
        | LAMB(bv,body) => lift pmk_abs (newvar bv (build_preterm body))
    end
end (* local *)

fun dvty ty = ty |> dest_vartype |> (fn s => String.extract(s,1,NONE))
fun build_skeleton ct =
    let val ((_, i), pt) = build_preterm ct env0
        fun newify n ptye = if n <= 0 then ptye
                            else newify (n - 1) (#1 (Pretype.Env.new ptye))
        val ptyenv = newify i Pretype.Env.empty
        val tm =
            trace ("notify type variable guesses", 0)
                  (Preterm.smash (Preterm.typecheck NONE pt))
                  ptyenv
        val tyvars = type_vars_in_term tm
        val sigma = map (
              fn tyv => {
                redex = tyv, residue = mk_vartype ("'UU__" ^ dvty tyv)
              }
            ) tyvars
    in
      Term.inst sigma tm
    end

val FUN_REL_t = prim_mk_const{Thy = "transfer", Name = "FUN_REL"}
fun ty2relvar cleftp skty cty =
    if is_vartype skty then
      mk_var("RV" ^ dvty skty,
             if cleftp then cty --> skty -->bool
             else skty --> cty --> bool)
    else
      let val (skd,skr) = dom_rng skty
          val (cd, cr) = dom_rng cty
          val dR = ty2relvar cleftp skd cd
          val rR = ty2relvar cleftp skr cr
      in
        mk_icomb(mk_icomb(FUN_REL_t, dR), rR)
      end

val GFUN_REL_COMB = GEN_ALL FUN_REL_COMB
fun prove_relation_thm cleftp ct skt =
    let
      val argl = if cleftp then [ct, skt] else [skt, ct]
      val skty = type_of skt and cty = type_of ct
    in
      case dest_term ct of
          VAR _ => ASSUME (list_mk_comb(ty2relvar cleftp skty cty, argl))
        | CONST _ => ASSUME (list_mk_comb(ty2relvar cleftp skty cty, argl))
        | COMB(cf, cx) =>
          let
            val fthm = prove_relation_thm cleftp cf (rator skt)
            val xthm = prove_relation_thm cleftp cx (rand skt)
          in
            MATCH_MP GFUN_REL_COMB (CONJ fthm xthm)
          end
        | LAMB (cbv, cbod) =>
          let
            val (skbv, skbod) = dest_abs skt
            val brel = ty2relvar cleftp (type_of skbv) (type_of cbv)
            val b_asm_t =
                list_mk_comb(brel, if cleftp then [cbv, skbv] else [skbv, cbv])
            val bod_thm = prove_relation_thm cleftp cbod skbod
            val (lv,rv) = if cleftp then (cbv,skbv) else (skbv,cbv)
            val hyp_thm =
                bod_thm
                  |> CONV_RULE (FORK_CONV (UNBETA_CONV lv, UNBETA_CONV rv))
                  |> DISCH b_asm_t |> GENL [lv,rv]
          in
            EQ_MP (PART_MATCH lhs (GSYM FUN_REL_def) (concl hyp_thm)) hyp_thm
          end
    end

val notsing_empty = let
  val ct = concl NOT_SING_EMPTY
in
  prove_relation_thm false ct (build_skeleton ct)
end

val funion_comm = let
  val ct = “∀f1 f2. fUNION f1 f2 = fUNION f2 f1”
in
  prove_relation_thm true ct (build_skeleton ct)
end

val union_commeg = let
  val ct = concl UNION_COMM
in
  prove_relation_thm false ct (build_skeleton ct)
    |> INST_TYPE [alpha |-> beta,
                  “:'UU__a” |-> “:'a fset”,
                  “:'UU__b” |-> bool,
                  “:'UU__c” |-> bool,
                  “:'UU__d” |-> “:'a fset”,
                  “:'UU__e” |-> bool,
                  “:'UU__f” |-> “:'a fset”,
                  “:'UU__g” |-> “:'a fset”]
    |> Q.INST [
         ‘RVUU__a’ |-> ‘FSET AB’,
         ‘RVUU__b’ |-> ‘combin$C (==>)’,
         ‘RVUU__c’ |-> ‘combin$C (==>)’,
         ‘RVUU__d’ |-> ‘FSET AB’,
         ‘RVUU__e’ |-> ‘(=)’,
         ‘RVUU__f’ |-> ‘FSET AB’,
         ‘RVUU__g’ |-> ‘FSET AB’,
         ‘UC0’ |-> ‘(!)’, ‘UC2’ |-> ‘(!)’, ‘UC4’ |-> ‘(=)’,
         ‘UC5’ |-> ‘fUNION’, ‘UC6’ |-> ‘fUNION’
       ]
    |> PROVE_HYP fUNION_UNION
    |> PROVE_HYP (ALL_total_cimp_cimp |> INST_TYPE [alpha |-> “:'a fset”,
                                                    beta |-> “:'b set”]
                                      |> Q.INST [‘AB’ |-> ‘FSET AB'’]
                                      |> Q.INST [‘AB'’ |-> ‘AB’]
                                      |> UNDISCH)
    |> PROVE_HYP (ALL_total_iff_cimp |> INST_TYPE [alpha |-> “:'a fset”,
                                                    beta |-> “:'b set”]
                                      |> Q.INST [‘AB’ |-> ‘FSET AB'’]
                                      |> Q.INST [‘AB'’ |-> ‘AB’]
                                      |> UNDISCH)
    |> PROVE_HYP (UNDISCH total_FSET)
    |> PROVE_HYP (bi_unique_EQ  |> INST_TYPE [alpha |-> “:'a fset”,
                                                    beta |-> “:'b set”]
                                |> Q.INST [‘AB’ |-> ‘FSET AB'’]
                                |> Q.INST [‘AB'’ |-> ‘AB’]
                                |> UNDISCH)
    |> PROVE_HYP (UNDISCH bi_unique_FSET)
end

val ct = “∀P. P ∅ ∧ (∀s :: FINITE. ∀e. e ∉ s ⇒ P (e INSERT s)) ⇒
              ∀s :: FINITE. P s”


prove_relation_thm false ct (build_skeleton ct)

val induct_example = let
  val ct = concl FINITE_INDUCT
in
  prove_relation_thm false ct (build_skeleton ct)
    |> INST_TYPE [alpha |-> beta,
                  “:'UU__a” |-> “:'a fset”,
                  “:'UU__b” |-> bool,
                  “:'UU__c” |-> bool,
                  “:'UU__d” |-> bool,
                  “:'UU__e” |-> bool,
                  “:'UU__f” |-> bool,
                  “:'UU__g” |-> bool,
                  “:'UU__h” |-> bool,
                  “:'UU__i” |-> bool,
                  “:'UU__j” |-> bool,
                  “:'UU__k” |-> bool,
                  “:'UU__l” |-> alpha,
                  “:'UU__m” |-> bool,
                  “:'UU__n” |-> bool,
                  “:'UU__o” |-> bool,
                  “:'UU__p” |-> bool,
                  “:'UU__q” |-> bool
                 ]
    |> Q.INST [‘RVUU__a’ |-> ‘FSET AB’,
               ‘RVUU__b’ |-> ‘(=)’,
               ‘RVUU__c’ |-> ‘combin$C $==>’,
               ‘RVUU__d’ |-> ‘combin$C $==>’,
               ‘RVUU__f’ |-> ‘combin$C $==>’,
               ‘RVUU__l’ |-> ‘AB’,


               ‘UC0’ |-> ‘$!’,
               ‘UC2’ |-> ‘$==>’,
               ‘UC3’ |-> ‘$/\’,
               ‘UC4’ |-> ‘FEMPTY’,
               ‘UC5’ |-> ‘$!’,
               ‘UC7’ |-> ‘$==>’,
               ‘UC8’ |-> ‘$/\’,
               ‘UC9’ |-> ‘K T’,
               ‘UC10’ |-> ‘$!’,
               ‘UC12’ |-> ‘$==>’,
               ‘UC13’ |-> ‘$~’,
               ‘UC14’ |-> ‘fIN’,
               ‘UC15’ |-> ‘fINSERT’,
               ‘UC16’ |-> ‘$!’,
               ‘UC18’ |-> ‘$==>’,
               ‘UC19’ |-> ‘K T’
              ]

    |> PROVE_HYP fEMPTY_EMPTY |> PROVE_HYP (UNDISCH fINSERT_INSERT)
    |> SIMP_RULE (bool_ss ++ combinSimps.COMBIN_ss) []


fIN_IN

datatype sequent = SQ of term list * term
type validation = thm list -> thm
datatype 'a state = Unsolved | Progressed of 'a
datatype 'a tpf_tree =
  TPF of sequent (* conclusion *)
       * ('a tpf_tree list * term list * validation * 'a) state
         (* possible sub-trees *)

fun tree0 R leftp t =
    let
      val (ds, rng) = strip_fun (type_of R)
      val _ = rng = bool orelse raise Fail "Relation of bad type"
      val (d1,d2) = case ds of [ty1,ty2] => (ty1,ty2)
                             | _ => raise Fail "Relation of bad type"
      val c_t = if leftp then list_mk_comb(R, [t, mk_uvar("B", d2)])
                else list_mk_comb(R, [mk_uvar("A", d1), t])
    in
      TPF(SQ([], c_t), Unsolved)
    end

fun relconstraint_tm t =
    case dest_term t of
        CONST {Thy = "transfer", Name, ...} =>
          Name = "left_unique" orelse Name = "bitotal" orelse
          Name = "total" orelse Name = "bi_unique"
      | _ => false
fun is_relconstraint t =
    relconstraint_tm (rator t)




(* thm is : !vs. hyp1 /\ hyp2 /\ ... /\ hypn ==> R tm1 tm2 *)
(* hyps can be Rlns or side constraints *)
fun build_tree1 k leftp asms thm tm =
  let
    val seln_f = if leftp then lhand o #2 o dest_imp
                 else rand o #2 o dest_imp
    val thm_instance = PART_MATCH' seln_f thm tm |> BETA_RULE |> GUSPEC_ALL
    val (sgblock, sq_tm) =
        thm_instance |> concl |> strip_forall |> #2 |> dest_imp
  in
    TPF (SQ (asms, sq_tm), k thm_instance asms (strip_conj sgblock))
  end

fun dischvs vs th =
    case vs of
        [] => th
      | v::rest => (case List.find (free_in v) (hyp th) of
                        SOME h => dischvs rest (DISCH h th)
                      | NONE => raise Fail ("Can't find hyp mentioning: "^
                                            term_to_string v))


fun process1 asms t =
    if is_forall t then
      let val (vs', t') = gcspec_all t
          val (hs, c) = strip_imp t'
      in
        (SQ(tunion asms hs,c), fn th => th |> dischvs vs' |> GENL vs')
      end
    else
      (SQ(asms, t), fn th => th)

fun process_subgoals th asms ts =
    let
      fun recurse sqA scA fsA ts =
          case ts of
              [] => (List.rev sqA, List.rev scA, List.rev fsA)
            | t::rest =>
              if is_relconstraint t then
                recurse sqA (t::scA) (I :: fsA) rest
              else
                let val (sq,f) = process1 asms t
                in
                  recurse (sq::sqA) scA (f::fsA) rest
                end
      val (sqs, scs, fs) = recurse [] [] [] ts
      val scfns = List.tabulate(length scs, K (fn th => th))
      fun sq2pf sq = TPF (sq, Unsolved)
    in
      Progressed (map sq2pf sqs, scs,
                  fn ths => MATCH_MP th
                                     (LIST_CONJ (map (fn (f,x) => f x)
                                                     (ListPair.zip (fs, ths)))),
                  th)
    end




fun mapFirst f l =
    let
      fun recurse A l =
          case l of
              [] => NONE
            | h::t => case f h of
                          SOME h' => SOME (List.revAppend(A, h'::t))
                        | NONE => recurse (h::A) t
    in
      recurse [] l
    end

fun attack_left pft leftp th =
    case pft of
        TPF (SQ(hs,c), Unsolved) =>
          let
            val selfn = if leftp then lhand else rand
          in
            SOME (build_tree1 process_subgoals leftp hs th (selfn c))
          end
      | TPF (rsq, Progressed(pfts, scs, vfn, info)) =>
        case mapFirst (fn pft => attack_left pft leftp th) pfts of
            NONE => NONE
          | SOME pfts' => SOME (TPF (rsq, Progressed(pfts', scs, vfn, info)))

val t0 = valOf
           (attack_left (tree0 “combin$C (==>)” false (concl UNION_COMM)) false
                        all_cimp_cimp')
val SOME t1 = attack_left t0 false all_cimp_cimp'

local
  val p = mk_var("p", bool)
  val q = mk_var("q", bool)
  val iff = mk_eq(p,q)
  val c0 = combinTheory.C_DEF
             |> INST_TYPE [alpha |-> bool, beta |-> bool, gamma |-> bool]
             |> C AP_THM boolSyntax.implication |> C AP_THM p |> C AP_THM q
             |> BETA_RULE |> SYM
in
  val piffq_imp_pimpq = EQ_MP (ASSUME iff) (ASSUME p) |> DISCH p |> DISCH iff
  val piffq_imp_ppmiq =
      EQ_MP (SYM (ASSUME iff)) (ASSUME q) |> DISCH q
            |> EQ_MP c0 |> DISCH iff
end

fun transform th =
    th|> INST_TYPE [alpha |-> gen_tyvar(), beta |-> gen_tyvar()]
      |> SIMP_RULE bool_ss [FUN_REL_def, PULL_FORALL]
      |> SIMP_RULE bool_ss [AND_IMP_INTRO] |> GEN_ALL

val eq' = transform bi_unique_EQ

val t0 = valOf
           (attack_left (tree0 “combin$C (==>)” false (concl UNION_COMM)) false
                        all_cimp_cimp')
val SOME t1 = attack_left t0 false all_cimp_cimp'
val SOME t2 = attack_left t1 false (GEN_ALL piffq_imp_ppmiq)
val SOME t3 = attack_left t2 false eq'
val SOME t4 = attack_left t3 false (transform fUNION_UNION)

val f0 = tree0 “combin$C (==>)” false (concl FINITE_INDUCT)
val SOME f1 = attack_left f0 false all_cimp_cimp'
val SOME f2 = attack_left f1 false cimp_imp'
val SOME f3 = attack_left f2 false imp_conj'
val SOME f4 = attack_left f3 false (transform FUN_REL_COMB)

(*
val stage1' = check_stage1_match thm (tm, leftp) |> BETA_RULE |> guspec_all

*)

fun new_goals th = th |> dest_imp |> #1 |> strip_conj

(* val new1 = new_goals stage1' *)



val (rcs, others) = List.partition relconstraint new1

fun process_other tm =
    let
      val tm' = tm |> ASSUME |> gcspec_all |> concl
      val (h,c) = dest_imp tm'
    in
      map check_stage1_match ..



end (* struct *)
