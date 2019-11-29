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
