structure transferLib :> transferLib =
struct

open transferTheory FullUnify
val PART_MATCH' = mp_then.PART_MATCH'
val op $ = Portable.$

fun relconstraint_tm t =
    case dest_term t of
        CONST {Thy = "transfer", Name, ...} =>
          Name = "left_unique" orelse Name = "bitotal" orelse
          Name = "total" orelse Name = "bi_unique" orelse
          Name = "equalityp" orelse Name = "right_unique" orelse
          Name = "surj"
      | _ => false
fun is_relconstraint t =
    relconstraint_tm (rator t)

fun gen_tyvar_sigma (tys : hol_type list) =
    map (fn ty => {redex = ty, residue = gen_tyvar()}) tys

fun gen_tyvarify tm =
    Term.inst (gen_tyvar_sigma (type_vars_in_term tm)) tm

fun GEN_TYVARIFY th =
    let
      val tyvs = HOLset.addList(hyp_tyvars th, type_vars_in_term (concl th))
    in
      INST_TYPE (gen_tyvar_sigma (HOLset.listItems tyvs)) th
    end

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
type preterm = Preterm.preterm
type env = (term, preterm) Binarymap.dict * int
type 'a t = env -> env * 'a
fun getmap E = (E, #1 E)
val newconst : Preterm.preterm t = fn (vmap, i) =>
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

type ruledb = {
  left: thm Net.net,
  right : thm Net.net,
  safe : thm Net.net,
  bad : term Net.net
}

fun eliminate_with_unifier ctys th1 h th2 =
    (* h probably a hypothesis of th2; conclusion of th1 unifies with h;
       instantiate th1 and th2 so that PROVE_HYP th1' th2' produces a
       theorem that is th2 without an h

       ctys a list of type variables from th2 that should be held constant
     *)
    let
      val rule = GEN_TYVARIFY th1
      val cr_t = concl rule
      val mk_vartype = trace ("Vartype Format Complaint", 0) mk_vartype
    in
      case unify ctys [] (cr_t, h) Env.empty of
          NONE => NONE
        | SOME (E, ()) =>
          let
            val tyinst =
                Binarymap.foldl
                  (fn (s,ty,A) => {redex = mk_vartype s,
                                   residue = Env.lookup_ty E ty}::A)
                  []
                  (Env.triTY E)
            val tminst =
                Binarymap.foldl
                  (fn (v,tm,A) =>
                      {redex = v, residue = Env.lookup_tm E tm} :: A)
                  []
                  (Env.triTM E)
            val f = INST tminst o INST_TYPE tyinst
          in
            SOME (PROVE_HYP (f rule) (f th2))
          end
    end


fun addrule th ({left, right, safe, bad} : ruledb) =
    let
      val th = UNDISCH th handle HOL_ERR _ => th
    in
      { left = Net.enter (lhand (concl th), th) left,
        right = Net.enter (rand (concl th), th) right,
        safe = safe, bad = bad}
    end

fun addsafe th ({left,right,safe,bad} : ruledb) =
    { left = left, right = right, bad = bad,
      safe = Net.enter (concl th, th) safe }

fun addbad t ({left,right,safe,bad} : ruledb) : ruledb =
  { left = left, right = right, safe = safe,
    bad = Net.enter(t,t) bad }

fun lookup_rule cleftp (rdb:ruledb) t =
    let
      val n = if cleftp then #left rdb else #right rdb
      val t = if cleftp then lhand t else rand t
    in
      Net.lookup t n
    end

fun check cleftp (ruledb:ruledb) th =
    let
      infix +++
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
      fun sq >>- f = seq.flatten (seq.map f sq)
      fun sq1 +++ sq2 =
          case seq.cases sq1 of
              NONE => sq2
            | _ => sq1
      fun return x = seq.fromList [x]
      val fail = seq.empty
      val hs = hyp th
      fun u1 h th rule =
          case eliminate_with_unifier ctys rule h th of
              NONE => fail
            | SOME th' => return th'
      fun safe_recurse hs th =
          case hs of
              [] => return th
            | h::rest =>
              let
                val ths = Net.lookup h (#safe ruledb)
              in
                ((seq.fromList ths >>- u1 h th) +++ return th) >>-
                safe_recurse rest
              end
      fun bad_recurse hs th =
          case hs of
              [] => return th
            | h::rest =>
                if List.exists
                     (fn pat => can (match_term (gen_tyvarify pat)) h)
                     (Net.lookup h (#bad ruledb))
                then
                  fail
                else bad_recurse rest th
    in
      safe_recurse hs th >>- S (C bad_recurse) hyp
    end

fun resolve_relhyps cleftp rdb th =
    let
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
      fun sq >>- f = seq.flatten (seq.map f sq)
      fun return x = seq.fromList [x]
      val fail = seq.empty
      fun goodhyp h = not (is_relconstraint h)
    in
      case HOLset.find goodhyp (hypset th) of
          NONE => fail
        | SOME h =>
          let
            val candidate_rules = case lookup_rule cleftp rdb h of
                                      [] => [UNDISCH equalityp_applied]
                                    | xs => xs
            fun kont candidate_rule =
                case eliminate_with_unifier ctys candidate_rule h th of
                    NONE => fail
                  | SOME th' => return th'
          in
            seq.fromList candidate_rules >>- kont >>- check cleftp rdb
          end
    end

fun mksel cleftp = if cleftp then lhand else rand

fun boolhyp_tm cleftp h =
    case dest_term (mksel cleftp h) of
        CONST {Thy = "bool", Name, ...} =>
          Name = "/\\" orelse Name = "\\/" orelse Name = "~"
      | _ => false

local
  val eqty = alpha --> alpha --> bool
  val ABty = alpha --> beta --> bool
  val x = mk_var("x", alpha)
  val A = mk_var("A", eqty)
  val AB = mk_var("AB", ABty)
in
fun eliminate_booleans_and_equalities cleftp th =
    let
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
      val boolhyps = List.filter (boolhyp_tm cleftp) (hyp th)
      fun bh_recurse hs th =
          case hs of
              [] => th
            | h::rest =>
              let
                val eq = equalityp_applied
                           |> INST [A |-> genvar eqty, x |-> genvar alpha]
                           |> GEN_TYVARIFY |> UNDISCH
              in
                case eliminate_with_unifier ctys eq h th of
                    NONE => bh_recurse rest th
                  | SOME th' => bh_recurse rest th'
              end
      val bh_gone = th |> bh_recurse boolhyps
      fun is_eqhyp t =
          List.length (#2 (strip_comb t)) >= 2 andalso
          same_const equality (argsel t) handle HOL_ERR _ => false
      val eqhyps = List.filter is_eqhyp (hyp bh_gone)
      fun eq_recurse hs th =
          case hs of
              [] => th
            | h::rest =>
              let
                val eqr = EQ_bi_unique |> INST [AB |-> genvar ABty]
                                       |> GEN_TYVARIFY |> UNDISCH
              in
                case eliminate_with_unifier ctys eqr h th of
                    NONE => eq_recurse rest th
                  | SOME th' => eq_recurse rest th'
              end
    in
      eq_recurse eqhyps bh_gone
    end
end (* local *)

fun seqrpt f x =
    let
      val s1 = f x
    in
      case seq.cases s1 of
        NONE => seq.fromList [x]
      | SOME _ => seq.flatten (seq.map (seqrpt f) s1)
    end

val empty_rdb : ruledb =
   {left = Net.empty, right = Net.empty, safe = Net.empty, bad = Net.empty}

open pred_setTheory fsetsTheory

val ruledb = empty_rdb
               |> addrule fUNION_UNION
               |> addrule fIN_IN
               |> addrule fINSERT_INSERT
               |> addrule fupdate_correct
               |> addrule fEMPTY_EMPTY
               |> addrule EQ_bi_unique
               |> addrule UPAIR_COMMA
               |> addrule toSet_correct
               |> addrule ALL_IFF
               |> addrule ALL_total_RRANGE
               |> addrule ALL_total_iff_cimp
               |> addrule ALL_total_cimp_cimp
               |> addrule ALL_surj_RDOM
               |> addrule ALL_surj_iff_imp
               |> addrule ALL_surj_imp_imp
               |> addrule EXISTS_bitotal
               |> addrule EXISTS_total_iff_imp
               |> addrule EXISTS_total_imp_imp
               |> addrule EXISTS_surj_iff_cimp
               |> addrule EXISTS_surj_cimp_cimp
               |> addrule EXISTS_IFF_RDOM
               |> addrule EXISTS_IFF_RRANGE
               |> addrule UREL_EQ
               |> addrule PAIRU_COMMA
               |> addrule cimp_imp
               |> addrule (equalityp_applied
                             |> INST_TYPE [alpha |-> (bool --> bool --> bool)]
                             |> Q.INST [‘x’ |-> ‘(==>)’])
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                           equalityp_FUN_REL))
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                           bi_unique_implied))
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                           total_total_sets))
               |> addsafe eq_equalityp
               |> addsafe bi_unique_EQ
               |> addsafe bitotal_EQ
               |> addsafe total_EQ
               |> addsafe (SPEC_ALL EQ_REFL)
               |> addsafe (UNDISCH total_FSET)
               |> addsafe (UNDISCH left_unique_FSET)
               |> addsafe (UNDISCH right_unique_FSET)
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO] bi_unique_FSET))
               |> addbad “equalityp (==>)”
               |> addbad “equalityp (combin$C (==>))”
               |> addbad “bitotal (FSET AB)”
               |> addbad “surj (FSET AB)”

val notsing_empty = let
  val ct = concl NOT_SING_EMPTY
  val th0 = prove_relation_thm false ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities false
in
  seq.take 10 (seqrpt (resolve_relhyps false ruledb) th0)
end

val funion_comm = let
  val ct = “!f1 f2. fUNION f1 f2 = fUNION f2 f1”
  val th0 = prove_relation_thm true ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities true
in
  seq.take 10 (seqrpt (resolve_relhyps true ruledb) th0)
end

val IN_INTER_eq = let
  val ct = concl IN_INTER
  val th0 = prove_relation_thm false ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities false
in
  seq.take 10 (seqrpt (resolve_relhyps false ruledb) th0)
end

val union_commeg = let
  val ct = concl UNION_COMM
  val th0 = prove_relation_thm false ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities false
in
  seq.take 10 (seqrpt (resolve_relhyps false ruledb) th0)
end

val induct = let
  val ct = “!P. P FEMPTY /\ (!s e. ~fIN e s ==> P (fINSERT e s)) ==>
                !s. P s”
  val th0 = prove_relation_thm true ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities true
in
  seqrpt (resolve_relhyps true ruledb) th0 |> seq.take 10
end

(* doesn't get as far as you might like because you have no way of knowing
   that the set asserted to exist in the second disjunct should be finite *)
val cases1 = let
  val ct = concl SET_CASES
in
  ct |> build_skeleton |> prove_relation_thm false ct
     |> eliminate_booleans_and_equalities false
     |> seqrpt (resolve_relhyps false ruledb)
     |> seq.hd
end

val cases2 = let
  val ct = “!fs. fs = FEMPTY \/ ?e fs0. ~(fIN e fs0) /\ fs = fINSERT e fs0”
in
  ct |> build_skeleton |> prove_relation_thm true ct
     |> eliminate_booleans_and_equalities true
     |> seqrpt (resolve_relhyps true ruledb)
     |> seq.take 10
     |> map (SIMP_RULE (bool_ss ++ combinSimps.COMBIN_ss) [])
end


val induct_example = let
  val ct = concl FINITE_INDUCT
in
  prove_relation_thm false ct (build_skeleton ct)
end






end (* struct *)
