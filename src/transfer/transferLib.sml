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
  bad : term Net.net,
  DOMRNG_ss : thm list
}

fun collapse E =
    let
      val mk_vartype = trace ("Vartype Format Complaint", 0) mk_vartype
    in
      (Binarymap.foldl
         (fn (s,ty,A) => {redex=mk_vartype s, residue = Env.lookup_ty E ty}::A)
         []
         (Env.triTY E),
       Binarymap.foldl
         (fn (v,tm,A) => {redex = v, residue = Env.lookup_tm E tm} :: A)
         []
         (Env.triTM E))
    end

fun eliminate_with_unifier ctys th1 h th2 =
    (* h probably a hypothesis of th2; conclusion of th1 unifies with h;
       instantiate th1 and th2 so that PROVE_HYP th1' th2' produces a
       theorem that is th2 without an h

       ctys a list of type variables from th2 that should be held constant
     *)
    let
      val rule = GEN_TYVARIFY th1
      val cr_t = concl rule
    in
      case unify ctys [] (cr_t, h) Env.empty of
          NONE => NONE
        | SOME (E, ()) =>
          let
            val (tyinst,tminst) = collapse E
            val f = INST tminst o INST_TYPE tyinst
          in
            SOME (PROVE_HYP (f rule) (f th2))
          end
    end


fun addrule th ({left, right, safe, bad, DOMRNG_ss} : ruledb) =
    let
      val th = UNDISCH th handle HOL_ERR _ => th
    in
      { left = Net.enter (lhand (concl th), th) left,
        right = Net.enter (rand (concl th), th) right,
        safe = safe, bad = bad, DOMRNG_ss = DOMRNG_ss}
    end

fun addsafe th ({left,right,safe,bad,DOMRNG_ss} : ruledb) =
    { left = left, right = right, bad = bad, DOMRNG_ss = DOMRNG_ss,
      safe = Net.enter (concl th, th) safe }

fun addbad t ({left,right,safe,bad,DOMRNG_ss} : ruledb) : ruledb =
  { left = left, right = right, safe = safe, DOMRNG_ss = DOMRNG_ss,
    bad = Net.enter(t,t) bad }

fun add_domrng th ({left,right,safe,bad,DOMRNG_ss} :ruledb) : ruledb =
   {left = left, right = right, safe = safe, bad = bad,
    DOMRNG_ss = th :: DOMRNG_ss}

fun lookup_rule cleftp (rdb:ruledb) t =
    let
      val n = if cleftp then #left rdb else #right rdb
      val t = if cleftp then lhand t else rand t
    in
      Net.lookup t n
    end

infix ~>
fun sq ~> f = seq.flatten (seq.map f sq)

fun check {cleftp,forceprogress} (ruledb:ruledb) th =
    let
      infix +++
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
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
            | SOME th' => return (true, th')
      fun safe_recurse hs (progressed,th) =
          case hs of
              [] => return (progressed,th)
            | h::rest =>
              let
                val ths = Net.lookup h (#safe ruledb)
              in
                ((seq.fromList ths ~> u1 h th) +++ return (progressed, th)) ~>
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
      fun assertprogress (p, th) = if not p andalso forceprogress then fail
                                   else return th
    in
      safe_recurse hs (false,th) ~> assertprogress ~> S (C bad_recurse) hyp
    end

fun resolve_relhyps cleftp rdb th =
    let
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
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
            seq.fromList candidate_rules ~> kont ~>
            check {cleftp=cleftp,forceprogress=false} rdb
          end
    end

fun mksel cleftp = if cleftp then lhand else rand

fun boolhyp_tm cleftp h =
    case dest_term (mksel cleftp h) of
        CONST {Thy = "bool", Name, ...} =>
          Name = "/\\" orelse Name = "\\/" orelse Name = "~"
      | _ => false

fun mkrelsyms_eq cleftp th =
    let
      val ctys = type_vars_in_term (th |> concl |> mksel cleftp)
      fun instv (v, th) =
          case unify ctys [] (gen_tyvarify boolSyntax.equality, v) Env.empty of
              NONE => th
            | SOME (E, _) =>
              let
                val (tyi,tmi) = collapse E
              in
                th |> INST_TYPE tyi |> INST tmi
              end
    in
      HOLset.foldl instv th (hyp_frees th)
    end

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

fun seqrptUntil P f x =
    if P x then seq.fromList [x]
    else f x ~> seqrptUntil P f

fun seqrpt f x = seqrptUntil (List.all is_relconstraint o hyp) f x

val empty_rdb : ruledb =
   {left = Net.empty, right = Net.empty, safe = Net.empty, bad = Net.empty,
    DOMRNG_ss = []}

open pred_setTheory fsetsTheory

val RES_FORALL_RRANGE =
    RES_FORALL_THM
      |> INST_TYPE [alpha |-> beta]
      |> SPEC (mk_comb(prim_mk_const{Thy = "relation", Name = "RRANGE"},
                       mk_var("P", alpha --> beta --> bool)))
      |> REWRITE_RULE [pred_setTheory.SPECIFICATION]
val RES_FORALL_RDOM =
    RES_FORALL_THM
      |> SPEC (mk_comb(prim_mk_const{Thy = "relation", Name = "RDOM"},
                       mk_var("P", alpha --> beta --> bool)))
      |> REWRITE_RULE [pred_setTheory.SPECIFICATION]
val RES_EXISTS_RRANGE =
    RES_EXISTS_THM
      |> INST_TYPE [alpha |-> beta]
      |> SPEC (mk_comb(prim_mk_const{Thy = "relation", Name = "RRANGE"},
                       mk_var("P", alpha --> beta --> bool)))
      |> REWRITE_RULE [pred_setTheory.SPECIFICATION]
val RES_EXISTS_RDOM =
    RES_EXISTS_THM
      |> SPEC (mk_comb(prim_mk_const{Thy = "relation", Name = "RDOM"},
                       mk_var("P", alpha --> beta --> bool)))
      |> REWRITE_RULE [pred_setTheory.SPECIFICATION]


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
                                           bitotal_implied))
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                           total_total_sets))
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                           surj_sets))
               |> addsafe eq_equalityp
               |> addsafe bi_unique_EQ
               |> addsafe bitotal_EQ
               |> addsafe total_EQ
               |> addsafe left_unique_EQ
               |> addsafe right_unique_EQ
               |> addsafe surj_EQ
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
               |> add_domrng RRANGE_EQ
               |> add_domrng RDOM_EQ
               |> add_domrng RRANGE_FSET_EQ
               |> add_domrng RDOM_FSET_EQ
               |> add_domrng RES_EXISTS_RDOM
               |> add_domrng RES_EXISTS_RRANGE
               |> add_domrng RES_FORALL_RDOM
               |> add_domrng RES_FORALL_RRANGE

fun search_for P depth sq =
    let
      val (default, sq') = case seq.cases sq of
                               NONE => raise Fail "No theorems!"
                             | SOME (th, rest) => (th, rest)
      fun recurse i sq =
          if i > depth then default
          else
            case seq.cases sq of
                NONE => default
              | SOME (th, rest) => if P (concl th) then th
                                   else recurse (i + 1) rest
    in
      recurse (depth - 1) sq'
    end

fun const_occurs c = can (find_term (same_const c))
val RRANGE_tm = prim_mk_const{Thy = "relation", Name = "RRANGE"}
val RDOM_tm = prim_mk_const{Thy = "relation", Name = "RDOM"}

fun base_transfer cleftp ruledb t =
    let
      val th0 = prove_relation_thm cleftp t (build_skeleton t)
                                   |> eliminate_booleans_and_equalities cleftp
    in
      seqrpt (resolve_relhyps cleftp ruledb) th0 ~>
      seqrptUntil (List.all (is_var o rand) o hyp)
                  (check{cleftp=cleftp,forceprogress=true} ruledb) |>
      seq.map (mkrelsyms_eq cleftp) ~>
      check {cleftp=cleftp,forceprogress=false} ruledb |>
      seq.map
        (SIMP_RULE (bool_ss ++ combinSimps.COMBIN_ss) (#DOMRNG_ss ruledb)) |>
      seq.filter (not o const_occurs RRANGE_tm o concl) |>
      seq.filter (not o const_occurs RDOM_tm o concl)
    end

fun transfer_tm depth cleftp ruledb t =
    base_transfer cleftp ruledb t |> search_for is_eq depth

fun transfer_thm depth cleftp ruledb th =
    let
      fun goodconcl c =
          is_eq c orelse
          aconv (#1 (dest_imp c)) (concl th) handle HOL_ERR _ => false
      val th0 = base_transfer cleftp ruledb (concl th)
                              |> search_for goodconcl depth
    in
      if is_eq (concl th0) then
        if cleftp then EQ_MP th0 th else EQ_MP (SYM th0) th
      else MP th0 th
    end

val notsing_empty = transfer_thm 4 false ruledb NOT_SING_EMPTY
val funion_comm1 = transfer_thm 4 false ruledb UNION_COMM
val funion_comm2 =
    transfer_tm 4 true ruledb “!f1 f2. fUNION f1 f2 = fUNION f2 f1”

(*
val IN_INTER_eq = let
  val ct = concl IN_INTER
  val th0 = prove_relation_thm false ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities false
in
  seqrpt (resolve_relhyps false ruledb) th0 ~>
  seqrptUntil (List.all (is_var o rand) o hyp)
              (check{cleftp=false,forceprogress=true} ruledb) |> seq.hd
end *)

val induct =
    transfer_tm 4 true ruledb
                “!P. P FEMPTY /\ (!s e. ~fIN e s ==> P (fINSERT e s)) ==>
                     !s. P s”

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

val cases2 =
    transfer_tm 4 true ruledb
                “!fs. fs = FEMPTY \/ ?e fs0. ~(fIN e fs0) /\ fs = fINSERT e fs0”

(*
Definition o2n_def:
  o2n s = FUN_FMAP (K ()) s
End

Definition n2o_def:
  n2o fm = FDOM fm
End

Theorem tydef:
  (!s. FINITE s <=> (n2o (o2n s) = s)) /\
  (!fm. o2n (n2o fm) = fm)
Proof
  simp[n2o_def, o2n_def] >> conj_tac
  >- (qx_gen_tac ‘s’ >> Cases_on ‘FINITE s’ >> simp[] >> strip_tac >>
      metis_tac[finite_mapTheory.FDOM_FINITE]) >>
  simp[finite_mapTheory.fmap_EXT]
QED

Theorem o2n_thm:
  FSET $= b a ==> o2n a = b
Proof
  simp[FSET_def, o2n_def, finite_mapTheory.fmap_EXT] >> strip_tac >>
  rename [‘fIN _ fm <=> _ IN s’] >>
  ‘FINITE s’ suffices_by simp[pred_setTheory.EXTENSION] >>
  ‘s = FDOM fm’ suffices_by simp[] >> simp[pred_setTheory.EXTENSION]
QED

Theorem n2o_thm:
  FSET $= fm (n2o fm)
Proof
  simp[FSET_def, n2o_def]
QED

Theorem FSETR_eq:
  FSET $= O inv (FSET $=) = (\s1 s2. FINITE s1 /\ s1 = s2)
Proof
  simp[Ntimes FUN_EQ_THM 2, FSET_def, relationTheory.O_DEF,
       relationTheory.inv_DEF] >> rw[Once EQ_IMP_THM]
  >- (rename [‘FINITE s’, ‘fIN _ fm <=> _ IN s’] >>
      ‘s = FDOM fm’ suffices_by simp[] >>
      simp[pred_setTheory.EXTENSION] >> metis_tac[])
  >- (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  rename [‘FINITE s’]>> qexists_tac ‘FUN_FMAP (K ()) s’ >>
  simp[]
QED


Definition fmi_def:
  fmi fs1 fs2 = o2n (n2o fs1 INTER n2o fs2)
End

Theorem fmi_correct:
  (FSET $= ===> FSET $= ===> FSET $=) fmi $INTER
Proof
  simp[FUN_REL_def, fmi_def]
*)

end (* struct *)
