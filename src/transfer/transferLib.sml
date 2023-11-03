structure transferLib :> transferLib =
struct

open HolKernel boolLib
open transferTheory FullUnify
val op $ = Portable.$

val SIMP_CONV = simpLib.SIMP_CONV
val SIMP_RULE = simpLib.SIMP_RULE
val transfer_ss = simpLib.++(boolSimps.bool_ss, combinSimps.COMBIN_ss)

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
      if numSyntax.is_numeral ct then
        newconst
      else
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
          val sigma = match_type (alpha --> beta --> bool) (type_of dR) @
                      match_type (gamma --> delta --> bool) (type_of rR)
      in
        mk_comb(mk_comb(FUN_REL_t |> inst sigma, dR), rR)
      end

val GFUN_REL_COMB = GEN_ALL FUN_REL_COMB
fun prove_relation_thm cleftp ct skt =
    let
      val argl = if cleftp then [ct, skt] else [skt, ct]
      val skty = type_of skt and cty = type_of ct
    in
      if numSyntax.is_numeral ct then
        ASSUME (list_mk_comb(ty2relvar cleftp skty cty, argl))
      else
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
                  list_mk_comb(brel,
                               if cleftp then [cbv, skbv] else [skbv, cbv])
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

structure ruledb =
struct
type t = {
  left: thm Net.net,
  right : thm Net.net,
  safe : thm Net.net,
  bad : term Net.net,
  DOMRNG_ss : thm list
}

val empty_rdb : t =
   {left = Net.empty, right = Net.empty, safe = Net.empty, bad = Net.empty,
    DOMRNG_ss = []}

fun fupd_left f ({left,right,safe,bad,DOMRNG_ss}:t) : t =
  {left = f left, right = right, safe = safe, bad = bad, DOMRNG_ss = DOMRNG_ss}

fun fupd_right f ({left,right,safe,bad,DOMRNG_ss}:t) : t =
  {left = left, right = f right, safe = safe, bad = bad, DOMRNG_ss = DOMRNG_ss}

fun fupd_safe f ({left,right,safe,bad,DOMRNG_ss}:t) : t =
  {left = left, right = right, safe = f safe, bad = bad, DOMRNG_ss = DOMRNG_ss}

fun fupd_bad f ({left,right,safe,bad,DOMRNG_ss}:t) : t =
  {left = left, right = right, safe = safe, bad = f bad, DOMRNG_ss = DOMRNG_ss}

fun fupd_DOMRNG_ss f ({left,right,safe,bad,DOMRNG_ss}:t) : t =
  {left = left, right = right, safe = safe, bad = bad, DOMRNG_ss = f DOMRNG_ss}

fun addrule0 (th, r) =
    let
      val th = UNDISCH_ALL th handle HOL_ERR _ => th
    in
      r |> fupd_left (Net.enter (lhand (concl th), th))
        |> fupd_right(Net.enter (rand (concl th), th))
    end

fun addrule th r = List.foldl addrule0 r (CONJUNCTS th)

fun addsafe th r = r |> fupd_safe (Net.enter (concl th, th))
fun addbad t r = r |> fupd_bad (Net.enter(t,t))
fun add_domrng th r = r |> fupd_DOMRNG_ss (cons th)

fun lookup_rule cleftp (rdb:t) t =
    let
      val n = if cleftp then #left rdb else #right rdb
      val t = if cleftp then lhand t else rand t
    in
      Net.lookup t n
    end

end (* ruledb struct *)

fun eliminate_with_unifier ctys th1 h th2 =
    (* h probably a hypothesis of th2; conclusion of th1 unifies with h;
       instantiate th1 and th2 so that PROVE_HYP th1' th2' produces a
       theorem that is th2 without an h

       ctys a list of type variables from th2 that should be held constant
     *)
    let
      open optmonad
      val rule = FULL_GEN_TYVARIFY th1
      val cr_t = concl rule
    in
      case Env.fromEmpty (unify ctys [] (cr_t, h) >> collapse) of
          NONE => NONE
        | SOME (tyinst,tminst) =>
          let
            val f = INST tminst o INST_TYPE tyinst
          in
            SOME (PROVE_HYP (f rule) (f th2))
          end
    end


infix ~>
fun sq ~> f = seq.flatten (seq.map f sq)
fun sqreturn x = seq.fromList [x]

fun check {cleftp,forceprogress} (ruledb:ruledb.t) th =
    let
      infix +++
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
      fun sq1 +++ sq2 =
          case seq.cases sq1 of
              NONE => sq2
            | _ => sq1
      val fail = seq.empty
      val hs = hyp th
      fun u1 h th rule =
          case eliminate_with_unifier ctys rule h th of
              NONE => fail
            | SOME th' => sqreturn (true, th')
      fun safe_recurse hs (progressed,th) =
          case hs of
              [] => sqreturn (progressed,th)
            | h::rest =>
              let
                val ths = Net.lookup h (#safe ruledb)
              in
                ((seq.fromList ths ~> u1 h th) +++ sqreturn (progressed, th)) ~>
                safe_recurse rest
              end
      fun bad_recurse hs th =
          case hs of
              [] => sqreturn th
            | h::rest =>
                if List.exists
                     (fn pat => can (match_term (gen_tyvarify pat)) h)
                     (Net.lookup h (#bad ruledb))
                then
                  fail
                else bad_recurse rest th
      fun simphyp (h, th) =
          if not (is_relconstraint h) then th
          else
            let
              val hth = SIMP_CONV transfer_ss (#DOMRNG_ss ruledb) h
            in
              if rhs (concl hth) ~~ T then
                PROVE_HYP (EQT_ELIM hth) th
              else
                PROVE_HYP (EQ_IMP_RULE hth |> #2 |> UNDISCH) th
            end handle UNCHANGED => th | HOL_ERR _ => th
      fun simphyps th = sqreturn (List.foldl simphyp th (hyp th))
      fun assertprogress (p, th) = if not p andalso forceprogress then fail
                                   else sqreturn th
    in
      safe_recurse hs (false,th) ~> assertprogress ~> simphyps ~>
      S (C bad_recurse) hyp
    end

fun check_constraints cleftp rdb th =
    check{cleftp=cleftp,forceprogress=false} rdb th

fun resolve_relhyps hints cleftp rdb th =
    let
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
      val fail = seq.empty
      fun goodname nm t = #Name (dest_thy_const (argsel t)) = nm
                          handle HOL_ERR _ => false
      fun goodhyp h = not (is_relconstraint h)
      val goods0 = HOLset.filter goodhyp (hypset th)
      fun check_hints [] s = HOLset.find (K true) s
        | check_hints (h::hs) s =
          case HOLset.find (goodname h) s of
              NONE => check_hints hs s
            | SOME hy => SOME hy
    in
      if HOLset.isEmpty goods0 then fail
      else
        case check_hints hints goods0 of
            NONE => fail
          | SOME h =>
            let
              val candidate_rules =
                  case ruledb.lookup_rule cleftp rdb h of
                      [] => [UNDISCH equalityp_applied]
                    | ths => ths @ [UNDISCH equalityp_applied]

              fun kont candidate_rule =
                  case eliminate_with_unifier ctys candidate_rule h th of
                      NONE => fail
                    | SOME th' => sqreturn th'
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
      open optmonad
      val ctys = type_vars_in_term (th |> concl |> mksel cleftp)
      fun instv (v, th) =
          case Env.fromEmpty
                 (unify ctys [] (gen_tyvarify boolSyntax.equality, v) >>
                  collapse)
           of
              NONE => th
            | SOME (tyi, tmi) => th |> INST_TYPE tyi |> INST tmi
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
                           |> FULL_GEN_TYVARIFY |> UNDISCH
              in
                case eliminate_with_unifier ctys eq h th of
                    NONE => bh_recurse rest th
                  | SOME th' => bh_recurse rest th'
              end
    in
      th |> bh_recurse boolhyps
    end
end (* local *)

fun seqrptUntil P f x =
    if P x then seq.fromList [x]
    else f x ~> seqrptUntil P f

fun seqrpt f x = seqrptUntil (List.all is_relconstraint o hyp) f x

open pred_setTheory

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


val equalityp_tm = prim_mk_const{Name = "equalityp", Thy = "transfer"}
val right_unique_tm = prim_mk_const{Name = "right_unique", Thy = "transfer"}
val cimp_tm = mk_icomb(combinSyntax.C_tm, boolSyntax.implication)

val ruledb =
    let
      open ruledb
    in
      empty_rdb
        |> addrule EQ_bi_unique
        |> addrule UPAIR_COMMA
        |> addrule ALL_total_iff_cimp
        |> addrule ALL_total_cimp_cimp
        |> addrule ALL_surj_iff_imp
        |> addrule ALL_surj_imp_imp
        |> addrule ALL_IFF
        |> addrule ALL_surj_RDOM
        |> addrule ALL_total_RRANGE
        |> addrule EXISTS_total_iff_imp
        |> addrule EXISTS_total_imp_imp
        |> addrule EXISTS_surj_iff_cimp
        |> addrule EXISTS_surj_cimp_cimp
        |> addrule EXISTS_IFF_RDOM
        |> addrule EXISTS_IFF_RRANGE
        |> addrule EXISTS_bitotal
        |> addrule UREL_EQ
        |> addrule PAIRU_COMMA
        |> addrule pair_CASE_CONG
        |> addrule LET_rule
        |> addrule FST_CORRECT
        |> addrule SND_CORRECT
        |> addrule COMMA_CORRECT
        |> addrule option_CASE_CONG
        |> addrule list_CASE_CONG
        |> addrule cimp_imp
        |> addrule (equalityp_applied
                      |> INST_TYPE [alpha |-> (bool --> bool --> bool)]
                      |> INST [mk_var("x", bool --> bool --> bool) |->
                               boolSyntax.implication])
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
        |> addsafe LIST_REL_surj
        |> addsafe LIST_REL_total
        |> addsafe LIST_REL_right_unique
        |> addbad (mk_icomb(equalityp_tm, boolSyntax.implication))
        |> addbad (mk_icomb(equalityp_tm, cimp_tm))
        |> addbad (mk_icomb(right_unique_tm, boolSyntax.implication))
        |> addbad (mk_icomb(right_unique_tm, cimp_tm))
        |> add_domrng RRANGE_EQ
        |> add_domrng RDOM_EQ
        |> add_domrng RES_EXISTS_RDOM
        |> add_domrng RES_EXISTS_RRANGE
        |> add_domrng RES_FORALL_RDOM
        |> add_domrng RES_FORALL_RRANGE
        |> add_domrng FUN_REL_EQ2
    end (* let *)

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
      recurse 1 sq'
    end

fun const_occurs c = can (find_term (same_const c))
val RRANGE_tm = prim_mk_const{Thy = "relation", Name = "RRANGE"}
val RDOM_tm = prim_mk_const{Thy = "relation", Name = "RDOM"}

fun transfer_skeleton cleftp t =
    let val th0 = prove_relation_thm cleftp t (build_skeleton t)
    in
      (* eliminate_booleans_and_equalities cleftp *) th0
    end

fun resolveN n hints cleftp ruledb t =
    let
      fun recurse n th =
          if n < 1 then sqreturn th
          else resolve_relhyps hints cleftp ruledb th ~> recurse (n - 1)
    in
      recurse n (transfer_skeleton cleftp t)
    end

fun transfer_phase1 hints cleftp ruledb t =
    let
      open simpLib boolSimps
    in
      seqrpt (resolve_relhyps hints cleftp ruledb)
             (transfer_skeleton cleftp t) ~>
      seqrptUntil (List.all (is_var o rand) o hyp)
                  (check{cleftp=cleftp,forceprogress=true} ruledb)
    end

fun eliminate_domrng cleftp ruledb =
    let
      val argsel = if cleftp then RAND_CONV else LAND_CONV
    in
      CONV_RULE (argsel $ SIMP_CONV transfer_ss (#DOMRNG_ss ruledb))
    end

fun base_transfer hints cleftp ruledb t =
    let
      open simpLib boolSimps
      val argsel = if cleftp then RAND_CONV else LAND_CONV
    in
      transfer_phase1 hints cleftp ruledb t |>
      seq.map (mkrelsyms_eq cleftp) ~>
      check {cleftp=cleftp,forceprogress=false} ruledb |>
      seq.map (eliminate_domrng cleftp ruledb) |>
      seq.filter (not o const_occurs RRANGE_tm o concl) |>
      seq.filter (not o const_occurs RDOM_tm o concl)
    end

fun transfer_tm depth hints cleftp ruledb t =
    base_transfer hints cleftp ruledb t |> search_for is_eq depth

fun transfer_thm depth hints cleftp ruledb th =
    let
      fun goodconcl c =
          is_eq c orelse
          aconv (#1 (dest_imp c)) (concl th) handle HOL_ERR _ => false
      val th0 = base_transfer hints cleftp ruledb (concl th)
                              |> search_for goodconcl depth
    in
      if is_eq (concl th0) then
        if cleftp then EQ_MP th0 th else EQ_MP (SYM th0) th
      else MP th0 th
    end

val default_depth = Sref.new 4
val the_ruledb = Sref.new ruledb
fun xfer_back_tac hints (g as (asl,c)) =
    let
      val th = transfer_tm (Sref.value default_depth) hints false
                           (Sref.value the_ruledb) c
      val con = concl th
      val mkE = mk_HOL_ERR "transferLib" "xfer_back_tac"
    in
      if aconv con c then ACCEPT_TAC th g
      else if is_imp con then
        if aconv (rand con) c then
          if aconv (lhand con) c then
            raise mkE "Derived p ==> p implication"
          else Tactic.MATCH_MP_TAC th g
        else raise mkE "Derived an implication, but conclusion <> goal"
      else if is_eq con andalso aconv (rand con) c then
        if aconv (lhand con) c then raise mkE "Derived p <=> p equality"
        else CONV_TAC (REWR_CONV (SYM th)) g
      else raise mkE ("Derived non-equality, non-implication: "^
                      term_to_string con)
    end

open ruledb
fun not_ceq th1 th2 = concl th1 !~ concl th2
fun temp_add_rule th = Sref.update the_ruledb (addrule th)
fun temp_add_safe th =
    Sref.update the_ruledb
            (addsafe (UNDISCH_ALL (PURE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))
fun temp_add_simp th = Sref.update the_ruledb (add_domrng th)
fun temp_remove_rule th =
    Sref.update the_ruledb (fupd_left (Net.filter (not_ceq th)) o
                            fupd_right (Net.filter (not_ceq th)))
fun temp_remove_safe th =
    Sref.update the_ruledb (fupd_left (Net.filter (not_ceq th)) o
                            fupd_right (Net.filter (not_ceq th)))
fun delsimp th rwts = List.filter (not_ceq th) rwts
fun temp_remove_simp th =
    Sref.update the_ruledb (fupd_DOMRNG_ss (delsimp th))

fun name_to_thm n =
    case String.fields (equal #".") n of
        [s] => DB.fetch (current_theory()) s
      | [thy,name] => DB.fetch thy name
      | _ => raise mk_HOL_ERR "transferLib" "temp_remove_named_rule"
                   ("Malformed thm-spec: "^n)
fun temp_remove_named_rule n = temp_remove_rule (name_to_thm n)
fun temp_remove_named_safe n = temp_remove_safe (name_to_thm n)
fun temp_remove_named_simp n = temp_remove_simp (name_to_thm n)

fun new_exporter nm add del =
    let
      val {export,...} =
          ThmSetData.new_exporter {
            settype = nm,
            efns = {add = fn {named_thm,...} => add (#2 named_thm),
                    remove = fn {remove,...} => del remove}
          }
    in
      export
    end

val add_rule = new_exporter "transfer_rule" temp_add_rule temp_remove_named_rule
val add_safe = new_exporter "transfer_safe" temp_add_safe temp_remove_named_safe
val add_simp = new_exporter "transfer_simp" temp_add_simp temp_remove_named_simp

fun global_ruledb() = Sref.value the_ruledb


end (* struct *)
